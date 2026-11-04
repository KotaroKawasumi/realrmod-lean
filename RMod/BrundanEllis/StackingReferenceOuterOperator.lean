import RMod.BrundanEllis.StackingReferenceAssociator
import RMod.BrundanEllis.StackingReferenceShiftedExchange
import RMod.BrundanEllis.StackingReferenceHexagonData

/-! Exchange an atom with a binary fusion kernel. The inner row is retained;
its parity supplies exactly the outer-crossing sign in the finite hexagons. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- Equality transport keeps coefficient coordinates in their original order. -/
theorem coefficientCast_apply {a b : ZMod 8} (h : a = b) (x : Coeff a)
    (i : Fin (realRepDim b.val)) :
    coefficientCast h x i = x (Fin.cast (congrArg (fun c : ZMod 8 => realRepDim c.val) h.symm) i) := by
  cases h
  rfl

/-- Each real matrix entry is the normalized integer exchange entry. -/
theorem normalizedKernelEquiv_basis (a b : ZMod 8) (r : Index b a) (s : Index a b) :
    normalizedKernelEquiv a b ((coordinates a b).symm (Pi.single s 1)) r.1 r.2 =
      normalizingScalar a b * (forwardZ a b r s : ℝ) := by
  rw [normalizedKernelEquiv_apply]
  change normalizingScalar a b * coordinates b a
    (kernelEquiv a b ((coordinates a b).symm (Pi.single s 1))) r = _
  rw [coordinates_kernelEquiv, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one]
  change normalizingScalar a b * (↑(forward a b r s) : ℝ) = _
  simp only [forward, Matrix.map_apply, Rat.cast_intCast]

/-- A right-associated coordinate basis has support in exactly one pair of rows. -/
theorem rightCoordinates_basis (a b c : ZMod 8) (s : RightIndex a b c)
    (i : FusionTable.Index b c) (j : FusionTable.Index a (b + c)) :
    (rightCoordinates a b c).symm (Pi.single s 1) i j =
      if i = s.1 ∧ j = s.2.1 then RealPChiKernel.coefficientBasis (a + b + c) s.2.2 else 0 := by
  rcases s with ⟨s, t, u⟩
  funext k
  by_cases hi : i = s <;> by_cases hj : j = t <;>
    simp [rightCoordinates, Pi.single_apply, RealPChiKernel.coefficientBasis, hi, hj]

/-- Move the first atom past the entire binary object. -/
def outerRightOperator (a b c : ZMod 8) : RightCarrier a b c →ₗ[ℝ] LeftCarrier b c a where
  toFun v r := shiftedExchange a (b + c) 0
    (FusionTable.indexParity b c r + shiftNu realComputableNuBeta.data b c)
      (fun j => coefficientCast (add_assoc a b c) (v r j))
  map_add' v w := by
    funext r
    simp only [map_add, Pi.add_apply]
    exact map_add _ _ _
  map_smul' q v := by
    funext r
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    exact map_smul (shiftedExchange a (b + c) 0
      (FusionTable.indexParity b c r + shiftNu realComputableNuBeta.data b c)) q
      (fun j => coefficientCast (add_assoc a b c) (v r j))

/-- Its basis coefficients are precisely the finite outer-crossing matrix. -/
theorem outerRightOperator_basis (a b c : ZMod 8) (r : LeftIndex b c a) (s : RightIndex a b c) :
    leftCoordinates b c a
      (outerRightOperator a b c ((rightCoordinates a b c).symm (Pi.single s 1))) r =
        normalizingScalar a (b + c) * (outerRightZ a b c r s : ℝ) := by
  let hs := congrArg (fun z : ZMod 8 => realRepDim z.val) (add_assoc a b c)
  have hv : (fun j => coefficientCast (add_assoc a b c)
      ((rightCoordinates a b c).symm (Pi.single s 1) r.1 j)) =
      if r.1 = s.1 then
        (coordinates a (b + c)).symm (Pi.single (s.2.1, Fin.cast hs s.2.2) 1) else 0 := by
    funext j
    rw [rightCoordinates_basis]
    simp only [ite_and, apply_ite, map_zero, coefficientCast_basis]
    by_cases h : r.1 = s.1
    · simp only [h, if_true]
      exact (coordinates_basis a (b + c) (s.2.1, Fin.cast hs s.2.2) j).symm
    · simp [h]
  change shiftedExchange a (b + c) 0 _ _ r.2.1 r.2.2 = _
  rw [hv]
  by_cases h : r.1 = s.1
  · rw [if_pos h]
    simp only [shiftedExchange, LinearMap.smul_apply, LinearEquiv.coe_coe, Pi.smul_apply,
      smul_eq_mul, normalizedKernelEquiv_basis, exchangeShift, zero_add, zero_mul, add_zero]
    have hdim : s.2.2.val < realRepDim (a + (b + c)).val := by
      rw [← add_assoc]
      exact s.2.2.isLt
    have hrank : r.2.1.val < RealPChiKernel.fusionRank (b + c) a := r.2.1.isLt
    have hsrank : s.2.1.val < RealPChiKernel.fusionRank a (b + c) := s.2.1.isLt
    simp only [outerRightZ, h, if_true, exchangeEntry, dif_pos hrank,
      dif_pos r.2.2.isLt, dif_pos hsrank, dif_pos hdim, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, ← paritySign_pow]
    change paritySign _ * (normalizingScalar a (b + c) * (forwardZ _ _ _ _ : ℝ)) = _
    rw [mul_left_comm]
    congr 2
  · rw [if_neg h, map_zero]
    simp [outerRightZ, h]

/-- The full outer operator therefore has the stated normalized matrix. -/
theorem outerRightOperator_matrix (a b c : ZMod 8) :
    ((leftCoordinates b c a).toLinearMap.comp (outerRightOperator a b c)).comp
      (rightCoordinates a b c).symm.toLinearMap =
      (normalizingScalar a (b + c) • (outerRightZ a b c).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (RightIndex a b c)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change leftCoordinates b c a
    (outerRightOperator a b c ((rightCoordinates a b c).symm (Pi.single s 1))) r = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact outerRightOperator_basis a b c r s

/-- Move a binary object past the third atom, retaining its inner row. -/
def outerLeftOperator (a b c : ZMod 8) : LeftCarrier a b c →ₗ[ℝ] RightCarrier c a b where
  toFun v r j := coefficientCast (add_assoc c a b).symm
    (shiftedExchange (a + b) c
      (FusionTable.indexParity a b r + shiftNu realComputableNuBeta.data a b) 0 (v r) j)
  map_add' v w := by
    funext r j
    simp only [map_add, Pi.add_apply]
  map_smul' q v := by
    funext r j
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- Its finite matrix includes exactly the parity of the retained inner row. -/
theorem outerLeftOperator_basis (a b c : ZMod 8) (r : RightIndex c a b) (s : LeftIndex a b c) :
    rightCoordinates c a b
      (outerLeftOperator a b c ((leftCoordinates a b c).symm (Pi.single s 1))) r =
        normalizingScalar (a + b) c * (outerLeftZ a b c r s : ℝ) := by
  have hv : (leftCoordinates a b c).symm (Pi.single s 1) r.1 =
      if r.1 = s.1 then (coordinates (a + b) c).symm (Pi.single (s.2.1, s.2.2) 1) else 0 := by
    funext j
    rw [leftCoordinates_basis]
    simp only [ite_and]
    by_cases h : r.1 = s.1
    · simp only [h, if_true]
      exact (coordinates_basis (a + b) c (s.2.1, s.2.2) j).symm
    · simp [h]
  change coefficientCast (add_assoc c a b).symm
    (shiftedExchange (a + b) c _ 0 _ r.2.1) r.2.2 = _
  rw [hv, coefficientCast_apply]
  by_cases h : r.1 = s.1
  · rw [if_pos h]
    simp only [shiftedExchange, LinearMap.smul_apply, LinearEquiv.coe_coe, Pi.smul_apply,
      smul_eq_mul, normalizedKernelEquiv_basis, exchangeShift, add_zero, mul_zero]
    have hdim : r.2.2.val < realRepDim (c + (a + b)).val := by
      rw [← add_assoc]
      exact r.2.2.isLt
    rw [normalizedKernelEquiv_basis (a + b) c
      (r.2.1, Fin.cast (congrArg (fun z : ZMod 8 => realRepDim z.val) (add_assoc c a b)) r.2.2)
      (s.2.1, s.2.2)]
    have hrank : r.2.1.val < RealPChiKernel.fusionRank c (a + b) := r.2.1.isLt
    have hsrank : s.2.1.val < RealPChiKernel.fusionRank (a + b) c := s.2.1.isLt
    simp only [outerLeftZ, h, if_true, exchangeEntry, dif_pos hrank,
      dif_pos hdim, dif_pos hsrank, dif_pos s.2.2.isLt, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, ← paritySign_pow]
    change paritySign _ * (normalizingScalar (a + b) c * (forwardZ _ _ _ _ : ℝ)) = _
    rw [mul_left_comm]
    congr 2
  · rw [if_neg h, map_zero]
    simp [outerLeftZ, h]

/-- The second outer leg uses the same normalized exchange matrices. -/
theorem outerLeftOperator_matrix (a b c : ZMod 8) :
    ((rightCoordinates c a b).toLinearMap.comp (outerLeftOperator a b c)).comp
      (leftCoordinates a b c).symm.toLinearMap =
      (normalizingScalar (a + b) c • (outerLeftZ a b c).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (LeftIndex a b c)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change rightCoordinates c a b
    (outerLeftOperator a b c ((leftCoordinates a b c).symm (Pi.single s 1))) r = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact outerLeftOperator_basis a b c r s

end RMod.BrundanEllis.Stacking.ReferenceCommutor

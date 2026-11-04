import RMod.BrundanEllis.StackingReferenceAssociator
import RMod.BrundanEllis.StackingReferenceShiftedExchange
import RMod.BrundanEllis.StackingReferenceHexagonData

/-! The inner crossing acts through the existing left/right division-algebra
action on the outer fusion kernel. Its matrix is obtained by real-linear
extension of the already verified action on algebra basis elements. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- Transport the two labels of a fusion kernel without changing coordinates. -/
def kernelLabelCast {a b c d : ZMod 8} (h : a = b) (k : c = d) :
    RealCCarrier a c ≃ₗ[ℝ] RealCCarrier b d := by
  cases h
  cases k
  exact LinearEquiv.refl ℝ _

/-- Coordinate basis vectors retain their row and coefficient positions. -/
theorem kernelLabelCast_basis {a b c d : ZMod 8} (h : a = b) (k : c = d) (s : Index a c) :
    kernelLabelCast h k ((coordinates a c).symm (Pi.single s 1)) =
      (coordinates b d).symm (Pi.single
        (Fin.cast (congrArg₂ RealPChiKernel.fusionRank h k) s.1,
          Fin.cast (congrArg (fun z : ZMod 8 => realRepDim z.val) (congrArg₂ (· + ·) h k)) s.2) 1) := by
  cases h
  cases k
  rfl

/-- Arbitrary integer coefficients in the first slot use the certified action matrices. -/
theorem leftOperator_integer_basis (a b : ZMod 8) (x : Fin (realRepDim a.val) → ℤ)
    (r s : Index a b) :
    coordinates a b (leftOperator a b (fun u => (x u : ℝ)) (Coeff.one b)
      ((coordinates a b).symm (Pi.single s 1))) r =
        ∑ u, (x u : ℝ) * (leftActionZ a b u r s : ℝ) := by
  have hs := (Pi.basisFun ℝ (Fin (realRepDim a.val))).sum_repr (fun u => (x u : ℝ))
  have ht := congrArg (firstInput a b (Coeff.one b) ((coordinates a b).symm (Pi.single s 1))) hs
  simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] at ht
  have he := congrArg (fun v => coordinates a b v r) ht
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  change (∑ u, (x u : ℝ) * coordinates a b
    (leftOperator a b (Pi.single u 1) (Coeff.one b)
      ((coordinates a b).symm (Pi.single s 1))) r) = _ at he
  simp_rw [← coefficientBasis_single, shifted_left_basis] at he
  simpa only [firstInput, LinearMap.coe_mk, AddHom.coe_mk, leftAction, Matrix.map_apply, Rat.cast_intCast] using he.symm

/-- The same real-linear extension applies in the second slot. -/
theorem rightOperator_integer_basis (a b : ZMod 8) (x : Fin (realRepDim b.val) → ℤ)
    (r s : Index a b) :
    coordinates a b (leftOperator a b (Coeff.one a) (fun u => (x u : ℝ))
      ((coordinates a b).symm (Pi.single s 1))) r =
        ∑ u, (x u : ℝ) * (rightActionZ a b u r s : ℝ) := by
  have hs := (Pi.basisFun ℝ (Fin (realRepDim b.val))).sum_repr (fun u => (x u : ℝ))
  have ht := congrArg (secondInput a b (Coeff.one a) ((coordinates a b).symm (Pi.single s 1))) hs
  simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] at ht
  have he := congrArg (fun v => coordinates a b v r) ht
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  change (∑ u, (x u : ℝ) * coordinates a b
    (leftOperator a b (Coeff.one a) (Pi.single u 1)
      ((coordinates a b).symm (Pi.single s 1))) r) = _ at he
  simp_rw [← coefficientBasis_single, shifted_right_basis] at he
  simpa only [secondInput, LinearMap.coe_mk, AddHom.coe_mk, rightAction, Matrix.map_apply, Rat.cast_intCast] using he.symm

/-- Tensor the inner exchange coefficients with the identity of the third atom. -/
def innerLeftOperator (a b c : ZMod 8) : LeftCarrier a b c →ₗ[ℝ] LeftCarrier b a c :=
  LinearMap.pi fun r => normalizingScalar a b • ∑ s : FusionTable.Index a b,
    (leftOperator (b + a) c (fun u => (coefficientZ a b (forwardZ a b) r s u.val : ℝ))
      (Coeff.one c)).comp
      ((kernelLabelCast (add_comm a b) rfl).toLinearMap.comp (LinearMap.proj s))

/-- The individual outer-kernel action in the left inner leg. -/
theorem innerLeftOperator_apply (a b c : ZMod 8) (v : LeftCarrier a b c)
    (r : FusionTable.Index b a) :
    innerLeftOperator a b c v r = normalizingScalar a b • ∑ s : FusionTable.Index a b,
      leftOperator (b + a) c (fun u => (coefficientZ a b (forwardZ a b) r s u.val : ℝ))
        (Coeff.one c) (kernelLabelCast (add_comm a b) rfl (v s)) := by
  simp only [innerLeftOperator, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]

/-- The left inner leg has exactly the coefficient matrix used by the finite hexagon. -/
theorem innerLeftOperator_basis (a b c : ZMod 8) (r : LeftIndex b a c) (s : LeftIndex a b c) :
    leftCoordinates b a c
      (innerLeftOperator a b c ((leftCoordinates a b c).symm (Pi.single s 1))) r =
        normalizingScalar a b * (innerLeftZ a b c r s : ℝ) := by
  have hv (i : FusionTable.Index a b) :
      (leftCoordinates a b c).symm (Pi.single s 1) i =
      if i = s.1 then (coordinates (a + b) c).symm (Pi.single (s.2.1, s.2.2) 1) else 0 := by
    funext j
    rw [leftCoordinates_basis]
    simp only [ite_and]
    by_cases h : i = s.1
    · simp only [h, if_true]
      exact (coordinates_basis (a + b) c (s.2.1, s.2.2) j).symm
    · simp [h]
  change (innerLeftOperator a b c _ r.1) r.2.1 r.2.2 = _
  rw [innerLeftOperator_apply]
  simp_rw [hv, apply_ite, map_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [kernelLabelCast_basis]
  change normalizingScalar a b * coordinates (b + a) c
    (leftOperator (b + a) c _ (Coeff.one c) ((coordinates (b + a) c).symm _)) r.2 = _
  rw [leftOperator_integer_basis]
  congr 1
  simp only [innerLeftZ, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [leftActionZ, Fin.val_cast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- Passing from basis columns to the full real matrix introduces no extra factor. -/
theorem innerLeftOperator_matrix (a b c : ZMod 8) :
    ((leftCoordinates b a c).toLinearMap.comp (innerLeftOperator a b c)).comp
      (leftCoordinates a b c).symm.toLinearMap =
      (normalizingScalar a b • (innerLeftZ a b c).map ((↑) : ℤ → ℝ)).mulVecLin := by
  apply (Pi.basisFun ℝ (LeftIndex a b c)).ext
  intro s
  rw [Pi.basisFun_apply]
  funext r
  change leftCoordinates b a c
    (innerLeftOperator a b c ((leftCoordinates a b c).symm (Pi.single s 1))) r = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact innerLeftOperator_basis a b c r s

end RMod.BrundanEllis.Stacking.ReferenceCommutor

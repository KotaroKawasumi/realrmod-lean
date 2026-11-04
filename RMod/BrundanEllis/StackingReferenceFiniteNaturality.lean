import RMod.BrundanEllis.StackingReferenceTensorRows
import RMod.BrundanEllis.StackingReferenceExchangeNaturality

/-! Finite-sum naturality of the reference exchange. Each summand uses the
actual parity-shifted tensor operator; linearity extends the atomic equation
to arbitrary coefficient matrices between finite families. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Tensor two coefficient matrices, block by block on the actual fusion kernels. -/
def blockTensorOperator {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    (Fin n → Fin m → RealCCarrier a b) →ₗ[ℝ] (Fin n' → Fin m' → RealCCarrier a b) :=
  LinearMap.pi fun i' => LinearMap.pi fun j' => ∑ i : Fin n, ∑ j : Fin m,
    (shiftedTensorOperator a b (p i) (q j) (q' j') (F i i') (G j j')).comp
      ((LinearMap.proj j : (Fin m → RealCCarrier a b) →ₗ[ℝ] RealCCarrier a b).comp
        (LinearMap.proj i : (Fin n → Fin m → RealCCarrier a b) →ₗ[ℝ] (Fin m → RealCCarrier a b)))

@[simp] theorem blockTensorOperator_apply {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (v : Fin n → Fin m → RealCCarrier a b) (i' : Fin n') (j' : Fin m') :
    blockTensorOperator a b p q q' F G v i' j' =
      ∑ i : Fin n, ∑ j : Fin m,
        shiftedTensorOperator a b (p i) (q j) (q' j') (F i i') (G j j') (v i j) := by
  simp only [blockTensorOperator, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

/-- The reversed tensor action, over the same endpoint coefficient algebra. -/
def reversedBlockTensorOperator {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    (Fin m → Fin n → FusionTable.Index b a → Coeff (a + b)) →ₗ[ℝ]
      (Fin m' → Fin n' → FusionTable.Index b a → Coeff (a + b)) :=
  LinearMap.pi fun j' => LinearMap.pi fun i' => ∑ i : Fin n, ∑ j : Fin m,
    (reversedTensorOperator a b (q j) (p i) (p' i') (G j j') (F i i')).comp
      ((LinearMap.proj i : (Fin n → FusionTable.Index b a → Coeff (a + b)) →ₗ[ℝ]
        (FusionTable.Index b a → Coeff (a + b))).comp
        (LinearMap.proj j : (Fin m → Fin n → FusionTable.Index b a → Coeff (a + b)) →ₗ[ℝ]
          (Fin n → FusionTable.Index b a → Coeff (a + b))))

@[simp] theorem reversedBlockTensorOperator_apply {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (v : Fin m → Fin n → FusionTable.Index b a → Coeff (a + b)) (j' : Fin m') (i' : Fin n') :
    reversedBlockTensorOperator a b p p' q F G v j' i' =
      ∑ i : Fin n, ∑ j : Fin m,
        reversedTensorOperator a b (q j) (p i) (p' i') (G j j') (F i i') (v j i) := by
  simp only [reversedBlockTensorOperator, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

/-- Signed naturality holds for every finite matrix of homogeneous morphisms. -/
theorem blockExchange_naturality {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) (d e : ZMod 2)
    (hF : ∀ i i', (realDData.algebra a).MemGrade (d + p i + p' i') (F i i'))
    (hG : ∀ j j', (realDData.algebra b).MemGrade (e + q j + q' j') (G j j')) :
    (blockExchange a b p' q').toLinearMap.comp (blockTensorOperator a b p q q' F G) =
      paritySign (degree a b * (d + e) + d * e) •
        (reversedBlockTensorOperator a b p p' q F G).comp (blockExchange a b p q).toLinearMap := by
  apply LinearMap.ext
  intro v
  funext j' i'
  change shiftedCommonKernelEquiv a b (p' i') (q' j')
      (blockTensorOperator a b p q q' F G v i' j') =
    paritySign (degree a b * (d + e) + d * e) •
      reversedBlockTensorOperator a b p p' q F G (blockExchange a b p q v) j' i'
  rw [blockTensorOperator_apply, reversedBlockTensorOperator_apply]
  simp_rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact LinearMap.congr_fun
    (commonExchange_naturality a b (p i) (p' i') (q j) (q' j') d e (F i i') (G j j')
      (hF i i') (hG j j')) (v i j)

/-- The tensor operator in the stored, flattened reference-object coordinates. -/
def familyTensorOperator {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    (Fin (rowTensorObject a b p q).size → Coeff (a + b)) →ₗ[ℝ]
      (Fin (rowTensorObject a b p' q').size → Coeff (a + b)) :=
  (rowTensorCoordinates a b p' q' (Coeff (a + b))).symm.toLinearMap.comp
    ((blockTensorOperator a b p q q' F G).comp
      (rowTensorCoordinates a b p q (Coeff (a + b))).toLinearMap)

/-- The reversed tensor operator in the corresponding actual reference enumeration. -/
def reversedFamilyTensorOperator {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    (Fin (rowTensorObject b a q p).size → Coeff (a + b)) →ₗ[ℝ]
      (Fin (rowTensorObject b a q' p').size → Coeff (a + b)) :=
  (rowTensorCoordinates b a q' p' (Coeff (a + b))).symm.toLinearMap.comp
    ((reversedBlockTensorOperator a b p p' q F G).comp
      (rowTensorCoordinates b a q p (Coeff (a + b))).toLinearMap)

/-- Coordinate changes preserve the full finite-sum naturality equation. -/
theorem rowTensorEquiv_naturality {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) (d e : ZMod 2)
    (hF : ∀ i i', (realDData.algebra a).MemGrade (d + p i + p' i') (F i i'))
    (hG : ∀ j j', (realDData.algebra b).MemGrade (e + q j + q' j') (G j j')) :
    (rowTensorEquiv a b p' q').toLinearMap.comp (familyTensorOperator a b p p' q q' F G) =
      paritySign (degree a b * (d + e) + d * e) •
        (reversedFamilyTensorOperator a b p p' q q' F G).comp (rowTensorEquiv a b p q).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply (rowTensorCoordinates b a q' p' (Coeff (a + b))).injective
  have h := LinearMap.congr_fun (blockExchange_naturality a b p p' q q' F G d e hF hG)
    (rowTensorCoordinates a b p q (Coeff (a + b)) v)
  simpa only [rowTensorEquiv, familyTensorOperator, reversedFamilyTensorOperator,
    LinearEquiv.trans_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, LinearMap.smul_apply, map_smul] using h

end RMod.BrundanEllis.Stacking.ReferenceCommutor

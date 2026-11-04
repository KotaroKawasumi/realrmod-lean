import RMod.BrundanEllis.StackingReferenceShiftedKernelHom

/-! Transport the signed naturality of normalized exchanges from free-module
operators to actual coefficient morphisms. All maps use the stored algebra
multiplication; the parity signs are those of the actual tensor operator. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Taking unit columns recovers a coefficient matrix exactly. -/
theorem rowMatrixOf_operator {n m : ℕ} (a : ZMod 8) (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    rowMatrixOf a (rowOperator a M) = M := by
  funext j i
  exact rowOperator_unit a M i j

/-- Unit columns of a composite right-linear operator are the actual coefficient product. -/
theorem rowMatrixOf_comp {n m l : ℕ} (a : ZMod 8)
    (F : (Fin n → Coeff a) →ₗ[ℝ] (Fin m → Coeff a))
    (G : (Fin m → Coeff a) →ₗ[ℝ] (Fin l → Coeff a))
    (hF : ∀ v x, F (rowRight a v x) = rowRight a (F v) x)
    (hG : ∀ v x, G (rowRight a v x) = rowRight a (G v) x) :
    rowMatrixOf a (G.comp F) = rowProduct a (rowMatrixOf a G) (rowMatrixOf a F) := by
  conv_lhs => rw [← rowOperator_matrixOf a F hF, ← rowOperator_matrixOf a G hG, rowOperator_comp]
  exact rowMatrixOf_operator a _

/-- Scalar multiplication in the actual category is coefficientwise scalar multiplication. -/
theorem rowHom_smul {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (r : ℝ) (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    Hom.smul r (rowHom a p q M) = rowHom a p q (r • M) := by
  funext i j
  apply AtomHom.ext_same_label
  change (AtomHom.smul r (AtomHom.ofLabelEq (dD := realDData)
    (X := (a, p i)) (Y := (a, q j)) rfl (M j i))).coeff rfl = _
  rw [AtomHom.coeff_smul, AtomHom.coeff_ofLabelEq]
  change Coeff.smul a r (M j i) = (rowHom a p q (r • M) i j).coeff rfl
  rw [rowHom_coeff]
  rfl

/-- The shifted tensor operator is right-linear over the endpoint algebra. -/
theorem shiftedTensorOperator_right (a b : ZMod 8) (p q q' : ZMod 2)
    (x : Coeff a) (y : Coeff b) (v : RealCCarrier a b) (z : Coeff (a + b)) :
    shiftedTensorOperator a b p q q' x y (rowRight (a + b) v z) =
      rowRight (a + b) (shiftedTensorOperator a b p q q' x y v) z := by
  simp only [shiftedTensorOperator, LinearMap.smul_apply, rowRight_smul]
  apply congrArg (fun w : RealCCarrier a b => paritySign (p * (q + q')) • w)
  exact (realComputableShiftedRawDCT.laws.C.actions_comm a b
    (routeRowTwist realDData a q' x) (routeRowTwist realDData b p y) v z).symm

/-- Transport the tensor action on the reversed rows to the common endpoint algebra. -/
def reversedTensorOperator (a b : ZMod 8) (q p p' : ZMod 2) (y : Coeff b) (x : Coeff a) :
    (FusionTable.Index b a → Coeff (a + b)) →ₗ[ℝ] (FusionTable.Index b a → Coeff (a + b)) :=
  (kernelTargetCast a b).toLinearMap.comp
    ((shiftedTensorOperator b a q p p' y x).comp (kernelTargetCast a b).symm.toLinearMap)

/-- The shifted common-algebra exchange is just endpoint transport of the shifted exchange. -/
theorem shiftedCommonKernelEquiv_transport (a b : ZMod 8) (p q : ZMod 2) (v : RealCCarrier a b) :
    shiftedCommonKernelEquiv a b p q v = kernelTargetCast a b (shiftedExchange a b p q v) := by
  simp only [shiftedCommonKernelEquiv_apply, shiftedExchange, LinearMap.smul_apply,
    LinearEquiv.coe_coe, map_smul]
  rfl

/-- Naturality after placing both row modules over exactly the same coefficient algebra. -/
theorem commonExchange_naturality (a b : ZMod 8) (p p' q q' i j : ZMod 2)
    (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade (i + p + p') x)
    (hy : (realDData.algebra b).MemGrade (j + q + q') y) :
    (shiftedCommonKernelEquiv a b p' q').toLinearMap.comp (shiftedTensorOperator a b p q q' x y) =
      paritySign (degree a b * (i + j) + i * j) •
        (reversedTensorOperator a b q p p' y x).comp (shiftedCommonKernelEquiv a b p q).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    shiftedCommonKernelEquiv_transport, reversedTensorOperator,
    LinearEquiv.symm_apply_apply]
  rw [shiftedExchange_naturality a b p p' q q' i j x y hx hy, map_smul]

/-- Endpoint transport commutes with the strict right action. -/
theorem kernelTargetCast_right (a b : ZMod 8) (v : RealCCarrier b a) (x : Coeff (b + a)) :
    kernelTargetCast a b (realCRight b a v x) =
      rowRight (a + b) (kernelTargetCast a b v) (coefficientCast (add_comm b a) x) := by
  funext i
  exact coefficientCast_mul (add_comm b a) (v i) x

theorem kernelTargetCast_symm_right (a b : ZMod 8)
    (v : FusionTable.Index b a → Coeff (a + b)) (x : Coeff (a + b)) :
    (kernelTargetCast a b).symm (rowRight (a + b) v x) =
      realCRight b a ((kernelTargetCast a b).symm v) (coefficientCast (add_comm a b) x) := by
  apply (kernelTargetCast a b).injective
  rw [LinearEquiv.apply_symm_apply, kernelTargetCast_right,
    LinearEquiv.apply_symm_apply, coefficientCast_trans]
  rfl

/-- The reversed tensor action is also right-linear over the common endpoint algebra. -/
theorem reversedTensorOperator_right (a b : ZMod 8) (q p p' : ZMod 2)
    (y : Coeff b) (x : Coeff a) (v : FusionTable.Index b a → Coeff (a + b)) (z : Coeff (a + b)) :
    reversedTensorOperator a b q p p' y x (rowRight (a + b) v z) =
      rowRight (a + b) (reversedTensorOperator a b q p p' y x v) z := by
  simp only [reversedTensorOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
    kernelTargetCast_symm_right]
  change kernelTargetCast a b
    (shiftedTensorOperator b a q p p' y x
      (rowRight (b + a) ((kernelTargetCast a b).symm v) (coefficientCast (add_comm a b) z))) = _
  rw [shiftedTensorOperator_right]
  change kernelTargetCast a b (realCRight b a
    (shiftedTensorOperator b a q p p' y x ((kernelTargetCast a b).symm v))
    (coefficientCast (add_comm a b) z)) = _
  rw [kernelTargetCast_right, coefficientCast_trans]
  rfl

/-- The coefficient morphisms satisfy the actual signed composition equation. -/
theorem rowExchange_naturality (a b : ZMod 8) (p p' q q' i j : ZMod 2)
    (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade (i + p + p') x)
    (hy : (realDData.algebra b).MemGrade (j + q + q') y) :
    Hom.comp
      (rowHom (a + b) (fun k => p + q + kernelRowParity a b k)
        (fun k => p' + q' + kernelRowParity a b k)
        (rowMatrixOf (a + b) (shiftedTensorOperator a b p q q' x y)))
      (rowHom (a + b) (fun k => p' + q' + kernelRowParity a b k)
        (fun k => q' + p' + kernelRowParity b a k)
        (rowMatrixOf (a + b) (shiftedCommonKernelEquiv a b p' q').toLinearMap)) =
    Hom.smul (paritySign (degree a b * (i + j) + i * j))
      (Hom.comp
        (rowHom (a + b) (fun k => p + q + kernelRowParity a b k)
          (fun k => q + p + kernelRowParity b a k)
          (rowMatrixOf (a + b) (shiftedCommonKernelEquiv a b p q).toLinearMap))
        (rowHom (a + b) (fun k => q + p + kernelRowParity b a k)
          (fun k => q' + p' + kernelRowParity b a k)
          (rowMatrixOf (a + b) (reversedTensorOperator a b q p p' y x)))) := by
  rw [rowHom_comp, rowHom_comp, rowHom_smul]
  apply congrArg (rowHom (a + b) _ _)
  rw [← rowMatrixOf_comp (a + b) _ _ (shiftedTensorOperator_right a b p q q' x y)
    (shiftedCommonKernelEquiv_right a b p' q'),
    ← rowMatrixOf_comp (a + b) _ _ (shiftedCommonKernelEquiv_right a b p q)
      (reversedTensorOperator_right a b q p p' y x)]
  rw [commonExchange_naturality a b p p' q q' i j x y hx hy]
  rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor

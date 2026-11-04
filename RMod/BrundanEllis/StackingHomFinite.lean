import RMod.BrundanEllis.Surface
import RMod.BrundanEllis.StackingKaroubiEnrichment

/-! Finite-dimensional graded Hom spaces survive both the super tensor
product and passage to idempotent corners. Each tensor degree is a finite
coproduct of ordinary tensor products, and every corner is a submodule. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking

theorem tensor_grade_finite (V W : SuperVec)
    (hV : ∀ a, FiniteDimensional ℝ (V a)) (hW : ∀ a, FiniteDimensional ℝ (W a)) (a : ZMod 2) :
    FiniteDimensional ℝ ((V ⊗ W) a) := by
  classical
  letI := hV
  letI := hW
  let J := {ij : ZMod 2 × ZMod 2 // ij.1 + ij.2 = a}
  let f : J → ModuleCat ℝ := fun ij => V ij.val.1 ⊗ W ij.val.2
  letI (j : J) : FiniteDimensional ℝ (f j) := by
    change FiniteDimensional ℝ (V j.val.1 ⊗[ℝ] W j.val.2)
    infer_instance
  let e : (V ⊗ W) a ≅ ModuleCat.of ℝ (∀ j : J, f j) :=
    (biproduct.isoCoproduct f).symm ≪≫ ModuleCat.biproductIsoPi f
  exact FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective

theorem product_hom_finite {A B : Type} [SuperCategory A] [SuperCategory B]
    (hA : ∀ X Y a, FiniteDimensional ℝ (SHom A X Y a))
    (hB : ∀ X Y a, FiniteDimensional ℝ (SHom B X Y a))
    (X Y : SuperTensorProduct A B) (a : ZMod 2) :
    FiniteDimensional ℝ (SHom (SuperTensorProduct A B) X Y a) :=
  tensor_grade_finite (SHom A X.1 Y.1) (SHom B X.2 Y.2) (hA X.1 Y.1) (hB X.2 Y.2) a

theorem corner_hom_finite {C : Type} [SuperCategory C]
    (hC : ∀ X Y a, FiniteDimensional ℝ (SHom C X Y a))
    (P Q : Karoubi (Even C)) (a : ZMod 2) :
    FiniteDimensional ℝ (SHom (Karoubi (Even C)) P Q a) := by
  letI := hC (ForgetEnrichment.to SuperVec P.X) (ForgetEnrichment.to SuperVec Q.X) a
  change FiniteDimensional ℝ (KaroubiSuper.homSubmodule P Q a)
  infer_instance

/-- The finite-Hom part of the fusion axioms for the proposed completed product. -/
theorem completed_product_hom_finite (A B : WeaklyPointedFusionPiSuperCat)
    (P Q : Karoubi (Even (SuperTensorProduct A B))) (a : ZMod 2) :
    FiniteDimensional ℝ (SHom (Karoubi (Even (SuperTensorProduct A B))) P Q a) :=
  corner_hom_finite
    (product_hom_finite (FusionPiSuperCategory.hom_finite (C := A))
      (FusionPiSuperCategory.hom_finite (C := B))) P Q a

end RMod.BrundanEllis.Stacking

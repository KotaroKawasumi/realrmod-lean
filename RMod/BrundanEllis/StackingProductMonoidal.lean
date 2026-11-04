import RMod.BrundanEllis.StackingProductNaturality
import RMod.BrundanEllis.StackingProductPure
import RMod.BrundanEllis.StackingEvenTensor

/-! The ordinary monoidal laws of the super product. Naturality follows
from the full Hom-object equations; pentagon and triangle are the images
of the component coherence diagrams under the even pairing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B : Type} [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

instance productMonoidal : MonoidalCategory (Even (SuperTensorProduct A B)) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro X Y
      exact (productTensorFunctor A B).map_id (X, Y))
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intro X X' X'' Y Y' Y'' f g f' g'
      exact ((productTensorFunctor A B).map_comp
        (X := (X, Y)) (Y := (X', Y')) (Z := (X'', Y'')) (f, g) (f', g')).symm)
    (associator_naturality := by
      intro X Y Z X' Y' Z' f g h
      apply (eHomEquiv SuperVec).injective
      rw [← even_post, ← even_pre]
      change ForgetEnrichment.homTo SuperVec ((f ⊗ₘ g) ⊗ₘ h) ≫ _ =
        ForgetEnrichment.homTo SuperVec (f ⊗ₘ (g ⊗ₘ h)) ≫ _
      simp only [product_tensor_homTo, assoc]
      exact even_triple_naturality _ _ _ _ _ _ _ _ _
        (product_associator_naturality X X' Y Y' Z Z'))
    (leftUnitor_naturality := by
      intro X Y f
      apply (eHomEquiv SuperVec).injective
      rw [← even_post, ← even_pre]
      change ForgetEnrichment.homTo SuperVec ((𝟙 (𝟙_ _)) ⊗ₘ f) ≫ _ =
        ForgetEnrichment.homTo SuperVec f ≫ _
      rw [product_tensor_homTo, ForgetEnrichment.homTo_id]
      have h := congrArg (fun k => ForgetEnrichment.homTo SuperVec f ≫ k)
        (product_left_naturality X Y)
      simpa only [productTensorMap, assoc, even_left_tensor_assoc, ForgetEnrichment.to, Even] using h)
    (rightUnitor_naturality := by
      intro X Y f
      apply (eHomEquiv SuperVec).injective
      rw [← even_post, ← even_pre]
      change ForgetEnrichment.homTo SuperVec (f ⊗ₘ (𝟙 (𝟙_ _))) ≫ _ =
        ForgetEnrichment.homTo SuperVec f ≫ _
      rw [product_tensor_homTo, ForgetEnrichment.homTo_id]
      have h := congrArg (fun k => ForgetEnrichment.homTo SuperVec f ≫ k)
        (product_right_naturality X Y)
      simpa only [productTensorMap, assoc, even_right_tensor_assoc, ForgetEnrichment.to, Even] using h)
    (pentagon := by
      intro W X Y Z
      let w : Even A × Even B := (productFirst W, productSecond W)
      let x : Even A × Even B := (productFirst X, productSecond X)
      let y : Even A × Even B := (productFirst Y, productSecond Y)
      let z : Even A × Even B := (productFirst Z, productSecond Z)
      have h :
          ((α_ w x y).hom ⊗ₘ 𝟙 z) ≫ (α_ w (x ⊗ y) z).hom ≫
            (𝟙 w ⊗ₘ (α_ x y z).hom) =
          (α_ (w ⊗ x) y z).hom ≫ (α_ w x (y ⊗ z)).hom := by
        simpa only [tensorHom_id, id_tensorHom] using
          pentagon (C := Even A × Even B) w x y z
      have h' := congrArg (fun k => (productPair A B).map
        (X := ((w ⊗ x) ⊗ y) ⊗ z) (Y := w ⊗ (x ⊗ (y ⊗ z))) k) h
      simp only [Functor.map_comp, ← productPair_tensor, Functor.map_id] at h'
      exact h')
    (triangle := by
      intro X Y
      let x : Even A × Even B := (productFirst X, productSecond X)
      let y : Even A × Even B := (productFirst Y, productSecond Y)
      have h :
          (α_ x (𝟙_ _) y).hom ≫ (𝟙 x ⊗ₘ (λ_ y).hom) = (ρ_ x).hom ⊗ₘ 𝟙 y := by
        simpa only [tensorHom_id, id_tensorHom] using
          triangle (C := Even A × Even B) x y
      have h' := congrArg (fun k => (productPair A B).map
        (X := (x ⊗ (𝟙_ _)) ⊗ y) (Y := x ⊗ y) k) h
      simp only [Functor.map_comp, ← productPair_tensor, Functor.map_id] at h'
      exact h')

end RMod.BrundanEllis.Stacking

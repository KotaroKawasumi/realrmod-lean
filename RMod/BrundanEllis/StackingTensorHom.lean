import RMod.Classification.Instances.TensorHomBilinear
import RMod.Classification.Proofs.TensorEndInjection
import Mathlib.RingTheory.Flat.Basic

/-! The actual tensor map on arbitrary total Hom spaces is injective.
Embed each Hom space as a corner of an endomorphism algebra of a finite
biproduct, then apply the established tensor-endomorphism injectivity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking.Raw
open RMod.Classification
variable (C : RMod.WeaklyPointedSuperfusion.{0, 0})

def tensorHomLinear (X X' Y Y' : LinearCategory C) :
    (X ⟶ X') ⊗[ℝ] (Y ⟶ Y') →ₗ[ℝ]
      (@Quiver.Hom (LinearCategory C) _ (C.data.tensorObj X Y) (C.data.tensorObj X' Y')) :=
  TensorProduct.lift (tensorHomBilinear C X X' Y Y')

/-- Composition with specified even inclusions and projections selects a corner. -/
def cornerLinear {X X' A A' : LinearCategory C} (p : A ⟶ X) (i : X' ⟶ A') :
    (X ⟶ X') →ₗ[ℝ] (A ⟶ A') where
  toFun f := p ≫ f ≫ i
  map_add' f g := by simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r f := by simp [Linear.comp_smul, Linear.smul_comp]

/-- A corner embedding has a left inverse whenever both ends split. -/
theorem corner_injective {X X' A : LinearCategory C}
    (i : X ⟶ A) (p : A ⟶ X) (j : X' ⟶ A) (q : A ⟶ X')
    (hi : i ≫ p = 𝟙 X) (hj : j ≫ q = 𝟙 X') :
    Function.Injective (cornerLinear C p j) := by
  have he (f : X ⟶ X') : i ≫ cornerLinear C p j f ≫ q = f := by
    change i ≫ (p ≫ f ≫ j) ≫ q = f
    simp only [← Category.assoc, hi, Category.id_comp]
    simp only [Category.assoc, hj, Category.comp_id]
  intro f g h
  exact (he f).symm.trans ((congrArg (fun k => i ≫ k ≫ q) h).trans (he g))

/-- Even corner maps commute with the signed categorical tensor. -/
theorem corner_tensor {X X' Y Y' A A' B B' : LinearCategory C}
    (p : A ⟶ X) (q : B ⟶ Y) (i : X' ⟶ A') (j : Y' ⟶ B')
    (hp : C.data.IsHomogeneous 0 p) (hj : C.data.IsHomogeneous 0 j) :
    (tensorHomLinear C A A' B B').comp
        (TensorProduct.map (cornerLinear C p i) (cornerLinear C q j)) =
      (cornerLinear C (C.data.tensorHom p q) (C.data.tensorHom i j)).comp
        (tensorHomLinear C X X' Y Y') := by
  ext f g
  change C.data.tensorHom (C.data.comp p (C.data.comp f i)) (C.data.comp q (C.data.comp g j)) =
    C.data.comp (C.data.tensorHom p q)
      (C.data.comp (C.data.tensorHom f g) (C.data.tensorHom i j))
  symm
  rw [← C.laws.comp_assoc, interchange_first_even C.laws _ _ _ _ hp,
    interchange_second_even C.laws _ _ _ _ hj]
  simp only [C.laws.comp_assoc]

/-- Injectivity does not require the four objects to be simple or to have equal type. -/
theorem tensorHomLinear_injective (X X' Y Y' : LinearCategory C) :
    Function.Injective (tensorHomLinear C X X' Y Y') := by
  obtain ⟨A, i, p, hi, hp, hd, _, _⟩ := C.laws.has_finite_biproducts ![X, X']
  obtain ⟨B, j, q, hj, hq, he, _, _⟩ := C.laws.has_finite_biproducts ![Y, Y']
  have hiA := corner_injective C (i 0) (p 0) (i 1) (p 1) (hd 0) (hd 1)
  have hiB := corner_injective C (j 0) (q 0) (j 1) (q 1) (he 0) (he 1)
  have hmap := TensorProduct.map_injective_of_flat_flat _ _ hiA hiB
  have hc := corner_tensor C (p 0) (q 0) (i 1) (j 1) (hp 0) (hj 1)
  intro f g hfg
  apply hmap
  apply tensorEndLinear_injective C A B
  change tensorHomLinear C A A B B _ = tensorHomLinear C A A B B _
  calc
    _ = cornerLinear C (C.data.tensorHom (p 0) (q 0)) (C.data.tensorHom (i 1) (j 1))
        (tensorHomLinear C X X' Y Y' f) := LinearMap.congr_fun hc f
    _ = _ := congrArg _ hfg
    _ = _ := (LinearMap.congr_fun hc g).symm

end RMod.BrundanEllis.Stacking.Raw

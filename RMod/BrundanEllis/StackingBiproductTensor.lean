import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import RMod.Classification.Proofs.IteratedBiproducts

/-! Tensor distributions over two finite sums in the support order used
by the exterior comparison. These are ordinary even-category maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]
  {I J : Type} [Fintype I] [Fintype J]

/-- Distribute the right sum first, then the left sum, retaining the pair of labels. -/
def reversedBiproductDistributor (F : J → C) (G : I → C) :
    (⨁ F) ⊗ (⨁ G) ≅ ⨁ (fun ij : I × J => F ij.2 ⊗ G ij.1) :=
  leftDistributor _ G ≪≫
    biproduct.mapIso (fun i => rightDistributor F (G i)) ≪≫
    biproductBiproductIso (fun _ : I => J) (fun i j => F j ⊗ G i) ≪≫
    biproduct.whiskerEquiv
      (f := fun ij : (_ : I) × J => F ij.2 ⊗ G ij.1)
      (g := fun ij : I × J => F ij.2 ⊗ G ij.1)
      (Equiv.sigmaEquivProd I J) (fun _ => Iso.refl _)

/-- A tensor of inclusions is sent to precisely its pair-indexed inclusion. -/
theorem reversedBiproductDistributor_inclusion (F : J → C) (G : I → C) (i : I) (j : J) :
    (biproduct.ι F j ⊗ₘ biproduct.ι G i) ≫ (reversedBiproductDistributor F G).hom =
      biproduct.ι (fun ij : I × J => F ij.2 ⊗ G ij.1) (i, j) := by
  simp only [reversedBiproductDistributor, Iso.trans_hom, tensorHom_def, Category.assoc,
    biproduct_ι_comp_leftDistributor_hom_assoc, biproduct.mapIso_hom, biproduct.ι_map_assoc]
  rw [← Category.assoc, biproduct_ι_comp_rightDistributor_hom]
  have hi := RMod.Classification.iteratedBiproduct_inclusion (fun i j => F j ⊗ G i) i j
  simp only [← Category.assoc] at hi ⊢
  rw [hi]
  simp only [biproduct.whiskerEquiv_hom, biproduct.ι_desc, Iso.refl_inv]
  exact Category.id_comp _

end RMod.BrundanEllis.Stacking

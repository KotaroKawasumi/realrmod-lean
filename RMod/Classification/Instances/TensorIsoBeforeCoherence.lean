import RMod.Classification.Abstract.MonoidalComparison

/-!
# Tensor products of isomorphisms before the pentagon

Only bifunctoriality is required to tensor two isomorphisms. Keeping this
construction separate makes the later coherence transport noncircular.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory CategoryTheory.MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategoryStruct D]

def tensorIsoBeforeCoherence (hD : TensorStructuralLaws D)
    {X X' Y Y' : D} (e : X ≅ X') (f : Y ≅ Y') : X ⊗ Y ≅ X' ⊗ Y' where
  hom := e.hom ⊗ₘ f.hom
  inv := e.inv ⊗ₘ f.inv
  hom_inv_id := by
    rw [← hD.tensor_comp, e.hom_inv_id, f.hom_inv_id, hD.tensor_id]
  inv_hom_id := by
    rw [← hD.tensor_comp, e.inv_hom_id, f.inv_hom_id, hD.tensor_id]

end RMod.Classification

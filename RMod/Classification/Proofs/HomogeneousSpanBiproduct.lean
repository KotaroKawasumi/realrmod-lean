import RMod.Classification.Proofs.HomogeneousSpanOrthogonalCharacterization
import RMod.Classification.Proofs.EvenBiproductFullBicone

/-!
# A finite even biproduct stays in one homogeneous span

Project a map from any simple outside the component to every summand.
All entries vanish by orthogonality. The full-category biproduct property
then proves that the map itself is zero, giving component membership.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I]

theorem inHomogeneousSpan_even_biproduct {S : C.data.Obj} (hS : C.data.IsSimple S)
    (V : I → EvenSubcategory ℝ (LinearCategory C)) (hV : ∀ i, InHomogeneousSpan C S (V i).obj) :
    InHomogeneousSpan C S (⨁ V).obj := by
  apply (inHomogeneousSpan_iff_orthogonal C hS).mpr
  intro T hT hST f
  apply (evenBiproductFullIsBilimit C V).isLimit.hom_ext
  rintro ⟨i⟩
  change C.data.comp f (biproduct.π V i).hom = C.data.comp C.data.zero (biproduct.π V i).hom
  rw [raw_zero_comp C.laws]
  exact hom_zero_of_distinct_spans C hT hS (fun h => hST h.symm)
    (spanGenerator_mem C T) (hV i) _

end RMod.Classification

import RMod.Classification.Abstract.HomogeneousSpan
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homogeneous finite sums in a full span subcategory

Mathlib's induced Hom additive equivalence identifies the underlying map
of a finite sum with the sum of its underlying maps. The ambient grading
submodule therefore proves homogeneity term by term.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj}
  {X Y : HomogeneousSpanCategory C S} {n : ℕ}

theorem span_sum_hom (f : Fin n → (X ⟶ Y)) : (∑ i, f i).hom = ∑ i, (f i).hom :=
  map_sum (InducedCategory.homAddEquiv (C := LinearCategory C)
    (F := fun Z : HomogeneousSpanCategory C S => Z.obj) (X := X) (Y := Y)) f Finset.univ

theorem span_sum_grade {a : ZMod 2} (f : Fin n → (X ⟶ Y))
    (hf : ∀ i, C.data.IsHomogeneous a (f i).hom) : C.data.IsHomogeneous a (∑ i, f i).hom := by
  rw [span_sum_hom]
  change (∑ i, (f i).hom) ∈ LinearCategory.grade C X.obj Y.obj a
  exact Submodule.sum_mem _ (fun i _ => hf i)

end RMod.Classification

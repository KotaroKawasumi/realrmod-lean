import RMod.Classification.Abstract.SpanPreimages
import RMod.Classification.Instances.SpanSuperfunctor

/-!
# Selecting the specified even preimages and their isomorphisms

Classical choice selects objects and both maps from even essential
surjectivity. The completed preimages retain their even inverse laws.
The ordinary isomorphisms below use these exact maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  (F : SpanSuperfunctor C D S T)

theorem exists_spanPreimagesData
    (h : ∀ Y : HomogeneousSpanCategory D T, ∃ X, D.data.HasHomogeneousIso 0 (F.data.obj X).obj Y.obj) :
    ∃ d : SpanPreimagesData F.data, SpanPreimagesLaws d := by
  classical
  choose X i p hip hpi hi hp using h
  exact ⟨⟨X, fun Y => ⟨i Y, p Y⟩⟩, ⟨fun Y => ⟨⟨hip Y, hpi Y⟩, hi Y, hp Y⟩⟩⟩

noncomputable def spanPreimagesData
    (h : ∀ Y : HomogeneousSpanCategory D T, ∃ X, D.data.HasHomogeneousIso 0 (F.data.obj X).obj Y.obj) :
    SpanPreimagesData F.data := (exists_spanPreimagesData F h).choose

theorem spanPreimagesLaws
    (h : ∀ Y : HomogeneousSpanCategory D T, ∃ X, D.data.HasHomogeneousIso 0 (F.data.obj X).obj Y.obj) :
    SpanPreimagesLaws (spanPreimagesData F h) := (exists_spanPreimagesData F h).choose_spec

noncomputable def spanPreimages
    (h : ∀ Y : HomogeneousSpanCategory D T, ∃ X, D.data.HasHomogeneousIso 0 (F.data.obj X).obj Y.obj) :
    SpanPreimages F := ⟨spanPreimagesData F h, spanPreimagesLaws F h⟩

def SpanPreimages.counitIso {F : SpanSuperfunctor C D S T} (p : SpanPreimages F)
    (Y : HomogeneousSpanCategory D T) : F.toFunctor.obj (p.data.object Y) ≅ Y where
  hom := ObjectProperty.homMk (p.data.counit Y).hom
  inv := ObjectProperty.homMk (p.data.counit Y).inv
  hom_inv_id := ObjectProperty.hom_ext _ (p.laws.counit Y).hom_inv
  inv_hom_id := ObjectProperty.hom_ext _ (p.laws.counit Y).inv_hom

end RMod.Classification

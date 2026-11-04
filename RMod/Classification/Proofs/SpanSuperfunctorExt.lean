import RMod.Classification.Abstract.SpanSuperfunctor

/-!
# Component functors are determined by their ambient objects and maps

Membership certificates and superfunctor laws are propositions. Equality
of the ambient object functions and heterogeneous equality of the raw
map functions therefore determine the complete component superfunctor.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperfunctor

open CategoryTheory

theorem ext_raw {A C : WeaklyPointedSuperfusion.{0, 0}} {S : A.data.Obj} {T : C.data.Obj}
    {F G : SpanSuperfunctor A C S T}
    (hobj : ∀ X, (F.data.obj X).obj = (G.data.obj X).obj)
    (hmap : ∀ (X Y : HomogeneousSpanCategory A S) (f : X ⟶ Y),
      HEq (F.data.map f).hom (G.data.map f).hom) : F = G := by
  rcases F with ⟨⟨fo, fm⟩, fl⟩
  rcases G with ⟨⟨go, gm⟩, gl⟩
  have ho : fo = go := funext (fun X => ObjectProperty.FullSubcategory.ext (hobj X))
  cases ho
  have hm : @fm = @gm := by
    funext X Y f
    exact ObjectProperty.hom_ext _ (eq_of_heq (hmap X Y f))
  cases hm
  rfl

end RMod.Classification.SpanSuperfunctor

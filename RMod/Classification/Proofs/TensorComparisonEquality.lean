import RMod.Classification.Abstract.TensorComparison

/-!
# Equality of completed comparisons from their forward maps

Inverse maps are uniquely determined by the inverse identities. Thus
pointwise equality of the forward maps determines the entire specified
comparison data; proof irrelevance identifies their laws.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem IsoData.eq_of_hom_eq {C : WeaklyPointedSuperfusion.{0, 0}}
    {X Y : C.data.Obj} {d e : IsoData C.data X Y} (hd : IsoLaws C.data d) (he : IsoLaws C.data e)
    (h : d.hom = e.hom) : d = e := by
  have hi : d.inv = e.inv := by
    calc
      _ = C.data.comp (C.data.comp d.inv e.hom) e.inv := by
        rw [C.laws.comp_assoc, he.hom_inv, C.laws.comp_id]
      _ = _ := by rw [← h, hd.inv_hom, C.laws.id_comp]
  cases d
  cases e
  cases h
  cases hi
  rfl

theorem TensorComparison.ext {A C : WeaklyPointedSuperfusion.{0, 0}}
    {S T : SimpleObject A} {U V : SimpleObject C}
    {E : SpanSuperfunctor A C S.data.object U.data.object}
    {H : SpanSuperfunctor A C T.data.object V.data.object}
    {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object} {a : ZMod 2}
    {η θ : TensorComparison S T U V E H N a}
    (h : ∀ X Y, (η.data.app X Y).hom = (θ.data.app X Y).hom) : η = θ := by
  have he : η.data.app = θ.data.app := by
    funext X Y
    exact IsoData.eq_of_hom_eq (η.laws.iso X Y) (θ.laws.iso X Y) (h X Y)
  rcases η with ⟨⟨f⟩, hf⟩
  rcases θ with ⟨⟨g⟩, hg⟩
  cases he
  rfl

end RMod.Classification

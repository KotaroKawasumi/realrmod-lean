import RMod.Classification.Proofs.IsoEqualityMaps

/-!
# Equality maps for dependent families of component morphisms

An equality of component indices transports the actual incoming or
outgoing map by precisely the induced equality isomorphism of objects.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} (P : I → C.data.Obj)

theorem indexed_map_to_eq {X : C.data.Obj} (q : ∀ i, C.data.Hom X (P i))
    {i j : I} (h : i = j) :
    C.data.comp (q j) (IsoData.ofEq C.data (congrArg P h)).inv = q i := by
  subst j
  exact C.laws.comp_id _

theorem indexed_map_from_eq {X : C.data.Obj} (q : ∀ i, C.data.Hom (P i) X)
    {i j : I} (h : i = j) :
    C.data.comp (IsoData.ofEq C.data (congrArg P h)).hom (q j) = q i := by
  subst j
  exact C.laws.id_comp _

end RMod.Classification

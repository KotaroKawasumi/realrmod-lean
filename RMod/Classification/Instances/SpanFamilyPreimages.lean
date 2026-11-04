import RMod.Classification.Abstract.SpanFamilyPreimages

/-! # The specified counit maps as Mathlib isomorphisms -/

set_option autoImplicit false

namespace RMod.Classification.SpanFamilyPreimages

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {I : Type} {S : I → C.data.Obj}
  {F : SpanFamilyCategory C S ⥤ LinearCategory C} (p : SpanFamilyPreimages C S F)

def counitIso (X : LinearCategory C) : F.obj (p.data.family X) ≅ X where
  hom := (p.data.iso X).hom
  inv := (p.data.iso X).inv
  hom_inv_id := (p.laws.evenIso X).hom_inv
  inv_hom_id := (p.laws.evenIso X).inv_hom

end RMod.Classification.SpanFamilyPreimages

import RMod.Classification.Proofs.SpanFamilySum

/-! # The completed finite-sum functor of homogeneous component families -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def spanFamilySum (C : WeaklyPointedSuperfusion.{0, 0})
    {I : Type} [Fintype I] (S : I → C.data.Obj) : SpanFamilyCategory C S ⥤ LinearCategory C where
  obj := (spanFamilySumData C S).obj
  map := (spanFamilySumData C S).map
  map_id := spanFamilySum_map_id C S
  map_comp := spanFamilySum_map_comp C S

end RMod.Classification

import RMod.Classification.Abstract.Normalizers

/-!
# Homogeneous laws on specified isomorphism data

The existing isomorphism data already retain both maps. This purely
propositional refinement records their common degree, allowing the same
data to be used when composing or tensoring comparison maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

structure HomogeneousIsoLaws (C : WeaklyPointedSuperfusionData.{u, v})
    (a : ZMod 2) {X Y : C.Obj} (d : IsoData C X Y) : Prop extends IsoLaws C d where
  hom_grade : C.IsHomogeneous a d.hom
  inv_grade : C.IsHomogeneous a d.inv

end RMod.Classification

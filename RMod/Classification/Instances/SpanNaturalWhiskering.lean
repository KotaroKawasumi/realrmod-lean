import RMod.Classification.Instances.SpanNaturalIso
import RMod.Classification.Instances.SpanSuperfunctorComposition

/-!
# Whiskering a signed natural isomorphism with a superfunctor

Precomposition evaluates the existing maps on the new source objects.
Postcomposition applies the given superfunctor to both maps. Real
linearity and parity preservation retain the same signed naturality law.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNatIso

open CategoryTheory

variable {B A C D : WeaklyPointedSuperfusion.{0, 0}}
  {R : B.data.Obj} {S : A.data.Obj} {T : C.data.Obj} {U : D.data.Obj}

def precomposeData {F G : SpanSuperfunctorData A C S T}
    (K : SpanSuperfunctorData B A R S) (η : SpanHomogeneousNatIsoData F G) :
    SpanHomogeneousNatIsoData (SpanSuperfunctor.compData K F) (SpanSuperfunctor.compData K G) where
  app X := η.app (K.obj X)
  inv.app X := η.inv.app (K.obj X)

theorem precomposeLaws {F G : SpanSuperfunctor A C S T} {a : ZMod 2}
    (K : SpanSuperfunctor B A R S) (η : SpanHomogeneousNatIso F G a) :
    SpanHomogeneousNatIsoLaws a (precomposeData K.data η.data) where
  grade X := η.laws.grade (K.data.obj X)
  naturality f hf := η.laws.naturality (K.data.map f) (K.laws.map_grade f hf)
  inverse.grade X := η.laws.inverse.grade (K.data.obj X)
  inverse.naturality f hf := η.laws.inverse.naturality (K.data.map f) (K.laws.map_grade f hf)
  hom_inv X := η.laws.hom_inv (K.data.obj X)
  inv_hom X := η.laws.inv_hom (K.data.obj X)

def precompose {F G : SpanSuperfunctor A C S T} {a : ZMod 2}
    (η : SpanHomogeneousNatIso F G a) (K : SpanSuperfunctor B A R S) :
    SpanHomogeneousNatIso (K.comp F) (K.comp G) a :=
  ⟨precomposeData K.data η.data, precomposeLaws K η⟩

def postcomposeData {F G : SpanSuperfunctorData A C S T}
    (H : SpanSuperfunctorData C D T U) (η : SpanHomogeneousNatIsoData F G) :
    SpanHomogeneousNatIsoData (SpanSuperfunctor.compData F H) (SpanSuperfunctor.compData G H) where
  app X := H.map (η.app X)
  inv.app X := H.map (η.inv.app X)

theorem postcomposeLaws {F G : SpanSuperfunctor A C S T} {a : ZMod 2}
    (H : SpanSuperfunctor C D T U) (η : SpanHomogeneousNatIso F G a) :
    SpanHomogeneousNatIsoLaws a (postcomposeData H.data η.data) where
  grade X := H.laws.map_grade _ (η.laws.grade X)
  naturality f hf := (H.laws.map_comp _ _).symm.trans
    ((congrArg H.data.map (η.laws.naturality f hf)).trans
      ((H.laws.map_smul _ _).trans (congrArg (fun q => _ • q) (H.laws.map_comp _ _))))
  inverse.grade X := H.laws.map_grade _ (η.laws.inverse.grade X)
  inverse.naturality f hf := (H.laws.map_comp _ _).symm.trans
    ((congrArg H.data.map (η.laws.inverse.naturality f hf)).trans
      ((H.laws.map_smul _ _).trans (congrArg (fun q => _ • q) (H.laws.map_comp _ _))))
  hom_inv X := (H.laws.map_comp _ _).symm.trans
    ((congrArg H.data.map (η.laws.hom_inv X)).trans (H.laws.map_id _))
  inv_hom X := (H.laws.map_comp _ _).symm.trans
    ((congrArg H.data.map (η.laws.inv_hom X)).trans (H.laws.map_id _))

def postcompose {F G : SpanSuperfunctor A C S T} {a : ZMod 2}
    (η : SpanHomogeneousNatIso F G a) (H : SpanSuperfunctor C D T U) :
    SpanHomogeneousNatIso (F.comp H) (G.comp H) a :=
  ⟨postcomposeData H.data η.data, postcomposeLaws H η⟩

end RMod.Classification.SpanHomogeneousNatIso

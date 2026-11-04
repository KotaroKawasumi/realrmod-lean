import RMod.Definitions.WeaklyPointedSuperfusion

/-!
# Specified parity objects

The objects of the classification are triples `(C, π, ζ)`. Both directions
of the odd isomorphism are data. Its degree and inverse equations are laws
on exactly that data. All compositions below use the repository's
diagrammatic order: `comp f g` means `g ∘ f`.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

/-- The extra executable data in a specified monoidal Π-structure. -/
structure PiData (C : WeaklyPointedSuperfusionData.{u, v}) where
  object : C.Obj
  hom : C.Hom object C.tensorUnit
  inv : C.Hom C.tensorUnit object

/-- The specified comparison with the unit is an odd isomorphism. -/
structure PiLaws (C : WeaklyPointedSuperfusionData.{u, v})
    (d : PiData C) : Prop where
  hom_odd : C.IsHomogeneous 1 d.hom
  inv_odd : C.IsHomogeneous 1 d.inv
  hom_inv : C.comp d.hom d.inv = C.id d.object
  inv_hom : C.comp d.inv d.hom = C.id C.tensorUnit

/-- A chosen parity object and its verified comparison. -/
structure Pi (C : WeaklyPointedSuperfusionData.{u, v}) where
  data : PiData C
  laws : PiLaws C data

/-- Data of a structured classification object; the parent is parent data. -/
structure PiSuperfusionData extends WeaklyPointedSuperfusionData.{u, v} where
  pi : PiData toWeaklyPointedSuperfusionData

/-- The parent laws and parity laws depend on the corresponding projections. -/
structure PiSuperfusionLaws (d : PiSuperfusionData.{u, v}) : Prop
    extends WeaklyPointedSuperfusionLaws d.toWeaklyPointedSuperfusionData where
  pi : PiLaws d.toWeaklyPointedSuperfusionData d.pi

/-- A weakly pointed split-unit real fusion monoidal Π-supercategory. -/
structure PiSuperfusion where
  data : PiSuperfusionData.{u, v}
  laws : PiSuperfusionLaws data

/-- Forget only the specified parity object, retaining the category laws. -/
def PiSuperfusion.toWeaklyPointedSuperfusion (C : PiSuperfusion.{u, v}) :
    WeaklyPointedSuperfusion.{u, v} where
  data := C.data.toWeaklyPointedSuperfusionData
  laws := C.laws.toWeaklyPointedSuperfusionLaws

end RMod.Classification

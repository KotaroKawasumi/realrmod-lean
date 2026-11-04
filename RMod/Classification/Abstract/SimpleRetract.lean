import RMod.Classification.Abstract.SimpleObjects

/-!
# A specified simple even retract

Retain the simple object's carrier and the two retraction maps as Data.
The Laws inherit simplicity of that carrier and add the inverse and
evenness conditions on those exact maps.
-/

set_option autoImplicit false

namespace RMod.Classification

structure SimpleRetractData (C : WeaklyPointedSuperfusionData.{0, 0}) (X : C.Obj)
    extends SimpleObjectData C where
  inclusion : C.Hom object X
  projection : C.Hom X object

structure SimpleRetractLaws {C : WeaklyPointedSuperfusionData.{0, 0}} {X : C.Obj}
    (d : SimpleRetractData C X) : Prop extends SimpleObjectLaws C d.toSimpleObjectData where
  inclusion_projection : C.comp d.inclusion d.projection = C.id d.object
  inclusion_even : C.IsHomogeneous 0 d.inclusion
  projection_even : C.IsHomogeneous 0 d.projection

structure SimpleRetract (C : WeaklyPointedSuperfusion.{0, 0}) (X : C.data.Obj) where
  data : SimpleRetractData C.data X
  laws : SimpleRetractLaws data

end RMod.Classification

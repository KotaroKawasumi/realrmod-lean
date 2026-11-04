import RMod.Definitions.WeaklyPointedSuperfusion

/-!
# Simple objects with separated object data and simplicity laws

The object is retained as data; simplicity is a property of that exact
object. Completed simple objects will index the intrinsic parity-orbit
quotient, without imposing the reference property on the category.
-/

set_option autoImplicit false

namespace RMod.Classification

structure SimpleObjectData (C : WeaklyPointedSuperfusionData.{0, 0}) where
  object : C.Obj

structure SimpleObjectLaws (C : WeaklyPointedSuperfusionData.{0, 0})
    (d : SimpleObjectData C) : Prop where
  simple : C.IsSimple d.object

structure SimpleObject (C : WeaklyPointedSuperfusion.{0, 0}) where
  data : SimpleObjectData C.data
  laws : SimpleObjectLaws C.data data

end RMod.Classification

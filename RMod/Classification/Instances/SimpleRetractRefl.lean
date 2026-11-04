import RMod.Classification.Abstract.SimpleRetract

/-!
# A simple object as its own specified even retract

Both retraction maps are the identity. This supplies the simple retract
required to realize an algebra map on the tensor unit itself.
-/

set_option autoImplicit false

namespace RMod.Classification

def simpleRetractReflData {C : WeaklyPointedSuperfusionData.{0, 0}} (S : SimpleObjectData C) :
    SimpleRetractData C S.object where
  toSimpleObjectData := S
  inclusion := C.id S.object
  projection := C.id S.object

theorem simpleRetractReflLaws {C : WeaklyPointedSuperfusion.{0, 0}} (S : SimpleObject C) :
    SimpleRetractLaws (simpleRetractReflData S.data) where
  toSimpleObjectLaws := S.laws
  inclusion_projection := C.laws.comp_id _
  inclusion_even := C.laws.id_even _
  projection_even := C.laws.id_even _

def simpleRetractRefl {C : WeaklyPointedSuperfusion.{0, 0}} (S : SimpleObject C) :
    SimpleRetract C S.data.object := ⟨simpleRetractReflData S.data, simpleRetractReflLaws S⟩

end RMod.Classification

import RMod.Classification.Instances.EndDualHom
import RMod.Classification.Instances.TensorEndomorphisms

/-!
# Slicing a tensor endomorphism by a real functional

Insert the even unit vector for the left dual, apply id(L) tensor T, and
contract with the cap representing the functional. Associators and unitors
are included explicitly. Every map used in the slice is constructed from
the category and the selected dual pairing.
-/

set_option autoImplicit false

namespace RMod.Classification.DualPairing

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {L X : C.data.Obj}
  (p : DualPairing C L X) (Y : C.data.Obj)

def slicePre : C.data.Hom Y (C.data.tensorObj L (C.data.tensorObj X Y)) :=
  C.data.comp (C.data.leftUnitorInv Y)
    (C.data.comp (C.data.tensorHom p.endUnitVector (C.data.id Y)) (C.data.associatorHom L X Y))

noncomputable def slicePost (φ : Module.Dual ℝ (End (C := LinearCategory C) X)) :
    C.data.Hom (C.data.tensorObj L (C.data.tensorObj X Y)) Y :=
  C.data.comp (C.data.associatorInv L X Y)
    (C.data.comp (C.data.tensorHom (p.endCap φ) (C.data.id Y)) (C.data.leftUnitorHom Y))

noncomputable def endSlice (φ : Module.Dual ℝ (End (C := LinearCategory C) X)) :
    End (C := LinearCategory C) (C.data.tensorObj X Y) →ₗ[ℝ] End (C := LinearCategory C) Y where
  toFun T := C.data.comp (p.slicePre Y)
    (C.data.comp (C.data.tensorHom (C.data.id L) T) (p.slicePost Y φ))
  map_add' S T := by
    change C.data.comp (p.slicePre Y)
        (C.data.comp (C.data.tensorHom (C.data.id L) (C.data.add S T)) (p.slicePost Y φ)) = _
    rw [C.laws.tensor_add_right, C.laws.add_comp, C.laws.comp_add]
    rfl
  map_smul' r T := by
    change C.data.comp (p.slicePre Y)
        (C.data.comp (C.data.tensorHom (C.data.id L) (C.data.smul r T)) (p.slicePost Y φ)) = _
    rw [C.laws.tensor_smul_right, C.laws.smul_comp, C.laws.comp_smul]
    rfl

end RMod.Classification.DualPairing

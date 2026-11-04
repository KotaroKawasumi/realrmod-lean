import RMod.Classification.Abstract.SimpleRetract
import RMod.Classification.Proofs.Grading

/-!
# The projector of a specified simple retract

The projector uses only the inclusion and projection maps. Its
idempotence, degree and nonvanishing follow from the completed retract
laws and simplicity of its retained object.
-/

set_option autoImplicit false

namespace RMod.Classification.SimpleRetract

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X : C.data.Obj}

def projectorData (d : SimpleRetractData C.data X) : C.data.Hom X X :=
  C.data.comp d.projection d.inclusion

theorem projector_even (d : SimpleRetract C X) : C.data.IsHomogeneous 0 (projectorData d.data) := by
  have h := C.laws.comp_grade _ _ d.laws.projection_even d.laws.inclusion_even
  rw [zero_add] at h
  exact h

theorem projector_idempotent (d : SimpleRetract C X) :
    C.data.comp (projectorData d.data) (projectorData d.data) = projectorData d.data := by
  change C.data.comp (C.data.comp d.data.projection d.data.inclusion)
    (C.data.comp d.data.projection d.data.inclusion) = _
  rw [C.laws.comp_assoc, ← C.laws.comp_assoc d.data.inclusion, d.laws.inclusion_projection,
    C.laws.id_comp]
  rfl

theorem projector_ne_zero (d : SimpleRetract C X) : projectorData d.data ≠ C.data.zero := by
  intro hz
  have hh : C.data.comp d.data.inclusion (C.data.comp (projectorData d.data) d.data.projection) =
      C.data.id d.data.object := by
    change C.data.comp d.data.inclusion
      (C.data.comp (C.data.comp d.data.projection d.data.inclusion) d.data.projection) = _
    rw [C.laws.comp_assoc d.data.projection, d.laws.inclusion_projection, C.laws.comp_id,
      d.laws.inclusion_projection]
  rw [hz, raw_zero_comp C.laws, raw_comp_zero C.laws] at hh
  exact simple_id_ne_zero C.laws d.laws.simple hh.symm

end RMod.Classification.SimpleRetract

import RMod.Classification.Instances.SimpleRetractCoordinates

/-!
# The endomorphism corner identities

Compression is a left inverse to expansion. Expanding a compression
inserts the retract projector on both sides. Expansion preserves
composition and has exactly the projector as its image of the unit.
-/

set_option autoImplicit false

namespace RMod.Classification.SimpleRetract

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X : LinearCategory C} (d : SimpleRetract C X)

theorem expand_id : expand C d.data (𝟙 _) = projectorData d.data := by
  change C.data.comp d.data.projection (C.data.comp (C.data.id _) d.data.inclusion) = _
  rw [C.laws.id_comp]
  rfl

theorem compress_expand (f : @End (LinearCategory C) _ d.data.object) :
    compress C d.data (expand C d.data f) = f := by
  change C.data.comp d.data.inclusion
    (C.data.comp (C.data.comp d.data.projection (C.data.comp f d.data.inclusion)) d.data.projection) = f
  rw [C.laws.comp_assoc d.data.projection, C.laws.comp_assoc f, d.laws.inclusion_projection,
    C.laws.comp_id, ← C.laws.comp_assoc, d.laws.inclusion_projection, C.laws.id_comp]

theorem expand_injective : Function.Injective (expand C d.data) :=
  Function.LeftInverse.injective (compress_expand d)

theorem expand_compress (f : End X) : expand C d.data (compress C d.data f) =
    C.data.comp (projectorData d.data) (C.data.comp f (projectorData d.data)) := by
  change C.data.comp d.data.projection
    (C.data.comp (C.data.comp d.data.inclusion (C.data.comp f d.data.projection)) d.data.inclusion) =
      C.data.comp (C.data.comp d.data.projection d.data.inclusion)
        (C.data.comp f (C.data.comp d.data.projection d.data.inclusion))
  simp only [C.laws.comp_assoc]

theorem expand_comp (f g : @End (LinearCategory C) _ d.data.object) :
    expand C d.data (f ≫ g) = expand C d.data f ≫ expand C d.data g := by
  change C.data.comp d.data.projection (C.data.comp (C.data.comp f g) d.data.inclusion) =
    C.data.comp (C.data.comp d.data.projection (C.data.comp f d.data.inclusion))
      (C.data.comp d.data.projection (C.data.comp g d.data.inclusion))
  simp only [C.laws.comp_assoc]
  rw [← C.laws.comp_assoc d.data.inclusion, d.laws.inclusion_projection, C.laws.id_comp]

theorem projector_expand (f : @End (LinearCategory C) _ d.data.object) :
    C.data.comp (projectorData d.data) (expand C d.data f) = expand C d.data f := by
  change C.data.comp (C.data.comp d.data.projection d.data.inclusion)
    (C.data.comp d.data.projection (C.data.comp f d.data.inclusion)) = _
  rw [C.laws.comp_assoc, ← C.laws.comp_assoc d.data.inclusion, d.laws.inclusion_projection,
    C.laws.id_comp]
  rfl

theorem expand_projector (f : @End (LinearCategory C) _ d.data.object) :
    C.data.comp (expand C d.data f) (projectorData d.data) = expand C d.data f := by
  change C.data.comp (C.data.comp d.data.projection (C.data.comp f d.data.inclusion))
    (C.data.comp d.data.projection d.data.inclusion) = _
  rw [C.laws.comp_assoc, C.laws.comp_assoc f, ← C.laws.comp_assoc d.data.inclusion,
    d.laws.inclusion_projection, C.laws.id_comp]
  rfl

end RMod.Classification.SimpleRetract

import RMod.Classification.Instances.SimpleRetract

/-!
# Linear expansion and compression at a simple retract

Mathlib's linear pre- and post-composition maps expand an endomorphism
of the retract to its corner, and compress an ambient endomorphism back.
These operations use only the retained inclusion and projection data.
-/

set_option autoImplicit false

namespace RMod.Classification.SimpleRetract

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) {X : LinearCategory C}

def expand (d : SimpleRetractData C.data X) :
    @End (LinearCategory C) _ d.object →ₗ[ℝ] End X :=
  (Linear.leftComp ℝ (C := LinearCategory C) X d.projection).comp
    (Linear.rightComp ℝ (C := LinearCategory C) d.object d.inclusion)

def compress (d : SimpleRetractData C.data X) :
    End X →ₗ[ℝ] @End (LinearCategory C) _ d.object :=
  (Linear.leftComp ℝ (C := LinearCategory C) d.object d.inclusion).comp
    (Linear.rightComp ℝ (C := LinearCategory C) X d.projection)

end RMod.Classification.SimpleRetract

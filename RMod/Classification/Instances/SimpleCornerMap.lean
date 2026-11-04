import RMod.Classification.Instances.SimpleRetractCoordinates

/-!
# The map between two specified simple corners

Expand in the source, apply the ambient algebra equivalence, and compress
in the target. The map is defined before imposing the equality of the
two projectors; that equality supplies its algebra and inverse laws.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

def simpleCornerMap (C D : WeaklyPointedSuperfusion.{0, 0})
    {X : LinearCategory C} {Y : LinearCategory D}
    (d : SimpleRetractData C.data X) (t : SimpleRetractData D.data Y)
    (φ : End X ≃ₐ[ℝ] End Y) :
    @End (LinearCategory C) _ d.object →ₗ[ℝ] @End (LinearCategory D) _ t.object :=
  (SimpleRetract.compress D t).comp (φ.toLinearMap.comp (SimpleRetract.expand C d))

end RMod.Classification

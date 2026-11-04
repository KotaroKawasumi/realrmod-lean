import RMod.BrundanEllis.StackingDeletionCorrection
import RMod.BrundanEllis.StackingReferenceShuffleCochain

/-! Identify the scalar extracted from actual triple comparison routes with the explicit deletion-correction cochain. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open Superfusion RMod.Classification

/-- The correction read from the actual triple routes is exactly the
cochain used by comparisonTwist. Only the two input parity cocycles are
needed to simplify the two deletion phases. -/
theorem deletionCorrection_eq_referenceTriple {G : FiniteGrp.{0}}
    (r t : G →* Multiplicative (ZMod 8)) (v w : G → G → ZMod 2) (g h k : G)
    (hp : v g h + v (g * h) k = v h k + v g (h * k))
    (hq : w g h + w (g * h) k = w h k + w g (h * k)) :
    deletionCorrection r t v w g h k =
      ((v (g * h) k * w g h + v g h * w g h + v (g * h) k * w (g * h) k +
        (v (g * h) k + w (g * h) k + ReferenceCommutor.degree ((r g).toAdd + (r h).toAdd) (t k).toAdd) *
          ReferenceCommutor.degree (r g).toAdd (t h).toAdd +
        (ReferenceCommutor.rightDefect (r g).toAdd (r h).toAdd (t k).toAdd +
          ReferenceCommutor.degree (r g).toAdd (t h).toAdd * ReferenceCommutor.degree (r h).toAdd (t k).toAdd)) +
        (v g (h * k) * w h k + v h k * w h k + v g (h * k) * w g (h * k) +
          (v g (h * k) + w g (h * k) + ReferenceCommutor.degree (r g).toAdd ((t h).toAdd + (t k).toAdd)) *
            ReferenceCommutor.degree (r h).toAdd (t k).toAdd)) := by
  have hh := deletion_phase (v g h) (v (g * h) k) (v h k) (v g (h * k))
    (w g h) (w (g * h) k) (w h k) (w g (h * k))
    (ReferenceCommutor.degree (r g).toAdd (t h).toAdd)
    (ReferenceCommutor.degree (r h).toAdd (t k).toAdd) hp hq
    (ReferenceCommutor.degree ((r g).toAdd + (r h).toAdd) (t k).toAdd)
    (ReferenceCommutor.degree (r g).toAdd ((t h).toAdd + (t k).toAdd))
  rw [show ∀ x y z : ZMod 2, (x + z) + y = (x + y) + z by intros; ring]
  rw [hh]
  simp only [deletionCorrection, cupOne, sumNu, cross, map_mul, bwBit_mul,
    referenceDegree_add_left, referenceDegree_add_right, ReferenceCommutor.degree,
    ReferenceCommutor.rightDefect, bwBit, bwPrimitive]
  simp only [toAdd_mul]
  ring

end RMod.BrundanEllis.Stacking

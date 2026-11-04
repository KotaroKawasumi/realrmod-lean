import RMod.BrundanEllis.StackingReferenceShuffleAssociativity
import RMod.BrundanEllis.StackingReferenceCrossingGauge

/-! Identify the type-dependent part of crossingCorrection with the actual reference shuffle defect. The remaining cup-one terms come from parity factors. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace RMod.BrundanEllis.Stacking

/-- The type-dependent part of the specified crossing correction is the
actual defect of the six-object reference shuffle. -/
theorem crossingCorrection_eq_referenceShuffle {G : FiniteGrp.{0}}
    (r t : G →* Multiplicative (ZMod 8)) (v w : G → G → ZMod 2) (g h k : G) :
    crossingCorrection r t v w g h k =
      cupOne w v g h k + cupOne (cross r t) (fun a b => v a b + w a b) g h k +
        (ReferenceCommutor.rightDefect (r g).toAdd (r h).toAdd (t k).toAdd +
          ReferenceCommutor.degree (r g).toAdd (t h).toAdd *
            ReferenceCommutor.degree (r h).toAdd (t k).toAdd) := by
  simp only [crossingCorrection, ReferenceCommutor.rightDefect,
    ReferenceCommutor.degree, bwBit, bwPrimitive]
  ring

end RMod.BrundanEllis.Stacking

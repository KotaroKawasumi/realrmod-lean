import RMod.BrundanEllis.StackingReferenceCochainOrientation
import RMod.BrundanEllis.StackingTypeCoherence

/-! Explicit scalar gauge relating the two placements of the quadratic
primitive.  This is a cochain identity; categorical hexagon coherence is
a separate obligation, not an input to these definitions. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- The normalized binary scalar exponent which moves the quadratic primitive. -/
def crossingPrimitive (r t : G →* Multiplicative (ZMod 8)) (g h : G) : ZMod 2 :=
  bwPrimitive (r g) * bwPrimitive (t h)

/-- The alternative correction, with the quadratic primitive on the final t-label. -/
def crossingCorrection (r t : G →* Multiplicative (ZMod 8)) (v w : G → G → ZMod 2)
    (g h k : G) : ZMod 2 :=
  cupOne w v g h k + cupOne (cross r t) (fun a b => v a b + w a b) g h k +
    (bwBit (r g) * bwBit (r h) * bwPrimitive (t k) +
      bwBit (r g) * (bwBit (r h) * bwBit (t h)) * bwBit (t k))

theorem crossingPrimitive_normalized (r t : G →* Multiplicative (ZMod 8)) :
    (∀ g, crossingPrimitive r t 1 g = 0) ∧ (∀ g, crossingPrimitive r t g 1 = 0) := by
  constructor <;> intro g <;> simp [crossingPrimitive]

/-- The two displayed corrections differ by exactly this binary coboundary. -/
theorem crossingCorrection_coboundary (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (g h k : G) :
    correction r t v w g h k + d₂ (crossingPrimitive r t) g h k =
      crossingCorrection r t v w g h k := by
  rw [show d₂ (crossingPrimitive r t) g h k = _ from typeCorrection_other_primitive r t g h k |>.symm]
  simp only [correction, crossingCorrection]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The prescribed gauge convention realizes the change of primitive on scalar cochains. -/
theorem crossingOmega_scalarMove (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (a b : G → G → G → ℝˣ) :
    scalarMove (sumNu r t v w) (stackOmega r t v w a b) (fun _ => 0)
      (fun g h => realSign (crossingPrimitive r t g h)) =
    (fun g h k => a g h k * b g h k * realSign (crossingCorrection r t v w g h k)) := by
  funext g h k
  simp only [scalarMove_ratio, stackOmega, scalarRatio_sign, parityFactor, mul_zero,
    zero_mul, add_zero, realSign_zero, mul_one]
  rw [mul_assoc, ← realSign_add, crossingCorrection_coboundary]

end RMod.BrundanEllis.Stacking

import RMod.BrundanEllis.StackingReferenceCrossingGauge
import Mathlib.FieldTheory.Finite.Basic

/-! Explicit scalar gauges for two parity-deletion conventions. These
cochain identities do not by themselves assert categorical coherence;
they specify the correction available when comparing the actual routes. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- A binary primitive for the cup-one square of the parity crossing. -/
def crossingSelfPrimitive (r t : G →* Multiplicative (ZMod 8)) (g h : G) : ZMod 2 :=
  bwPrimitive (r g) * bwBit (t h) + bwBit (r g) * bwPrimitive (t h)

/-- The two mod-eight lifts make this particular cup-one square exact. -/
theorem crossingSelfPrimitive_data (r t : G →* Multiplicative (ZMod 8)) (g h k : G) :
    d₂ (crossingSelfPrimitive r t) g h k = cupOne (cross r t) (cross r t) g h k := by
  simp only [d₂, crossingSelfPrimitive, cupOne, cross, map_mul, bwBit_mul,
    bwPrimitive_mul, CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.two_eq_zero, ZMod.pow_card]
  ring

/-- Scalar gauge between the two orderings of the parity-deletion terms. -/
def deletionPrimitive (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (g h : G) : ZMod 2 :=
  cross r t g h * (v g h + w g h) + crossingSelfPrimitive r t g h

/-- The correction written with the total output parity in the first cup-one slot.
Its identification with categorical deletion routes is a separate obligation. -/
def deletionCorrection (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (g h k : G) : ZMod 2 :=
  cupOne w v g h k + cupOne (sumNu r t v w) (cross r t) g h k +
    (bwBit (r g) * bwBit (r h) * bwPrimitive (t k) +
      bwBit (r g) * (bwBit (r h) * bwBit (t h)) * bwBit (t k))

theorem deletionPrimitive_normalized (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) :
    (∀ g, deletionPrimitive r t v w 1 g = 0) ∧
      (∀ g, deletionPrimitive r t v w g 1 = 0) := by
  constructor <;> intro g <;> simp [deletionPrimitive, crossingSelfPrimitive, cross]

/-- The displayed change of correction is exactly this scalar coboundary. -/
theorem deletionCorrection_coboundary (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (hw : ∀ g h k, d₂ w g h k = 0) (g h k : G) :
    crossingCorrection r t v w g h k + d₂ (deletionPrimitive r t v w) g h k =
      deletionCorrection r t v w g h k := by
  have hvw : ∀ a b c, d₂ (fun x y => v x y + w x y) a b c = 0 := by
    intro a b c
    have hv' := hv a b c
    have hw' := hw a b c
    simp only [d₂] at hv' hw' ⊢
    linear_combination hv' + hw'
  have hs := d₂_cupTwo₂₂ (cross_cocycle r t) hvw g h k
  have hc := crossingSelfPrimitive_data r t g h k
  simp only [d₂, deletionPrimitive, deletionCorrection, crossingCorrection,
    sumNu, cupOne, cupOne₂₂, cupTwo₂₂, CharTwo.sub_eq_add] at hs hc ⊢
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hs + hc

/-- Ordered inner and outer deletions reduce to the cup-one term and the
crossing against the total output parity. Only the input parity cocycles
are used in this algebraic reduction. -/
theorem deletion_phase (p a b d q e f h x z : ZMod 2)
    (hp : p + a = b + d) (hq : q + e = f + h) (cL cR : ZMod 2) :
    (a * q + p * q + a * e + (a + e + cL) * x) +
      (d * f + b * f + d * h + (d + h + cR) * z) =
    e * p + h * b + (a + e + cL) * x + (d + h + cR) * z := by
  have ha : a = p + b + d := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hp
  have he : e = q + f + h := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hq
  rw [ha, he]
  ring_nf
  simp [CharTwo.two_eq_zero]
  rw [show (3 : ZMod 2) = 1 from rfl, mul_one]


/-- Combine the change of quadratic primitive with the deletion-order gauge. -/
def comparisonGaugeExponent (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (g h : G) : ZMod 2 :=
  crossingPrimitive r t g h + deletionPrimitive r t v w g h

theorem comparisonGaugeExponent_normalized (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) :
    (∀ g, comparisonGaugeExponent r t v w 1 g = 0) ∧
      (∀ g, comparisonGaugeExponent r t v w g 1 = 0) := by
  constructor <;> intro g <;>
    simp [comparisonGaugeExponent, (crossingPrimitive_normalized r t).1,
      (crossingPrimitive_normalized r t).2, (deletionPrimitive_normalized r t v w).1,
      (deletionPrimitive_normalized r t v w).2]

/-- The correction obtained by this algebraic deletion convention differs
from the prescribed correction by a fully explicit normalized scalar gauge. -/
theorem deletionCorrection_from_prescribed (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (hw : ∀ g h k, d₂ w g h k = 0) (g h k : G) :
    correction r t v w g h k + d₂ (comparisonGaugeExponent r t v w) g h k =
      deletionCorrection r t v w g h k := by
  have h₁ := crossingCorrection_coboundary r t v w g h k
  have h₂ := deletionCorrection_coboundary r t v w hv hw g h k
  simp only [comparisonGaugeExponent, d₂] at h₁ h₂ ⊢
  linear_combination h₁ + h₂

/-- The existing scalar gauge convention realizes this explicit correction. -/
theorem deletionOmega_scalarMove (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (hw : ∀ g h k, d₂ w g h k = 0) (a b : G → G → G → ℝˣ) :
    scalarMove (sumNu r t v w) (stackOmega r t v w a b) (fun _ => 0)
      (fun g h => realSign (comparisonGaugeExponent r t v w g h)) =
      (fun g h k => a g h k * b g h k * realSign (deletionCorrection r t v w g h k)) := by
  funext g h k
  simp only [scalarMove_ratio, stackOmega, scalarRatio_sign, parityFactor, mul_zero,
    zero_mul, add_zero, realSign_zero, mul_one]
  rw [mul_assoc, ← realSign_add, deletionCorrection_from_prescribed r t v w hv hw]

end RMod.BrundanEllis.Stacking

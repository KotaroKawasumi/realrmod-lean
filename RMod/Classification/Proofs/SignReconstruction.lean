import RMod.Classification.Proofs.Reconstruction
import RMod.Classification.Proofs.ScalarReplacement
import RMod.Classification.Proofs.SignNormalization
import RMod.Classification.Proofs.EquivalenceComposition

/-!
# Reconstruction with sign-valued associator scalars

Finite averaging already supplies a normalized positive comparison cochain.
Its multiplicative coboundary removes the magnitude of omega. The actual
scalar comparison on each convolution summand gives a monoidal
superequivalence to the sign model; composing with reconstruction proves
the public conclusion for every completed Pi-superfusion category.
-/

set_option autoImplicit false

namespace RMod.Classification

/-- The averaged positive cochain satisfies the equation for the actual
scalar tensorator, with its two composition routes in the stated order. -/
theorem positiveGauge_associativity (t : Twist) (g h k : t.data.group) :
    ((positiveGaugeData t.data).beta g h * (positiveGaugeData t.data).beta (g * h) k) *
      t.data.omega g h k = unitSign (t.data.omega g h k) *
        ((positiveGaugeData t.data).beta h k * (positiveGaugeData t.data).beta g (h * k)) := by
  have he := (positiveGaugeLaws t.laws).omega g h k
  change unitSign (t.data.omega g h k) = t.data.omega g h k *
    ((positiveGaugeData t.data).beta (g * h) k * (positiveGaugeData t.data).beta g h) *
    ((positiveGaugeData t.data).beta h k * (positiveGaugeData t.data).beta g (h * k))⁻¹ *
    realSign (t.data.nu g h * 0 + 0 * t.data.nu h k) at he
  simp only [mul_zero, zero_mul, zero_add, show realSign 0 = 1 from rfl, mul_one] at he
  rw [he, inv_mul_cancel_right]
  ac_rfl

/-- Removing the positive magnitude is realized by a completed monoidal
superequivalence, not just by an equation between parameter tuples. -/
theorem equivalent_signTwist (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : Twist) :
    Equivalent (twistedPullback C hC t) (twistedPullback C hC (signTwist t)) :=
  scalarReplacement_equivalent C hC t (fun g h k => unitSign (t.data.omega g h k))
    (signTwistLaws t.laws) (positiveGaugeData t.data).beta
    (positiveGaugeLaws t.laws).beta_one_left (positiveGaugeLaws t.laws).beta_one_right
    (positiveGauge_associativity t)

/- Use the algebraic real-ring instance appearing in the Mathlib-only
Challenge. The additional normed-ring imports provide a definitionally
equal instance through another projection path; Comparator requires the
advertised statement's actual expression to agree as well. -/
attribute [local instance 2000] CommRing.toNonUnitalCommRing in
theorem sign_reconstruction (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (A : PiSuperfusion.{0, 0}) :
    ∃ t : Twist, (∀ g h k, t.data.omega g h k = 1 ∨ t.data.omega g h k = -1) ∧
      Equivalent A (twistedPullback C hC t) := by
  obtain ⟨t, ht⟩ := reconstruction C hC A
  exact ⟨signTwist t, fun _ _ _ => unitSign_cases _,
    ht.trans (equivalent_signTwist C hC t)⟩

end RMod.Classification

import RMod.Classification.Instances.EquivalenceGaugeData
import RMod.Classification.Proofs.GaugeNuNecessity
import RMod.Classification.Proofs.GaugeComponentUnit
import RMod.Classification.Proofs.GaugeNormalization
import RMod.Classification.Proofs.GaugeComparisonRatio

/-!
# Structural laws and the convention of the extracted gauge data

The retained group isomorphism and parity already satisfy the rho and nu
equations. The raw binary ratio recovers beta with the sign verified for
the actual gauge normalizer. Once its omega equation is established, the
general normalization theorem supplies all unit laws simultaneously.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceUnnormalizedGaugeData_rho (g : s.data.group) :
    t.data.rho ((equivalenceUnnormalizedGaugeData C hC s t E).phi g) = s.data.rho g :=
  equivalenceGaugePhi_rho C hC s t E g

theorem equivalenceUnnormalizedGaugeData_lam_one :
    (equivalenceUnnormalizedGaugeData C hC s t E).lam 1 = 0 :=
  equivalenceGaugeLambda_one C hC s t E

theorem equivalenceUnnormalizedGaugeData_nu (g h : s.data.group) :
    let d := equivalenceUnnormalizedGaugeData C hC s t E
    t.data.nu (d.phi g) (d.phi h) = s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g :=
  equivalenceGaugeLambda_nu C hC s t E g h

/-- This is the coefficient in the comparison-ratio theorem for the
specified local gauge tensorator with the extracted beta. -/
theorem equivalenceUnnormalizedGaugeData_ratio (g h : s.data.group) :
    let d := equivalenceUnnormalizedGaugeData C hC s t E
    (d.beta g h)⁻¹ * realSign (d.lam g * d.lam h +
      (d.lam g + d.lam h) * t.data.nu (d.phi g) (d.phi h) + d.lam (g * h) * s.data.nu g h) =
        equivalenceGaugeRatio C hC s t E g h := by
  dsimp only [equivalenceUnnormalizedGaugeData]
  rw [mul_inv_rev, inv_inv, mul_comm _ (equivalenceGaugeRatio C hC s t E g h),
    mul_assoc, inv_mul_cancel, mul_one]

end RMod.Classification

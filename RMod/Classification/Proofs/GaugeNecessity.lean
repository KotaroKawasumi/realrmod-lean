import RMod.Classification.Proofs.GaugeOmegaNecessity

/-!
# A gauge is extracted from every equivalence

The extracted group map, component parities and binary ratios satisfy the
rho, nu and omega equations. Normalize the common unit value of beta and
then bundle the constructed data with their laws. No extra compatibility
or chosen form of the original monoidal equivalence is assumed.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem gauge_of_equivalent (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (h : Equivalent (twistedPullback C hC s) (twistedPullback C hC t)) :
    GaugeEquivalent s.data t.data := by
  obtain ⟨E⟩ := h
  exact ⟨⟨normalizedGaugeData (equivalenceUnnormalizedGaugeData C hC s t E),
    normalizedGaugeLaws s t (equivalenceUnnormalizedGaugeData C hC s t E)
      (equivalenceUnnormalizedGaugeData_lam_one C hC s t E)
      (equivalenceUnnormalizedGaugeData_omega C hC s t E)
      (equivalenceUnnormalizedGaugeData_rho C hC s t E)
      (equivalenceUnnormalizedGaugeData_nu C hC s t E)⟩⟩

end RMod.Classification

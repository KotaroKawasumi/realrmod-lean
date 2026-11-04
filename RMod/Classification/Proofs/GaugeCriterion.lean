import RMod.Classification.Proofs.GaugeNecessity
import RMod.Classification.Proofs.GaugeSufficiency

/-!
# The necessary-and-sufficient gauge classification

The reference category is arbitrary subject to P. Necessity extracts a
normalized gauge from an actual equivalence; sufficiency constructs an
actual strong monoidal superequivalence from those gauge data and laws.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem equivalence_iff_gauge (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (s t : Twist) :
    Equivalent (twistedPullback C hC s) (twistedPullback C hC t) ↔
      GaugeEquivalent s.data t.data :=
  ⟨gauge_of_equivalent C hC s t, equivalent_of_gauge C hC s t⟩

end RMod.Classification

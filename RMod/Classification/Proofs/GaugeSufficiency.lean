import RMod.Classification.Proofs.GaugeAssociativity
import RMod.Classification.Proofs.GaugeMonoidalAssembly
import RMod.Classification.Proofs.GaugeEquivalenceAssembly

/-!
# Every gauge equivalence gives an actual monoidal superequivalence

All forward coherence laws now follow from the gauge laws for the
specified maps. The already constructed inverse and even natural
cancellation maps supply the completed equivalence on full Hom spaces.
This proves the sufficiency direction of the public gauge criterion.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hd : GaugeLaws s.data t.data d)

theorem gaugeMonoidalFunctorLaws :
    MonoidalSuperfunctorLaws (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (gaugeMonoidalFunctorData C hC s t d hd.rho hd.nu hd.lam_one) :=
  gaugeMonoidalFunctorLaws_of_associativity C hC s t d hd.rho hd.nu hd.lam_one
    hd.beta_one_left hd.beta_one_right (gaugeTensorator_associativity C hC s t d hd)

theorem gaugeSuperequivalenceLaws :
    MonoidalSuperequivalenceLaws (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (gaugeSuperequivalenceData C hC s t d hd.rho hd.nu hd.lam_one) :=
  gaugeSuperequivalenceLaws_of_monoidal C hC s t d hd.rho hd.nu hd.lam_one
    (gaugeMonoidalFunctorLaws C hC s t d hd)

omit d hd in
theorem equivalent_of_gauge (h : GaugeEquivalent s.data t.data) :
    Equivalent (twistedPullback C hC s) (twistedPullback C hC t) := by
  obtain ⟨g⟩ := h
  exact ⟨⟨gaugeSuperequivalenceData C hC s t g.data g.laws.rho g.laws.nu g.laws.lam_one,
    gaugeSuperequivalenceLaws C hC s t g.data g.laws⟩⟩

end RMod.Classification

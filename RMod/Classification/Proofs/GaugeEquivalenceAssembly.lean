import RMod.Classification.Instances.GaugeMonoidalData
import RMod.Classification.Proofs.GaugeInverseFunctor

/-!
# The specified inverse upgrades a monoidal gauge functor to an equivalence

The only input here is monoidal coherence of the already constructed
forward maps. The explicit inverse and both natural cancellation maps
supply every remaining equivalence law, on arbitrary full Hom spaces.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
  (hlam : d.lam 1 = 0)

theorem gaugeSuperequivalenceLaws_of_monoidal
    (hF : MonoidalSuperfunctorLaws (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (gaugeMonoidalFunctorData C hC s t d hρ hν hlam)) :
    MonoidalSuperequivalenceLaws (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (gaugeSuperequivalenceData C hC s t d hρ hν hlam) where
  forward := hF
  backward := (gaugeInverseUnderlyingFunctor C hC s t d.phi d.lam hρ).laws
  unit_hom_even X := (gaugeSourceCancellation_evenIso C hC s t d.phi d.lam hρ X).inv_even
  unit_inv_even X := (gaugeSourceCancellation_evenIso C hC s t d.phi d.lam hρ X).hom_even
  unit_hom_inv X := (gaugeSourceCancellation_evenIso C hC s t d.phi d.lam hρ X).inv_hom
  unit_inv_hom X := (gaugeSourceCancellation_evenIso C hC s t d.phi d.lam hρ X).hom_inv
  counit_hom_even Y := (gaugeTargetCancellation_evenIso C hC s t d.phi d.lam hρ Y).hom_even
  counit_inv_even Y := (gaugeTargetCancellation_evenIso C hC s t d.phi d.lam hρ Y).inv_even
  counit_hom_inv Y := (gaugeTargetCancellation_evenIso C hC s t d.phi d.lam hρ Y).hom_inv
  counit_inv_hom Y := (gaugeTargetCancellation_evenIso C hC s t d.phi d.lam hρ Y).inv_hom
  unit_naturality f := iso_naturality_symm (twistedPullback C hC s).laws.toWeaklyPointedSuperfusionLaws
    (gaugeSourceCancellation_evenIso C hC s t d.phi d.lam hρ _).toIsoLaws
    (gaugeSourceCancellation_evenIso C hC s t d.phi d.lam hρ _).toIsoLaws
    (gaugeSourceCancellation_naturality C hC s t d.phi d.lam hρ f)
  counit_naturality f := gaugeTargetCancellation_naturality C hC s t d.phi d.lam hρ f

end RMod.Classification

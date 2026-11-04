import RMod.Classification.Instances.GaugeTensorator
import RMod.Classification.Instances.GaugeUnit
import RMod.Classification.Instances.GaugeInverseFunctor

/-!
# The actual monoidal gauge maps and equivalence data

Bundle the specified tensorator and canonical unit with the reindexing
superfunctor. The inverse superfunctor and both even shift cancellations
are retained explicitly. No coherence condition is hidden in these data;
associativity and the unit diagrams are proved for these very maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
  (hlam : d.lam 1 = 0)

noncomputable def gaugeMonoidalFunctorData :
    MonoidalSuperfunctorData (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData where
  toPrefunctor := (gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data
  tensorHom X Y k := (gaugeTensoratorData C hC s t d hρ hν X Y k).hom
  tensorInv X Y k := (gaugeTensoratorData C hC s t d hρ hν X Y k).inv
  unitHom k := (gaugeUnitComponentData C hC s t d hρ hlam k).hom
  unitInv k := (gaugeUnitComponentData C hC s t d hρ hlam k).inv

noncomputable def gaugeSuperequivalenceData :
    MonoidalSuperequivalenceData (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData where
  forward := gaugeMonoidalFunctorData C hC s t d hρ hν hlam
  backward := (gaugeInverseUnderlyingFunctor C hC s t d.phi d.lam hρ).data
  unitHom X := (gaugeSourceCancellationData C hC s t d.phi d.lam hρ X).inv
  unitInv X := (gaugeSourceCancellationData C hC s t d.phi d.lam hρ X).hom
  counitHom Y := (gaugeTargetCancellationData C hC s t d.phi d.lam hρ Y).hom
  counitInv Y := (gaugeTargetCancellationData C hC s t d.phi d.lam hρ Y).inv

end RMod.Classification

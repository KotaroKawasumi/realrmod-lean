import RMod.Classification.Instances.GaugeInverseFunctor
import RMod.Classification.Proofs.IndexedShiftSquare

/-!
# Both gauge inverse comparisons are even natural isomorphisms

The inverse equations and degrees hold at each group coordinate by the
specified shift-square laws. Indexed naturality proves the two squares
on all raw morphisms, retaining the exact maps of both functors.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (φ : s.data.group ≃* t.data.group) (lam : s.data.group → ZMod 2)
  (hρ : ∀ g, t.data.rho (φ g) = s.data.rho g)

theorem gaugeSourceCancellation_evenIso (X : PullbackObj C s.data) :
    EvenIsoLaws (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (gaugeSourceCancellationData C hC s t φ lam hρ X) where
  hom_inv := funext (fun g =>
    (hC.pi.indexedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
      (fun k => (X k).val) lam (φ.symm_apply_apply g)).hom_inv)
  inv_hom := funext (fun g =>
    (hC.pi.indexedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
      (fun k => (X k).val) lam (φ.symm_apply_apply g)).inv_hom)
  hom_even g := (hC.pi.indexedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
    (fun k => (X k).val) lam (φ.symm_apply_apply g)).hom_even
  inv_even g := (hC.pi.indexedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
    (fun k => (X k).val) lam (φ.symm_apply_apply g)).inv_even

theorem gaugeTargetCancellation_evenIso (Y : PullbackObj C t.data) :
    EvenIsoLaws (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (gaugeTargetCancellationData C hC s t φ lam hρ Y) where
  hom_inv := funext (fun k =>
    (hC.pi.indexedMixedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
      (fun l => (Y l).val) (fun l => lam (φ.symm l)) (φ.apply_symm_apply k)).hom_inv)
  inv_hom := funext (fun k =>
    (hC.pi.indexedMixedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
      (fun l => (Y l).val) (fun l => lam (φ.symm l)) (φ.apply_symm_apply k)).inv_hom)
  hom_even k := (hC.pi.indexedMixedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
    (fun l => (Y l).val) (fun l => lam (φ.symm l)) (φ.apply_symm_apply k)).hom_even
  inv_even k := (hC.pi.indexedMixedShiftSquare_evenIso hC.toWeaklyPointedSuperfusionLaws
    (fun l => (Y l).val) (fun l => lam (φ.symm l)) (φ.apply_symm_apply k)).inv_even

theorem gaugeSourceCancellation_naturality {X Y : PullbackObj C s.data} (f : PullbackHom C s.data X Y) :
    (twistedPullback C hC s).data.comp
      ((gaugeInverseUnderlyingFunctor C hC s t φ lam hρ).data.map
        ((gaugeUnderlyingFunctor C hC s t φ lam hρ).data.map f))
      (gaugeSourceCancellationData C hC s t φ lam hρ Y).hom =
      (twistedPullback C hC s).data.comp (gaugeSourceCancellationData C hC s t φ lam hρ X).hom f :=
  funext (fun g => hC.pi.indexedShiftSquare_naturality hC.toWeaklyPointedSuperfusionLaws
    (fun k => (X k).val) lam (φ.symm_apply_apply g) f)

theorem gaugeTargetCancellation_naturality {X Y : PullbackObj C t.data} (f : PullbackHom C t.data X Y) :
    (twistedPullback C hC t).data.comp
      ((gaugeUnderlyingFunctor C hC s t φ lam hρ).data.map
        ((gaugeInverseUnderlyingFunctor C hC s t φ lam hρ).data.map f))
      (gaugeTargetCancellationData C hC s t φ lam hρ Y).hom =
      (twistedPullback C hC t).data.comp (gaugeTargetCancellationData C hC s t φ lam hρ X).hom f :=
  funext (fun k => hC.pi.indexedMixedShiftSquare_naturality hC.toWeaklyPointedSuperfusionLaws
    (fun l => (X l).val) (fun l => lam (φ.symm l)) (φ.apply_symm_apply k) f)

end RMod.Classification

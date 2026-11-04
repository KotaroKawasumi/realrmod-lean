import RMod.Classification.Instances.GaugeUnderlyingFunctor
import RMod.Classification.Instances.IndexedShiftSquare

/-!
# Inverse reindexing and the actual shift cancellation maps

The inverse uses phi inverse and the transported parity function. Both
composites have two equal right shifts after the forced index equality.
The specified shift-square maps therefore give the unit and counit data.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (φ : s.data.group ≃* t.data.group) (lam : s.data.group → ZMod 2)
  (hρ : ∀ g, t.data.rho (φ g) = s.data.rho g)

include hρ

omit C hC lam in
theorem gaugeInverseRho (k : t.data.group) : s.data.rho (φ.symm k) = t.data.rho k :=
  (hρ (φ.symm k)).symm.trans (congrArg t.data.rho (φ.apply_symm_apply k))

noncomputable def gaugeInverseUnderlyingFunctor :
    Superfunctor (twistedPullback C hC t).toWeaklyPointedSuperfusion
      (twistedPullback C hC s).toWeaklyPointedSuperfusion :=
  gaugeUnderlyingFunctor C hC t s φ.symm (fun k => lam (φ.symm k)) (gaugeInverseRho s t φ hρ)

noncomputable def gaugeSourceCancellationData (X : PullbackObj C s.data) :
    IsoData (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      ((gaugeInverseUnderlyingFunctor C hC s t φ lam hρ).data.obj
        ((gaugeUnderlyingFunctor C hC s t φ lam hρ).data.obj X)) X where
  hom g := (C.pi.indexedShiftSquare (fun k => (X k).val) lam (φ.symm_apply_apply g)).hom
  inv g := (C.pi.indexedShiftSquare (fun k => (X k).val) lam (φ.symm_apply_apply g)).inv

noncomputable def gaugeTargetCancellationData (Y : PullbackObj C t.data) :
    IsoData (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      ((gaugeUnderlyingFunctor C hC s t φ lam hρ).data.obj
        ((gaugeInverseUnderlyingFunctor C hC s t φ lam hρ).data.obj Y)) Y where
  hom k := (C.pi.indexedMixedShiftSquare (fun l => (Y l).val)
    (fun l => lam (φ.symm l)) (φ.apply_symm_apply k)).hom
  inv k := (C.pi.indexedMixedShiftSquare (fun l => (Y l).val)
    (fun l => lam (φ.symm l)) (φ.apply_symm_apply k)).inv

end RMod.Classification

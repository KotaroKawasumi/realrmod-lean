import RMod.Classification.Instances.GaugeProductAssociator
import RMod.Classification.Proofs.GaugeLocalAssociativity
import RMod.Classification.Proofs.GaugeLocalOutputParity

/-!
# Local gauge associativity in the actual target product coordinates

The inverse group isomorphism transports the source cocycle and omega
equation. The two output shifts are identified by group associativity.
The proved local diagram then compares the two specified product routes,
including the equality map of their final parity factors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
  (hω : ∀ g h k, t.data.omega (d.phi g) (d.phi h) (d.phi k) =
    s.data.omega g h k * (d.beta (g * h) k * d.beta g h) *
      (d.beta h k * d.beta g (h * k))⁻¹ *
      realSign (t.data.nu (d.phi g) (d.phi h) * d.lam k + d.lam g * s.data.nu h k))

include hω

theorem gaugeProductLocal_associativity (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    C.comp (C.comp (gaugeProductLeftLocalData C hC s t d hρ hν X Y Z g h k).hom
      (C.tensorHom (gaugeProductSourceAssociatorData C s t d X Y Z g h k).hom
        (C.id (C.pi.factor (d.lam (d.phi.symm ((g * h) * k)))))))
      (gaugeProductRightParityTransportData C s t d X Y Z g h k).hom =
      C.comp (C.pi.localAssociator
        (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) g).val
        (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) h).val
        (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Z) k).val
        (t.data.nu g h) (t.data.nu (g * h) k) (t.data.nu h k) (t.data.nu g (h * k))
        (t.laws.normalizer_parity g h k) (t.data.omega g h k)).hom
        (gaugeProductRightLocalData C hC s t d hρ hν X Y Z g h k).hom := by
  let ef := congrArg (fun j => d.lam (d.phi.symm j)) (mul_assoc g h k)
  have h₄ := (gaugeProductParityTotal d hν g (h * k)).trans
    (congrArg (fun z => s.data.nu (d.phi.symm g) (d.phi.symm (h * k)) + z) ef.symm)
  have hw : t.data.omega g h k =
      s.data.omega (d.phi.symm g) (d.phi.symm h) (d.phi.symm k) *
        (d.beta (d.phi.symm (g * h)) (d.phi.symm k) * d.beta (d.phi.symm g) (d.phi.symm h)) *
        (d.beta (d.phi.symm h) (d.phi.symm k) * d.beta (d.phi.symm g) (d.phi.symm (h * k)))⁻¹ *
        realSign (t.data.nu g h * d.lam (d.phi.symm k) +
          d.lam (d.phi.symm g) * s.data.nu (d.phi.symm h) (d.phi.symm k)) := by
    simpa only [d.phi.apply_symm_apply, map_mul] using hω (d.phi.symm g) (d.phi.symm h) (d.phi.symm k)
  have hl := hC.pi.gaugeLocalTensorator_associativity hC.toWeaklyPointedSuperfusionLaws
    (X (d.phi.symm g)).val (Y (d.phi.symm h)).val (Z (d.phi.symm k)).val
    (d.lam (d.phi.symm g)) (d.lam (d.phi.symm h)) (d.lam (d.phi.symm k))
    (d.lam (d.phi.symm (g * h))) (d.lam (d.phi.symm (h * k))) (d.lam (d.phi.symm ((g * h) * k)))
    (s.data.nu (d.phi.symm g) (d.phi.symm h)) (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k))
    (s.data.nu (d.phi.symm h) (d.phi.symm k)) (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))
    (t.data.nu g h) (t.data.nu (g * h) k) (t.data.nu h k) (t.data.nu g (h * k))
    (gaugeSourceNormalizerParity s t d g h k) (t.laws.normalizer_parity g h k)
    (gaugeProductParityTotal d hν g h) (gaugeProductParityTotal d hν (g * h) k)
    (gaugeProductParityTotal d hν h k) h₄
    (d.beta (d.phi.symm g) (d.phi.symm h)) (d.beta (d.phi.symm (g * h)) (d.phi.symm k))
    (d.beta (d.phi.symm h) (d.phi.symm k)) (d.beta (d.phi.symm g) (d.phi.symm (h * k)))
    (s.data.omega (d.phi.symm g) (d.phi.symm h) (d.phi.symm k)) (t.data.omega g h k) hw
  let q := (gaugeProductRightParityTransportData C s t d X Y Z g h k).hom
  have hg := PiLaws.gaugeLocalTensorator_output_parity hC.toWeaklyPointedSuperfusionLaws C.pi
    (X (d.phi.symm g)).val (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k))
    (d.lam (d.phi.symm g)) (d.lam (d.phi.symm (h * k)))
    (t.data.nu g (h * k)) (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))
    (d.lam (d.phi.symm ((g * h) * k))) (d.lam (d.phi.symm (g * (h * k)))) ef h₄
    (gaugeProductParityTotal d hν g (h * k)) (d.beta (d.phi.symm g) (d.phi.symm (h * k)))
  have hl' := congrArg (fun z => C.comp z q) hl
  refine hl'.trans ?_
  rw [hC.comp_assoc, hC.comp_assoc]
  apply congrArg (C.comp _)
  apply congrArg (C.comp _)
  exact hg

end RMod.Classification

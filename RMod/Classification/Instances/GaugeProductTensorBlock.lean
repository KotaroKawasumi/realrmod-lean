import RMod.Classification.Instances.GaugeTensorBlock
import RMod.Classification.Instances.ConvolutionProductInsertions
import RMod.Classification.Proofs.GaugeProductIndices

/-!
# Gauge blocks and their source inclusions indexed by a target pair

The local comparison uses the two specified target degrees. Its output
parity is evaluated at the inverse image of their product. The inclusion
into the original source convolution retains the complementary-index
equality map; it is tensored with that same output parity factor.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)

noncomputable def gaugeProductTensorBlockData (X Y : PullbackObj C s.data) (g h : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (twistSummand C t.data
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) g h)
      (C.tensorObj (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h))
        (C.pi.factor (d.lam (d.phi.symm (g * h))))) :=
  C.pi.gaugeLocalTensorator (X (d.phi.symm g)).val (Y (d.phi.symm h)).val
    (d.lam (d.phi.symm g)) (d.lam (d.phi.symm h)) (t.data.nu g h)
    (s.data.nu (d.phi.symm g) (d.phi.symm h)) (d.lam (d.phi.symm (g * h)))
    (gaugeProductParityTotal d hν g h) (d.beta (d.phi.symm g) (d.phi.symm h))

noncomputable def gaugeProductBaseInclusion (X Y : PullbackObj C s.data) (g h : t.data.group) :
    C.Hom (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h))
      (convolutionObj C hC s.data X Y (d.phi.symm (g * h))).val :=
  C.comp
    (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (congrArg (twistSummand C s.data X Y (d.phi.symm g)) (gaugeProductComplement d g h))).hom
    (convolutionInclusion C hC s.data X Y (d.phi.symm (g * h)) (d.phi.symm g))

noncomputable def gaugeProductSourceInclusion (X Y : PullbackObj C s.data) (g h : t.data.group) :
    C.Hom (C.tensorObj (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h))
      (C.pi.factor (d.lam (d.phi.symm (g * h)))))
      (C.tensorObj (convolutionObj C hC s.data X Y (d.phi.symm (g * h))).val
        (C.pi.factor (d.lam (d.phi.symm (g * h))))) :=
  C.tensorHom (gaugeProductBaseInclusion C hC s t d X Y g h)
    (C.id (C.pi.factor (d.lam (d.phi.symm (g * h)))))

end RMod.Classification

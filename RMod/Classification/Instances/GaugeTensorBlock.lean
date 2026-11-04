import RMod.Classification.Instances.GaugeUnderlyingFunctor
import RMod.Classification.Instances.GaugeLocalNormalizers
import RMod.Classification.Proofs.GaugeTensorIndices

/-!
# The local gauge tensorator at a fixed target output degree

Use the ordered parity-factor comparison, then retain the equality map
identifying the complementary source index. The scalar beta and both
inverse maps are part of these data. Only the rho and nu equations enter
this construction; the omega equation is reserved for associativity.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def gaugeTensorBlockData
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
    (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
      s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
    (X Y : PullbackObj C s.data) (k l : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (twistSummand C t.data
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) l (l⁻¹ * k))
      (C.tensorObj
        (twistSummand C s.data X Y (d.phi.symm l) ((d.phi.symm l)⁻¹ * d.phi.symm k))
        (C.pi.factor (d.lam (d.phi.symm k)))) :=
  (C.pi.gaugeLocalTensorator (X (d.phi.symm l)).val (Y (d.phi.symm (l⁻¹ * k))).val
    (d.lam (d.phi.symm l)) (d.lam (d.phi.symm (l⁻¹ * k))) (t.data.nu l (l⁻¹ * k))
    (s.data.nu (d.phi.symm l) (d.phi.symm (l⁻¹ * k))) (d.lam (d.phi.symm k))
    (gaugeIndexedParityTotal d hν k l) (d.beta (d.phi.symm l) (d.phi.symm (l⁻¹ * k)))).trans
      C.toWeaklyPointedSuperfusionData
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg (fun q => C.tensorObj (twistSummand C s.data X Y (d.phi.symm l) q)
          (C.pi.factor (d.lam (d.phi.symm k)))) (gaugeComplementaryIndex d k l)))

end RMod.Classification

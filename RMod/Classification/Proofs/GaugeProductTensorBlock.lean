import RMod.Classification.Instances.GaugeProductTensorBlock
import RMod.Classification.Proofs.GaugeTensorator
import RMod.Classification.Proofs.TensorEqualityMaps

/-!
# The actual gauge tensorator on a product-indexed summand

An arbitrary equality identifying the second degree with the original
complementary degree transports the fixed-output block. Equality
elimination retains the specified comparison and its source inclusion.
Specializing to a product gives the insertion formula used on triples.
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

theorem gaugeTensorBlock_index_formula (X Y : PullbackObj C s.data) (k g h : t.data.group)
    (he : h = g⁻¹ * k)
    (hpar : (d.lam (d.phi.symm g) + d.lam (d.phi.symm h)) + t.data.nu g h =
      s.data.nu (d.phi.symm g) (d.phi.symm h) + d.lam (d.phi.symm k))
    (hc : d.phi.symm h = (d.phi.symm g)⁻¹ * d.phi.symm k) :
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (congrArg (twistSummand C t.data
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) g) he)).hom
      (gaugeTensorBlockData C hC s t d hρ hν X Y k g).hom =
      C.comp (C.pi.gaugeLocalTensorator (X (d.phi.symm g)).val (Y (d.phi.symm h)).val
        (d.lam (d.phi.symm g)) (d.lam (d.phi.symm h)) (t.data.nu g h)
        (s.data.nu (d.phi.symm g) (d.phi.symm h)) (d.lam (d.phi.symm k)) hpar
        (d.beta (d.phi.symm g) (d.phi.symm h))).hom
        (C.tensorHom (IsoData.ofEq C.toWeaklyPointedSuperfusionData
          (congrArg (twistSummand C s.data X Y (d.phi.symm g)) hc)).hom
          (C.id (C.pi.factor (d.lam (d.phi.symm k))))) := by
  cases he
  change C.comp (C.id _) (C.comp _ _) = _
  rw [hC.id_comp, isoData_tensorRight_ofEq hC.toWeaklyPointedSuperfusionLaws]

theorem gaugeTensorator_productInclusion (X Y : PullbackObj C s.data) (g h : t.data.group) :
    C.comp (convolutionProductInclusion C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) g h)
      (gaugeTensoratorData C hC s t d hρ hν X Y (g * h)).hom =
      C.comp (gaugeProductTensorBlockData C hC s t d hρ hν X Y g h).hom
        (gaugeProductSourceInclusion C hC s t d X Y g h) := by
  unfold convolutionProductInclusion
  rw [hC.comp_assoc, gaugeTensorator_inclusion, ← hC.comp_assoc,
    gaugeTensorBlock_index_formula C hC s t d hρ hν X Y (g * h) g h
      (inv_mul_cancel_left g h).symm (gaugeProductParityTotal d hν g h) (gaugeProductComplement d g h),
    hC.comp_assoc]
  congr 1
  exact ((tensorRightLaws ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (C.pi.factor (d.lam (d.phi.symm (g * h))))).map_comp _ _).symm

end RMod.Classification

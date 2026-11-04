import RMod.Classification.Instances.GaugeTensorator
import RMod.Classification.Instances.ConvolutionInsertions

/-!
# Invertibility and the summand formula of the gauge tensorator

The even biproduct construction supplies both inverse laws. Cancelling
the convolution comparisons on each inclusion recovers exactly the
prescribed local gauge block and the shifted source inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)

theorem gaugeTensorator_evenIso (X Y : PullbackObj C s.data) (k : t.data.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (gaugeTensoratorData C hC s t d hρ hν X Y k) :=
  evenIsoLaws_ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (gaugeTensoratorEvenIso C hC s t d hρ hν X Y k)

theorem gaugeTensoratorEvenIso_inclusion (X Y : PullbackObj C s.data) (k l : t.data.group) :
    convolutionInclusionEven C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) k l ≫
      (gaugeTensoratorEvenIso C hC s t d hρ hν X Y k).hom =
    (gaugeTensorBlockEvenIso C hC s t d hρ hν X Y k l).hom ≫
      (convolutionInclusionEven C hC s.data X Y (d.phi.symm k) (d.phi.symm l) ▷
        referenceEvenObj C hC (C.pi.factor (d.lam (d.phi.symm k)))) := by
  simp only [convolutionInclusionEven, gaugeTensoratorEvenIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, biproduct.whiskerEquiv_hom,
    biproduct.ι_desc_assoc, Iso.symm_inv, biproduct_ι_comp_rightDistributor_inv_assoc,
    tensorIso_hom, Iso.refl_hom, comp_whiskerRight]
  rfl

theorem gaugeTensorator_inclusion (X Y : PullbackObj C s.data) (k l : t.data.group) :
    C.comp (convolutionInclusion C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) k l)
      (gaugeTensoratorData C hC s t d hρ hν X Y k).hom =
    C.comp (gaugeTensorBlockData C hC s t d hρ hν X Y k l).hom
      (C.tensorHom (convolutionInclusion C hC s.data X Y (d.phi.symm k) (d.phi.symm l))
        (C.id (C.pi.factor (d.lam (d.phi.symm k))))) :=
  congrArg (fun f => f.hom) (gaugeTensoratorEvenIso_inclusion C hC s t d hρ hν X Y k l)

end RMod.Classification

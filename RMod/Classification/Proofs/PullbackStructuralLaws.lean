import RMod.Classification.Instances.TwistedPullbackData
import RMod.Classification.Proofs.ConvolutionAssociator
import RMod.Classification.Proofs.ConvolutionUnitors

/-!
# Structural inverse and parity laws on the constructed data

The componentwise Hom operations lift the proved inverse equations and
degrees to the full pullback. These theorems concern the actual advertised
construction data. They are separate from the remaining naturality,
pentagon, triangle, semisimplicity and duality obligations.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullbackPiLaws :
    PiLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (twistedPullbackData C hC t ht).pi where
  hom_inv := funext (pullbackPi_hom_inv C hC t)
  inv_hom := funext (pullbackPi_inv_hom C hC t)
  hom_odd := pullbackPi_hom_odd C hC t
  inv_odd := pullbackPi_inv_odd C hC t

theorem twistedPullbackAssociator_evenIso (X Y Z : PullbackObj C t) :
    EvenIsoLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (IsoData.assoc (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData X Y Z) where
  hom_inv := funext (fun k => (convolutionAssociator_evenIso C hC t ht X Y Z k).hom_inv)
  inv_hom := funext (fun k => (convolutionAssociator_evenIso C hC t ht X Y Z k).inv_hom)
  hom_even := fun k => (convolutionAssociator_evenIso C hC t ht X Y Z k).hom_even
  inv_even := fun k => (convolutionAssociator_evenIso C hC t ht X Y Z k).inv_even

theorem twistedPullbackLeftUnitor_evenIso (X : PullbackObj C t) :
    EvenIsoLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (IsoData.leftUnit (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData X) where
  hom_inv := funext (fun k => (convolutionLeftUnitor_evenIso C hC t ht X k).hom_inv)
  inv_hom := funext (fun k => (convolutionLeftUnitor_evenIso C hC t ht X k).inv_hom)
  hom_even := fun k => (convolutionLeftUnitor_evenIso C hC t ht X k).hom_even
  inv_even := fun k => (convolutionLeftUnitor_evenIso C hC t ht X k).inv_even

theorem twistedPullbackRightUnitor_evenIso (X : PullbackObj C t) :
    EvenIsoLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (IsoData.rightUnit (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData X) where
  hom_inv := funext (fun k => (convolutionRightUnitor_evenIso C hC t ht X k).hom_inv)
  inv_hom := funext (fun k => (convolutionRightUnitor_evenIso C hC t ht X k).inv_hom)
  hom_even := fun k => (convolutionRightUnitor_evenIso C hC t ht X k).hom_even
  inv_even := fun k => (convolutionRightUnitor_evenIso C hC t ht X k).inv_even

/-! Nontriviality checks on the advertised construction itself. -/

example : (twistedPullbackData C hC t ht).id (twistedPullbackData C hC t ht).tensorUnit ≠
    (twistedPullbackData C hC t ht).zero := by
  intro h
  have h₁ := congrFun h 1
  change C.id (pullbackUnitObj C hC t 1).val = C.zero at h₁
  rw [pullbackUnitObj, supportedObj_one] at h₁
  exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hC.simple_unit h₁

example : (twistedPullbackData C hC t ht).pi.hom ≠ (twistedPullbackData C hC t ht).zero := by
  intro h
  have h₁ := congrFun h 1
  change pullbackPiHom C hC t 1 = C.zero at h₁
  have hi := pullbackPi_inv_hom C hC t 1
  rw [h₁, raw_comp_zero hC.toWeaklyPointedSuperfusionLaws,
    pullbackUnitObj, supportedObj_one] at hi
  exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hC.simple_unit hi.symm

end RMod.Classification

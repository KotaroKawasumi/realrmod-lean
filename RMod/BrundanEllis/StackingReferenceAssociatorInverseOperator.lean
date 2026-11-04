import RMod.BrundanEllis.StackingReferenceAssociatorOperator
import RMod.BrundanEllis.StackingReferenceAssociatorInverse
import RMod.BrundanEllis.StackingReferenceOperatorTransport

/-! Faithfulness and the actual reference inverse laws identify the reverse
categorical associator with the normalized inverse connector operator. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

attribute [local irreducible] uniformOperator RealAssociator.hom RealAssociator.inv

/-- The inverse matrix represents the actual inverse associator as well. -/
theorem atomAssociatorInverse_operator (a b c : ZMod 8) :
    ((leftTripleCoordinates a b c).toLinearMap.comp
      (uniformOperator (a + b + c) (rightAtomTensor a b c) (leftAtomTensor a b c)
        (rightAtomTensor_label a b c) (leftAtomTensor_label a b c)
        (RealAssociator.inv (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))))).comp
        (rightTripleCoordinates a b c).symm.toLinearMap = associatorInverseOperator a b c := by
  have hr : Hom.comp
      (RealAssociator.inv (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0)))
      (RealAssociator.hom (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))) =
      Hom.id realDData (rightAtomTensor a b c) :=
    RealAssociatorLaws.realAssociator_inv_hom _ _ _
  have hc := congrArg (uniformOperator (a + b + c) (rightAtomTensor a b c) (rightAtomTensor a b c)
    (rightAtomTensor_label a b c) (rightAtomTensor_label a b c)) hr
  rw [uniformOperator_comp _ _ _ _ (rightAtomTensor_label a b c) (leftAtomTensor_label a b c)
    (rightAtomTensor_label a b c), uniformOperator_id] at hc
  let B : RightCarrier a b c →ₗ[ℝ] LeftCarrier a b c :=
    ((leftTripleCoordinates a b c).toLinearMap.comp
      (uniformOperator (a + b + c) (rightAtomTensor a b c) (leftAtomTensor a b c)
        (rightAtomTensor_label a b c) (leftAtomTensor_label a b c)
        (RealAssociator.inv (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))))).comp
        (rightTripleCoordinates a b c).symm.toLinearMap
  change B = associatorInverseOperator a b c
  apply LinearMap.ext
  intro v
  have ha := LinearMap.congr_fun (atomAssociator_operator a b c) (B v)
  have hb : associatorOperator a b c (B v) = v := by
    rw [← ha]
    dsimp only [B, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_apply]
    have he := LinearMap.congr_fun hc ((rightTripleCoordinates a b c).symm v)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.apply_symm_apply] using
      congrArg (rightTripleCoordinates a b c) he
  calc
    B v = associatorInverseOperator a b c (associatorOperator a b c (B v)) :=
      (associatorInverseOperator_hom a b c (B v)).symm
    _ = associatorInverseOperator a b c v := by rw [hb]

end RMod.BrundanEllis.Stacking.ReferenceCommutor

import RMod.BrundanEllis.StackingReferenceInnerMapOperator
import RMod.BrundanEllis.StackingReferenceOuterMapOperator
import RMod.BrundanEllis.StackingReferenceAssociatorInverseOperator
import RMod.BrundanEllis.StackingReferenceHexagonOperators

/-! Reflect the finite reference hexagons to the actual categorical maps.
The finite coefficient equations remain explicit hypotheses here; their
separate verification supplies those hypotheses without changing any map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT
attribute [local irreducible] uniformOperator RealAssociator.hom RealAssociator.inv

/-- The actual associator in transported label coordinates is the connector operator. -/
theorem atomAssociator_arrow (a b c : ZMod 8) :
    LinearEquiv.arrowCongr (leftTripleCoordinates a b c) (rightTripleCoordinates a b c)
      (labelOperator (a + b + c) (a + b + c) _ _ (leftAtomTensor_label a b c)
        (rightAtomTensor_label a b c) rfl
        (RealAssociator.hom (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0)))) =
      associatorOperator a b c := atomAssociator_operator a b c

/-- The inverse associator has the matching inverse coordinate operator. -/
theorem atomAssociatorInverse_arrow (a b c : ZMod 8) :
    LinearEquiv.arrowCongr (rightTripleCoordinates a b c) (leftTripleCoordinates a b c)
      (labelOperator (a + b + c) (a + b + c) _ _ (rightAtomTensor_label a b c)
        (leftAtomTensor_label a b c) rfl
        (RealAssociator.inv (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0)))) =
      associatorInverseOperator a b c := atomAssociatorInverse_operator a b c

/-- The outer right exchange in transported coordinates. -/
theorem outerRightMap_arrow (a b c : ZMod 8) :
    LinearEquiv.arrowCongr (rightTripleCoordinates a b c) (leftTripleCoordinates b c a)
      (labelOperator (a + b + c) (b + c + a) _ _ (rightAtomTensor_label a b c)
        (leftAtomTensor_label b c a) ((add_assoc a b c).trans (add_comm a (b + c)))
        (outerRightMap a b c)) = outerRightOperator a b c := outerRightMap_operator a b c

/-- The outer left exchange in transported coordinates. -/
theorem outerLeftMap_arrow (a b c : ZMod 8) :
    LinearEquiv.arrowCongr (leftTripleCoordinates a b c) (rightTripleCoordinates c a b)
      (labelOperator (a + b + c) (c + a + b) _ _ (leftAtomTensor_label a b c)
        (rightAtomTensor_label c a b) ((add_comm (a + b) c).trans (add_assoc c a b).symm)
        (outerLeftMap a b c)) = outerLeftOperator a b c := outerLeftMap_operator a b c

/-- The inner left exchange in transported coordinates. -/
theorem innerLeftMap_arrow (a b c : ZMod 8) :
    LinearEquiv.arrowCongr (leftTripleCoordinates a b c) (leftTripleCoordinates b a c)
      (labelOperator (a + b + c) (b + a + c) _ _ (leftAtomTensor_label a b c)
        (leftAtomTensor_label b a c) (congrArg (fun z => z + c) (add_comm a b))
        (innerLeftMap a b c)) = innerLeftOperator a b c := innerLeftMap_operator a b c

/-- The inner right exchange in transported coordinates. -/
theorem innerRightMap_arrow (a b c : ZMod 8) :
    LinearEquiv.arrowCongr (rightTripleCoordinates a b c) (rightTripleCoordinates a c b)
      (labelOperator (a + b + c) (a + c + b) _ _ (rightAtomTensor_label a b c)
        (rightAtomTensor_label a c b)
        ((add_assoc a b c).trans ((congrArg (fun z => a + z) (add_comm b c)).trans
          (add_assoc a c b).symm)) (innerRightMap a b c)) =
      innerRightOperator a b c := innerRightMap_operator a b c

/-- A verified first coefficient hexagon is the first hexagon of the actual reference maps. -/
theorem leftHexagon_categorical (a b c : ZMod 8) (h : LeftEquation a b c) :
    leftHexagonShortMap a b c = leftHexagonLongMap a b c := by
  apply labelOperator_injective (a + b + c) (b + c + a) _ _
    (leftAtomTensor_label a b c) (rightAtomTensor_label b c a)
    ((add_assoc a b c).trans (add_comm a (b + c)))
  apply (LinearEquiv.arrowCongr (leftTripleCoordinates a b c) (rightTripleCoordinates b c a)).injective
  unfold leftHexagonShortMap leftHexagonLongMap
  rw [labelOperator_comp (a + b + c) (a + b + c) (b + c + a) _ _ _
    (leftAtomTensor_label a b c) (rightAtomTensor_label a b c) (rightAtomTensor_label b c a)
    rfl ((add_assoc a b c).trans (add_comm a (b + c))),
    LinearEquiv.arrowCongr_comp (leftTripleCoordinates a b c) (rightTripleCoordinates a b c)
      (rightTripleCoordinates b c a),
    labelOperator_comp (a + b + c) (b + c + a) (b + c + a) _ _ _
      (rightAtomTensor_label a b c) (leftAtomTensor_label b c a) (rightAtomTensor_label b c a)
      ((add_assoc a b c).trans (add_comm a (b + c))) rfl,
    LinearEquiv.arrowCongr_comp (rightTripleCoordinates a b c) (leftTripleCoordinates b c a)
      (rightTripleCoordinates b c a)]
  rw [labelOperator_comp (a + b + c) (b + a + c) (b + c + a) _ _ _
    (leftAtomTensor_label a b c) (leftAtomTensor_label b a c) (rightAtomTensor_label b c a)
    (congrArg (fun z => z + c) (add_comm a b)) (by ac_rfl),
    LinearEquiv.arrowCongr_comp (leftTripleCoordinates a b c) (leftTripleCoordinates b a c)
      (rightTripleCoordinates b c a),
    labelOperator_comp (b + a + c) (b + a + c) (b + c + a) _ _ _
      (leftAtomTensor_label b a c) (rightAtomTensor_label b a c) (rightAtomTensor_label b c a)
      rfl (by ac_rfl),
    LinearEquiv.arrowCongr_comp (leftTripleCoordinates b a c) (rightTripleCoordinates b a c)
      (rightTripleCoordinates b c a)]
  rw [atomAssociator_arrow, atomAssociator_arrow, atomAssociator_arrow,
    outerRightMap_arrow, innerLeftMap_arrow, innerRightMap_arrow]
  simpa only [LinearMap.comp_assoc] using leftHexagon_operators a b c h

/-- The second categorical hexagon retains the certified reference defect sign. -/
theorem rightHexagon_categorical (a b c : ZMod 8) (h : RightEquation a b c) :
    outerLeftMap a b c = Hom.smul (paritySign (rightDefect a b c)) (rightHexagonLongMap a b c) := by
  apply labelOperator_injective (a + b + c) (c + a + b) _ _
    (leftAtomTensor_label a b c) (rightAtomTensor_label c a b)
    ((add_comm (a + b) c).trans (add_assoc c a b).symm)
  apply (LinearEquiv.arrowCongr (leftTripleCoordinates a b c) (rightTripleCoordinates c a b)).injective
  rw [labelOperator_smul, map_smul, outerLeftMap_arrow]
  unfold rightHexagonLongMap
  rw [labelOperator_comp (a + b + c) (a + b + c) (c + a + b) _ _ _
    (leftAtomTensor_label a b c) (rightAtomTensor_label a b c) (rightAtomTensor_label c a b)
    rfl ((add_comm (a + b) c).trans (add_assoc c a b).symm),
    LinearEquiv.arrowCongr_comp (leftTripleCoordinates a b c) (rightTripleCoordinates a b c)
      (rightTripleCoordinates c a b),
    labelOperator_comp (a + b + c) (a + c + b) (c + a + b) _ _ _
      (rightAtomTensor_label a b c) (rightAtomTensor_label a c b) (rightAtomTensor_label c a b)
      (by ac_rfl) (congrArg (fun z => z + b) (add_comm a c)),
    LinearEquiv.arrowCongr_comp (rightTripleCoordinates a b c) (rightTripleCoordinates a c b)
      (rightTripleCoordinates c a b),
    labelOperator_comp (a + c + b) (a + c + b) (c + a + b) _ _ _
      (rightAtomTensor_label a c b) (leftAtomTensor_label a c b) (rightAtomTensor_label c a b)
      rfl (congrArg (fun z => z + b) (add_comm a c)),
    LinearEquiv.arrowCongr_comp (rightTripleCoordinates a c b) (leftTripleCoordinates a c b)
      (rightTripleCoordinates c a b),
    labelOperator_comp (a + c + b) (c + a + b) (c + a + b) _ _ _
      (leftAtomTensor_label a c b) (leftAtomTensor_label c a b) (rightAtomTensor_label c a b)
      (congrArg (fun z => z + b) (add_comm a c)) rfl,
    LinearEquiv.arrowCongr_comp (leftTripleCoordinates a c b) (leftTripleCoordinates c a b)
      (rightTripleCoordinates c a b)]
  rw [atomAssociator_arrow, atomAssociator_arrow, atomAssociatorInverse_arrow,
    innerLeftMap_arrow, innerRightMap_arrow]
  simpa only [LinearMap.comp_assoc] using rightHexagon_operators a b c h

end RMod.BrundanEllis.Stacking.ReferenceCommutor

import RMod.Classification.Instances.OrderedParityDeletion
import RMod.Classification.Proofs.NormalizerDeletion

/-!
# Homogeneous inverse laws for ordered parity deletions

Each tensor product has an identity as its other factor. Hence its
specified reverse map is an inverse without a tensor-interchange sign.
The degrees of the successive deletions add.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem orderedLeftDeletion_homogeneousIso (X Y Z : C.Obj) (a b : ZMod 2) :
    HomogeneousIsoLaws C (a + b) (p.orderedLeftDeletion X Y Z a b) := by
  have he := ((((hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj X Y) a).whiskerRight hC Z).whiskerRight
    hC (p.factor b)).trans hC
    (hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj (C.tensorObj X Y) Z) b)).trans hC
      (EvenIsoLaws.assoc hC X Y Z).homogeneous
  simpa only [PiData.orderedLeftDeletion, add_zero] using he

theorem orderedRightDeletion_homogeneousIso (X Y Z : C.Obj) (a b : ZMod 2) :
    HomogeneousIsoLaws C (a + b) (p.orderedRightDeletion X Y Z a b) :=
  (((hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj Y Z) a).whiskerLeft hC X).whiskerRight
    hC (p.factor b)).trans hC
    (hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj X (C.tensorObj Y Z)) b)

theorem orderedOutputDeletion_homogeneousIso (X Y Z : C.Obj) (a b c : ZMod 2) :
    HomogeneousIsoLaws C ((a + b) + c) (p.orderedOutputDeletion X Y Z a b c) :=
  ((hp.orderedRightDeletion_homogeneousIso hC X Y Z a b).whiskerRight hC (p.factor c)).trans hC
    (hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj X (C.tensorObj Y Z)) c)

theorem localAssociator_orderedDeletion (X Y Z : C.Obj) (a b c d : ZMod 2)
    (e : a + b = c + d) (omega : ℝˣ) :
    C.comp (p.localAssociator X Y Z a b c d e omega).hom
      (p.orderedRightDeletion X Y Z c d).hom =
      C.smul omega.val (p.orderedLeftDeletion X Y Z a b).hom := by
  exact (hp.localAssociator_deletion hC X Y Z a b c d e omega).trans
    (congrArg (C.smul omega.val) (hC.comp_assoc _ _ _).symm)

end RMod.Classification.PiLaws

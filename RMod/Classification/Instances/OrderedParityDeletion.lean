import RMod.Classification.Instances.RightFactorDeletion

/-!
# Ordered deletion maps for the two bracketings of a triple

In each bracketing delete the inner factor and then the outer factor.
The left bracketing finishes with the original associator. Every inverse
is supplied as part of the existing IsoData, before its laws are proved.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

def orderedLeftDeletion (X Y Z : C.Obj) (a b : ZMod 2) :
    IsoData C
      (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj X Y) (p.factor a)) Z) (p.factor b))
      (C.tensorObj X (C.tensorObj Y Z)) :=
  ((((p.rightFactorDeletion (C.tensorObj X Y) a).tensor C (IsoData.refl C Z)).tensor C
    (IsoData.refl C (p.factor b))).trans C
    (p.rightFactorDeletion (C.tensorObj (C.tensorObj X Y) Z) b)).trans C (IsoData.assoc C X Y Z)

def orderedRightDeletion (X Y Z : C.Obj) (a b : ZMod 2) :
    IsoData C
      (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor a))) (p.factor b))
      (C.tensorObj X (C.tensorObj Y Z)) :=
  (((IsoData.refl C X).tensor C (p.rightFactorDeletion (C.tensorObj Y Z) a)).tensor C
    (IsoData.refl C (p.factor b))).trans C (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) b)

def orderedOutputDeletion (X Y Z : C.Obj) (a b c : ZMod 2) :
    IsoData C
      (C.tensorObj
        (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor a))) (p.factor b))
        (p.factor c)) (C.tensorObj X (C.tensorObj Y Z)) :=
  ((p.orderedRightDeletion X Y Z a b).tensor C (IsoData.refl C (p.factor c))).trans C
    (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) c)

end RMod.Classification.PiData

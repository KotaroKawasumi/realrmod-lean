import RMod.Classification.Abstract.Normalizers
import RMod.Classification.Abstract.Duals

/-!
# The two explicit parity contractions used by duality

The positive comparison removes the two adjacent parity factors after
reassociation. The negative comparison first moves the parity factor
past X. Both retain their specified inverse maps. The proposed evaluation
then carries exactly the inverse omega weight from the manuscript.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

def contractEqualFactors (a : ZMod 2) :
    IsoData C (C.tensorObj (p.factor a) (p.factor a)) C.tensorUnit :=
  (p.multiplyFactors a a).trans C (IsoData.ofEq C (congrArg p.factor (CharTwo.add_self_eq_zero a)))

def eraseFactorPair (X : C.Obj) (a : ZMod 2) :
    IsoData C (C.tensorObj (C.tensorObj X (p.factor a)) (p.factor a)) X :=
  ((IsoData.assoc C X (p.factor a) (p.factor a)).trans C
    ((IsoData.refl C X).tensor C (p.contractEqualFactors a))).trans C (IsoData.rightUnit C X)

def dualPositiveNormalizer (X Y : C.Obj) (a : ZMod 2) :
    IsoData C (C.tensorObj (C.tensorObj X (C.tensorObj Y (p.factor a))) (p.factor a))
      (C.tensorObj X Y) :=
  (((IsoData.assoc C X Y (p.factor a)).symm C).tensor C (IsoData.refl C (p.factor a))).trans C
    (p.eraseFactorPair (C.tensorObj X Y) a)

def dualNegativeNormalizer (X Y : C.Obj) (a : ZMod 2) :
    IsoData C (C.tensorObj (C.tensorObj (C.tensorObj Y (p.factor a)) X) (p.factor a))
      (C.tensorObj Y X) :=
  ((((IsoData.assoc C Y (p.factor a) X).trans C
    ((IsoData.refl C Y).tensor C (p.moveFactor a X))).trans C
      ((IsoData.assoc C Y X (p.factor a)).symm C)).tensor C
        (IsoData.refl C (p.factor a))).trans C (p.eraseFactorPair (C.tensorObj Y X) a)

def twistedCoevaluation {X Y : C.Obj} (d : DualPairingData C X Y) (a : ZMod 2) :
    C.Hom C.tensorUnit (C.tensorObj (C.tensorObj X (C.tensorObj Y (p.factor a))) (p.factor a)) :=
  C.comp d.coeval (p.dualPositiveNormalizer X Y a).inv

def twistedEvaluation {X Y : C.Obj} (d : DualPairingData C X Y) (a : ZMod 2) (ω : ℝˣ) :
    C.Hom (C.tensorObj (C.tensorObj (C.tensorObj Y (p.factor a)) X) (p.factor a)) C.tensorUnit :=
  C.smul ((ω⁻¹ : ℝˣ) : ℝ) (C.comp (p.dualNegativeNormalizer X Y a).hom d.eval)

end RMod.Classification.PiData

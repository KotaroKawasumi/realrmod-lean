import RMod.Classification.Abstract.Normalizers

/-!
# The specified local tensorator for a parity gauge transformation

Gather the two component-shift factors in their existing order, then
contract the target tensor parity. The output normalization contracts the
source tensor parity followed by the product shift. Equality of these
parity totals is the binary gauge equation. Both normalization directions
are explicit, and the scalar multiplies the resulting even comparison.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

def rightFactorPairNormalizer (X : C.Obj) (a b : ZMod 2) :
    IsoData C (C.tensorObj (C.tensorObj X (p.factor a)) (p.factor b))
      (C.tensorObj X (p.factor (a + b))) :=
  (IsoData.assoc C X (p.factor a) (p.factor b)).trans C
    ((IsoData.refl C X).tensor C (p.multiplyFactors a b))

def rightFactorTensorNormalizer (X Y : C.Obj) (a b : ZMod 2) :
    IsoData C (C.tensorObj (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b)))
      (C.tensorObj (C.tensorObj X Y) (p.factor (a + b))) :=
  let i₁ := (IsoData.assoc C (C.tensorObj X (p.factor a)) Y (p.factor b)).symm C
  let i₂ := (IsoData.assoc C X (p.factor a) Y).tensor C (IsoData.refl C (p.factor b))
  let i₃ := ((IsoData.refl C X).tensor C (p.moveFactor a Y)).tensor C (IsoData.refl C (p.factor b))
  let i₄ := ((IsoData.assoc C X Y (p.factor a)).symm C).tensor C (IsoData.refl C (p.factor b))
  (((i₁.trans C i₂).trans C i₃).trans C i₄).trans C
    (p.rightFactorPairNormalizer (C.tensorObj X Y) a b)

def gaugeSourceNormalizer (X Y : C.Obj) (a b n' : ZMod 2) :
    IsoData C
      (C.tensorObj (C.tensorObj (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b))) (p.factor n'))
      (C.tensorObj (C.tensorObj X Y) (p.factor ((a + b) + n'))) :=
  ((p.rightFactorTensorNormalizer X Y a b).tensor C (IsoData.refl C (p.factor n'))).trans C
    (p.rightFactorPairNormalizer (C.tensorObj X Y) (a + b) n')

def gaugeLocalTensorator (X Y : C.Obj) (a b n' n c : ZMod 2)
    (e : (a + b) + n' = n + c) (β : ℝˣ) :
    IsoData C
      (C.tensorObj (C.tensorObj (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b))) (p.factor n'))
      (C.tensorObj (C.tensorObj (C.tensorObj X Y) (p.factor n)) (p.factor c)) :=
  ((p.gaugeSourceNormalizer X Y a b n').trans C
    ((IsoData.ofEq C (congrArg (fun q => C.tensorObj (C.tensorObj X Y) (p.factor q)) e)).trans C
      ((p.rightFactorPairNormalizer (C.tensorObj X Y) n c).symm C))).scale C β

end RMod.Classification.PiData

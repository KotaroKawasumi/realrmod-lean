import RMod.Classification.Instances.GaugeLocalNormalizers
import RMod.Classification.Proofs.NormalizerNaturality

/-!
# Inverse and parity laws of the specified local gauge tensorator

Every structural step is even: associators, the central factor crossing,
factor multiplication, and the forced equality map. Their supplied
inverses compose in reverse order, including the inverse real scalar.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem rightFactorPairNormalizer_evenIso (X : C.Obj) (a b : ZMod 2) :
    EvenIsoLaws C (p.rightFactorPairNormalizer X a b) :=
  (EvenIsoLaws.assoc hC X (p.factor a) (p.factor b)).trans hC
    ((EvenIsoLaws.refl hC X).tensor hC (hp.multiplyFactors_evenIso hC a b))

theorem rightFactorTensorNormalizer_evenIso (X Y : C.Obj) (a b : ZMod 2) :
    EvenIsoLaws C (p.rightFactorTensorNormalizer X Y a b) :=
  (((((EvenIsoLaws.assoc hC (C.tensorObj X (p.factor a)) Y (p.factor b)).symm).trans hC
    ((EvenIsoLaws.assoc hC X (p.factor a) Y).tensor hC (EvenIsoLaws.refl hC (p.factor b)))).trans hC
    (((EvenIsoLaws.refl hC X).tensor hC (hp.moveFactor_evenIso hC a Y)).tensor hC
      (EvenIsoLaws.refl hC (p.factor b)))).trans hC
    ((EvenIsoLaws.assoc hC X Y (p.factor a)).symm.tensor hC (EvenIsoLaws.refl hC (p.factor b)))).trans hC
    (hp.rightFactorPairNormalizer_evenIso hC (C.tensorObj X Y) a b)

theorem gaugeSourceNormalizer_evenIso (X Y : C.Obj) (a b n' : ZMod 2) :
    EvenIsoLaws C (p.gaugeSourceNormalizer X Y a b n') :=
  ((hp.rightFactorTensorNormalizer_evenIso hC X Y a b).tensor hC
    (EvenIsoLaws.refl hC (p.factor n'))).trans hC
      (hp.rightFactorPairNormalizer_evenIso hC (C.tensorObj X Y) (a + b) n')

theorem gaugeLocalTensorator_evenIso (X Y : C.Obj) (a b n' n c : ZMod 2)
    (e : (a + b) + n' = n + c) (β : ℝˣ) :
    EvenIsoLaws C (p.gaugeLocalTensorator X Y a b n' n c e β) :=
  ((hp.gaugeSourceNormalizer_evenIso hC X Y a b n').trans hC
    ((EvenIsoLaws.ofEq hC (congrArg (fun q => C.tensorObj (C.tensorObj X Y) (p.factor q)) e)).trans hC
      (hp.rightFactorPairNormalizer_evenIso hC (C.tensorObj X Y) n c).symm)).scale hC β

end RMod.Classification.PiLaws

import RMod.Classification.Instances.ParityDualNormalizers
import RMod.Classification.Proofs.Normalizers

/-!
# Even inverse laws for the explicit duality comparisons

The normalizers consist solely of the already proved even structural
isomorphisms. Their data remain independent of these proofs. Grading of
the proposed coevaluation and evaluation follows for any supplied base
pairing, before either new snake identity is claimed.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
  {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem contractEqualFactors_evenIso (a : ZMod 2) :
    EvenIsoLaws C (p.contractEqualFactors a) :=
  (hp.multiplyFactors_evenIso hC a a).trans hC (EvenIsoLaws.ofEq hC _)

theorem eraseFactorPair_evenIso (X : C.Obj) (a : ZMod 2) :
    EvenIsoLaws C (p.eraseFactorPair X a) :=
  ((EvenIsoLaws.assoc hC X (p.factor a) (p.factor a)).trans hC
    ((EvenIsoLaws.refl hC X).tensor hC (hp.contractEqualFactors_evenIso hC a))).trans hC
      (EvenIsoLaws.rightUnit hC X)

theorem dualPositiveNormalizer_evenIso (X Y : C.Obj) (a : ZMod 2) :
    EvenIsoLaws C (p.dualPositiveNormalizer X Y a) :=
  ((EvenIsoLaws.assoc hC X Y (p.factor a)).symm.tensor hC
    (EvenIsoLaws.refl hC (p.factor a))).trans hC (hp.eraseFactorPair_evenIso hC (C.tensorObj X Y) a)

theorem dualNegativeNormalizer_evenIso (X Y : C.Obj) (a : ZMod 2) :
    EvenIsoLaws C (p.dualNegativeNormalizer X Y a) :=
  ((((EvenIsoLaws.assoc hC Y (p.factor a) X).trans hC
    ((EvenIsoLaws.refl hC Y).tensor hC (hp.moveFactor_evenIso hC a X))).trans hC
      (EvenIsoLaws.assoc hC Y X (p.factor a)).symm).tensor hC
        (EvenIsoLaws.refl hC (p.factor a))).trans hC (hp.eraseFactorPair_evenIso hC (C.tensorObj Y X) a)

theorem twistedCoevaluation_even {X Y : C.Obj} {d : DualPairingData C X Y}
    (hd : DualPairingLaws C d) (a : ZMod 2) : C.IsHomogeneous 0 (p.twistedCoevaluation d a) := by
  exact comp_even hC hd.coeval_even (hp.dualPositiveNormalizer_evenIso hC X Y a).inv_even

theorem twistedEvaluation_even {X Y : C.Obj} {d : DualPairingData C X Y}
    (hd : DualPairingLaws C d) (a : ZMod 2) (ω : ℝˣ) : C.IsHomogeneous 0 (p.twistedEvaluation d a ω) := by
  exact hC.grade_smul _ _ (comp_even hC (hp.dualNegativeNormalizer_evenIso hC X Y a).hom_even hd.eval_even)

end RMod.Classification.PiLaws

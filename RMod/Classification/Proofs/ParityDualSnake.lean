import RMod.Classification.Proofs.ParityDualCenter
import RMod.Classification.Proofs.ParityTriangle
import RMod.Classification.Proofs.ParityCentralNormalizers
import RMod.Classification.Instances.Duals

/-!
# The first snake for the specified local parity twist

The inverse-pair parity is a on both sides, and the two unit-adjacent
parities vanish. Removing those outer unit factors identifies the actual
local associator with the central middle comparison. Its first snake is
therefore the central contraction cancellation already proved above.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

attribute [local implicit_reducible] factorCenter

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem multiplyFactorsEven_one_zero :
    IsoData.toEvenIso C (p.multiplyFactors 1 0) (hp.multiplyFactors_evenIso C.laws 1 0) =
      ρ_ (evenObj ℝ (LinearCategory C) p.object) := rfl

theorem scalarFreeAssociatorEven_dual (X Y Z : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2) :
    (scalarFreeAssociatorEvenIso C p hp X Y Z a 0 a 0 rfl).hom =
      (CentralDuality.middle X Y Z (factorCenter C p hp a)).hom ⊗ₘ
        𝟙 (𝟙_ (EvenSubcategory ℝ (LinearCategory C))) := by
  unfold scalarFreeAssociatorEvenIso normalLeftEvenIso normalRightEvenIso CentralDuality.middle
  rw [factorHalfBraiding_evenIso]
  dsimp only [factorCenter]
  rcases parity_cases a with rfl | rfl
  · rw [moveFactorEven_zero C p hp, multiplyFactorsEven_zero C p hp]
    simp only [eqToIso_refl, factorEven_zero C p]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
    monoidal
  · rw [multiplyFactorsEven_one_zero C p hp]
    simp only [eqToIso_refl, factorEven_zero C p, factorEven_one C p]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
    have he := CentralDuality.unit_normalizer X Y Z (evenObj ℝ (LinearCategory C) p.object)
      (IsoData.toEvenIso C (p.moveFactor 1 Z.obj) (hp.moveFactor_evenIso C.laws 1 Z.obj))
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.assoc] at he ⊢
    exact he

/-- The full local first snake, including the outer unit factor retained
by the actual tensor convention, in the ordinary even category. -/
theorem localParity_first_snake_even (X Y : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2)
    (q : ExactPairing X Y) :
    ((q.coevaluation' ≫ (CentralDuality.positive X Y (factorCenter C p hp a)
      (factorSquareCenterIso C p hp a)).inv) ▷ X) ▷ 𝟙_ (EvenSubcategory ℝ (LinearCategory C)) ≫
      (scalarFreeAssociatorEvenIso C p hp X (Y ⊗ evenObj ℝ (LinearCategory C) (p.factor a))
        X a 0 a 0 rfl).hom ≫
      (X ◁ ((CentralDuality.negative X Y (factorCenter C p hp a)
        (factorSquareCenterIso C p hp a)).hom ≫ q.evaluation')) ▷
          𝟙_ (EvenSubcategory ℝ (LinearCategory C)) =
      ((λ_ X).hom ≫ (ρ_ X).inv) ▷ 𝟙_ (EvenSubcategory ℝ (LinearCategory C)) := by
  rw [scalarFreeAssociatorEven_dual, tensorHom_id]
  have he := congrArg (fun f => f ▷ 𝟙_ (EvenSubcategory ℝ (LinearCategory C)))
    (CentralDuality.positive_snake X Y (factorCenter C p hp a) (factorSquareCenterIso C p hp a)
      q.coevaluation' q.evaluation' q.evaluation_coevaluation')
  simp only [comp_whiskerRight] at he ⊢
  exact he

include hp

/-- The actual scalar-free raw associator and the specified dual maps
satisfy the first snake, before inserting the reciprocal omega weight. -/
theorem localAssociator_first_snake {X Y : C.data.Obj} (q : DualPairing C X Y) (a : ZMod 2) :
    C.data.comp
      (C.data.comp
        (C.data.tensorHom (C.data.tensorHom (p.twistedCoevaluation q.data a) (C.data.id X))
          (C.data.id C.data.tensorUnit))
        (p.localAssociator X (C.data.tensorObj Y (p.factor a)) X a 0 a 0 rfl 1).hom)
      (C.data.tensorHom
        (C.data.tensorHom (C.data.id X)
          (C.data.comp (p.dualNegativeNormalizer X Y a).hom q.data.eval))
        (C.data.id C.data.tensorUnit)) =
      C.data.tensorHom (C.data.comp (C.data.leftUnitorHom X) (C.data.rightUnitorInv X))
        (C.data.id C.data.tensorUnit) := by
  let X' := evenObj ℝ (LinearCategory C) X
  let Y' := evenObj ℝ (LinearCategory C) Y
  have he := congrArg (fun f => f.hom) (localParity_first_snake_even C p hp X' Y' a q.toEvenPairing)
  change C.data.comp
    (C.data.tensorHom (C.data.tensorHom
      (C.data.comp q.data.coeval (CentralDuality.positive X' Y' (factorCenter C p hp a)
        (factorSquareCenterIso C p hp a)).inv.hom) (C.data.id X))
        (C.data.id C.data.tensorUnit))
    (C.data.comp (scalarFreeAssociatorEvenIso C p hp _ _ _ a 0 a 0 rfl).hom.hom
      (C.data.tensorHom (C.data.tensorHom (C.data.id X)
        (C.data.comp (CentralDuality.negative X' Y' (factorCenter C p hp a)
          (factorSquareCenterIso C p hp a)).hom.hom q.data.eval))
          (C.data.id C.data.tensorUnit))) = _ at he
  rw [centralPositive_inv, centralNegative_hom, scalarFreeAssociatorEvenIso_hom] at he
  exact (C.laws.comp_assoc _ _ _).trans he

end RMod.Classification

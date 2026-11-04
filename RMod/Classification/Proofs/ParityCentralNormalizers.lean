import RMod.Classification.Proofs.CentralWordRoutes
import RMod.Classification.Proofs.ParityWordCrossing
import RMod.Classification.Proofs.EvenNormalizers

/-!
# The specified parity normalizers as central-factor comparisons

These comparisons identify the exact maps already used by the pullback.
They do not replace the definition by an equivalent construction: both
normalizers, their equality transport, and their multiplication inverses
agree with the central-word expression on the nose as isomorphisms.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

attribute [local implicit_reducible] CategoryTheory.Center CategoryTheory.Center.tensorObj

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem factorHalfBraiding_evenIso (a : ZMod 2) (X : EvenSubcategory ℝ (LinearCategory C)) :
    (factorCenter C p hp a).2.β X =
      IsoData.toEvenIso C (p.moveFactor a X.obj) (hp.moveFactor_evenIso C.laws a X.obj) := by
  apply Iso.ext
  apply WideSubcategory.hom_ext
  exact factorHalfBraiding_hom C p hp a X

theorem parityCenter_pairCompare_evenIso (a b c d : ZMod 2) (he : a + b = c + d) :
    (Center.forget (EvenSubcategory ℝ (LinearCategory C))).mapIso
      (MonoidalWord.pairCompare (parityCenterFunctor C p hp)
        (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (congrArg Multiplicative.ofAdd he)) =
      IsoData.toEvenIso C (p.multiplyFactors a b) (hp.multiplyFactors_evenIso C.laws a b) ≪≫
        eqToIso (congrArg (fun q => evenObj ℝ (LinearCategory C) (p.factor q)) he) ≪≫
          (IsoData.toEvenIso C (p.multiplyFactors c d) (hp.multiplyFactors_evenIso C.laws c d)).symm := by
  apply Iso.ext
  apply WideSubcategory.hom_ext
  change (MonoidalWord.pairCompare (parityCenterFunctor C p hp)
    (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (congrArg Multiplicative.ofAdd he)).hom.f.hom =
    C.data.comp (p.multiplyFactors a b).hom
      (C.data.comp (eqToIso (congrArg (fun q => evenObj ℝ (LinearCategory C) (p.factor q)) he)).hom.hom
        (p.multiplyFactors c d).inv)
  rw [parityCenter_pairCompare_hom C p hp a b c d he]
  congr 2
  exact (even_eqToIso_hom C (congrArg p.factor he)).symm

theorem scalarFreeAssociatorEvenIso_eq_central (X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d : ZMod 2) (he : a + b = c + d) :
    scalarFreeAssociatorEvenIso C p hp X Y Z a b c d he =
      CentralWord.localMove X Y Z
        (MonoidalWord.pairCompare (parityCenterFunctor C p hp)
          (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (congrArg Multiplicative.ofAdd he)) := by
  unfold CentralWord.localMove
  rw [parityCenter_pairCompare_evenIso C p hp a b c d he]
  apply Iso.ext
  simp only [scalarFreeAssociatorEvenIso, normalLeftEvenIso, normalRightEvenIso,
    CentralWord.gatherLeft, CentralWord.gatherRight, parityCenterFunctor, Discrete.functor_obj,
    factorHalfBraiding_evenIso C p hp,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, tensorIso_hom, tensorIso_inv,
    Iso.refl_hom, Iso.refl_inv]
  simp only [factorCenter, toAdd_ofAdd, eqToIso.hom]
  rw [← whiskerLeft_eqToHom (X ⊗ (Y ⊗ Z))
    (congrArg (fun q => evenObj ℝ (LinearCategory C) (p.factor q)) he)]
  monoidal

end RMod.Classification

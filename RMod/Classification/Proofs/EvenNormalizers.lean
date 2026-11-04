import RMod.Classification.Instances.EvenNormalizers

/-!
# The even normalizer expressions preserve the specified maps

Both directions agree definitionally with the raw data. Thus later
coherence calculations in Mathlib apply to the exact normalizers used
by the pullback construction, including their supplied inverse maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem normalLeftEvenIso_hom (X Y Z : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (normalLeftEvenIso C p hp X Y Z a b).hom.hom = (p.normalLeft X.obj Y.obj Z.obj a b).hom := rfl

theorem normalLeftEvenIso_inv (X Y Z : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (normalLeftEvenIso C p hp X Y Z a b).inv.hom = (p.normalLeft X.obj Y.obj Z.obj a b).inv := rfl

theorem normalRightEvenIso_hom (X Y Z : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (normalRightEvenIso C p hp X Y Z a b).hom.hom = (p.normalRight X.obj Y.obj Z.obj a b).hom := rfl

theorem normalRightEvenIso_inv (X Y Z : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (normalRightEvenIso C p hp X Y Z a b).inv.hom = (p.normalRight X.obj Y.obj Z.obj a b).inv := rfl

theorem even_eqToIso_hom {X Y : C.data.Obj} (he : X = Y) :
    (eqToIso (congrArg (evenObj ℝ (LinearCategory C)) he)).hom.hom = (IsoData.ofEq C.data he).hom := by
  subst Y
  rfl

theorem scalarFreeAssociatorEvenIso_hom (X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d : ZMod 2) (he : a + b = c + d) :
    (scalarFreeAssociatorEvenIso C p hp X Y Z a b c d he).hom.hom =
      (p.localAssociator X.obj Y.obj Z.obj a b c d he 1).hom := by
  change C.data.comp (p.normalLeft X.obj Y.obj Z.obj a b).hom
    (C.data.comp (eqToIso (congrArg (fun q => (X ⊗ (Y ⊗ Z)) ⊗
      evenObj ℝ (LinearCategory C) (p.factor q)) he)).hom.hom
      (p.normalRight X.obj Y.obj Z.obj c d).inv) =
    C.data.smul 1 (C.data.comp (p.normalLeft X.obj Y.obj Z.obj a b).hom
      (C.data.comp (IsoData.ofEq C.data _).hom (p.normalRight X.obj Y.obj Z.obj c d).inv))
  rw [C.laws.one_smul]
  congr 2
  exact even_eqToIso_hom C _

end RMod.Classification

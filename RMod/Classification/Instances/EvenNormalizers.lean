import RMod.Classification.Proofs.Normalizers
import RMod.Classification.Instances.EvenIsos

/-!
# The normalizer expressions in Mathlib's even monoidal category

These are the same finite lists of associators, comparisons, contractions,
and inverses as the raw normalizers. Keeping their monoidal expression
visible allows Mathlib's coherence tactics to handle the surrounding
structural maps. Separate comparison lemmas identify the underlying maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

noncomputable def normalLeftEvenIso (X Y Z : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (((X ⊗ Y) ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗ Z) ⊗
        evenObj ℝ (LinearCategory C) (p.factor b) ≅
      (X ⊗ (Y ⊗ Z)) ⊗ evenObj ℝ (LinearCategory C) (p.factor (a + b)) :=
  let P := evenObj ℝ (LinearCategory C) (p.factor a)
  let Q := evenObj ℝ (LinearCategory C) (p.factor b)
  let U := X ⊗ (Y ⊗ Z)
  let c := IsoData.toEvenIso C (p.moveFactor a Z.obj) (hp.moveFactor_evenIso C.laws a Z.obj)
  let m := IsoData.toEvenIso C (p.multiplyFactors a b) (hp.multiplyFactors_evenIso C.laws a b)
  let f₁ := tensorIso (α_ (X ⊗ Y) P Z) (Iso.refl Q)
  let f₂ := tensorIso (tensorIso (Iso.refl (X ⊗ Y)) c) (Iso.refl Q)
  let f₃ := tensorIso (α_ (X ⊗ Y) Z P).symm (Iso.refl Q)
  let f₄ := tensorIso (tensorIso (α_ X Y Z) (Iso.refl P)) (Iso.refl Q)
  let f₅ := α_ U P Q
  let f₆ := tensorIso (Iso.refl U) m
  ((((f₁ ≪≫ f₂) ≪≫ f₃) ≪≫ f₄) ≪≫ f₅) ≪≫ f₆

noncomputable def normalRightEvenIso (X Y Z : EvenSubcategory ℝ (LinearCategory C)) (a b : ZMod 2) :
    (X ⊗ ((Y ⊗ Z) ⊗ evenObj ℝ (LinearCategory C) (p.factor a))) ⊗
        evenObj ℝ (LinearCategory C) (p.factor b) ≅
      (X ⊗ (Y ⊗ Z)) ⊗ evenObj ℝ (LinearCategory C) (p.factor (a + b)) :=
  let P := evenObj ℝ (LinearCategory C) (p.factor a)
  let Q := evenObj ℝ (LinearCategory C) (p.factor b)
  let U := X ⊗ (Y ⊗ Z)
  let m := IsoData.toEvenIso C (p.multiplyFactors a b) (hp.multiplyFactors_evenIso C.laws a b)
  let f₁ := tensorIso (α_ X (Y ⊗ Z) P).symm (Iso.refl Q)
  let f₂ := α_ U P Q
  let f₃ := tensorIso (Iso.refl U) m
  (f₁ ≪≫ f₂) ≪≫ f₃

noncomputable def scalarFreeAssociatorEvenIso (X Y Z : EvenSubcategory ℝ (LinearCategory C))
    (a b c d : ZMod 2) (he : a + b = c + d) :
    (((X ⊗ Y) ⊗ evenObj ℝ (LinearCategory C) (p.factor a)) ⊗ Z) ⊗
        evenObj ℝ (LinearCategory C) (p.factor b) ≅
      (X ⊗ ((Y ⊗ Z) ⊗ evenObj ℝ (LinearCategory C) (p.factor c))) ⊗
        evenObj ℝ (LinearCategory C) (p.factor d) :=
  normalLeftEvenIso C p hp X Y Z a b ≪≫
    (eqToIso (congrArg (fun q => (X ⊗ (Y ⊗ Z)) ⊗ evenObj ℝ (LinearCategory C) (p.factor q)) he) ≪≫
      (normalRightEvenIso C p hp X Y Z c d).symm)

end RMod.Classification

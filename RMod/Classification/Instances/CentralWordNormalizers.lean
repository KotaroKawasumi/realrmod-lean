import Mathlib.CategoryTheory.Monoidal.Center

/-!
# Moving central factors to the right of ordinary objects

The ordinary objects need no braiding. Only the factors in the Drinfeld
center are moved past them. Pair comparisons remain arbitrary center
isomorphisms, so their commutative squares can later move contractions
past an ordinary object without choosing any concrete parity model.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.CentralWord

open CategoryTheory MonoidalCategory

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- Remove the single interleaving factor in a left-associated triple. -/
def gatherLeft (X Y Z : V) (A B : Center V) :
    (((X ⊗ Y) ⊗ A.1) ⊗ Z) ⊗ B.1 ≅ (X ⊗ (Y ⊗ Z)) ⊗ (A.1 ⊗ B.1) :=
  tensorIso (α_ (X ⊗ Y) A.1 Z) (Iso.refl B.1) ≪≫
  tensorIso (tensorIso (Iso.refl (X ⊗ Y)) (A.2.β Z)) (Iso.refl B.1) ≪≫
  tensorIso (α_ (X ⊗ Y) Z A.1).symm (Iso.refl B.1) ≪≫
  tensorIso (tensorIso (α_ X Y Z) (Iso.refl A.1)) (Iso.refl B.1) ≪≫
  α_ (X ⊗ (Y ⊗ Z)) A.1 B.1

/-- Gathering on the right-associated triple uses structural maps only. -/
def gatherRight (X Y Z : V) (A B : Center V) :
    (X ⊗ ((Y ⊗ Z) ⊗ A.1)) ⊗ B.1 ≅ (X ⊗ (Y ⊗ Z)) ⊗ (A.1 ⊗ B.1) :=
  tensorIso (α_ X (Y ⊗ Z) A.1).symm (Iso.refl B.1) ≪≫ α_ (X ⊗ (Y ⊗ Z)) A.1 B.1

/-- Change an adjacent pair of central factors after gathering them. -/
noncomputable def localMove (X Y Z : V) {A B C D : Center V} (f : A ⊗ B ≅ C ⊗ D) :
    (((X ⊗ Y) ⊗ A.1) ⊗ Z) ⊗ B.1 ≅ (X ⊗ ((Y ⊗ Z) ⊗ C.1)) ⊗ D.1 :=
  gatherLeft X Y Z A B ≪≫
    tensorIso (Iso.refl (X ⊗ (Y ⊗ Z))) ((Center.forget V).mapIso f) ≪≫
      (gatherRight X Y Z C D).symm

/-- Gather all factors in the source of a four-object pentagon. -/
noncomputable def gatherFourLeft (W X Y Z : V) (A B T : Center V) :
    (((((W ⊗ X) ⊗ A.1) ⊗ Y) ⊗ B.1) ⊗ Z) ⊗ T.1 ≅
      (W ⊗ (X ⊗ (Y ⊗ Z))) ⊗ ((A.1 ⊗ B.1) ⊗ T.1) :=
  tensorIso (tensorIso (gatherLeft W X Y A B) (Iso.refl Z)) (Iso.refl T.1) ≪≫
    gatherLeft W (X ⊗ Y) Z (A ⊗ B) T ≪≫
      tensorIso (tensorIso (Iso.refl W) (α_ X Y Z)) (Iso.refl ((A.1 ⊗ B.1) ⊗ T.1))

/-- The final pentagon object has all factors after the ordinary objects;
only its parentheses need to be rearranged. -/
def gatherFourRight (W X Y Z : V) (E Q S : Center V) :
    (W ⊗ ((X ⊗ ((Y ⊗ Z) ⊗ E.1)) ⊗ Q.1)) ⊗ S.1 ≅
      (W ⊗ (X ⊗ (Y ⊗ Z))) ⊗ ((E.1 ⊗ Q.1) ⊗ S.1) :=
  tensorIso (tensorIso (Iso.refl W)
    (tensorIso (α_ X (Y ⊗ Z) E.1).symm (Iso.refl Q.1))) (Iso.refl S.1) ≪≫
  tensorIso (α_ W ((X ⊗ (Y ⊗ Z)) ⊗ E.1) Q.1).symm (Iso.refl S.1) ≪≫
  tensorIso (tensorIso (α_ W (X ⊗ (Y ⊗ Z)) E.1).symm (Iso.refl Q.1)) (Iso.refl S.1) ≪≫
  tensorIso (α_ (W ⊗ (X ⊗ (Y ⊗ Z))) E.1 Q.1) (Iso.refl S.1) ≪≫
  α_ (W ⊗ (X ⊗ (Y ⊗ Z))) (E.1 ⊗ Q.1) S.1

end RMod.Classification.CentralWord

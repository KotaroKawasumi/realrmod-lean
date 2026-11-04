import RMod.Classification.Instances.MonoidalWordComparisons
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The contraction-word part of the pentagon

The three-edge route replaces the first pair, last pair, then first pair
of parity labels. The two-edge route replaces the last pair, interchanges
the first two remaining factors, and replaces the last pair again. Keep
both the canonical comparison and the actual braided crossing available;
their discrepancy is the only scalar to be evaluated for parity factors.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification.MonoidalWord

open CategoryTheory MonoidalCategory BraidedCategory

variable {G : Type u} [CommMonoid G] {D : Type v} [Category.{w} D] [MonoidalCategory D]
  (F : Discrete G ⥤ D) [F.Monoidal]

def threeMoves (a b c d e f q _r s t : G)
    (h₁ : a * b = c * d) (h₂ : c * f = e * q) (h₅ : d * t = f * s) :
    (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b)) ⊗ F.obj (Discrete.mk t) ≅
      (F.obj (Discrete.mk e) ⊗ F.obj (Discrete.mk q)) ⊗ F.obj (Discrete.mk s) :=
  (replaceLeft F a b c d t h₁ ≪≫ replaceRight F c d t f s h₅) ≪≫ replaceLeft F c f e q s h₂

def twoMoves (a b _c _d e _f q r s t : G)
    (h₃ : a * r = q * s) (h₄ : b * t = e * r) :
    (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b)) ⊗ F.obj (Discrete.mk t) ≅
      (F.obj (Discrete.mk e) ⊗ F.obj (Discrete.mk q)) ⊗ F.obj (Discrete.mk s) :=
  (replaceRight F a b t e r h₄ ≪≫ replaceLeft F a e e a r (mul_comm a e)) ≪≫
    replaceRight F e a r q s h₃

def twoBraidedMoves [BraidedCategory D] (a b _c _d e _f q r s t : G)
    (h₃ : a * r = q * s) (h₄ : b * t = e * r) :
    (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b)) ⊗ F.obj (Discrete.mk t) ≅
      (F.obj (Discrete.mk e) ⊗ F.obj (Discrete.mk q)) ⊗ F.obj (Discrete.mk s) :=
  (replaceRight F a b t e r h₄ ≪≫
    tensorIso (β_ (F.obj (Discrete.mk a)) (F.obj (Discrete.mk e)))
      (Iso.refl (F.obj (Discrete.mk r)))) ≪≫ replaceRight F e a r q s h₃

end RMod.Classification.MonoidalWord

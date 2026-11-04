import RMod.Classification.Instances.WordPentagon
import RMod.Classification.Proofs.TripleWordComparisons

/-!
# Canonical contraction-word pentagon

Replacing either adjacent pair is the canonical comparison of the entire
triple. Consecutive replacements therefore compose to that same triple
comparison on both routes. The discrete source has at most one map with
the required endpoints, so the particular equality witnesses disappear.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification.MonoidalWord

open CategoryTheory MonoidalCategory

variable {G : Type u} [CommMonoid G] {D : Type v} [Category.{w} D] [MonoidalCategory D]
  (F : Discrete G ⥤ D) [F.Monoidal]

theorem threeMoves_eq_twoMoves (a b c d e f q r s t : G)
    (h₁ : a * b = c * d) (h₂ : c * f = e * q) (h₃ : a * r = q * s)
    (h₄ : b * t = e * r) (h₅ : d * t = f * s) :
    threeMoves F a b c d e f q r s t h₁ h₂ h₅ = twoMoves F a b c d e f q r s t h₃ h₄ := by
  simp only [threeMoves, twoMoves, replaceLeft_eq_tripleCompare, replaceRight_eq_tripleCompare,
    tripleCompare_trans]

end RMod.Classification.MonoidalWord

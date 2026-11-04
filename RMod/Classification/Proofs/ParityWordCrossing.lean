import RMod.Classification.Proofs.ParityCenterFunctor
import RMod.Classification.Proofs.WordPentagon

/-!
# The scalar discrepancy of the actual parity crossing

The canonical pair replacement multiplies, transports the parity sum,
then expands. The actual center braiding followed by multiplication has
the Koszul sign. Cancelling the invertible multiplication identifies the
braiding itself with that signed canonical replacement.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory BraidedCategory Superfusion.Category

attribute [local implicit_reducible] CategoryTheory.Center

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem parityCenter_pairCompare_hom (a b c d : ZMod 2) (he : a + b = c + d) :
    (MonoidalWord.pairCompare (parityCenterFunctor C p hp)
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)
      (congrArg Multiplicative.ofAdd he)).hom.f.hom =
    C.data.comp (p.multiplyFactors a b).hom
      (C.data.comp (IsoData.ofEq C.data (congrArg p.factor he)).hom (p.multiplyFactors c d).inv) := by
  change C.data.comp (p.multiplyFactors a b).hom
    (C.data.comp ((parityCenterFunctor C p hp).map
      (Discrete.eqToIso (congrArg Multiplicative.ofAdd he)).hom).f.hom
      (factorMultiplyCenterIso C p hp c d).inv.f.hom) = _
  rw [parityCenterFunctor_map, center_eqToHom, factorMultiplyCenterIso_inv]
  rfl

theorem parityCenter_braiding_eq_pairCompare (a b : ZMod 2) :
    (β_ (factorCenter C p hp a) (factorCenter C p hp b)).hom.f.hom =
      C.data.smul ((-1 : ℝ) ^ (a * b).val)
        (MonoidalWord.pairCompare (parityCenterFunctor C p hp)
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) (Multiplicative.ofAdd b) (Multiplicative.ofAdd a)
          (congrArg Multiplicative.ofAdd (add_comm a b))).hom.f.hom := by
  rw [parityCenter_pairCompare_hom C p hp a b b a (add_comm a b),
    factorCenter_braiding_hom C p hp a b]
  have he := hp.moveFactor_multiply C.laws a b
  have hh := congrArg (fun f => C.data.comp f (p.multiplyFactors b a).inv) he
  rw [C.laws.comp_assoc, (hp.multiplyFactors_evenIso C.laws b a).hom_inv, C.laws.comp_id,
    C.laws.smul_comp, C.laws.comp_assoc] at hh
  exact hh

/-- Only the exchange of the first and fourth parity labels contributes a
scalar to the two-edge contraction route. -/
theorem parityCenter_twoBraidedMoves_sign (a b c d e f q r s t : ZMod 2)
    (h₃ : a + r = q + s) (h₄ : b + t = e + r) :
    (MonoidalWord.twoBraidedMoves (parityCenterFunctor C p hp)
      (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (.ofAdd e) (.ofAdd f)
      (.ofAdd q) (.ofAdd r) (.ofAdd s) (.ofAdd t)
      (congrArg Multiplicative.ofAdd h₃) (congrArg Multiplicative.ofAdd h₄)).hom.f.hom =
      C.data.smul ((-1 : ℝ) ^ (a * e).val)
        (MonoidalWord.twoMoves (parityCenterFunctor C p hp)
          (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (.ofAdd e) (.ofAdd f)
          (.ofAdd q) (.ofAdd r) (.ofAdd s) (.ofAdd t)
          (congrArg Multiplicative.ofAdd h₃) (congrArg Multiplicative.ofAdd h₄)).hom.f.hom := by
  let A := (MonoidalWord.replaceRight (parityCenterFunctor C p hp)
    (.ofAdd a) (.ofAdd b) (.ofAdd t) (.ofAdd e) (.ofAdd r)
    (congrArg Multiplicative.ofAdd h₄)).hom.f.hom
  let B := (MonoidalWord.replaceRight (parityCenterFunctor C p hp)
    (.ofAdd e) (.ofAdd a) (.ofAdd r) (.ofAdd q) (.ofAdd s)
    (congrArg Multiplicative.ofAdd h₃)).hom.f.hom
  change C.data.comp (C.data.comp A
    (C.data.tensorHom (β_ (factorCenter C p hp a) (factorCenter C p hp e)).hom.f.hom
      (C.data.id (p.factor r)))) B =
    C.data.smul ((-1 : ℝ) ^ (a * e).val)
      (C.data.comp (C.data.comp A
        (C.data.tensorHom (MonoidalWord.pairCompare (parityCenterFunctor C p hp)
          (.ofAdd a) (.ofAdd e) (.ofAdd e) (.ofAdd a)
          (congrArg Multiplicative.ofAdd (add_comm a e))).hom.f.hom
          (C.data.id (p.factor r)))) B)
  rw [parityCenter_braiding_eq_pairCompare C p hp a e]
  have hs {U V X Y Z : C.data.Obj}
      (l : C.data.Hom U (C.data.tensorObj X Z)) (m : C.data.Hom X Y)
      (n : C.data.Hom (C.data.tensorObj Y Z) V) (z : ℝ) :
      C.data.comp (C.data.comp l (C.data.tensorHom (C.data.smul z m) (C.data.id Z))) n =
        C.data.smul z (C.data.comp (C.data.comp l (C.data.tensorHom m (C.data.id Z))) n) := by
    rw [C.laws.tensor_smul_left, C.laws.comp_smul, C.laws.smul_comp]
  exact hs A _ B _

/-- The contraction words on the two pentagon routes differ by the
fermionic sign. Ordinary objects and their half-braidings are treated
separately when these words are inserted into the full normalizers. -/
theorem parityCenter_contractionWord_sign (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₃ : a + r = q + s)
    (h₄ : b + t = e + r) (h₅ : d + t = f + s) :
    (MonoidalWord.twoBraidedMoves (parityCenterFunctor C p hp)
      (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (.ofAdd e) (.ofAdd f)
      (.ofAdd q) (.ofAdd r) (.ofAdd s) (.ofAdd t)
      (congrArg Multiplicative.ofAdd h₃) (congrArg Multiplicative.ofAdd h₄)).hom.f.hom =
      C.data.smul ((-1 : ℝ) ^ (a * e).val)
        (MonoidalWord.threeMoves (parityCenterFunctor C p hp)
          (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (.ofAdd e) (.ofAdd f)
          (.ofAdd q) (.ofAdd r) (.ofAdd s) (.ofAdd t)
          (congrArg Multiplicative.ofAdd h₁) (congrArg Multiplicative.ofAdd h₂)
          (congrArg Multiplicative.ofAdd h₅)).hom.f.hom := by
  rw [parityCenter_twoBraidedMoves_sign C p hp a b c d e f q r s t h₃ h₄]
  rw [MonoidalWord.threeMoves_eq_twoMoves (parityCenterFunctor C p hp)
    (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (.ofAdd e) (.ofAdd f)
    (.ofAdd q) (.ofAdd r) (.ofAdd s) (.ofAdd t)
    (congrArg Multiplicative.ofAdd h₁) (congrArg Multiplicative.ofAdd h₂)
    (congrArg Multiplicative.ofAdd h₃) (congrArg Multiplicative.ofAdd h₄)
    (congrArg Multiplicative.ofAdd h₅)]

end RMod.Classification

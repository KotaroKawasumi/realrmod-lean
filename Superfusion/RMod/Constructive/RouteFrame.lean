import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-!
# Computable parity-aligned route frames

This data-only module flattens a pair of even-first frames

`Fin (p + q) × Fin (r + s)`

into the parity-aligned composite frame

`Fin ((p * r + q * s) + (p * s + q * r))`.

The equivalence is assembled only from the standard computable `Fin`, sum,
and product equivalences.  The accompanying laws identify its numerical
formula and prove that it preserves the sum of the two input parities.
-/

set_option autoImplicit false

namespace Superfusion
namespace RMod
namespace ConstructiveRouteFrame

/-! ## Frame parities -/

/-- Parity of an index in an even-first frame `Fin (p + q)`. -/
def frameParity (p q : ℕ) (i : Fin (p + q)) : ZMod 2 :=
  if i.val < p then 0 else 1

/-- Parity of a pair of indices before collapsing the two frames. -/
def pairParity (p q r s : ℕ)
    (x : Fin (p + q) × Fin (r + s)) : ZMod 2 :=
  frameParity p q x.1 + frameParity r s x.2

/-- Parity of an index in the parity-aligned flattened frame. -/
def flatParity (p q r s : ℕ)
    (i : Fin ((p * r + q * s) + (p * s + q * r))) : ZMod 2 :=
  match finSumFinEquiv.symm i with
  | Sum.inl _ => 0
  | Sum.inr _ => 1

@[simp]
theorem frameParity_castAdd (p q : ℕ) (i : Fin p) :
    frameParity p q (Fin.castAdd q i) = 0 := by
  simp [frameParity]

@[simp]
theorem frameParity_natAdd (p q : ℕ) (i : Fin q) :
    frameParity p q (Fin.natAdd p i) = 1 := by
  simp [frameParity]

/-- The sum-block definition of flat parity agrees with the numerical
even-first cutoff. -/
theorem flatParity_eq_frameParity (p q r s : ℕ)
    (i : Fin ((p * r + q * s) + (p * s + q * r))) :
    flatParity p q r s i =
      frameParity (p * r + q * s) (p * s + q * r) i := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i <;> simp [flatParity]

/-! ## The computable parity-aligned equivalence -/

/-- Sort the four blocks of `(p | q) × (r | s)` into total-even blocks
`p × r`, `q × s`, followed by total-odd blocks `p × s`, `q × r`, and
flatten each product and sum. -/
def parityBlockEquiv (p q r s : ℕ) :
    (Fin p ⊕ Fin q) × (Fin r ⊕ Fin s) ≃
      Fin (p * r + q * s) ⊕ Fin (p * s + q * r) :=
  (Equiv.sumProdDistrib _ _ _).trans <|
    (Equiv.sumCongr (Equiv.prodSumDistrib _ _ _)
      (Equiv.prodSumDistrib _ _ _)).trans <|
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans <|
    (Equiv.sumSumSumComm _ _ _ _).trans <|
    Equiv.sumCongr
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
        finSumFinEquiv)
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
        finSumFinEquiv)

/-- The parity-aligned pair-frame equivalence, with a single `Fin` on both
the input factors and the output. -/
def frameEquiv (p q r s : ℕ) :
    Fin (p + q) × Fin (r + s) ≃
      Fin ((p * r + q * s) + (p * s + q * r)) :=
  ((finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).trans
    (parityBlockEquiv p q r s)).trans finSumFinEquiv

/-- The collapse equivalence preserves parity. -/
theorem frameEquiv_parity (p q r s : ℕ)
    (x : Fin (p + q) × Fin (r + s)) :
    frameParity p q x.1 + frameParity r s x.2 =
      flatParity p q r s (frameEquiv p q r s x) := by
  rcases x with ⟨x, y⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective y
  rcases i with i | i <;> rcases j with j | j <;>
    simp [flatParity, frameEquiv, parityBlockEquiv,
      Equiv.sumSumSumComm, frameParity]
  rfl

theorem pairParity_frameEquiv (p q r s : ℕ)
    (x : Fin (p + q) × Fin (r + s)) :
    pairParity p q r s x = flatParity p q r s (frameEquiv p q r s x) := by
  simpa only [pairParity] using frameEquiv_parity p q r s x

/-! ## Numerical formula and inverse laws -/

/-- Natural-number formula used by the raw connector tables for the
parity-aligned position of a pair of even-first frame indices. -/
def collapsePositionNat (p q r s i j : ℕ) : ℕ :=
  if i < p then
    if j < r then i * r + j
    else p * r + q * s + i * s + (j - r)
  else
    if j < r then p * r + q * s + p * s + (i - p) * r + j
    else p * r + (i - p) * s + (j - r)

/-- The standard-equivalence construction computes the same numerical
position as `collapsePositionNat`. -/
theorem frameEquiv_val (p q r s : ℕ)
    (i : Fin (p + q)) (j : Fin (r + s)) :
    (frameEquiv p q r s (i, j)).val =
      collapsePositionNat p q r s i.val j.val := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [frameEquiv, parityBlockEquiv, collapsePositionNat,
      Equiv.sumSumSumComm, Nat.mul_comm] <;> omega

/-- The raw numerical position is bounded by the composite frame rank. -/
theorem collapsePositionNat_lt (p q r s : ℕ)
    (i : Fin (p + q)) (j : Fin (r + s)) :
    collapsePositionNat p q r s i.val j.val <
      (p * r + q * s) + (p * s + q * r) := by
  rw [← frameEquiv_val]
  exact (frameEquiv p q r s (i, j)).isLt

/-- Typed inverse of the numerical parity-aligned flattening. -/
def unframeEquiv (p q r s : ℕ)
    (n : Fin ((p * r + q * s) + (p * s + q * r))) :
    Fin (p + q) × Fin (r + s) :=
  (frameEquiv p q r s).symm n

@[simp]
theorem unframeEquiv_frameEquiv (p q r s : ℕ)
    (x : Fin (p + q) × Fin (r + s)) :
    unframeEquiv p q r s (frameEquiv p q r s x) = x :=
  (frameEquiv p q r s).left_inv x

@[simp]
theorem frameEquiv_unframeEquiv (p q r s : ℕ)
    (n : Fin ((p * r + q * s) + (p * s + q * r))) :
    frameEquiv p q r s (unframeEquiv p q r s n) = n :=
  (frameEquiv p q r s).right_inv n

/-- Applying the raw numerical formula to the typed inverse recovers the
flat index value. -/
theorem collapsePositionNat_unframeEquiv (p q r s : ℕ)
    (n : Fin ((p * r + q * s) + (p * s + q * r))) :
    collapsePositionNat p q r s (unframeEquiv p q r s n).1.val
        (unframeEquiv p q r s n).2.val = n.val := by
  rw [← frameEquiv_val, frameEquiv_unframeEquiv]

end ConstructiveRouteFrame
end RMod
end Superfusion

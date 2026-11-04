/-
Superfusion / Cochain / CyclicH4

**`H⁴(ℤ/8; F₂) = ℤ/2`, constructively** — the finite `F₂` obligation named
`H4Detects` in `GaugeChi/HchiProto.lean`, discharged with **no certificate
data at all**: every step is a closed-form identity, and the only `decide`
calls are on the 8-element group itself (at most 512 cases) or on a handful
of `F₂` scalars.

The route is the comparison of the bar resolution of a cyclic group with its
standard length-two periodic resolution, rewritten so that no resolution ever
appears.  What survives is:

* `cc` — the carry two-cocycle `cc a b = ⌊(rep a + rep b)/8⌋`, whose class
  generates `H²(ℤ/8;F₂)`; `kappa = cc ⌣ cc` generates `H⁴`;
* one **normalisation coboundary** `nrm s x y z = s x 1 y z`, after which
  `sn s a 1 c d = 0` (`sn_norm`);
* the **norm two-cocycle** `Psi s x y = ∑ k, s x y k (gm 1)`, a normalised
  `F₂`-valued 2-cocycle (`Psi_cocycle`, `Psi_norm`);
* the classical `H²` computation for a cyclic group (`h2_main`):
  `Psi a b = A a + A b + A (a*b) + cc a b * lam2`, with
  `A x = ∑_{i < rep x} Psi (gm i) (gm 1)` — an eight-step induction along the
  generator;
* the **homotopy** `uu`, three terms wide, with
  `d₃ (uu s) = s + lam2 · kappa` (`uu_main`).

Applying the weight-four detector `lam` (which kills `B⁴` — `lam_d₃` — and
has `lam kappa = 1`) to `uu_main` identifies `lam2 = lam`, so `lam s = 0`
forces `s = d₃ (uu (sn s) + nrm s)`.  That is `h4Detects`.

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.Cochain.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

namespace Superfusion

namespace CyclicH4

open Finset

/-! ## 0. `F₂` scalar identities (all `decide`, ≤ 4096 closed cases) -/

theorem sub_eq_add₂ (x y : ZMod 2) : x - y = x + y := by revert x y; decide

theorem add_self₂ (x : ZMod 2) : x + x = 0 := by revert x; decide

private theorem z2_split : ∀ X Y : ZMod 2, X = Y + X + Y := by decide

private theorem z2_nocarry : ∀ X Y : ZMod 2, X + Y + X + Y = 0 := by decide

private theorem z2_carry : ∀ X Y Z : ZMod 2, X + Z + Y + X + Y = 1 * Z := by decide

private theorem z2_succ : ∀ Z X Y W : ZMod 2, Z + X + Y = W → X = Y + Z + W := by decide

private theorem z2_rearr : ∀ P X Y Z W : ZMod 2, P = X + Y + Z + W → X + Y + Z = P + W := by
  decide

private theorem z2_sum4 : ∀ A B C D : ZMod 2, A + B + C + D = 0 → B + C + D = A := by decide

private theorem z2_base : ∀ X : ZMod 2, (0 : ZMod 2) = X + 0 + X + 0 := by decide

private theorem z2_h2step : ∀ x p q r A1 A2 A3 L c1 c2 c3 c4 : ZMod 2,
    p + q + x + r = 0 → r = A1 + A2 + A3 + c1 * L → c2 + c3 + c4 + c1 = 0 →
    x = A1 + (A2 + p + c2 * L) + (A3 + q + c3 * L) + c4 * L := by decide

private theorem z2_nrm : ∀ x1 x2 x3 x4 x5 x6 x7 : ZMod 2,
    x1 + x2 + x2 + x3 + x4 + x5 = 0 → x6 + x7 + x3 + x4 + x5 = x6 + x7 + x1 := by decide

private theorem z2_snorm : ∀ x y : ZMod 2, x + (y + x + y) = 0 := by decide

private theorem z2_G : ∀ x1 x2 x3 x4 : ZMod 2, x1 + x2 + x3 + x4 + x4 + x4 = 0 →
    x1 + x2 + x3 = x4 := by decide

private theorem z2_br : ∀ x1 x2 x3 x4 x5 x6 : ZMod 2,
    x1 + x2 + x3 + x4 + x5 + x6 = 0 → x1 + x2 + x3 = x4 + x5 + x6 := by decide

private theorem z2_psi : ∀ A B C D E : ZMod 2, A + B + C + D + E + E = 0 →
    A + B + C + D = 0 := by decide

private theorem z2_move : ∀ X Y Z : ZMod 2, X = Y + Z → Y = X + Z := by decide

private theorem z2_back : ∀ X Y : ZMod 2, X = X + Y + Y := by decide

/-! ## 1. The group `ℤ/8`, its representatives and the carry cocycle -/

/-- The group, written multiplicatively (the shape `d₃`/`d₄` want). -/
abbrev G8 := Multiplicative (ZMod 8)

/-- The canonical representative in `{0,…,7}`. -/
def rep (a : G8) : ℕ := (Multiplicative.toAdd a).val

/-- The group element `n mod 8`. -/
def gm (n : ℕ) : G8 := Multiplicative.ofAdd (n : ZMod 8)

/-- The carry, as a natural number. -/
def ccN (a b : G8) : ℕ := if 8 ≤ rep a + rep b then 1 else 0

/-- **The carry two-cocycle** — a representative of the generator of
`H²(ℤ/8;F₂)`. -/
def cc (a b : G8) : ZMod 2 := (ccN a b : ZMod 2)

theorem rep_lt (a : G8) : rep a < 8 := by revert a; decide

theorem gm_rep (a : G8) : gm (rep a) = a := by revert a; decide

theorem rep_gm {i : ℕ} (h : i < 8) : rep (gm i) = i := by
  interval_cases i <;> decide

theorem rep_gm_one : rep (gm 1) = 1 := by decide

theorem rep_one : rep 1 = 0 := by decide

theorem gm_zero : gm 0 = 1 := by decide

theorem gm_add (m n : ℕ) : gm (m + n) = gm m * gm n := by
  simp only [gm, Nat.cast_add, ofAdd_add]

/-- The defining property of the carry. -/
theorem rep_mul_add (a b : G8) : rep (a * b) + 8 * ccN a b = rep a + rep b := by
  revert a b; decide

/-- `cc` is a two-cocycle. -/
theorem cc_cocycle (a b c : G8) : cc b c + cc (a * b) c + cc a (b * c) + cc a b = 0 := by
  revert a b c; decide

theorem cc_right_one (a : G8) : cc a 1 = 0 := by revert a; decide

/-! ## 2. Sums over `ℤ/8` -/

/-- `Fin 8 ≃ G8`, used only to convert `range 8` sums into `univ` sums. -/
def eG8 : Fin 8 ≃ G8 where
  toFun i := gm i
  invFun a := ⟨rep a, rep_lt a⟩
  left_inv i := Fin.ext (rep_gm i.isLt)
  right_inv a := gm_rep a

theorem sum_range_eq_univ (F : G8 → ZMod 2) :
    ∑ i ∈ range 8, F (gm i) = ∑ k : G8, F k := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => F (gm i)) 8]
  exact Fintype.sum_equiv eG8 _ _ (fun _ => rfl)

/-- Partial sums of `F` along the canonical enumeration. -/
def T (F : G8 → ZMod 2) (m : ℕ) : ZMod 2 := ∑ i ∈ range m, F (gm i)

theorem T_zero (F : G8 → ZMod 2) : T F 0 = 0 := by simp [T]

theorem T_add (F : G8 → ZMod 2) (m n : ℕ) :
    T F (m + n) = T F m + ∑ i ∈ range n, F (gm (m + i)) :=
  Finset.sum_range_add _ _ _

theorem T_shift (F : G8 → ZMod 2) (m : ℕ) :
    ∑ i ∈ range 8, F (gm (m + i)) = T F 8 := by
  have h : ∀ i : ℕ, F (gm (m + i)) = (fun k => F (gm m * k)) (gm i) := by
    intro i; rw [gm_add]
  simp only [h]
  rw [sum_range_eq_univ (fun k => F (gm m * k)), T, sum_range_eq_univ F]
  exact Fintype.sum_equiv (Equiv.mulLeft (gm m)) _ _ (fun _ => rfl)

theorem T_period (F : G8 → ZMod 2) (m : ℕ) : T F (m + 8) = T F m + T F 8 := by
  rw [T_add, T_shift]

/-- **The carry lemma.**  Translating a partial sum by `c` costs exactly one
full period, and exactly when `c * d` wraps. -/
theorem T_carry (F : G8 → ZMod 2) (c d : G8) :
    (∑ i ∈ range (rep d), F (c * gm i)) + T F (rep (c * d)) + T F (rep c)
      = cc c d * T F 8 := by
  have hrew : ∀ i : ℕ, F (c * gm i) = F (gm (rep c + i)) := by
    intro i; rw [gm_add, gm_rep]
  have hsplit : (∑ i ∈ range (rep d), F (c * gm i))
      = T F (rep c + rep d) + T F (rep c) := by
    simp only [hrew]
    rw [T_add]
    exact z2_split _ _
  rw [hsplit]
  have hmul := rep_mul_add c d
  by_cases hc : 8 ≤ rep c + rep d
  · have h1 : ccN c d = 1 := by simp [ccN, hc]
    have h2 : rep c + rep d = rep (c * d) + 8 := by omega
    have h3 : cc c d = 1 := by simp [cc, h1]
    rw [h2, T_period, h3]
    exact z2_carry _ _ _
  · have h1 : ccN c d = 0 := by simp [ccN, hc]
    have h2 : rep (c * d) = rep c + rep d := by omega
    have h3 : cc c d = 0 := by simp [cc, h1]
    rw [h2, h3, zero_mul]
    exact z2_nocarry _ _

/-- The primitive of `F` along the canonical enumeration. -/
def AA (F : G8 → ZMod 2) (x : G8) : ZMod 2 := T F (rep x)

theorem AA_one (F : G8 → ZMod 2) : AA F 1 = 0 := by
  simp [AA, rep_one, T_zero]

/-- One step of `AA` along the generator. -/
theorem AA_succ (F : G8 → ZMod 2) (c : G8) :
    AA F (c * gm 1) = AA F c + F c + cc c (gm 1) * T F 8 := by
  have h := T_carry F c (gm 1)
  rw [rep_gm_one] at h
  simp only [Finset.sum_range_one, gm_zero, mul_one] at h
  simp only [AA]
  exact z2_succ _ _ _ _ h

/-! ## 3. `H²` of a cyclic group -/

section H2

variable (P : G8 → G8 → ZMod 2)

/-- Restriction of a 2-cochain to the generator. -/
def gen1 : G8 → ZMod 2 := fun i => P i (gm 1)

/-- The `H²` invariant: the sum of the generator column. -/
def lam2 : ZMod 2 := T (gen1 P) 8

/-- **`H²(ℤ/8;F₂) = ℤ/2`.**  A normalised `F₂`-valued 2-cocycle differs from
`cc` times its invariant by the explicit coboundary of `AA (gen1 P)`. -/
theorem h2_main (hcoc : ∀ a b c, P b c + P (a * b) c + P a (b * c) + P a b = 0)
    (hnorm : ∀ a, P a 1 = 0) (a b : G8) :
    P a b = AA (gen1 P) a + AA (gen1 P) b + AA (gen1 P) (a * b) + cc a b * lam2 P := by
  have step : ∀ b : G8,
      (∀ a, P a b = AA (gen1 P) a + AA (gen1 P) b + AA (gen1 P) (a * b) + cc a b * lam2 P) →
      ∀ a, P a (b * gm 1) = AA (gen1 P) a + AA (gen1 P) (b * gm 1)
        + AA (gen1 P) (a * (b * gm 1)) + cc a (b * gm 1) * lam2 P := by
    intro b ih a
    have hc := hcoc a b (gm 1)
    have ihab := ih a
    have hb := AA_succ (gen1 P) b
    have hab := AA_succ (gen1 P) (a * b)
    have hcc := cc_cocycle a b (gm 1)
    have hassoc : a * (b * gm 1) = a * b * gm 1 := (mul_assoc _ _ _).symm
    rw [hassoc, hb, hab]
    simp only [gen1, lam2] at ihab hc hcc ⊢
    exact z2_h2step _ _ _ _ _ _ _ _ _ _ _ _ hc ihab hcc
  have base : ∀ a, P a 1 = AA (gen1 P) a + AA (gen1 P) 1 + AA (gen1 P) (a * 1)
      + cc a 1 * lam2 P := by
    intro a
    rw [hnorm a, AA_one, mul_one, cc_right_one, zero_mul]
    exact z2_base _
  have h1 := step 1 base
  have h2 := step _ h1
  have h3 := step _ h2
  have h4 := step _ h3
  have h5 := step _ h4
  have h6 := step _ h5
  have h7 := step _ h6
  have hcases : b = 1 ∨ b = 1 * gm 1 ∨ b = 1 * gm 1 * gm 1 ∨ b = 1 * gm 1 * gm 1 * gm 1 ∨
      b = 1 * gm 1 * gm 1 * gm 1 * gm 1 ∨ b = 1 * gm 1 * gm 1 * gm 1 * gm 1 * gm 1 ∨
      b = 1 * gm 1 * gm 1 * gm 1 * gm 1 * gm 1 * gm 1 ∨
      b = 1 * gm 1 * gm 1 * gm 1 * gm 1 * gm 1 * gm 1 * gm 1 := by
    revert b; decide
  rcases hcases with h | h | h | h | h | h | h | h <;> subst h
  · exact base a
  · exact h1 a
  · exact h2 a
  · exact h3 a
  · exact h4 a
  · exact h5 a
  · exact h6 a
  · exact h7 a

end H2

/-! ## 4. Degree-four cochains: unfolding and normalisation -/

theorem d₃_two (f : G8 → G8 → G8 → ZMod 2) (a b c d : G8) :
    d₃ f a b c d = f b c d + f (a * b) c d + f a (b * c) d + f a b (c * d) + f a b c := by
  simp only [d₃, sub_eq_add₂]

theorem d₄_two (f : G8 → G8 → G8 → G8 → ZMod 2) (a b c d e : G8) :
    d₄ f a b c d e = f b c d e + f (a * b) c d e + f a (b * c) d e + f a b (c * d) e
      + f a b c (d * e) + f a b c d := by
  simp only [d₄, sub_eq_add₂]

section Normalise

variable (s : G8 → G8 → G8 → G8 → ZMod 2)

/-- The normalising 3-cochain. -/
def nrm : G8 → G8 → G8 → ZMod 2 := fun x y z => s x 1 y z

/-- The cocycle normalised in its second slot. -/
def sn : G8 → G8 → G8 → G8 → ZMod 2 := fun a b c d => s a b c d + d₃ (nrm s) a b c d

variable (hs : ∀ a b c d e, d₄ s a b c d e = 0)

include hs

theorem d₃_nrm (a b c d : G8) :
    d₃ (nrm s) a b c d = s b 1 c d + s (a * b) 1 c d + s 1 b c d := by
  have h := hs a 1 b c d
  rw [d₄_two] at h
  simp only [mul_one, one_mul] at h
  rw [d₃_two]
  simp only [nrm]
  exact z2_nrm _ _ _ _ _ _ _ h

theorem sn_cocycle (a b c d e : G8) : d₄ (sn s) a b c d e = 0 := by
  have hadd : ∀ a b c d e, d₄ (sn s) a b c d e
      = d₄ s a b c d e + d₄ (d₃ (nrm s)) a b c d e := by
    intro a b c d e
    simp only [d₄_two, sn]
    ring
  rw [hadd, hs, d₄_d₃, add_zero]

theorem sn_norm (a c d : G8) : sn s a 1 c d = 0 := by
  simp only [sn]
  rw [d₃_nrm s hs]
  simp only [mul_one]
  exact z2_snorm _ _

end Normalise

/-! ## 5. The norm two-cocycle of a four-cocycle -/

section Psi

variable (s : G8 → G8 → G8 → G8 → ZMod 2)

/-- The norm 2-cochain: the sum of the `(·,·,k,gm 1)` column. -/
def Psi : G8 → G8 → ZMod 2 := fun x y => ∑ k : G8, s x y k (gm 1)

variable (hs : ∀ a b c d e, d₄ s a b c d e = 0)

include hs

theorem Psi_cocycle (a b c : G8) :
    Psi s b c + Psi s (a * b) c + Psi s a (b * c) + Psi s a b = 0 := by
  have h : ∑ k : G8, d₄ s a b c k (gm 1) = 0 := by simp [hs]
  simp only [d₄_two, Finset.sum_add_distrib] at h
  have e1 : ∑ k : G8, s a b (c * k) (gm 1) = Psi s a b :=
    Fintype.sum_equiv (Equiv.mulLeft c) _ _ (fun _ => rfl)
  have e2 : ∑ k : G8, s a b c (k * gm 1) = ∑ k : G8, s a b c k :=
    Fintype.sum_equiv (Equiv.mulRight (gm 1)) _ _ (fun _ => rfl)
  rw [e1, e2] at h
  simp only [Psi]
  exact z2_psi _ _ _ _ _ h

end Psi

theorem Psi_norm (s : G8 → G8 → G8 → G8 → ZMod 2) (hn : ∀ a c d, s a 1 c d = 0) (a : G8) :
    Psi s a 1 = 0 := by
  simp [Psi, hn]

/-! ## 6. The homotopy -/

section Homotopy

variable (s : G8 → G8 → G8 → G8 → ZMod 2)

/-- **The explicit contracting homotopy**, three terms wide. -/
def uu : G8 → G8 → G8 → ZMod 2 := fun x y z =>
  cc y z * AA (gen1 (Psi s)) x + s x y 1 1 + ∑ i ∈ range (rep z), s x y (gm i) (gm 1)

variable (hs : ∀ a b c d e, d₄ s a b c d e = 0) (hn : ∀ a c d, s a 1 c d = 0)

include hs hn

/-- **The homotopy identity.**  For a four-cocycle normalised in its second
slot, `d₃ (uu s)` is `s` plus the invariant times the generator `cc ⌣ cc`. -/
theorem uu_main (a b c d : G8) :
    d₃ (uu s) a b c d = s a b c d + lam2 (Psi s) * (cc a b * cc c d) := by
  -- (i) the `s · 1 1` column
  have hG : s b c 1 1 + s (a * b) c 1 1 + s a (b * c) 1 1 = s a b c 1 := by
    have h := hs a b c 1 1
    rw [d₄_two] at h
    simp only [mul_one] at h
    exact z2_G _ _ _ _ h
  -- (ii) the `range (rep d)` sums
  have hbr : ∀ i ∈ range (rep d), s b c (gm i) (gm 1) + s (a * b) c (gm i) (gm 1)
      + s a (b * c) (gm i) (gm 1)
      = s a b (c * gm i) (gm 1) + (s a b c (gm (i + 1)) + s a b c (gm i)) := by
    intro i _
    have h := hs a b c (gm i) (gm 1)
    rw [d₄_two] at h
    rw [gm_add, ← add_assoc]
    exact z2_br _ _ _ _ _ _ h
  have htel : ∑ i ∈ range (rep d), (s a b c (gm (i + 1)) + s a b c (gm i))
      = s a b c d + s a b c 1 := by
    have h := Finset.sum_range_sub (fun i => s a b c (gm i)) (rep d)
    simp only [sub_eq_add₂] at h
    rw [h, gm_rep, gm_zero]
  have hsum3 : (∑ i ∈ range (rep d), s b c (gm i) (gm 1))
      + (∑ i ∈ range (rep d), s (a * b) c (gm i) (gm 1))
      + (∑ i ∈ range (rep d), s a (b * c) (gm i) (gm 1))
      = (∑ i ∈ range (rep d), s a b (c * gm i) (gm 1)) + s a b c d + s a b c 1 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl hbr, Finset.sum_add_distrib, htel]
    ring
  -- (iii) the carry lemma at `F k = s a b k (gm 1)`
  have hT8 : T (fun k => s a b k (gm 1)) 8 = Psi s a b :=
    sum_range_eq_univ (fun k => s a b k (gm 1))
  have hcar := T_carry (fun k => s a b k (gm 1)) c d
  rw [hT8] at hcar
  simp only [T] at hcar
  -- (iv) the `cc · AA` head, via the `H²` computation
  have hH2 := h2_main (Psi s) (Psi_cocycle s hs) (Psi_norm s hn) a b
  have hAsum : AA (gen1 (Psi s)) a + AA (gen1 (Psi s)) b + AA (gen1 (Psi s)) (a * b)
      = Psi s a b + cc a b * lam2 (Psi s) := z2_rearr _ _ _ _ _ hH2
  have hccsum : cc (b * c) d + cc b (c * d) + cc b c = cc c d :=
    z2_sum4 _ _ _ _ (cc_cocycle b c d)
  have hhead : cc c d * AA (gen1 (Psi s)) b + cc c d * AA (gen1 (Psi s)) (a * b)
      + cc (b * c) d * AA (gen1 (Psi s)) a + cc b (c * d) * AA (gen1 (Psi s)) a
      + cc b c * AA (gen1 (Psi s)) a
      = cc c d * Psi s a b + cc c d * (cc a b * lam2 (Psi s)) := by
    calc cc c d * AA (gen1 (Psi s)) b + cc c d * AA (gen1 (Psi s)) (a * b)
          + cc (b * c) d * AA (gen1 (Psi s)) a + cc b (c * d) * AA (gen1 (Psi s)) a
          + cc b c * AA (gen1 (Psi s)) a
        = cc c d * AA (gen1 (Psi s)) b + cc c d * AA (gen1 (Psi s)) (a * b)
            + (cc (b * c) d + cc b (c * d) + cc b c) * AA (gen1 (Psi s)) a := by ring
      _ = cc c d * (AA (gen1 (Psi s)) a + AA (gen1 (Psi s)) b
            + AA (gen1 (Psi s)) (a * b)) := by rw [hccsum]; ring
      _ = cc c d * (Psi s a b + cc a b * lam2 (Psi s)) := by rw [hAsum]
      _ = cc c d * Psi s a b + cc c d * (cc a b * lam2 (Psi s)) := by ring
  -- assemble
  have hzero1 : s a b 1 1 + s a b 1 1 = 0 := add_self₂ _
  have hzero2 : s a b c 1 + s a b c 1 = 0 := add_self₂ _
  have hzero3 : cc c d * Psi s a b + cc c d * Psi s a b = 0 := add_self₂ _
  have expand : d₃ (uu s) a b c d
      = (cc c d * AA (gen1 (Psi s)) b + cc c d * AA (gen1 (Psi s)) (a * b)
          + cc (b * c) d * AA (gen1 (Psi s)) a + cc b (c * d) * AA (gen1 (Psi s)) a
          + cc b c * AA (gen1 (Psi s)) a)
        + (s b c 1 1 + s (a * b) c 1 1 + s a (b * c) 1 1)
        + (s a b 1 1 + s a b 1 1)
        + ((∑ i ∈ range (rep d), s b c (gm i) (gm 1))
            + (∑ i ∈ range (rep d), s (a * b) c (gm i) (gm 1))
            + (∑ i ∈ range (rep d), s a (b * c) (gm i) (gm 1)))
        + ((∑ i ∈ range (rep (c * d)), s a b (gm i) (gm 1))
            + (∑ i ∈ range (rep c), s a b (gm i) (gm 1))) := by
    rw [d₃_two]; simp only [uu]; ring
  rw [expand, hhead, hG, hsum3, hzero1]
  calc (cc c d * Psi s a b + cc c d * (cc a b * lam2 (Psi s))) + s a b c 1 + 0
        + ((∑ i ∈ range (rep d), s a b (c * gm i) (gm 1)) + s a b c d + s a b c 1)
        + ((∑ i ∈ range (rep (c * d)), s a b (gm i) (gm 1))
            + (∑ i ∈ range (rep c), s a b (gm i) (gm 1)))
      = ((∑ i ∈ range (rep d), s a b (c * gm i) (gm 1))
            + (∑ i ∈ range (rep (c * d)), s a b (gm i) (gm 1))
            + (∑ i ∈ range (rep c), s a b (gm i) (gm 1)))
          + cc c d * Psi s a b + cc c d * (cc a b * lam2 (Psi s))
          + (s a b c 1 + s a b c 1) + s a b c d := by ring
    _ = cc c d * Psi s a b + cc c d * Psi s a b
          + cc c d * (cc a b * lam2 (Psi s)) + 0 + s a b c d := by rw [hcar, hzero2]
    _ = s a b c d + lam2 (Psi s) * (cc a b * cc c d) := by rw [hzero3]; ring

end Homotopy

/-! ## 7. The weight-four detector -/

/-- The minimal-weight functional detecting `H⁴(ℤ/8;F₂)`; its support lies in
the order-two subgroup `{0,4}`. -/
def lam (s : G8 → G8 → G8 → G8 → ZMod 2) : ZMod 2 :=
  s 1 1 (gm 4) (gm 4) + s (gm 4) 1 1 (gm 4)
    + s (gm 4) (gm 4) 1 1 + s (gm 4) (gm 4) (gm 4) (gm 4)

/-- The generator of `H⁴(ℤ/8;F₂)`: the cup square of the carry cocycle. -/
def kappa : G8 → G8 → G8 → G8 → ZMod 2 := fun a b c d => cc a b * cc c d

theorem gm4_sq : (gm 4 * gm 4 : G8) = 1 := by decide

theorem lam_kappa : lam kappa = 1 := by decide

/-- `lam` annihilates coboundaries. -/
theorem lam_d₃ (w : G8 → G8 → G8 → ZMod 2) : lam (d₃ w) = 0 := by
  simp only [lam, d₃_two, one_mul, mul_one, gm4_sq]
  generalize w 1 (gm 4) (gm 4) = A
  generalize w 1 1 1 = B
  generalize w 1 1 (gm 4) = C
  generalize w (gm 4) 1 (gm 4) = D
  generalize w (gm 4) 1 1 = E
  generalize w (gm 4) (gm 4) 1 = F
  generalize w (gm 4) (gm 4) (gm 4) = H
  revert A B C D E F H; decide

theorem lam_add (s t : G8 → G8 → G8 → G8 → ZMod 2) :
    lam (fun a b c d => s a b c d + t a b c d) = lam s + lam t := by
  simp only [lam]; ring

/-! ## 8. The theorem -/

/-- **`H⁴(ℤ/8;F₂) = ℤ/2`, detected by `lam`.**  A four-cocycle killed by the
weight-four detector is the coboundary of an explicit three-cochain. -/
theorem h4Detects (s : G8 → G8 → G8 → G8 → ZMod 2)
    (hs : ∀ a b c d e, d₄ s a b c d e = 0) (hdet : lam s = 0) :
    ∃ u : G8 → G8 → G8 → ZMod 2, ∀ a b c d, s a b c d = d₃ u a b c d := by
  have hsn := sn_cocycle s hs
  have hnn := sn_norm s hs
  have hmain := uu_main (sn s) hsn hnn
  -- the detector computes the invariant
  have hpt : ∀ a b c d, sn s a b c d
      = d₃ (uu (sn s)) a b c d + lam2 (Psi (sn s)) * kappa a b c d := by
    intro a b c d
    simp only [kappa]
    exact z2_move _ _ _ (hmain a b c d)
  have hsum4 : lam (sn s) = lam (d₃ (uu (sn s))) + lam2 (Psi (sn s)) * lam kappa := by
    simp only [lam]
    rw [hpt 1 1 (gm 4) (gm 4), hpt (gm 4) 1 1 (gm 4), hpt (gm 4) (gm 4) 1 1,
      hpt (gm 4) (gm 4) (gm 4) (gm 4)]
    ring
  rw [lam_d₃, lam_kappa, mul_one, zero_add] at hsum4
  have hlamsn : lam (sn s) = lam s := by
    have h : lam (sn s) = lam s + lam (d₃ (nrm s)) := by
      simp only [lam, sn]; ring
    rw [h, lam_d₃, add_zero]
  have hlam : lam2 (Psi (sn s)) = 0 := by rw [← hsum4, hlamsn, hdet]
  refine ⟨fun x y z => uu (sn s) x y z + nrm s x y z, fun a b c d => ?_⟩
  have hd : d₃ (fun x y z => uu (sn s) x y z + nrm s x y z) a b c d
      = d₃ (uu (sn s)) a b c d + d₃ (nrm s) a b c d := by
    simp only [d₃_two]; ring
  rw [hd, hmain a b c d, hlam, zero_mul, add_zero]
  simp only [sn]
  exact z2_back _ _

end CyclicH4

end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.CyclicH4.h2_main
#print axioms Superfusion.CyclicH4.uu_main
#print axioms Superfusion.CyclicH4.lam_d₃
#print axioms Superfusion.CyclicH4.h4Detects

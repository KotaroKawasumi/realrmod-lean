/-
Superfusion / Super / PentagonEdge35

Milestone M7d-5b-4-iii(c), part 4 (repair round): **the signed swap
unit for the (a,b,cd)-cluster edge e35**.

`PentagonFactor35.lean` established that the plain factorization
`quadRoute3 = cluster35Tail3 ∘ cluster35Prefix` (F3′) is *false*: the
two orders of stabilizing `M_σ(T_{a+b}) ᵍ⊗ M_γ(T_{c+d})` differ by
the Koszul-signed layer transposition.  This file constructs the
correcting unit.  Numerical verification against the landed tails
(reproducing the landed `quadRoute2_factor`, `alignedRoute4_factor`
and `alignedRoute5_factor` exactly) shows the honest correction is
conjugation by the **signed permutation unit**

  `swapSign(i, j) = (−1)^{π_σ(I)·π_γ(K)} · [j = φ(i)]`,

where `(I, K)` is the decoding of the flat pentagon-frame index `i`
through the (σ,τ,ρ)-grouping of the landed `cluster13SharedTail`, and
`φ` re-encodes it through the (γ,μ,ν′)-grouping of the landed
`cluster35SharedTail` — a theta-genre sorting discrepancy.  The pure
diagonal `D_ε` alone is *not* sufficient: at the three realizable
size patterns with `fuseSize a b = fuseSize c d = (8,8)` the two
groupings also differ by the genuine permutation `φ` (240 of 256
indices moved at `κ = (1,0)`, 3840 of 4096 at `κ = (8,8)`); at the
other fifteen realizable patterns `φ = id` and the unit degenerates
to the diagonal.  The corrected factorization

  `(cluster35Tail3 ∘ cluster35Prefix)(w)
     = swapSign · quadRoute3(w) · swapSign`

is verified end-to-end in the model (64/64 basis elements at
nondegenerate sizes) and at all 18 realizable size tuples; its Lean
proof is the next round (the E1/E2 stabilization-order comparison on
generators).  Here we deliver:

- `swapSign` with `swapSign_mem_even` and `swapSign_mul_self` —
  `φ` is an involution compatible with the sign and the index
  parity, certified by kernel `decide` after the `fuseSize`
  dichotomy (the three cast identities of the tails cut the 2^7
  size patterns to exactly the 18 realizable ones);
- the edge element `edgeT35 := edge₀ · swapSign` (the amplified
  route intertwiner `pentagonT a b (c+d)` pushed through the shared
  tail, times the swap unit), homogeneous of parity `p(a,b,c+d)`
  and invertible.
-/
import Superfusion.Super.PentagonFactor35

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

/-! ### The layer-swap index involution -/

section SwapIdx

/-- Cast of a flat `p|q`-index along an equality of size pairs. -/
private def sumFinCast {s t : ℕ × ℕ} (h : s = t) :
    Fin s.1 ⊕ Fin s.2 → Fin t.1 ⊕ Fin t.2 :=
  Sum.map (Fin.cast (congrArg Prod.fst h))
    (Fin.cast (congrArg Prod.snd h))

/-- The generic layer-swap index map: decode the flat pentagon-frame
index through the `(s,t,r)`-grouping (the `(ab)`-cluster shared
tail), transpose the two outer layers, and re-encode through the
`(g,m,n)`-grouping (the `(cd)`-cluster shared tail).  Here
`s,g,k,t,r,m,n` play `σ,γ,κ,τ,ρ,μ,ν′`. -/
private def swapIdxGen (s g k t r m n : ℕ × ℕ)
    (hcl : (t.1 * r.1 + t.2 * r.2, t.1 * r.2 + t.2 * r.1)
      = (g.1 * k.1 + g.2 * k.2, g.1 * k.2 + g.2 * k.1))
    (h35 : (s.1 * k.1 + s.2 * k.2, s.1 * k.2 + s.2 * k.1)
      = (m.1 * n.1 + m.2 * n.2, m.1 * n.2 + m.2 * n.1))
    (hout : ((g.1 * m.1 + g.2 * m.2) * n.1
          + (g.1 * m.2 + g.2 * m.1) * n.2,
        (g.1 * m.1 + g.2 * m.2) * n.2
          + (g.1 * m.2 + g.2 * m.1) * n.1)
      = ((s.1 * t.1 + s.2 * t.2) * r.1
          + (s.1 * t.2 + s.2 * t.1) * r.2,
        (s.1 * t.1 + s.2 * t.2) * r.2
          + (s.1 * t.2 + s.2 * t.1) * r.1))
    (i : Fin ((s.1 * t.1 + s.2 * t.2) * r.1
        + (s.1 * t.2 + s.2 * t.1) * r.2)
      ⊕ Fin ((s.1 * t.1 + s.2 * t.2) * r.2
        + (s.1 * t.2 + s.2 * t.1) * r.1)) :
    Fin ((s.1 * t.1 + s.2 * t.2) * r.1
        + (s.1 * t.2 + s.2 * t.1) * r.2)
      ⊕ Fin ((s.1 * t.1 + s.2 * t.2) * r.2
        + (s.1 * t.2 + s.2 * t.1) * r.1) :=
  let zr := (collapseIndexEquiv (s.1 * t.1 + s.2 * t.2)
      (s.1 * t.2 + s.2 * t.1) r.1 r.2).symm i
  let It := (collapseIndexEquiv s.1 s.2 t.1 t.2).symm zr.1
  let Kn := (collapseIndexEquiv g.1 g.2 k.1 k.2).symm
    (sumFinCast hcl (collapseIndexEquiv t.1 t.2 r.1 r.2 (It.2, zr.2)))
  let mn := (collapseIndexEquiv m.1 m.2 n.1 n.2).symm
    (sumFinCast h35 (collapseIndexEquiv s.1 s.2 k.1 k.2 (It.1, Kn.2)))
  sumFinCast hout
    (collapseIndexEquiv (g.1 * m.1 + g.2 * m.2) (g.1 * m.2 + g.2 * m.1)
      n.1 n.2 (collapseIndexEquiv g.1 g.2 m.1 m.2 (Kn.1, mn.1), mn.2))

/-- The Koszul sign exponent of the layer swap at a flat
pentagon-frame index: the product of the `σ`-parity and the
`γ`-parity of its decoding. -/
private def swapParityGen (s g k t r : ℕ × ℕ)
    (hcl : (t.1 * r.1 + t.2 * r.2, t.1 * r.2 + t.2 * r.1)
      = (g.1 * k.1 + g.2 * k.2, g.1 * k.2 + g.2 * k.1))
    (i : Fin ((s.1 * t.1 + s.2 * t.2) * r.1
        + (s.1 * t.2 + s.2 * t.1) * r.2)
      ⊕ Fin ((s.1 * t.1 + s.2 * t.2) * r.2
        + (s.1 * t.2 + s.2 * t.1) * r.1)) : ZMod 2 :=
  let zr := (collapseIndexEquiv (s.1 * t.1 + s.2 * t.2)
      (s.1 * t.2 + s.2 * t.1) r.1 r.2).symm i
  let It := (collapseIndexEquiv s.1 s.2 t.1 t.2).symm zr.1
  let Kn := (collapseIndexEquiv g.1 g.2 k.1 k.2).symm
    (sumFinCast hcl (collapseIndexEquiv t.1 t.2 r.1 r.2 (It.2, zr.2)))
  sumParity s.1 s.2 It.1 * sumParity g.1 g.2 Kn.1

/-- **The swap certificates**: at the standard fusion sizes, the
layer-swap index map is an involution, compatible with the Koszul
sign and with the flat index parity.  The three cast identities of
the landed tails cut the `2^7` size patterns to exactly the 18
realizable ones; each survivor is a kernel `decide` (the largest,
all sizes `(8,8)`, is a 4096-point check). -/
private theorem swapIdxGen_certs (s g k t r m n : ℕ × ℕ)
    (hs : s = (1, 0) ∨ s = (8, 8)) (hg : g = (1, 0) ∨ g = (8, 8))
    (hk : k = (1, 0) ∨ k = (8, 8)) (ht : t = (1, 0) ∨ t = (8, 8))
    (hr : r = (1, 0) ∨ r = (8, 8)) (hm : m = (1, 0) ∨ m = (8, 8))
    (hn : n = (1, 0) ∨ n = (8, 8))
    (hcl : (t.1 * r.1 + t.2 * r.2, t.1 * r.2 + t.2 * r.1)
      = (g.1 * k.1 + g.2 * k.2, g.1 * k.2 + g.2 * k.1))
    (h35 : (s.1 * k.1 + s.2 * k.2, s.1 * k.2 + s.2 * k.1)
      = (m.1 * n.1 + m.2 * n.2, m.1 * n.2 + m.2 * n.1))
    (hout : ((g.1 * m.1 + g.2 * m.2) * n.1
          + (g.1 * m.2 + g.2 * m.1) * n.2,
        (g.1 * m.1 + g.2 * m.2) * n.2
          + (g.1 * m.2 + g.2 * m.1) * n.1)
      = ((s.1 * t.1 + s.2 * t.2) * r.1
          + (s.1 * t.2 + s.2 * t.1) * r.2,
        (s.1 * t.1 + s.2 * t.2) * r.2
          + (s.1 * t.2 + s.2 * t.1) * r.1)) :
    ∀ i, swapIdxGen s g k t r m n hcl h35 hout
        (swapIdxGen s g k t r m n hcl h35 hout i) = i
      ∧ swapParityGen s g k t r hcl
          (swapIdxGen s g k t r m n hcl h35 hout i)
        = swapParityGen s g k t r hcl i
      ∧ sumParity ((s.1 * t.1 + s.2 * t.2) * r.1
            + (s.1 * t.2 + s.2 * t.1) * r.2)
          ((s.1 * t.1 + s.2 * t.2) * r.2
            + (s.1 * t.2 + s.2 * t.1) * r.1)
          (swapIdxGen s g k t r m n hcl h35 hout i)
        = sumParity ((s.1 * t.1 + s.2 * t.2) * r.1
            + (s.1 * t.2 + s.2 * t.1) * r.2)
          ((s.1 * t.1 + s.2 * t.2) * r.2
            + (s.1 * t.2 + s.2 * t.1) * r.1) i := by
  rcases hs with rfl | rfl <;> rcases hg with rfl | rfl <;>
      rcases hk with rfl | rfl <;> rcases ht with rfl | rfl <;>
      rcases hr with rfl | rfl <;> rcases hm with rfl | rfl <;>
      rcases hn with rfl | rfl <;>
    first
      | exact absurd hcl (by decide)
      | exact absurd h35 (by decide)
      | exact absurd hout (by decide)
      | (rw [proof_irrel hcl (by decide), proof_irrel h35 (by decide),
           proof_irrel hout (by decide)]
         set_option maxHeartbeats 400000000 in
         set_option maxRecDepth 100000 in
         decide)

end SwapIdx

/-! ### The signed swap unit and the e35 edge element -/

section Edge35

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The standard fusion sizes take exactly two values (local copy of
the private helper of `PentagonEdge24.lean`). -/
private theorem fuseSize_cases (a b : ZMod 8) :
    fuseSize a b = (1, 0) ∨ fuseSize a b = (8, 8) := by
  unfold fuseSize
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The `(σ,τ,ρ)`-to-`(γ,κ)` cast identity of the `(ab)`-cluster
tail, flat-spelled. -/
private theorem swapCast_cl (a b c d : ZMod 8) :
    ((fuseSize (a + b) c).1 * (fuseSize (a + b + c) d).1
        + (fuseSize (a + b) c).2 * (fuseSize (a + b + c) d).2,
      (fuseSize (a + b) c).1 * (fuseSize (a + b + c) d).2
        + (fuseSize (a + b) c).2 * (fuseSize (a + b + c) d).1)
      = ((fuseSize c d).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize c d).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).1) :=
  sizeL_eq_sizeR (a + b) c d

/-- The `(σ,κ)`-to-`(μ,ν′)` cast identity of the `(cd)`-cluster
tail, flat-spelled. -/
private theorem swapCast_35 (a b c d : ZMod 8) :
    ((fuseSize a b).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize a b).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize a b).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize a b).2 * (fuseSize (a + b) (c + d)).1)
      = ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2,
      (fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1) :=
  sizeL_eq_sizeR a b (c + d)

/-- The `(γ,μ,ν′)`-to-`(σ,τ,ρ)` output cast identity, flat-spelled
(a 4096-case kernel `decide`). -/
private theorem swapCast_out : ∀ a b c d : ZMod 8,
    (((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          * (fuseSize a (b + (c + d))).1
        + ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)
          * (fuseSize a (b + (c + d))).2,
      ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          * (fuseSize a (b + (c + d))).2
        + ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)
          * (fuseSize a (b + (c + d))).1)
      = (((fuseSize a b).1 * (fuseSize (a + b) c).1
          + (fuseSize a b).2 * (fuseSize (a + b) c).2)
          * (fuseSize (a + b + c) d).1
        + ((fuseSize a b).1 * (fuseSize (a + b) c).2
          + (fuseSize a b).2 * (fuseSize (a + b) c).1)
          * (fuseSize (a + b + c) d).2,
      ((fuseSize a b).1 * (fuseSize (a + b) c).1
          + (fuseSize a b).2 * (fuseSize (a + b) c).2)
          * (fuseSize (a + b + c) d).2
        + ((fuseSize a b).1 * (fuseSize (a + b) c).2
          + (fuseSize a b).2 * (fuseSize (a + b) c).1)
          * (fuseSize (a + b + c) d).1) := by
  decide

/-- The layer-swap index involution at the pentagon frame. -/
private def swapIdx35 (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2 :=
  swapIdxGen (fuseSize a b) (fuseSize c d) (fuseSize (a + b) (c + d))
    (fuseSize (a + b) c) (fuseSize (a + b + c) d) (fuseSize b (c + d))
    (fuseSize a (b + (c + d))) (swapCast_cl a b c d)
    (swapCast_35 a b c d) (swapCast_out a b c d) i

/-- The Koszul sign exponent at the pentagon frame. -/
private def swapParity35 (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) : ZMod 2 :=
  swapParityGen (fuseSize a b) (fuseSize c d)
    (fuseSize (a + b) (c + d)) (fuseSize (a + b) c)
    (fuseSize (a + b + c) d) (swapCast_cl a b c d) i

/-- The swap certificates at the pentagon frame. -/
private theorem swapIdx35_certs (a b c d : ZMod 8) :
    ∀ i, swapIdx35 a b c d (swapIdx35 a b c d i) = i
      ∧ swapParity35 a b c d (swapIdx35 a b c d i)
        = swapParity35 a b c d i
      ∧ sumParity (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2
          (swapIdx35 a b c d i)
        = sumParity (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2 i :=
  swapIdxGen_certs (fuseSize a b) (fuseSize c d)
    (fuseSize (a + b) (c + d)) (fuseSize (a + b) c)
    (fuseSize (a + b + c) d) (fuseSize b (c + d))
    (fuseSize a (b + (c + d)))
    (fuseSize_cases a b) (fuseSize_cases c d)
    (fuseSize_cases (a + b) (c + d)) (fuseSize_cases (a + b) c)
    (fuseSize_cases (a + b + c) d) (fuseSize_cases b (c + d))
    (fuseSize_cases a (b + (c + d)))
    (swapCast_cl a b c d) (swapCast_35 a b c d) (swapCast_out a b c d)

private theorem zmod2_zero_add_add_self : ∀ x : ZMod 2,
    (0 : ZMod 2) + x + x = 0 := by decide

/-- The signed swap unit, at the raw matrix type. -/
private noncomputable def swapSignM (a b c d : ZMod 8) :
    Matrix
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (stdTower (K := K) (a + b + c + d)).carrier :=
  Matrix.of fun i j =>
    if j = swapIdx35 a b c d i
    then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
      (1 : (stdTower (K := K) (a + b + c + d)).carrier)
    else 0

omit [Invertible (2 : K)] in
private theorem swapSignM_mul_self (a b c d : ZMod 8) :
    swapSignM (K := K) a b c d * swapSignM a b c d = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (swapIdx35 a b c d i)
    (fun k _ hk => by
      show (if k = swapIdx35 a b c d i
          then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
            (1 : (stdTower (K := K) (a + b + c + d)).carrier)
          else 0) * swapSignM a b c d k j = 0
      rw [if_neg hk, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  show (if swapIdx35 a b c d i = swapIdx35 a b c d i
      then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
        (1 : (stdTower (K := K) (a + b + c + d)).carrier)
      else 0)
    * (if j = swapIdx35 a b c d (swapIdx35 a b c d i)
      then ((sgn (swapParity35 a b c d
          (swapIdx35 a b c d i)) : ℤˣ) : ℤ) •
        (1 : (stdTower (K := K) (a + b + c + d)).carrier)
      else 0)
    = (1 : Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier) i j
  rw [if_pos rfl, (swapIdx35_certs a b c d i).1,
    (swapIdx35_certs a b c d i).2.1]
  by_cases hij : j = i
  · subst hij
    rw [if_pos rfl, Matrix.one_apply_eq, smul_mul_smul_comm, one_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  · rw [if_neg hij, mul_zero, Matrix.one_apply_ne (Ne.symm hij)]

/-- **The signed swap unit** `W` at the pentagon frame: the signed
permutation matrix with `W i (φ i) = (−1)^{π_σ(I)π_γ(K)}` through
the flat-index decoding, all other entries `0`.  This is the honest
correction of the failed F3′: `(cluster35Tail3 ∘ cluster35Prefix)(w)
= W · quadRoute3(w) · W`.  On the fifteen realizable size patterns
where at most one cluster wraps it is the plain Koszul diagonal
`D_ε`; when both clusters wrap it also carries the sorting
permutation of the two shared-tail regroupings. -/
noncomputable def swapSign (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  swapSignM a b c d

omit [Invertible (2 : K)] in
/-- The swap unit is even. -/
theorem swapSign_mem_even (a b c d : ZMod 8) :
    swapSign (K := K) a b c d
      ∈ ((stdTower (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading 0 := by
  intro i j
  show (if j = swapIdx35 a b c d i
      then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
        (1 : (stdTower (K := K) (a + b + c + d)).carrier)
      else 0)
    ∈ (stdTower (a + b + c + d)).grading
      (0 + sumParity (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2 i
      + sumParity (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2 j)
  by_cases hj : j = swapIdx35 a b c d i
  · rw [if_pos hj, hj, (swapIdx35_certs a b c d i).2.2,
      zmod2_zero_add_add_self]
    exact zsmul_mem (SetLike.one_mem_graded _) _
  · rw [if_neg hj]
    exact zero_mem _

omit [Invertible (2 : K)] in
/-- The swap unit squares to `1`. -/
theorem swapSign_mul_self (a b c d : ZMod 8) :
    swapSign (K := K) a b c d * swapSign a b c d = 1 :=
  swapSignM_mul_self a b c d

omit [Invertible (2 : K)] in
/-- The swap unit is a unit. -/
theorem swapSign_isUnit (a b c d : ZMod 8) :
    IsUnit (swapSign (K := K) a b c d) :=
  ⟨⟨swapSign a b c d, swapSign a b c d, swapSign_mul_self a b c d,
    swapSign_mul_self a b c d⟩, rfl⟩

/-- The amplified route intertwiner of the cluster triple
`(a, b, c+d)`, pushed through the shared `(cd)`-cluster tail. -/
private noncomputable def edge35Core (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  (cluster35SharedTail a b c d).toAlgEquiv
    (sdiagAmp (sumParity (fuseSize c d).1 (fuseSize c d).2)
      (pentagonParity (K := K) a b (c + d))
      (pentagonT a b (c + d)))

/-- **The (a,b,cd)-cluster edge intertwiner** of the pentagon: the
triple intertwiner of `(a, b, c+d)`, amplified to the `γ`-matrix
layer by the signed diagonal, pushed through the shared cluster
tail, and corrected by the signed swap unit. -/
noncomputable def edgeT35 (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  edge35Core a b c d * swapSign a b c d

theorem edgeT35_mem (a b c d : ZMod 8) :
    edgeT35 (K := K) a b c d
      ∈ ((stdTower (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) a b (c + d)) := by
  have h₀ : edge35Core (K := K) a b c d
      ∈ ((stdTower (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) a b (c + d)) := by
    rw [edge35Core, ← (cluster35SharedTail a b c d).map_grading]
    exact Submodule.mem_map_of_mem
      (sdiagAmp_mem _ _ (pentagonT_mem a b (c + d)))
  have h := SetLike.mul_mem_graded h₀ (swapSign_mem_even a b c d)
  rwa [add_zero] at h

theorem edgeT35_isUnit (a b c d : ZMod 8) :
    IsUnit (edgeT35 (K := K) a b c d) := by
  refine IsUnit.mul ?_ (swapSign_isUnit a b c d)
  rw [edge35Core]
  exact IsUnit.map _
    (sdiagAmp_isUnit _ (pentagonT_isUnit a b (c + d)))

/-- **The pre-swap half of the e35 edge relation**: the amplified
intertwiner relates `alignedRoute5` to the `(cd)`-cluster spelling
`cluster35Tail3 ∘ cluster35Prefix` of vertex 3, by the standard
transport chain (both factored routes pass through the same shared
tail by construction).  Combined with the corrected signed
factorization `(cluster35Tail3 ∘ cluster35Prefix)(w) = swapSign ·
quadRoute3(w) · swapSign` (next round), this yields the full
`edgeT35`-intertwining of `(alignedRoute5, quadRoute3)`. -/
theorem edge35Core_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (alignedRoute5 a b c d).toAlgEquiv w * edge35Core a b c d
        = ((sgn (j * pentagonParity (K := K) a b (c + d)) : ℤˣ) : ℤ) •
          (edge35Core a b c d
            * (cluster35Tail3 a b c d).toAlgEquiv
              ((cluster35Prefix a b c d).toAlgEquiv w)) := by
  intro j w hw
  -- step 1: the signed-diagonal transport of the triple intertwiner
  -- to the γ-matrix layer
  have h1 := intertwines_mapMatrix
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower (c + d))).grading)
    (sumParity (fuseSize c d).1 (fuseSize c d).2)
    (routeL a b (c + d)).toAlgEquiv.toAlgHom
    (routeR a b (c + d)).toAlgEquiv.toAlgHom
    (pentagonT_intertwines a b (c + d))
  -- step 2: push along the shared tail
  have h2 := intertwines_map
    ((((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower (c + d))).matrixSuper (fuseSize c d).1
      (fuseSize c d).2)).grading)
    (routeL a b (c + d)).toAlgEquiv.toAlgHom.mapMatrix
    (routeR a b (c + d)).toAlgEquiv.toAlgHom.mapMatrix
    (cluster35SharedTail a b c d).toAlgEquiv.toAlgHom
    h1
  -- step 3: precompose with the matrix-frame change and the cluster
  -- prefix
  have h3 := intertwines_precomp
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).grading)
    ((((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower (c + d))).matrixSuper (fuseSize c d).1
      (fuseSize c d).2)).grading)
    (((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).grading)
    ((cluster35SharedTail a b c d).toAlgEquiv.toAlgHom.comp
      (routeL a b (c + d)).toAlgEquiv.toAlgHom.mapMatrix)
    ((cluster35SharedTail a b c d).toAlgEquiv.toAlgHom.comp
      (routeR a b (c + d)).toAlgEquiv.toAlgHom.mapMatrix)
    (cluster35Frame a b c d).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _
      (cluster35Frame a b c d).map_grading)
    h2
  have h4 := intertwines_precomp
    (((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).grading)
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).grading)
    (((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).grading)
    (((cluster35SharedTail a b c d).toAlgEquiv.toAlgHom.comp
        (routeL a b (c + d)).toAlgEquiv.toAlgHom.mapMatrix).comp
      (cluster35Frame a b c d).toAlgEquiv.toAlgHom)
    (((cluster35SharedTail a b c d).toAlgEquiv.toAlgHom.comp
        (routeR a b (c + d)).toAlgEquiv.toAlgHom.mapMatrix).comp
      (cluster35Frame a b c d).toAlgEquiv.toAlgHom)
    (cluster35Prefix a b c d).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _
      (cluster35Prefix a b c d).map_grading)
    h3
  -- step 4: identify the composites with the factored vertex routes
  rw [show (alignedRoute5 a b c d).toAlgEquiv w
      = (cluster35SharedTail a b c d).toAlgEquiv
          (((routeR a b (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv
            ((cluster35Frame a b c d).toAlgEquiv
              ((cluster35Prefix a b c d).toAlgEquiv w))) from
      alignedRoute5_factor a b c d w,
    show (cluster35Tail3 a b c d).toAlgEquiv
        ((cluster35Prefix a b c d).toAlgEquiv w)
      = (cluster35SharedTail a b c d).toAlgEquiv
          (((routeL a b (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv
            ((cluster35Frame a b c d).toAlgEquiv
              ((cluster35Prefix a b c d).toAlgEquiv w))) from rfl]
  exact h4 hw

end Edge35

end Superfusion

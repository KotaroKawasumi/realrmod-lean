/-
Superfusion / Gauge / SizeRigidity

Milestone M9-1c of the intrinsic gauge track: **size rigidity of matrix
superalgebras over super division coefficients** — the intrinsic
replacement for the concrete wrap-count decides.

For `(D, 𝒟)` a `ZMod 2`-graded `K`-algebra (bundled as `P : SuperAlgebra K`,
`P.carrier = D`, `P.grading = 𝒟`) and a graded isomorphism
`e : SuperAlgEquiv (P.matrixSuper p q) (P.matrixSuper p' q')` of matrix
stabilizations (`SuperAlgebra.matrixSuper`, `Superfusion.Super.BWPeriodicity`):

* **total rigidity** (`sizeRigidity_total`): `p + q = p' + q'`, for *any*
  nontrivial finite-dimensional `D` — pure `finrank` arithmetic (`Module.
  finrank_matrix`), no module theory, no super-division hypothesis needed;
* **pair rigidity up to swap, purely even case** (`sizeRigidity_even`):
  if `𝒟 1 = ⊥` then `(p = p' ∧ q = q') ∨ (p = q' ∧ q = p')` — again pure
  counting, via the **checkerboard-with-coefficient finrank formula**
  (`finrank_matrixGradingA_sumParity`, the general computation of the
  `K`-dimension of each graded piece of `M_{p|q}(D)` in terms of the graded
  pieces of `D`) specialized to the purely-even case, plus an elementary
  ℕ-arithmetic Vieta argument (`nat_pair_rigidity`: a sum and a product
  pin down an unordered pair of naturals).

Route for the pair-rigidity case (§ design guidance): the naive plan of
computing the checkerboard grading via a graded-module-over-`D` argument
(homogeneous bases, `Superfusion.Gauge.SuperDivisionModule`) is bypassed
entirely — the even/odd `K`-dimensions of `M_{p|q}(D)` are computed
*directly* from the matrix grading's definition (`matrixGradingA`,
`Superfusion.Super.MatrixSuperCoeff`) via an explicit entrywise
`LinearEquiv` to a Pi-type of graded pieces of `D`
(`matrixGradingA_equivPi`), with **no super-division hypothesis on `D`
at all** and no reference to `IsSuperDivision`; `finrank K D ≠ 0` only
needs `D` nontrivial and finite-dimensional (`Bimod.finrank_D_pos`,
already proved in the `SuperDivisionModule` round for exactly this
reason, reused verbatim). The odd-unit case is not addressed here beyond
what `sizeRigidity_total` already gives (`p + q = p' + q'` is sharp: an
odd unit collapses `M_{p|q}(D) ≅ M_{p+q|0}(D)`, so no finer pair
invariant survives) — the collapse isomorphism itself
(`matrixSuper_oddUnit_collapse`, conjugation by the diagonal matrix with
`u` in the odd rows) is **deferred to M9-2**: it is a genuine
construction (an explicit graded algebra equivalence, not a counting
argument) needed for σ-normalization there, not for this round's size
rigidity.

Design record: docs/super-track-design.md (M9 sections).
-/
import Superfusion.Gauge.SuperDivisionModule
import Superfusion.Super.MatrixSuperCoeff
import Superfusion.Super.BWPeriodicity
import Superfusion.Super.GradedEndMatrix

namespace Superfusion

open Module

/-! ### The checkerboard-with-coefficient finrank formula -/

section MatrixGradingFinrank

variable {K : Type*} [Field K]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {D : Type*} [Ring D] [Algebra K D] [FiniteDimensional K D]
variable (π : n → ZMod 2) (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]

/-- The entrywise identification of the degree-`i` slice of a matrix superalgebra with
coefficient grading `𝒟` and a Pi-type collecting the graded pieces of `D` at each index pair:
`M ↦ (a, b) ↦ M a b`. The membership condition `mem_matrixGradingA` is definitional, so this is
literally the identity function under the hood, packaged as a `K`-linear map. -/
noncomputable def matrixGradingA_toPi (i : ZMod 2) :
    (matrixGradingA π 𝒟 i) →ₗ[K] (Π p : n × n, (𝒟 (i + π p.1 + π p.2))) where
  toFun M p := ⟨(M : Matrix n n D) p.1 p.2, M.2 p.1 p.2⟩
  map_add' M N := by funext p; apply Subtype.ext; simp [Matrix.add_apply]
  map_smul' c M := by funext p; apply Subtype.ext; simp [Matrix.smul_apply]

omit [Fintype n] [DecidableEq n] [FiniteDimensional K D] [GradedAlgebra 𝒟] in
theorem matrixGradingA_toPi_bijective (i : ZMod 2) :
    Function.Bijective (matrixGradingA_toPi π 𝒟 i) := by
  constructor
  · intro M N h
    apply Subtype.ext
    ext a b
    exact congrArg Subtype.val (congrFun h (a, b))
  · intro f
    refine ⟨⟨Matrix.of (fun a b => (f (a, b) : D)), fun a b => (f (a, b)).2⟩, ?_⟩
    funext p
    apply Subtype.ext
    rfl

/-- The degree-`i` slice of a matrix superalgebra with coefficient grading `𝒟`, as a `K`-linear
equivalence with the Pi-type collecting the graded pieces of `D` at each index pair. -/
noncomputable def matrixGradingA_equivPi (i : ZMod 2) :
    (matrixGradingA π 𝒟 i) ≃ₗ[K] (Π p : n × n, (𝒟 (i + π p.1 + π p.2))) :=
  LinearEquiv.ofBijective (matrixGradingA_toPi π 𝒟 i) (matrixGradingA_toPi_bijective π 𝒟 i)

omit [DecidableEq n] [GradedAlgebra 𝒟] in
/-- The `K`-dimension of the degree-`i` slice of a matrix superalgebra with coefficient
grading `𝒟`, as a double sum over index pairs of the `K`-dimensions of the corresponding
graded pieces of `D`. -/
theorem finrank_matrixGradingA (i : ZMod 2) :
    finrank K (matrixGradingA π 𝒟 i) = ∑ a : n, ∑ b : n, finrank K (𝒟 (i + π a + π b)) := by
  rw [(matrixGradingA_equivPi π 𝒟 i).finrank_eq, Module.finrank_pi_fintype,
    Fintype.sum_prod_type]

end MatrixGradingFinrank

section SumParitySpecialize

private theorem zmod2_add_one_add_one : ∀ i : ZMod 2, i + 1 + 1 = i := by decide

/-- The purely arithmetic (`Nat`-valued, no dependent types involved) content of the
`sumParity`-checkerboard count: split the double sum over `Fin p ⊕ Fin q` into its four
blocks and collect terms, using `i + 1 + 1 = i` in `ZMod 2` to identify the two "matching
parity" blocks (contributing `g i`) and the two "opposite parity" blocks (contributing
`g (i + 1)`). Stated for a generic `g : ZMod 2 → ℕ` (rather than inlining `finrank K (𝒟 ·)`
directly) to keep the `Finset.sum` simplification purely arithmetic: `simp` rewriting the
*index* `i + sumParity p q a + sumParity p q b` inside a dependent type such as `↥(𝒟 (…))`
would also need to transport the buried `AddCommMonoid` instance argument, which it does not
do automatically. -/
theorem sumParity_double_sum (p q : ℕ) (i : ZMod 2) (g : ZMod 2 → ℕ) :
    (∑ a : Fin p ⊕ Fin q, ∑ b : Fin p ⊕ Fin q, g (i + sumParity p q a + sumParity p q b))
      = (p ^ 2 + q ^ 2) * g i + 2 * p * q * g (i + 1) := by
  simp only [Fintype.sum_sum_type, sumParity, Sum.elim_inl, Sum.elim_inr, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    zmod2_add_one_add_one]
  ring

variable {K : Type*} [Field K]
variable {D : Type*} [Ring D] [Algebra K D] [FiniteDimensional K D]
variable (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]

omit [GradedAlgebra 𝒟] in
/-- **The checkerboard-with-coefficient finrank formula** (M9-1c, item 4 of the design
guidance): for `M_{p|q}(D)`, the `K`-dimension of the degree-`i` part is
`(p²+q²)·finrank K (𝒟 i) + 2pq·finrank K (𝒟 (i+1))` — entries `(a,b)` of matching checkerboard
parity contribute the degree-`i` piece of `D`, entries of opposite parity contribute the
degree-`(i+1)` piece. -/
theorem finrank_matrixGradingA_sumParity (p q : ℕ) (i : ZMod 2) :
    finrank K (matrixGradingA (sumParity p q) 𝒟 i)
      = (p ^ 2 + q ^ 2) * finrank K (𝒟 i) + 2 * p * q * finrank K (𝒟 (i + 1)) := by
  rw [finrank_matrixGradingA]
  exact sumParity_double_sum p q i (fun j => finrank K (𝒟 j))

end SumParitySpecialize

/-! ### The two size-rigidity theorems -/

section SizeRigidity

variable {K : Type*} [Field K]

/-- The `K`-dimension of `M_{p|q}(D)` is `(p+q)² · finrank K D` (`Module.finrank_matrix`,
specialized along `Fintype.card (Fin p ⊕ Fin q) = p + q`). -/
theorem finrank_matrixSuper (P : SuperAlgebra K) (p q : ℕ) :
    finrank K (P.matrixSuper p q).carrier = (p + q) * (p + q) * finrank K P.carrier := by
  show finrank K (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) = _
  rw [Module.finrank_matrix, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-- `finrank_matrixGradingA_sumParity`, bundled at the level of `SuperAlgebra.matrixSuper`. -/
theorem finrank_matrixSuper_grading (P : SuperAlgebra K) [FiniteDimensional K P.carrier]
    (p q : ℕ) (i : ZMod 2) :
    finrank K ((P.matrixSuper p q).grading i)
      = (p ^ 2 + q ^ 2) * finrank K (P.grading i) + 2 * p * q * finrank K (P.grading (i + 1)) :=
  finrank_matrixGradingA_sumParity P.grading p q i

/-- **Total rigidity** (M9-1c, deliverable 1): a graded isomorphism `M_{p|q}(D) ≅ M_{p'|q'}(D)`
forces `p + q = p' + q'`, for *any* nontrivial finite-dimensional `D` — no super-division
hypothesis needed. Route: `finrank K` of the carrier is `(p+q)² · finrank K D` on either side
(`finrank_matrixSuper`); the equivalence identifies the two carriers, so the two squares agree;
cancel the common nonzero factor `finrank K D` (`Bimod.finrank_D_pos`) and take square roots in
`ℕ` (`mul_self_inj`). -/
theorem sizeRigidity_total {P : SuperAlgebra K} [Nontrivial P.carrier]
    [FiniteDimensional K P.carrier] {p q p' q' : ℕ}
    (e : SuperAlgEquiv (P.matrixSuper p q) (P.matrixSuper p' q')) :
    p + q = p' + q' := by
  have heq : finrank K (P.matrixSuper p q).carrier = finrank K (P.matrixSuper p' q').carrier :=
    e.toAlgEquiv.toLinearEquiv.finrank_eq
  rw [finrank_matrixSuper, finrank_matrixSuper] at heq
  have hd : 0 < finrank K P.carrier := Bimod.finrank_D_pos
  have h2 : (p + q) * (p + q) = (p' + q') * (p' + q') := Nat.eq_of_mul_eq_mul_right hd heq
  exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp h2

/-- **Vieta's uniqueness for a pair of naturals**: a sum and a product pin down an unordered
pair. Proved over `ℤ` (an integral domain), where `(p - p') * (p - q') = 0` is an exact
algebraic identity given `p + q = p' + q'` and `p * q = p' * q'` (`linear_combination`); the
zero-product property then forces `p = p'` or `p = q'`, and the sum equation gives the matching
second component in either case. -/
private theorem nat_pair_rigidity {p q p' q' : ℕ} (hs : p + q = p' + q') (ht : p * q = p' * q') :
    (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  have hs' : (p : ℤ) + q = p' + q' := by exact_mod_cast hs
  have ht' : (p : ℤ) * q = p' * q' := by exact_mod_cast ht
  have key : ((p : ℤ) - p') * ((p : ℤ) - q') = 0 := by linear_combination p * hs' - ht'
  rcases mul_eq_zero.mp key with h | h
  · have hpn : p = p' := by exact_mod_cast (by linarith : (p : ℤ) = p')
    exact Or.inl ⟨hpn, by omega⟩
  · have hpn : p = q' := by exact_mod_cast (by linarith : (p : ℤ) = q')
    exact Or.inr ⟨hpn, by omega⟩

/-- **Pair rigidity up to swap, purely even case** (M9-1c, deliverable 2): for a *purely even*
`D` (`𝒟 1 = ⊥`), a graded isomorphism `M_{p|q}(D) ≅ M_{p'|q'}(D)` forces the unordered pair
`{p, q}` to equal `{p', q'}`. Route: `sizeRigidity_total` gives the sum `p + q = p' + q'`; the
degree-`1` (odd) part of `M_{p|q}(D)` has `K`-dimension `2pq · finrank K D` (purely even `D`
kills the `(p²+q²) · finrank K (𝒟 1)` term of `finrank_matrixSuper_grading` and collapses
`finrank K (𝒟 0)` to `finrank K D`, via `isCompl_grades`), so the equivalence's degree-`1`
part (`SuperAlgEquiv.map_grading`, transported along the graded isomorphism by
`LinearEquiv.finrank_map_eq`) gives the product `p * q = p' * q'`; a sum and a product pin down
an unordered pair (`nat_pair_rigidity`). The odd-unit case is not addressed here: total
rigidity is already sharp there (`M_{p|q}(D) ≅ M_{p+q|0}(D)` via the odd-unit collapse,
deferred to M9-2), so no finer pair invariant exists to prove. -/
theorem sizeRigidity_even {P : SuperAlgebra K} [Nontrivial P.carrier]
    [FiniteDimensional K P.carrier] (h1 : P.grading 1 = ⊥) {p q p' q' : ℕ}
    (e : SuperAlgEquiv (P.matrixSuper p q) (P.matrixSuper p' q')) :
    (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  have hs : p + q = p' + q' := sizeRigidity_total e
  have h0top : P.grading 0 = ⊤ := by
    have hc := (isCompl_grades P.grading).codisjoint
    rwa [codisjoint_iff, h1, sup_bot_eq] at hc
  have hd0 : finrank K (P.grading 0) = finrank K P.carrier := by rw [h0top]; exact finrank_top K P.carrier
  have hd1 : finrank K (P.grading 1) = 0 := by rw [h1]; exact finrank_bot K P.carrier
  have hg1 : finrank K ((P.matrixSuper p q).grading 1)
      = finrank K ((P.matrixSuper p' q').grading 1) := by
    rw [← e.map_grading 1]
    exact (LinearEquiv.finrank_map_eq e.toAlgEquiv.toLinearEquiv _).symm
  rw [finrank_matrixSuper_grading, finrank_matrixSuper_grading,
    show (1 : ZMod 2) + 1 = 0 from by decide, hd0, hd1] at hg1
  simp only [mul_zero, zero_add] at hg1
  have ht : p * q = p' * q' := by
    have h2 : 2 * (p * q) * finrank K P.carrier = 2 * (p' * q') * finrank K P.carrier := by
      linarith [hg1]
    have hd : 0 < finrank K P.carrier := Bimod.finrank_D_pos
    have h3 : 2 * (p * q) = 2 * (p' * q') := Nat.eq_of_mul_eq_mul_right hd h2
    omega
  exact nat_pair_rigidity hs ht

end SizeRigidity

end Superfusion

/-
Superfusion / Gauge / SuperDivisionModule

Milestone M9-1b of the intrinsic gauge track: **graded module theory over a
super division algebra** — homogeneous bases and the type-split multiplicity
invariants, the shared core feeding both the gauge classification and the
future mini-Wedderburn theorem.

Setting: `(D, 𝒟)` a `ZMod 2`-graded `K`-algebra with `hdiv : IsSuperDivision
𝒟` (reused verbatim from `Superfusion.Bimod.ColumnSimple`), and `M` a
**left** `D`-module (`Module D M`, `IsScalarTower K D M`) carrying a
compatible `ZMod 2`-grading `ℳ : ZMod 2 → Submodule K M` in the sense of
mathlib's `SetLike.GradedSMul 𝒟 ℳ` (`𝒟 i • ℳ j ⊆ ℳ (i+j)`) — the same
left-action convention already used throughout `Superfusion.Bimod` for the
left leg of a super bimodule (`Bimod/Basic.lean`'s `Envelope` section, e.g.
`variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul ℬ ℳ]`).  The core
exchange argument is written once for left modules, where it directly uses
mathlib's ordinary `Basis` API.  The final section applies it to a native
right `D`-module by regarding that module as a left module over the ordinary
opposite `Dᵐᵒᵖ`, equipped with `opGrading 𝒟`.  This is an unsigned
`MulOpposite` bridge, not the Koszul-twisted `SuperOp`.

Since a super division algebra need NOT be a division ring (a mixed-parity
element such as `1 + u` for an odd unit `u` with `u ^ 2 = 1` can be a zero
divisor, `(1 + u) * (1 - u) = 0`), mathlib's `Basis.ofVectorSpace` does not
apply directly; instead we redo the classical Steinitz exchange argument by
hand, restricted throughout to **homogeneous** vectors and **homogeneous**
coefficients (`HomogeneousIndependent`) — the graded pieces `𝒟 i` of a
nonzero coefficient are separately invertible by `hdiv`, which is exactly
enough to run the exchange step (`homogeneousIndependent_snoc`).  Finite
induction on the `K`-dimension of the current `D`-span (not Zorn: `M` is
finite-dimensional over `K`, so the process terminates) then produces a
homogeneous `D`-basis indexed by some `Fin r` (`exists_homogeneous_basis`),
packaged as an ordinary mathlib `Basis (Fin r) D M` together with the parity
function — the shape best suited to matrix-size rigidity downstream (M9-1c),
mirroring `Super/GradedEndMatrix.lean`'s `homBasis`.

The multiplicity invariants (§4, "type dichotomy") are stated in the
**finrank-quotient** shape recommended by the design record: rather than
developing `D`-rank theory (which would fail outright in the mixed
non-division case) we compare `K`-dimensions only, by exhibiting an explicit
`K`-linear equivalence `M ≃ₗ[K] (Fin r → D)` (`Basis.equivFun` restricted
along the scalar tower) and reading off `finrank K (Fin r → D) = r *
finrank K D` (`Module.finrank_pi_fintype`).  This needs no invariant-basis-
number assumption on `D` at all: the *size* of a homogeneous basis is
recovered as a quotient of manifestly basis-independent `K`-dimensions, so
its invariance is immediate:

* unconditionally (`finrank_eq_card_mul_finrank`), `finrank K M = r *
  finrank K D` for any `D`-basis of size `r` — the odd-unit-case total
  invariant `finrank K M = (m + n) * finrank K D` (via `r = m + n`,
  `Fintype.card_subtype_...`);
* in the purely even case `𝒟 1 = ⊥` (so `D = 𝒟 0`, hence `ℳ 0` and `ℳ 1`
  are themselves `D`-submodules of `M`, `gradeSubmoduleD`), the same
  argument applied to the even/odd sub-bases separately gives
  `finrank K (ℳ 0) = m * finrank K D` and `finrank K (ℳ 1) = n *
  finrank K D` — the finer pair invariant.

Design record: docs/super-track-design.md (M9 sections).
-/
import Superfusion.Gauge.SuperDivisionBasic
import Superfusion.Bimod.GradedModule
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Superfusion

namespace Bimod

open Module

/-! ### Setup and Deliverables 1-3: homogeneous generation, independence,
existence of a homogeneous basis -/

section HomBasis

variable {K : Type*} [Field K]
variable {D : Type*} [Ring D] [Algebra K D] (𝒟 : ZMod 2 → Submodule K D)
  [GradedAlgebra 𝒟]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module D M] [IsScalarTower K D M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒟 ℳ]

private theorem modProj_add_modProj_shift (w : ZMod 2) (x : D) :
    modProj 𝒟 w x + modProj 𝒟 (w + 1) x = x := by
  rcases zmod2_cases w with hw | hw <;> subst hw
  · simpa using modProj_zero_add_modProj_one 𝒟 x
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm]
    exact modProj_zero_add_modProj_one 𝒟 x

private theorem zmod2_coord_cancel (w x : ZMod 2) :
    w + x + x = w := by decide +revert

private theorem zmod2_coord_cancel' (w x : ZMod 2) :
    w + x + 1 + x = w + 1 := by decide +revert

private theorem zmod2_coord_ne (w : ZMod 2) :
    w + 1 ≠ w := by decide +revert

omit [IsScalarTower K D M] in
/-- The coordinates of a homogeneous vector in a homogeneous basis have
the forced degrees: if `m` has degree `w` and `b j` has degree `p j`,
then the `j`-th coordinate of `m` has degree `w + p j`. -/
theorem basis_repr_mem_grading
    {ι : Type*} [Fintype ι] {p : ι → ZMod 2}
    (b : Basis ι D M) (hb : ∀ k, b k ∈ ℳ (p k))
    {w : ZMod 2} {m : M} (hm : m ∈ ℳ w) (j : ι) :
    b.repr m j ∈ 𝒟 (w + p j) := by
  classical
  let c : ι → D := fun k => b.repr m k
  let e0 : ι → D := fun k => modProj 𝒟 (w + p k) (c k)
  let e1 : ι → D := fun k => modProj 𝒟 (w + p k + 1) (c k)
  have hsplit : ∀ k, e0 k + e1 k = c k :=
    fun k => modProj_add_modProj_shift 𝒟 (w + p k) (c k)
  have hmem0 : ∀ k, e0 k • b k ∈ ℳ w := by
    intro k
    have h := SetLike.GradedSMul.smul_mem
      (A := 𝒟) (B := ℳ)
      (modProj_mem 𝒟 (w + p k) (c k)) (hb k)
    rwa [vadd_eq_add, zmod2_coord_cancel] at h
  have hmem1 : ∀ k, e1 k • b k ∈ ℳ (w + 1) := by
    intro k
    have h := SetLike.GradedSMul.smul_mem
      (A := 𝒟) (B := ℳ)
      (modProj_mem 𝒟 (w + p k + 1) (c k)) (hb k)
    rwa [vadd_eq_add, zmod2_coord_cancel'] at h
  have heq :
      m = (∑ k, e0 k • b k) + (∑ k, e1 k • b k) := by
    have hm' : m = ∑ k, c k • b k :=
      (Basis.sum_repr b m).symm
    rw [hm', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← hsplit k, add_smul]
  have hsum0 : (∑ k, e0 k • b k) ∈ ℳ w :=
    sum_mem fun k _ => hmem0 k
  have hsum1 : (∑ k, e1 k • b k) ∈ ℳ (w + 1) :=
    sum_mem fun k _ => hmem1 k
  have hsum1' : (∑ k, e1 k • b k) ∈ ℳ w := by
    have heq2 :
        (∑ k, e1 k • b k) =
          m - (∑ k, e0 k • b k) := by
      rw [heq]
      abel
    rw [heq2]
    exact (ℳ w).sub_mem hm hsum0
  have he1zero : (∑ k, e1 k • b k) = (0 : M) := by
    have h0 :
        modProj ℳ w (∑ k, e1 k • b k) =
          (∑ k, e1 k • b k) :=
      modProj_of_mem ℳ hsum1'
    have h1 :
        modProj ℳ w (∑ k, e1 k • b k) = 0 :=
      modProj_of_mem_ne ℳ hsum1 (zmod2_coord_ne w)
    rw [← h0, h1]
  have hzero_all : ∀ k, e1 k = 0 :=
    Fintype.linearIndependent_iff.mp
      b.linearIndependent e1 he1zero
  have hj : c j = e0 j := by
    have hs := hsplit j
    rw [hzero_all j, add_zero] at hs
    exact hs.symm
  show c j ∈ 𝒟 (w + p j)
  rw [hj]
  exact modProj_mem 𝒟 (w + p j) (c j)

/-! #### Deliverable 1: homogeneous generation -/

omit [Algebra K D] [IsScalarTower K D M] in
/-- **A graded `D`-module is generated over `D` by its homogeneous
elements** (easy half): every `m` splits as `modProj ℳ 0 m + modProj ℳ 1 m`,
both homogeneous. -/
theorem span_homogeneous_eq_top :
    Submodule.span D {m : M | ∃ i, m ∈ ℳ i} = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun m => ?_
  rw [← modProj_zero_add_modProj_one ℳ m]
  exact Submodule.add_mem _
    (Submodule.subset_span ⟨0, modProj_mem ℳ 0 m⟩)
    (Submodule.subset_span ⟨1, modProj_mem ℳ 1 m⟩)

omit [Algebra K D] [IsScalarTower K D M] in
/-- A proper `D`-submodule always misses some homogeneous vector: otherwise
it would contain the (homogeneous) spanning set of `span_homogeneous_eq_top`,
forcing it to be everything. -/
theorem exists_homogeneous_not_mem {p : Submodule D M} (hp : p ≠ ⊤) :
    ∃ (i : ZMod 2) (w : M), w ∈ ℳ i ∧ w ∉ p := by
  by_contra h
  push Not at h
  refine hp (top_le_iff.mp ?_)
  rw [← span_homogeneous_eq_top ℳ]
  refine Submodule.span_le.mpr ?_
  rintro m ⟨i, hm⟩
  exact h i m hm

/-! #### Deliverable 2: homogeneous independence and the graded exchange
step -/

/-- **Homogeneous linear independence** over `D` (matching the left-module
convention of this file): a homogeneous family `v : Fin r → M` of respective
degrees `p : Fin r → ZMod 2` is *homogeneously independent* if every
homogeneous-coefficient relation among the `v i` is trivial — at any target
degree `k`, coefficients `d i` homogeneous of the degree `k + p i` that lands
`d i • v i` in `ℳ k`.  Splitting a general `D`-coefficient into its two
graded parts (`HomogeneousIndependent.linearIndependent`) shows this implies
genuine `LinearIndependent D v`, so this is the right notion to build a
`D`-basis by finite exchange (`homogeneousIndependent_snoc`). -/
def HomogeneousIndependent {r : ℕ} (p : Fin r → ZMod 2) (v : Fin r → M) : Prop :=
  ∀ (k : ZMod 2) (d : Fin r → D), (∀ i, d i ∈ 𝒟 (k + p i)) →
    (∑ i, d i • v i = 0) → ∀ i, d i = 0

/-- A homogeneous coefficient splits into its two graded parts, one landing
each target degree (the module-`D` analogue of `modProj_zero_add_modProj_one`
at a shifted base degree). -/
private theorem modProj_split (i : ZMod 2) (x : D) :
    modProj 𝒟 i x + modProj 𝒟 (i + 1) x = x := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · simpa using modProj_zero_add_modProj_one 𝒟 x
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm]
    exact modProj_zero_add_modProj_one 𝒟 x

private theorem zmod2_double : ∀ i : ZMod 2, i + i = 0 := by decide

omit [IsScalarTower K D M] in
/-- **Homogeneous independence implies genuine `D`-linear independence.**
Split every coefficient `g i` into its two graded parts (landing `ℳ 0` and
`ℳ 1` respectively when multiplied against the homogeneous `v i`), project
the vanishing relation `∑ g i • v i = 0` onto each of the two components of
`M`, and invoke homogeneous independence on each of the resulting two
homogeneous-coefficient relations. -/
theorem HomogeneousIndependent.linearIndependent {r : ℕ} {p : Fin r → ZMod 2}
    {v : Fin r → M} (hmem : ∀ i, v i ∈ ℳ (p i))
    (hv : HomogeneousIndependent 𝒟 p v) : LinearIndependent D v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set e0 : Fin r → D := fun j => modProj 𝒟 (p j) (g j) with he0
  set e1 : Fin r → D := fun j => modProj 𝒟 (p j + 1) (g j) with he1
  have hsplit : ∀ j, e0 j + e1 j = g j := fun j => modProj_split 𝒟 (p j) (g j)
  have hmem0 : ∀ j, e0 j • v j ∈ ℳ 0 := by
    intro j
    have h := SetLike.GradedSMul.smul_mem (A := 𝒟) (B := ℳ)
      (modProj_mem 𝒟 (p j) (g j)) (hmem j)
    rwa [vadd_eq_add, zmod2_double (p j)] at h
  have hmem1 : ∀ j, e1 j • v j ∈ ℳ 1 := by
    intro j
    have h := SetLike.GradedSMul.smul_mem (A := 𝒟) (B := ℳ)
      (modProj_mem 𝒟 (p j + 1) (g j)) (hmem j)
    rwa [vadd_eq_add, show p j + 1 + p j = 1 from by
      rw [add_right_comm, zmod2_double (p j), zero_add]] at h
  have heq : ∑ j, g j • v j = (∑ j, e0 j • v j) + (∑ j, e1 j • v j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [← hsplit j, add_smul]
  have hg0 : ∑ j, e0 j • v j = 0 := by
    have hze : modProj ℳ 0 (∑ j, g j • v j) = 0 := by rw [hg, map_zero]
    rwa [heq, map_add, modProj_of_mem ℳ (sum_mem fun j _ => hmem0 j),
      modProj_of_mem_ne ℳ (sum_mem fun j _ => hmem1 j) (by decide), add_zero] at hze
  have hg1 : ∑ j, e1 j • v j = 0 := by
    have hze : modProj ℳ 1 (∑ j, g j • v j) = 0 := by rw [hg, map_zero]
    rwa [heq, map_add, modProj_of_mem_ne ℳ (sum_mem fun j _ => hmem0 j) (by decide),
      modProj_of_mem ℳ (sum_mem fun j _ => hmem1 j), zero_add] at hze
  have hz0 : e0 i = 0 :=
    hv 0 e0 (fun j => by rw [zero_add]; exact modProj_mem 𝒟 (p j) (g j)) hg0 i
  have hz1 : e1 i = 0 :=
    hv 1 e1 (fun j => by
      rw [add_comm]; exact modProj_mem 𝒟 (p j + 1) (g j)) hg1 i
  rw [← hsplit i, hz0, hz1, add_zero]

omit [GradedAlgebra 𝒟] [IsScalarTower K D M] [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒟 ℳ] in
/-- **The graded exchange step.**  Appending one homogeneous vector `w`
(degree `q`) not in the `D`-span of a homogeneously independent family to
that family (via `Fin.snoc`) keeps it homogeneously independent: split a
would-be relation at the new index into its "old part" and its `w`-
coefficient `c`; if `c = 0` the old part is a homogeneous relation among the
old family, trivial by hypothesis; if `c ≠ 0` it is a homogeneous unit
(`hdiv`), so it can be inverted to solve for `w` as a `D`-combination of the
old family — contradicting `w ∉ span`. -/
theorem homogeneousIndependent_snoc (hdiv : IsSuperDivision 𝒟) {r : ℕ}
    {p : Fin r → ZMod 2} {v : Fin r → M} (_hmem : ∀ i, v i ∈ ℳ (p i))
    (hv : HomogeneousIndependent 𝒟 p v) {q : ZMod 2} {w : M} (_hw : w ∈ ℳ q)
    (hwnot : w ∉ Submodule.span D (Set.range v)) :
    HomogeneousIndependent 𝒟 (Fin.snoc p q) (Fin.snoc v w) := by
  intro k d hd hsum
  have hsum' : (∑ i : Fin r, d i.castSucc • v i) + d (Fin.last r) • w = 0 := by
    rw [Fin.sum_univ_castSucc] at hsum
    simpa [Fin.snoc_castSucc, Fin.snoc_last] using hsum
  by_cases hc0 : d (Fin.last r) = 0
  · have hsum'' : ∑ i : Fin r, d i.castSucc • v i = 0 := by
      rwa [hc0, zero_smul, add_zero] at hsum'
    have hind : ∀ i : Fin r, d i.castSucc = 0 :=
      hv k (fun i => d i.castSucc)
        (fun i => by have h := hd i.castSucc; rwa [Fin.snoc_castSucc] at h) hsum''
    intro i
    exact Fin.lastCases hc0 hind i
  · exfalso
    apply hwnot
    have hcmem : d (Fin.last r) ∈ 𝒟 (k + q) := by
      have h := hd (Fin.last r); rwa [Fin.snoc_last] at h
    obtain ⟨u, hu⟩ := hdiv hcmem hc0
    have hcw : d (Fin.last r) • w = -(∑ i : Fin r, d i.castSucc • v i) :=
      eq_neg_of_add_eq_zero_right hsum'
    have hcw_mem : d (Fin.last r) • w ∈ Submodule.span D (Set.range v) := by
      rw [hcw]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    have hmem' : ((u⁻¹ : Dˣ) : D) • (d (Fin.last r) • w)
        ∈ Submodule.span D (Set.range v) :=
      Submodule.smul_mem _ _ hcw_mem
    rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at hmem'

/-! #### Deliverable 3: existence of a homogeneous basis -/

variable [FiniteDimensional K M]

omit [GradedAlgebra 𝒟] [SetLike.GradedSMul 𝒟 ℳ] in
/-- The induction driving `exists_homogeneous_basis`: extend a homogeneously
independent family to a homogeneous `D`-basis, by finite induction on the
`K`-dimension deficit between the ambient space and the current `D`-span
(no Zorn: `M` is finite-dimensional over `K`, so the deficit is a natural
number and strictly decreases at each exchange step,
`Submodule.finrank_lt_finrank_of_lt`). -/
private theorem exists_extension (hdiv : IsSuperDivision 𝒟) :
    ∀ (n : ℕ) {r : ℕ} (p : Fin r → ZMod 2) (v : Fin r → M),
      (∀ i, v i ∈ ℳ (p i)) → HomogeneousIndependent 𝒟 p v →
      finrank K M ≤
          finrank K ((Submodule.span D (Set.range v)).restrictScalars K) + n →
      ∃ (r' : ℕ) (p' : Fin r' → ZMod 2) (v' : Fin r' → M),
        (∀ i, v' i ∈ ℳ (p' i)) ∧ HomogeneousIndependent 𝒟 p' v' ∧
          Submodule.span D (Set.range v') = ⊤ := by
  intro n
  induction n with
  | zero =>
      intro r p v hmem hind hle
      refine ⟨r, p, v, hmem, hind, ?_⟩
      rw [add_zero] at hle
      have htop : (Submodule.span D (Set.range v)).restrictScalars K = ⊤ :=
        Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hle)
      refine Submodule.eq_top_iff'.mpr fun x => ?_
      have hx : x ∈ (Submodule.span D (Set.range v)).restrictScalars K := by
        rw [htop]; exact Submodule.mem_top
      exact hx
  | succ n ih =>
      intro r p v hmem hind hle
      by_cases htop : Submodule.span D (Set.range v) = ⊤
      · exact ⟨r, p, v, hmem, hind, htop⟩
      · obtain ⟨q, w, hw, hwnot⟩ := exists_homogeneous_not_mem ℳ htop
        set v' : Fin (r + 1) → M := Fin.snoc v w with hv'def
        set p' : Fin (r + 1) → ZMod 2 := Fin.snoc p q with hp'def
        have hmem' : ∀ i, v' i ∈ ℳ (p' i) := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · rw [hv'def, hp'def, Fin.snoc_last, Fin.snoc_last]; exact hw
          · intro j
            rw [hv'def, hp'def, Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hmem j
        have hind' : HomogeneousIndependent 𝒟 p' v' :=
          homogeneousIndependent_snoc 𝒟 ℳ hdiv hmem hind hw hwnot
        have hrange_sub : Set.range v ⊆ Set.range v' := by
          rintro x ⟨i, rfl⟩
          exact ⟨i.castSucc, by rw [hv'def, Fin.snoc_castSucc]⟩
        have hspan_le : Submodule.span D (Set.range v) ≤ Submodule.span D (Set.range v') :=
          Submodule.span_mono hrange_sub
        have hwmem' : w ∈ Submodule.span D (Set.range v') :=
          Submodule.subset_span ⟨Fin.last r, by rw [hv'def, Fin.snoc_last]⟩
        have hlt : Submodule.span D (Set.range v) < Submodule.span D (Set.range v') :=
          lt_of_le_of_ne hspan_le (fun heq => hwnot (heq ▸ hwmem'))
        have hlt' : (Submodule.span D (Set.range v)).restrictScalars K
            < (Submodule.span D (Set.range v')).restrictScalars K := by
          rw [Submodule.restrictScalars_lt]; exact hlt
        have hstrict := Submodule.finrank_lt_finrank_of_lt hlt'
        have hle' : finrank K M ≤
            finrank K ((Submodule.span D (Set.range v')).restrictScalars K) + n := by
          omega
        exact ih p' v' hmem' hind' hle'

/-- **Existence of a homogeneous `D`-basis** (Deliverable 3): a finite-
dimensional (over `K`) graded `D`-module admits a `D`-basis indexed by some
`Fin r`, all of whose vectors are homogeneous (`b i ∈ ℳ (p i)`).  Packaged
as a bundled mathlib `Basis` (rather than, say, a bare existential pairing of
independence and spanning) so downstream matrix-size arguments (M9-1c) can
reuse `Basis.repr`/`Basis.equivFun` directly, mirroring `Super/
GradedEndMatrix.lean`'s `homBasis`. -/
theorem exists_homogeneous_basis (hdiv : IsSuperDivision 𝒟) :
    ∃ (r : ℕ) (p : Fin r → ZMod 2) (b : Basis (Fin r) D M), ∀ i, b i ∈ ℳ (p i) := by
  obtain ⟨r, p, v, hmem, hind, hspan⟩ :=
    exists_extension 𝒟 ℳ hdiv (finrank K M) (Fin.elim0) (Fin.elim0)
      (fun i => i.elim0) (fun _ _ _ _ i => i.elim0) (by simp)
  have hli : LinearIndependent D v :=
    HomogeneousIndependent.linearIndependent (𝒟 := 𝒟) (ℳ := ℳ) hmem hind
  exact ⟨r, p, Basis.mk hli hspan.ge, fun i => by rw [Basis.mk_apply]; exact hmem i⟩

end HomBasis

/-! ### Homogeneous bases for right modules -/

section RightHomBasis

variable {K : Type*} [Field K]
variable {D : Type*} [Ring D] [Algebra K D]
variable (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]
variable {M : Type*} [AddCommGroup M] [Module K M]
  [Module Dᵐᵒᵖ M] [IsScalarTower K Dᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M)
  [DirectSum.Decomposition ℳ] [GradedRightSMul 𝒟 ℳ]
  [FiniteDimensional K M]

/-- Regard a graded right action as the corresponding graded left action of
the ordinary opposite algebra.  This is kept as an explicit bridge rather
than a global instance, so it cannot introduce typeclass search loops. -/
@[implicit_reducible]
def gradedSMul_opGrading :
    SetLike.GradedSMul (opGrading 𝒟) ℳ :=
  { smul_mem := by
      intro i j a m ha hm
      have h :=
        GradedRightSMul.smul_mem
          ((mem_opGrading_iff 𝒟).mp ha) hm
      simpa only [vadd_eq_add, MulOpposite.op_unop] using h }

/-- A finite-dimensional graded right module over a super division algebra
has a finite homogeneous basis.  The right action is regarded as a left
action of the ordinary opposite algebra; no signed super-opposite or matrix
presentation is involved. -/
theorem exists_homogeneous_right_basis
    (hdiv : IsSuperDivision 𝒟) :
    ∃ (r : ℕ) (p : Fin r → ZMod 2)
      (b : Basis (Fin r) Dᵐᵒᵖ M),
      ∀ i, b i ∈ ℳ (p i) := by
  letI : SetLike.GradedSMul (opGrading 𝒟) ℳ :=
    gradedSMul_opGrading 𝒟 ℳ
  exact
    exists_homogeneous_basis (opGrading 𝒟) ℳ
      (isSuperDivision_opGrading 𝒟 hdiv)

omit [IsScalarTower K Dᵐᵒᵖ M] [FiniteDimensional K M] in
/-- Right-module form of coordinate homogeneity.  The coordinate supplied
by an ordinary-opposite basis is unopposed to recover the right coefficient
in the original superalgebra. -/
theorem basis_repr_mem_right_grading
    {ι : Type*} [Fintype ι] {p : ι → ZMod 2}
    (b : Basis ι Dᵐᵒᵖ M) (hb : ∀ k, b k ∈ ℳ (p k))
    {w : ZMod 2} {m : M} (hm : m ∈ ℳ w) (j : ι) :
    MulOpposite.unop (b.repr m j) ∈ 𝒟 (w + p j) := by
  letI : SetLike.GradedSMul (opGrading 𝒟) ℳ :=
    gradedSMul_opGrading 𝒟 ℳ
  exact
    (mem_opGrading_iff 𝒟).mp
      (basis_repr_mem_grading
        (opGrading 𝒟) ℳ b hb hm j)

end RightHomBasis

/-! ### Deliverable 4: multiplicity invariants, split by the type dichotomy -/

section Multiplicity

variable {K : Type*} [Field K]
variable {D : Type*} [Ring D] [Algebra K D] [Nontrivial D] [FiniteDimensional K D]
variable (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module D M] [IsScalarTower K D M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒟 ℳ]

/-- `finrank K D` is positive: `D` is a nontrivial finite-dimensional `K`-algebra, so
`(⊥ : Submodule K D) < ⊤` and `Submodule.finrank_lt_finrank_of_lt` applies. -/
theorem finrank_D_pos : 0 < finrank K D := by
  have hlt : (⊥ : Submodule K D) < ⊤ := by
    refine lt_of_le_of_ne bot_le (fun h => ?_)
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    refine hx ?_
    have hxmem : x ∈ (⊥ : Submodule K D) := h ▸ Submodule.mem_top
    rwa [Submodule.mem_bot] at hxmem
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  rwa [finrank_bot, finrank_top] at hfr

theorem finrank_D_ne_zero : finrank K D ≠ 0 := (finrank_D_pos (K := K) (D := D)).ne'

omit [Nontrivial D] in
/-- **The total-count invariant, unconditionally** (no type-dichotomy hypothesis needed):
the `K`-dimension of `M` is `finrank K D` times the size of ANY `D`-basis, via the explicit
`K`-linear equivalence `M ≃ₗ[K] (Fin r → D)` given by `Basis.equivFun` (restricted along the
scalar tower) and `Module.finrank_pi_fintype`.  In the odd-unit case this is the invariance
of `m + n` (the total count of a homogeneous basis, split by parity), since `r` is pinned
down as a quotient of manifestly basis-independent `K`-dimensions:
`r = finrank K M / finrank K D`. -/
theorem finrank_eq_card_mul_finrank {r : ℕ} (b : Basis (Fin r) D M) :
    finrank K M = r * finrank K D := by
  have e : M ≃ₗ[K] (Fin r → D) := (Basis.equivFun b).restrictScalars K
  rw [e.finrank_eq, Module.finrank_pi_fintype (R := K) (M := fun _ : Fin r => D)]
  simp

include K in
/-- Two `D`-bases of `M` (of a priori different sizes) have the same size: cancel the
(nonzero, `finrank_D_ne_zero`) common factor `finrank K D` from
`finrank_eq_card_mul_finrank`. -/
theorem card_eq_of_two_bases {r₁ r₂ : ℕ} (b₁ : Basis (Fin r₁) D M) (b₂ : Basis (Fin r₂) D M) :
    r₁ = r₂ :=
  Nat.eq_of_mul_eq_mul_right (finrank_D_pos (K := K) (D := D))
    ((finrank_eq_card_mul_finrank b₁).symm.trans (finrank_eq_card_mul_finrank b₂))

/-! #### The purely even case: the finer pair invariant -/

omit [Nontrivial D] in
/-- The `K`-dimension of a `D`-submodule (given as a `Submodule D M`, restricted to `K`) is
`finrank K D` times the size of any `D`-basis of it — the submodule form of
`finrank_eq_card_mul_finrank`, needed for the finer even/odd split below. -/
private theorem finrank_restrictScalars_eq_card_mul_finrank {N : Submodule D M}
    {ι : Type} [Fintype ι] (bN : Basis ι D (N.restrictScalars K)) :
    finrank K (N.restrictScalars K) = Fintype.card ι * finrank K D := by
  have e : (N.restrictScalars K) ≃ₗ[K] (ι → D) := (Basis.equivFun bN).restrictScalars K
  rw [e.finrank_eq, Module.finrank_pi_fintype (R := K) (M := fun _ : ι => D)]
  simp

omit [Nontrivial D] [FiniteDimensional K D] in
private theorem mem_zero_of_bot_one (h1 : 𝒟 1 = ⊥) (d : D) : d ∈ 𝒟 0 := by
  have hm : modProj 𝒟 1 d ∈ 𝒟 1 := modProj_mem 𝒟 1 d
  rw [h1, Submodule.mem_bot] at hm
  have hsum := modProj_zero_add_modProj_one 𝒟 d
  rw [hm, add_zero] at hsum
  rw [← hsum]
  exact modProj_mem 𝒟 0 d

private theorem zmod2_add_one_ne : ∀ j : ZMod 2, j + 1 ≠ j := by decide

private theorem zmod2_ne_imp_eq_add_one : ∀ a b : ZMod 2, a ≠ b → a = b + 1 := by decide

/-- (Purely even case) either graded piece `ℳ j` is closed under the `D`-action: since
`𝒟 1 = ⊥` forces `D = 𝒟 0` wholly, `SetLike.GradedSMul 𝒟 ℳ` at degree `0` says exactly that.
Bundled as a genuine `Submodule D M` so we can build a `D`-basis of it. -/
def gradeSubmoduleD (h1 : 𝒟 1 = ⊥) (j : ZMod 2) : Submodule D M where
  carrier := ℳ j
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' d x hx := by
    have hd0 : d ∈ 𝒟 0 := mem_zero_of_bot_one 𝒟 h1 d
    have h := SetLike.GradedSMul.smul_mem (A := 𝒟) (B := ℳ) hd0 hx
    rwa [vadd_eq_add, zero_add] at h

omit [Nontrivial D] [FiniteDimensional K D] [DirectSum.Decomposition ℳ] in
theorem restrictScalars_gradeSubmoduleD (h1 : 𝒟 1 = ⊥) (j : ZMod 2) :
    (gradeSubmoduleD 𝒟 ℳ h1 j).restrictScalars K = ℳ j :=
  SetLike.coe_injective rfl

private theorem grade_disjoint {j : ZMod 2} {y : M} (hy0 : y ∈ ℳ j) (hy1 : y ∈ ℳ (j + 1)) :
    y = 0 := by
  have h0 : modProj ℳ j y = y := modProj_of_mem ℳ hy0
  have h1 : modProj ℳ j y = 0 := modProj_of_mem_ne ℳ hy1 (zmod2_add_one_ne j)
  rw [← h0, h1]

omit [Nontrivial D] [FiniteDimensional K D] [IsScalarTower K D M] in
/-- **Support lemma** (purely even case): the `D`-coordinates of a homogeneous vector along
a homogeneous `D`-basis vanish off-degree — the module-`D` analogue of
`Super/GradedEndMatrix.lean`'s `homBasis_repr_eq_zero`, simpler here since every element of
`D` is already homogeneous of degree `0` (`𝒟 1 = ⊥`), so no coefficient splitting is needed:
project the basis expansion of `x` onto the two degrees directly. -/
private theorem repr_eq_zero_of_ne (h1 : 𝒟 1 = ⊥) {r : ℕ} {p : Fin r → ZMod 2}
    (b : Basis (Fin r) D M) (hb : ∀ i, b i ∈ ℳ (p i)) {j : ZMod 2} {x : M} (hx : x ∈ ℳ j)
    {i : Fin r} (hi : p i ≠ j) : b.repr x i = 0 := by
  classical
  set c : Fin r → D := fun k => if p k = j then (0 : D) else b.repr x k with hcdef
  set A : M := ∑ k, (if p k = j then b.repr x k else 0) • b k with hAdef
  set Bsum : M := ∑ k, c k • b k with hBdef
  have hcoef : ∀ k, (if p k = j then b.repr x k else 0) + c k = b.repr x k := by
    intro k; by_cases hk : p k = j <;> simp [hcdef, hk]
  have hxAB : A + Bsum = x := by
    have hstep : A + Bsum = ∑ k, b.repr x k • b k := by
      rw [hAdef, hBdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← add_smul, hcoef k]
    rw [hstep]; exact Basis.sum_repr b x
  have hAmem : A ∈ ℳ j := by
    refine sum_mem fun k _ => ?_
    by_cases hk : p k = j
    · have hd0 : (if p k = j then b.repr x k else 0) ∈ 𝒟 0 := mem_zero_of_bot_one 𝒟 h1 _
      have h := SetLike.GradedSMul.smul_mem (A := 𝒟) (B := ℳ) hd0 (hk ▸ hb k)
      rwa [vadd_eq_add, zero_add] at h
    · simp [hk]
  have hBmem : Bsum ∈ ℳ (j + 1) := by
    refine sum_mem fun k _ => ?_
    by_cases hk : p k = j
    · simp [hcdef, hk]
    · have hpk : p k = j + 1 := zmod2_ne_imp_eq_add_one (p k) j hk
      have hd0 : c k ∈ 𝒟 0 := mem_zero_of_bot_one 𝒟 h1 _
      have h := SetLike.GradedSMul.smul_mem (A := 𝒟) (B := ℳ) hd0 (hpk ▸ hb k)
      rwa [vadd_eq_add, zero_add] at h
  have hBmem' : Bsum ∈ ℳ j := by
    have hBeq : Bsum = x - A := by rw [← hxAB]; abel
    rw [hBeq]; exact sub_mem hx hAmem
  have hB0 : Bsum = 0 := grade_disjoint ℳ hBmem' hBmem
  have hcsum : ∑ k, c k • b k = 0 := by rw [← hBdef]; exact hB0
  have hzero : c i = 0 := Fintype.linearIndependent_iff.mp b.linearIndependent c hcsum i
  rw [hcdef] at hzero
  simpa [if_neg hi] using hzero

omit [Nontrivial D] in
/-- **Purely-even multiplicity formula**: `finrank K (ℳ j) = (#{i : p i = j}) * finrank K D`
for either graded piece `j`, via the sub-basis `{b i : p i = j}` of `ℳ j`
(`Basis.span` applied to the restricted independent family, its span identified with
`gradeSubmoduleD` by the support lemma) and the submodule form of the tower computation,
`finrank_restrictScalars_eq_card_mul_finrank`. -/
theorem finrank_grade_eq_card_mul_finrank (h1 : 𝒟 1 = ⊥) {r : ℕ} {p : Fin r → ZMod 2}
    (b : Basis (Fin r) D M) (hb : ∀ i, b i ∈ ℳ (p i)) (j : ZMod 2) :
    finrank K (ℳ j) = Fintype.card {i : Fin r // p i = j} * finrank K D := by
  classical
  have hli' : LinearIndependent D (fun i : {i : Fin r // p i = j} => b i.1) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have hspaneq : Submodule.span D (Set.range (fun i : {i : Fin r // p i = j} => b i.1))
      = gradeSubmoduleD 𝒟 ℳ h1 j := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (fun x hx => ?_)
    · rintro x ⟨i, rfl⟩
      have hbi := hb i.1
      rwa [i.2] at hbi
    · have hxmem : x ∈ ℳ j := hx
      have hrepr : ∀ k : Fin r, p k ≠ j → b.repr x k = 0 :=
        fun k hk => repr_eq_zero_of_ne 𝒟 ℳ h1 b hb hxmem hk
      have hxeq : x = ∑ k ∈ Finset.univ.filter (fun k => p k = j), (b.repr x k) • b k := by
        conv_lhs => rw [← Basis.sum_repr b x]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => p k = j)
            (fun k => (b.repr x k) • b k)]
        have hzero : ∑ k ∈ Finset.univ.filter (fun k => ¬p k = j), (b.repr x k) • b k = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          rw [Finset.mem_filter] at hk
          rw [hrepr k hk.2, zero_smul]
        rw [hzero, add_zero]
      rw [hxeq,
        Finset.sum_subtype (p := fun k => p k = j) (F := inferInstance)
          (Finset.univ.filter (fun k => p k = j)) (by simp)
          (fun k => (b.repr x k) • b k)]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i))
  have bN : Basis {i : Fin r // p i = j} D ((gradeSubmoduleD 𝒟 ℳ h1 j).restrictScalars K) := by
    rw [← hspaneq]
    exact Basis.span hli'
  have hcard := finrank_restrictScalars_eq_card_mul_finrank bN
  rwa [restrictScalars_gradeSubmoduleD 𝒟 ℳ h1 j] at hcard

/-- **Purely-even case, the finer pair invariant**: for two homogeneous `D`-bases, the
even-count `Fintype.card {i : p i = 0}` (and, symmetrically, the odd-count) agree — cancel
the common factor `finrank K D` from `finrank_grade_eq_card_mul_finrank` applied to each
basis at the same degree `j`. -/
theorem card_grade_eq_of_two_bases (h1 : 𝒟 1 = ⊥) {r₁ r₂ : ℕ}
    {p₁ : Fin r₁ → ZMod 2} {p₂ : Fin r₂ → ZMod 2} (b₁ : Basis (Fin r₁) D M)
    (b₂ : Basis (Fin r₂) D M) (hb₁ : ∀ i, b₁ i ∈ ℳ (p₁ i)) (hb₂ : ∀ i, b₂ i ∈ ℳ (p₂ i))
    (j : ZMod 2) :
    Fintype.card {i : Fin r₁ // p₁ i = j} = Fintype.card {i : Fin r₂ // p₂ i = j} :=
  Nat.eq_of_mul_eq_mul_right (finrank_D_pos (K := K) (D := D))
    ((finrank_grade_eq_card_mul_finrank 𝒟 ℳ h1 b₁ hb₁ j).symm.trans
      (finrank_grade_eq_card_mul_finrank 𝒟 ℳ h1 b₂ hb₂ j))

end Multiplicity

end Bimod

end Superfusion

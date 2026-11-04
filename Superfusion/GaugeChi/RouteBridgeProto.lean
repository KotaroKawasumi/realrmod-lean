/-
Superfusion / GaugeChi / RouteBridgeProto

**The semantic bridge, measured**: one certificate carried end to end at two
triples with genuine block structure, through the coefficient checker.

`GaugeChi/RouteMatrixProto.lean` §8 carried the triple `(1,1,1)` to a
pointwise value of `gParity`, but that triple **degenerates**: `T = 1`, every
frame is `1|0`, so no matrix product is ever multiplied out and no index
bookkeeping happens.  This file removes both degeneracies and, in doing so,
measures the cost of the step the design document left unmeasured — the
**semantic bridge** from `TDictGauge`'s route entry lemmas to
`CoeffChecker`'s integer arrays.

## 0. A blocking discovery: the frozen connectors are in the WRONG FRAME ORDER

`scripts/certgen/out/connectors_cache.json` stores each connector as a flat
`M × M` real matrix, `M = (σ.1+σ.2)·dim D_{a+b+c}`.  Its frame index is the
**naive outer-major Kronecker order**

    (outer block index, inner block index)  ↦  inner + (p₂+q₂)·outer

whereas `gaugeRouteL`/`gaugeRouteR` are built by `matrixSuperComp`, whose
frame index is the **parity-sorted** `collapseIndexEquiv`

    (inl,inl) ↦ even block, (inr,inr) ↦ even block,
    (inl,inr) ↦ odd block,  (inr,inl) ↦ odd block.

The two orders differ at every triple where both composite frames are
genuinely graded.  Worse, the left and the right route factor differently
(`(size a b, size (a+b) c)` versus `(size b c, size a (b+c))`), so **the row
index and the column index of `T` need DIFFERENT permutations**:

    T_lean r s = T_certgen (permR r) (permL s)      (up to an overall scalar)

with `permL`/`permR` the `collapseIndexEquiv`-to-naive position maps of the
two factorizations.  With that transport — and only with it — the frozen
connectors satisfy the Lean intertwining identity: verified offline at **all
500 triples where `hsz` holds**, at every slot generator (a Python model of
the entry lemmas of `TDictGauge` and this file; 6336 generator checks).
Without the transport, 148 of the 500 fail.

This is invisible at `(1,1,1)` (and at `(1,7,1)` below), where one of the two
factors is `1|0` and both orders coincide — which is why `RouteMatrixProto`
§8 did not hit it.  **Any 512-point rollout must apply this transport.**

## 1. The uniform layer (§§1–5): what a rollout writes ONCE

* §1  linearity of the graded tensor and of `Finset.sum` under a fusion map;
* §2  `fuseRow`/`fuseCol`, the flattened frame indices, and `IsFuseZ`, the
      integer shadow of a frozen `realFuseMatrix` literal;
* §3  `realFuse_comboL_entry` / `realFuse_comboR_entry` — **the general,
      dense form of the fusion entry at a linear combination**, which is what
      the second fuse of each route consumes.  `RouteMatrixProto` §7 only had
      the single-nonzero-column specialization.
* §4  **the six slot route matrices as integer coefficient arrays**:
      `routeL_aSlot_coeff`, `routeL_bSlot_coeff`, `routeL_cSlot_coeff`,
      `routeR'_aSlot_coeff`, `routeR'_bSlot_coeff`, `routeR'_cSlot_coeff`.
      Each takes the integer shadows of the two fusion matrices it routes
      through and returns the entry of the route matrix as
      `∑ g, ((closed ℤ expression) : ℝ) • basis g`.  These are the semantic
      bridge; they are `realGauge`-generic and **triple-independent**.
* §5  the consumers: `matOfCoeff_intertwine` (a checked integer convolution
      identity gives the matrix identity), `matOfCoeff_mem_matrixGrading`
      (hypothesis 2), `matOfCoeff_ne_zero`.

Because the coefficient arrays of §4 are *closed computable `ℤ` expressions*
(the index equivalences `gblIndexEquiv`, `gbrNativeIndexEquiv`,
`gaugeSizeCastEquiv` all reduce in the kernel at a literal triple), the
per-triple certificate needs **no arithmetic proof at all**: the whole
convolution identity is one `by decide`.

## 2. The per-triple layer (§§6–7): what a rollout GENERATES

For each triple: `hsz` (`decide`), the integer shadows of its ≤ 4 fusion
matrices (shared across triples — 64 in total for the whole rollout), the
transported connector literal, `hT` (`decide`), `T ≠ 0` (`decide`), one
certificate per slot generator (each: two `Matrix.ext` applications of §4 and
one `decide`), the three slot families, and the assembly through
`gtOfT_mem_interSpace_of_realRepBasis`.  Every line is emitted by
`scripts/certgen`-style generation; none is bespoke.

### The two triples

| triple | `σL = σR` | `dim D_{a+b+c}` | `e` | `T` | generators | permutation |
|---|---|---|---|---|---|---|
| `(1,7,1)` | `1\|1` | 2 (`ℂ`) | 1 | `[[-g,1],[-1,g]]` | 6 | trivial |
| `(1,6,1)` | `2\|2` | 1 (`ℝ`) | 1 | 8 nonzeros | 8 | **nontrivial** |

`(1,7,1)` exercises: a genuinely graded `1|1` frame, a non-identity connector
over a nontrivial coefficient algebra, a live Koszul sign on BOTH sides
(`size 1 7 = size 7 1 = (1,1)`), and `e = 1` so the outer sign
`(−1)^{|y|·e}` is live.  `(1,6,1)` exercises: a `2|2` composite frame, all
four fusion corners nontrivial, intermediate algebras `D₇` of dimension 2 (so
the second fuse really does consume a linear combination), and the
**nontrivial frame permutation** of §0.

No `sorry`, no `native_decide`, no new axioms.

Design record: `docs/route-layer-design.md`; prototype closure:
`GaugeChi/RouteMatrixProto.lean` §8; arithmetic layer:
`GaugeChi/CoeffChecker.lean`.
-/
import Superfusion.GaugeChi.CoeffChecker
import Superfusion.GaugeChi.RouteMatrixProto
import Superfusion.Gauge.RealFuseSpecTransposeClose
import Superfusion.Gauge.RealFuseSpecPeel

namespace Superfusion
namespace GaugeChi

open Module GradedTensorProduct

/-! ### 1. Linearity helpers -/

theorem tmul_sum_left {A B : SuperAlgebra ℝ} {n : ℕ} (u : Fin n → A.carrier) (v : B.carrier) :
    GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ (∑ t, u t) v
      = ∑ t, GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ (u t) v := by
  show GradedTensorProduct.of ℝ A.grading B.grading ((∑ t, u t) ⊗ₜ[ℝ] v) = _
  rw [TensorProduct.sum_tmul, map_sum]

theorem tmul_sum_right {A B : SuperAlgebra ℝ} {n : ℕ} (u : A.carrier) (v : Fin n → B.carrier) :
    GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ u (∑ t, v t)
      = ∑ t, GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ u (v t) := by
  show GradedTensorProduct.of ℝ A.grading B.grading (u ⊗ₜ[ℝ] (∑ t, v t)) = _
  rw [TensorProduct.tmul_sum, map_sum]

private theorem regroup {M : Type*} [AddCommMonoid M] [Module ℝ M] {n m : ℕ}
    (ce : Fin n → ℝ) (d : Fin n → Fin m → ℝ) (v : Fin m → M) :
    ∑ i, ce i • (∑ g, d i g • v g) = ∑ g, (∑ i, ce i * d i g) • v g := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

private theorem matsum_apply {X : Type*} [AddCommMonoid X] [Module ℝ X] {ι : Type*} {n : ℕ}
    (ce : Fin n → ℝ) (M : Fin n → Matrix ι ι X) (r s : ι) :
    (∑ i, ce i • M i) r s = ∑ i, ce i • (M i r s) := by
  rw [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- Pushing a guarded integer rescaling of a basis expansion into the coefficients. -/
theorem cond_zsmul_sum {M : Type*} [AddCommGroup M] [Module ℝ M] {m : ℕ}
    (P : Prop) [Decidable P] (z : ℤ) (x : Fin m → ℝ) (v : Fin m → M) :
    (if P then z • (∑ g, x g • v g) else 0)
      = ∑ g, (if P then (z : ℝ) * x g else 0) • v g := by
  by_cases h : P
  · rw [if_pos h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [if_pos h, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  · rw [if_neg h]
    symm
    exact Finset.sum_eq_zero fun g _ => by rw [if_neg h, zero_smul]

/-- Pushing an algebra map through a basis expansion. -/
theorem map_sum_smul {M N : Type*} [AddCommMonoid M] [Module ℝ M] [AddCommMonoid N]
    [Module ℝ N] {m : ℕ} (f : M →ₗ[ℝ] N) (x : Fin m → ℝ) (v : Fin m → M) :
    f (∑ g, x g • v g) = ∑ g, x g • f (v g) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => map_smul f _ _

/-! ### 2. Frame index abbreviations -/

/-- The flattened target-frame index of the fusion corner `(a,b)`. -/
abbrev fuseRow (a b : ZMod 8) (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2)
    (e : Fin (realRepDim (a + b).val)) :
    Fin (((realSize a b).1 + (realSize a b).2) * ((realSize a b).1 + (realSize a b).2)
      * realRepDim (a + b).val) :=
  matrixSuperIndexEquiv (realSize a b).1 (realSize a b).2 (realRepDim (a + b).val) (r, s, e)

/-- The flattened source-frame index of the fusion corner `(a,b)`. -/
abbrev fuseCol (a b : ZMod 8) (i : Fin (realRepDim a.val)) (j : Fin (realRepDim b.val)) :
    Fin (realRepDim a.val * realRepDim b.val) := finProdFinEquiv (i, j)

/-- The integer shadow of a frozen fusion matrix. -/
abbrev IsFuseZ (a b : ZMod 8)
    (AZ : Fin (((realSize a b).1 + (realSize a b).2) * ((realSize a b).1 + (realSize a b).2)
      * realRepDim (a + b).val) → Fin (realRepDim a.val * realRepDim b.val) → ℤ) : Prop :=
  ∀ f col, realFuseMatrix a b f col = ((AZ f col : ℤ) : ℝ)

/-! ### 3. Fusion images of frame vectors, entrywise -/

theorem realFuse_comboL_entry (a b : ZMod 8) (ce : Fin (realRepDim a.val) → ℝ)
    (j : Fin (realRepDim b.val))
    (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2) :
    (realFuse a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          (∑ i, ce i • realRepBasis a i) (realRepBasis b j)) r s
      = ∑ g : Fin (realRepDim (a + b).val),
          (∑ i, ce i * realFuseMatrix a b (fuseRow a b r s g) (fuseCol a b i j))
            • realRepBasis (a + b) g := by
  classical
  have e1 : GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
        (∑ i, ce i • realRepBasis a i) (realRepBasis b j)
      = ∑ i, ce i • GradedTensorProduct.tmul (𝒜 := (realRep a).grading)
          (ℬ := (realRep b).grading) ℝ (realRepBasis a i) (realRepBasis b j) :=
    (tmul_sum_left (A := realRep a) (B := realRep b) _ _).trans
      (Finset.sum_congr rfl fun i _ => tmul_smul_left _ _ _)
  have e2 : (realFuse a b).toAlgEquiv
        (∑ i, ce i • GradedTensorProduct.tmul (𝒜 := (realRep a).grading)
          (ℬ := (realRep b).grading) ℝ (realRepBasis a i) (realRepBasis b j))
      = ∑ i, ce i • (realFuse a b).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
            (realRepBasis a i) (realRepBasis b j)) :=
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => map_smul _ _ _)
  refine (congrArg (fun M : Matrix (Fin (realSize a b).1 ⊕ Fin (realSize a b).2)
      (Fin (realSize a b).1 ⊕ Fin (realSize a b).2) (realRep (a + b)).carrier => M r s)
    ((congrArg (realFuse a b).toAlgEquiv e1).trans e2)).trans ?_
  refine (matsum_apply _ _ r s).trans ?_
  refine (Finset.sum_congr rfl fun i _ =>
    congrArg (fun w => ce i • w) (realFuse_tmul_entry a b i j r s)).trans ?_
  exact regroup _ _ _

theorem realFuse_comboR_entry (a b : ZMod 8) (i : Fin (realRepDim a.val))
    (ce : Fin (realRepDim b.val) → ℝ)
    (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2) :
    (realFuse a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          (realRepBasis a i) (∑ j, ce j • realRepBasis b j)) r s
      = ∑ g : Fin (realRepDim (a + b).val),
          (∑ j, ce j * realFuseMatrix a b (fuseRow a b r s g) (fuseCol a b i j))
            • realRepBasis (a + b) g := by
  classical
  have e1 : GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
        (realRepBasis a i) (∑ j, ce j • realRepBasis b j)
      = ∑ j, ce j • GradedTensorProduct.tmul (𝒜 := (realRep a).grading)
          (ℬ := (realRep b).grading) ℝ (realRepBasis a i) (realRepBasis b j) :=
    (tmul_sum_right (A := realRep a) (B := realRep b) _ _).trans
      (Finset.sum_congr rfl fun j _ => tmul_smul_right _ _ _)
  have e2 : (realFuse a b).toAlgEquiv
        (∑ j, ce j • GradedTensorProduct.tmul (𝒜 := (realRep a).grading)
          (ℬ := (realRep b).grading) ℝ (realRepBasis a i) (realRepBasis b j))
      = ∑ j, ce j • (realFuse a b).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
            (realRepBasis a i) (realRepBasis b j)) :=
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => map_smul _ _ _)
  refine (congrArg (fun M : Matrix (Fin (realSize a b).1 ⊕ Fin (realSize a b).2)
      (Fin (realSize a b).1 ⊕ Fin (realSize a b).2) (realRep (a + b)).carrier => M r s)
    ((congrArg (realFuse a b).toAlgEquiv e1).trans e2)).trans ?_
  refine (matsum_apply _ _ r s).trans ?_
  refine (Finset.sum_congr rfl fun j _ =>
    congrArg (fun w => ce j • w) (realFuse_tmul_entry a b i j r s)).trans ?_
  exact regroup _ _ _

theorem realFuse_basisL_entry (a b : ZMod 8) (i : Fin (realRepDim a.val))
    (jb : Fin (realRepDim b.val)) (hjb : (jb : ℕ) = 0)
    (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2) :
    (realFuse a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          (realRepBasis a i) 1) r s
      = ∑ g, realFuseMatrix a b (fuseRow a b r s g) (fuseCol a b i jb)
          • realRepBasis (a + b) g := by
  rw [← realRepBasis_zero b jb hjb]
  exact realFuse_tmul_entry a b i jb r s

theorem realFuse_basisR_entry (a b : ZMod 8) (ia : Fin (realRepDim a.val)) (hia : (ia : ℕ) = 0)
    (j : Fin (realRepDim b.val))
    (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2) :
    (realFuse a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          1 (realRepBasis b j)) r s
      = ∑ g, realFuseMatrix a b (fuseRow a b r s g) (fuseCol a b ia j)
          • realRepBasis (a + b) g := by
  rw [← realRepBasis_zero a ia hia]
  exact realFuse_tmul_entry a b ia j r s

theorem realFuse_comboL_one_entry (a b : ZMod 8) (ce : Fin (realRepDim a.val) → ℝ)
    (jb : Fin (realRepDim b.val)) (hjb : (jb : ℕ) = 0)
    (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2) :
    (realFuse a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          (∑ i, ce i • realRepBasis a i) 1) r s
      = ∑ g, (∑ i, ce i * realFuseMatrix a b (fuseRow a b r s g) (fuseCol a b i jb))
          • realRepBasis (a + b) g := by
  rw [← realRepBasis_zero b jb hjb]
  exact realFuse_comboL_entry a b ce jb r s

theorem realFuse_comboR_one_entry (a b : ZMod 8) (ia : Fin (realRepDim a.val))
    (hia : (ia : ℕ) = 0) (ce : Fin (realRepDim b.val) → ℝ)
    (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2) :
    (realFuse a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep b).grading) ℝ
          1 (∑ j, ce j • realRepBasis b j)) r s
      = ∑ g, (∑ j, ce j * realFuseMatrix a b (fuseRow a b r s g) (fuseCol a b ia j))
          • realRepBasis (a + b) g := by
  rw [← realRepBasis_zero a ia hia]
  exact realFuse_comboR_entry a b ia ce r s


/-! ### 4. The six slot route matrices, as integer coefficient arrays -/

theorem algEquiv_sum_smul {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B] {m : ℕ}
    (f : A ≃ₐ[ℝ] B) (x : Fin m → ℝ) (v : Fin m → A) :
    f (∑ g, x g • v g) = ∑ g, x g • f (v g) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => map_smul f _ _

section RouteSlots

variable (a b c : ZMod 8)

/-- Outer block index of the left composite frame. -/
noncomputable abbrev lo
    (I : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    Fin (realSize a b).1 ⊕ Fin (realSize a b).2 :=
  ((gblIndexEquiv ℝ realGauge a b c).symm I).1

/-- Inner block index of the left composite frame. -/
noncomputable abbrev li
    (I : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    Fin (realSize (a + b) c).1 ⊕ Fin (realSize (a + b) c).2 :=
  ((gblIndexEquiv ℝ realGauge a b c).symm I).2

variable (hsz : realGauge.gaugeSizeR a b c = realGauge.gaugeSizeL a b c)

/-- Outer block index of the right composite frame, read at the aligned index. -/
noncomputable abbrev ro
    (I : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    Fin (realSize b c).1 ⊕ Fin (realSize b c).2 :=
  ((gbrNativeIndexEquiv ℝ realGauge a b c).symm
    ((gaugeSizeCastEquiv ℝ realGauge a b c hsz).symm I)).1

/-- Inner block index of the right composite frame, read at the aligned index. -/
noncomputable abbrev ri
    (I : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    Fin (realSize a (b + c)).1 ⊕ Fin (realSize a (b + c)).2 :=
  ((gbrNativeIndexEquiv ℝ realGauge a b c).symm
    ((gaugeSizeCastEquiv ℝ realGauge a b c hsz).symm I)).2

/-- The associativity coefficient cast, applied to the right tower's basis. -/
noncomputable abbrev castBasis (g : Fin (realRepDim (a + (b + c)).val)) :
    (realGauge.D (a + b + c)).carrier :=
  (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv (realRepBasis (a + (b + c)) g)

/-- **Left route at an `a`-slot generator, in coefficient form.** -/
theorem routeL_aSlot_coeff
    {AZ : Fin (((realSize a b).1 + (realSize a b).2) * ((realSize a b).1 + (realSize a b).2)
      * realRepDim (a + b).val) → Fin (realRepDim a.val * realRepDim b.val) → ℤ}
    (hA : IsFuseZ a b AZ)
    {BZ : Fin (((realSize (a + b) c).1 + (realSize (a + b) c).2)
        * ((realSize (a + b) c).1 + (realSize (a + b) c).2) * realRepDim (a + b + c).val)
      → Fin (realRepDim (a + b).val * realRepDim c.val) → ℤ}
    (hB : IsFuseZ (a + b) c BZ)
    (i : Fin (realRepDim a.val))
    (jb : Fin (realRepDim b.val)) (hjb : (jb : ℕ) = 0)
    (jc : Fin (realRepDim c.val)) (hjc : (jc : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    (realGauge.gaugeRouteL a b c).toAlgEquiv
        (aSlot ℝ realGauge a b c (realRepBasis a i)) I J
      = ∑ g, ((∑ e, AZ (fuseRow a b (lo a b c I) (lo a b c J) e) (fuseCol a b i jb)
              * BZ (fuseRow (a + b) c (li a b c I) (li a b c J) g)
                  (fuseCol (a + b) c e jc) : ℤ) : ℝ)
          • realRepBasis (a + b + c) g := by
  refine (routeL_aSlot_entry ℝ realGauge a b c (realRepBasis a i) I J).trans ?_
  refine (congrArg (fun u : (realRep (a + b)).carrier => (realFuse (a + b) c).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep (a + b)).grading) (ℬ := (realRep c).grading) ℝ
        u 1) (li a b c I) (li a b c J))
    (realFuse_basisL_entry a b i jb hjb (lo a b c I) (lo a b c J))).trans ?_
  refine (realFuse_comboL_one_entry (a + b) c _ jc hjc _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => congrArg (fun w : ℝ => w • realRepBasis (a + b + c) g) ?_
  simp only [hA, hB]
  push_cast
  ring

/-- **Left route at a `b`-slot generator, in coefficient form.** -/
theorem routeL_bSlot_coeff
    {AZ : Fin (((realSize a b).1 + (realSize a b).2) * ((realSize a b).1 + (realSize a b).2)
      * realRepDim (a + b).val) → Fin (realRepDim a.val * realRepDim b.val) → ℤ}
    (hA : IsFuseZ a b AZ)
    {BZ : Fin (((realSize (a + b) c).1 + (realSize (a + b) c).2)
        * ((realSize (a + b) c).1 + (realSize (a + b) c).2) * realRepDim (a + b + c).val)
      → Fin (realRepDim (a + b).val * realRepDim c.val) → ℤ}
    (hB : IsFuseZ (a + b) c BZ)
    (ia : Fin (realRepDim a.val)) (hia : (ia : ℕ) = 0)
    (j : Fin (realRepDim b.val))
    (jc : Fin (realRepDim c.val)) (hjc : (jc : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    (realGauge.gaugeRouteL a b c).toAlgEquiv
        (bSlot ℝ realGauge a b c (realRepBasis b j)) I J
      = ∑ g, ((∑ e, AZ (fuseRow a b (lo a b c I) (lo a b c J) e) (fuseCol a b ia j)
              * BZ (fuseRow (a + b) c (li a b c I) (li a b c J) g)
                  (fuseCol (a + b) c e jc) : ℤ) : ℝ)
          • realRepBasis (a + b + c) g := by
  refine (routeL_bSlot_entry ℝ realGauge a b c (realRepBasis b j) I J).trans ?_
  refine (congrArg (fun u : (realRep (a + b)).carrier => (realFuse (a + b) c).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep (a + b)).grading) (ℬ := (realRep c).grading) ℝ
        u 1) (li a b c I) (li a b c J))
    (realFuse_basisR_entry a b ia hia j (lo a b c I) (lo a b c J))).trans ?_
  refine (realFuse_comboL_one_entry (a + b) c _ jc hjc _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => congrArg (fun w : ℝ => w • realRepBasis (a + b + c) g) ?_
  simp only [hA, hB]
  push_cast
  ring

/-- **Left route at a `c`-slot generator, in coefficient form** — the Koszul slot. -/
theorem routeL_cSlot_coeff
    {BZ : Fin (((realSize (a + b) c).1 + (realSize (a + b) c).2)
        * ((realSize (a + b) c).1 + (realSize (a + b) c).2) * realRepDim (a + b + c).val)
      → Fin (realRepDim (a + b).val * realRepDim c.val) → ℤ}
    (hB : IsFuseZ (a + b) c BZ)
    (iab : Fin (realRepDim (a + b).val)) (hiab : (iab : ℕ) = 0)
    (l : Fin (realRepDim c.val))
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    (realGauge.gaugeRouteL a b c).toAlgEquiv
        (cSlot ℝ realGauge a b c (realRepBasis c l)) I J
      = ∑ g, ((if lo a b c I = lo a b c J then
              ((sgn (sumParity (realSize a b).1 (realSize a b).2 (lo a b c I)
                  * realRepBasisParity c l) : ℤˣ) : ℤ)
                * BZ (fuseRow (a + b) c (li a b c I) (li a b c J) g)
                    (fuseCol (a + b) c iab l)
            else 0 : ℤ) : ℝ)
          • realRepBasis (a + b + c) g := by
  refine (routeL_cSlot_entry ℝ realGauge a b c (realRepBasis_mem c l) I J).trans ?_
  refine (congrArg (fun w : (realRep (a + b + c)).carrier =>
      if lo a b c I = lo a b c J then
        ((sgn (sumParity (realSize a b).1 (realSize a b).2 (lo a b c I)
            * realRepBasisParity c l) : ℤˣ) : ℤ) • w else 0)
    (realFuse_basisR_entry (a + b) c iab hiab l (li a b c I) (li a b c J))).trans ?_
  refine (cond_zsmul_sum _ _ _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => congrArg (fun w : ℝ => w • realRepBasis (a + b + c) g) ?_
  by_cases h : lo a b c I = lo a b c J
  · rw [if_pos h, if_pos h, hB]
    push_cast
    ring
  · rw [if_neg h, if_neg h, Int.cast_zero]

/-- **Aligned right route at an `a`-slot generator, in coefficient form** — the Koszul slot. -/
theorem routeR'_aSlot_coeff
    {BZ : Fin (((realSize a (b + c)).1 + (realSize a (b + c)).2)
        * ((realSize a (b + c)).1 + (realSize a (b + c)).2) * realRepDim (a + (b + c)).val)
      → Fin (realRepDim a.val * realRepDim (b + c).val) → ℤ}
    (hB : IsFuseZ a (b + c) BZ)
    (i : Fin (realRepDim a.val))
    (jbc : Fin (realRepDim (b + c).val)) (hjbc : (jbc : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    (realGauge.gaugeRouteR' a b c).toAlgEquiv
        (aSlot ℝ realGauge a b c (realRepBasis a i)) I J
      = ∑ g, ((if ro a b c hsz I = ro a b c hsz J then
              ((sgn (sumParity (realSize b c).1 (realSize b c).2 (ro a b c hsz I)
                  * realRepBasisParity a i) : ℤˣ) : ℤ)
                * BZ (fuseRow a (b + c) (ri a b c hsz I) (ri a b c hsz J) g)
                    (fuseCol a (b + c) i jbc)
            else 0 : ℤ) : ℝ)
          • castBasis a b c g := by
  refine (routeR'_aSlot_entry ℝ realGauge a b c hsz (realRepBasis_mem a i) I J).trans ?_
  refine (congrArg (fun w : (realRep (a + (b + c))).carrier =>
      if ro a b c hsz I = ro a b c hsz J then
        ((sgn (sumParity (realSize b c).1 (realSize b c).2 (ro a b c hsz I)
            * realRepBasisParity a i) : ℤˣ) : ℤ)
          • (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv w else 0)
    (realFuse_basisL_entry a (b + c) i jbc hjbc (ri a b c hsz I) (ri a b c hsz J))).trans ?_
  refine (congrArg (fun w : (realGauge.D (a + b + c)).carrier =>
      if ro a b c hsz I = ro a b c hsz J then
        ((sgn (sumParity (realSize b c).1 (realSize b c).2 (ro a b c hsz I)
            * realRepBasisParity a i) : ℤˣ) : ℤ) • w else 0)
    (algEquiv_sum_smul (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv _ _)).trans ?_
  refine (cond_zsmul_sum _ _ _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => congrArg (fun w : ℝ => w • castBasis a b c g) ?_
  by_cases h : ro a b c hsz I = ro a b c hsz J
  · rw [if_pos h, if_pos h, hB]
    push_cast
    ring
  · rw [if_neg h, if_neg h, Int.cast_zero]

/-- **Aligned right route at a `b`-slot generator, in coefficient form.** -/
theorem routeR'_bSlot_coeff
    {AZ : Fin (((realSize b c).1 + (realSize b c).2) * ((realSize b c).1 + (realSize b c).2)
      * realRepDim (b + c).val) → Fin (realRepDim b.val * realRepDim c.val) → ℤ}
    (hA : IsFuseZ b c AZ)
    {BZ : Fin (((realSize a (b + c)).1 + (realSize a (b + c)).2)
        * ((realSize a (b + c)).1 + (realSize a (b + c)).2) * realRepDim (a + (b + c)).val)
      → Fin (realRepDim a.val * realRepDim (b + c).val) → ℤ}
    (hB : IsFuseZ a (b + c) BZ)
    (j : Fin (realRepDim b.val))
    (jc : Fin (realRepDim c.val)) (hjc : (jc : ℕ) = 0)
    (ia : Fin (realRepDim a.val)) (hia : (ia : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    (realGauge.gaugeRouteR' a b c).toAlgEquiv
        (bSlot ℝ realGauge a b c (realRepBasis b j)) I J
      = ∑ g, ((∑ e, AZ (fuseRow b c (ro a b c hsz I) (ro a b c hsz J) e) (fuseCol b c j jc)
              * BZ (fuseRow a (b + c) (ri a b c hsz I) (ri a b c hsz J) g)
                  (fuseCol a (b + c) ia e) : ℤ) : ℝ)
          • castBasis a b c g := by
  refine (routeR'_bSlot_entry ℝ realGauge a b c hsz (realRepBasis b j) I J).trans ?_
  refine (congrArg (fun u : (realRep (b + c)).carrier =>
      (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv
        ((realFuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep (b + c)).grading) ℝ
            1 u) (ri a b c hsz I) (ri a b c hsz J)))
    (realFuse_basisL_entry b c j jc hjc (ro a b c hsz I) (ro a b c hsz J))).trans ?_
  refine (congrArg (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv
    (realFuse_comboR_one_entry a (b + c) ia hia _ _ _)).trans ?_
  refine (algEquiv_sum_smul (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => congrArg (fun w : ℝ => w • castBasis a b c g) ?_
  simp only [hA, hB]
  push_cast
  ring

/-- **Aligned right route at a `c`-slot generator, in coefficient form.** -/
theorem routeR'_cSlot_coeff
    {AZ : Fin (((realSize b c).1 + (realSize b c).2) * ((realSize b c).1 + (realSize b c).2)
      * realRepDim (b + c).val) → Fin (realRepDim b.val * realRepDim c.val) → ℤ}
    (hA : IsFuseZ b c AZ)
    {BZ : Fin (((realSize a (b + c)).1 + (realSize a (b + c)).2)
        * ((realSize a (b + c)).1 + (realSize a (b + c)).2) * realRepDim (a + (b + c)).val)
      → Fin (realRepDim a.val * realRepDim (b + c).val) → ℤ}
    (hB : IsFuseZ a (b + c) BZ)
    (ib : Fin (realRepDim b.val)) (hib : (ib : ℕ) = 0)
    (l : Fin (realRepDim c.val))
    (ia : Fin (realRepDim a.val)) (hia : (ia : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    (realGauge.gaugeRouteR' a b c).toAlgEquiv
        (cSlot ℝ realGauge a b c (realRepBasis c l)) I J
      = ∑ g, ((∑ e, AZ (fuseRow b c (ro a b c hsz I) (ro a b c hsz J) e) (fuseCol b c ib l)
              * BZ (fuseRow a (b + c) (ri a b c hsz I) (ri a b c hsz J) g)
                  (fuseCol a (b + c) ia e) : ℤ) : ℝ)
          • castBasis a b c g := by
  refine (routeR'_cSlot_entry ℝ realGauge a b c hsz (realRepBasis c l) I J).trans ?_
  refine (congrArg (fun u : (realRep (b + c)).carrier =>
      (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv
        ((realFuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (realRep a).grading) (ℬ := (realRep (b + c)).grading) ℝ
            1 u) (ri a b c hsz I) (ri a b c hsz J)))
    (realFuse_basisR_entry b c ib hib l (ro a b c hsz I) (ro a b c hsz J))).trans ?_
  refine (congrArg (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv
    (realFuse_comboR_one_entry a (b + c) ia hia _ _ _)).trans ?_
  refine (algEquiv_sum_smul (realGauge.gaugeCast (add_assoc a b c).symm).toAlgEquiv _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => congrArg (fun w : ℝ => w • castBasis a b c g) ?_
  simp only [hA, hB]
  push_cast
  ring

end RouteSlots

/-! ### 5. Generic consumers of the coefficient form -/

/-- **The certificate consumer**: a checked integer convolution identity gives the
matrix identity `X · T = c • (T · Y)` over a based algebra. -/
theorem matOfCoeff_intertwine {P : Type*} [Ring P] [Algebra ℝ P] {k : ℕ} {ι : Type*}
    [Fintype ι] (bP : Basis (Fin k) ℝ P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : ℝ) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X T Y : ι → ι → Fin k → ℤ)
    (h : ∀ r t g, convCoeff sg co X T r t g = c * convCoeff sg co T Y r t g) :
    matOfCoeff bP X * matOfCoeff bP T = c • (matOfCoeff bP T * matOfCoeff bP Y) := by
  rw [matOfCoeff_mul hmul hco hco', matOfCoeff_mul hmul hco hco', matOfCoeff_zsmul]
  exact congrArg (matOfCoeff bP) (funext fun r => funext fun t => funext fun g => h r t g)

/-- The `realGauge` instance of `matOfCoeff_intertwine`. -/
theorem realMatOfCoeff_intertwine (m : ZMod 8) {ι : Type*} [Fintype ι] (c : ℤ)
    (X T Y : ι → ι → Fin (realRepDim m.val) → ℤ)
    (h : ∀ r t g, convCoeff (realRepMulSign m) (realRepMulIdx m) X T r t g
      = c * convCoeff (realRepMulSign m) (realRepMulIdx m) T Y r t g) :
    matOfCoeff (realRepBasis m) X * matOfCoeff (realRepBasis m) T
      = c • (matOfCoeff (realRepBasis m) T * matOfCoeff (realRepBasis m) Y) :=
  matOfCoeff_intertwine (realRepBasis m) (realRepBasis_mul m)
    (realRepMulIdx_involutive m) (realRepMulIdx_involutive m) c X T Y h

/-- **The grading of a coefficient matrix**: every basis index carrying a nonzero
coefficient must have the prescribed parity. -/
theorem matOfCoeff_mem_matrixGrading (m : ZMod 8) {p q : ℕ}
    (x : (Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → Fin (realRepDim m.val) → ℤ) (e : ZMod 2)
    (h : ∀ r s g, x r s g = 0 ∨
      realRepBasisParity m g = e + sumParity p q r + sumParity p q s) :
    matOfCoeff (realRepBasis m) x ∈ ((realRep m).matrixSuper p q).grading e := by
  intro r s
  show (∑ g, ((x r s g : ℤ) : ℝ) • realRepBasis m g)
    ∈ (realRep m).grading (e + sumParity p q r + sumParity p q s)
  refine Submodule.sum_mem _ fun g _ => ?_
  rcases h r s g with h0 | hp
  · rw [h0, Int.cast_zero, zero_smul]
    exact zero_mem _
  · exact Submodule.smul_mem _ _ (hp ▸ realRepBasis_mem m g)

/-- A coefficient matrix with a nonzero coefficient is nonzero. -/
theorem matOfCoeff_ne_zero (m : ZMod 8) {ι : Type*} [Fintype ι]
    (x : ι → ι → Fin (realRepDim m.val) → ℤ) (r s : ι) (g : Fin (realRepDim m.val))
    (h : x r s g ≠ 0) : matOfCoeff (realRepBasis m) x ≠ 0 := by
  intro h0
  refine h ?_
  have hz : matOfCoeff (realRepBasis m) x
      = matOfCoeff (realRepBasis m) (fun (_ _ : ι) (_ : Fin (realRepDim m.val)) => (0 : ℤ)) := by
    rw [h0]
    refine (Matrix.ext fun r' s' => ?_).symm
    show ∑ g', ((0 : ℤ) : ℝ) • realRepBasis m g' = 0
    exact Finset.sum_eq_zero fun g' _ => by rw [Int.cast_zero, zero_smul]
  exact congrFun (congrFun (congrFun (matOfCoeff_injective (realRepBasis m) hz) r) s) g

/-- The position of a block-frame index in the flattened order (`inl` block first). -/
def sumPos {p q : ℕ} : Fin p ⊕ Fin q → ℕ
  | Sum.inl i => i.val
  | Sum.inr j => p + j.val

/-- Nested-list lookup for the frozen integer literals. -/
def matGet (L : List (List ℤ)) (i j : ℕ) : ℤ := (L.getD i []).getD j 0

/-! ### The triple `(1,7,1)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_1 = 2`, certgen parity `1`.
The frozen connector literal is transported from certgen's NAIVE
outer-major frame order into Lean's parity-sorted `collapseIndexEquiv`
order on both routes (see the module header). -/
section Triple_171
open Module
theorem hsz171 : realGauge.gaugeSizeR 1 7 1 = realGauge.gaugeSizeL 1 7 1 := by decide
/-- Integer shadow of the frozen `realFuseMatrix 1 7` literal. -/
def fuseZ_1_7 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 1],
    [0, 1, 1, 0],
    [0, 1, -1, 0],
    [1, 0, 0, -1]]
  f.val col.val

theorem hfuseZ_1_7 : IsFuseZ 1 7 fuseZ_1_7 := by
  intro f col
  rw [realFuseMatrix_1_7]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_1_7, matGet] <;> rfl
/-- Integer shadow of the frozen `realFuseMatrix 0 1` literal. -/
def fuseZ_0_1 : Fin 2 → Fin 2 → ℤ := fun f col => matGet
  [[1, 0],
    [0, 1]]
  f.val col.val

theorem hfuseZ_0_1 : IsFuseZ 0 1 fuseZ_0_1 := by
  intro f col
  rw [realFuseMatrix_zero_left_1]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_0_1, matGet, Matrix.one_apply] <;> rfl
/-- Integer shadow of the frozen `realFuseMatrix 7 1` literal. -/
def fuseZ_7_1 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, -1],
    [0, 1, 1, 0],
    [0, -1, 1, 0],
    [1, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_7_1 : IsFuseZ 7 1 fuseZ_7_1 := by
  intro f col
  rw [realFuseMatrix_7_1]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_7_1, matGet] <;> rfl
/-- Integer shadow of the frozen `realFuseMatrix 1 0` literal. -/
def fuseZ_1_0 : Fin 2 → Fin 2 → ℤ := fun f col => matGet
  [[1, 0],
    [0, 1]]
  f.val col.val

theorem hfuseZ_1_0 : IsFuseZ 1 0 fuseZ_1_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_1]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_1_0, matGet, Matrix.one_apply] <;> rfl


/-- **The frozen connector**, as an integer coefficient array over `D_1`. -/
noncomputable def Tc171 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet [[[0, -1], [1, 0]], [[-1, 0], [0, 1]]] (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T171 : ((realGauge.D ((1 : ZMod 8) + 7 + 1)).matrixSuper
    (realGauge.gaugeSizeL 1 7 1).1 (realGauge.gaugeSizeL 1 7 1).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Tc171

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT171 : T171 ∈ ((realGauge.D ((1 : ZMod 8) + 7 + 1)).matrixSuper
    (realGauge.gaugeSizeL 1 7 1).1 (realGauge.gaugeSizeL 1 7 1).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 7 + 1) Tc171 1 (by decide)

theorem T171_ne_zero : T171 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 7 + 1) Tc171 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa171_0 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) = (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((7 : ZMod 8) + 1) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) g) (fuseCol (1 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya171_0 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow ((1 : ZMod 8) + 7) (1 : ZMod 8) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `a`-slot generator `0`.** -/
theorem hinta171_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T171
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Xa171_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Ya171_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_1_7 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 7 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xa171_0 Tc171 Ya171_0 (by decide)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa171_1 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) = (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((7 : ZMod 8) + 1) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) g) (fuseCol (1 : ZMod 8) ((7 : ZMod 8) + 1) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya171_1 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow ((1 : ZMod 8) + 7) (1 : ZMod 8) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `a`-slot generator `1`.** -/
theorem hinta171_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T171
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Xa171_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 hfuseZ_1_0 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Ya171_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_1_7 hfuseZ_0_1 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 7 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xa171_1 Tc171 Ya171_1 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb171_0 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((7 : ZMod 8) + 1) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) g) (fuseCol (1 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb171_0 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow ((1 : ZMod 8) + 7) (1 : ZMod 8) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `b`-slot generator `0`.** -/
theorem hintb171_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T171
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Xb171_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 hfuseZ_7_1 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Yb171_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_1_7 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 7 + 1) ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xb171_0 Tc171 Yb171_0 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb171_1 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((7 : ZMod 8) + 1) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) g) (fuseCol (1 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb171_1 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow ((1 : ZMod 8) + 7) (1 : ZMod 8) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `b`-slot generator `1`.** -/
theorem hintb171_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T171
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Xb171_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 hfuseZ_7_1 hfuseZ_1_0 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Yb171_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_1_7 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 7 + 1) ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xb171_1 Tc171 Yb171_1 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc171_0 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((7 : ZMod 8) + 1) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) g) (fuseCol (1 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc171_0 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) = (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_1 (fuseRow ((1 : ZMod 8) + 7) (1 : ZMod 8) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 7) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- **The intertwining certificate at the `c`-slot generator `0`.** -/
theorem hintc171_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T171
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Xc171_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 hfuseZ_7_1 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Yc171_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 7 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xc171_0 Tc171 Yc171_0 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc171_1 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ro (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((7 : ZMod 8) + 1) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 I) (ri (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 J) g) (fuseCol (1 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc171_1 : (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → (Fin (realGauge.gaugeSizeL 1 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 7 1).2) → Fin (realRepDim ((1 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) = (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (lo (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_1 (fuseRow ((1 : ZMod 8) + 7) (1 : ZMod 8) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 7) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- **The intertwining certificate at the `c`-slot generator `1`.** -/
theorem hintc171_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T171
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Xc171_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 hfuseZ_7_1 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 7 + 1)) Yc171_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 7 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xc171_1 Tc171 Yc171_1 (by decide)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint171 (i : Fin (realRepDim ((1 : ZMod 8)).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T171
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta171_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta171_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint171 (i : Fin (realRepDim ((7 : ZMod 8)).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T171
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb171_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb171_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint171 (i : Fin (realRepDim ((1 : ZMod 8)).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T171
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T171 * (realGauge.gaugeRouteL (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc171_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc171_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT171_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 T171 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 hT171 hAint171 hBint171 hCint171

theorem gtOfT171_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 T171 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz171 T171_ne_zero

theorem gInterSpace171_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT171_mem_gInterSpace, gtOfT171_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity171 : gParity ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) gInterSpace171_ne_bot).symm

end Triple_171

/-! ### The triple `(1,6,1)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_0 = 1`, certgen parity `1`.
The frozen connector literal is transported from certgen's NAIVE
outer-major frame order into Lean's parity-sorted `collapseIndexEquiv`
order on both routes (see the module header). -/
section Triple_161
open Module
theorem hsz161 : realGauge.gaugeSizeR 1 6 1 = realGauge.gaugeSizeL 1 6 1 := by decide
/-- Integer shadow of the frozen `realFuseMatrix 1 6` literal. -/
def fuseZ_1_6 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 0, 0, -1],
    [0, 0, 1, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, -1, 0, 0],
    [0, 0, 1, 0, -1, 0, 0, 0],
    [0, 0, 0, -1, 0, -1, 0, 0],
    [1, 0, 0, 0, 0, 0, -1, 0],
    [0, -1, 0, 0, 0, 0, 0, -1]]
  f.val col.val

theorem hfuseZ_1_6 : IsFuseZ 1 6 fuseZ_1_6 := by
  intro f col
  rw [realFuseMatrix_1_6]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_1_6, matGet] <;> rfl
/-- Integer shadow of the frozen `realFuseMatrix 6 1` literal. -/
def fuseZ_6_1 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, -1],
    [0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0],
    [0, -1, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, -1, 0],
    [1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, -1]]
  f.val col.val

theorem hfuseZ_6_1 : IsFuseZ 6 1 fuseZ_6_1 := by
  intro f col
  rw [realFuseMatrix_6_1]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_6_1, matGet] <;> rfl


/-- **The frozen connector**, as an integer coefficient array over `D_0`. -/
noncomputable def Tc161 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun r s g => coeffGet [[[0], [0], [1], [-1]], [[0], [0], [1], [1]], [[-1], [-1], [0], [0]], [[1], [-1], [0], [0]]] (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T161 : ((realGauge.D ((1 : ZMod 8) + 6 + 1)).matrixSuper
    (realGauge.gaugeSizeL 1 6 1).1 (realGauge.gaugeSizeL 1 6 1).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Tc161

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT161 : T161 ∈ ((realGauge.D ((1 : ZMod 8) + 6 + 1)).matrixSuper
    (realGauge.gaugeSizeL 1 6 1).1 (realGauge.gaugeSizeL 1 6 1).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 6 + 1) Tc161 1 (by decide)

theorem T161_ne_zero : T161 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 6 + 1) Tc161 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa161_0 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) = (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (1 : ZMod 8)).1 (realSize (6 : ZMod 8) (1 : ZMod 8)).2 (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya161_0 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `a`-slot generator `0`.** -/
theorem hinta161_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xa161_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Ya161_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_1_6 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xa161_0 Tc161 Ya161_0 (by decide)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa161_1 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) = (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (1 : ZMod 8)).1 (realSize (6 : ZMod 8) (1 : ZMod 8)).2 (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya161_1 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `a`-slot generator `1`.** -/
theorem hinta161_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xa161_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Ya161_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_1_6 hfuseZ_7_1 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xa161_1 Tc161 Ya161_1 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb161_0 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_1 (fuseRow (6 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) ee) (fuseCol (6 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb161_0 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `b`-slot generator `0`.** -/
theorem hintb161_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xb161_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_6_1 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Yb161_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_1_6 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xb161_0 Tc161 Yb161_0 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb161_1 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_1 (fuseRow (6 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) ee) (fuseCol (6 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb161_1 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `b`-slot generator `1`.** -/
theorem hintb161_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xb161_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_6_1 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Yb161_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_1_6 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xb161_1 Tc161 Yb161_1 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb161_2 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_1 (fuseRow (6 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) ee) (fuseCol (6 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb161_2 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `b`-slot generator `2`.** -/
theorem hintb161_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xb161_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_6_1 hfuseZ_1_7 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Yb161_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_1_6 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xb161_2 Tc161 Yb161_2 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb161_3 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_1 (fuseRow (6 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) ee) (fuseCol (6 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb161_3 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- **The intertwining certificate at the `b`-slot generator `3`.** -/
theorem hintb161_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xb161_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_6_1 hfuseZ_1_7 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Yb161_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_1_6 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xb161_3 Tc161 Yb161_3 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc161_0 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_1 (fuseRow (6 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) ee) (fuseCol (6 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc161_0 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) = (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- **The intertwining certificate at the `c`-slot generator `0`.** -/
theorem hintc161_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xc161_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_6_1 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Yc161_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xc161_0 Tc161 Yc161_0 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc161_1 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_1 (fuseRow (6 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ro (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) ee) (fuseCol (6 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((6 : ZMod 8) + 1) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 I) (ri (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 J) g) (fuseCol (1 : ZMod 8) ((6 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc161_1 : (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → (Fin (realGauge.gaugeSizeL 1 6 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 6 1).2) → Fin (realRepDim ((1 : ZMod 8) + 6 + 1).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) = (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (lo (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_1 (fuseRow ((1 : ZMod 8) + 6) (1 : ZMod 8) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 6) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- **The intertwining certificate at the `c`-slot generator `1`.** -/
theorem hintc161_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T161
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Xc161_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hfuseZ_6_1 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 6 + 1)) Yc161_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff_intertwine ((1 : ZMod 8) + 6 + 1) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) Xc161_1 Tc161 Yc161_1 (by decide)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint161 (i : Fin (realRepDim ((1 : ZMod 8)).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T161
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta161_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta161_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint161 (i : Fin (realRepDim ((6 : ZMod 8)).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T161
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintb161_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintb161_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintb161_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintb161_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint161 (i : Fin (realRepDim ((1 : ZMod 8)).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T161
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T161 * (realGauge.gaugeRouteL (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc161_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc161_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT161_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 T161 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 hT161 hAint161 hBint161 hCint161

theorem gtOfT161_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 T161 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) hsz161 T161_ne_zero

theorem gInterSpace161_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT161_mem_gInterSpace, gtOfT161_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity161 : gParity ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (6 : ZMod 8) (1 : ZMod 8) gInterSpace161_ne_bot).symm

end Triple_161

end GaugeChi

end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.gParity171
#print axioms Superfusion.GaugeChi.gParity161
#print axioms Superfusion.GaugeChi.routeL_aSlot_coeff
#print axioms Superfusion.GaugeChi.routeR'_cSlot_coeff

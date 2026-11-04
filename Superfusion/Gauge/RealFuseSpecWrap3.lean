/-
Superfusion / Gauge / RealFuseSpecWrap3

M15 semantic-bridge GROUP C (final part): the **ampliated wrap pairs** —
the branches of `RealFuse4` whose Clifford floors sum *past* the Bott
floor `4` by more than nothing, so that after the floor-`4` certificate
a genuine matrix-ampliation tail
`M_{1|1}(ℍ) ᵍ⊗ Cl → M_{1|1}(ℍ ᵍ⊗ Cl) → M_{1|1}(M_{1|0}(D)) → M_{1|1}(D)`
has to be evaluated.

**Landed here**

* `realFuseMatrix_2_3` (32 × 32), through the `ε = -1` composite
  certificate `divisionTowerNegFourQuatSuper` and `realFuse_four_one`,
* `realFuseMatrix_3_2` — its Koszul transpose, decoder form,
* `realFuseMatrix_5_6` (32 × 32), through the field-generic
  `towerFourQuatSuper` and `realFuse_four_seven`,
* `realFuseMatrix_6_5` — its Koszul transpose, decoder form.

**The machinery.**  Everything is factored so that a single column of a
branch is one application of a `colEngine` lemma.

1. `tfuseK` / `tfuseKsymm` — the tower fusion at a *named* target index
   (`e_i ᵍ⊗ e_j ↦ e_k` whenever `k = i + 2^a·j`), and its inverse,
   crossed with `AlgEquiv.symm_apply_eq` only.  `splitAB` chains the two
   into the `Cl_{a+b} ≅ Cl_4 ᵍ⊗ Cl_1` regrouping used by both branches.
2. `termG` — **the ampliation tail on a single matrix entry**, generic
   in the two superalgebras: `(single r c q) ᵍ⊗ w ↦ (-1)^{|c||w|} ·
   single (collapse r) (collapse c) (F (q ᵍ⊗ w))`.  The only sign is
   `matrixSuperGtensor`'s column twist; it is carried as a `ℤˣ` through
   `msg_single'` and converted to a real coefficient at the very end
   (`zsmul_dstS`).  No inverse is ever unfolded, and no rewrite is ever
   attempted against the branch composite: the whole chain is built with
   `congrArg`/`Eq.trans`, so that the `realRep`-versus-`divisionTower`
   spelling mismatch never has to be seen by `rw`.
3. `fG` — the `(4,1)` / `(4,7)` seed values re-expressed on *signed
   quaternion literals*: `F ((σ • quatBasis e) ᵍ⊗ w) = single (inl 0)
   (inl 0) ((σ t) • bT idx)`, pulling the scalar through the left slot
   (`gtmul_smul_left`).
4. `d3_*` (source frame of `M_{1|0}(D)`) and `dm_*` (target frame of
   `M_{1|1}(D)`, all 32 entries, generic in `ε`) — the two frame
   dictionaries, both instances of `matrixSuperBasis_apply_pair`.

**Not landed here** — the two `64 × 64` siblings `(3,3)` and `(5,5)`.
They have the same tower half (`towerFuse ε a b ; (towerFuse ε 4 2).symm`
after splitting `6 = 4 + 2`), but their ampliation tail runs through
`realFuse_four_two` / `realFuse_four_six` instead of
`realFuse_four_one` / `realFuse_four_seven`, and those two are
*not* single-entry maps: they land in `M_{1|1}(Cl_{∓2})` with **two**
nonzero entries per column, so the frozen literals `fuse_3_3` /
`fuse_5_5` carry **four** nonzero entries per column rather than two.
Concretely what is still missing:

* element-level values of `realFuse_four_six` on
  `quatBasis e ᵍ⊗ towerBasis 1 2 v` (16 of them).  They are one
  `gtensorAssoc`/`matrixSuperOne` composition away from `val47_*`
  together with `RealFuseSpecPeel`'s `c3_7_0 … c3_7_15` (the
  `peelFuse (baseFuseR 2)` column values, already landed there);
* the mirror for `realFuse_four_two`, which additionally has to cross
  the Koszul braiding, since `realFuse_five_one` is
  `realFuse_transpose realFuse_one_five` and only the `(1,5)` direction
  is pinned (`RealFuseSpecPeel`);
* a two-entry variant of `termG` (the tail then ends in
  `matrixSuperComp T 1 1 1 1`, not `… 1 1 1 0`), giving four terms per
  column instead of two.

Everything else in this file — `tfuseK`/`tfuseKsymm`, `fG`, the frame
dictionaries, the `congrArg`-only assembly discipline — carries over
unchanged.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7).
-/
import Superfusion.Gauge.RealFuseSpecWrap2

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Superfusion

open Module TensorProduct GradedTensorProduct Quaternion

open private q1 q1_def mem_q1 towerFuse_basis hmem_tone
  val41_0_0 val41_0_1 val41_1_0 val41_1_1 val41_2_0 val41_2_1 val41_3_0 val41_3_1
  val47_0_0 val47_0_1 val47_1_0 val47_1_1 val47_2_0 val47_2_1 val47_3_0 val47_3_1
  from Superfusion.Gauge.RealFuseSpecQuat

open private qi qj qk n1 nqi nqj nqk offM diaM
  sb_p_0 sb_p_1 sb_p_2 sb_p_3 sb_m_0 sb_m_1 sb_m_2 sb_m_3
  towerBasis_one_zero towerBasis_one_one superRefl_apply
  qv4_0 qv4_1 qv4_2 qv4_3 qv4_4 qv4_5 qv4_6 qv4_7
  qv4_8 qv4_9 qv4_10 qv4_11 qv4_12 qv4_13 qv4_14 qv4_15
  from Superfusion.Gauge.RealFuseSpecWrap

open private nqv4_0 nqv4_1 nqv4_2 nqv4_3 nqv4_4 nqv4_5 nqv4_6 nqv4_7
  nqv4_8 nqv4_9 nqv4_10 nqv4_11 nqv4_12 nqv4_13 nqv4_14 nqv4_15
  msg_single' matrixSuperMap_single' matrixSuperComp_single'
  from Superfusion.Gauge.RealFuseSpecWrap2

/-! ### Generic scalar/entry plumbing -/

/-- A scalar pulls out of the left slot of `ᵍ⊗ₜ`. -/
private theorem gtmul_smul_left {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A)
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (c : ℝ) (x : A) (y : B) :
    ((c • x) ᵍ⊗ₜ[ℝ] y : 𝒜 ᵍ⊗[ℝ] ℬ) = c • (x ᵍ⊗ₜ[ℝ] y) := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ ((c • x) ⊗ₜ[ℝ] y) = _
  rw [← TensorProduct.smul_tmul', map_smul]

/-- Scalars pass into the entry of a single-entry matrix. -/
private theorem single_smulG {P : SuperAlgebra ℝ} {p q : ℕ} (t : ℝ)
    (r c : Fin p ⊕ Fin q) (v : P.carrier) :
    (t • (Matrix.single r c v : (P.matrixSuper p q).carrier))
      = Matrix.single r c (t • v) := by
  show (t • (Matrix.single r c v :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier))
    = Matrix.single r c (t • v)
  refine Matrix.ext fun x y => ?_
  rw [Matrix.smul_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp

/-- The same, taking the single-entry shape as a hypothesis so that the
`HSMul` type argument stays in the *bundled* spelling. -/
private theorem smul_dstG {P : SuperAlgebra ℝ} {p q : ℕ} (t : ℝ)
    {r c : Fin p ⊕ Fin q} {v : P.carrier} {M : (P.matrixSuper p q).carrier}
    (hM : M = Matrix.single r c v) : t • M = Matrix.single r c (t • v) := by
  rw [hM]; exact single_smulG t r c v

/-- The `ℤ`-scalar of the Koszul twist, converted to a real coefficient. -/
private theorem zsmul_dstS {P : SuperAlgebra ℝ} (n : ℤ) (r c : Fin 1 ⊕ Fin 1)
    (t : ℝ) (v : P.carrier) {κ : ℝ} (h : ((n : ℝ)) * t = κ) :
    n • (Matrix.single r c (t • v) : (P.matrixSuper 1 1).carrier)
      = Matrix.single r c (κ • v) := by
  have e1 : n • (Matrix.single r c (t • v) : (P.matrixSuper 1 1).carrier)
      = ((n : ℝ)) • (Matrix.single r c (t • v) : (P.matrixSuper 1 1).carrier) :=
    (Int.cast_smul_eq_zsmul ℝ n _).symm
  rw [e1, single_smulG, smul_smul, h]

/-! ### The tower fusion at a named index -/

private theorem tfuseK (ε : ℝ) (a b : ℕ) (i : Fin (2 ^ a)) (j : Fin (2 ^ b))
    (k : Fin (2 ^ (a + b))) (h : (k : ℕ) = (i : ℕ) + 2 ^ a * (j : ℕ)) :
    (towerFuse ε a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε b).grading) ℝ
          (towerBasis ε a i) (towerBasis ε b j))
      = towerBasis ε (a + b) k := by
  rw [towerFuse_basis ε a b i j]
  congr 1
  exact (Fin.ext h).symm

private theorem tfuseKsymm (ε : ℝ) (a b : ℕ) (i : Fin (2 ^ a)) (j : Fin (2 ^ b))
    (k : Fin (2 ^ (a + b))) (h : (k : ℕ) = (i : ℕ) + 2 ^ a * (j : ℕ)) :
    (towerFuse ε a b).symm.toAlgEquiv (towerBasis ε (a + b) k)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε b).grading) ℝ
          (towerBasis ε a i) (towerBasis ε b j) := by
  show ((towerFuse ε a b).toAlgEquiv).symm _ = _
  rw [AlgEquiv.symm_apply_eq]
  exact (tfuseK ε a b i j k h).symm

/-! ### The two shapes of a floor-`4` certificate value -/

private theorem offM_eq (a b : ℍ[ℝ]) : offM a b
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) a
      + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) b := rfl

private theorem diaM_eq (a b : ℍ[ℝ]) : diaM a b
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) a
      + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) b := rfl

/-! ### The floor-`1` frame -/

private theorem tb1z (ε : ℝ) :
    towerBasis ε 1 0 = (1 : (divisionTower ε 1).carrier) := towerBasis_one_zero ε

private theorem tb1g (ε : ℝ) : towerBasis ε 1 1 = q1 ε := towerBasis_one_one ε

/-! ### The `(4,·)` seed values on signed quaternion literals -/

private theorem fG {R T : SuperAlgebra ℝ}
    (F : SuperAlgEquiv (quatEvenSuper.gtensor R) (T.matrixSuper 1 0))
    (σ t' : ℝ) {e : Fin 4} {t : ℝ} {bT : Basis (Fin 8) ℝ T.carrier}
    {idx : Fin 8} {w : R.carrier} {q : ℍ[ℝ]}
    (hb : F.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := R.grading) ℝ (quatBasis e) w)
          = t • matrixSuperBasis bT 1 0 idx)
    (hd : matrixSuperBasis bT 1 0 idx
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (bT idx))
    (hq : σ • quatBasis e = q) (ht : σ * t = t') :
    F.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := R.grading) ℝ q w)
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (t' • bT idx) := by
  have h0 : GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := R.grading) ℝ q w
      = σ • GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := R.grading) ℝ (quatBasis e) w := by
    rw [← hq]
    exact gtmul_smul_left quatEvenSuper.grading R.grading σ (quatBasis e) w
  refine (congrArg (fun z => F.toAlgEquiv z) h0).trans ?_
  refine (map_smul F.toAlgEquiv σ _).trans ?_
  rw [hb]
  refine (smul_dstG σ (smul_dstG t hd)).trans ?_
  rw [smul_smul, ht]

/-! ### The matrix-ampliation tail, on one entry -/

private theorem termG {R T : SuperAlgebra ℝ}
    (F : SuperAlgEquiv (quatEvenSuper.gtensor R) (T.matrixSuper 1 0))
    {jw : ZMod 2} {w : R.carrier} (hw : w ∈ R.grading jw)
    (r c : Fin 1 ⊕ Fin 1) {q : ℍ[ℝ]} {t : ℝ}
    {bT : Basis (Fin 8) ℝ T.carrier} {idx : Fin 8}
    (hF : F.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := R.grading) ℝ q w)
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
              (t • bT idx))
    {κ : ℝ} {I : Fin 32}
    (hI : matrixSuperBasis bT 1 1 I
          = Matrix.single (collapseIndexEquiv 1 1 1 0 (r, Sum.inl 0))
              (collapseIndexEquiv 1 1 1 0 (c, Sum.inl 0)) (bT idx))
    (hκ : (((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) : ℝ) * t = κ) :
    ((matrixSuperGtensor quatEvenSuper R 1 1).trans
        ((F.matrixSuper 1 1).trans (matrixSuperComp T 1 1 1 0))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := R.grading) ℝ (Matrix.single r c q) w)
      = κ • matrixSuperBasis bT 1 1 I := by
  have h1 := msg_single' quatEvenSuper R 1 1 r c q hw
  have h2 : (F.matrixSuper 1 1).toAlgEquiv
        (Matrix.single r c
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := R.grading) ℝ q w))
      = Matrix.single r c
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
            (t • bT idx)) :=
    (matrixSuperMap_single' F 1 1 r c _).trans (congrArg _ hF)
  have h3 := matrixSuperComp_single' T 1 1 1 0 r c
    (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (t • bT idx)
  have e1 : ((matrixSuperGtensor quatEvenSuper R 1 1).trans
        ((F.matrixSuper 1 1).trans (matrixSuperComp T 1 1 1 0))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := R.grading) ℝ (Matrix.single r c q) w)
      = (matrixSuperComp T 1 1 1 0).toAlgEquiv
          ((F.matrixSuper 1 1).toAlgEquiv
            ((matrixSuperGtensor quatEvenSuper R 1 1).toAlgEquiv
              (GradedTensorProduct.tmul
                (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
                (ℬ := R.grading) ℝ (Matrix.single r c q) w))) := rfl
  refine e1.trans ?_
  refine (congrArg (fun z => (matrixSuperComp T 1 1 1 0).toAlgEquiv
      ((F.matrixSuper 1 1).toAlgEquiv z)) h1).trans ?_
  refine (congrArg (matrixSuperComp T 1 1 1 0).toAlgEquiv
      ((map_zsmul (F.matrixSuper 1 1).toAlgEquiv _ _).trans
        (congrArg (fun z => ((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) • z)
          h2))).trans ?_
  refine ((map_zsmul (matrixSuperComp T 1 1 1 0).toAlgEquiv _ _).trans
      (congrArg (fun z => ((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) • z)
        h3)).trans ?_
  rw [smul_dstG κ hI]
  exact zsmul_dstS _ _ _ t _ hκ


/-! ### The source frame of `M_{1|0}(D)` -/

private theorem d3_0 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 0
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 0

private theorem d3_1 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 1
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 1

private theorem d3_2 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 2
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 2

private theorem d3_3 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 3
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 3

private theorem d3_4 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 4
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 4) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 4

private theorem d3_5 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 5
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 5) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 5

private theorem d3_6 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 6
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 6) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 6

private theorem d3_7 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 0 7
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (towerBasis ε 3 7) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) 7


/-! ### The target frame of `M_{1|1}(D)` (index `e + 8·(s' + 2·r')`) -/

private theorem dm_0 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 0
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 0

private theorem dm_1 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 1
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 1

private theorem dm_2 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 2
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 2

private theorem dm_3 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 3
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 3

private theorem dm_4 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 4
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 4) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 4

private theorem dm_5 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 5
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 5) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 5

private theorem dm_6 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 6
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 6) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 6

private theorem dm_7 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 7
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 7) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inl 0) 7

private theorem dm_8 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 8
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 0

private theorem dm_9 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 9
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 1

private theorem dm_10 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 10
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 2

private theorem dm_11 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 11
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 3

private theorem dm_12 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 12
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 4) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 4

private theorem dm_13 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 13
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 5) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 5

private theorem dm_14 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 14
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 6) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 6

private theorem dm_15 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 15
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 7) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inl 0) (Sum.inr 0) 7

private theorem dm_16 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 16
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 0

private theorem dm_17 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 17
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 1

private theorem dm_18 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 18
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 2

private theorem dm_19 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 19
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 3

private theorem dm_20 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 20
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 4) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 4

private theorem dm_21 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 21
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 5) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 5

private theorem dm_22 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 22
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 6) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 6

private theorem dm_23 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 23
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 3 7) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inl 0) 7

private theorem dm_24 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 24
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 0

private theorem dm_25 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 25
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 1

private theorem dm_26 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 26
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 2

private theorem dm_27 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 27
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 3

private theorem dm_28 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 28
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 4) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 4

private theorem dm_29 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 29
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 5) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 5

private theorem dm_30 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 30
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 6) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 6

private theorem dm_31 (ε : ℝ) : matrixSuperBasis (towerBasis ε 3) 1 1 31
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 3 7) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 1 (Sum.inr 0) (Sum.inr 0) 7

/-! ### The `(2,3)` branch (`Cl_{0,2} ᵍ⊗ Cl_{0,3}`, `ε = -1`) -/

private theorem unfold23 (x : ((divisionTower (-1 : ℝ) 2).gtensor (divisionTower (-1 : ℝ) 3)).carrier) :
    realFuse_two_three.toAlgEquiv x
      = ((matrixSuperGtensor quatEvenSuper (divisionTower (-1 : ℝ) 1) 1 1).trans
          ((realFuse_four_one.matrixSuper 1 1).trans
            (matrixSuperComp (divisionTower (1 : ℝ) 3) 1 1 1 0))).toAlgEquiv
          ((divisionTowerNegFourQuatSuper.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
            ((towerFuse (-1 : ℝ) 4 1).symm.toAlgEquiv
              ((towerFuse (-1 : ℝ) 2 3).toAlgEquiv x))) := rfl


private theorem split23 (i : Fin 4) (j : Fin 8) (u : Fin 16) (v : Fin 2)
    (k : Fin 32) (h1 : (k : ℕ) = (i : ℕ) + 4 * (j : ℕ))
    (h2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ)) :
    (towerFuse (-1 : ℝ) 4 1).symm.toAlgEquiv
        ((towerFuse (-1 : ℝ) 2 3).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
            (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ
            (towerBasis (-1 : ℝ) 2 i) (towerBasis (-1 : ℝ) 3 j)))
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 4).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 4 u) (towerBasis (-1 : ℝ) 1 v) := by
  rw [tfuseK (-1 : ℝ) 2 3 i j k h1]
  exact tfuseKsymm (-1 : ℝ) 4 1 u v k h2


private theorem colEngine23 (i : Fin 4) (j : Fin 8) (u : Fin 16) (v : Fin 2)
    (k : Fin 32) (hk1 : (k : ℕ) = (i : ℕ) + 4 * (j : ℕ))
    (hk2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ))
    {jw : ZMod 2} {w : (divisionTower (-1 : ℝ) 1).carrier}
    (hwv : towerBasis (-1 : ℝ) 1 v = w)
    (hw : w ∈ (divisionTower (-1 : ℝ) 1).grading jw)
    (r1 c1 r2 c2 : Fin 1 ⊕ Fin 1) {qa qb : ℍ[ℝ]}
    (hcert : divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 u)
        = Matrix.single r1 c1 qa + Matrix.single r2 c2 qb)
    (ta tb : ℝ) {ea eb : Fin 8}
    (hFa : realFuse_four_one.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ qa w)
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
              (ta • towerBasis (1 : ℝ) 3 ea))
    (hFb : realFuse_four_one.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ qb w)
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
              (tb • towerBasis (1 : ℝ) 3 eb))
    {κ1 κ2 : ℝ} {I1 I2 : Fin 32}
    (hI1 : matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 I1
        = Matrix.single (collapseIndexEquiv 1 1 1 0 (r1, Sum.inl 0))
            (collapseIndexEquiv 1 1 1 0 (c1, Sum.inl 0)) (towerBasis (1 : ℝ) 3 ea))
    (hI2 : matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 I2
        = Matrix.single (collapseIndexEquiv 1 1 1 0 (r2, Sum.inl 0))
            (collapseIndexEquiv 1 1 1 0 (c2, Sum.inl 0)) (towerBasis (1 : ℝ) 3 eb))
    (hκ1 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb = κ2) :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) (finProdFinEquiv (i, j)))
      = κ1 • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 I1
        + κ2 • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 I2 := by
  refine (congrArg (fun z => realFuse_two_three.toAlgEquiv z)
      (gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) i j)).trans ?_
  refine (unfold23 _).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 1) 1 1).trans
        ((realFuse_four_one.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 3) 1 1 1 0))).toAlgEquiv
      ((divisionTowerNegFourQuatSuper.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv z))
      (split23 i j u v k hk1 hk2)).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 1) 1 1).trans
        ((realFuse_four_one.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 3) 1 1 1 0))).toAlgEquiv z)
      (SuperAlgEquiv.gtensorCongr_tmul divisionTowerNegFourQuatSuper
        (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))
        (towerBasis (-1 : ℝ) 4 u) (towerBasis (-1 : ℝ) 1 v))).trans ?_
  have e3 : GradedTensorProduct.tmul
        (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
        (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
        (divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 u))
        ((SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1)).toAlgEquiv
          (towerBasis (-1 : ℝ) 1 v))
      = GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (Matrix.single r1 c1 qa) w
        + GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (Matrix.single r2 c2 qb) w := by
    rw [superRefl_apply, hwv, hcert]
    exact add_gtmul (matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
      (divisionTower (-1 : ℝ) 1).grading _ _ _
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 1) 1 1).trans
        ((realFuse_four_one.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 3) 1 1 1 0))).toAlgEquiv z) e3).trans ?_
  refine (map_add ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 1) 1 1).trans
        ((realFuse_four_one.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 3) 1 1 1 0))).toAlgEquiv _ _).trans ?_
  exact congrArg₂ (fun x y => x + y)
    (termG realFuse_four_one hw r1 c1 hFa hI1 hκ1) (termG realFuse_four_one hw r2 c2 hFb hI2 hκ2)


private theorem col23_0 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 0)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 24 :=
  colEngine23 0 0 0 0 0 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_0) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_p_0 (by norm_num))
    (dm_0 (1 : ℝ)) (dm_24 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_1 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 1)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 11
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 19 :=
  colEngine23 0 1 4 0 4 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_4) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_m_1 (by norm_num))
    (dm_11 (1 : ℝ)) (dm_19 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_2 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 2)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 8
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 16 :=
  colEngine23 0 2 8 0 8 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_8) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_m_0 (by norm_num))
    (dm_8 (1 : ℝ)) (dm_16 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_3 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 3)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 3
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 27 :=
  colEngine23 0 3 12 0 12 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_12) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_m_1 (by norm_num))
    (dm_3 (1 : ℝ)) (dm_27 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_4 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 4)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 7
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 31 :=
  colEngine23 0 4 0 1 16 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_0) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_p_0 (by norm_num))
    (dm_7 (1 : ℝ)) (dm_31 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_5 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 5)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 12
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 20 :=
  colEngine23 0 5 4 1 20 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_4) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_m_1 (by norm_num))
    (dm_12 (1 : ℝ)) (dm_20 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_6 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 6)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 15
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 23 :=
  colEngine23 0 6 8 1 24 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_8) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_m_0 (by norm_num))
    (dm_15 (1 : ℝ)) (dm_23 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_7 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 7)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 4
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 28 :=
  colEngine23 0 7 12 1 28 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_12) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_m_1 (by norm_num))
    (dm_4 (1 : ℝ)) (dm_28 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_8 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 8)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 14
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 22 :=
  colEngine23 1 0 1 0 1 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_1) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_m_2 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_m_2 (by norm_num))
    (dm_14 (1 : ℝ)) (dm_22 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_9 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 9)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 5
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 29 :=
  colEngine23 1 1 5 0 5 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_5) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_m_3 (by norm_num))
    (dm_5 (1 : ℝ)) (dm_29 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_10 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 10)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 6
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 30 :=
  colEngine23 1 2 9 0 9 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_9) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_m_2 (by norm_num))
    (dm_6 (1 : ℝ)) (dm_30 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_11 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 11)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 13
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 21 :=
  colEngine23 1 3 13 0 13 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_13) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_p_3 (by norm_num))
    (dm_13 (1 : ℝ)) (dm_21 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_12 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 12)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 9
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 17 :=
  colEngine23 1 4 1 1 17 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_1) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_m_2 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_m_2 (by norm_num))
    (dm_9 (1 : ℝ)) (dm_17 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_13 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 13)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 2
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 26 :=
  colEngine23 1 5 5 1 21 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_5) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_m_3 (by norm_num))
    (dm_2 (1 : ℝ)) (dm_26 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_14 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 14)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 1
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 25 :=
  colEngine23 1 6 9 1 25 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_9) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_m_2 (by norm_num))
    (dm_1 (1 : ℝ)) (dm_25 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_15 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 15)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 10
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 18 :=
  colEngine23 1 7 13 1 29 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_13) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_p_3 (by norm_num))
    (dm_10 (1 : ℝ)) (dm_18 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_16 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 16)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 13
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 21 :=
  colEngine23 2 0 2 0 2 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_2) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_m_3 (by norm_num))
    (dm_13 (1 : ℝ)) (dm_21 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_17 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 17)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 6
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 30 :=
  colEngine23 2 1 6 0 6 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_6) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_p_2 (by norm_num))
    (dm_6 (1 : ℝ)) (dm_30 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_18 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 18)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 5
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 29 :=
  colEngine23 2 2 10 0 10 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_10) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_p_3 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_0 (d3_5 (1 : ℝ)) sb_m_3 (by norm_num))
    (dm_5 (1 : ℝ)) (dm_29 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_19 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 19)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 14
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 22 :=
  colEngine23 2 3 14 0 14 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_14) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_2_0 (d3_6 (1 : ℝ)) sb_m_2 (by norm_num))
    (dm_14 (1 : ℝ)) (dm_22 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_20 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 20)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 10
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 18 :=
  colEngine23 2 4 2 1 18 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_2) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_m_3 (by norm_num))
    (dm_10 (1 : ℝ)) (dm_18 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_21 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 21)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 1
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 25 :=
  colEngine23 2 5 6 1 22 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_6) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_p_2 (by norm_num))
    (dm_1 (1 : ℝ)) (dm_25 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_22 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 22)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 2
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 26 :=
  colEngine23 2 6 10 1 26 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_10) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_p_3 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_3_1 (d3_2 (1 : ℝ)) sb_m_3 (by norm_num))
    (dm_2 (1 : ℝ)) (dm_26 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_23 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 23)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 9
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 17 :=
  colEngine23 2 7 14 1 30 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_14) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_2_1 (d3_1 (1 : ℝ)) sb_m_2 (by norm_num))
    (dm_9 (1 : ℝ)) (dm_17 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_24 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 24)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 3
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 27 :=
  colEngine23 3 0 3 0 3 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_3) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_p_1 (by norm_num))
    (dm_3 (1 : ℝ)) (dm_27 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_25 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 25)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 8
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 16 :=
  colEngine23 3 1 7 0 7 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_7) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_p_0 (by norm_num))
    (dm_8 (1 : ℝ)) (dm_16 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_26 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 26)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 11
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 19 :=
  colEngine23 3 2 11 0 11 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_11) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_1_0 (d3_3 (1 : ℝ)) sb_m_1 (by norm_num))
    (dm_11 (1 : ℝ)) (dm_19 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_27 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 27)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 24 :=
  colEngine23 3 3 15 0 15 (by norm_num) (by norm_num) (tb1z (-1 : ℝ)) (hmem_tone (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_15) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_m_0 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_0 (d3_0 (1 : ℝ)) sb_p_0 (by norm_num))
    (dm_0 (1 : ℝ)) (dm_24 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_28 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 28)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 4
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 28 :=
  colEngine23 3 4 3 1 19 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_3) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_p_1 (by norm_num))
    (dm_4 (1 : ℝ)) (dm_28 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_29 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 29)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 15
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 23 :=
  colEngine23 3 5 7 1 23 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_7) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_p_0 (by norm_num))
    (dm_15 (1 : ℝ)) (dm_23 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_30 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 30)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 12
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 20 :=
  colEngine23 3 6 11 1 27 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact nqv4_11) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (1 : ℝ) (-1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_one (-1 : ℝ) (1 : ℝ) val41_1_1 (d3_4 (1 : ℝ)) sb_m_1 (by norm_num))
    (dm_12 (1 : ℝ)) (dm_20 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col23_31 :
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) 31)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 7
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 31 :=
  colEngine23 3 7 15 1 31 (by norm_num) (by norm_num) (tb1g (-1 : ℝ)) (mem_q1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact nqv4_15) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_one (-1 : ℝ) (-1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_m_0 (by norm_num))
    (fG realFuse_four_one (1 : ℝ) (1 : ℝ) val41_0_1 (d3_7 (1 : ℝ)) sb_p_0 (by norm_num))
    (dm_7 (1 : ℝ)) (dm_31 (1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


set_option maxHeartbeats 16000000 in
private theorem hcol23 : ∀ c : Fin 32,
    realFuse_two_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) c)
      = (![1, -1, 1, 1, 1, -1, -1, -1, -1, -1, 1, -1, -1, -1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1] c : ℝ)
          • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 (![0, 11, 8, 3, 7, 12, 15, 4, 14, 5, 6, 13, 9, 2, 1, 10, 13, 6, 5, 14, 10, 1, 2, 9, 3, 8, 11, 0, 4, 15, 12, 7] c)
        + (![1, -1, -1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1] c : ℝ)
          • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1 (![24, 19, 16, 27, 31, 20, 23, 28, 22, 29, 30, 21, 17, 26, 25, 18, 21, 30, 29, 22, 18, 25, 26, 17, 27, 16, 19, 24, 28, 23, 20, 31] c) := by
  intro c
  fin_cases c
  · exact col23_0
  · exact col23_1
  · exact col23_2
  · exact col23_3
  · exact col23_4
  · exact col23_5
  · exact col23_6
  · exact col23_7
  · exact col23_8
  · exact col23_9
  · exact col23_10
  · exact col23_11
  · exact col23_12
  · exact col23_13
  · exact col23_14
  · exact col23_15
  · exact col23_16
  · exact col23_17
  · exact col23_18
  · exact col23_19
  · exact col23_20
  · exact col23_21
  · exact col23_22
  · exact col23_23
  · exact col23_24
  · exact col23_25
  · exact col23_26
  · exact col23_27
  · exact col23_28
  · exact col23_29
  · exact col23_30
  · exact col23_31


set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- **Deliverable `(2,3)`**: the `ε = -1` wrap past the Bott floor, with the `M_{1|1}(ℍ) ᵍ⊗ Cl_{0,1}` ampliation tail. -/
theorem realFuseMatrix_2_3 :
    realFuseMatrix 2 3
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
           0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by
  have key : ∀ i j : Fin 32,
      ((matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 1).repr
          (realFuse_two_three.toAlgEquiv
            (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 3)
              (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 3) j))) i
        = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
             0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
             0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
             1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : Matrix (Fin 32) (Fin 32) ℝ) i j := by
    intro i j
    rw [hcol23 j, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, Basis.repr_self_apply,
      Basis.repr_self_apply, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  refine Matrix.ext fun i j => ?_
  rw [realFuseMatrix_apply]
  exact key i j


set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- The `!![…]` deliverable of `(2,3)`, in the packed decoder form that
`RealFuseSpecTranspose` consumes. -/
private theorem bridge_2_3 : ∀ (i j : Fin 32),
    realFuseMatrix 2 3 i j = fuseLitFwd_2_3 i j := by
  have h := realFuseMatrix_2_3
  intro i j
  rw [h]
  show (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : Matrix (Fin 32) (Fin 32) ℝ) i j = _
  fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- **Deliverable `(3,2)`**: the Koszul transpose of `(2,3)`,
discharged from the forward spec through `RealFuseSpecTranspose`. -/
theorem realFuseMatrix_3_2 : ∀ (i j : Fin 32),
    realFuseMatrix 3 2 i j = fuseLit_3_2 i j :=
  realFuseMatrix_3_2_of_forward bridge_2_3

/-! ### The `(5,6)` branch (`Cl_{3,0} ᵍ⊗ Cl_{2,0}`, `ε = +1`) -/

private theorem unfold56 (x : ((divisionTower (1 : ℝ) 3).gtensor (divisionTower (1 : ℝ) 2)).carrier) :
    realFuse_five_six.toAlgEquiv x
      = ((matrixSuperGtensor quatEvenSuper (divisionTower (1 : ℝ) 1) 1 1).trans
          ((realFuse_four_seven.matrixSuper 1 1).trans
            (matrixSuperComp (divisionTower (-1 : ℝ) 3) 1 1 1 0))).toAlgEquiv
          (((towerFourQuatSuper ℝ).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
            ((towerFuse (1 : ℝ) 4 1).symm.toAlgEquiv
              ((towerFuse (1 : ℝ) 3 2).toAlgEquiv x))) := rfl


private theorem split56 (i : Fin 8) (j : Fin 4) (u : Fin 16) (v : Fin 2)
    (k : Fin 32) (h1 : (k : ℕ) = (i : ℕ) + 8 * (j : ℕ))
    (h2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ)) :
    (towerFuse (1 : ℝ) 4 1).symm.toAlgEquiv
        ((towerFuse (1 : ℝ) 3 2).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
            (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
            (towerBasis (1 : ℝ) 3 i) (towerBasis (1 : ℝ) 2 j)))
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 4).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (1 : ℝ) 4 u) (towerBasis (1 : ℝ) 1 v) := by
  rw [tfuseK (1 : ℝ) 3 2 i j k h1]
  exact tfuseKsymm (1 : ℝ) 4 1 u v k h2


private theorem colEngine56 (i : Fin 8) (j : Fin 4) (u : Fin 16) (v : Fin 2)
    (k : Fin 32) (hk1 : (k : ℕ) = (i : ℕ) + 8 * (j : ℕ))
    (hk2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ))
    {jw : ZMod 2} {w : (divisionTower (1 : ℝ) 1).carrier}
    (hwv : towerBasis (1 : ℝ) 1 v = w)
    (hw : w ∈ (divisionTower (1 : ℝ) 1).grading jw)
    (r1 c1 r2 c2 : Fin 1 ⊕ Fin 1) {qa qb : ℍ[ℝ]}
    (hcert : (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 u)
        = Matrix.single r1 c1 qa + Matrix.single r2 c2 qb)
    (ta tb : ℝ) {ea eb : Fin 8}
    (hFa : realFuse_four_seven.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ qa w)
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
              (ta • towerBasis (-1 : ℝ) 3 ea))
    (hFb : realFuse_four_seven.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ qb w)
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
              (tb • towerBasis (-1 : ℝ) 3 eb))
    {κ1 κ2 : ℝ} {I1 I2 : Fin 32}
    (hI1 : matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 I1
        = Matrix.single (collapseIndexEquiv 1 1 1 0 (r1, Sum.inl 0))
            (collapseIndexEquiv 1 1 1 0 (c1, Sum.inl 0)) (towerBasis (-1 : ℝ) 3 ea))
    (hI2 : matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 I2
        = Matrix.single (collapseIndexEquiv 1 1 1 0 (r2, Sum.inl 0))
            (collapseIndexEquiv 1 1 1 0 (c2, Sum.inl 0)) (towerBasis (-1 : ℝ) 3 eb))
    (hκ1 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb = κ2) :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) (finProdFinEquiv (i, j)))
      = κ1 • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 I1
        + κ2 • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 I2 := by
  refine (congrArg (fun z => realFuse_five_six.toAlgEquiv z)
      (gtensorBasis_apply_pair (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) i j)).trans ?_
  refine (unfold56 _).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 1) 1 1).trans
        ((realFuse_four_seven.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 3) 1 1 1 0))).toAlgEquiv
      (((towerFourQuatSuper ℝ).gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv z))
      (split56 i j u v k hk1 hk2)).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 1) 1 1).trans
        ((realFuse_four_seven.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 3) 1 1 1 0))).toAlgEquiv z)
      (SuperAlgEquiv.gtensorCongr_tmul (towerFourQuatSuper ℝ)
        (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))
        (towerBasis (1 : ℝ) 4 u) (towerBasis (1 : ℝ) 1 v))).trans ?_
  have e3 : GradedTensorProduct.tmul
        (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
        ((towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 u))
        ((SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1)).toAlgEquiv
          (towerBasis (1 : ℝ) 1 v))
      = GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (Matrix.single r1 c1 qa) w
        + GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (Matrix.single r2 c2 qb) w := by
    rw [superRefl_apply, hwv, hcert]
    exact add_gtmul (matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
      (divisionTower (1 : ℝ) 1).grading _ _ _
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 1) 1 1).trans
        ((realFuse_four_seven.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 3) 1 1 1 0))).toAlgEquiv z) e3).trans ?_
  refine (map_add ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 1) 1 1).trans
        ((realFuse_four_seven.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 3) 1 1 1 0))).toAlgEquiv _ _).trans ?_
  exact congrArg₂ (fun x y => x + y)
    (termG realFuse_four_seven hw r1 c1 hFa hI1 hκ1) (termG realFuse_four_seven hw r2 c2 hFb hI2 hκ2)


private theorem col56_0 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 0)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 24 :=
  colEngine56 0 0 0 0 0 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_0) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_p_0 (by norm_num))
    (dm_0 (-1 : ℝ)) (dm_24 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_1 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 1)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 13
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 21 :=
  colEngine56 0 1 8 0 8 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_8) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_p_3 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_m_3 (by norm_num))
    (dm_13 (-1 : ℝ)) (dm_21 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_2 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 2)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 7
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 31 :=
  colEngine56 0 2 0 1 16 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_0) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_p_0 (by norm_num))
    (dm_7 (-1 : ℝ)) (dm_31 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_3 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 3)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 10
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 18 :=
  colEngine56 0 3 8 1 24 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_8) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_p_3 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_m_3 (by norm_num))
    (dm_10 (-1 : ℝ)) (dm_18 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_4 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 4)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 8
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 16 :=
  colEngine56 1 0 1 0 1 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_1) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_p_0 (by norm_num))
    (dm_8 (-1 : ℝ)) (dm_16 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_5 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 5)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 5
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 29 :=
  colEngine56 1 1 9 0 9 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_9) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_p_3 (by norm_num))
    (dm_5 (-1 : ℝ)) (dm_29 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_6 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 6)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 15
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 23 :=
  colEngine56 1 2 1 1 17 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_1) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_p_0 (by norm_num))
    (dm_15 (-1 : ℝ)) (dm_23 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_7 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 7)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 2
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 26 :=
  colEngine56 1 3 9 1 25 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_9) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_p_3 (by norm_num))
    (dm_2 (-1 : ℝ)) (dm_26 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_8 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 8)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 11
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 19 :=
  colEngine56 2 0 2 0 2 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_2) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_m_1 (by norm_num))
    (dm_11 (-1 : ℝ)) (dm_19 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_9 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 9)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 6
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 30 :=
  colEngine56 2 1 10 0 10 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_10) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_p_2 (by norm_num))
    (dm_6 (-1 : ℝ)) (dm_30 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_10 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 10)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 12
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 20 :=
  colEngine56 2 2 2 1 18 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_2) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_p_1 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_m_1 (by norm_num))
    (dm_12 (-1 : ℝ)) (dm_20 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_11 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 11)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 1
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 25 :=
  colEngine56 2 3 10 1 26 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_10) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_p_2 (by norm_num))
    (dm_1 (-1 : ℝ)) (dm_25 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_12 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 12)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 3
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 27 :=
  colEngine56 3 0 3 0 3 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_3) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_p_1 (by norm_num))
    (dm_3 (-1 : ℝ)) (dm_27 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_13 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 13)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 14
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 22 :=
  colEngine56 3 1 11 0 11 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_11) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_p_2 (by norm_num))
    (dm_14 (-1 : ℝ)) (dm_22 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_14 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 14)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 4
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 28 :=
  colEngine56 3 2 3 1 19 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_3) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_p_1 (by norm_num))
    (dm_4 (-1 : ℝ)) (dm_28 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_15 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 15)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 9
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 17 :=
  colEngine56 3 3 11 1 27 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_11) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_p_2 (by norm_num))
    (dm_9 (-1 : ℝ)) (dm_17 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_16 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 16)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 14
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 22 :=
  colEngine56 4 0 4 0 4 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_4) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_m_2 (by norm_num))
    (dm_14 (-1 : ℝ)) (dm_22 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_17 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 17)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 3
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 27 :=
  colEngine56 4 1 12 0 12 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_12) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_m_1 (by norm_num))
    (dm_3 (-1 : ℝ)) (dm_27 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_18 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 18)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 9
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 17 :=
  colEngine56 4 2 4 1 20 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_4) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_p_2 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_m_2 (by norm_num))
    (dm_9 (-1 : ℝ)) (dm_17 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_19 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 19)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 4
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 28 :=
  colEngine56 4 3 12 1 28 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_12) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_m_1 (by norm_num))
    (dm_4 (-1 : ℝ)) (dm_28 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_20 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 20)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 6
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 30 :=
  colEngine56 5 0 5 0 5 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_5) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_m_2 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_2_0 (d3_6 (-1 : ℝ)) sb_p_2 (by norm_num))
    (dm_6 (-1 : ℝ)) (dm_30 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_21 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 21)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 11
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 19 :=
  colEngine56 5 1 13 0 13 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_13) (-1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_1_0 (d3_3 (-1 : ℝ)) sb_m_1 (by norm_num))
    (dm_11 (-1 : ℝ)) (dm_19 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_22 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 22)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 1
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 25 :=
  colEngine56 5 2 5 1 21 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_5) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_m_2 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (-1 : ℝ) val47_2_1 (d3_1 (-1 : ℝ)) sb_p_2 (by norm_num))
    (dm_1 (-1 : ℝ)) (dm_25 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_23 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 23)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 12
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 20 :=
  colEngine56 5 3 13 1 29 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_13) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_m_1 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_1_1 (d3_4 (-1 : ℝ)) sb_m_1 (by norm_num))
    (dm_12 (-1 : ℝ)) (dm_20 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_24 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 24)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 5
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 29 :=
  colEngine56 6 0 6 0 6 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_6) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_m_3 (by norm_num))
    (dm_5 (-1 : ℝ)) (dm_29 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_25 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 25)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 8
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 16 :=
  colEngine56 6 1 14 0 14 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_14) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_m_0 (by norm_num))
    (dm_8 (-1 : ℝ)) (dm_16 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_26 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 26)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 2
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 26 :=
  colEngine56 6 2 6 1 22 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_6) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_m_3 (by norm_num))
    (dm_2 (-1 : ℝ)) (dm_26 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_27 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 27)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 15
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 23 :=
  colEngine56 6 3 14 1 30 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_14) (1 : ℝ) (-1 : ℝ)
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_p_0 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_m_0 (by norm_num))
    (dm_15 (-1 : ℝ)) (dm_23 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_28 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 28)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 13
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 21 :=
  colEngine56 7 0 7 0 7 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_7) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_0 (d3_5 (-1 : ℝ)) sb_m_3 (by norm_num))
    (dm_13 (-1 : ℝ)) (dm_21 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_29 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 29)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 24 :=
  colEngine56 7 1 15 0 15 (by norm_num) (by norm_num) (tb1z (1 : ℝ)) (hmem_tone (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_15) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_m_0 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_0 (d3_0 (-1 : ℝ)) sb_p_0 (by norm_num))
    (dm_0 (-1 : ℝ)) (dm_24 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_30 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 30)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 10
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 18 :=
  colEngine56 7 2 7 1 23 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (by exact qv4_7) (1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_m_3 (by norm_num))
    (fG realFuse_four_seven (-1 : ℝ) (1 : ℝ) val47_3_1 (d3_2 (-1 : ℝ)) sb_m_3 (by norm_num))
    (dm_10 (-1 : ℝ)) (dm_18 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


private theorem col56_31 :
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) 31)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 7
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 31 :=
  colEngine56 7 3 15 1 31 (by norm_num) (by norm_num) (tb1g (1 : ℝ)) (mem_q1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (by exact qv4_15) (-1 : ℝ) (1 : ℝ)
    (fG realFuse_four_seven (-1 : ℝ) (-1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_m_0 (by norm_num))
    (fG realFuse_four_seven (1 : ℝ) (1 : ℝ) val47_0_1 (d3_7 (-1 : ℝ)) sb_p_0 (by norm_num))
    (dm_7 (-1 : ℝ)) (dm_31 (-1 : ℝ)) (by simp [sumParity]) (by simp [sumParity])


set_option maxHeartbeats 16000000 in
private theorem hcol56 : ∀ c : Fin 32,
    realFuse_five_six.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) c)
      = (![1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, -1, -1, -1] c : ℝ)
          • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 (![0, 13, 7, 10, 8, 5, 15, 2, 11, 6, 12, 1, 3, 14, 4, 9, 14, 3, 9, 4, 6, 11, 1, 12, 5, 8, 2, 15, 13, 0, 10, 7] c)
        + (![1, 1, -1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1] c : ℝ)
          • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1 (![24, 21, 31, 18, 16, 29, 23, 26, 19, 30, 20, 25, 27, 22, 28, 17, 22, 27, 17, 28, 30, 19, 25, 20, 29, 16, 26, 23, 21, 24, 18, 31] c) := by
  intro c
  fin_cases c
  · exact col56_0
  · exact col56_1
  · exact col56_2
  · exact col56_3
  · exact col56_4
  · exact col56_5
  · exact col56_6
  · exact col56_7
  · exact col56_8
  · exact col56_9
  · exact col56_10
  · exact col56_11
  · exact col56_12
  · exact col56_13
  · exact col56_14
  · exact col56_15
  · exact col56_16
  · exact col56_17
  · exact col56_18
  · exact col56_19
  · exact col56_20
  · exact col56_21
  · exact col56_22
  · exact col56_23
  · exact col56_24
  · exact col56_25
  · exact col56_26
  · exact col56_27
  · exact col56_28
  · exact col56_29
  · exact col56_30
  · exact col56_31


set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- **Deliverable `(5,6)`**: the `ε = +1` wrap past the Bott floor, with the `M_{1|1}(ℍ) ᵍ⊗ Cl_{1,0}` ampliation tail. -/
theorem realFuseMatrix_5_6 :
    realFuseMatrix 5 6
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
           0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by
  have key : ∀ i j : Fin 32,
      ((matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 1).repr
          (realFuse_five_six.toAlgEquiv
            (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 2)
              (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 2) j))) i
        = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
             0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
             0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
             0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
             1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
             0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : Matrix (Fin 32) (Fin 32) ℝ) i j := by
    intro i j
    rw [hcol56 j, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, Basis.repr_self_apply,
      Basis.repr_self_apply, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  refine Matrix.ext fun i j => ?_
  rw [realFuseMatrix_apply]
  exact key i j


set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- The `!![…]` deliverable of `(5,6)`, in the packed decoder form that
`RealFuseSpecTranspose` consumes. -/
private theorem bridge_5_6 : ∀ (i j : Fin 32),
    realFuseMatrix 5 6 i j = fuseLitFwd_5_6 i j := by
  have h := realFuseMatrix_5_6
  intro i j
  rw [h]
  show (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : Matrix (Fin 32) (Fin 32) ℝ) i j = _
  fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- **Deliverable `(6,5)`**: the Koszul transpose of `(5,6)`,
discharged from the forward spec through `RealFuseSpecTranspose`. -/
theorem realFuseMatrix_6_5 : ∀ (i j : Fin 32),
    realFuseMatrix 6 5 i j = fuseLit_6_5 i j :=
  realFuseMatrix_6_5_of_forward bridge_5_6


end Superfusion

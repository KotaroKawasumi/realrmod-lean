/-
Superfusion / Gauge / RealFuseSpecQuat3

M15 semantic-bridge, **the closing file**: the last two forward corners
`(4,3)` and `(4,5)` (`32 × 32`, size `2|2`), and the two Koszul
transposes they release, `(3,4)` and `(5,4)`.  With these the value
pinning of the real fusion table is complete — **64 / 64**.

**Landed here** (kernel-checked; no proof holes, no kernel-reducing
tactics beyond `decide`, no new axioms — each depends only on `propext`,
`Classical.choice`, `Quot.sound`):

* `realFuseMatrix_4_3` — `ℍ ᵍ⊗ Cl_{0,3} ≅ M_{2|2}(Cl_{1,0})`,
* `realFuseMatrix_4_5` — `ℍ ᵍ⊗ Cl_{3,0} ≅ M_{2|2}(Cl_{0,1})`,
* `realFuseMatrix_3_4`, `realFuseMatrix_5_4` — the two Koszul transposes
  they release, discharged from `RealFuseSpecTranspose`'s conditional
  `…_of_forward` statements.

## Method: the doubly ampliated tail over a landed outer branch

`realFuse_four_three` (`RealFuse4`) is the six-stage composite

```
ℍ ᵍ⊗ T₃⁻ → ℍ ᵍ⊗ (T₂⁻ ᵍ⊗ T₁⁻) → (ℍ ᵍ⊗ T₂⁻) ᵍ⊗ T₁⁻
         → M_{1|1}(T₂⁺) ᵍ⊗ T₁⁻ → M_{1|1}(T₂⁺ ᵍ⊗ T₁⁻)
         → M_{1|1}(M_{1|1}(T₁⁺)) → M_{2|2}(T₁⁺)
```

and `realFuse_four_five` is the mirror, through `realFuse_four_six` and
`realFuse_two_seven`.  So the shape is exactly `RealFuseSpecWrap4`'s
doubly ampliated tail, except that the *outer* two-entry value is now a
landed `(4,·)` quaternion branch instead of a floor-`4` Bott
certificate, and the *inner* seed is a landed mixed pair.  Consequently:

* `termG2'` / `fG2'` are `RealFuseSpecWrap4`'s `termG2` / `fG2` with the
  left tensor factor made **generic** (there it is `quatEvenSuper`; here
  the ampliation tail runs over `realRep 6` / `realRep 2`).  Nothing in
  either proof was quaternion-specific — only `msg_single'`,
  `matrixSuperMap_single'`, `matrixSuperComp_single'`.
* `col2` is the `col2_of_matrix` that `RealFuseSpecQuat2`'s docstring
  listed as missing: a *landed* `realFuseMatrix` column with two nonzero
  entries, read back as a two-term value
  `E (bA j) = c₁ • bC I₁ + c₂ • bC I₂`, by `Basis.sum_repr` and
  `Finset.sum_eq_single`.  It supplies the sixteen inner seed values
  `w61_*` / `w27_*` straight off `realFuseMatrix_6_1` /
  `realFuseMatrix_2_7`, so the Koszul braiding of `(6,1)` is never
  re-derived — it is already inside the landed literal.
* the outer two-entry values are `RealFuseSpecWrap4`'s own `val42_*` /
  `val46_*`, re-shaped by `two_singles`.

Each of the `32` columns is therefore a **four**-term sum (two outer
entries × two inner entries), assembled by `colEngine43` / `colEngine45`
with `congrArg` only: no `rw` ever meets the `realRep`-versus-
`divisionTower` spelling mismatch, because the branch composite enters
through `unfold43` / `unfold45`, both `rfl`.

**The `32 × 32` closing step** follows `RealFuseSpecPeel3` and
`RealFuseSpecWrap4`: there is no `N²` tactic goal anywhere.  `entry43` /
`entry45` turn `realFuseMatrix a b i j` into a four-term sum generically
in `(i, j)` (one `realFuseMatrix_apply`, one instance of `hcol43` /
`hcol45`); `coefs43` / `coefs45` rewrite the four real sign vectors as
`fuseDecode ∘ kᵥ` for base-3 code vectors (one `fin_cases j`); and
`master43` / `master45` check, in `ℕ`, all `1024` points with a single
kernel `decide` — both the disjointness (the four target-index vectors
of a column are pairwise distinct) and the base-3 digit of the frozen
literal.

The packed literals `fuseRows_4_3` / `fuseRows_4_5` are verbatim from
`scripts/certgen/out/lean_literals/fuse_4_3.txt` / `fuse_4_5.txt`, and
agree entrywise with `scripts/certgen/fuse.py`'s `real_fuse(4,3)` /
`real_fuse(4,5)`.  `fwd43` / `fwd45` bridge them to
`RealFuseSpecTranspose`'s own `fuseLitFwd_4_3` / `fuseLitFwd_4_5`, whose
row tables are numerically identical.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 9 — closing).
-/
import Superfusion.Gauge.RealFuseSpecQuat2
import Superfusion.Gauge.RealFuseSpecWrap4
import Batteries.Tactic.OpenPrivate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Superfusion

open Module TensorProduct GradedTensorProduct Quaternion

open private superRefl_apply from Superfusion.Gauge.RealFuseSpecWrap

open private msg_single' matrixSuperMap_single' matrixSuperComp_single'
  from Superfusion.Gauge.RealFuseSpecWrap2

open private gtmul_smul_left single_smulG smul_dstG zsmul_dstS
  tfuseKsymm gtAssocSymm smul2 zsmul_add2 tb1m0 tb1m1
  fuseDecode_zero dmul dpick dpick_add
  dm2_0 dm2_1 dm2_2 dm2_3 dm2_4 dm2_5 dm2_6 dm2_7
  dm2_8 dm2_9 dm2_10 dm2_11 dm2_12 dm2_13 dm2_14 dm2_15
  val42_0_0 val42_0_1 val42_0_2 val42_0_3 val42_1_0 val42_1_1 val42_1_2
  val42_1_3 val42_2_0 val42_2_1 val42_2_2 val42_2_3 val42_3_0 val42_3_1
  val42_3_2 val42_3_3
  val46_0_0 val46_0_1 val46_0_2 val46_0_3 val46_1_0 val46_1_1 val46_1_2
  val46_1_3 val46_2_0 val46_2_1 val46_2_2 val46_2_3 val46_3_0 val46_3_1
  val46_3_2 val46_3_3
  from Superfusion.Gauge.RealFuseSpecWrap4

/-! ### Generic plumbing: a two-nonzero column of a landed matrix -/

/-- **The `col2_of_matrix` of `RealFuseSpecQuat2`'s to-do list.**  If the
`j`-th column of the matrix of `E` in the frames `bA` / `bC` is supported
on `{I₁, I₂}` with values `c₁`, `c₂`, then
`E (bA j) = c₁ • bC I₁ + c₂ • bC I₂`.  No `N²` goal: the hypothesis is
one indicator identity, discharged column by column. -/
private theorem col2 {A C : SuperAlgebra ℝ} {n k : ℕ}
    (bA : Basis (Fin n) ℝ A.carrier) (bC : Basis (Fin k) ℝ C.carrier)
    (E : SuperAlgEquiv A C) (j : Fin n) (I1 I2 : Fin k) (c1 c2 : ℝ)
    (h : ∀ i : Fin k,
        LinearMap.toMatrix bA bC E.toAlgEquiv.toLinearMap i j
          = (if i = I1 then c1 else 0) + (if i = I2 then c2 else 0)) :
    E.toAlgEquiv (bA j) = c1 • bC I1 + c2 • bC I2 := by
  have hsum : ∀ (I : Fin k) (c : ℝ),
      (∑ i : Fin k, (if i = I then c else 0) • bC i) = c • bC I := by
    intro I c
    rw [Finset.sum_eq_single I]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, zero_smul]
    · intro hI; exact absurd (Finset.mem_univ I) hI
  have hco : ∀ i : Fin k, (bC.repr (E.toAlgEquiv (bA j))) i
      = (if i = I1 then c1 else 0) + (if i = I2 then c2 else 0) := by
    intro i
    have hx : LinearMap.toMatrix bA bC E.toAlgEquiv.toLinearMap i j
        = (bC.repr (E.toAlgEquiv (bA j))) i := by
      rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply]
    exact hx.symm.trans (h i)
  refine (bC.sum_repr (E.toAlgEquiv (bA j))).symm.trans ?_
  refine (Finset.sum_congr rfl fun i _ => by rw [hco i]).trans ?_
  refine (Finset.sum_congr rfl fun i _ => add_smul _ _ _).trans ?_
  rw [Finset.sum_add_distrib, hsum, hsum]

/-- The tensor frame vector at a named flat index. -/
private theorem gb_at {A B : SuperAlgebra ℝ} {m n : ℕ}
    (bA : Basis (Fin m) ℝ A.carrier) (bB : Basis (Fin n) ℝ B.carrier)
    (i : Fin m) (jx : Fin n) (J : Fin (m * n))
    (h : (J : ℕ) = (jx : ℕ) + n * (i : ℕ)) :
    gtensorBasis bA bB J
      = GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ
          (bA i) (bB jx) := by
  have hJ : J = (⟨(jx : ℕ) + n * (i : ℕ), gtensorIndex_lt i jx⟩ : Fin (m * n)) :=
    Fin.ext h
  rw [hJ]
  exact gtensorBasis_apply bA bB i jx

/-- Two frame vectors, re-shaped as two single-entry matrices. -/
private theorem two_singles {T : SuperAlgebra ℝ} {k p q : ℕ}
    {bT : Basis (Fin k) ℝ T.carrier} {X : (T.matrixSuper p q).carrier}
    {t1 t2 : ℝ} {K1 K2 : Fin ((p + q) * (p + q) * k)}
    {ra ca rb cb : Fin p ⊕ Fin q} {e1 e2 : Fin k}
    (hX : X = t1 • matrixSuperBasis bT p q K1
        + t2 • matrixSuperBasis bT p q K2)
    (hd1 : matrixSuperBasis bT p q K1 = Matrix.single ra ca (bT e1))
    (hd2 : matrixSuperBasis bT p q K2 = Matrix.single rb cb (bT e2)) :
    X = Matrix.single ra ca (t1 • bT e1) + Matrix.single rb cb (t2 • bT e2) :=
  hX.trans (congrArg₂ (fun x y => x + y) (smul_dstG t1 hd1) (smul_dstG t2 hd2))

/-- `RealFuseSpecWrap4.fG2` with the left tensor factor generic: the seed
on a *scaled* left factor, two-entry version. -/
private theorem fG2' {A R T : SuperAlgebra ℝ}
    (F : SuperAlgEquiv (A.gtensor R) (T.matrixSuper 1 1))
    (σ t1' t2' : ℝ) {a q : A.carrier} {t1 t2 : ℝ}
    {bT : Basis (Fin 2) ℝ T.carrier} {K1 K2 : Fin 8} {w : R.carrier}
    {ra ca rb cb : Fin 1 ⊕ Fin 1} {e1 e2 : Fin 2}
    (hb : F.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := R.grading) ℝ a w)
          = t1 • matrixSuperBasis bT 1 1 K1 + t2 • matrixSuperBasis bT 1 1 K2)
    (hd1 : matrixSuperBasis bT 1 1 K1 = Matrix.single ra ca (bT e1))
    (hd2 : matrixSuperBasis bT 1 1 K2 = Matrix.single rb cb (bT e2))
    (hq : σ • a = q) (ht1 : σ * t1 = t1') (ht2 : σ * t2 = t2') :
    F.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := R.grading) ℝ q w)
      = Matrix.single ra ca (t1' • bT e1)
        + Matrix.single rb cb (t2' • bT e2) := by
  have h0 : GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := R.grading) ℝ q w
      = σ • GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := R.grading) ℝ a w := by
    rw [← hq]
    exact gtmul_smul_left A.grading R.grading σ a w
  refine (congrArg (fun z => F.toAlgEquiv z) h0).trans ?_
  refine (map_smul F.toAlgEquiv σ _).trans ?_
  refine (congrArg (fun z => σ • z) hb).trans ?_
  refine (smul2 σ t1 t2 t1' t2' _ _ ht1 ht2).trans ?_
  exact congrArg₂ (fun x y => x + y) (smul_dstG t1' hd1) (smul_dstG t2' hd2)

/-- `RealFuseSpecWrap4.termG2` with the left tensor factor generic: the
doubly ampliated tail `matrixSuperGtensor ; F.matrixSuper ;
matrixSuperComp` on one entry of the outer certificate. -/
private theorem termG2' {A R T : SuperAlgebra ℝ}
    (F : SuperAlgEquiv (A.gtensor R) (T.matrixSuper 1 1))
    {jw : ZMod 2} {w : R.carrier} (hw : w ∈ R.grading jw)
    (r c : Fin 1 ⊕ Fin 1) {q : A.carrier} {t1 t2 : ℝ}
    {bT : Basis (Fin 2) ℝ T.carrier} {e1 e2 : Fin 2}
    {ra ca rb cb : Fin 1 ⊕ Fin 1}
    (hF : F.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := R.grading) ℝ q w)
          = Matrix.single ra ca (t1 • bT e1)
            + Matrix.single rb cb (t2 • bT e2))
    {κ1 κ2 : ℝ} {I1 I2 : Fin 32}
    (hI1 : matrixSuperBasis bT 2 2 I1
          = Matrix.single (collapseIndexEquiv 1 1 1 1 (r, ra))
              (collapseIndexEquiv 1 1 1 1 (c, ca)) (bT e1))
    (hI2 : matrixSuperBasis bT 2 2 I2
          = Matrix.single (collapseIndexEquiv 1 1 1 1 (r, rb))
              (collapseIndexEquiv 1 1 1 1 (c, cb)) (bT e2))
    (hκ1 : (((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) : ℝ) * t1 = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) : ℝ) * t2 = κ2) :
    ((matrixSuperGtensor A R 1 1).trans
        ((F.matrixSuper 1 1).trans (matrixSuperComp T 1 1 1 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) A.grading)
          (ℬ := R.grading) ℝ (Matrix.single r c q) w)
      = κ1 • matrixSuperBasis bT 2 2 I1 + κ2 • matrixSuperBasis bT 2 2 I2 := by
  have h1 := msg_single' A R 1 1 r c q hw
  have h2 : (F.matrixSuper 1 1).toAlgEquiv
        (Matrix.single r c
          (GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := R.grading) ℝ q w))
      = Matrix.single r c (Matrix.single ra ca (t1 • bT e1))
        + Matrix.single r c (Matrix.single rb cb (t2 • bT e2)) :=
    (matrixSuperMap_single' F 1 1 r c _).trans
      ((congrArg (fun z => Matrix.single r c z) hF).trans
        (Matrix.single_add r c _ _))
  have h3a := matrixSuperComp_single' T 1 1 1 1 r c ra ca (t1 • bT e1)
  have h3b := matrixSuperComp_single' T 1 1 1 1 r c rb cb (t2 • bT e2)
  have e1' : ((matrixSuperGtensor A R 1 1).trans
        ((F.matrixSuper 1 1).trans (matrixSuperComp T 1 1 1 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) A.grading)
          (ℬ := R.grading) ℝ (Matrix.single r c q) w)
      = (matrixSuperComp T 1 1 1 1).toAlgEquiv
          ((F.matrixSuper 1 1).toAlgEquiv
            ((matrixSuperGtensor A R 1 1).toAlgEquiv
              (GradedTensorProduct.tmul
                (𝒜 := matrixGradingA (sumParity 1 1) A.grading)
                (ℬ := R.grading) ℝ (Matrix.single r c q) w))) := rfl
  refine e1'.trans ?_
  refine (congrArg (fun z => (matrixSuperComp T 1 1 1 1).toAlgEquiv
      ((F.matrixSuper 1 1).toAlgEquiv z)) h1).trans ?_
  refine (congrArg (matrixSuperComp T 1 1 1 1).toAlgEquiv
      ((map_zsmul (F.matrixSuper 1 1).toAlgEquiv _ _).trans
        (congrArg (fun z => ((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) • z)
          h2))).trans ?_
  refine ((map_zsmul (matrixSuperComp T 1 1 1 1).toAlgEquiv _ _).trans
      (congrArg (fun z => ((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) • z)
        ((map_add (matrixSuperComp T 1 1 1 1).toAlgEquiv _ _).trans
          (congrArg₂ (fun x y => x + y) h3a h3b)))).trans ?_
  refine (zsmul_add2 _ _ _).trans ?_
  rw [smul_dstG κ1 hI1, smul_dstG κ2 hI2]
  exact congrArg₂ (fun x y => x + y)
    (zsmul_dstS _ _ _ t1 _ hκ1) (zsmul_dstS _ _ _ t2 _ hκ2)

/-! ### The `1|1` frame of a floor-`1` tower (8 entries) -/

private theorem dm1_0 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 0
    = Matrix.single (Sum.inl 0) (Sum.inl 0) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 0

private theorem dm1_1 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 1
    = Matrix.single (Sum.inl 0) (Sum.inl 0) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 1

private theorem dm1_2 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 2
    = Matrix.single (Sum.inl 0) (Sum.inr 0) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 0

private theorem dm1_3 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 3
    = Matrix.single (Sum.inl 0) (Sum.inr 0) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 1

private theorem dm1_4 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 4
    = Matrix.single (Sum.inr 0) (Sum.inl 0) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 0

private theorem dm1_5 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 5
    = Matrix.single (Sum.inr 0) (Sum.inl 0) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 1

private theorem dm1_6 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 6
    = Matrix.single (Sum.inr 0) (Sum.inr 0) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 0

private theorem dm1_7 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 1 1 7
    = Matrix.single (Sum.inr 0) (Sum.inr 0) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 1

/-! ### The `2|2` frame of a floor-`1` tower (32 entries) -/

private theorem dp_0 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 0
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_1 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 1
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_2 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 2
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_3 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 3
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 1

private theorem dp_4 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 4
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_5 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 5
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_6 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 6
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_7 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 7
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 1

private theorem dp_8 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 8
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_9 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 9
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_10 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 10
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_11 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 11
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 1

private theorem dp_12 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 12
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_13 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 13
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_14 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 14
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_15 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 15
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 1

private theorem dp_16 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 16
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_17 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 17
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_18 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 18
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_19 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 19
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 1

private theorem dp_20 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 20
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_21 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 21
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_22 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 22
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_23 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 23
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 1

private theorem dp_24 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 24
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_25 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 25
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_26 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 26
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_27 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 27
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1 : Fin 2 ⊕ Fin 2) 1

private theorem dp_28 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 28
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 0

private theorem dp_29 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 29
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) 1

private theorem dp_30 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 30
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 0

private theorem dp_31 (ε : ℝ) : matrixSuperBasis (towerBasis ε 1) 2 2 31
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) (towerBasis ε 1 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 1) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1 : Fin 2 ⊕ Fin 2) 1

/-! ### The eight `(6,1)` inner seed values, read off the
landed literal `realFuseMatrix_6_1` by `col2` -/

private theorem w61gen (ea : Fin 4) (v2 : Fin 2) (j : Fin 8)
    (hj : (j : ℕ) = (v2 : ℕ) + 2 * (ea : ℕ))
    (I1 I2 : Fin 8) (c1 c2 : ℝ)
    (h : ∀ i : Fin 8, realFuseMatrix 6 1 i j
        = (if i = I1 then c1 else 0) + (if i = I2 then c2 else 0)) :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 ea) (towerBasis (-1 : ℝ) 1 v2))
      = c1 • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 I1
        + c2 • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 I2 :=
  (congrArg realFuse_six_one.toAlgEquiv
      (gb_at (towerBasis (1 : ℝ) 2) (towerBasis (-1 : ℝ) 1)
        ea v2 j hj).symm).trans
    (col2 _ _ realFuse_six_one j I1 I2 c1 c2 h)

private theorem w61_0_0 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 0) (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 6 :=
  w61gen 0 0 0 rfl 0 6 1 1
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

private theorem w61_0_1 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 0) (towerBasis (-1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 2
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 4 :=
  w61gen 0 1 1 rfl 2 4 1 (-1)
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

private theorem w61_1_0 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 1) (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 1
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 7 :=
  w61gen 1 0 2 rfl 1 7 1 (-1)
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

private theorem w61_1_1 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 1) (towerBasis (-1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 3
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 5 :=
  w61gen 1 1 3 rfl 3 5 1 1
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

private theorem w61_2_0 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 2) (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 2
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 4 :=
  w61gen 2 0 4 rfl 2 4 1 1
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

private theorem w61_2_1 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 2) (towerBasis (-1 : ℝ) 1 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 6 :=
  w61gen 2 1 5 rfl 0 6 (-1) 1
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

private theorem w61_3_0 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 3) (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 3
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 5 :=
  w61gen 3 0 6 rfl 3 5 1 (-1)
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

private theorem w61_3_1 :
    realFuse_six_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 2 3) (towerBasis (-1 : ℝ) 1 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 1
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 1 1 7 :=
  w61gen 3 1 7 rfl 1 7 (-1) (-1)
    (by intro i; rw [realFuseMatrix_6_1]; fin_cases i <;> simp)

/-! ### The eight `(2,7)` inner seed values, read off the
landed literal `realFuseMatrix_2_7` by `col2` -/

private theorem w27gen (ea : Fin 4) (v2 : Fin 2) (j : Fin 8)
    (hj : (j : ℕ) = (v2 : ℕ) + 2 * (ea : ℕ))
    (I1 I2 : Fin 8) (c1 c2 : ℝ)
    (h : ∀ i : Fin 8, realFuseMatrix 2 7 i j
        = (if i = I1 then c1 else 0) + (if i = I2 then c2 else 0)) :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 ea) (towerBasis (1 : ℝ) 1 v2))
      = c1 • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 I1
        + c2 • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 I2 :=
  (congrArg realFuse_two_seven.toAlgEquiv
      (gb_at (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1)
        ea v2 j hj).symm).trans
    (col2 _ _ realFuse_two_seven j I1 I2 c1 c2 h)

private theorem w27_0_0 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 6 :=
  w27gen 0 0 0 rfl 0 6 1 1
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

private theorem w27_0_1 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 2
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 4 :=
  w27gen 0 1 1 rfl 2 4 1 1
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

private theorem w27_1_0 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 1
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 7 :=
  w27gen 1 0 2 rfl 1 7 1 (-1)
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

private theorem w27_1_1 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 3
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 5 :=
  w27gen 1 1 3 rfl 3 5 1 (-1)
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

private theorem w27_2_0 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 2
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 4 :=
  w27gen 2 0 4 rfl 2 4 1 (-1)
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

private theorem w27_2_1 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 0
        + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 6 :=
  w27gen 2 1 5 rfl 0 6 1 (-1)
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

private theorem w27_3_0 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 3
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 5 :=
  w27gen 3 0 6 rfl 3 5 1 1
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

private theorem w27_3_1 :
    realFuse_two_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 1
        + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 1 1 7 :=
  w27gen 3 1 7 rfl 1 7 1 1
    (by intro i; rw [realFuseMatrix_2_7]; fin_cases i <;> simp)

/-! ### The `(4,3)` branch -/

private theorem unfold43
    (x : (quatEvenSuper.gtensor (divisionTower (-1 : ℝ) 3)).carrier) :
    realFuse_four_three.toAlgEquiv x
      = ((matrixSuperGtensor (realRep 6) (realRep 1) 1 1).trans
        ((realFuse_six_one.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 7) 1 1 1 1))).toAlgEquiv
          ((realFuse_four_two.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
            ((gtensorAssoc quatEvenSuper (divisionTower (-1 : ℝ) 2)
                (divisionTower (-1 : ℝ) 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                  (towerFuse (-1 : ℝ) 2 1).symm).toAlgEquiv x))) := rfl

private theorem colEngine43 (e : Fin 4) (v1 : Fin 4) (v2 : Fin 2)
    (v : Fin 8) (hv : (v : ℕ) = (v1 : ℕ) + 2 ^ 2 * (v2 : ℕ))
    {jw : ZMod 2} {w : (realRep 1).carrier}
    (hwv : towerBasis (-1 : ℝ) 1 v2 = w)
    (hw : w ∈ (realRep 1).grading jw)
    (r1 c1 r2 c2 : Fin 1 ⊕ Fin 1) {qa qb : (realRep 6).carrier}
    (hcert : realFuse_four_two.toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis e)
            (towerBasis (-1 : ℝ) 2 v1))
        = Matrix.single r1 c1 qa + Matrix.single r2 c2 qb)
    {ta1 ta2 tb1 tb2 : ℝ} {ea1 ea2 eb1 eb2 : Fin 2}
    {raa caa rab cab rba cba rbb cbb : Fin 1 ⊕ Fin 1}
    (hFa : realFuse_six_one.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
              (ℬ := (realRep 1).grading) ℝ qa w)
          = Matrix.single raa caa (ta1 • towerBasis (1 : ℝ) 1 ea1)
            + Matrix.single rab cab (ta2 • towerBasis (1 : ℝ) 1 ea2))
    (hFb : realFuse_six_one.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
              (ℬ := (realRep 1).grading) ℝ qb w)
          = Matrix.single rba cba (tb1 • towerBasis (1 : ℝ) 1 eb1)
            + Matrix.single rbb cbb (tb2 • towerBasis (1 : ℝ) 1 eb2))
    {κ1 κ2 κ3 κ4 : ℝ} {I1 I2 I3 I4 : Fin 32}
    (hI1 : matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I1
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, raa))
            (collapseIndexEquiv 1 1 1 1 (c1, caa))
            (towerBasis (1 : ℝ) 1 ea1))
    (hI2 : matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I2
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, rab))
            (collapseIndexEquiv 1 1 1 1 (c1, cab))
            (towerBasis (1 : ℝ) 1 ea2))
    (hI3 : matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I3
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rba))
            (collapseIndexEquiv 1 1 1 1 (c2, cba))
            (towerBasis (1 : ℝ) 1 eb1))
    (hI4 : matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I4
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rbb))
            (collapseIndexEquiv 1 1 1 1 (c2, cbb))
            (towerBasis (1 : ℝ) 1 eb2))
    (hκ1 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta1 = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta2 = κ2)
    (hκ3 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb1 = κ3)
    (hκ4 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb2 = κ4) :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3)
          (finProdFinEquiv (e, v)))
      = (κ1 • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I1
          + κ2 • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I2)
        + (κ3 • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I3
          + κ4 • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 I4) := by
  have hA : ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
        (towerFuse (-1 : ℝ) 2 1).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (quatBasis e)
          (towerBasis (-1 : ℝ) 3 v))
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((divisionTower (-1 : ℝ) 2).gtensor
            (divisionTower (-1 : ℝ) 1)).grading) ℝ (quatBasis e)
          (GradedTensorProduct.tmul
            (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
            (towerBasis (-1 : ℝ) 2 v1)
            (towerBasis (-1 : ℝ) 1 v2)) := by
    refine (SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl quatEvenSuper)
      (towerFuse (-1 : ℝ) 2 1).symm (quatBasis e)
      (towerBasis (-1 : ℝ) 3 v)).trans ?_
    rw [superRefl_apply]
    exact congrArg
      (fun z => GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := ((divisionTower (-1 : ℝ) 2).gtensor
          (divisionTower (-1 : ℝ) 1)).grading) ℝ (quatBasis e) z)
      (tfuseKsymm (-1 : ℝ) 2 1 v1 v2 v hv)
  have e3 : (realFuse_four_two.gtensorCongr
        (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (quatEvenSuper.gtensor (divisionTower (-1 : ℝ) 2)).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis e)
            (towerBasis (-1 : ℝ) 2 v1))
          (towerBasis (-1 : ℝ) 1 v2))
      = GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ (Matrix.single r1 c1 qa) w
        + GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ (Matrix.single r2 c2 qb) w := by
    refine (SuperAlgEquiv.gtensorCongr_tmul realFuse_four_two
      (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1)) _ _).trans ?_
    rw [superRefl_apply, hwv, hcert]
    exact add_gtmul (matrixGradingA (sumParity 1 1) (realRep 6).grading)
      (realRep 1).grading _ _ _
  refine (congrArg (fun z => realFuse_four_three.toAlgEquiv z)
      (gtensorBasis_apply_pair quatBasis (towerBasis (-1 : ℝ) 3)
        e v)).trans ?_
  refine (unfold43 _).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor (realRep 6) (realRep 1) 1 1).trans
        ((realFuse_six_one.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 7) 1 1 1 1))).toAlgEquiv
      ((realFuse_four_two.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
        ((gtensorAssoc quatEvenSuper (divisionTower (-1 : ℝ) 2)
            (divisionTower (-1 : ℝ) 1)).symm.toAlgEquiv z))) hA).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor (realRep 6) (realRep 1) 1 1).trans
        ((realFuse_six_one.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 7) 1 1 1 1))).toAlgEquiv
      ((realFuse_four_two.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv z))
      (gtAssocSymm quatEvenSuper (divisionTower (-1 : ℝ) 2)
        (divisionTower (-1 : ℝ) 1) (quatBasis e)
        (towerBasis (-1 : ℝ) 2 v1)
        (towerBasis (-1 : ℝ) 1 v2))).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor (realRep 6) (realRep 1) 1 1).trans
        ((realFuse_six_one.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 7) 1 1 1 1))).toAlgEquiv z) e3).trans ?_
  refine (map_add ((matrixSuperGtensor (realRep 6) (realRep 1) 1 1).trans
        ((realFuse_six_one.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 7) 1 1 1 1))).toAlgEquiv _ _).trans ?_
  exact congrArg₂ (fun x y => x + y)
    (termG2' realFuse_six_one hw r1 c1 hFa hI1 hI2 hκ1 hκ2)
    (termG2' realFuse_six_one hw r2 c2 hFb hI3 hI4 hκ3 hκ4)

/-! ### The thirty-two columns of `(4,3)` -/

private theorem col43_0 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 0)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 0
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 20)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 30
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 10) :=
  colEngine43 0 0 0 0 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (1 : ℝ)) (dp_20 (1 : ℝ))
    (dp_30 (1 : ℝ)) (dp_10 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_1 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 1)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 23)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 29
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 9) :=
  colEngine43 0 1 0 1 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (1 : ℝ)) (dp_23 (1 : ℝ))
    (dp_29 (1 : ℝ)) (dp_9 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_2 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 2)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 6
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 18)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 24
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 12) :=
  colEngine43 0 2 0 2 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (1 : ℝ)) (dp_18 (1 : ℝ))
    (dp_24 (1 : ℝ)) (dp_12 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_3 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 3)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 17)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 27
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 15) :=
  colEngine43 0 3 0 3 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (1 : ℝ)) (dp_17 (1 : ℝ))
    (dp_27 (1 : ℝ)) (dp_15 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_4 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 4)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 16)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 26
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 14) :=
  colEngine43 0 0 1 4 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (1 : ℝ)) (dp_16 (1 : ℝ))
    (dp_26 (1 : ℝ)) (dp_14 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_5 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 5)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 19)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 25
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 13) :=
  colEngine43 0 1 1 5 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (1 : ℝ)) (dp_19 (1 : ℝ))
    (dp_25 (1 : ℝ)) (dp_13 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_6 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 6)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 2
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 22)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 28
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 8) :=
  colEngine43 0 2 1 6 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (1 : ℝ)) (dp_22 (1 : ℝ))
    (dp_28 (1 : ℝ)) (dp_8 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_7 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 7)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 21)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 31
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 11) :=
  colEngine43 0 3 1 7 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (1 : ℝ) (1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (1 : ℝ)) (dp_21 (1 : ℝ))
    (dp_31 (1 : ℝ)) (dp_11 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_8 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 8)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 5
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 17)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 27
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 15) :=
  colEngine43 1 0 0 0 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (1 : ℝ)) (dp_17 (1 : ℝ))
    (dp_27 (1 : ℝ)) (dp_15 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_9 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 9)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 18)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 24
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 12) :=
  colEngine43 1 1 0 1 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (1 : ℝ)) (dp_18 (1 : ℝ))
    (dp_24 (1 : ℝ)) (dp_12 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_10 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 10)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 23)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 29
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 9) :=
  colEngine43 1 2 0 2 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_3_0
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (1 : ℝ)) (dp_23 (1 : ℝ))
    (dp_29 (1 : ℝ)) (dp_9 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_11 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 11)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 0
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 20)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 30
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 10) :=
  colEngine43 1 3 0 3 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_0_0
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (1 : ℝ)) (dp_20 (1 : ℝ))
    (dp_30 (1 : ℝ)) (dp_10 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_12 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 12)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 1
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 21)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 31
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 11) :=
  colEngine43 1 0 1 4 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (1 : ℝ)) (dp_21 (1 : ℝ))
    (dp_31 (1 : ℝ)) (dp_11 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_13 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 13)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 22)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 28
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 8) :=
  colEngine43 1 1 1 5 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (1 : ℝ)) (dp_22 (1 : ℝ))
    (dp_28 (1 : ℝ)) (dp_8 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_14 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 14)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 19)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 25
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 13) :=
  colEngine43 1 2 1 6 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (1 : ℝ) (1 : ℝ) w61_3_1
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (1 : ℝ)) (dp_19 (1 : ℝ))
    (dp_25 (1 : ℝ)) (dp_13 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_15 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 15)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 16)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 26
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 14) :=
  colEngine43 1 3 1 7 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_0_1
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (1 : ℝ)) (dp_16 (1 : ℝ))
    (dp_26 (1 : ℝ)) (dp_14 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_16 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 16)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 2
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 22)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 28
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 8) :=
  colEngine43 2 0 0 0 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (1 : ℝ)) (dp_22 (1 : ℝ))
    (dp_28 (1 : ℝ)) (dp_8 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_17 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 17)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 21)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 31
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 11) :=
  colEngine43 2 1 0 1 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (1 : ℝ)) (dp_21 (1 : ℝ))
    (dp_31 (1 : ℝ)) (dp_11 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_18 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 18)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 16)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 26
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 14) :=
  colEngine43 2 2 0 2 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (1 : ℝ)) (dp_16 (1 : ℝ))
    (dp_26 (1 : ℝ)) (dp_14 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_19 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 19)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 19)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 25
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 13) :=
  colEngine43 2 3 0 3 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (1 : ℝ)) (dp_19 (1 : ℝ))
    (dp_25 (1 : ℝ)) (dp_13 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_20 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 20)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 18)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 24
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 12) :=
  colEngine43 2 0 1 4 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (1 : ℝ)) (dp_18 (1 : ℝ))
    (dp_24 (1 : ℝ)) (dp_12 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_21 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 21)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 5
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 17)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 27
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 15) :=
  colEngine43 2 1 1 5 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (1 : ℝ)) (dp_17 (1 : ℝ))
    (dp_27 (1 : ℝ)) (dp_15 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_22 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 22)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 20)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 30
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 10) :=
  colEngine43 2 2 1 6 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (1 : ℝ)) (dp_20 (1 : ℝ))
    (dp_30 (1 : ℝ)) (dp_10 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_23 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 23)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 3
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 23)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 29
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 9) :=
  colEngine43 2 3 1 7 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (1 : ℝ)) (dp_23 (1 : ℝ))
    (dp_29 (1 : ℝ)) (dp_9 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_24 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 24)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 7
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 19)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 25
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 13) :=
  colEngine43 3 0 0 0 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (1 : ℝ)) (dp_19 (1 : ℝ))
    (dp_25 (1 : ℝ)) (dp_13 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_25 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 25)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 4
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 16)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 26
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 14) :=
  colEngine43 3 1 0 1 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (1 : ℝ)) (dp_16 (1 : ℝ))
    (dp_26 (1 : ℝ)) (dp_14 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_26 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 26)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 21)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 31
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 11) :=
  colEngine43 3 2 0 2 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_1_0
      (dm1_1 (1 : ℝ)) (dm1_7 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (1 : ℝ)) (dp_21 (1 : ℝ))
    (dp_31 (1 : ℝ)) (dp_11 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_27 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 27)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 2
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 22)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 28
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 8) :=
  colEngine43 3 3 0 3 rfl rfl (tb1m0 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_2_0
      (dm1_2 (1 : ℝ)) (dm1_4 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (1 : ℝ)) (dp_22 (1 : ℝ))
    (dp_28 (1 : ℝ)) (dp_8 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_28 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 28)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 23)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 29
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 9) :=
  colEngine43 3 0 1 4 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (1 : ℝ) (1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (1 : ℝ)) (dp_23 (1 : ℝ))
    (dp_29 (1 : ℝ)) (dp_9 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_29 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 29)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 0
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 20)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 30
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 10) :=
  colEngine43 3 1 1 5 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (1 : ℝ) (-1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (1 : ℝ)) (dp_20 (1 : ℝ))
    (dp_30 (1 : ℝ)) (dp_10 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_30 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 30)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 5
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 17)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 27
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 15) :=
  colEngine43 3 2 1 6 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w61_1_1
      (dm1_3 (1 : ℝ)) (dm1_5 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (1 : ℝ)) (dp_17 (1 : ℝ))
    (dp_27 (1 : ℝ)) (dp_15 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col43_31 :
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) 31)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 18)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 24
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 12) :=
  colEngine43 3 3 1 7 rfl rfl (tb1m1 (-1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_six_one (1 : ℝ) (-1 : ℝ) (1 : ℝ) w61_2_1
      (dm1_0 (1 : ℝ)) (dm1_6 (1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (1 : ℝ)) (dp_18 (1 : ℝ))
    (dp_24 (1 : ℝ)) (dp_12 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

/-! ### The packed literal for `(4,3)` — verbatim from
`scripts/certgen/out/lean_literals/fuse_4_3.txt` -/

/-- Packed row codes for `realFuseMatrix 4 3` (32 × 32).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_4_3 : Fin 32 → ℕ :=
  ![137292135966523,
    5083991002053,
    7625642127489,
    45847728147801,
    848077799409,
    411803184902319,
    617676883107723,
    284758842627,
    7625685173481,
    45941871326631,
    68661758778787,
    2542124642283,
    617680369892133,
    283596581403,
    1695380757759,
    205912052814231,
    848092148397,
    411803184908853,
    1235353766176071,
    566026117641,
    68693139661249,
    2541996033561,
    7625643721083,
    45847728206853,
    1235350279391679,
    567188379351,
    1695366408933,
    205912052807643,
    7625686768533,
    45941871385677,
    137323517203279,
    5083861330449]

/-- Packed literal for `realFuseMatrix 4 3`: decode digit `j` of
`fuseRows_4_3 i`. -/
def fuseLit_4_3 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j =>
    match fuseRows_4_3 i / 3 ^ (j : ℕ) % 3 with
    | 1 => (1 : ℝ)
    | 2 => -1
    | _ => 0

/-! ### The four columns of `hcol43`, as data -/

private def vv431 : Fin 32 → ℝ :=
  ![1, 1, 1, -1, 1, 1, -1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1]

private def vv432 : Fin 32 → ℝ :=
  ![1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, 1, -1, -1]

private def vv433 : Fin 32 → ℝ :=
  ![1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1, -1]

private def vv434 : Fin 32 → ℝ :=
  ![1, -1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1]

private def kv431 : Fin 32 → ℕ :=
  ![1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1]

private def kv432 : Fin 32 → ℕ :=
  ![1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2]

private def kv433 : Fin 32 → ℕ :=
  ![1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2]

private def kv434 : Fin 32 → ℕ :=
  ![1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1]

private def nv431 : Fin 32 → Fin 32 :=
  ![0, 3, 6, 5, 4, 7, 2, 1, 5, 6, 3, 0, 1, 2, 7, 4, 2, 1, 4, 7, 6, 5, 0, 3, 7, 4, 1, 2, 3, 0, 5, 6]

private def nv432 : Fin 32 → Fin 32 :=
  ![20, 23, 18, 17, 16, 19, 22, 21, 17, 18, 23, 20, 21, 22, 19, 16, 22, 21, 16, 19, 18, 17, 20, 23, 19, 16, 21, 22, 23, 20, 17, 18]

private def nv433 : Fin 32 → Fin 32 :=
  ![30, 29, 24, 27, 26, 25, 28, 31, 27, 24, 29, 30, 31, 28, 25, 26, 28, 31, 26, 25, 24, 27, 30, 29, 25, 26, 31, 28, 29, 30, 27, 24]

private def nv434 : Fin 32 → Fin 32 :=
  ![10, 9, 12, 15, 14, 13, 8, 11, 15, 12, 9, 10, 11, 8, 13, 14, 8, 11, 14, 13, 12, 15, 10, 9, 13, 14, 11, 8, 9, 10, 15, 12]

/-! ### The `1024`-point kernel certificate -/

private def tt431 (i j : Fin 32) : ℕ :=
  if nv431 j = i then kv431 j else 0

private def tt432 (i j : Fin 32) : ℕ :=
  if nv432 j = i then kv432 j else 0

private def tt433 (i j : Fin 32) : ℕ :=
  if nv433 j = i then kv433 j else 0

private def tt434 (i j : Fin 32) : ℕ :=
  if nv434 j = i then kv434 j else 0

/-- **The table certificate.**  For every one of the `32 x 32` points:
the first three conjuncts say that merging the four column contributions
never merges two nonzero codes (i.e. at most one of the four `hcol43`
columns lands on row `i`), and the last says that the surviving code is
exactly the base-3 digit `j` of `fuseRows_4_3`.  Checked by the kernel. -/
private theorem master43 : ∀ i j : Fin 32,
    (tt431 i j = 0 ∨ tt432 i j = 0)
  ∧ (tt433 i j = 0 ∨ tt434 i j = 0)
  ∧ (dpick (tt431 i j) (tt432 i j) = 0
      ∨ dpick (tt433 i j) (tt434 i j) = 0)
  ∧ dpick (dpick (tt431 i j) (tt432 i j))
      (dpick (tt433 i j) (tt434 i j))
      = fuseRows_4_3 i / 3 ^ (j : ℕ) % 3 := by decide

set_option maxHeartbeats 16000000 in
private theorem hcol43 : ∀ j : Fin 32,
    realFuse_four_three.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 3) j)
      = (vv431 j • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 (nv431 j)
          + vv432 j • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 (nv432 j))
        + (vv433 j • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 (nv433 j)
          + vv434 j • matrixSuperBasis (towerBasis (1 : ℝ) 1) 2 2 (nv434 j)) := by
  intro j
  fin_cases j

  · exact col43_0

  · exact col43_1

  · exact col43_2

  · exact col43_3

  · exact col43_4

  · exact col43_5

  · exact col43_6

  · exact col43_7

  · exact col43_8

  · exact col43_9

  · exact col43_10

  · exact col43_11

  · exact col43_12

  · exact col43_13

  · exact col43_14

  · exact col43_15

  · exact col43_16

  · exact col43_17

  · exact col43_18

  · exact col43_19

  · exact col43_20

  · exact col43_21

  · exact col43_22

  · exact col43_23

  · exact col43_24

  · exact col43_25

  · exact col43_26

  · exact col43_27

  · exact col43_28

  · exact col43_29

  · exact col43_30

  · exact col43_31


/-! ### From `hcol43` to a single matrix entry -/

/-- The entry formula, generic in `i` and `j`: one `realFuseMatrix_apply`,
one instance of `hcol43`, no case split. -/
private theorem entry43 (i j : Fin 32) :
    realFuseMatrix 4 3 i j
      = (vv431 j * (if nv431 j = i then 1 else 0)
          + vv432 j * (if nv432 j = i then 1 else 0))
        + (vv433 j * (if nv433 j = i then 1 else 0)
          + vv434 j * (if nv434 j = i then 1 else 0)) := by
  have h1 : realFuseMatrix 4 3 i j
      = (realFuseDstBasis 4 3).repr
          ((realFuse 4 3).toAlgEquiv (realFuseSrcBasis 4 3 j)) i :=
    realFuseMatrix_apply 4 3 i j
  have h2 : (realFuse 4 3).toAlgEquiv (realFuseSrcBasis 4 3 j)
      = (vv431 j • realFuseDstBasis 4 3 (nv431 j)
          + vv432 j • realFuseDstBasis 4 3 (nv432 j))
        + (vv433 j • realFuseDstBasis 4 3 (nv433 j)
          + vv434 j • realFuseDstBasis 4 3 (nv434 j)) := hcol43 j
  rw [h1, h2, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rfl

/-- The four real sign vectors are the decodings of the four code
vectors.  One `fin_cases` on `j`; four definitional checks each. -/
private theorem coefs43 (j : Fin 32) :
    vv431 j = fuseDecode (kv431 j)
  ∧ vv432 j = fuseDecode (kv432 j)
  ∧ vv433 j = fuseDecode (kv433 j)
  ∧ vv434 j = fuseDecode (kv434 j) := by
  fin_cases j <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Deliverable `(4,3)`** (`32 x 32`): the fusion matrix is the packed
base-3 literal emitted by `scripts/certgen`. -/
theorem realFuseMatrix_4_3 : ∀ (i j : Fin 32),
    realFuseMatrix 4 3 i j = fuseLit_4_3 i j := by
  intro i j
  obtain ⟨h1, h2, h3, h4⟩ := master43 i j
  refine (entry43 i j).trans ?_
  rw [(coefs43 j).1, (coefs43 j).2.1, (coefs43 j).2.2.1,
    (coefs43 j).2.2.2, dmul, dmul, dmul, dmul]
  show (fuseDecode (tt431 i j) + fuseDecode (tt432 i j))
      + (fuseDecode (tt433 i j) + fuseDecode (tt434 i j)) = _
  rw [dpick_add _ _ h1, dpick_add _ _ h2, dpick_add _ _ h3, h4]
  rfl

/-- The same statement against `RealFuseSpecTranspose`'s own copy of the
forward literal: the two packed row tables are numerically identical, so
the bridge is one `fin_cases` on the row. -/
private theorem fwd43 (i j : Fin 32) :
    realFuseMatrix 4 3 i j = fuseLitFwd_4_3 i j :=
  (realFuseMatrix_4_3 i j).trans (by fin_cases i <;> rfl)

/-! ### The `(4,5)` branch -/

private theorem unfold45
    (x : (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 3)).carrier) :
    realFuse_four_five.toAlgEquiv x
      = ((matrixSuperGtensor (realRep 2) (realRep 7) 1 1).trans
        ((realFuse_two_seven.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 1) 1 1 1 1))).toAlgEquiv
          ((realFuse_four_six.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
            ((gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 2)
                (divisionTower (1 : ℝ) 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                  (towerFuse (1 : ℝ) 2 1).symm).toAlgEquiv x))) := rfl

private theorem colEngine45 (e : Fin 4) (v1 : Fin 4) (v2 : Fin 2)
    (v : Fin 8) (hv : (v : ℕ) = (v1 : ℕ) + 2 ^ 2 * (v2 : ℕ))
    {jw : ZMod 2} {w : (realRep 7).carrier}
    (hwv : towerBasis (1 : ℝ) 1 v2 = w)
    (hw : w ∈ (realRep 7).grading jw)
    (r1 c1 r2 c2 : Fin 1 ⊕ Fin 1) {qa qb : (realRep 2).carrier}
    (hcert : realFuse_four_six.toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis e)
            (towerBasis (1 : ℝ) 2 v1))
        = Matrix.single r1 c1 qa + Matrix.single r2 c2 qb)
    {ta1 ta2 tb1 tb2 : ℝ} {ea1 ea2 eb1 eb2 : Fin 2}
    {raa caa rab cab rba cba rbb cbb : Fin 1 ⊕ Fin 1}
    (hFa : realFuse_two_seven.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
              (ℬ := (realRep 7).grading) ℝ qa w)
          = Matrix.single raa caa (ta1 • towerBasis (-1 : ℝ) 1 ea1)
            + Matrix.single rab cab (ta2 • towerBasis (-1 : ℝ) 1 ea2))
    (hFb : realFuse_two_seven.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
              (ℬ := (realRep 7).grading) ℝ qb w)
          = Matrix.single rba cba (tb1 • towerBasis (-1 : ℝ) 1 eb1)
            + Matrix.single rbb cbb (tb2 • towerBasis (-1 : ℝ) 1 eb2))
    {κ1 κ2 κ3 κ4 : ℝ} {I1 I2 I3 I4 : Fin 32}
    (hI1 : matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I1
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, raa))
            (collapseIndexEquiv 1 1 1 1 (c1, caa))
            (towerBasis (-1 : ℝ) 1 ea1))
    (hI2 : matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I2
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, rab))
            (collapseIndexEquiv 1 1 1 1 (c1, cab))
            (towerBasis (-1 : ℝ) 1 ea2))
    (hI3 : matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I3
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rba))
            (collapseIndexEquiv 1 1 1 1 (c2, cba))
            (towerBasis (-1 : ℝ) 1 eb1))
    (hI4 : matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I4
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rbb))
            (collapseIndexEquiv 1 1 1 1 (c2, cbb))
            (towerBasis (-1 : ℝ) 1 eb2))
    (hκ1 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta1 = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta2 = κ2)
    (hκ3 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb1 = κ3)
    (hκ4 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb2 = κ4) :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3)
          (finProdFinEquiv (e, v)))
      = (κ1 • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I1
          + κ2 • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I2)
        + (κ3 • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I3
          + κ4 • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 I4) := by
  have hA : ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
        (towerFuse (1 : ℝ) 2 1).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ (quatBasis e)
          (towerBasis (1 : ℝ) 3 v))
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((divisionTower (1 : ℝ) 2).gtensor
            (divisionTower (1 : ℝ) 1)).grading) ℝ (quatBasis e)
          (GradedTensorProduct.tmul
            (𝒜 := (divisionTower (1 : ℝ) 2).grading)
            (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
            (towerBasis (1 : ℝ) 2 v1)
            (towerBasis (1 : ℝ) 1 v2)) := by
    refine (SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl quatEvenSuper)
      (towerFuse (1 : ℝ) 2 1).symm (quatBasis e)
      (towerBasis (1 : ℝ) 3 v)).trans ?_
    rw [superRefl_apply]
    exact congrArg
      (fun z => GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := ((divisionTower (1 : ℝ) 2).gtensor
          (divisionTower (1 : ℝ) 1)).grading) ℝ (quatBasis e) z)
      (tfuseKsymm (1 : ℝ) 2 1 v1 v2 v hv)
  have e3 : (realFuse_four_six.gtensorCongr
        (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 2)).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis e)
            (towerBasis (1 : ℝ) 2 v1))
          (towerBasis (1 : ℝ) 1 v2))
      = GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ (Matrix.single r1 c1 qa) w
        + GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ (Matrix.single r2 c2 qb) w := by
    refine (SuperAlgEquiv.gtensorCongr_tmul realFuse_four_six
      (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1)) _ _).trans ?_
    rw [superRefl_apply, hwv, hcert]
    exact add_gtmul (matrixGradingA (sumParity 1 1) (realRep 2).grading)
      (realRep 7).grading _ _ _
  refine (congrArg (fun z => realFuse_four_five.toAlgEquiv z)
      (gtensorBasis_apply_pair quatBasis (towerBasis (1 : ℝ) 3)
        e v)).trans ?_
  refine (unfold45 _).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor (realRep 2) (realRep 7) 1 1).trans
        ((realFuse_two_seven.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 1) 1 1 1 1))).toAlgEquiv
      ((realFuse_four_six.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
        ((gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 2)
            (divisionTower (1 : ℝ) 1)).symm.toAlgEquiv z))) hA).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor (realRep 2) (realRep 7) 1 1).trans
        ((realFuse_two_seven.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 1) 1 1 1 1))).toAlgEquiv
      ((realFuse_four_six.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv z))
      (gtAssocSymm quatEvenSuper (divisionTower (1 : ℝ) 2)
        (divisionTower (1 : ℝ) 1) (quatBasis e)
        (towerBasis (1 : ℝ) 2 v1)
        (towerBasis (1 : ℝ) 1 v2))).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor (realRep 2) (realRep 7) 1 1).trans
        ((realFuse_two_seven.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 1) 1 1 1 1))).toAlgEquiv z) e3).trans ?_
  refine (map_add ((matrixSuperGtensor (realRep 2) (realRep 7) 1 1).trans
        ((realFuse_two_seven.matrixSuper 1 1).trans
          (matrixSuperComp (realRep 1) 1 1 1 1))).toAlgEquiv _ _).trans ?_
  exact congrArg₂ (fun x y => x + y)
    (termG2' realFuse_two_seven hw r1 c1 hFa hI1 hI2 hκ1 hκ2)
    (termG2' realFuse_two_seven hw r2 c2 hFb hI3 hI4 hκ3 hκ4)

/-! ### The thirty-two columns of `(4,5)` -/

private theorem col45_0 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 0)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 0
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 20)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 30
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 10) :=
  colEngine45 0 0 0 0 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (-1 : ℝ)) (dp_20 (-1 : ℝ))
    (dp_30 (-1 : ℝ)) (dp_10 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_1 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 1)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 3
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 23)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 29
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 9) :=
  colEngine45 0 1 0 1 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (-1 : ℝ)) (dp_23 (-1 : ℝ))
    (dp_29 (-1 : ℝ)) (dp_9 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_2 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 2)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 6
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 18)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 24
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 12) :=
  colEngine45 0 2 0 2 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (-1 : ℝ)) (dp_18 (-1 : ℝ))
    (dp_24 (-1 : ℝ)) (dp_12 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_3 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 3)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 17)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 27
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 15) :=
  colEngine45 0 3 0 3 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (-1 : ℝ)) (dp_17 (-1 : ℝ))
    (dp_27 (-1 : ℝ)) (dp_15 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_4 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 4)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 4
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 16)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 26
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 14) :=
  colEngine45 0 0 1 4 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (-1 : ℝ)) (dp_16 (-1 : ℝ))
    (dp_26 (-1 : ℝ)) (dp_14 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_5 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 5)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 7
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 19)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 25
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 13) :=
  colEngine45 0 1 1 5 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (-1 : ℝ)) (dp_19 (-1 : ℝ))
    (dp_25 (-1 : ℝ)) (dp_13 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_6 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 6)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 22)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 28
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 8) :=
  colEngine45 0 2 1 6 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (-1 : ℝ)) (dp_22 (-1 : ℝ))
    (dp_28 (-1 : ℝ)) (dp_8 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_7 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 7)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 21)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 31
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 11) :=
  colEngine45 0 3 1 7 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (-1 : ℝ)) (dp_21 (-1 : ℝ))
    (dp_31 (-1 : ℝ)) (dp_11 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_8 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 8)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 17)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 27
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 15) :=
  colEngine45 1 0 0 0 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (-1 : ℝ)) (dp_17 (-1 : ℝ))
    (dp_27 (-1 : ℝ)) (dp_15 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_9 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 9)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 18)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 24
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 12) :=
  colEngine45 1 1 0 1 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (-1 : ℝ)) (dp_18 (-1 : ℝ))
    (dp_24 (-1 : ℝ)) (dp_12 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_10 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 10)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 3
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 23)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 29
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 9) :=
  colEngine45 1 2 0 2 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_0
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (-1 : ℝ)) (dp_23 (-1 : ℝ))
    (dp_29 (-1 : ℝ)) (dp_9 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_11 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 11)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 20)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 30
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 10) :=
  colEngine45 1 3 0 3 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_0
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (-1 : ℝ)) (dp_20 (-1 : ℝ))
    (dp_30 (-1 : ℝ)) (dp_10 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_12 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 12)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 21)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 31
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 11) :=
  colEngine45 1 0 1 4 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (-1 : ℝ)) (dp_21 (-1 : ℝ))
    (dp_31 (-1 : ℝ)) (dp_11 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_13 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 13)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 2
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 22)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 28
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 8) :=
  colEngine45 1 1 1 5 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (-1 : ℝ)) (dp_22 (-1 : ℝ))
    (dp_28 (-1 : ℝ)) (dp_8 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_14 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 14)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 7
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 19)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 25
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 13) :=
  colEngine45 1 2 1 6 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_3_1
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (-1 : ℝ)) (dp_19 (-1 : ℝ))
    (dp_25 (-1 : ℝ)) (dp_13 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_15 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 15)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 16)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 26
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 14) :=
  colEngine45 1 3 1 7 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (1 : ℝ) w27_0_1
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (-1 : ℝ)) (dp_16 (-1 : ℝ))
    (dp_26 (-1 : ℝ)) (dp_14 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_16 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 16)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 22)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 28
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 8) :=
  colEngine45 2 0 0 0 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (-1 : ℝ)) (dp_22 (-1 : ℝ))
    (dp_28 (-1 : ℝ)) (dp_8 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_17 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 17)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 21)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 31
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 11) :=
  colEngine45 2 1 0 1 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (-1 : ℝ)) (dp_21 (-1 : ℝ))
    (dp_31 (-1 : ℝ)) (dp_11 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_18 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 18)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 16)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 26
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 14) :=
  colEngine45 2 2 0 2 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (-1 : ℝ)) (dp_16 (-1 : ℝ))
    (dp_26 (-1 : ℝ)) (dp_14 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_19 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 19)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 19)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 25
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 13) :=
  colEngine45 2 3 0 3 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (-1 : ℝ)) (dp_19 (-1 : ℝ))
    (dp_25 (-1 : ℝ)) (dp_13 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_20 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 20)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 6
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 18)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 24
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 12) :=
  colEngine45 2 0 1 4 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (-1 : ℝ)) (dp_18 (-1 : ℝ))
    (dp_24 (-1 : ℝ)) (dp_12 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_21 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 21)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 17)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 27
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 15) :=
  colEngine45 2 1 1 5 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (-1 : ℝ)) (dp_17 (-1 : ℝ))
    (dp_27 (-1 : ℝ)) (dp_15 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_22 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 22)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 20)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 30
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 10) :=
  colEngine45 2 2 1 6 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (-1 : ℝ)) (dp_20 (-1 : ℝ))
    (dp_30 (-1 : ℝ)) (dp_10 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_23 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 23)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 23)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 29
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 9) :=
  colEngine45 2 3 1 7 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (-1 : ℝ)) (dp_23 (-1 : ℝ))
    (dp_29 (-1 : ℝ)) (dp_9 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_24 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 24)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 19)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 25
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 13) :=
  colEngine45 3 0 0 0 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_7 (-1 : ℝ)) (dp_19 (-1 : ℝ))
    (dp_25 (-1 : ℝ)) (dp_13 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_25 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 25)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 4
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 16)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 26
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 14) :=
  colEngine45 3 1 0 1 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_4 (-1 : ℝ)) (dp_16 (-1 : ℝ))
    (dp_26 (-1 : ℝ)) (dp_14 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_26 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 26)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 21)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 31
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 11) :=
  colEngine45 3 2 0 2 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_0
      (dm1_1 (-1 : ℝ)) (dm1_7 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_1 (-1 : ℝ)) (dp_21 (-1 : ℝ))
    (dp_31 (-1 : ℝ)) (dp_11 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_27 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 27)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 2
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 22)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 28
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 8) :=
  colEngine45 3 3 0 3 rfl rfl (tb1m0 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_0
      (dm1_2 (-1 : ℝ)) (dm1_4 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_2 (-1 : ℝ)) (dp_22 (-1 : ℝ))
    (dp_28 (-1 : ℝ)) (dp_8 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_28 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 28)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 23)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 29
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 9) :=
  colEngine45 3 0 1 4 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_3 (-1 : ℝ)) (dp_23 (-1 : ℝ))
    (dp_29 (-1 : ℝ)) (dp_9 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_29 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 29)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 0
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 20)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 30
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 10) :=
  colEngine45 3 1 1 5 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_0 (-1 : ℝ)) (dp_20 (-1 : ℝ))
    (dp_30 (-1 : ℝ)) (dp_10 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_30 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 30)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 17)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 27
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 15) :=
  colEngine45 3 2 1 6 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0)
    (two_singles val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_1_1
      (dm1_3 (-1 : ℝ)) (dm1_5 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_5 (-1 : ℝ)) (dp_17 (-1 : ℝ))
    (dp_27 (-1 : ℝ)) (dp_15 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col45_31 :
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) 31)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 18)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 24
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 12) :=
  colEngine45 3 3 1 7 rfl rfl (tb1m1 (1 : ℝ))
    (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0)
    (two_singles val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)))
    (fG2' realFuse_two_seven (-1 : ℝ) (-1 : ℝ) (1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (fG2' realFuse_two_seven (1 : ℝ) (1 : ℝ) (-1 : ℝ) w27_2_1
      (dm1_0 (-1 : ℝ)) (dm1_6 (-1 : ℝ))
      rfl (by norm_num) (by norm_num))
    (dp_6 (-1 : ℝ)) (dp_18 (-1 : ℝ))
    (dp_24 (-1 : ℝ)) (dp_12 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

/-! ### The packed literal for `(4,5)` — verbatim from
`scripts/certgen/out/lean_literals/fuse_4_5.txt` -/

/-- Packed row codes for `realFuseMatrix 4 5` (32 × 32).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_4_5 : Fin 32 → ℕ :=
  ![137292136143670,
    5083990470612,
    15251239612476,
    22970935692840,
    1694993337270,
    411803184902292,
    617680369892124,
    567193162320,
    15251282658468,
    23065078871670,
    68661758601640,
    2542125173724,
    1235353766156388,
    284758842870,
    1695380757840,
    411792724549116,
    848092148316,
    205901592454440,
    1235350279391670,
    283601364372,
    68693139838396,
    2541995502120,
    7625685174210,
    45941871326628,
    617676883088040,
    566026117884,
    847704727908,
    205912052807670,
    7625642126760,
    45847728147804,
    137323517026132,
    5083861861890]

/-- Packed literal for `realFuseMatrix 4 5`: decode digit `j` of
`fuseRows_4_5 i`. -/
def fuseLit_4_5 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j =>
    match fuseRows_4_5 i / 3 ^ (j : ℕ) % 3 with
    | 1 => (1 : ℝ)
    | 2 => -1
    | _ => 0

/-! ### The four columns of `hcol45`, as data -/

private def vv451 : Fin 32 → ℝ :=
  ![1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1]

private def vv452 : Fin 32 → ℝ :=
  ![1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1]

private def vv453 : Fin 32 → ℝ :=
  ![1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1]

private def vv454 : Fin 32 → ℝ :=
  ![1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, -1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, -1, -1]

private def kv451 : Fin 32 → ℕ :=
  ![1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1]

private def kv452 : Fin 32 → ℕ :=
  ![1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2]

private def kv453 : Fin 32 → ℕ :=
  ![1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1]

private def kv454 : Fin 32 → ℕ :=
  ![1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2]

private def nv451 : Fin 32 → Fin 32 :=
  ![0, 3, 6, 5, 4, 7, 2, 1, 5, 6, 3, 0, 1, 2, 7, 4, 2, 1, 4, 7, 6, 5, 0, 3, 7, 4, 1, 2, 3, 0, 5, 6]

private def nv452 : Fin 32 → Fin 32 :=
  ![20, 23, 18, 17, 16, 19, 22, 21, 17, 18, 23, 20, 21, 22, 19, 16, 22, 21, 16, 19, 18, 17, 20, 23, 19, 16, 21, 22, 23, 20, 17, 18]

private def nv453 : Fin 32 → Fin 32 :=
  ![30, 29, 24, 27, 26, 25, 28, 31, 27, 24, 29, 30, 31, 28, 25, 26, 28, 31, 26, 25, 24, 27, 30, 29, 25, 26, 31, 28, 29, 30, 27, 24]

private def nv454 : Fin 32 → Fin 32 :=
  ![10, 9, 12, 15, 14, 13, 8, 11, 15, 12, 9, 10, 11, 8, 13, 14, 8, 11, 14, 13, 12, 15, 10, 9, 13, 14, 11, 8, 9, 10, 15, 12]

/-! ### The `1024`-point kernel certificate -/

private def tt451 (i j : Fin 32) : ℕ :=
  if nv451 j = i then kv451 j else 0

private def tt452 (i j : Fin 32) : ℕ :=
  if nv452 j = i then kv452 j else 0

private def tt453 (i j : Fin 32) : ℕ :=
  if nv453 j = i then kv453 j else 0

private def tt454 (i j : Fin 32) : ℕ :=
  if nv454 j = i then kv454 j else 0

/-- **The table certificate.**  For every one of the `32 x 32` points:
the first three conjuncts say that merging the four column contributions
never merges two nonzero codes (i.e. at most one of the four `hcol45`
columns lands on row `i`), and the last says that the surviving code is
exactly the base-3 digit `j` of `fuseRows_4_5`.  Checked by the kernel. -/
private theorem master45 : ∀ i j : Fin 32,
    (tt451 i j = 0 ∨ tt452 i j = 0)
  ∧ (tt453 i j = 0 ∨ tt454 i j = 0)
  ∧ (dpick (tt451 i j) (tt452 i j) = 0
      ∨ dpick (tt453 i j) (tt454 i j) = 0)
  ∧ dpick (dpick (tt451 i j) (tt452 i j))
      (dpick (tt453 i j) (tt454 i j))
      = fuseRows_4_5 i / 3 ^ (j : ℕ) % 3 := by decide

set_option maxHeartbeats 16000000 in
private theorem hcol45 : ∀ j : Fin 32,
    realFuse_four_five.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 3) j)
      = (vv451 j • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 (nv451 j)
          + vv452 j • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 (nv452 j))
        + (vv453 j • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 (nv453 j)
          + vv454 j • matrixSuperBasis (towerBasis (-1 : ℝ) 1) 2 2 (nv454 j)) := by
  intro j
  fin_cases j

  · exact col45_0

  · exact col45_1

  · exact col45_2

  · exact col45_3

  · exact col45_4

  · exact col45_5

  · exact col45_6

  · exact col45_7

  · exact col45_8

  · exact col45_9

  · exact col45_10

  · exact col45_11

  · exact col45_12

  · exact col45_13

  · exact col45_14

  · exact col45_15

  · exact col45_16

  · exact col45_17

  · exact col45_18

  · exact col45_19

  · exact col45_20

  · exact col45_21

  · exact col45_22

  · exact col45_23

  · exact col45_24

  · exact col45_25

  · exact col45_26

  · exact col45_27

  · exact col45_28

  · exact col45_29

  · exact col45_30

  · exact col45_31


/-! ### From `hcol45` to a single matrix entry -/

/-- The entry formula, generic in `i` and `j`: one `realFuseMatrix_apply`,
one instance of `hcol45`, no case split. -/
private theorem entry45 (i j : Fin 32) :
    realFuseMatrix 4 5 i j
      = (vv451 j * (if nv451 j = i then 1 else 0)
          + vv452 j * (if nv452 j = i then 1 else 0))
        + (vv453 j * (if nv453 j = i then 1 else 0)
          + vv454 j * (if nv454 j = i then 1 else 0)) := by
  have h1 : realFuseMatrix 4 5 i j
      = (realFuseDstBasis 4 5).repr
          ((realFuse 4 5).toAlgEquiv (realFuseSrcBasis 4 5 j)) i :=
    realFuseMatrix_apply 4 5 i j
  have h2 : (realFuse 4 5).toAlgEquiv (realFuseSrcBasis 4 5 j)
      = (vv451 j • realFuseDstBasis 4 5 (nv451 j)
          + vv452 j • realFuseDstBasis 4 5 (nv452 j))
        + (vv453 j • realFuseDstBasis 4 5 (nv453 j)
          + vv454 j • realFuseDstBasis 4 5 (nv454 j)) := hcol45 j
  rw [h1, h2, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rfl

/-- The four real sign vectors are the decodings of the four code
vectors.  One `fin_cases` on `j`; four definitional checks each. -/
private theorem coefs45 (j : Fin 32) :
    vv451 j = fuseDecode (kv451 j)
  ∧ vv452 j = fuseDecode (kv452 j)
  ∧ vv453 j = fuseDecode (kv453 j)
  ∧ vv454 j = fuseDecode (kv454 j) := by
  fin_cases j <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Deliverable `(4,5)`** (`32 x 32`): the fusion matrix is the packed
base-3 literal emitted by `scripts/certgen`. -/
theorem realFuseMatrix_4_5 : ∀ (i j : Fin 32),
    realFuseMatrix 4 5 i j = fuseLit_4_5 i j := by
  intro i j
  obtain ⟨h1, h2, h3, h4⟩ := master45 i j
  refine (entry45 i j).trans ?_
  rw [(coefs45 j).1, (coefs45 j).2.1, (coefs45 j).2.2.1,
    (coefs45 j).2.2.2, dmul, dmul, dmul, dmul]
  show (fuseDecode (tt451 i j) + fuseDecode (tt452 i j))
      + (fuseDecode (tt453 i j) + fuseDecode (tt454 i j)) = _
  rw [dpick_add _ _ h1, dpick_add _ _ h2, dpick_add _ _ h3, h4]
  rfl

/-- The same statement against `RealFuseSpecTranspose`'s own copy of the
forward literal: the two packed row tables are numerically identical, so
the bridge is one `fin_cases` on the row. -/
private theorem fwd45 (i j : Fin 32) :
    realFuseMatrix 4 5 i j = fuseLitFwd_4_5 i j :=
  (realFuseMatrix_4_5 i j).trans (by fin_cases i <;> rfl)

/-! ### The two released transposes -/

/-- **Deliverable `(3,4)`**, discharged from the forward `(4,3)`. -/
theorem realFuseMatrix_3_4 : ∀ (i j : Fin 32),
    realFuseMatrix 3 4 i j = fuseLit_3_4 i j :=
  realFuseMatrix_3_4_of_forward fwd43

/-- **Deliverable `(5,4)`**, discharged from the forward `(4,5)`. -/
theorem realFuseMatrix_5_4 : ∀ (i j : Fin 32),
    realFuseMatrix 5 4 i j = fuseLit_5_4 i j :=
  realFuseMatrix_5_4_of_forward fwd45

end Superfusion

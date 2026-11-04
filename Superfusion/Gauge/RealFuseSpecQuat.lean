/-
Superfusion / Gauge / RealFuseSpecQuat

M15 semantic-bridge GROUP 3: **value-pinning spec theorems for the
quaternion row/column** — the matrix of `realFuse a b` in the explicit
frames of `RealFuseMatrix` *is* a stated literal.  Landed here:

  `realFuseMatrix_4_1`, `realFuseMatrix_4_7`, `realFuseMatrix_1_4`,
  `realFuseMatrix_7_4`  — the odd-target quaternion pairs and their
  Koszul transposes; `8 × 8` signed permutations;
  `realFuseMatrix_4_4`  — Wall's isomorphism `ℍ ᵍ⊗ ℍ ≅ M_{4|0}(ℝ)`
  along the explicit basis `1, i, j, k`; `16 × 16`, four nonzero
  entries per column.

Values are the frozen certificates
`scripts/certgen/out/lean_literals/fuse_{a}_{b}.txt`.

*Not* landed: the remaining quaternion matrix-target pairs
`(4,2), (4,6), (4,3), (4,5)`.  Every one of them ends in a `peelFuse`
branch (`realFuse_five_one`/`realFuse_three_seven` for `(4,2)`/`(4,6)`,
and those again for `(4,3)`/`(4,5)` through this file's own pairs), and
the `peelFuse` *evaluation* machinery is the piece deliberately parked
by the tower track — see the "Not yet landed" note at the end of
`RealFuseSpecTower` and the out-of-tree draft
`scripts/certgen/out/tower_peel_wip.lean.txt`.  They become one-page
compositions once that lands; nothing else here blocks them.

Method (following `RealFuseSpecPilot`, whose conclusions this file
inherits): casts dissolve by kernel defeq at concrete labels; per-column
evaluation pushes each source frame vector through the branch's own
composite with `have`-by-`have` application lemmas, lands on
`Matrix.single`, and pins entries via `Basis.repr_self_apply`.

New generic machinery contributed here (used by the whole 64-branch
rollout):

* `toMatrix_of_coord` / `toMatrix_signedPerm` / `toMatrix_of_entries44`
  — the **column-to-matrix step, done in a generic lemma**.  This is not
  cosmetic: the fusion isomorphism is typed at the `realRep` spelling
  while the frames are spelled at `quatEvenSuper`/`divisionTower`, so
  `LinearMap.toMatrix bX bY f` is type-correct only at `default`
  transparency and every `rw` into it fails ("did not find an
  occurrence") because `rw` checks its motive at `instances`
  transparency.  Inside a generic lemma the term is honestly typed; at
  the call site only `refine` (a defeq check) meets the mismatch.
* `matrixSuperBasis_repr` — coordinates along the flattened matrix frame
  ARE entrywise coordinates: `repr M (r,s,e) = bP.repr (M r s) e`.
* `towerFuse_basis` — **the tower fusion is a sign-free permutation on
  the canonical tower bases**: `e_i ᵍ⊗ e_j ↦ e_{i + 2^a·j}`, generic in
  `ε`, `a`, `b` (single induction, no per-floor case analysis).
* the four coordinate multiplication rules of the odd double
  (`mkA_mul_mkA` … `mkB_mul_mkB`) and the floor-`1..4` basis
  dictionaries, which turn every division-tower product into a
  two-line rewrite.
* `qv_mul` / `qv_star` — the quaternion multiplication table and
  conjugation signs on `1, i, j, k`, proved at the honest `ℍ[ℝ]`
  spelling (`qv`) and transported to `quatEvenSuper.carrier`: at the
  bundled carrier `*`, `•`, `star` go through `SuperAlgebra.ring`, which
  no `QuaternionAlgebra` `simp` lemma matches, and `Star` is not even
  found by instance search.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7).
-/
import Superfusion.Gauge.RealFuseMatrix

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Superfusion

open Module GradedTensorProduct Quaternion

/-! ### Entry extraction from the matrix frame -/

/-- Coordinates along the flattened matrix frame ARE entrywise
coordinates, stated at the raw `Matrix` carrier. -/
private theorem matrixSuperBasis_repr' {P : SuperAlgebra ℝ} {k : ℕ}
    (bP : Basis (Fin k) ℝ P.carrier) (p q : ℕ)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier)
    (r s : Fin p ⊕ Fin q) (e : Fin k) :
    ((matrixEntryBasis bP (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)).reindex
        (matrixSuperIndexEquiv p q k)).repr M
        (matrixSuperIndexEquiv p q k (r, s, e))
      = bP.repr (M r s) e := by
  rw [Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    matrixEntryBasis, Basis.repr_reindex_apply]
  rw [show (matrixIndexPack (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (Fin k)).symm
      (r, s, e) = ⟨r, s, e⟩ from rfl]
  rfl

/-- **Entry extraction**: the `(r, s, e)`-coordinate of a matrix `M`
along the flattened matrix frame is the `e`-coordinate of the entry
`M r s`. -/
private theorem matrixSuperBasis_repr {P : SuperAlgebra ℝ} {k : ℕ}
    (bP : Basis (Fin k) ℝ P.carrier) (p q : ℕ)
    (M : (P.matrixSuper p q).carrier) (r s : Fin p ⊕ Fin q) (e : Fin k) :
    (matrixSuperBasis bP p q).repr M (matrixSuperIndexEquiv p q k (r, s, e))
      = bP.repr (M r s) e :=
  matrixSuperBasis_repr' bP p q M r s e

/-! ### From column data to the matrix

The last step of every branch turns per-column values into the matrix.
It **must** be done by a generic lemma, applied with `refine`, and never
by rewriting inside the concrete goal.  Reason: the fusion isomorphism
`realFuse_a_b` is typed at the `realRep` spelling of its source and
target, while the frames are spelled at `quatEvenSuper` /
`divisionTower` / `towerBasis`.  These are definitionally equal, so
`LinearMap.toMatrix bX bY f` elaborates — but the resulting term is
type-correct only at `default` transparency, and `rw` type-checks its
motive at `instances` transparency, where it is *not*.  Every rewrite
therefore fails with "did not find an occurrence".  Inside a generic
lemma all of `bX, bY, f` are variables, the term is honestly typed, and
the rewrites go through; at the call site only `refine` (a defeq check)
touches the mismatched spelling. -/

/-- **Column-to-matrix, general form**: pinning every coordinate of
every column pins the matrix. -/
private theorem toMatrix_of_coord {X Y : Type*} [AddCommGroup X]
    [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {m n : ℕ}
    (bX : Basis (Fin n) ℝ X) (bY : Basis (Fin m) ℝ Y) (f : X →ₗ[ℝ] Y)
    (M : Matrix (Fin m) (Fin n) ℝ)
    (h : ∀ (i : Fin m) (j : Fin n), bY.repr (f (bX j)) i = M i j) :
    LinearMap.toMatrix bX bY f = M := by
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply]
  exact h i j

/-- **Column-to-matrix, signed-permutation form**: if `f` sends the
`j`-th source frame vector to `c j` times the `σ j`-th target frame
vector, the matrix is the signed permutation matrix of `(c, σ)`. -/
private theorem toMatrix_signedPerm {X Y : Type*} [AddCommGroup X]
    [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {m n : ℕ}
    (bX : Basis (Fin n) ℝ X) (bY : Basis (Fin m) ℝ Y) (f : X →ₗ[ℝ] Y)
    (c : Fin n → ℝ) (σ : Fin n → Fin m) (M : Matrix (Fin m) (Fin n) ℝ)
    (hcol : ∀ j, f (bX j) = c j • bY (σ j))
    (hM : ∀ (i : Fin m) (j : Fin n),
      c j * (if σ j = i then (1 : ℝ) else 0) = M i j) :
    LinearMap.toMatrix bX bY f = M := by
  refine toMatrix_of_coord bX bY f M fun i j => ?_
  rw [hcol j, map_smul, Finsupp.smul_apply, Basis.repr_self_apply,
    smul_eq_mul]
  exact hM i j

/-! ### The four coordinate multiplication rules of the odd double -/

section MkMul

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (ε : ℝ)

private theorem mkA_mul_mkA (a c : A) :
    OddDouble.mk 𝒜 ε a 0 * OddDouble.mk 𝒜 ε c 0
      = OddDouble.mk 𝒜 ε (a * c) 0 := by
  rw [OddDouble.mk_mul_mk]
  simp only [map_zero, mul_zero, zero_mul, smul_zero, add_zero, zero_add]

private theorem mkA_mul_mkB (a d : A) :
    OddDouble.mk 𝒜 ε a 0 * OddDouble.mk 𝒜 ε 0 d
      = OddDouble.mk 𝒜 ε 0 (a * d) := by
  rw [OddDouble.mk_mul_mk]
  simp only [map_zero, mul_zero, zero_mul, smul_zero, add_zero, zero_add]

private theorem mkB_mul_mkA (b c : A) :
    OddDouble.mk 𝒜 ε 0 b * OddDouble.mk 𝒜 ε c 0
      = OddDouble.mk 𝒜 ε 0 (b * parityMap 𝒜 c) := by
  rw [OddDouble.mk_mul_mk]
  simp only [map_zero, mul_zero, zero_mul, smul_zero, add_zero, zero_add]

private theorem mkB_mul_mkB (b d : A) :
    OddDouble.mk 𝒜 ε 0 b * OddDouble.mk 𝒜 ε 0 d
      = OddDouble.mk 𝒜 ε (ε • (b * parityMap 𝒜 d)) 0 := by
  rw [OddDouble.mk_mul_mk]
  simp only [map_zero, mul_zero, zero_mul, smul_zero, add_zero, zero_add]

private theorem mkA_neg (a : A) :
    OddDouble.mk 𝒜 ε (-a) 0 = -OddDouble.mk 𝒜 ε a 0 := by
  refine OddDouble.ext 𝒜 ε ?_ ?_ <;> simp

private theorem mkB_neg (b : A) :
    OddDouble.mk 𝒜 ε 0 (-b) = -OddDouble.mk 𝒜 ε 0 b := by
  refine OddDouble.ext 𝒜 ε ?_ ?_ <;> simp

private theorem smul_mkA (c : ℝ) (a : A) :
    OddDouble.mk 𝒜 ε (c • a) 0 = c • OddDouble.mk 𝒜 ε a 0 := by
  refine OddDouble.ext 𝒜 ε ?_ ?_ <;> simp

private theorem smul_mkB (c : ℝ) (b : A) :
    OddDouble.mk 𝒜 ε 0 (c • b) = c • OddDouble.mk 𝒜 ε 0 b := by
  refine OddDouble.ext 𝒜 ε ?_ ?_ <;> simp

end MkMul

/-! ### Shared application lemmas (pilot copies) -/

private theorem superRefl_apply (P : SuperAlgebra ℝ) (x : P.carrier) :
    (SuperAlgEquiv.refl P).toAlgEquiv x = x := rfl

/-- The inverse of `matrixSuperOne` is the single-entry matrix at the
unique index. -/
private theorem matrixSuperOne_symm_single (P : SuperAlgebra ℝ)
    (v : P.carrier) :
    (matrixSuperOne P).symm.toAlgEquiv v
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v := by
  refine Matrix.ext fun r c => ?_
  show v = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v r c
  cases r with
  | inr r => exact r.elim0
  | inl r =>
    cases c with
    | inr c => exact c.elim0
    | inl c =>
      obtain rfl : r = 0 := Subsingleton.elim r 0
      obtain rfl : c = 0 := Subsingleton.elim c 0
      rw [Matrix.single_apply_same]

/-- `equivGradedTensor` on `t ᵍ⊗ 1`. -/
private theorem equivGradedTensor_tmul_one {A : Type*} [Ring A]
    [Algebra ℝ A] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (ε : ℝ)
    (t : A) :
    OddDouble.equivGradedTensor 𝒜 ε
        (GradedTensorProduct.tmul (𝒜 := 𝒜) (ℬ := AdjoinOdd.grading ε) ℝ t 1)
      = OddDouble.mk 𝒜 ε t 0 := by
  rw [OddDouble.equivGradedTensor_tmul, map_one, mul_one, OddDouble.inl_apply]

/-- `equivGradedTensor` on `t ᵍ⊗ e`. -/
private theorem equivGradedTensor_tmul_e {A : Type*} [Ring A]
    [Algebra ℝ A] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (ε : ℝ)
    (t : A) :
    OddDouble.equivGradedTensor 𝒜 ε
        (GradedTensorProduct.tmul (𝒜 := 𝒜) (ℬ := AdjoinOdd.grading ε) ℝ t
          (AdjoinOdd.e ε))
      = OddDouble.mk 𝒜 ε 0 t := by
  rw [OddDouble.equivGradedTensor_tmul, OddDouble.inl_apply, OddDouble.inr_e]
  refine OddDouble.ext 𝒜 ε ?_ ?_ <;> simp [parityMap_one]

private theorem gtensorUnitorLeft_one_tmul (P : SuperAlgebra ℝ)
    {jp : ZMod 2} {v : P.carrier} (hv : v ∈ P.grading jp) :
    (gtensorUnitorLeft P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := P.grading) ℝ (1 : ℝ) v) = v := by
  have hcomm := gtensorComm_tmul_of_mem (SuperAlgebra.base ℝ) P
    (show (1 : ℝ) ∈ (SuperAlgebra.base ℝ).grading 0 from
      mem_evenGrading_zero ℝ ℝ 1) hv
  rw [mul_zero, uzpow_zero, one_smul] at hcomm
  have hru := gunitorRightHom_tmul P.grading v (1 : ℝ)
  rw [map_one, mul_one] at hru
  show gunitorRightHom P.grading
      ((gtensorComm (SuperAlgebra.base ℝ) P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := P.grading) ℝ (1 : ℝ) v)) = v
  rw [hcomm]
  exact hru

private theorem gtensorUnitorRight_tmul_one (P : SuperAlgebra ℝ)
    (v : P.carrier) :
    (gtensorUnitorRight P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ v (1 : ℝ)) = v := by
  have h := gunitorRightHom_tmul P.grading v (1 : ℝ)
  rw [map_one, mul_one] at h
  exact h

/-- `D_ε ≅ T₁` sends the odd generator to the odd generator. -/
private theorem adjoinOddEquivTowerOne_e (ε : ℝ) :
    (adjoinOddEquivTowerOne ε).toAlgEquiv (AdjoinOdd.e ε)
      = OddDouble.gen (SuperAlgebra.base ℝ).grading ε := by
  have hin : ((gtensorUnitorLeft (SuperAlgebra.adjoinOdd ε)).toAlgEquiv).symm
        (AdjoinOdd.e ε)
      = GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := (SuperAlgebra.adjoinOdd ε).grading) ℝ (1 : ℝ)
          (AdjoinOdd.e ε) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (gtensorUnitorLeft_one_tmul (SuperAlgebra.adjoinOdd ε)
      (AdjoinOdd.e_mem_grading_one ε)).symm
  show OddDouble.equivGradedTensor (SuperAlgebra.base ℝ).grading ε
      (((gtensorUnitorLeft (SuperAlgebra.adjoinOdd ε)).toAlgEquiv).symm
        (AdjoinOdd.e ε))
      = OddDouble.gen (SuperAlgebra.base ℝ).grading ε
  rw [hin]
  exact equivGradedTensor_tmul_e (SuperAlgebra.base ℝ).grading ε (1 : ℝ)

/-- The inverse tower step on `t ᵍ⊗ 1`. -/
private theorem towerSuccEquiv_symm_tmul_one (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).symm.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk (divisionTower ε n).grading ε t 0 := by
  have hin : (OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
        (OddDouble.mk (divisionTower ε n).grading ε t 0)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (SuperAlgebra.adjoinOdd ε).grading) ℝ t
          (1 : (SuperAlgebra.adjoinOdd ε).carrier) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (equivGradedTensor_tmul_one (divisionTower ε n).grading ε t).symm
  have hone : (adjoinOddEquivTowerOne ε).toAlgEquiv
      (1 : (SuperAlgebra.adjoinOdd ε).carrier) = 1 := map_one _
  have happ := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε n)) (adjoinOddEquivTowerOne ε)
    t (1 : (SuperAlgebra.adjoinOdd ε).carrier)
  rw [superRefl_apply, hone] at happ
  show ((towerSuccEquiv ε n).toAlgEquiv).symm
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk (divisionTower ε n).grading ε t 0
  rw [AlgEquiv.symm_apply_eq]
  show GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (1 : (divisionTower ε 1).carrier)
      = ((SuperAlgEquiv.refl (divisionTower ε n)).gtensorCongr
          (adjoinOddEquivTowerOne ε)).toAlgEquiv
        ((OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
          (OddDouble.mk (divisionTower ε n).grading ε t 0))
  rw [hin, happ]

/-- The inverse tower step on `t ᵍ⊗ g`. -/
private theorem towerSuccEquiv_symm_tmul_gen (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).symm.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = OddDouble.mk (divisionTower ε n).grading ε 0 t := by
  have hin : (OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
        (OddDouble.mk (divisionTower ε n).grading ε 0 t)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (SuperAlgebra.adjoinOdd ε).grading) ℝ t
          (AdjoinOdd.e ε) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (equivGradedTensor_tmul_e (divisionTower ε n).grading ε t).symm
  have happ := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε n)) (adjoinOddEquivTowerOne ε)
    t (AdjoinOdd.e ε)
  rw [superRefl_apply, adjoinOddEquivTowerOne_e] at happ
  show ((towerSuccEquiv ε n).toAlgEquiv).symm
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = OddDouble.mk (divisionTower ε n).grading ε 0 t
  rw [AlgEquiv.symm_apply_eq]
  show GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
      = ((SuperAlgEquiv.refl (divisionTower ε n)).gtensorCongr
          (adjoinOddEquivTowerOne ε)).toAlgEquiv
        ((OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
          (OddDouble.mk (divisionTower ε n).grading ε 0 t))
  rw [hin, happ]

/-- Forward tower step on the `A`-coordinate. -/
private theorem towerSuccEquiv_mk_left (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).toAlgEquiv
        (OddDouble.mk (divisionTower ε n).grading ε t 0)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (1 : (divisionTower ε 1).carrier) := by
  have h := towerSuccEquiv_symm_tmul_one ε n t
  exact ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε n).toAlgEquiv)).mp h).symm

/-- Forward tower step on the `A·g`-coordinate. -/
private theorem towerSuccEquiv_mk_right (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).toAlgEquiv
        (OddDouble.mk (divisionTower ε n).grading ε 0 t)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) := by
  have h := towerSuccEquiv_symm_tmul_gen ε n t
  exact ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε n).toAlgEquiv)).mp h).symm

/-- The associator inverse on nested pure tensors. -/
private theorem gtensorAssoc_symm_tmul (P Q R : SuperAlgebra ℝ)
    (x : P.carrier) (y : Q.carrier) (z : R.carrier) :
    (gtensorAssoc P Q R).symm.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (Q.gtensor R).grading) ℝ x
          (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := R.grading) ℝ y z))
      = GradedTensorProduct.tmul (𝒜 := (P.gtensor Q).grading)
          (ℬ := R.grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y)
          z := by
  show ((gtensorAssoc P Q R).toAlgEquiv).symm
      (GradedTensorProduct.tmul (𝒜 := P.grading)
        (ℬ := (Q.gtensor R).grading) ℝ x
        (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := R.grading) ℝ y z))
      = GradedTensorProduct.tmul (𝒜 := (P.gtensor Q).grading)
          (ℬ := R.grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y)
          z
  rw [AlgEquiv.symm_apply_eq]
  exact (gtensorAssoc_tmul P Q R x y z).symm

/-! ### The generic tower-fusion index map: sign-free -/

private theorem towerFuse_index_lt (a b : ℕ) (i : Fin (2 ^ a))
    (j : Fin (2 ^ b)) : (i : ℕ) + 2 ^ a * (j : ℕ) < 2 ^ (a + b) := by
  have hi := i.isLt
  have hj := j.isLt
  have h : (j : ℕ) + 1 ≤ 2 ^ b := hj
  calc (i : ℕ) + 2 ^ a * (j : ℕ) < 2 ^ a + 2 ^ a * (j : ℕ) := by omega
    _ = 2 ^ a * ((j : ℕ) + 1) := by ring
    _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_left _ h
    _ = 2 ^ (a + b) := (pow_add 2 a b).symm

/-- **The tower fusion is a sign-free permutation on the canonical
bases**: `e_i ᵍ⊗ e_j ↦ e_{i + 2^a j}`, generic in `ε`, `a`, `b`. -/
private theorem towerFuse_basis (ε : ℝ) (a b : ℕ) (i : Fin (2 ^ a))
    (j : Fin (2 ^ b)) :
    (towerFuse ε a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε b).grading) ℝ
          (towerBasis ε a i) (towerBasis ε b j))
      = towerBasis ε (a + b)
          ⟨(i : ℕ) + 2 ^ a * (j : ℕ), towerFuse_index_lt a b i j⟩ := by
  induction b with
  | zero =>
      have hj : towerBasis ε 0 j = (1 : ℝ) := towerBasis_zero_apply ε j
      have h0 : (j : ℕ) = 0 := by omega
      have hidx : (⟨(i : ℕ) + 2 ^ a * (j : ℕ),
          towerFuse_index_lt a 0 i j⟩ : Fin (2 ^ (a + 0))) = i := by
        refine Fin.ext ?_
        show (i : ℕ) + 2 ^ a * (j : ℕ) = (i : ℕ)
        rw [h0, mul_zero, add_zero]
      rw [hj, hidx]
      exact gtensorUnitorRight_tmul_one (divisionTower ε a) (towerBasis ε a i)
  | succ b IH =>
      rcases Nat.lt_or_ge (j : ℕ) (2 ^ b) with hlow | hhigh
      · -- low block: `e_j = (e_{j'}, 0)`
        set j' : Fin (2 ^ b) := ⟨(j : ℕ), hlow⟩
        have hj : j = ⟨(j' : ℕ), towerIndexLow_lt b j'⟩ := Fin.ext rfl
        have hbasis := towerBasis_low ε b j'
        have h1 := SuperAlgEquiv.gtensorCongr_tmul
          (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε b)
          (towerBasis ε a i)
          (OddDouble.mk (divisionTower ε b).grading ε (towerBasis ε b j') 0)
        rw [superRefl_apply, towerSuccEquiv_mk_left] at h1
        have h2 := gtensorAssoc_symm_tmul (divisionTower ε a)
          (divisionTower ε b) (divisionTower ε 1)
          (towerBasis ε a i) (towerBasis ε b j')
          (1 : (divisionTower ε 1).carrier)
        have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a b)
          (SuperAlgEquiv.refl (divisionTower ε 1))
          (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
            (ℬ := (divisionTower ε b).grading) ℝ
            (towerBasis ε a i) (towerBasis ε b j'))
          (1 : (divisionTower ε 1).carrier)
        rw [superRefl_apply, IH j'] at h3
        have h4 := towerSuccEquiv_symm_tmul_one ε (a + b)
          (towerBasis ε (a + b)
            ⟨(i : ℕ) + 2 ^ a * (j' : ℕ), towerFuse_index_lt a b i j'⟩)
        have e1 : (towerFuse ε a (b + 1)).toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
              (ℬ := (divisionTower ε (b + 1)).grading) ℝ
              (towerBasis ε a i) (towerBasis ε (b + 1) j))
            = (towerSuccEquiv ε (a + b)).symm.toAlgEquiv
                (((towerFuse ε a b).gtensorCongr
                    (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
                  ((gtensorAssoc (divisionTower ε a) (divisionTower ε b)
                      (divisionTower ε 1)).symm.toAlgEquiv
                    (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                        (towerSuccEquiv ε b)).toAlgEquiv
                      (GradedTensorProduct.tmul
                        (𝒜 := (divisionTower ε a).grading)
                        (ℬ := (divisionTower ε (b + 1)).grading) ℝ
                        (towerBasis ε a i) (towerBasis ε (b + 1) j))))) := rfl
        rw [hj, hbasis] at e1
        rw [h1, h2, h3, h4] at e1
        have hlowidx := towerBasis_low ε (a + b)
          ⟨(i : ℕ) + 2 ^ a * (j' : ℕ), towerFuse_index_lt a b i j'⟩
        rw [← hlowidx] at e1
        conv_lhs => rw [hj, hbasis]
        refine e1.trans (congrArg (towerBasis ε (a + b + 1)) (Fin.ext ?_))
        show (i : ℕ) + 2 ^ a * (j : ℕ) = (i : ℕ) + 2 ^ a * (j : ℕ)
        rfl
      · -- high block: `e_j = (0, e_{j'})`
        obtain ⟨t, htlt, htval⟩ : ∃ t, t < 2 ^ b ∧ (j : ℕ) = 2 ^ b + t := by
          refine ⟨(j : ℕ) - 2 ^ b, ?_, ?_⟩
          · have h1 := j.isLt
            have h2 := two_pow_add_self b
            omega
          · omega
        set j' : Fin (2 ^ b) := ⟨t, htlt⟩
        have hj : j = ⟨2 ^ b + (j' : ℕ), towerIndexHigh_lt b j'⟩ :=
          Fin.ext htval
        have hbasis := towerBasis_high ε b j'
        have h1 := SuperAlgEquiv.gtensorCongr_tmul
          (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε b)
          (towerBasis ε a i)
          (OddDouble.mk (divisionTower ε b).grading ε 0 (towerBasis ε b j'))
        rw [superRefl_apply, towerSuccEquiv_mk_right] at h1
        have h2 := gtensorAssoc_symm_tmul (divisionTower ε a)
          (divisionTower ε b) (divisionTower ε 1)
          (towerBasis ε a i) (towerBasis ε b j')
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
        have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a b)
          (SuperAlgEquiv.refl (divisionTower ε 1))
          (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
            (ℬ := (divisionTower ε b).grading) ℝ
            (towerBasis ε a i) (towerBasis ε b j'))
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
        rw [superRefl_apply, IH j'] at h3
        have h4 := towerSuccEquiv_symm_tmul_gen ε (a + b)
          (towerBasis ε (a + b)
            ⟨(i : ℕ) + 2 ^ a * (j' : ℕ), towerFuse_index_lt a b i j'⟩)
        have e1 : (towerFuse ε a (b + 1)).toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
              (ℬ := (divisionTower ε (b + 1)).grading) ℝ
              (towerBasis ε a i) (towerBasis ε (b + 1) j))
            = (towerSuccEquiv ε (a + b)).symm.toAlgEquiv
                (((towerFuse ε a b).gtensorCongr
                    (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
                  ((gtensorAssoc (divisionTower ε a) (divisionTower ε b)
                      (divisionTower ε 1)).symm.toAlgEquiv
                    (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                        (towerSuccEquiv ε b)).toAlgEquiv
                      (GradedTensorProduct.tmul
                        (𝒜 := (divisionTower ε a).grading)
                        (ℬ := (divisionTower ε (b + 1)).grading) ℝ
                        (towerBasis ε a i) (towerBasis ε (b + 1) j))))) := rfl
        rw [hj, hbasis] at e1
        rw [h1, h2, h3, h4] at e1
        have hhighidx := towerBasis_high ε (a + b)
          ⟨(i : ℕ) + 2 ^ a * (j' : ℕ), towerFuse_index_lt a b i j'⟩
        rw [← hhighidx] at e1
        conv_lhs => rw [hj, hbasis]
        refine e1.trans (congrArg (towerBasis ε (a + b + 1)) (Fin.ext ?_))
        show 2 ^ (a + b) + ((i : ℕ) + 2 ^ a * t) = (i : ℕ) + 2 ^ a * (j : ℕ)
        rw [htval, pow_add]
        ring
/-! ### Atoms: the tower basis elements as carrier-typed constants -/

section Atoms

variable (ε : ℝ)

private noncomputable def q1 (ε : ℝ) : (divisionTower ε 1).carrier :=
  OddDouble.gen (SuperAlgebra.base ℝ).grading ε

private noncomputable def qE1 (ε : ℝ) : (divisionTower ε 2).carrier :=
  OddDouble.mk (divisionTower ε 1).grading ε (q1 ε) 0

private noncomputable def qE2 (ε : ℝ) : (divisionTower ε 2).carrier :=
  OddDouble.mk (divisionTower ε 1).grading ε 0 (1 : (divisionTower ε 1).carrier)

private noncomputable def qE3 (ε : ℝ) : (divisionTower ε 2).carrier :=
  OddDouble.mk (divisionTower ε 1).grading ε 0 (q1 ε)

private noncomputable def qF1 (ε : ℝ) : (divisionTower ε 3).carrier :=
  OddDouble.mk (divisionTower ε 2).grading ε (qE1 ε) 0

private noncomputable def qF2 (ε : ℝ) : (divisionTower ε 3).carrier :=
  OddDouble.mk (divisionTower ε 2).grading ε (qE2 ε) 0

private noncomputable def qF3 (ε : ℝ) : (divisionTower ε 3).carrier :=
  OddDouble.mk (divisionTower ε 2).grading ε (qE3 ε) 0

private noncomputable def qF4 (ε : ℝ) : (divisionTower ε 3).carrier :=
  OddDouble.mk (divisionTower ε 2).grading ε 0 (1 : (divisionTower ε 2).carrier)

private noncomputable def qF5 (ε : ℝ) : (divisionTower ε 3).carrier :=
  OddDouble.mk (divisionTower ε 2).grading ε 0 (qE1 ε)

private noncomputable def qF6 (ε : ℝ) : (divisionTower ε 3).carrier :=
  OddDouble.mk (divisionTower ε 2).grading ε 0 (qE2 ε)

private noncomputable def qF7 (ε : ℝ) : (divisionTower ε 3).carrier :=
  OddDouble.mk (divisionTower ε 2).grading ε 0 (qE3 ε)

private noncomputable def qG1 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε (qF1 ε) 0

private noncomputable def qG2 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε (qF2 ε) 0

private noncomputable def qG3 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε (qF3 ε) 0

private noncomputable def qG4 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε (qF4 ε) 0

private noncomputable def qG5 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε (qF5 ε) 0

private noncomputable def qG6 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε (qF6 ε) 0

private noncomputable def qG7 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε (qF7 ε) 0

private noncomputable def qG8 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (1 : (divisionTower ε 3).carrier)

private noncomputable def qG9 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (qF1 ε)

private noncomputable def qG10 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (qF2 ε)

private noncomputable def qG11 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (qF3 ε)

private noncomputable def qG12 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (qF4 ε)

private noncomputable def qG13 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (qF5 ε)

private noncomputable def qG14 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (qF6 ε)

private noncomputable def qG15 (ε : ℝ) : (divisionTower ε 4).carrier :=
  OddDouble.mk (divisionTower ε 3).grading ε 0 (qF7 ε)

private theorem q1_def : q1 ε = OddDouble.gen (SuperAlgebra.base ℝ).grading ε := rfl

private theorem qE1_def : qE1 ε = OddDouble.mk (divisionTower ε 1).grading ε (q1 ε) 0 := rfl

private theorem qE2_def : qE2 ε = OddDouble.mk (divisionTower ε 1).grading ε 0 (1 : (divisionTower ε 1).carrier) := rfl

private theorem qE3_def : qE3 ε = OddDouble.mk (divisionTower ε 1).grading ε 0 (q1 ε) := rfl

private theorem qF1_def : qF1 ε = OddDouble.mk (divisionTower ε 2).grading ε (qE1 ε) 0 := rfl

private theorem qF2_def : qF2 ε = OddDouble.mk (divisionTower ε 2).grading ε (qE2 ε) 0 := rfl

private theorem qF3_def : qF3 ε = OddDouble.mk (divisionTower ε 2).grading ε (qE3 ε) 0 := rfl

private theorem qF4_def : qF4 ε = OddDouble.mk (divisionTower ε 2).grading ε 0 (1 : (divisionTower ε 2).carrier) := rfl

private theorem qF5_def : qF5 ε = OddDouble.mk (divisionTower ε 2).grading ε 0 (qE1 ε) := rfl

private theorem qF6_def : qF6 ε = OddDouble.mk (divisionTower ε 2).grading ε 0 (qE2 ε) := rfl

private theorem qF7_def : qF7 ε = OddDouble.mk (divisionTower ε 2).grading ε 0 (qE3 ε) := rfl

private theorem qG1_def : qG1 ε = OddDouble.mk (divisionTower ε 3).grading ε (qF1 ε) 0 := rfl

private theorem qG2_def : qG2 ε = OddDouble.mk (divisionTower ε 3).grading ε (qF2 ε) 0 := rfl

private theorem qG3_def : qG3 ε = OddDouble.mk (divisionTower ε 3).grading ε (qF3 ε) 0 := rfl

private theorem qG4_def : qG4 ε = OddDouble.mk (divisionTower ε 3).grading ε (qF4 ε) 0 := rfl

private theorem qG5_def : qG5 ε = OddDouble.mk (divisionTower ε 3).grading ε (qF5 ε) 0 := rfl

private theorem qG6_def : qG6 ε = OddDouble.mk (divisionTower ε 3).grading ε (qF6 ε) 0 := rfl

private theorem qG7_def : qG7 ε = OddDouble.mk (divisionTower ε 3).grading ε (qF7 ε) 0 := rfl

private theorem qG8_def : qG8 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (1 : (divisionTower ε 3).carrier) := rfl

private theorem qG9_def : qG9 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (qF1 ε) := rfl

private theorem qG10_def : qG10 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (qF2 ε) := rfl

private theorem qG11_def : qG11 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (qF3 ε) := rfl

private theorem qG12_def : qG12 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (qF4 ε) := rfl

private theorem qG13_def : qG13 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (qF5 ε) := rfl

private theorem qG14_def : qG14 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (qF6 ε) := rfl

private theorem qG15_def : qG15 ε = OddDouble.mk (divisionTower ε 3).grading ε 0 (qF7 ε) := rfl

end Atoms

/-! ### Floor-`1` square rule -/

section FloorRules

variable (ε : ℝ)

/-- `g₁² = ε`, at the bundled floor-`1` instances. -/
private theorem t1sq :
    (q1 ε * q1 ε : (divisionTower ε 1).carrier)
    = algebraMap ℝ (divisionTower ε 1).carrier ε :=
  OddDouble.gen_mul_gen (SuperAlgebra.base ℝ).grading ε

end FloorRules

/-! ### The tower basis dictionary, floors `1`–`4` -/

section TowerDict

variable (ε : ℝ)

private theorem tb1_0 : towerBasis ε 1 0 = (1 : (divisionTower ε 1).carrier) := by
  have h := towerBasis_low ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

private theorem tb1_1 : towerBasis ε 1 1 = q1 ε := by
  have h := towerBasis_high ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

private theorem tb2_0 : towerBasis ε 2 0 = (1 : (divisionTower ε 2).carrier) := by
  have h := towerBasis_low ε 1 0
  rw [tb1_0] at h
  exact h

private theorem tb2_1 : towerBasis ε 2 1 = (qE1 ε) := by
  have h := towerBasis_low ε 1 1
  rw [tb1_1] at h
  exact h

private theorem tb2_2 : towerBasis ε 2 2 = (qE2 ε) := by
  have h := towerBasis_high ε 1 0
  rw [tb1_0] at h
  exact h

private theorem tb2_3 : towerBasis ε 2 3 = (qE3 ε) := by
  have h := towerBasis_high ε 1 1
  rw [tb1_1] at h
  exact h

private theorem tb3_0 : towerBasis ε 3 0 = (1 : (divisionTower ε 3).carrier) := by
  have h := towerBasis_low ε 2 0
  rw [tb2_0] at h
  exact h

private theorem tb3_1 : towerBasis ε 3 1 = (qF1 ε) := by
  have h := towerBasis_low ε 2 1
  rw [tb2_1] at h
  exact h

private theorem tb3_2 : towerBasis ε 3 2 = (qF2 ε) := by
  have h := towerBasis_low ε 2 2
  rw [tb2_2] at h
  exact h

private theorem tb3_3 : towerBasis ε 3 3 = (qF3 ε) := by
  have h := towerBasis_low ε 2 3
  rw [tb2_3] at h
  exact h

private theorem tb3_4 : towerBasis ε 3 4 = (qF4 ε) := by
  have h := towerBasis_high ε 2 0
  rw [tb2_0] at h
  exact h

private theorem tb3_5 : towerBasis ε 3 5 = (qF5 ε) := by
  have h := towerBasis_high ε 2 1
  rw [tb2_1] at h
  exact h

private theorem tb3_6 : towerBasis ε 3 6 = (qF6 ε) := by
  have h := towerBasis_high ε 2 2
  rw [tb2_2] at h
  exact h

private theorem tb3_7 : towerBasis ε 3 7 = (qF7 ε) := by
  have h := towerBasis_high ε 2 3
  rw [tb2_3] at h
  exact h

private theorem tb4_0 : towerBasis ε 4 0 = (1 : (divisionTower ε 4).carrier) := by
  have h := towerBasis_low ε 3 0
  rw [tb3_0] at h
  exact h

private theorem tb4_1 : towerBasis ε 4 1 = qG1 ε := by
  have h := towerBasis_low ε 3 1
  rw [tb3_1] at h
  exact h

private theorem tb4_2 : towerBasis ε 4 2 = qG2 ε := by
  have h := towerBasis_low ε 3 2
  rw [tb3_2] at h
  exact h

private theorem tb4_3 : towerBasis ε 4 3 = qG3 ε := by
  have h := towerBasis_low ε 3 3
  rw [tb3_3] at h
  exact h

private theorem tb4_4 : towerBasis ε 4 4 = qG4 ε := by
  have h := towerBasis_low ε 3 4
  rw [tb3_4] at h
  exact h

private theorem tb4_5 : towerBasis ε 4 5 = qG5 ε := by
  have h := towerBasis_low ε 3 5
  rw [tb3_5] at h
  exact h

private theorem tb4_6 : towerBasis ε 4 6 = qG6 ε := by
  have h := towerBasis_low ε 3 6
  rw [tb3_6] at h
  exact h

private theorem tb4_7 : towerBasis ε 4 7 = qG7 ε := by
  have h := towerBasis_low ε 3 7
  rw [tb3_7] at h
  exact h

private theorem tb4_8 : towerBasis ε 4 8 = qG8 ε := by
  have h := towerBasis_high ε 3 0
  rw [tb3_0] at h
  exact h

private theorem tb4_9 : towerBasis ε 4 9 = qG9 ε := by
  have h := towerBasis_high ε 3 1
  rw [tb3_1] at h
  exact h

private theorem tb4_10 : towerBasis ε 4 10 = qG10 ε := by
  have h := towerBasis_high ε 3 2
  rw [tb3_2] at h
  exact h

private theorem tb4_11 : towerBasis ε 4 11 = qG11 ε := by
  have h := towerBasis_high ε 3 3
  rw [tb3_3] at h
  exact h

private theorem tb4_12 : towerBasis ε 4 12 = qG12 ε := by
  have h := towerBasis_high ε 3 4
  rw [tb3_4] at h
  exact h

private theorem tb4_13 : towerBasis ε 4 13 = qG13 ε := by
  have h := towerBasis_high ε 3 5
  rw [tb3_5] at h
  exact h

private theorem tb4_14 : towerBasis ε 4 14 = qG14 ε := by
  have h := towerBasis_high ε 3 6
  rw [tb3_6] at h
  exact h

private theorem tb4_15 : towerBasis ε 4 15 = qG15 ε := by
  have h := towerBasis_high ε 3 7
  rw [tb3_7] at h
  exact h

end TowerDict

/-! ### Parity-involution values on the low floors -/

section ParityDict

variable (ε : ℝ)

private theorem mem_q1 : q1 ε ∈ (divisionTower ε 1).grading 1 :=
  OddDouble.gen_mem_grading (SuperAlgebra.base ℝ).grading ε

private theorem pm_q1 : parityMap (divisionTower ε 1).grading (q1 ε) = -(q1 ε) :=
  parityMap_of_mem_one (divisionTower ε 1).grading (mem_q1 ε)

private theorem mem_qE3 : qE3 ε ∈ (divisionTower ε 2).grading 0 :=
  OddDouble.mk_mem_grading (divisionTower ε 1).grading ε (zero_mem _) (mem_q1 ε)

private theorem pm_qE3 : parityMap (divisionTower ε 2).grading (qE3 ε) = qE3 ε :=
  parityMap_of_mem_zero (divisionTower ε 2).grading (mem_qE3 ε)

end ParityDict

/-! ### Product values on the atoms -/

section ProdDict

variable (ε : ℝ)

private theorem prodE1E2 : qE1 ε * qE2 ε = qE3 ε := by
  show OddDouble.mk (divisionTower ε 1).grading ε (q1 ε) 0 * OddDouble.mk (divisionTower ε 1).grading ε 0 (1 : (divisionTower ε 1).carrier) = qE3 ε
  rw [mkA_mul_mkB, mul_one]
  exact rfl

private theorem prodE3E3 (hε2 : ε * ε = 1) : qE3 ε * qE3 ε = -(1 : (divisionTower ε 2).carrier) := by
  show OddDouble.mk (divisionTower ε 1).grading ε 0 (q1 ε) * OddDouble.mk (divisionTower ε 1).grading ε 0 (q1 ε) = -(1 : (divisionTower ε 2).carrier)
  rw [mkB_mul_mkB, pm_q1, mul_neg, t1sq, Algebra.algebraMap_eq_smul_one,
    smul_neg, smul_smul, hε2, one_smul, mkA_neg]
  exact rfl

private theorem prodE2E3 : qE2 ε * qE3 ε = -(ε • qE1 ε) := by
  show OddDouble.mk (divisionTower ε 1).grading ε 0 (1 : (divisionTower ε 1).carrier) * OddDouble.mk (divisionTower ε 1).grading ε 0 (q1 ε) = -(ε • qE1 ε)
  rw [mkB_mul_mkB, pm_q1, one_mul, smul_neg, mkA_neg, smul_mkA]
  exact rfl

private theorem prodE3E2 : qE3 ε * qE2 ε = ε • qE1 ε := by
  show OddDouble.mk (divisionTower ε 1).grading ε 0 (q1 ε) * OddDouble.mk (divisionTower ε 1).grading ε 0 (1 : (divisionTower ε 1).carrier) = ε • qE1 ε
  rw [mkB_mul_mkB, parityMap_one, mul_one, smul_mkA]
  exact rfl

private theorem prodE1E3 : qE1 ε * qE3 ε = ε • qE2 ε := by
  show OddDouble.mk (divisionTower ε 1).grading ε (q1 ε) 0 * OddDouble.mk (divisionTower ε 1).grading ε 0 (q1 ε) = ε • qE2 ε
  rw [mkA_mul_mkB, t1sq, Algebra.algebraMap_eq_smul_one, smul_mkB]
  exact rfl

private theorem prodF1F2 : qF1 ε * qF2 ε = qF3 ε := by
  show OddDouble.mk (divisionTower ε 2).grading ε (qE1 ε) 0 * OddDouble.mk (divisionTower ε 2).grading ε (qE2 ε) 0 = qF3 ε
  rw [mkA_mul_mkA, prodE1E2]
  exact rfl

private theorem prodF2F4 : qF2 ε * qF4 ε = qF6 ε := by
  show OddDouble.mk (divisionTower ε 2).grading ε (qE2 ε) 0 * OddDouble.mk (divisionTower ε 2).grading ε 0 (1 : (divisionTower ε 2).carrier) = qF6 ε
  rw [mkA_mul_mkB, mul_one]
  exact rfl

private theorem prodF3F4 : qF3 ε * qF4 ε = qF7 ε := by
  show OddDouble.mk (divisionTower ε 2).grading ε (qE3 ε) 0 * OddDouble.mk (divisionTower ε 2).grading ε 0 (1 : (divisionTower ε 2).carrier) = qF7 ε
  rw [mkA_mul_mkB, mul_one]
  exact rfl

private theorem prodF3F6 : qF3 ε * qF6 ε = ε • qF5 ε := by
  show OddDouble.mk (divisionTower ε 2).grading ε (qE3 ε) 0 * OddDouble.mk (divisionTower ε 2).grading ε 0 (qE2 ε) = ε • qF5 ε
  rw [mkA_mul_mkB, prodE3E2 ε, smul_mkB]
  exact rfl

private theorem prodF3F7 (hε2 : ε * ε = 1) : qF3 ε * qF7 ε = -(qF4 ε) := by
  show OddDouble.mk (divisionTower ε 2).grading ε (qE3 ε) 0 * OddDouble.mk (divisionTower ε 2).grading ε 0 (qE3 ε) = -(qF4 ε)
  rw [mkA_mul_mkB, prodE3E3 ε hε2, mkB_neg]
  exact rfl

private theorem prodF6F7 (hε2 : ε * ε = 1) : qF6 ε * qF7 ε = -(qF1 ε) := by
  show OddDouble.mk (divisionTower ε 2).grading ε 0 (qE2 ε) * OddDouble.mk (divisionTower ε 2).grading ε 0 (qE3 ε) = -(qF1 ε)
  rw [mkB_mul_mkB, pm_qE3, prodE2E3 ε, smul_neg, smul_smul, hε2, one_smul,
    mkA_neg]
  exact rfl

private theorem prodF5F7 (hε2 : ε * ε = 1) : qF5 ε * qF7 ε = qF2 ε := by
  show OddDouble.mk (divisionTower ε 2).grading ε 0 (qE1 ε) * OddDouble.mk (divisionTower ε 2).grading ε 0 (qE3 ε) = qF2 ε
  rw [mkB_mul_mkB, pm_qE3, prodE1E3 ε, smul_smul, hε2, one_smul]
  exact rfl

end ProdDict

/-! ### The Clifford value dictionary -/

section CliffDict

variable (ε : ℝ)

private theorem cliffG1_val : cliffG1 ε = qF1 ε := rfl

private theorem cliffG2_val : cliffG2 ε = qF2 ε := rfl

private theorem cliffG3_val : cliffG3 ε = qF4 ε := rfl

/-- `I = g₁g₂` is the third floor-`3` basis vector. -/
private theorem cliffI_val : cliffI ε = qF3 ε := by
  show cliffG1 ε * cliffG2 ε = qF3 ε
  rw [cliffG1_val, cliffG2_val]
  exact prodF1F2 ε

/-- `J = g₂g₃` is the sixth floor-`3` basis vector. -/
private theorem cliffJ_val : cliffJ ε = qF6 ε := by
  show cliffG2 ε * cliffG3 ε = qF6 ε
  rw [cliffG2_val, cliffG3_val]
  exact prodF2F4 ε

/-- `K = I·J = ε·g₁g₃`. -/
private theorem cliffK_val : cliffI ε * cliffJ ε = ε • qF5 ε := by
  rw [cliffI_val, cliffJ_val]
  exact prodF3F6 ε

/-- `ω = g₁g₂g₃` is the last floor-`3` basis vector. -/
private theorem cliffOmega_val : cliffOmega ε = qF7 ε := by
  show cliffG1 ε * cliffG2 ε * cliffG3 ε = qF7 ε
  rw [show cliffG1 ε * cliffG2 ε = cliffI ε from rfl, cliffI_val, cliffG3_val]
  exact prodF3F4 ε

end CliffDict
/-! ### Quaternion basis vectors, explicitly -/

private theorem quatBasis_zero : quatBasis 0 = (1 : ℍ[ℝ]) := by
  rw [Basis.apply_eq_iff]
  refine Finsupp.ext fun e => ?_
  show (![(1 : ℝ), 0, 0, 0]) e = (Finsupp.single (0 : Fin 4) (1 : ℝ)) e
  fin_cases e <;> simp

private theorem quatBasis_one : quatBasis 1 = (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
  rw [Basis.apply_eq_iff]
  refine Finsupp.ext fun e => ?_
  show (![(0 : ℝ), 1, 0, 0]) e = (Finsupp.single (1 : Fin 4) (1 : ℝ)) e
  fin_cases e <;> simp

private theorem quatBasis_two : quatBasis 2 = (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) := by
  rw [Basis.apply_eq_iff]
  refine Finsupp.ext fun e => ?_
  show (![(0 : ℝ), 0, 1, 0]) e = (Finsupp.single (2 : Fin 4) (1 : ℝ)) e
  fin_cases e <;> simp

private theorem quatBasis_three : quatBasis 3 = (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by
  rw [Basis.apply_eq_iff]
  refine Finsupp.ext fun e => ?_
  show (![(0 : ℝ), 0, 0, 1]) e = (Finsupp.single (3 : Fin 4) (1 : ℝ)) e
  fin_cases e <;> simp

/-! ### `cliffPhi` values on the quaternion basis -/

section PhiVals

variable (ε : ℝ) (hε2 : ε * ε = 1)

private theorem cliffPhi_e0 : cliffPhi ε hε2 (quatBasis 0) = 1 := by
  rw [quatBasis_zero]
  exact map_one _

private theorem cliffPhi_e1 : cliffPhi ε hε2 (quatBasis 1) = qF3 ε := by
  rw [quatBasis_one]
  show algebraMap ℝ (divisionTower ε 3).carrier (0 : ℝ)
      + (1 : ℝ) • (cliffQuatBasis ε hε2).i + (0 : ℝ) • (cliffQuatBasis ε hε2).j
      + (0 : ℝ) • (cliffQuatBasis ε hε2).k = qF3 ε
  simp only [map_zero, zero_add, one_smul, zero_smul, add_zero]
  exact cliffI_val ε

private theorem cliffPhi_e2 : cliffPhi ε hε2 (quatBasis 2) = qF6 ε := by
  rw [quatBasis_two]
  show algebraMap ℝ (divisionTower ε 3).carrier (0 : ℝ)
      + (0 : ℝ) • (cliffQuatBasis ε hε2).i + (1 : ℝ) • (cliffQuatBasis ε hε2).j
      + (0 : ℝ) • (cliffQuatBasis ε hε2).k = qF6 ε
  simp only [map_zero, zero_add, one_smul, zero_smul, add_zero]
  exact cliffJ_val ε

private theorem cliffPhi_e3 : cliffPhi ε hε2 (quatBasis 3) = ε • qF5 ε := by
  rw [quatBasis_three]
  show algebraMap ℝ (divisionTower ε 3).carrier (0 : ℝ)
      + (0 : ℝ) • (cliffQuatBasis ε hε2).i + (0 : ℝ) • (cliffQuatBasis ε hε2).j
      + (1 : ℝ) • (cliffQuatBasis ε hε2).k = ε • qF5 ε
  simp only [map_zero, zero_add, one_smul, zero_smul, add_zero]
  exact cliffK_val ε

end PhiVals

/-! ### `cliffThetaEquiv` on the two coordinates -/

section ThetaVals

variable (ε : ℝ) (hε2 : ε * ε = 1)

private theorem cliffTheta_hconj' (x : ℍ[ℝ]) :
    cliffOmega ε * cliffPhi ε hε2 x
      = cliffPhi ε hε2 (parityMap quatEvenSuper.grading x) * cliffOmega ε := by
  rw [show parityMap quatEvenSuper.grading x = x from
    parityMap_of_mem_zero (evenGrading ℝ ℍ[ℝ]) (mem_evenGrading_zero ℝ ℍ[ℝ] x)]
  exact cliffOmega_commute_cliffPhi ε hε2 x

private theorem cliffThetaEquiv_mk_left (x : ℍ[ℝ]) :
    (cliffThetaEquiv ε hε2).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-ε) x 0) = cliffPhi ε hε2 x := by
  show cliffTheta ε hε2 (OddDouble.mk quatEvenSuper.grading (-ε) x 0)
      = cliffPhi ε hε2 x
  exact OddDouble.lift_inl quatEvenSuper.grading (-ε) (cliffPhi ε hε2)
    (cliffOmega ε) (cliffOmega_sq ε hε2) (cliffTheta_hconj' ε hε2) x

private theorem cliffThetaEquiv_mk_right (x : ℍ[ℝ]) :
    (cliffThetaEquiv ε hε2).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-ε) 0 x)
      = cliffPhi ε hε2 x * cliffOmega ε := by
  show cliffTheta ε hε2 (OddDouble.mk quatEvenSuper.grading (-ε) 0 x)
      = cliffPhi ε hε2 x * cliffOmega ε
  have h0 := OddDouble.lift_mk quatEvenSuper.grading (-ε) (cliffPhi ε hε2)
    (cliffOmega ε) (cliffOmega_sq ε hε2) (cliffTheta_hconj' ε hε2) 0 x
  rw [map_zero, zero_add] at h0
  exact h0

end ThetaVals

/-! ### The odd-double bridge on pure tensors -/

section OddBridge

private theorem adjoinOdd_hconj' (ε : ℝ) (a : ℝ) :
    AdjoinOdd.e ε * (Algebra.ofId ℝ (AdjoinOdd ε)) a
      = (Algebra.ofId ℝ (AdjoinOdd ε))
          (parityMap (SuperAlgebra.base ℝ).grading a) * AdjoinOdd.e ε := by
  rw [show parityMap (SuperAlgebra.base ℝ).grading a = a from
    parityMap_of_mem_zero (evenGrading ℝ ℝ) (mem_evenGrading_zero ℝ ℝ a)]
  simp only [Algebra.ofId_apply]
  exact (Algebra.commutes a (AdjoinOdd.e ε)).symm

private theorem divOne_gen (ε : ℝ) (hε : ε ≠ 0) :
    (divisionTowerOneEquivAdjoinOdd ε hε).toAlgEquiv (q1 ε) = AdjoinOdd.e ε := by
  show OddDouble.lift (SuperAlgebra.base ℝ).grading ε
      (Algebra.ofId ℝ (AdjoinOdd ε)) (AdjoinOdd.e ε) (AdjoinOdd.e_mul_e ε)
      (adjoinOdd_hconj' ε)
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) = AdjoinOdd.e ε
  exact OddDouble.lift_gen (SuperAlgebra.base ℝ).grading ε
    (Algebra.ofId ℝ (AdjoinOdd ε)) (AdjoinOdd.e ε) (AdjoinOdd.e_mul_e ε)
    (adjoinOdd_hconj' ε)

private theorem oddDoubleGDOne_tmul_one (P : SuperAlgebra ℝ) (ε : ℝ)
    (hε : ε ≠ 0) (x : P.carrier) :
    (oddDoubleGtensorDivisionOneEquiv ε P hε).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (divisionTower ε 1).grading) ℝ x
          (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk P.grading ε x 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl P)
    (divisionTowerOneEquivAdjoinOdd ε hε) x (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, map_one] at h1
  show (oddDoubleGtensorEquiv P ε).toAlgEquiv
      (((SuperAlgEquiv.refl P).gtensorCongr
          (divisionTowerOneEquivAdjoinOdd ε hε)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (divisionTower ε 1).grading) ℝ x
          (1 : (divisionTower ε 1).carrier)))
      = OddDouble.mk P.grading ε x 0
  rw [h1]
  exact equivGradedTensor_tmul_one P.grading ε x

private theorem oddDoubleGDOne_tmul_gen (P : SuperAlgebra ℝ) (ε : ℝ)
    (hε : ε ≠ 0) (x : P.carrier) :
    (oddDoubleGtensorDivisionOneEquiv ε P hε).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (divisionTower ε 1).grading) ℝ x (q1 ε))
      = OddDouble.mk P.grading ε 0 x := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl P)
    (divisionTowerOneEquivAdjoinOdd ε hε) x (q1 ε)
  rw [superRefl_apply, divOne_gen] at h1
  show (oddDoubleGtensorEquiv P ε).toAlgEquiv
      (((SuperAlgEquiv.refl P).gtensorCongr
          (divisionTowerOneEquivAdjoinOdd ε hε)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (divisionTower ε 1).grading) ℝ x (q1 ε)))
      = OddDouble.mk P.grading ε 0 x
  rw [h1]
  exact equivGradedTensor_tmul_e P.grading ε x

/-- Transporting the odd double along an `ε`-equality is the identity on
coordinates. -/
private theorem oddDouble_congr_eps_mk {P : SuperAlgebra ℝ} {ε ε' : ℝ}
    (h : ε = ε') (a b : P.carrier) :
    (oddDouble_congr_eps (P := P) h).toAlgEquiv (OddDouble.mk P.grading ε a b)
      = OddDouble.mk P.grading ε' a b := by
  subst h
  rfl

end OddBridge

/-! ### The `M_{1|0}(T₃)` frame vectors -/

section Dst3

variable (ε : ℝ)

private theorem dst3_0 : matrixSuperBasis (towerBasis ε 3) 1 0 0
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (1 : (divisionTower ε 3).carrier) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 0
  rw [tb3_0] at h
  exact h

private theorem dst3_1 : matrixSuperBasis (towerBasis ε 3) 1 0 1
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (qF1 ε) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 1
  rw [tb3_1] at h
  exact h

private theorem dst3_2 : matrixSuperBasis (towerBasis ε 3) 1 0 2
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (qF2 ε) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 2
  rw [tb3_2] at h
  exact h

private theorem dst3_3 : matrixSuperBasis (towerBasis ε 3) 1 0 3
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (qF3 ε) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 3
  rw [tb3_3] at h
  exact h

private theorem dst3_4 : matrixSuperBasis (towerBasis ε 3) 1 0 4
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (qF4 ε) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 4
  rw [tb3_4] at h
  exact h

private theorem dst3_5 : matrixSuperBasis (towerBasis ε 3) 1 0 5
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (qF5 ε) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 5
  rw [tb3_5] at h
  exact h

private theorem dst3_6 : matrixSuperBasis (towerBasis ε 3) 1 0 6
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (qF6 ε) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 6
  rw [tb3_6] at h
  exact h

private theorem dst3_7 : matrixSuperBasis (towerBasis ε 3) 1 0 7
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) (qF7 ε) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 7
  rw [tb3_7] at h
  exact h

end Dst3

/-! ### Canonical scalar facts -/

private theorem fuse_h11 : (1 : ℝ) * 1 = 1 := mul_one 1

private theorem fuse_hm1 : (-1 : ℝ) * -1 = 1 := by norm_num

private theorem fuse_hneg : (-1 : ℝ) ≠ 0 := by norm_num

private theorem fuse_hcast : (1 : ℝ) = -(-1 : ℝ) := by norm_num

/-! ### Branch `(4,1)`: `ℍ ᵍ⊗ Cl_{0,1} ≅ M_{1|0}(Cl_{3,0})` -/

private theorem fuse41_tmul_one (x : ℍ[ℝ]) :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ x
          (1 : (divisionTower (-1 : ℝ) 1).carrier))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (cliffPhi 1 fuse_h11 x) := by
  have h1 := oddDoubleGDOne_tmul_one quatEvenSuper (-1 : ℝ) fuse_hneg x
  have e1 : realFuse_four_one.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ x
          (1 : (divisionTower (-1 : ℝ) 1).carrier))
      = (matrixSuperOne (divisionTower (1 : ℝ) 3)).symm.toAlgEquiv
          ((cliffThetaEquiv 1 fuse_h11).toAlgEquiv
            ((oddDoubleGtensorDivisionOneEquiv (-1 : ℝ) quatEvenSuper
                fuse_hneg).toAlgEquiv
              (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ x
          (1 : (divisionTower (-1 : ℝ) 1).carrier)))) := rfl
  rw [h1, cliffThetaEquiv_mk_left, matrixSuperOne_symm_single] at e1
  exact e1

private theorem fuse41_tmul_gen (x : ℍ[ℝ]) :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ x
          (q1 (-1 : ℝ)))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (cliffPhi 1 fuse_h11 x * cliffOmega 1) := by
  have h1 := oddDoubleGDOne_tmul_gen quatEvenSuper (-1 : ℝ) fuse_hneg x
  have e1 : realFuse_four_one.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ x
          (q1 (-1 : ℝ)))
      = (matrixSuperOne (divisionTower (1 : ℝ) 3)).symm.toAlgEquiv
          ((cliffThetaEquiv 1 fuse_h11).toAlgEquiv
            ((oddDoubleGtensorDivisionOneEquiv (-1 : ℝ) quatEvenSuper
                fuse_hneg).toAlgEquiv
              (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ x
          (q1 (-1 : ℝ))))) := rfl
  rw [h1, cliffThetaEquiv_mk_right, matrixSuperOne_symm_single] at e1
  exact e1

/-! ### Branch `(4,7)`: `ℍ ᵍ⊗ Cl_{1,0} ≅ M_{1|0}(Cl_{0,3})` -/

private theorem fuse47_tmul_one (x : ℍ[ℝ]) :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (cliffPhi (-1) fuse_hm1 x) := by
  have h1 := oddDoubleGDOne_tmul_one quatEvenSuper (1 : ℝ) one_ne_zero x
  have e1 : realFuse_four_seven.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = (matrixSuperOne (divisionTower (-1 : ℝ) 3)).symm.toAlgEquiv
          ((cliffThetaEquiv (-1) fuse_hm1).toAlgEquiv
            ((oddDouble_congr_eps (P := quatEvenSuper) fuse_hcast).toAlgEquiv
              ((oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper
                  one_ne_zero).toAlgEquiv
                (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x
          (1 : (divisionTower (1 : ℝ) 1).carrier))))) := rfl
  rw [h1, oddDouble_congr_eps_mk, cliffThetaEquiv_mk_left,
    matrixSuperOne_symm_single] at e1
  exact e1

private theorem fuse47_tmul_gen (x : ℍ[ℝ]) :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x
          (q1 (1 : ℝ)))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (cliffPhi (-1) fuse_hm1 x * cliffOmega (-1)) := by
  have h1 := oddDoubleGDOne_tmul_gen quatEvenSuper (1 : ℝ) one_ne_zero x
  have e1 : realFuse_four_seven.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x
          (q1 (1 : ℝ)))
      = (matrixSuperOne (divisionTower (-1 : ℝ) 3)).symm.toAlgEquiv
          ((cliffThetaEquiv (-1) fuse_hm1).toAlgEquiv
            ((oddDouble_congr_eps (P := quatEvenSuper) fuse_hcast).toAlgEquiv
              ((oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper
                  one_ne_zero).toAlgEquiv
                (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x
          (q1 (1 : ℝ)))))) := rfl
  rw [h1, oddDouble_congr_eps_mk, cliffThetaEquiv_mk_right,
    matrixSuperOne_symm_single] at e1
  exact e1

private theorem val41_0_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (1 : (divisionTower (-1 : ℝ) 1).carrier))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 0 := by
  rw [fuse41_tmul_one, cliffPhi_e0 (1 : ℝ) fuse_h11]
  rw [← dst3_0, one_smul]

private theorem val41_0_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (q1 (-1 : ℝ)))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 7 := by
  rw [fuse41_tmul_gen, cliffPhi_e0 (1 : ℝ) fuse_h11, one_mul, cliffOmega_val]
  rw [← dst3_7, one_smul]

private theorem val41_1_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (1 : (divisionTower (-1 : ℝ) 1).carrier))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 3 := by
  rw [fuse41_tmul_one, cliffPhi_e1 (1 : ℝ) fuse_h11]
  rw [← dst3_3, one_smul]

private theorem val41_1_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (q1 (-1 : ℝ)))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 4 := by
  rw [fuse41_tmul_gen, cliffPhi_e1 (1 : ℝ) fuse_h11, cliffOmega_val, prodF3F7 (1 : ℝ) fuse_h11]
  rw [← Matrix.single_neg, ← dst3_4, neg_one_smul]
  exact rfl

private theorem val41_2_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (1 : (divisionTower (-1 : ℝ) 1).carrier))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 6 := by
  rw [fuse41_tmul_one, cliffPhi_e2 (1 : ℝ) fuse_h11]
  rw [← dst3_6, one_smul]

private theorem val41_2_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (q1 (-1 : ℝ)))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 1 := by
  rw [fuse41_tmul_gen, cliffPhi_e2 (1 : ℝ) fuse_h11, cliffOmega_val, prodF6F7 (1 : ℝ) fuse_h11]
  rw [← Matrix.single_neg, ← dst3_1, neg_one_smul]
  exact rfl

private theorem val41_3_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (1 : (divisionTower (-1 : ℝ) 1).carrier))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 5 := by
  rw [fuse41_tmul_one, cliffPhi_e3 (1 : ℝ) fuse_h11, one_smul]
  rw [← dst3_5, one_smul]

private theorem val41_3_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (q1 (-1 : ℝ)))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 2 := by
  rw [fuse41_tmul_gen, cliffPhi_e3 (1 : ℝ) fuse_h11, one_smul, cliffOmega_val, prodF5F7 (1 : ℝ) fuse_h11]
  rw [← dst3_2, one_smul]

private theorem val47_0_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 0 := by
  rw [fuse47_tmul_one, cliffPhi_e0 (-1 : ℝ) fuse_hm1]
  rw [← dst3_0, one_smul]

private theorem val47_0_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (q1 (1 : ℝ)))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 7 := by
  rw [fuse47_tmul_gen, cliffPhi_e0 (-1 : ℝ) fuse_hm1, one_mul, cliffOmega_val]
  rw [← dst3_7, one_smul]

private theorem val47_1_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 3 := by
  rw [fuse47_tmul_one, cliffPhi_e1 (-1 : ℝ) fuse_hm1]
  rw [← dst3_3, one_smul]

private theorem val47_1_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (q1 (1 : ℝ)))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 4 := by
  rw [fuse47_tmul_gen, cliffPhi_e1 (-1 : ℝ) fuse_hm1, cliffOmega_val, prodF3F7 (-1 : ℝ) fuse_hm1]
  rw [← Matrix.single_neg, ← dst3_4, neg_one_smul]
  exact rfl

private theorem val47_2_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 6 := by
  rw [fuse47_tmul_one, cliffPhi_e2 (-1 : ℝ) fuse_hm1]
  rw [← dst3_6, one_smul]

private theorem val47_2_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (q1 (1 : ℝ)))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 1 := by
  rw [fuse47_tmul_gen, cliffPhi_e2 (-1 : ℝ) fuse_hm1, cliffOmega_val, prodF6F7 (-1 : ℝ) fuse_hm1]
  rw [← Matrix.single_neg, ← dst3_1, neg_one_smul]
  exact rfl

private theorem val47_3_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 5 := by
  rw [fuse47_tmul_one, cliffPhi_e3 (-1 : ℝ) fuse_hm1, neg_one_smul]
  rw [← Matrix.single_neg, ← dst3_5, neg_one_smul]
  exact rfl

private theorem val47_3_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (q1 (1 : ℝ)))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 2 := by
  rw [fuse47_tmul_gen, cliffPhi_e3 (-1 : ℝ) fuse_hm1, cliffOmega_val, smul_mul_assoc, prodF5F7 (-1 : ℝ) fuse_hm1, neg_one_smul]
  rw [← Matrix.single_neg, ← dst3_2, neg_one_smul]
  exact rfl

/-! ### Branches `(1,4)`, `(7,4)`: Koszul transposes (sign-free — the
quaternion factor is even) -/

private theorem hmem_tone (ε : ℝ) :
    (1 : (divisionTower ε 1).carrier) ∈ (divisionTower ε 1).grading 0 :=
  SetLike.one_mem_graded _

set_option maxHeartbeats 2000000 in
private theorem fuse14_comm
    (z : ((realRep 1).gtensor (realRep 4)).carrier) :
    realFuse_one_four.toAlgEquiv z
      = realFuse_four_one.toAlgEquiv
          ((gtensorComm (realRep 1) (realRep 4)).toAlgEquiv z) := rfl

private theorem val14_0_0 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (-1 : ℝ) 1).carrier)
          (quatBasis 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 0 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (1 : (divisionTower (-1 : ℝ) 1).carrier) ∈ (realRep 1).grading 0 from hmem_tone (-1 : ℝ))
    (show quatBasis 0 ∈ (realRep 4).grading 0 from quatBasis_mem 0)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_0_0

private theorem val14_0_1 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (-1 : ℝ) 1).carrier)
          (quatBasis 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 3 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (1 : (divisionTower (-1 : ℝ) 1).carrier) ∈ (realRep 1).grading 0 from hmem_tone (-1 : ℝ))
    (show quatBasis 1 ∈ (realRep 4).grading 0 from quatBasis_mem 1)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_1_0

private theorem val14_0_2 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (-1 : ℝ) 1).carrier)
          (quatBasis 2))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 6 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (1 : (divisionTower (-1 : ℝ) 1).carrier) ∈ (realRep 1).grading 0 from hmem_tone (-1 : ℝ))
    (show quatBasis 2 ∈ (realRep 4).grading 0 from quatBasis_mem 2)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_2_0

private theorem val14_0_3 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (-1 : ℝ) 1).carrier)
          (quatBasis 3))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 5 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (1 : (divisionTower (-1 : ℝ) 1).carrier) ∈ (realRep 1).grading 0 from hmem_tone (-1 : ℝ))
    (show quatBasis 3 ∈ (realRep 4).grading 0 from quatBasis_mem 3)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_3_0

private theorem val14_1_0 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (-1 : ℝ))
          (quatBasis 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 7 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (q1 (-1 : ℝ)) ∈ (realRep 1).grading 1 from mem_q1 (-1 : ℝ))
    (show quatBasis 0 ∈ (realRep 4).grading 0 from quatBasis_mem 0)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_0_1

private theorem val14_1_1 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (-1 : ℝ))
          (quatBasis 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 4 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (q1 (-1 : ℝ)) ∈ (realRep 1).grading 1 from mem_q1 (-1 : ℝ))
    (show quatBasis 1 ∈ (realRep 4).grading 0 from quatBasis_mem 1)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_1_1

private theorem val14_1_2 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (-1 : ℝ))
          (quatBasis 2))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 1 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (q1 (-1 : ℝ)) ∈ (realRep 1).grading 1 from mem_q1 (-1 : ℝ))
    (show quatBasis 2 ∈ (realRep 4).grading 0 from quatBasis_mem 2)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_2_1

private theorem val14_1_3 :
    realFuse_one_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (-1 : ℝ))
          (quatBasis 3))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 2 := by
  have hc := gtensorComm_tmul_of_mem (realRep 1) (realRep 4)
    (show (q1 (-1 : ℝ)) ∈ (realRep 1).grading 1 from mem_q1 (-1 : ℝ))
    (show quatBasis 3 ∈ (realRep 4).grading 0 from quatBasis_mem 3)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse14_comm, hc]
  exact val41_3_1

set_option maxHeartbeats 2000000 in
private theorem fuse74_comm
    (z : ((realRep 7).gtensor (realRep 4)).carrier) :
    realFuse_seven_four.toAlgEquiv z
      = realFuse_four_seven.toAlgEquiv
          ((gtensorComm (realRep 7) (realRep 4)).toAlgEquiv z) := rfl

private theorem val74_0_0 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (1 : ℝ) 1).carrier)
          (quatBasis 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 0 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (1 : (divisionTower (1 : ℝ) 1).carrier) ∈ (realRep 7).grading 0 from hmem_tone (1 : ℝ))
    (show quatBasis 0 ∈ (realRep 4).grading 0 from quatBasis_mem 0)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_0_0

private theorem val74_0_1 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (1 : ℝ) 1).carrier)
          (quatBasis 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 3 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (1 : (divisionTower (1 : ℝ) 1).carrier) ∈ (realRep 7).grading 0 from hmem_tone (1 : ℝ))
    (show quatBasis 1 ∈ (realRep 4).grading 0 from quatBasis_mem 1)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_1_0

private theorem val74_0_2 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (1 : ℝ) 1).carrier)
          (quatBasis 2))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 6 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (1 : (divisionTower (1 : ℝ) 1).carrier) ∈ (realRep 7).grading 0 from hmem_tone (1 : ℝ))
    (show quatBasis 2 ∈ (realRep 4).grading 0 from quatBasis_mem 2)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_2_0

private theorem val74_0_3 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (1 : (divisionTower (1 : ℝ) 1).carrier)
          (quatBasis 3))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 5 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (1 : (divisionTower (1 : ℝ) 1).carrier) ∈ (realRep 7).grading 0 from hmem_tone (1 : ℝ))
    (show quatBasis 3 ∈ (realRep 4).grading 0 from quatBasis_mem 3)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_3_0

private theorem val74_1_0 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (1 : ℝ))
          (quatBasis 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 7 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (q1 (1 : ℝ)) ∈ (realRep 7).grading 1 from mem_q1 (1 : ℝ))
    (show quatBasis 0 ∈ (realRep 4).grading 0 from quatBasis_mem 0)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_0_1

private theorem val74_1_1 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (1 : ℝ))
          (quatBasis 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 4 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (q1 (1 : ℝ)) ∈ (realRep 7).grading 1 from mem_q1 (1 : ℝ))
    (show quatBasis 1 ∈ (realRep 4).grading 0 from quatBasis_mem 1)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_1_1

private theorem val74_1_2 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (1 : ℝ))
          (quatBasis 2))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 1 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (q1 (1 : ℝ)) ∈ (realRep 7).grading 1 from mem_q1 (1 : ℝ))
    (show quatBasis 2 ∈ (realRep 4).grading 0 from quatBasis_mem 2)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_2_1

private theorem val74_1_3 :
    realFuse_seven_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 4).grading) ℝ (q1 (1 : ℝ))
          (quatBasis 3))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 2 := by
  have hc := gtensorComm_tmul_of_mem (realRep 7) (realRep 4)
    (show (q1 (1 : ℝ)) ∈ (realRep 7).grading 1 from mem_q1 (1 : ℝ))
    (show quatBasis 3 ∈ (realRep 4).grading 0 from quatBasis_mem 3)
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [fuse74_comm, hc]
  exact val47_3_1

private theorem col41_0 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 0)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 0 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 0 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 0)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (0, 0)) from rfl, hsrc]
  exact val41_0_0

private theorem col41_1 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 1)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 7 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 0 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 1)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (0, 1)) from rfl, hsrc]
  exact val41_0_1

private theorem col41_2 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 2)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 3 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 1 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 2)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (1, 0)) from rfl, hsrc]
  exact val41_1_0

private theorem col41_3 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 3)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 4 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 1 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 3)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (1, 1)) from rfl, hsrc]
  exact val41_1_1

private theorem col41_4 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 4)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 6 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 2 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 4)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (2, 0)) from rfl, hsrc]
  exact val41_2_0

private theorem col41_5 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 5)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 1 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 2 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 5)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (2, 1)) from rfl, hsrc]
  exact val41_2_1

private theorem col41_6 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 6)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 5 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 3 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 6)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (3, 0)) from rfl, hsrc]
  exact val41_3_0

private theorem col41_7 :
    realFuse_four_one.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 7)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 2 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1))
    quatBasis (towerBasis (-1 : ℝ) 1) 3 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1) 7)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1)
        (finProdFinEquiv (3, 1)) from rfl, hsrc]
  exact val41_3_1

private theorem fuse41_matrix :
    LinearMap.toMatrix
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1))
        (matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0)
        realFuse_four_one.toAlgEquiv.toLinearMap
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 1;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, -1, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 1, 0;
        0, 0, 0, 0, 1, 0, 0, 0;
        0, 1, 0, 0, 0, 0, 0, 0] := by
  refine toMatrix_signedPerm
      (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (-1 : ℝ) 1)) quatBasis (towerBasis (-1 : ℝ) 1))
      (matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0)
      realFuse_four_one.toAlgEquiv.toLinearMap
      ![1, 1, 1, -1, 1, -1, 1, 1] ![0, 7, 3, 4, 6, 1, 5, 2] _ ?_ ?_
  · intro j
    fin_cases j
    · exact col41_0
    · exact col41_1
    · exact col41_2
    · exact col41_3
    · exact col41_4
    · exact col41_5
    · exact col41_6
    · exact col41_7
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]

private theorem col47_0 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 0)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 0 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 0 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 0)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (0, 0)) from rfl, hsrc]
  exact val47_0_0

private theorem col47_1 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 1)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 7 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 0 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 1)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (0, 1)) from rfl, hsrc]
  exact val47_0_1

private theorem col47_2 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 2)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 3 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 1 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 2)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (1, 0)) from rfl, hsrc]
  exact val47_1_0

private theorem col47_3 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 3)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 4 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 1 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 3)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (1, 1)) from rfl, hsrc]
  exact val47_1_1

private theorem col47_4 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 4)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 6 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 2 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 4)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (2, 0)) from rfl, hsrc]
  exact val47_2_0

private theorem col47_5 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 5)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 1 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 2 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 5)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (2, 1)) from rfl, hsrc]
  exact val47_2_1

private theorem col47_6 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 6)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 5 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 3 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 6)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (3, 0)) from rfl, hsrc]
  exact val47_3_0

private theorem col47_7 :
    realFuse_four_seven.toAlgEquiv
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 7)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 2 := by
  have hsrc := gtensorBasis_apply_pair (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1))
    quatBasis (towerBasis (1 : ℝ) 1) 3 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1) 7)
      = gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1)
        (finProdFinEquiv (3, 1)) from rfl, hsrc]
  exact val47_3_1

private theorem fuse47_matrix :
    LinearMap.toMatrix
        (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1))
        (matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0)
        realFuse_four_seven.toAlgEquiv.toLinearMap
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 0, 0, 0, 0, -1;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, -1, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, -1, 0;
        0, 0, 0, 0, 1, 0, 0, 0;
        0, 1, 0, 0, 0, 0, 0, 0] := by
  refine toMatrix_signedPerm
      (gtensorBasis (A := quatEvenSuper) (B := (divisionTower (1 : ℝ) 1)) quatBasis (towerBasis (1 : ℝ) 1))
      (matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0)
      realFuse_four_seven.toAlgEquiv.toLinearMap
      ![1, 1, 1, -1, 1, -1, -1, -1] ![0, 7, 3, 4, 6, 1, 5, 2] _ ?_ ?_
  · intro j
    fin_cases j
    · exact col47_0
    · exact col47_1
    · exact col47_2
    · exact col47_3
    · exact col47_4
    · exact col47_5
    · exact col47_6
    · exact col47_7
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]

private theorem col14_0 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 0)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 0 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 0 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 0)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 0)) from rfl, hsrc]
  exact val14_0_0

private theorem col14_1 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 1)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 3 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 0 1
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 1)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 1)) from rfl, hsrc]
  exact val14_0_1

private theorem col14_2 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 2)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 6 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 0 2
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 2)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 2)) from rfl, hsrc]
  exact val14_0_2

private theorem col14_3 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 3)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 5 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 0 3
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 3)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 3)) from rfl, hsrc]
  exact val14_0_3

private theorem col14_4 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 4)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 7 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 1 0
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 4)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 0)) from rfl, hsrc]
  exact val14_1_0

private theorem col14_5 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 5)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 4 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 1 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 5)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 1)) from rfl, hsrc]
  exact val14_1_1

private theorem col14_6 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 6)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 1 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 1 2
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 6)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 2)) from rfl, hsrc]
  exact val14_1_2

private theorem col14_7 :
    realFuse_one_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 7)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 2 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (-1 : ℝ) 1) quatBasis 1 3
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis 7)
      = gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 3)) from rfl, hsrc]
  exact val14_1_3

private theorem fuse14_matrix :
    LinearMap.toMatrix
        (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis)
        (matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0)
        realFuse_one_four.toAlgEquiv.toLinearMap
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, -1, 0;
        0, 0, 0, 0, 0, 0, 0, 1;
        0, 1, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 1, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 1, 0, 0, 0] := by
  refine toMatrix_signedPerm
      (gtensorBasis (A := (divisionTower (-1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (-1 : ℝ) 1) quatBasis)
      (matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0)
      realFuse_one_four.toAlgEquiv.toLinearMap
      ![1, 1, 1, 1, 1, -1, -1, 1] ![0, 3, 6, 5, 7, 4, 1, 2] _ ?_ ?_
  · intro j
    fin_cases j
    · exact col14_0
    · exact col14_1
    · exact col14_2
    · exact col14_3
    · exact col14_4
    · exact col14_5
    · exact col14_6
    · exact col14_7
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]

private theorem col74_0 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 0)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 0 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 0 0
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 0)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 0)) from rfl, hsrc]
  exact val74_0_0

private theorem col74_1 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 1)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 3 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 0 1
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 1)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 1)) from rfl, hsrc]
  exact val74_0_1

private theorem col74_2 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 2)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 6 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 0 2
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 2)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 2)) from rfl, hsrc]
  exact val74_0_2

private theorem col74_3 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 3)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 5 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 0 3
  rw [tb1_0] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 3)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (0, 3)) from rfl, hsrc]
  exact val74_0_3

private theorem col74_4 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 4)
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 7 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 1 0
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 4)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 0)) from rfl, hsrc]
  exact val74_1_0

private theorem col74_5 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 5)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 4 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 1 1
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 5)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 1)) from rfl, hsrc]
  exact val74_1_1

private theorem col74_6 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 6)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 1 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 1 2
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 6)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 2)) from rfl, hsrc]
  exact val74_1_2

private theorem col74_7 :
    realFuse_seven_four.toAlgEquiv
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 7)
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 2 := by
  have hsrc := gtensorBasis_apply_pair (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper)
    (towerBasis (1 : ℝ) 1) quatBasis 1 3
  rw [tb1_1] at hsrc
  rw [show (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis 7)
      = gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis
        (finProdFinEquiv (1, 3)) from rfl, hsrc]
  exact val74_1_3

private theorem fuse74_matrix :
    LinearMap.toMatrix
        (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis)
        (matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0)
        realFuse_seven_four.toAlgEquiv.toLinearMap
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, -1, 0;
        0, 0, 0, 0, 0, 0, 0, -1;
        0, 1, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, -1, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 1, 0, 0, 0] := by
  refine toMatrix_signedPerm
      (gtensorBasis (A := (divisionTower (1 : ℝ) 1)) (B := quatEvenSuper) (towerBasis (1 : ℝ) 1) quatBasis)
      (matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0)
      realFuse_seven_four.toAlgEquiv.toLinearMap
      ![1, 1, 1, -1, 1, -1, -1, -1] ![0, 3, 6, 5, 7, 4, 1, 2] _ ?_ ?_
  · intro j
    fin_cases j
    · exact col74_0
    · exact col74_1
    · exact col74_2
    · exact col74_3
    · exact col74_4
    · exact col74_5
    · exact col74_6
    · exact col74_7
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]

/-! ### Branch `(4,4)`: Wall's isomorphism `ℍ ᵍ⊗ ℍ ≅ M_{4|0}(ℝ)` -/

/-- The singleton basis of the base algebra, typed at
`(SuperAlgebra.base ℝ).carrier`. -/
private noncomputable def qBaseBasis :
    Basis (Fin 1) ℝ (SuperAlgebra.base ℝ).carrier :=
  Basis.singleton (Fin 1) ℝ

private theorem qBaseBasis_repr (v : (SuperAlgebra.base ℝ).carrier)
    (e : Fin 1) : qBaseBasis.repr v e = v := by
  obtain rfl : e = default := Subsingleton.elim e default
  show (Finsupp.single (default : Fin 1) v) default = v
  exact Finsupp.single_eq_same

/-! ### The quaternion multiplication table -/

private def qv : Fin 4 → ℍ[ℝ] :=
  ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

private theorem quatBasis_eq_qv (i : Fin 4) : quatBasis i = qv i := by
  fin_cases i
  · exact quatBasis_zero
  · exact quatBasis_one
  · exact quatBasis_two
  · exact quatBasis_three

private def qidx : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

private def qsgn : Fin 4 → Fin 4 → ℝ :=
  ![![1, 1, 1, 1], ![1, -1, 1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

private def qstar : Fin 4 → ℝ := ![1, -1, -1, -1]

private theorem qv_mul (p q : Fin 4) :
    qv p * qv q = qsgn p q • qv (qidx p q) := by
  fin_cases p <;> fin_cases q <;>
    simp only [qv, qidx, qsgn, Matrix.cons_val_one, Matrix.cons_val] <;>
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp

private theorem qv_star (p : Fin 4) : star (qv p) = qstar p • qv p := by
  fin_cases p <;>
    simp only [qv, qstar, Matrix.cons_val_one, Matrix.cons_val] <;>
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp

/-- Quaternion conjugation as a function on `quatEvenSuper.carrier`. -/
private def qcj : quatEvenSuper.carrier → quatEvenSuper.carrier :=
  (star : ℍ[ℝ] → ℍ[ℝ])

private theorem quatBasis_mul (p q : Fin 4) :
    quatBasis p * quatBasis q = qsgn p q • quatBasis (qidx p q) := by
  rw [quatBasis_eq_qv p, quatBasis_eq_qv q, quatBasis_eq_qv (qidx p q)]
  exact qv_mul p q

private theorem quatBasis_conj (p : Fin 4) :
    qcj (quatBasis p) = qstar p • quatBasis p := by
  rw [quatBasis_eq_qv p]
  exact qv_star p

/-- The three-fold product that Wall's map produces on frame vectors. -/
private def w44 (a b s : Fin 4) : ℝ :=
  qstar b * qsgn s b * qsgn a (qidx s b)

private def t44 (a b s : Fin 4) : Fin 4 := qidx a (qidx s b)

private theorem quatBasis_triple (a b s : Fin 4) :
    quatBasis a * (quatBasis s * qcj (quatBasis b))
      = w44 a b s • quatBasis (t44 a b s) := by
  rw [quatBasis_conj, mul_smul_comm, quatBasis_mul, smul_smul, mul_smul_comm,
    quatBasis_mul, smul_smul, w44, t44]

/-! ### The composite on pure tensors -/

private noncomputable def qhb :
    Basis (Fin 4 ⊕ Fin 0) ℝ quatEvenSuper.carrier :=
  homBasisOf quatEvenSuper.grading quatEvenBasisZero quatEvenBasisOne

private theorem qhb_inl (k : Fin 4) : qhb (Sum.inl k) = quatBasis k := by
  rw [qhb, homBasisOf_inl]
  rfl

private theorem quat_mulMap (c z : quatEvenSuper.carrier) :
    SuperOp.mulMap quatEvenSuper.grading c z = z * c := by
  rw [SuperOp.mulMap_apply,
    oddPart_of_mem_zero quatEvenSuper.grading
      (show z ∈ quatEvenSuper.grading 0 from mem_evenGrading_zero ℝ ℍ[ℝ] z),
    zero_mul, smul_zero, sub_zero]

private theorem quatSop_unop (y : quatEvenSuper.carrier) :
    SuperOp.unop quatEvenSuper.grading (quatSopSuperEquiv.toAlgEquiv y)
      = qcj y := rfl

private theorem fuse44_entry (x y : quatEvenSuper.carrier) (r s : Fin 4) :
    (realFuse_four_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := quatEvenSuper.grading) ℝ x y)) (Sum.inl r) (Sum.inl s)
      = qhb.repr (x * (quatBasis s * qcj y)) (Sum.inl r) := by
  have e0 : realFuse_four_four.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := quatEvenSuper.grading) ℝ x y)
      = LinearMap.toMatrixAlgEquiv qhb
          (superMulLeftRight quatEvenSuper.grading
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := SuperOp.grading quatEvenSuper.grading) ℝ x
              (quatSopSuperEquiv.toAlgEquiv y))) := by
    have e1 : realFuse_four_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := quatEvenSuper.grading) ℝ x y)
        = (endMatrixSuperOf quatEvenSuper quatEvenBasisZero
              quatEvenBasisOne).toAlgEquiv
            ((wallSuperEquiv quatEvenSuper).toAlgEquiv
              (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                  quatSopSuperEquiv).toAlgEquiv
                (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
                  (ℬ := quatEvenSuper.grading) ℝ x y))) := rfl
    rw [SuperAlgEquiv.gtensorCongr_tmul] at e1
    exact e1
  rw [e0, LinearMap.toMatrixAlgEquiv_apply, superMulLeftRight_tmul_apply,
    quatSop_unop, quat_mulMap, qhb_inl]

private theorem fuse44_entry_basis (a b r s : Fin 4) :
    (realFuse_four_four.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := quatEvenSuper.grading) ℝ (quatBasis a) (quatBasis b)))
        (Sum.inl r) (Sum.inl s)
      = w44 a b s * (if t44 a b s = r then (1 : ℝ) else 0) := by
  rw [fuse44_entry, quatBasis_triple, ← qhb_inl, map_smul, Finsupp.smul_apply,
    Basis.repr_self_apply, smul_eq_mul]
  refine congrArg (fun t : ℝ => w44 a b s * t) ?_
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · exact Sum.inl_injective h
  · exact congrArg Sum.inl h

/-! ### Index tables -/

private def pIdx : Fin 4 → Fin 4 → Fin 16 :=
  ![![0, 1, 2, 3], ![4, 5, 6, 7], ![8, 9, 10, 11], ![12, 13, 14, 15]]

private theorem row44 (r s : Fin 4) :
    matrixSuperIndexEquiv 4 0 1 (Sum.inl r, Sum.inl s, (0 : Fin 1))
      = pIdx r s := by
  fin_cases r <;> fin_cases s <;> rfl

private theorem col44 (a b : Fin 4) :
    finProdFinEquiv (a, b) = pIdx a b := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Entry-level column-to-matrix step for a `4|0` target over the base
field, with both index flattenings replaced by the literal table. -/
private theorem toMatrix_of_entries44
    (f : (quatEvenSuper.gtensor quatEvenSuper).carrier →ₗ[ℝ]
      ((SuperAlgebra.base ℝ).matrixSuper 4 0).carrier)
    (M : Matrix (Fin ((4 + 0) * (4 + 0) * 1)) (Fin (4 * 4)) ℝ)
    (h : ∀ r s a b : Fin 4,
        (f (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := quatEvenSuper.grading) ℝ (quatBasis a) (quatBasis b)))
            (Sum.inl r) (Sum.inl s)
          = M (pIdx r s) (pIdx a b)) :
    LinearMap.toMatrix
        (gtensorBasis (A := quatEvenSuper) (B := quatEvenSuper) quatBasis
          quatBasis)
        (matrixSuperBasis (P := SuperAlgebra.base ℝ) qBaseBasis 4 0) f
      = M := by
  refine toMatrix_of_coord _ _ _ _ fun i j => ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨r, s, e⟩, rfl⟩ := (matrixSuperIndexEquiv 4 0 1).surjective i
  cases r with
  | inr r => exact r.elim0
  | inl r =>
    cases s with
    | inr s => exact s.elim0
    | inl s =>
      obtain rfl : e = 0 := Subsingleton.elim e 0
      rw [gtensorBasis_apply_pair, matrixSuperBasis_repr, qBaseBasis_repr,
        row44, col44]
      exact h r s a b

/-! ### The `(4,4)` matrix -/

private theorem fuse44_matrix :
    LinearMap.toMatrix
        (gtensorBasis (A := quatEvenSuper) (B := quatEvenSuper) quatBasis
          quatBasis)
        (matrixSuperBasis (P := SuperAlgebra.base ℝ) qBaseBasis 4 0)
        realFuse_four_four.toAlgEquiv.toLinearMap
      = !![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
        0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0;
        0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0;
        0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0;
        1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1;
        0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0;
        0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0;
        0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0;
        1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
        0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
        0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 0;
        0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0;
        0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
        1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1] := by
  refine toMatrix_of_entries44 _ _ ?_
  intro r s a b
  refine (fuse44_entry_basis a b r s).trans ?_
  fin_cases a <;> fin_cases b <;> fin_cases r <;> fin_cases s <;>
    simp [w44, t44, qidx, qsgn, qstar, pIdx]

/-! ### The public value-pinning theorems -/

/-- **Value-pinning spec for `realFuse 4 1`** in the canonical frames
of `RealFuseMatrix` — a signed permutation. -/
theorem realFuseMatrix_4_1 :
    realFuseMatrix 4 1
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 1;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, -1, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 1, 0;
        0, 0, 0, 0, 1, 0, 0, 0;
        0, 1, 0, 0, 0, 0, 0, 0] :=
  fuse41_matrix

/-- **Value-pinning spec for `realFuse 4 7`** in the canonical frames
of `RealFuseMatrix` — a signed permutation. -/
theorem realFuseMatrix_4_7 :
    realFuseMatrix 4 7
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 0, 0, 0, 0, -1;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, -1, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, -1, 0;
        0, 0, 0, 0, 1, 0, 0, 0;
        0, 1, 0, 0, 0, 0, 0, 0] :=
  fuse47_matrix

/-- **Value-pinning spec for `realFuse 1 4`** in the canonical frames
of `RealFuseMatrix` — a signed permutation. -/
theorem realFuseMatrix_1_4 :
    realFuseMatrix 1 4
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, -1, 0;
        0, 0, 0, 0, 0, 0, 0, 1;
        0, 1, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 1, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 1, 0, 0, 0] :=
  fuse14_matrix

/-- **Value-pinning spec for `realFuse 7 4`** in the canonical frames
of `RealFuseMatrix` — a signed permutation. -/
theorem realFuseMatrix_7_4 :
    realFuseMatrix 7 4
      = !![1, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, -1, 0;
        0, 0, 0, 0, 0, 0, 0, -1;
        0, 1, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, -1, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 1, 0, 0, 0] :=
  fuse74_matrix

/-- **Value-pinning spec for `realFuse 4 4`** (Wall's isomorphism
`ℍ ᵍ⊗ ℍ ≅ M_{4|0}(ℝ)` along the explicit basis `1, i, j, k`). -/
theorem realFuseMatrix_4_4 :
    realFuseMatrix 4 4
      = !![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
        0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0;
        0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0;
        0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0;
        1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1;
        0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0;
        0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0;
        0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0;
        0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0;
        1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
        0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
        0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 0;
        0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0;
        0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
        1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1] :=
  fuse44_matrix

end Superfusion

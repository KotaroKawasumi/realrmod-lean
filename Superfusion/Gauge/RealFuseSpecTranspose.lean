/-
Superfusion / Gauge / RealFuseSpecTranspose

M15 semantic-bridge GROUP 2: value-pinning spec theorems for the seventeen
**Koszul-braiding transpose branches** — the nine `RealFuse2` transposes
`(7,1), (6,1), (5,1), (7,2), (6,2), (5,2), (7,3), (6,3), (5,3)` and the
eight `RealFuse4` transposes `(2,4), (6,4), (3,4), (5,4), (7,5), (6,5),
(3,1), (3,2)`.

Every branch here is `realFuse_transpose` of a forward branch: at concrete
labels `realFuse B A` is *definitionally* the composite
`gtensorComm (realRep B) (realRep A) ; realFuse A B` (the `add_comm` and
`ZMod.val_add` `Eq.mpr` layers dissolve by kernel proof irrelevance, pilot
conclusion 1).  The derivation is therefore fully generic and needs **no
unwinding of the forward composite**:

1. **Per-branch comm reduction** (`comm_B_A`): evaluating a source frame
   vector `b_B(iB) ᵍ⊗ b_A(jA)` through the braiding
   (`gtensorComm_tmul_of_mem`) and re-reading the result as a *forward*
   source frame vector gives the entrywise identity
   `realFuseMatrix B A i ⟪iB,jA⟫ = (-1)^{p_A(jA)·p_B(iB)} •
    realFuseMatrix A B i ⟪jA,iB⟫` — the forward matrix stays opaque.
2. **Code-level column bookkeeping** (`codes_B_A`, kernel `decide`): the
   emitted base-3 row codes of the transpose literal are exactly the
   sign-twisted column permutation of the forward literal's codes,
   with the Koszul sign `(-1)^{p_B(iB)·p_A(jA)}` computed from the *Lean*
   parity tables (`realRepBasisParity`) — a kernel-checked cross-check of
   `scripts/certgen/fuse.py`'s `_comm_mat` against the Lean grading data.
3. **Value pinning** (`realFuseMatrix_B_A_of_forward`): combining 1 and 2
   pins `realFuseMatrix B A` to its stage-L literal **given the forward
   branch's value-pinning spec** (in its stage-L statement shape) as a
   hypothesis.  The forward specs are group 1's deliverables; once both
   files are in the tree the glue is one line per branch, e.g.
   `theorem realFuseMatrix_7_1 : realFuseMatrix 7 1 = !![…] :=
      realFuseMatrix_7_1_of_forward realFuseMatrix_1_7`
   (the hypothesis shapes below are definitionally the group-1 statement
   shapes; `fuseBang_*`-style definitions unfold by `rfl`).

Literal values: `scripts/certgen/fuse.py` via the stage-L emitter
`scripts/certgen/gen_fuse_literals.py` (row-major base-3 packed codes,
LSD = column 0; codes 0 ↦ 0, 1 ↦ 1, 2 ↦ -1, decoded by `fuseDecode`);
this file's rows were regenerated from `fuse.py` and byte-checked against
the stage-L output.

Proof-engineering note (extends the pilot's conclusions): entry-level
goals here mix index types that are only *definitionally* equal
(`Fin 4` vs `Fin (realRepDim …)`), which makes `rw`/`kabstract`
unreliable (motive checks fail at `instances` transparency); every step
through such terms is therefore an `Eq.trans`/`congrArg` chain
(unifier-driven), and rewriting happens only inside fully literal-typed
goals (`sign_decode`) or hypotheses stated by the library itself.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7); statement shapes as in
`Superfusion.Gauge.RealFuseSpecPilot`.
-/
import Superfusion.Gauge.RealFuseMatrix

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace Superfusion

open Module GradedTensorProduct

/-! ### Generic helpers -/

/-- **The base-3 value-code decoder** shared by all packed literals in
this file: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ -1` (the stage-L emitter contract of
`scripts/certgen/gen_fuse_literals.py`). -/
def fuseDecode : ℕ → ℝ
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Negation on value codes: `1 ↔ 2`, `0 ↦ 0`. -/
private def fuseNegCode : ℕ → ℕ
  | 1 => 2
  | 2 => 1
  | _ => 0

private theorem fuseDecode_negCode (c : ℕ) :
    fuseDecode (fuseNegCode c) = -fuseDecode c := by
  match c with
  | 0 => show (0 : ℝ) = -0; rw [neg_zero]
  | 1 => rfl
  | 2 => show (1 : ℝ) = -(-1); rw [neg_neg]
  | (n + 3) => show (0 : ℝ) = -0; rw [neg_zero]

/-- **The abstract sign-resolution step**: if the target code `cT` is the
(sign-conditional) twist of the source code `cF`, then the decoded target
value is the Koszul-signed decoded source value. -/
private theorem sign_decode (p q : ZMod 2) (cF cT : ℕ)
    (hcode : cT = if q = 1 ∧ p = 1 then fuseNegCode cF else cF) :
    (((-1 : ℤˣ) ^ (p * q) : ℤˣ) : ℤ) • fuseDecode cF = fuseDecode cT := by
  subst hcode
  rcases zmod2_cases p with h1 | h1 <;> subst h1 <;>
    rcases zmod2_cases q with h2 | h2 <;> subst h2
  · rw [if_neg (by decide), mul_zero, uzpow_zero, Units.val_one, one_zsmul]
  · rw [if_neg (by decide), zero_mul, uzpow_zero, Units.val_one, one_zsmul]
  · rw [if_neg (by decide), mul_zero, uzpow_zero, Units.val_one, one_zsmul]
  · rw [if_pos (⟨rfl, rfl⟩ : (1 : ZMod 2) = 1 ∧ (1 : ZMod 2) = 1),
      mul_one, uzpow_one, Units.val_neg, Units.val_one, neg_zsmul, one_zsmul,
      fuseDecode_negCode]

/-- A graded isomorphism commutes with `ℤ`-scaling (Koszul sign values). -/
private theorem superAlgEquiv_zsmul {A B : SuperAlgebra ℝ}
    (f : SuperAlgEquiv A B) (σ : ℤ) (x : A.carrier) :
    f.toAlgEquiv (σ • x) = σ • f.toAlgEquiv x :=
  map_zsmul f.toAlgEquiv σ x

/-- Coordinates commute with `ℤ`-scaling. -/
private theorem basis_repr_zsmul_apply {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module ℝ M] (b : Basis (Fin n) ℝ M) (σ : ℤ) (v : M) (i : Fin n) :
    b.repr (σ • v) i = σ • b.repr v i := by
  rw [map_zsmul, Finsupp.smul_apply]

/-- Application form of `SuperAlgEquiv.trans` (definitional).  Keeping the
per-branch cast crossing at the *equiv* level and applying this generic
lemma avoids unfolding the deep branch composites (the applied-form defeq
check explodes on the `peelFuse`-nested branches). -/
private theorem superAlgEquiv_trans_apply {P Q R : SuperAlgebra ℝ}
    (e : SuperAlgEquiv P Q) (f : SuperAlgEquiv Q R) (x : P.carrier) :
    (e.trans f).toAlgEquiv x = f.toAlgEquiv (e.toAlgEquiv x) :=
  AlgEquiv.trans_apply _ _ _

/-! ### Branch `(7, 1)` (transpose of `(1, 7)`, `4 × 4`) -/

private def rowsT_7_1 : Fin 4 → ℕ :=
  ![55,
    12,
    15,
    28]

private def rowsF_1_7 : Fin 4 → ℕ :=
  ![28,
    12,
    21,
    55]

/-- The forward `(1,7)` literal (stage-L values), decoder form. -/
def fuseLitFwd_1_7 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_1_7 i / 3 ^ (j : ℕ) % 3)

private def litT_7_1 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_7_1 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(7,1)` codes are the Koszul-signed column
transposition of the `(1,7)` codes, against the Lean parity tables. -/
private theorem codes_7_1 : ∀ (i : Fin 4) (iB : Fin 2) (jA : Fin 2),
    rowsT_7_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3
      = if realRepBasisParity 7 iB = 1 ∧ realRepBasisParity 1 jA = 1
        then fuseNegCode (rowsF_1_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
        else rowsF_1_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(7,1)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_7_1 (i : Fin 4) (iB : Fin 2) (jA : Fin 2) :
    realFuseMatrix 7 1 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 7 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 1 7 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 7) (realRep 1)
    (realRepBasis_mem 7 iB) (realRepBasis_mem 1 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 7 1 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 1).grading) ℝ (realRepBasis 7 iB)
          (realRepBasis 1 jA) :=
    gtensorBasis_apply_pair (realRepBasis 7) (realRepBasis 1) iB jA
  have hsrcR : realFuseSrcBasis 1 7 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 7).grading) ℝ (realRepBasis 1 jA)
          (realRepBasis 7 iB) :=
    gtensorBasis_apply_pair (realRepBasis 1) (realRepBasis 7) jA iB
  have e0 : realFuse 7 1
      = (gtensorComm (realRep 7) (realRep 1)).trans (realFuse 1 7) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 1 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 7) (realRep 1))
      (realFuse 1 7)
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 1 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 1 7).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 1 7) _ _))
  refine (realFuseMatrix_apply 7 1 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 1).repr
    ((realFuse 7 1).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 1).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 7 1) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 1 7 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 1 7).repr
      ((realFuse 1 7).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(7,1)`, from the forward spec. -/
private theorem spec_7_1
    (h : ∀ (i j : Fin 4), realFuseMatrix 1 7 i j = fuseLitFwd_1_7 i j) :
    ∀ (i j : Fin 4), realFuseMatrix 7 1 i j = litT_7_1 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := 2)).surjective j
  refine (comm_7_1 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 7 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_1_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_7_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_7_1 i iB jA)

/-- **Deliverable, branch `(7,1)`** (conditional on the group-1 forward
spec at `(1,7)`): the value-pinning literal form. -/
theorem realFuseMatrix_7_1_of_forward
    (h : realFuseMatrix 1 7
      = !![1, 0, 0, 1;
            0, 1, 1, 0;
            0, 1, -1, 0;
            1, 0, 0, -1]) :
    realFuseMatrix 7 1
      = !![1, 0, 0, -1;
            0, 1, 1, 0;
            0, -1, 1, 0;
            1, 0, 0, 1] := by
  have h' : ∀ (i j : Fin 4), realFuseMatrix 1 7 i j = fuseLitFwd_1_7 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 4), realFuseMatrix 7 1 i j
      = (!![1, 0, 0, -1;
              0, 1, 1, 0;
              0, -1, 1, 0;
              1, 0, 0, 1]
          : Matrix (Fin 4) (Fin 4) ℝ) i j := by
    intro i j
    refine (spec_7_1 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(6, 1)` (transpose of `(1, 6)`, `8 × 8`) -/

private def rowsT_6_1 : Fin 8 → ℕ :=
  ![487,
    4383,
    84,
    756,
    87,
    1485,
    244,
    4392]

private def rowsF_1_6 : Fin 8 → ℕ :=
  ![730,
    4377,
    90,
    513,
    171,
    540,
    1459,
    4380]

/-- The forward `(1,6)` literal (stage-L values), decoder form. -/
def fuseLitFwd_1_6 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_1_6 i / 3 ^ (j : ℕ) % 3)

private def litT_6_1 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_6_1 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(6,1)` codes are the Koszul-signed column
transposition of the `(1,6)` codes, against the Lean parity tables. -/
private theorem codes_6_1 : ∀ (i : Fin 8) (iB : Fin 4) (jA : Fin 2),
    rowsT_6_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3
      = if realRepBasisParity 6 iB = 1 ∧ realRepBasisParity 1 jA = 1
        then fuseNegCode (rowsF_1_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
        else rowsF_1_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(6,1)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_6_1 (i : Fin 8) (iB : Fin 4) (jA : Fin 2) :
    realFuseMatrix 6 1 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 6 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 1 6 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 6) (realRep 1)
    (realRepBasis_mem 6 iB) (realRepBasis_mem 1 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 6 1 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 1).grading) ℝ (realRepBasis 6 iB)
          (realRepBasis 1 jA) :=
    gtensorBasis_apply_pair (realRepBasis 6) (realRepBasis 1) iB jA
  have hsrcR : realFuseSrcBasis 1 6 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 6).grading) ℝ (realRepBasis 1 jA)
          (realRepBasis 6 iB) :=
    gtensorBasis_apply_pair (realRepBasis 1) (realRepBasis 6) jA iB
  have e0 : realFuse 6 1
      = (gtensorComm (realRep 6) (realRep 1)).trans (realFuse 1 6) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 1 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 6) (realRep 1))
      (realFuse 1 6)
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 1 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 1 6).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 1 6) _ _))
  refine (realFuseMatrix_apply 6 1 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 1).repr
    ((realFuse 6 1).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 1).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 6 1) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 1 6 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 1 6).repr
      ((realFuse 1 6).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(6,1)`, from the forward spec. -/
private theorem spec_6_1
    (h : ∀ (i j : Fin 8), realFuseMatrix 1 6 i j = fuseLitFwd_1_6 i j) :
    ∀ (i j : Fin 8), realFuseMatrix 6 1 i j = litT_6_1 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 4) (n := 2)).surjective j
  refine (comm_6_1 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 6 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_1_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_6_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_6_1 i iB jA)

/-- **Deliverable, branch `(6,1)`** (conditional on the group-1 forward
spec at `(1,6)`): the value-pinning literal form. -/
theorem realFuseMatrix_6_1_of_forward
    (h : realFuseMatrix 1 6
      = !![1, 0, 0, 0, 0, 0, 1, 0;
            0, 1, 0, 0, 0, 0, 0, -1;
            0, 0, 1, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, -1, 0, 0;
            0, 0, 1, 0, -1, 0, 0, 0;
            0, 0, 0, -1, 0, -1, 0, 0;
            1, 0, 0, 0, 0, 0, -1, 0;
            0, -1, 0, 0, 0, 0, 0, -1]) :
    realFuseMatrix 6 1
      = !![1, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 1, 0, 0, 0, 0, -1;
            0, 1, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 1, 0;
            0, -1, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 0, -1, 0;
            1, 0, 0, 0, 0, 1, 0, 0;
            0, 0, -1, 0, 0, 0, 0, -1] := by
  have h' : ∀ (i j : Fin 8), realFuseMatrix 1 6 i j = fuseLitFwd_1_6 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 8), realFuseMatrix 6 1 i j
      = (!![1, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 1, 0, 0, 0, 0, -1;
              0, 1, 0, 0, 1, 0, 0, 0;
              0, 0, 0, 1, 0, 0, 1, 0;
              0, -1, 0, 0, 1, 0, 0, 0;
              0, 0, 0, 1, 0, 0, -1, 0;
              1, 0, 0, 0, 0, 1, 0, 0;
              0, 0, -1, 0, 0, 0, 0, -1]
          : Matrix (Fin 8) (Fin 8) ℝ) i j := by
    intro i j
    refine (spec_6_1 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(5, 1)` (transpose of `(1, 5)`, `16 × 16`) -/

private def rowsT_5_1 : Fin 16 → ℕ :=
  ![39367,
    354303,
    3188727,
    28698543,
    6564,
    59076,
    531684,
    4785156,
    6567,
    118125,
    1063125,
    4787343,
    19684,
    354312,
    3188808,
    14349636]

private def rowsF_1_5 : Fin 16 → ℕ :=
  ![531442,
    3188649,
    9565947,
    14348934,
    6642,
    39609,
    118827,
    179334,
    13203,
    39852,
    119556,
    356481,
    1062883,
    3188652,
    9565956,
    28697841]

/-- The forward `(1,5)` literal (stage-L values), decoder form. -/
def fuseLitFwd_1_5 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_1_5 i / 3 ^ (j : ℕ) % 3)

private def litT_5_1 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_5_1 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(5,1)` codes are the Koszul-signed column
transposition of the `(1,5)` codes, against the Lean parity tables. -/
private theorem codes_5_1 : ∀ (i : Fin 16) (iB : Fin 8) (jA : Fin 2),
    rowsT_5_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3
      = if realRepBasisParity 5 iB = 1 ∧ realRepBasisParity 1 jA = 1
        then fuseNegCode (rowsF_1_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
        else rowsF_1_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(5,1)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_5_1 (i : Fin 16) (iB : Fin 8) (jA : Fin 2) :
    realFuseMatrix 5 1 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 5 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 1 5 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 5) (realRep 1)
    (realRepBasis_mem 5 iB) (realRepBasis_mem 1 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 5 1 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
          (ℬ := (realRep 1).grading) ℝ (realRepBasis 5 iB)
          (realRepBasis 1 jA) :=
    gtensorBasis_apply_pair (realRepBasis 5) (realRepBasis 1) iB jA
  have hsrcR : realFuseSrcBasis 1 5 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 5).grading) ℝ (realRepBasis 1 jA)
          (realRepBasis 5 iB) :=
    gtensorBasis_apply_pair (realRepBasis 1) (realRepBasis 5) jA iB
  have e0 : realFuse 5 1
      = (gtensorComm (realRep 5) (realRep 1)).trans (realFuse 1 5) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 1 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 5) (realRep 1))
      (realFuse 1 5)
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 1 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 1 5).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 1 5) _ _))
  refine (realFuseMatrix_apply 5 1 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 1).repr
    ((realFuse 5 1).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 1).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 5 1) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 1 5 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 1 5).repr
      ((realFuse 1 5).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(5,1)`, from the forward spec. -/
private theorem spec_5_1
    (h : ∀ (i j : Fin 16), realFuseMatrix 1 5 i j = fuseLitFwd_1_5 i j) :
    ∀ (i j : Fin 16), realFuseMatrix 5 1 i j = litT_5_1 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 8) (n := 2)).surjective j
  refine (comm_5_1 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 5 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_1_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_5_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_5_1 i iB jA)

/-- **Deliverable, branch `(5,1)`** (conditional on the group-1 forward
spec at `(1,5)`): the value-pinning literal form. -/
theorem realFuseMatrix_5_1_of_forward
    (h : realFuseMatrix 1 5
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]) :
    realFuseMatrix 5 1
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  have h' : ∀ (i j : Fin 16), realFuseMatrix 1 5 i j = fuseLitFwd_1_5 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 16), realFuseMatrix 5 1 i j
      = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
              0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1;
              0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
              0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0;
              1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
              0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
              0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
          : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    refine (spec_5_1 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(7, 2)` (transpose of `(2, 7)`, `8 × 8`) -/

private def rowsT_7_2 : Fin 8 → ℕ :=
  ![1459,
    2190,
    90,
    513,
    99,
    270,
    730,
    2193]

private def rowsF_2_7 : Fin 8 → ℕ :=
  ![244,
    2196,
    84,
    756,
    165,
    783,
    487,
    2205]

/-- The forward `(2,7)` literal (stage-L values), decoder form. -/
def fuseLitFwd_2_7 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_2_7 i / 3 ^ (j : ℕ) % 3)

private def litT_7_2 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_7_2 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(7,2)` codes are the Koszul-signed column
transposition of the `(2,7)` codes, against the Lean parity tables. -/
private theorem codes_7_2 : ∀ (i : Fin 8) (iB : Fin 2) (jA : Fin 4),
    rowsT_7_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 7 iB = 1 ∧ realRepBasisParity 2 jA = 1
        then fuseNegCode (rowsF_2_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
        else rowsF_2_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(7,2)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_7_2 (i : Fin 8) (iB : Fin 2) (jA : Fin 4) :
    realFuseMatrix 7 2 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 7 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 2 7 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 7) (realRep 2)
    (realRepBasis_mem 7 iB) (realRepBasis_mem 2 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 7 2 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 2).grading) ℝ (realRepBasis 7 iB)
          (realRepBasis 2 jA) :=
    gtensorBasis_apply_pair (realRepBasis 7) (realRepBasis 2) iB jA
  have hsrcR : realFuseSrcBasis 2 7 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 7).grading) ℝ (realRepBasis 2 jA)
          (realRepBasis 7 iB) :=
    gtensorBasis_apply_pair (realRepBasis 2) (realRepBasis 7) jA iB
  have e0 : realFuse 7 2
      = (gtensorComm (realRep 7) (realRep 2)).trans (realFuse 2 7) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 2 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 7) (realRep 2))
      (realFuse 2 7)
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 2 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 2 7).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 2 7) _ _))
  refine (realFuseMatrix_apply 7 2 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 2).repr
    ((realFuse 7 2).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 2).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 7 2) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 2 7 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 2 7).repr
      ((realFuse 2 7).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(7,2)`, from the forward spec. -/
private theorem spec_7_2
    (h : ∀ (i j : Fin 8), realFuseMatrix 2 7 i j = fuseLitFwd_2_7 i j) :
    ∀ (i j : Fin 8), realFuseMatrix 7 2 i j = litT_7_2 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := 4)).surjective j
  refine (comm_7_2 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 7 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_2_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_7_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_7_2 i iB jA)

/-- **Deliverable, branch `(7,2)`** (conditional on the group-1 forward
spec at `(2,7)`): the value-pinning literal form. -/
theorem realFuseMatrix_7_2_of_forward
    (h : realFuseMatrix 2 7
      = !![1, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 1, 0, 0, 0, 0, 1;
            0, 1, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 1, 0;
            0, 1, 0, 0, -1, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 1, 0;
            1, 0, 0, 0, 0, -1, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 1]) :
    realFuseMatrix 7 2
      = !![1, 0, 0, 0, 0, 0, -1, 0;
            0, 1, 0, 0, 0, 0, 0, 1;
            0, 0, 1, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, -1, 0, 0;
            0, 0, -1, 0, 1, 0, 0, 0;
            0, 0, 0, 1, 0, 1, 0, 0;
            1, 0, 0, 0, 0, 0, 1, 0;
            0, -1, 0, 0, 0, 0, 0, 1] := by
  have h' : ∀ (i j : Fin 8), realFuseMatrix 2 7 i j = fuseLitFwd_2_7 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 8), realFuseMatrix 7 2 i j
      = (!![1, 0, 0, 0, 0, 0, -1, 0;
              0, 1, 0, 0, 0, 0, 0, 1;
              0, 0, 1, 0, 1, 0, 0, 0;
              0, 0, 0, 1, 0, -1, 0, 0;
              0, 0, -1, 0, 1, 0, 0, 0;
              0, 0, 0, 1, 0, 1, 0, 0;
              1, 0, 0, 0, 0, 0, 1, 0;
              0, -1, 0, 0, 0, 0, 0, 1]
          : Matrix (Fin 8) (Fin 8) ℝ) i j := by
    intro i j
    refine (spec_7_2 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(6, 2)` (transpose of `(2, 6)`, `16 × 16`) -/

private def rowsT_6_2 : Fin 16 → ℕ :=
  ![28816399,
    571563,
    9743169,
    1605267,
    1103031,
    28757107,
    3199599,
    9920397,
    9920319,
    3197403,
    14467249,
    551907,
    1603089,
    9743253,
    1083321,
    14408443]

private def rowsF_2_6 : Fin 16 → ℕ :=
  ![28757107,
    571563,
    5137347,
    3197403,
    1103031,
    28816399,
    3206151,
    9920319,
    9920397,
    1605267,
    14408443,
    1103733,
    1609641,
    5137431,
    572319,
    14467249]

/-- The forward `(2,6)` literal (stage-L values), decoder form. -/
def fuseLitFwd_2_6 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_2_6 i / 3 ^ (j : ℕ) % 3)

private def litT_6_2 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_6_2 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(6,2)` codes are the Koszul-signed column
transposition of the `(2,6)` codes, against the Lean parity tables. -/
private theorem codes_6_2 : ∀ (i : Fin 16) (iB : Fin 4) (jA : Fin 4),
    rowsT_6_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 6 iB = 1 ∧ realRepBasisParity 2 jA = 1
        then fuseNegCode (rowsF_2_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
        else rowsF_2_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(6,2)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_6_2 (i : Fin 16) (iB : Fin 4) (jA : Fin 4) :
    realFuseMatrix 6 2 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 6 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 2 6 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 6) (realRep 2)
    (realRepBasis_mem 6 iB) (realRepBasis_mem 2 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 6 2 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 2).grading) ℝ (realRepBasis 6 iB)
          (realRepBasis 2 jA) :=
    gtensorBasis_apply_pair (realRepBasis 6) (realRepBasis 2) iB jA
  have hsrcR : realFuseSrcBasis 2 6 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 6).grading) ℝ (realRepBasis 2 jA)
          (realRepBasis 6 iB) :=
    gtensorBasis_apply_pair (realRepBasis 2) (realRepBasis 6) jA iB
  have e0 : realFuse 6 2
      = (gtensorComm (realRep 6) (realRep 2)).trans (realFuse 2 6) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 2 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 6) (realRep 2))
      (realFuse 2 6)
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 2 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 2 6).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 2 6) _ _))
  refine (realFuseMatrix_apply 6 2 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 2).repr
    ((realFuse 6 2).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 2).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 6 2) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 2 6 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 2 6).repr
      ((realFuse 2 6).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(6,2)`, from the forward spec. -/
private theorem spec_6_2
    (h : ∀ (i j : Fin 16), realFuseMatrix 2 6 i j = fuseLitFwd_2_6 i j) :
    ∀ (i j : Fin 16), realFuseMatrix 6 2 i j = litT_6_2 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 4) (n := 4)).surjective j
  refine (comm_6_2 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 6 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_2_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_6_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_6_2 i iB jA)

/-- **Deliverable, branch `(6,2)`** (conditional on the group-1 forward
spec at `(2,6)`): the value-pinning literal form. -/
theorem realFuseMatrix_6_2_of_forward
    (h : realFuseMatrix 2 6
      = !![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
            0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0;
            0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0;
            0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0;
            1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1;
            0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, 0;
            0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0;
            0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0;
            1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
            0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0;
            0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0;
            0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0;
            0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0;
            1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1]) :
    realFuseMatrix 6 2
      = !![1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1;
            0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0;
            0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0;
            1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
            0, 0, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0, 0;
            0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0;
            0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0;
            1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1;
            0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0;
            0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0;
            0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0;
            1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  have h' : ∀ (i j : Fin 16), realFuseMatrix 2 6 i j = fuseLitFwd_2_6 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 16), realFuseMatrix 6 2 i j
      = (!![1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1;
              0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0;
              0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0;
              0, 0, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0;
              0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0;
              1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
              0, 0, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0, 0;
              0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0;
              0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0;
              0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0;
              1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1;
              0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0;
              0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0;
              0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0;
              0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0;
              1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
          : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    refine (spec_6_2 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(5, 2)` (transpose of `(2, 5)`, `32 × 32`) -/

/-- Packed row codes for `realFuseMatrix 5 2` (`32 × 32`).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_5_2 : Fin 32 → ℕ :=
  ![15251969850319,
    1235409557875839,
    282687875883,
    22897717946523,
    5084893924689,
    411876407899809,
    847332010467,
    68633892847827,
    565117412391,
    45774510403671,
    15251582410147,
    1235378175221907,
    1694620619919,
    137264270213439,
    5086056192717,
    411970551610077,
    5086056186159,
    205985276336601,
    1694620442763,
    68637379632957,
    7626372345649,
    1235378176816311,
    282558735747,
    45774515184453,
    847331833329,
    137267756997111,
    5084893931253,
    206079418983987,
    564988272201,
    22897722731679,
    7625984944843,
    1235409556281597]

private def rowsF_2_5 : Fin 32 → ℕ :=
  ![411785751032749,
    1235367713628597,
    283204909629,
    848454061743,
    22939554580749,
    68724520583103,
    5083779486429,
    15251481948357,
    565634446839,
    1695742673373,
    411789237876199,
    1235357253098247,
    5083827316119,
    15251338459287,
    45816347035719,
    137354897948013,
    45816347042271,
    68818663761957,
    2541918441069,
    15251352808437,
    205894618997149,
    1235357253275397,
    565634977551,
    849616325397,
    2541956704821,
    15251467599693,
    22939554587319,
    137449041126813,
    283205441799,
    1696904932653,
    205898105722501,
    1235367713451453]

/-- The forward `(2,5)` literal (stage-L values), decoder form. -/
def fuseLitFwd_2_5 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_2_5 i / 3 ^ (j : ℕ) % 3)

/-- **The `(5,2)` transpose literal** (stage-L values), decoder form. -/
def fuseLit_5_2 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (fuseRows_5_2 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(5,2)` codes are the Koszul-signed column
transposition of the `(2,5)` codes, against the Lean parity tables. -/
private theorem codes_5_2 : ∀ (i : Fin 32) (iB : Fin 8) (jA : Fin 4),
    fuseRows_5_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 5 iB = 1 ∧ realRepBasisParity 2 jA = 1
        then fuseNegCode (rowsF_2_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
        else rowsF_2_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(5,2)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_5_2 (i : Fin 32) (iB : Fin 8) (jA : Fin 4) :
    realFuseMatrix 5 2 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 5 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 2 5 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 5) (realRep 2)
    (realRepBasis_mem 5 iB) (realRepBasis_mem 2 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 5 2 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
          (ℬ := (realRep 2).grading) ℝ (realRepBasis 5 iB)
          (realRepBasis 2 jA) :=
    gtensorBasis_apply_pair (realRepBasis 5) (realRepBasis 2) iB jA
  have hsrcR : realFuseSrcBasis 2 5 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 5).grading) ℝ (realRepBasis 2 jA)
          (realRepBasis 5 iB) :=
    gtensorBasis_apply_pair (realRepBasis 2) (realRepBasis 5) jA iB
  have e0 : realFuse 5 2
      = (gtensorComm (realRep 5) (realRep 2)).trans (realFuse 2 5) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 2 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 5) (realRep 2))
      (realFuse 2 5)
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 2 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 2 5).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 2 5) _ _))
  refine (realFuseMatrix_apply 5 2 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 2).repr
    ((realFuse 5 2).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 2).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 5 2) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 2 5 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 2 5).repr
      ((realFuse 2 5).toAlgEquiv t)) i) hsrcR)).symm

/-- **Deliverable, branch `(5,2)`** (conditional on the group-1 forward
spec at `(2,5)`): entrywise value pinning, stage-L packed shape. -/
theorem realFuseMatrix_5_2_of_forward
    (h : ∀ (i j : Fin 32), realFuseMatrix 2 5 i j = fuseLitFwd_2_5 i j) :
    ∀ (i j : Fin 32), realFuseMatrix 5 2 i j = fuseLit_5_2 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 8) (n := 4)).surjective j
  refine (comm_5_2 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 5 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_2_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
      = fuseDecode (fuseRows_5_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_5_2 i iB jA)


/-! ### Branch `(7, 3)` (transpose of `(3, 7)`, `16 × 16`) -/

private def rowsT_7_3 : Fin 16 → ℕ :=
  ![1062883,
    1594326,
    4782978,
    28697841,
    6642,
    39609,
    118827,
    179334,
    6723,
    19926,
    59778,
    181521,
    531442,
    1594329,
    4782987,
    14348934]

private def rowsF_3_7 : Fin 16 → ℕ :=
  ![19684,
    177156,
    1594404,
    14349636,
    6564,
    59076,
    531684,
    4785156,
    13125,
    59103,
    531927,
    9568125,
    39367,
    177165,
    1594485,
    28698543]

/-- The forward `(3,7)` literal (stage-L values), decoder form. -/
def fuseLitFwd_3_7 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_3_7 i / 3 ^ (j : ℕ) % 3)

private def litT_7_3 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_7_3 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(7,3)` codes are the Koszul-signed column
transposition of the `(3,7)` codes, against the Lean parity tables. -/
private theorem codes_7_3 : ∀ (i : Fin 16) (iB : Fin 2) (jA : Fin 8),
    rowsT_7_3 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3
      = if realRepBasisParity 7 iB = 1 ∧ realRepBasisParity 3 jA = 1
        then fuseNegCode (rowsF_3_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
        else rowsF_3_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(7,3)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_7_3 (i : Fin 16) (iB : Fin 2) (jA : Fin 8) :
    realFuseMatrix 7 3 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 7 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 3 7 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 7) (realRep 3)
    (realRepBasis_mem 7 iB) (realRepBasis_mem 3 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 7 3 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 3).grading) ℝ (realRepBasis 7 iB)
          (realRepBasis 3 jA) :=
    gtensorBasis_apply_pair (realRepBasis 7) (realRepBasis 3) iB jA
  have hsrcR : realFuseSrcBasis 3 7 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
          (ℬ := (realRep 7).grading) ℝ (realRepBasis 3 jA)
          (realRepBasis 7 iB) :=
    gtensorBasis_apply_pair (realRepBasis 3) (realRepBasis 7) jA iB
  have e0 : realFuse 7 3
      = (gtensorComm (realRep 7) (realRep 3)).trans (realFuse 3 7) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 3).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 3 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 7) (realRep 3))
      (realFuse 3 7)
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 3).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 3 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 3 7).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 3 7) _ _))
  refine (realFuseMatrix_apply 7 3 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 3).repr
    ((realFuse 7 3).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 3).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 7 3) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 3 7 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 3 7).repr
      ((realFuse 3 7).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(7,3)`, from the forward spec. -/
private theorem spec_7_3
    (h : ∀ (i j : Fin 16), realFuseMatrix 3 7 i j = fuseLitFwd_3_7 i j) :
    ∀ (i j : Fin 16), realFuseMatrix 7 3 i j = litT_7_3 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := 8)).surjective j
  refine (comm_7_3 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 7 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_3_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_7_3 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_7_3 i iB jA)

/-- **Deliverable, branch `(7,3)`** (conditional on the group-1 forward
spec at `(3,7)`): the value-pinning literal form. -/
theorem realFuseMatrix_7_3_of_forward
    (h : realFuseMatrix 3 7
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
            0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]) :
    realFuseMatrix 7 3
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  have h' : ∀ (i j : Fin 16), realFuseMatrix 3 7 i j = fuseLitFwd_3_7 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 16), realFuseMatrix 7 3 i j
      = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
              0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
              0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
              0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0;
              0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0;
              1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
              0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
              0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
              0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
          : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    refine (spec_7_3 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(6, 3)` (transpose of `(3, 6)`, `32 × 32`) -/

/-- Packed row codes for `realFuseMatrix 6 3` (`32 × 32`).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_6_3 : Fin 32 → ℕ :=
  ![411789237876199,
    1235357253098247,
    283204909629,
    848454061743,
    45784965976101,
    137449041126813,
    2541918441069,
    7625870114463,
    565634446839,
    1695742673373,
    411785751032749,
    1235367713628597,
    5083784269479,
    15251467599693,
    45816347042271,
    137354897928303,
    45816347035719,
    68818663742247,
    5083779486429,
    7625740974543,
    205898105722501,
    1235367713451453,
    282817489869,
    1695741076863,
    2541913658181,
    15251338459287,
    45784965982671,
    68724520583103,
    565247025621,
    848452469607,
    205894618997149,
    1235357253275397]

private def rowsF_3_6 : Fin 32 → ℕ :=
  ![15251582410147,
    1235378175221907,
    282687875883,
    22897717946523,
    2544190357827,
    206079418983987,
    1694620442763,
    137264255863803,
    565117412391,
    45774510403671,
    15251969850319,
    1235409557875839,
    1694663666631,
    137267756997111,
    5086056186159,
    411970551078879,
    5086056192717,
    205985275805403,
    847332010467,
    137267742648933,
    7625984944843,
    1235409556281597,
    565117471413,
    22887257595507,
    847374880041,
    137264270213439,
    2544190364391,
    411876407899809,
    282687934959,
    45764050048281,
    7626372345649,
    1235378176816311]

/-- The forward `(3,6)` literal (stage-L values), decoder form. -/
def fuseLitFwd_3_6 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_3_6 i / 3 ^ (j : ℕ) % 3)

/-- **The `(6,3)` transpose literal** (stage-L values), decoder form. -/
def fuseLit_6_3 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (fuseRows_6_3 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(6,3)` codes are the Koszul-signed column
transposition of the `(3,6)` codes, against the Lean parity tables. -/
private theorem codes_6_3 : ∀ (i : Fin 32) (iB : Fin 4) (jA : Fin 8),
    fuseRows_6_3 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3
      = if realRepBasisParity 6 iB = 1 ∧ realRepBasisParity 3 jA = 1
        then fuseNegCode (rowsF_3_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
        else rowsF_3_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(6,3)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_6_3 (i : Fin 32) (iB : Fin 4) (jA : Fin 8) :
    realFuseMatrix 6 3 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 6 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 3 6 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 6) (realRep 3)
    (realRepBasis_mem 6 iB) (realRepBasis_mem 3 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 6 3 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 3).grading) ℝ (realRepBasis 6 iB)
          (realRepBasis 3 jA) :=
    gtensorBasis_apply_pair (realRepBasis 6) (realRepBasis 3) iB jA
  have hsrcR : realFuseSrcBasis 3 6 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
          (ℬ := (realRep 6).grading) ℝ (realRepBasis 3 jA)
          (realRepBasis 6 iB) :=
    gtensorBasis_apply_pair (realRepBasis 3) (realRepBasis 6) jA iB
  have e0 : realFuse 6 3
      = (gtensorComm (realRep 6) (realRep 3)).trans (realFuse 3 6) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 3).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 3 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 6) (realRep 3))
      (realFuse 3 6)
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 3).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 3 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 3 6).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 3 6) _ _))
  refine (realFuseMatrix_apply 6 3 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 3).repr
    ((realFuse 6 3).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 3).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 6 3) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 3 6 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 3 6).repr
      ((realFuse 3 6).toAlgEquiv t)) i) hsrcR)).symm

/-- **Deliverable, branch `(6,3)`** (conditional on the group-1 forward
spec at `(3,6)`): entrywise value pinning, stage-L packed shape. -/
theorem realFuseMatrix_6_3_of_forward
    (h : ∀ (i j : Fin 32), realFuseMatrix 3 6 i j = fuseLitFwd_3_6 i j) :
    ∀ (i j : Fin 32), realFuseMatrix 6 3 i j = fuseLit_6_3 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 4) (n := 8)).surjective j
  refine (comm_6_3 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 6 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_3_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
      = fuseDecode (fuseRows_6_3 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_6_3 i iB jA)


/-! ### Branch `(5, 3)` (transpose of `(3, 5)`, `64 × 64`) -/

/-- Packed row codes for `realFuseMatrix 5 3` (`64 × 64`).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_5_3 : Fin 64 → ℕ :=
  ![1144677578813769192629561722612,
    84821091912810997309609384194,
    4712282403378515849285854092,
    3140166221154597882157268706,
    763389749345901996973449526446,
    127186423579592275411989454428,
    28261490117941245669035906466,
    523587151244623860584766252,
    42429933633542238924725511234,
    1144619426122453446018650193628,
    1570123322055907719194433186,
    4714436109499256960252803908,
    254359898406591738519834355572,
    763215299150121974611929391086,
    1046934784322038819689734628,
    28262208052401933867412809186,
    9422411112782426237407565652,
    3140245987581066203330481474,
    1144619429076616050308976828652,
    42429942500532913447686906786,
    14131104062675507510060822274,
    523826450623908900010593972,
    763215300135343158158403531534,
    254359924994055244912419088548,
    1570203088515593143012249326,
    9424564794587836241974300212,
    84821100771696562091391900174,
    1144677575859306383817446119372,
    1047174083601215015332653012,
    14131821924190203016858271406,
    127186450169757486934497390468,
    763389748361581376155025724066,
    763215300135343160701431614772,
    254359924994055245759664474114,
    14131104062674889868044003532,
    523826450623886012753005026,
    2289238849290293973339080215726,
    84801708663090762136564471068,
    4714436097336032440628788386,
    1570122993815617506342672492,
    127186450169757486087165557166,
    763389748361581378695729297492,
    1047174083601237881659969614,
    14131821924189585312082522092,
    42410550391927114057718550588,
    2289180702507603639829836123394,
    3140165892880953305906176332,
    4712282415530622247776759054,
    28261490117940627964256968668,
    523587151244646726921653166,
    763389749345901994432745966148,
    127186423579592276259320933454,
    9424564806739942640464141806,
    1570202760241948566789853308,
    2289180699553140846269690331106,
    42410559250812678274900273932,
    1046934784322015932441707246,
    28262208052401316225399179252,
    254359898406591737672588615694,
    763215299150121972068901294732,
    3140245659340775990507420052,
    9422411100619201717784612526,
    84801717530081437224643219908,
    2289238852244456592879826979746]

private def rowsF_3_5 : Fin 64 → ℕ :=
  ![2289238852244456592879826979746,
    42410559250812678274900273932,
    9424564794587630444984852706,
    1570122993815617506342672492,
    763389748361581376155025724066,
    127179962499053901303651946572,
    28262208052401933867412809186,
    523587151244623860584766252,
    84801717530081437224643219908,
    2289180699553140846269690331106,
    1570203088515661776890746788,
    4714436097336032440628788386,
    127186450169757486934497390468,
    381869323884185263162350656226,
    1046934784322038819689734628,
    28261490117941245669035906466,
    4714436109499050974976999234,
    3140166221154666516007069812,
    2289180702507603639829836123394,
    42429942500532913730245642452,
    28261490154415477361618201154,
    523826450623908900010593972,
    381869324869406446708824796674,
    254353463913516870804081580692,
    3140245659340775990507420052,
    9424564806739942640464141806,
    84821100771696561809091562932,
    2289238849290293973339080215726,
    1047174083601215015332653012,
    28262208015930172868415650286,
    254359898406591738519834355572,
    763389749345901996973449526446,
    381869324869406449251852893028,
    254353463913516869956750101666,
    14131821924189585312082522092,
    1046934674853018143083156494,
    1144677575859306383817446119372,
    84801708663090762419123206734,
    4714436109499256960252803908,
    3140166221154597882157268706,
    254359898406591737672588615694,
    763389749345901994432745966148,
    523587041875666274176191906,
    14131104062674889868044003532,
    42410550391927113775418213346,
    1144619429076616050308976828652,
    3140245659340707363602489934,
    9424564806739736843475757668,
    14131104026204364153077293308,
    1047173974232257428914508354,
    763389748361581378695729297492,
    127179962499053900456406561006,
    9424564794587836241974300212,
    1570122993815548879466441646,
    1144619426122453446018650193628,
    84821091912810997309609384194,
    523826341154888223394454274,
    14131821960665052414219503892,
    127186450169757486087165557166,
    381869323884185260619322572988,
    1570203088515593143012249326,
    4714436097335826455354046108,
    42429933633542238924725511234,
    1144677578813769192629561722612]

/-- The forward `(3,5)` literal (stage-L values), decoder form. -/
def fuseLitFwd_3_5 : Matrix (Fin 64) (Fin 64) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_3_5 i / 3 ^ (j : ℕ) % 3)

/-- **The `(5,3)` transpose literal** (stage-L values), decoder form. -/
def fuseLit_5_3 : Matrix (Fin 64) (Fin 64) ℝ :=
  Matrix.of fun i j => fuseDecode (fuseRows_5_3 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(5,3)` codes are the Koszul-signed column
transposition of the `(3,5)` codes, against the Lean parity tables. -/
private theorem codes_5_3 : ∀ (i : Fin 64) (iB : Fin 8) (jA : Fin 8),
    fuseRows_5_3 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3
      = if realRepBasisParity 5 iB = 1 ∧ realRepBasisParity 3 jA = 1
        then fuseNegCode (rowsF_3_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
        else rowsF_3_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(5,3)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_5_3 (i : Fin 64) (iB : Fin 8) (jA : Fin 8) :
    realFuseMatrix 5 3 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 5 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 3 5 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 5) (realRep 3)
    (realRepBasis_mem 5 iB) (realRepBasis_mem 3 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 5 3 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
          (ℬ := (realRep 3).grading) ℝ (realRepBasis 5 iB)
          (realRepBasis 3 jA) :=
    gtensorBasis_apply_pair (realRepBasis 5) (realRepBasis 3) iB jA
  have hsrcR : realFuseSrcBasis 3 5 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
          (ℬ := (realRep 5).grading) ℝ (realRepBasis 3 jA)
          (realRepBasis 5 iB) :=
    gtensorBasis_apply_pair (realRepBasis 3) (realRepBasis 5) jA iB
  have e0 : realFuse 5 3
      = (gtensorComm (realRep 5) (realRep 3)).trans (realFuse 3 5) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 3).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 3 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 5) (realRep 3))
      (realFuse 3 5)
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 3).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 3 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 3 5).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 3 5) _ _))
  refine (realFuseMatrix_apply 5 3 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 3).repr
    ((realFuse 5 3).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 3).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 5 3) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 3 5 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 3 5).repr
      ((realFuse 3 5).toAlgEquiv t)) i) hsrcR)).symm

/-- **Deliverable, branch `(5,3)`** (conditional on the group-1 forward
spec at `(3,5)`): entrywise value pinning, stage-L packed shape. -/
theorem realFuseMatrix_5_3_of_forward
    (h : ∀ (i j : Fin 64), realFuseMatrix 3 5 i j = fuseLitFwd_3_5 i j) :
    ∀ (i j : Fin 64), realFuseMatrix 5 3 i j = fuseLit_5_3 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 8) (n := 8)).surjective j
  refine (comm_5_3 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 3 jA * realRepBasisParity 5 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_3_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
      = fuseDecode (fuseRows_5_3 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_5_3 i iB jA)


/-! ### Branch `(2, 4)` (transpose of `(4, 2)`, `16 × 16`) -/

private def rowsT_2_4 : Fin 16 → ℕ :=
  ![1594324,
    355752,
    120285,
    1062885,
    7047,
    9565965,
    14348916,
    19764,
    13608,
    9565992,
    14348925,
    39447,
    3188647,
    355023,
    122472,
    531444]

private def rowsF_4_2 : Fin 16 → ℕ :=
  ![2188,
    9605304,
    1712421,
    135,
    495,
    885735,
    14355468,
    732,
    504,
    1417176,
    14362029,
    1461,
    4375,
    9585621,
    3306744,
    108]

/-- The forward `(4,2)` literal (stage-L values), decoder form. -/
def fuseLitFwd_4_2 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_4_2 i / 3 ^ (j : ℕ) % 3)

private def litT_2_4 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_2_4 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(2,4)` codes are the Koszul-signed column
transposition of the `(4,2)` codes, against the Lean parity tables. -/
private theorem codes_2_4 : ∀ (i : Fin 16) (iB : Fin 4) (jA : Fin 4),
    rowsT_2_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 2 iB = 1 ∧ realRepBasisParity 4 jA = 1
        then fuseNegCode (rowsF_4_2 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
        else rowsF_4_2 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(2,4)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_2_4 (i : Fin 16) (iB : Fin 4) (jA : Fin 4) :
    realFuseMatrix 2 4 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 2 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 4 2 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 2) (realRep 4)
    (realRepBasis_mem 2 iB) (realRepBasis_mem 4 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 2 4 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 4).grading) ℝ (realRepBasis 2 iB)
          (realRepBasis 4 jA) :=
    gtensorBasis_apply_pair (realRepBasis 2) (realRepBasis 4) iB jA
  have hsrcR : realFuseSrcBasis 4 2 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 4).grading)
          (ℬ := (realRep 2).grading) ℝ (realRepBasis 4 jA)
          (realRepBasis 2 iB) :=
    gtensorBasis_apply_pair (realRepBasis 4) (realRepBasis 2) jA iB
  have e0 : realFuse 2 4
      = (gtensorComm (realRep 2) (realRep 4)).trans (realFuse 4 2) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 2 iB)
        (realRepBasis 4 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 2) (realRep 4))
      (realFuse 4 2)
      (GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 2 iB)
        (realRepBasis 4 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 4 2).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 4 2) _ _))
  refine (realFuseMatrix_apply 2 4 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 2 4).repr
    ((realFuse 2 4).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 2 4).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 2 4) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 2 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 4 2 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 4 2).repr
      ((realFuse 4 2).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(2,4)`, from the forward spec. -/
private theorem spec_2_4
    (h : ∀ (i j : Fin 16), realFuseMatrix 4 2 i j = fuseLitFwd_4_2 i j) :
    ∀ (i j : Fin 16), realFuseMatrix 2 4 i j = litT_2_4 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 4) (n := 4)).surjective j
  refine (comm_2_4 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 2 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 2 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_4_2 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_2_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_2_4 i iB jA)

/-- **Deliverable, branch `(2,4)`** (conditional on the group-1 forward
spec at `(4,2)`): the value-pinning literal form. -/
theorem realFuseMatrix_2_4_of_forward
    (h : realFuseMatrix 4 2
      = !![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0;
            0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
            0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1;
            0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0;
            0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) :
    realFuseMatrix 2 4
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  have h' : ∀ (i j : Fin 16), realFuseMatrix 4 2 i j = fuseLitFwd_4_2 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 16), realFuseMatrix 2 4 i j
      = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
              0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0;
              0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
              0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
              0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
              0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
              0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
              1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0;
              0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
          : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    refine (spec_2_4 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(6, 4)` (transpose of `(4, 6)`, `16 × 16`) -/

private def rowsT_6_4 : Fin 16 → ℕ :=
  ![3188647,
    355752,
    63423,
    531444,
    7047,
    9565992,
    28697823,
    19764,
    6804,
    4783023,
    14348916,
    19845,
    1594324,
    355023,
    61236,
    1062885]

private def rowsF_4_6 : Fin 16 → ℕ :=
  ![4375,
    9605304,
    3247695,
    108,
    495,
    1417176,
    28704375,
    732,
    252,
    1240029,
    14355468,
    735,
    2188,
    9585621,
    1653372,
    135]

/-- The forward `(4,6)` literal (stage-L values), decoder form. -/
def fuseLitFwd_4_6 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_4_6 i / 3 ^ (j : ℕ) % 3)

private def litT_6_4 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_6_4 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(6,4)` codes are the Koszul-signed column
transposition of the `(4,6)` codes, against the Lean parity tables. -/
private theorem codes_6_4 : ∀ (i : Fin 16) (iB : Fin 4) (jA : Fin 4),
    rowsT_6_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 6 iB = 1 ∧ realRepBasisParity 4 jA = 1
        then fuseNegCode (rowsF_4_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
        else rowsF_4_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(6,4)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_6_4 (i : Fin 16) (iB : Fin 4) (jA : Fin 4) :
    realFuseMatrix 6 4 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 6 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 4 6 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 6) (realRep 4)
    (realRepBasis_mem 6 iB) (realRepBasis_mem 4 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 6 4 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 4).grading) ℝ (realRepBasis 6 iB)
          (realRepBasis 4 jA) :=
    gtensorBasis_apply_pair (realRepBasis 6) (realRepBasis 4) iB jA
  have hsrcR : realFuseSrcBasis 4 6 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 4).grading)
          (ℬ := (realRep 6).grading) ℝ (realRepBasis 4 jA)
          (realRepBasis 6 iB) :=
    gtensorBasis_apply_pair (realRepBasis 4) (realRepBasis 6) jA iB
  have e0 : realFuse 6 4
      = (gtensorComm (realRep 6) (realRep 4)).trans (realFuse 4 6) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 4 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 6) (realRep 4))
      (realFuse 4 6)
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 4 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 4 6).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 4 6) _ _))
  refine (realFuseMatrix_apply 6 4 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 4).repr
    ((realFuse 6 4).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 4).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 6 4) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 4 6 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 4 6).repr
      ((realFuse 4 6).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(6,4)`, from the forward spec. -/
private theorem spec_6_4
    (h : ∀ (i j : Fin 16), realFuseMatrix 4 6 i j = fuseLitFwd_4_6 i j) :
    ∀ (i j : Fin 16), realFuseMatrix 6 4 i j = litT_6_4 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 4) (n := 4)).surjective j
  refine (comm_6_4 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 6 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_4_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_6_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_6_4 i iB jA)

/-- **Deliverable, branch `(6,4)`** (conditional on the group-1 forward
spec at `(4,6)`): the value-pinning literal form. -/
theorem realFuseMatrix_6_4_of_forward
    (h : realFuseMatrix 4 6
      = !![1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0;
            0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1;
            0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
            0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
            0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) :
    realFuseMatrix 6 4
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] := by
  have h' : ∀ (i j : Fin 16), realFuseMatrix 4 6 i j = fuseLitFwd_4_6 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 16), realFuseMatrix 6 4 i j
      = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0;
              0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
              0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
              0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
              0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
              1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
              0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]
          : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    refine (spec_6_4 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(3, 4)` (transpose of `(4, 3)`, `32 × 32`) -/

/-- Packed row codes for `realFuseMatrix 3 4` (`32 × 32`).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_3_4 : Fin 32 → ℕ :=
  ![2730153780307,
    22877051091039,
    575333775081,
    205893456637347,
    68630420531889,
    15313958152077,
    617673783711483,
    850784959809,
    292904238609,
    411784588732077,
    2636012195803,
    22876921773729,
    617674171138533,
    854266961241,
    137260797898959,
    7688360667093,
    137260840943493,
    15313957620639,
    1235347567415919,
    850780176867,
    5177876429809,
    22877050913163,
    303364591803,
    205893456657111,
    1235347180001991,
    854271744237,
    68630463580797,
    7688360135649,
    585794128293,
    411784588751679,
    5272021202959,
    22876921950147]

private def rowsF_4_3 : Fin 32 → ℕ :=
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

/-- The forward `(4,3)` literal (stage-L values), decoder form. -/
def fuseLitFwd_4_3 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_4_3 i / 3 ^ (j : ℕ) % 3)

/-- **The `(3,4)` transpose literal** (stage-L values), decoder form. -/
def fuseLit_3_4 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (fuseRows_3_4 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(3,4)` codes are the Koszul-signed column
transposition of the `(4,3)` codes, against the Lean parity tables. -/
private theorem codes_3_4 : ∀ (i : Fin 32) (iB : Fin 8) (jA : Fin 4),
    fuseRows_3_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 3 iB = 1 ∧ realRepBasisParity 4 jA = 1
        then fuseNegCode (rowsF_4_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
        else rowsF_4_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(3,4)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_3_4 (i : Fin 32) (iB : Fin 8) (jA : Fin 4) :
    realFuseMatrix 3 4 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 3 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 4 3 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 3) (realRep 4)
    (realRepBasis_mem 3 iB) (realRepBasis_mem 4 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 3 4 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
          (ℬ := (realRep 4).grading) ℝ (realRepBasis 3 iB)
          (realRepBasis 4 jA) :=
    gtensorBasis_apply_pair (realRepBasis 3) (realRepBasis 4) iB jA
  have hsrcR : realFuseSrcBasis 4 3 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 4).grading)
          (ℬ := (realRep 3).grading) ℝ (realRepBasis 4 jA)
          (realRepBasis 3 iB) :=
    gtensorBasis_apply_pair (realRepBasis 4) (realRepBasis 3) jA iB
  have e0 : realFuse 3 4
      = (gtensorComm (realRep 3) (realRep 4)).trans (realFuse 4 3) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 3 iB)
        (realRepBasis 4 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 3) (realRep 4))
      (realFuse 4 3)
      (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 3 iB)
        (realRepBasis 4 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 4 3).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 4 3) _ _))
  refine (realFuseMatrix_apply 3 4 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 3 4).repr
    ((realFuse 3 4).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 3 4).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 3 4) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 3 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 4 3 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 4 3).repr
      ((realFuse 4 3).toAlgEquiv t)) i) hsrcR)).symm

/-- **Deliverable, branch `(3,4)`** (conditional on the group-1 forward
spec at `(4,3)`): entrywise value pinning, stage-L packed shape. -/
theorem realFuseMatrix_3_4_of_forward
    (h : ∀ (i j : Fin 32), realFuseMatrix 4 3 i j = fuseLitFwd_4_3 i j) :
    ∀ (i j : Fin 32), realFuseMatrix 3 4 i j = fuseLit_3_4 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 8) (n := 4)).surjective j
  refine (comm_3_4 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 3 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 3 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_4_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
      = fuseDecode (fuseRows_3_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_3_4 i iB jA)


/-! ### Branch `(5, 4)` (transpose of `(4, 5)`, `32 × 32`) -/

/-- Packed row codes for `realFuseMatrix 5 4` (`32 × 32`).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_5_4 : Fin 32 → ℕ :=
  ![2730155374630,
    22876921950876,
    575348123988,
    205892294375880,
    137260797839910,
    15313957620636,
    617674171131972,
    1701560353680,
    292918587516,
    411783426470610,
    2636010601480,
    22877050913892,
    1235347567415676,
    854271744210,
    137260840945680,
    15282577092468,
    137260797896772,
    7656979076040,
    1235347179995430,
    1701555570684,
    5177878024132,
    22876921773000,
    575333775090,
    411784588731996,
    617673783711240,
    854266961268,
    137260840884444,
    7688360667090,
    292904238600,
    205893456637428,
    5272019608636,
    22877051090310]

private def rowsF_4_5 : Fin 32 → ℕ :=
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

/-- The forward `(4,5)` literal (stage-L values), decoder form. -/
def fuseLitFwd_4_5 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_4_5 i / 3 ^ (j : ℕ) % 3)

/-- **The `(5,4)` transpose literal** (stage-L values), decoder form. -/
def fuseLit_5_4 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (fuseRows_5_4 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(5,4)` codes are the Koszul-signed column
transposition of the `(4,5)` codes, against the Lean parity tables. -/
private theorem codes_5_4 : ∀ (i : Fin 32) (iB : Fin 8) (jA : Fin 4),
    fuseRows_5_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 5 iB = 1 ∧ realRepBasisParity 4 jA = 1
        then fuseNegCode (rowsF_4_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
        else rowsF_4_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(5,4)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_5_4 (i : Fin 32) (iB : Fin 8) (jA : Fin 4) :
    realFuseMatrix 5 4 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 5 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 4 5 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 5) (realRep 4)
    (realRepBasis_mem 5 iB) (realRepBasis_mem 4 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 5 4 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
          (ℬ := (realRep 4).grading) ℝ (realRepBasis 5 iB)
          (realRepBasis 4 jA) :=
    gtensorBasis_apply_pair (realRepBasis 5) (realRepBasis 4) iB jA
  have hsrcR : realFuseSrcBasis 4 5 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 4).grading)
          (ℬ := (realRep 5).grading) ℝ (realRepBasis 4 jA)
          (realRepBasis 5 iB) :=
    gtensorBasis_apply_pair (realRepBasis 4) (realRepBasis 5) jA iB
  have e0 : realFuse 5 4
      = (gtensorComm (realRep 5) (realRep 4)).trans (realFuse 4 5) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 4 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 5) (realRep 4))
      (realFuse 4 5)
      (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
        (ℬ := (realRep 4).grading) ℝ (realRepBasis 5 iB)
        (realRepBasis 4 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 4 5).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 4 5) _ _))
  refine (realFuseMatrix_apply 5 4 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 4).repr
    ((realFuse 5 4).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 5 4).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 5 4) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 4 5 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 4 5).repr
      ((realFuse 4 5).toAlgEquiv t)) i) hsrcR)).symm

/-- **Deliverable, branch `(5,4)`** (conditional on the group-1 forward
spec at `(4,5)`): entrywise value pinning, stage-L packed shape. -/
theorem realFuseMatrix_5_4_of_forward
    (h : ∀ (i j : Fin 32), realFuseMatrix 4 5 i j = fuseLitFwd_4_5 i j) :
    ∀ (i j : Fin 32), realFuseMatrix 5 4 i j = fuseLit_5_4 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 8) (n := 4)).surjective j
  refine (comm_5_4 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 5 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 4 jA * realRepBasisParity 5 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_4_5 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
      = fuseDecode (fuseRows_5_4 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_5_4 i iB jA)


/-! ### Branch `(7, 5)` (transpose of `(5, 7)`, `16 × 16`) -/

private def rowsT_7_5 : Fin 16 → ℕ :=
  ![14348908,
    531495,
    118584,
    21141,
    4782972,
    3188655,
    177228,
    10935,
    9565941,
    3188664,
    177309,
    17496,
    28697815,
    531468,
    118341,
    40824]

private def rowsF_5_7 : Fin 16 → ℕ :=
  ![28697815,
    40824,
    118341,
    1062936,
    1594332,
    354375,
    8748,
    9565941,
    3188655,
    354456,
    15309,
    9565944,
    14348908,
    40095,
    59292,
    1062909]

/-- The forward `(5,7)` literal (stage-L values), decoder form. -/
def fuseLitFwd_5_7 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_5_7 i / 3 ^ (j : ℕ) % 3)

private def litT_7_5 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_7_5 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(7,5)` codes are the Koszul-signed column
transposition of the `(5,7)` codes, against the Lean parity tables. -/
private theorem codes_7_5 : ∀ (i : Fin 16) (iB : Fin 2) (jA : Fin 8),
    rowsT_7_5 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3
      = if realRepBasisParity 7 iB = 1 ∧ realRepBasisParity 5 jA = 1
        then fuseNegCode (rowsF_5_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
        else rowsF_5_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(7,5)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_7_5 (i : Fin 16) (iB : Fin 2) (jA : Fin 8) :
    realFuseMatrix 7 5 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 7 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 5 7 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 7) (realRep 5)
    (realRepBasis_mem 7 iB) (realRepBasis_mem 5 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 7 5 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
          (ℬ := (realRep 5).grading) ℝ (realRepBasis 7 iB)
          (realRepBasis 5 jA) :=
    gtensorBasis_apply_pair (realRepBasis 7) (realRepBasis 5) iB jA
  have hsrcR : realFuseSrcBasis 5 7 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
          (ℬ := (realRep 7).grading) ℝ (realRepBasis 5 jA)
          (realRepBasis 7 iB) :=
    gtensorBasis_apply_pair (realRepBasis 5) (realRepBasis 7) jA iB
  have e0 : realFuse 7 5
      = (gtensorComm (realRep 7) (realRep 5)).trans (realFuse 5 7) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 5).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 5 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 7) (realRep 5))
      (realFuse 5 7)
      (GradedTensorProduct.tmul (𝒜 := (realRep 7).grading)
        (ℬ := (realRep 5).grading) ℝ (realRepBasis 7 iB)
        (realRepBasis 5 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 5 7).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 5 7) _ _))
  refine (realFuseMatrix_apply 7 5 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 5).repr
    ((realFuse 7 5).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 7 5).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 7 5) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 5 7 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 5 7).repr
      ((realFuse 5 7).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(7,5)`, from the forward spec. -/
private theorem spec_7_5
    (h : ∀ (i j : Fin 16), realFuseMatrix 5 7 i j = fuseLitFwd_5_7 i j) :
    ∀ (i j : Fin 16), realFuseMatrix 7 5 i j = litT_7_5 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := 8)).surjective j
  refine (comm_7_5 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 7 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 7 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_5_7 i / 3 ^ ((iB : ℕ) + 2 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_7_5 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_7_5 i iB jA)

/-- **Deliverable, branch `(7,5)`** (conditional on the group-1 forward
spec at `(5,7)`): the value-pinning literal form. -/
theorem realFuseMatrix_7_5_of_forward
    (h : realFuseMatrix 5 7
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]) :
    realFuseMatrix 7 5
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0] := by
  have h' : ∀ (i j : Fin 16), realFuseMatrix 5 7 i j = fuseLitFwd_5_7 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 16), realFuseMatrix 7 5 i j
      = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
              0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
              0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
              0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
              0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
              1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
              0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0]
          : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    refine (spec_7_5 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(6, 5)` (transpose of `(5, 6)`, `32 × 32`) -/

/-- Packed row codes for `realFuseMatrix 6 5` (`32 × 32`).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_6_5 : Fin 32 → ℕ :=
  ![14348908,
    5094192009861,
    878669669052,
    531495,
    22877954716428,
    40095,
    118584,
    1235346835614615,
    4782972,
    7632571053789,
    376572715308,
    3188655,
    137261529570744,
    15309,
    177228,
    411782393329461,
    9565941,
    15258168538776,
    470715894135,
    3188664,
    68631152205861,
    8748,
    177309,
    411782522469624,
    28697815,
    2552326181532,
    910050728661,
    531468,
    45754747171389,
    20412,
    118341,
    1235346878661336]

private def rowsF_5_6 : Fin 32 → ℕ :=
  ![137260754729767,
    31381413903,
    2541865830516,
    259343208,
    1167044436,
    282429536724,
    6973588485,
    1235346792567903,
    847288609524,
    401769396,
    411782264189325,
    20920712967,
    188286416703,
    22876792454967,
    44641044,
    15251194971432,
    1694577218967,
    416118303,
    205891132094676,
    20920719528,
    94143237876,
    22876792454964,
    87687765,
    15251194970703,
    68630377364884,
    31381236756,
    5083731658845,
    258811767,
    2329305903,
    282429536967,
    3486804084,
    1235346792567912]

/-- The forward `(5,6)` literal (stage-L values), decoder form. -/
def fuseLitFwd_5_6 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_5_6 i / 3 ^ (j : ℕ) % 3)

/-- **The `(6,5)` transpose literal** (stage-L values), decoder form. -/
def fuseLit_6_5 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (fuseRows_6_5 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(6,5)` codes are the Koszul-signed column
transposition of the `(5,6)` codes, against the Lean parity tables. -/
private theorem codes_6_5 : ∀ (i : Fin 32) (iB : Fin 4) (jA : Fin 8),
    fuseRows_6_5 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3
      = if realRepBasisParity 6 iB = 1 ∧ realRepBasisParity 5 jA = 1
        then fuseNegCode (rowsF_5_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
        else rowsF_5_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(6,5)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_6_5 (i : Fin 32) (iB : Fin 4) (jA : Fin 8) :
    realFuseMatrix 6 5 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 6 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 5 6 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 6) (realRep 5)
    (realRepBasis_mem 6 iB) (realRepBasis_mem 5 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 6 5 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
          (ℬ := (realRep 5).grading) ℝ (realRepBasis 6 iB)
          (realRepBasis 5 jA) :=
    gtensorBasis_apply_pair (realRepBasis 6) (realRepBasis 5) iB jA
  have hsrcR : realFuseSrcBasis 5 6 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
          (ℬ := (realRep 6).grading) ℝ (realRepBasis 5 jA)
          (realRepBasis 6 iB) :=
    gtensorBasis_apply_pair (realRepBasis 5) (realRepBasis 6) jA iB
  have e0 : realFuse 6 5
      = (gtensorComm (realRep 6) (realRep 5)).trans (realFuse 5 6) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 5).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 5 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 6) (realRep 5))
      (realFuse 5 6)
      (GradedTensorProduct.tmul (𝒜 := (realRep 6).grading)
        (ℬ := (realRep 5).grading) ℝ (realRepBasis 6 iB)
        (realRepBasis 5 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 5 6).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 5 6) _ _))
  refine (realFuseMatrix_apply 6 5 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 5).repr
    ((realFuse 6 5).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 6 5).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 6 5) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 5 6 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 5 6).repr
      ((realFuse 5 6).toAlgEquiv t)) i) hsrcR)).symm

/-- **Deliverable, branch `(6,5)`** (conditional on the group-1 forward
spec at `(5,6)`): entrywise value pinning, stage-L packed shape. -/
theorem realFuseMatrix_6_5_of_forward
    (h : ∀ (i j : Fin 32), realFuseMatrix 5 6 i j = fuseLitFwd_5_6 i j) :
    ∀ (i j : Fin 32), realFuseMatrix 6 5 i j = fuseLit_6_5 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 4) (n := 8)).surjective j
  refine (comm_6_5 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 6 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 5 jA * realRepBasisParity 6 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_5_6 i / 3 ^ ((iB : ℕ) + 4 * (jA : ℕ)) % 3)
      = fuseDecode (fuseRows_6_5 i / 3 ^ ((jA : ℕ) + 8 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_6_5 i iB jA)


/-! ### Branch `(3, 1)` (transpose of `(1, 3)`, `16 × 16`) -/

private def rowsT_3_1 : Fin 16 → ℕ :=
  ![14348908,
    531495,
    40095,
    59292,
    8748,
    177309,
    4782975,
    3188664,
    15309,
    354456,
    9565944,
    1594341,
    28697815,
    1062936,
    20412,
    118341]

private def rowsF_1_3 : Fin 16 → ℕ :=
  ![28697815,
    20412,
    531468,
    118341,
    177228,
    1594341,
    15309,
    9565944,
    177309,
    3188664,
    17496,
    4782975,
    14348908,
    21141,
    1062909,
    118584]

/-- The forward `(1,3)` literal (stage-L values), decoder form. -/
def fuseLitFwd_1_3 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_1_3 i / 3 ^ (j : ℕ) % 3)

private def litT_3_1 : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsT_3_1 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(3,1)` codes are the Koszul-signed column
transposition of the `(1,3)` codes, against the Lean parity tables. -/
private theorem codes_3_1 : ∀ (i : Fin 16) (iB : Fin 8) (jA : Fin 2),
    rowsT_3_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3
      = if realRepBasisParity 3 iB = 1 ∧ realRepBasisParity 1 jA = 1
        then fuseNegCode (rowsF_1_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
        else rowsF_1_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(3,1)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_3_1 (i : Fin 16) (iB : Fin 8) (jA : Fin 2) :
    realFuseMatrix 3 1 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 3 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 1 3 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 3) (realRep 1)
    (realRepBasis_mem 3 iB) (realRepBasis_mem 1 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 3 1 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
          (ℬ := (realRep 1).grading) ℝ (realRepBasis 3 iB)
          (realRepBasis 1 jA) :=
    gtensorBasis_apply_pair (realRepBasis 3) (realRepBasis 1) iB jA
  have hsrcR : realFuseSrcBasis 1 3 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 3).grading) ℝ (realRepBasis 1 jA)
          (realRepBasis 3 iB) :=
    gtensorBasis_apply_pair (realRepBasis 1) (realRepBasis 3) jA iB
  have e0 : realFuse 3 1
      = (gtensorComm (realRep 3) (realRep 1)).trans (realFuse 1 3) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 3 iB)
        (realRepBasis 1 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 3) (realRep 1))
      (realFuse 1 3)
      (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
        (ℬ := (realRep 1).grading) ℝ (realRepBasis 3 iB)
        (realRepBasis 1 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 1 3).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 1 3) _ _))
  refine (realFuseMatrix_apply 3 1 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 3 1).repr
    ((realFuse 3 1).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 3 1).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 3 1) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 3 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 1 3 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 1 3).repr
      ((realFuse 1 3).toAlgEquiv t)) i) hsrcR)).symm

/-- Entrywise value pinning at `(3,1)`, from the forward spec. -/
private theorem spec_3_1
    (h : ∀ (i j : Fin 16), realFuseMatrix 1 3 i j = fuseLitFwd_1_3 i j) :
    ∀ (i j : Fin 16), realFuseMatrix 3 1 i j = litT_3_1 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 8) (n := 2)).surjective j
  refine (comm_3_1 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 3 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 1 jA * realRepBasisParity 3 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_1_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
      = fuseDecode (rowsT_3_1 i / 3 ^ ((jA : ℕ) + 2 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_3_1 i iB jA)

/-- **Deliverable, branch `(3,1)`** (conditional on the group-1 forward
spec at `(1,3)`): the value-pinning literal form. -/
theorem realFuseMatrix_3_1_of_forward
    (h : realFuseMatrix 1 3
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]) :
    realFuseMatrix 3 1
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] := by
  have h' : ∀ (i j : Fin 16), realFuseMatrix 1 3 i j = fuseLitFwd_1_3 i j := by
    intro i j
    refine (congrFun (congrFun h i) j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hmain : ∀ (i j : Fin 16), realFuseMatrix 3 1 i j
      = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
              0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
              0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
              0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
              0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
              0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
              0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
              1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
              0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
              0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
              0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]
          : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    refine (spec_3_1 h' i j).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  exact Matrix.ext hmain


/-! ### Branch `(3, 2)` (transpose of `(2, 3)`, `32 × 32`) -/

/-- Packed row codes for `realFuseMatrix 3 2` (`32 × 32`).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_3_2 : Fin 32 → ℕ :=
  ![28697815,
    1757339338104,
    2562786534735,
    531468,
    45755909432856,
    118341,
    40824,
    1235346835614615,
    8748,
    411782393329461,
    137261529570744,
    177309,
    7632571053789,
    3188664,
    4782975,
    753145430616,
    15309,
    411782522469624,
    137261142150255,
    354456,
    7629084269388,
    1594341,
    9565944,
    659002251789,
    14348908,
    1725958278495,
    2552326181532,
    1062909,
    45754747171389,
    59292,
    21141,
    1235346878661336]

private def rowsF_2_3 : Fin 32 → ℕ :=
  ![15251194969975,
    20930272344,
    31384248255,
    282429536508,
    45753584914296,
    387459855,
    129199212,
    1235346792567975,
    847288609452,
    94144241709,
    3501133308,
    2541865828335,
    205891132095135,
    86447736,
    1162274589,
    137260754731224,
    847288609461,
    94143710268,
    6987917709,
    5083731656664,
    205891132094892,
    86270589,
    2324536056,
    68630377366341,
    7625597484988,
    10469919141,
    31382653932,
    282429536535,
    22876792459335,
    774880344,
    129258261,
    1235346792568056]

/-- The forward `(2,3)` literal (stage-L values), decoder form. -/
def fuseLitFwd_2_3 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (rowsF_2_3 i / 3 ^ (j : ℕ) % 3)

/-- **The `(3,2)` transpose literal** (stage-L values), decoder form. -/
def fuseLit_3_2 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.of fun i j => fuseDecode (fuseRows_3_2 i / 3 ^ (j : ℕ) % 3)

/-- Kernel cross-check: the `(3,2)` codes are the Koszul-signed column
transposition of the `(2,3)` codes, against the Lean parity tables. -/
private theorem codes_3_2 : ∀ (i : Fin 32) (iB : Fin 8) (jA : Fin 4),
    fuseRows_3_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3
      = if realRepBasisParity 3 iB = 1 ∧ realRepBasisParity 2 jA = 1
        then fuseNegCode (rowsF_2_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
        else rowsF_2_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3 := by decide

/-- **Comm reduction** at `(3,2)`: the transpose matrix entry is the
Koszul-signed forward matrix entry (forward matrix opaque). -/
private theorem comm_3_2 (i : Fin 32) (iB : Fin 8) (jA : Fin 4) :
    realFuseMatrix 3 2 i (finProdFinEquiv (iB, jA))
      = (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 3 iB)
            : ℤˣ) : ℤ)
          • realFuseMatrix 2 3 i (finProdFinEquiv (jA, iB)) := by
  have hcomm := gtensorComm_tmul_of_mem (realRep 3) (realRep 2)
    (realRepBasis_mem 3 iB) (realRepBasis_mem 2 jA)
  rw [Units.smul_def] at hcomm
  have hsrcL : realFuseSrcBasis 3 2 (finProdFinEquiv (iB, jA))
      = GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
          (ℬ := (realRep 2).grading) ℝ (realRepBasis 3 iB)
          (realRepBasis 2 jA) :=
    gtensorBasis_apply_pair (realRepBasis 3) (realRepBasis 2) iB jA
  have hsrcR : realFuseSrcBasis 2 3 (finProdFinEquiv (jA, iB))
      = GradedTensorProduct.tmul (𝒜 := (realRep 2).grading)
          (ℬ := (realRep 3).grading) ℝ (realRepBasis 2 jA)
          (realRepBasis 3 iB) :=
    gtensorBasis_apply_pair (realRepBasis 2) (realRepBasis 3) jA iB
  have e0 : realFuse 3 2
      = (gtensorComm (realRep 3) (realRep 2)).trans (realFuse 2 3) :=
    rfl
  have e1 := (congrArg (fun E => E.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 3 iB)
        (realRepBasis 2 jA))) e0).trans
    (superAlgEquiv_trans_apply (gtensorComm (realRep 3) (realRep 2))
      (realFuse 2 3)
      (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
        (ℬ := (realRep 2).grading) ℝ (realRepBasis 3 iB)
        (realRepBasis 2 jA)))
  have hfuse := e1.trans
    ((congrArg (fun x => (realFuse 2 3).toAlgEquiv x) hcomm).trans
      (superAlgEquiv_zsmul (realFuse 2 3) _ _))
  refine (realFuseMatrix_apply 3 2 i (finProdFinEquiv (iB, jA))).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 3 2).repr
    ((realFuse 3 2).toAlgEquiv t)) i) hsrcL).trans ?_
  refine (congrArg (fun t => ((realFuseDstBasis 3 2).repr t) i) hfuse).trans ?_
  refine (basis_repr_zsmul_apply (realFuseDstBasis 3 2) _ _ i).trans ?_
  refine congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 3 iB)
        : ℤˣ) : ℤ) • t) ?_
  exact ((realFuseMatrix_apply 2 3 i (finProdFinEquiv (jA, iB))).trans
    (congrArg (fun t => ((realFuseDstBasis 2 3).repr
      ((realFuse 2 3).toAlgEquiv t)) i) hsrcR)).symm

/-- **Deliverable, branch `(3,2)`** (conditional on the group-1 forward
spec at `(2,3)`): entrywise value pinning, stage-L packed shape. -/
theorem realFuseMatrix_3_2_of_forward
    (h : ∀ (i j : Fin 32), realFuseMatrix 2 3 i j = fuseLitFwd_2_3 i j) :
    ∀ (i j : Fin 32), realFuseMatrix 3 2 i j = fuseLit_3_2 i j := by
  intro i j
  obtain ⟨⟨iB, jA⟩, rfl⟩ :=
    (finProdFinEquiv (m := 8) (n := 4)).surjective j
  refine (comm_3_2 i iB jA).trans ?_
  refine (congrArg (fun t : ℝ =>
    (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 3 iB)
        : ℤˣ) : ℤ) • t) (h i (finProdFinEquiv (jA, iB)))).trans ?_
  show (((-1 : ℤˣ) ^ (realRepBasisParity 2 jA * realRepBasisParity 3 iB)
          : ℤˣ) : ℤ)
        • fuseDecode (rowsF_2_3 i / 3 ^ ((iB : ℕ) + 8 * (jA : ℕ)) % 3)
      = fuseDecode (fuseRows_3_2 i / 3 ^ ((jA : ℕ) + 4 * (iB : ℕ)) % 3)
  exact sign_decode _ _ _ _ (codes_3_2 i iB jA)


end Superfusion

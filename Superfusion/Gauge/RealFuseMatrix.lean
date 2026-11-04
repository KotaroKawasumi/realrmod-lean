/-
Superfusion / Gauge / RealFuseMatrix

M15 semantic-bridge step 2: **coordinate frames for the real fusion
isomorphisms, and their matrices**.

`RealRepsBasis` equipped the eight representatives `realRep a` with the
canonical homogeneous bases `realRepBasis a`.  This file equips the
source and the target of every fusion isomorphism `realFuse a b` with
the induced frames and takes the matrix of the isomorphism in them.
The index flattenings follow the contract of
`scripts/certgen/engine.py` exactly:

* `gtensorBasis bA bB : Basis (Fin (m * n)) ℝ (A.gtensor B).carrier` —
  LEFT-MAJOR tensor frame, `e_i ⊗ f_j` at index `j + n·i` (mathlib's
  `finProdFinEquiv`); anchors `gtensorBasis_apply_pair` /
  `gtensorBasis_apply`.
* `matrixEntryBasis b m' n'` — the single-entry frame
  `Matrix.single r s (b e)` of a matrix module, and its flattening
  `matrixSuperBasis bP p q :
    Basis (Fin ((p+q) * (p+q) * k)) ℝ (P.matrixSuper p q).carrier`
  along `matrixSuperIndexEquiv`, which sends `(r, s, e)` to
  `e + k·(s' + (p+q)·r')` with `r', s'` the `finSumFinEquiv` images of
  the block indices (`inl` block before `inr`); anchors
  `matrixEntryBasis_apply`, `matrixSuperBasis_apply_pair` /
  `matrixSuperBasis_apply`.
* `realFuseSrcBasis a b` / `realFuseDstBasis a b` — the two frames at
  the fusion corner `(a, b)`, and `realFuseMatrix a b` — the matrix of
  `realFuse a b` in them (rows = codomain, columns = domain: matrices
  act on column vectors, engine.py's convention), with the tautological
  entry formula `realFuseMatrix_apply` and the column expansion
  `realFuse_apply_srcBasis`.
* `superAlgEquiv_ext_basis` — two graded isomorphisms agreeing on a
  basis agree everywhere.

Together these are the interface for the 64 generated value-pinning
certificates: name a frame vector by its index, pin the matrix entries,
and extend by `superAlgEquiv_ext_basis`.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge).
-/
import Superfusion.Gauge.RealRepsBasis
import Superfusion.Gauge.RealGaugeInstance
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basis

namespace Superfusion

open Module TensorProduct GradedTensorProduct

/-! ### The tensor frame -/

/-- The value of `finProdFinEquiv` in the LEFT-MAJOR contract form: the
pair `(i, j)` lands at `j + n·i`. -/
theorem finProdFinEquiv_val {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i, j) : ℕ) = (j : ℕ) + n * (i : ℕ) := rfl

/-- The LEFT-MAJOR index `j + n·i` is a valid index of `Fin (m * n)`. -/
theorem gtensorIndex_lt {m n : ℕ} (i : Fin m) (j : Fin n) :
    (j : ℕ) + n * (i : ℕ) < m * n :=
  finProdFinEquiv_val i j ▸ (finProdFinEquiv (i, j)).isLt

/-- **The tensor frame**: the basis of `(A.gtensor B).carrier` induced
by bases of the factors, flattened to `Fin (m * n)` in LEFT-MAJOR order
(`e_i ⊗ f_j` at index `j + n·i`, matching `scripts/certgen/engine.py`).
Anchors: `gtensorBasis_apply_pair`, `gtensorBasis_apply`. -/
noncomputable def gtensorBasis {A B : SuperAlgebra ℝ} {m n : ℕ}
    (bA : Basis (Fin m) ℝ A.carrier) (bB : Basis (Fin n) ℝ B.carrier) :
    Basis (Fin (m * n)) ℝ (A.gtensor B).carrier :=
  ((bA.tensorProduct bB).map (of ℝ A.grading B.grading)).reindex
    finProdFinEquiv

/-- **Pair-index anchor for the tensor frame**: the basis vector at
`finProdFinEquiv (i, j)` is the graded tensor `bA i ᵍ⊗ₜ bB j`. -/
@[simp] theorem gtensorBasis_apply_pair {A B : SuperAlgebra ℝ} {m n : ℕ}
    (bA : Basis (Fin m) ℝ A.carrier) (bB : Basis (Fin n) ℝ B.carrier)
    (i : Fin m) (j : Fin n) :
    gtensorBasis bA bB (finProdFinEquiv (i, j))
      = GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ
          (bA i) (bB j) := by
  have h : (((bA.tensorProduct bB).map (of ℝ A.grading B.grading)).reindex
        finProdFinEquiv) (finProdFinEquiv (i, j))
      = bA i ᵍ⊗ₜ[ℝ] bB j := by
    rw [Basis.reindex_apply, Equiv.symm_apply_apply, Basis.map_apply,
      Basis.tensorProduct_apply]
  exact h

/-- **LEFT-MAJOR anchor for the tensor frame** (the indexing contract of
`scripts/certgen/engine.py`): the basis vector at the explicit index
`j + n·i` is `bA i ᵍ⊗ₜ bB j`. -/
theorem gtensorBasis_apply {A B : SuperAlgebra ℝ} {m n : ℕ}
    (bA : Basis (Fin m) ℝ A.carrier) (bB : Basis (Fin n) ℝ B.carrier)
    (i : Fin m) (j : Fin n) :
    gtensorBasis bA bB ⟨(j : ℕ) + n * (i : ℕ), gtensorIndex_lt i j⟩
      = GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ
          (bA i) (bB j) := by
  rw [show (⟨(j : ℕ) + n * (i : ℕ), gtensorIndex_lt i j⟩ : Fin (m * n))
        = finProdFinEquiv (i, j) from
      Fin.ext (finProdFinEquiv_val i j).symm]
  exact gtensorBasis_apply_pair bA bB i j

/-! ### The matrix frame -/

/-- Packing the iterated sigma index of `Pi.basis` into the triple
`rows × columns × entry-index`. -/
def matrixIndexPack (m' n' ι : Type*) :
    (Σ _ : m', Σ _ : n', ι) ≃ m' × n' × ι where
  toFun x := (x.1, x.2.1, x.2.2)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The single-entry frame of a matrix module**: `Matrix m' n' M` has
the basis `Matrix.single r s (b e)` (the matrix with `b e` at `(r, s)`
and `0` elsewhere), indexed by `(r, s, e)` in
rows × columns × entry-index.  Anchor: `matrixEntryBasis_apply`. -/
noncomputable def matrixEntryBasis {M : Type*} [AddCommMonoid M]
    [Module ℝ M] {ι : Type*} (b : Basis ι ℝ M) (m' n' : Type*)
    [Fintype m'] [Fintype n'] :
    Basis (m' × n' × ι) ℝ (Matrix m' n' M) :=
  (((Pi.basis fun _ : m' => Pi.basis fun _ : n' => b).map
      (Matrix.ofLinearEquiv ℝ)).reindex (matrixIndexPack m' n' ι))

/-- **Anchor for the single-entry frame**: the basis vector at
`(r, s, e)` is the single-entry matrix `Matrix.single r s (b e)`. -/
@[simp] theorem matrixEntryBasis_apply {M : Type*} [AddCommMonoid M]
    [Module ℝ M] {ι : Type*} (b : Basis ι ℝ M) {m' n' : Type*}
    [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']
    (r : m') (s : n') (e : ι) :
    matrixEntryBasis b m' n' (r, s, e) = Matrix.single r s (b e) := by
  rw [matrixEntryBasis, Basis.reindex_apply,
    show (matrixIndexPack m' n' ι).symm (r, s, e) = ⟨r, s, e⟩ from rfl,
    Basis.map_apply, Pi.basis_apply, Pi.basis_apply,
    Matrix.single_eq_of_single_single]
  rfl

/-- **The flattening of the matrix frame index** (the indexing contract
of `scripts/certgen/engine.py`): `(r, s, e) ↦ e + k·(s' + (p+q)·r')`,
where `r', s'` are the `finSumFinEquiv` images of the block indices
(`inl` block of size `p` before `inr` block of size `q`). -/
def matrixSuperIndexEquiv (p q k : ℕ) :
    (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Fin k
      ≃ Fin ((p + q) * (p + q) * k) :=
  (Equiv.prodCongr finSumFinEquiv
      (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin k)))).trans
    ((Equiv.prodAssoc (Fin (p + q)) (Fin (p + q)) (Fin k)).symm.trans
      ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin k))).trans
        finProdFinEquiv))

/-- The index formula of `matrixSuperIndexEquiv`, in contract form. -/
@[simp] theorem matrixSuperIndexEquiv_val (p q k : ℕ)
    (r s : Fin p ⊕ Fin q) (e : Fin k) :
    (matrixSuperIndexEquiv p q k (r, s, e) : ℕ)
      = (e : ℕ) + k * ((finSumFinEquiv s : ℕ)
          + (p + q) * (finSumFinEquiv r : ℕ)) := rfl

/-- The flattened matrix-frame index is a valid index of
`Fin ((p+q) * (p+q) * k)`. -/
theorem matrixSuperIndex_lt (p q k : ℕ) (r s : Fin p ⊕ Fin q)
    (e : Fin k) :
    (e : ℕ) + k * ((finSumFinEquiv s : ℕ)
        + (p + q) * (finSumFinEquiv r : ℕ))
      < (p + q) * (p + q) * k :=
  matrixSuperIndexEquiv_val p q k r s e ▸
    (matrixSuperIndexEquiv p q k (r, s, e)).isLt

/-- **The matrix frame**: the basis of `(P.matrixSuper p q).carrier`
induced by a basis of the entry algebra, flattened to
`Fin ((p+q) * (p+q) * k)` along `matrixSuperIndexEquiv`.  Anchors:
`matrixSuperBasis_apply_pair`, `matrixSuperBasis_apply`. -/
noncomputable def matrixSuperBasis {P : SuperAlgebra ℝ} {k : ℕ}
    (bP : Basis (Fin k) ℝ P.carrier) (p q : ℕ) :
    Basis (Fin ((p + q) * (p + q) * k)) ℝ
      ((P.matrixSuper p q).carrier) :=
  (matrixEntryBasis bP (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)).reindex
    (matrixSuperIndexEquiv p q k)

/-- **Pair-index anchor for the matrix frame**: the basis vector at
`matrixSuperIndexEquiv p q k (r, s, e)` is the single-entry matrix
`Matrix.single r s (bP e)`. -/
@[simp] theorem matrixSuperBasis_apply_pair {P : SuperAlgebra ℝ} {k : ℕ}
    (bP : Basis (Fin k) ℝ P.carrier) (p q : ℕ)
    (r s : Fin p ⊕ Fin q) (e : Fin k) :
    matrixSuperBasis bP p q (matrixSuperIndexEquiv p q k (r, s, e))
      = Matrix.single r s (bP e) := by
  have h : ((matrixEntryBasis bP (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)).reindex
        (matrixSuperIndexEquiv p q k))
        (matrixSuperIndexEquiv p q k (r, s, e))
      = Matrix.single r s (bP e) := by
    rw [Basis.reindex_apply, Equiv.symm_apply_apply, matrixEntryBasis_apply]
  exact h

/-- **Flattened anchor for the matrix frame** (the indexing contract of
`scripts/certgen/engine.py`): the basis vector at the explicit index
`e + k·(s' + (p+q)·r')` is the single-entry matrix
`Matrix.single r s (bP e)`. -/
theorem matrixSuperBasis_apply {P : SuperAlgebra ℝ} {k : ℕ}
    (bP : Basis (Fin k) ℝ P.carrier) (p q : ℕ)
    (r s : Fin p ⊕ Fin q) (e : Fin k) :
    matrixSuperBasis bP p q
        ⟨(e : ℕ) + k * ((finSumFinEquiv s : ℕ)
            + (p + q) * (finSumFinEquiv r : ℕ)),
          matrixSuperIndex_lt p q k r s e⟩
      = Matrix.single r s (bP e) := by
  rw [show (⟨(e : ℕ) + k * ((finSumFinEquiv s : ℕ)
          + (p + q) * (finSumFinEquiv r : ℕ)),
        matrixSuperIndex_lt p q k r s e⟩ : Fin ((p + q) * (p + q) * k))
        = matrixSuperIndexEquiv p q k (r, s, e) from
      Fin.ext (matrixSuperIndexEquiv_val p q k r s e).symm,
    matrixSuperBasis_apply_pair]

/-! ### The fusion frames and the fusion matrices -/

/-- **The source frame** at the fusion corner `(a, b)`: the LEFT-MAJOR
tensor frame of `realRep a ᵍ⊗ realRep b`, built from the canonical
homogeneous bases of the factors. -/
noncomputable def realFuseSrcBasis (a b : ZMod 8) :
    Basis (Fin (realRepDim a.val * realRepDim b.val)) ℝ
      ((realRep a).gtensor (realRep b)).carrier :=
  gtensorBasis (realRepBasis a) (realRepBasis b)

/-- Anchor for the source frame, inherited from `gtensorBasis_apply`. -/
theorem realFuseSrcBasis_apply (a b : ZMod 8)
    (i : Fin (realRepDim a.val)) (j : Fin (realRepDim b.val)) :
    realFuseSrcBasis a b
        ⟨(j : ℕ) + realRepDim b.val * (i : ℕ), gtensorIndex_lt i j⟩
      = GradedTensorProduct.tmul (𝒜 := (realRep a).grading)
          (ℬ := (realRep b).grading) ℝ
          (realRepBasis a i) (realRepBasis b j) :=
  gtensorBasis_apply (realRepBasis a) (realRepBasis b) i j

/-- **The target frame** at the fusion corner `(a, b)`: the flattened
single-entry frame of `M_{p|q}(realRep (a + b))` at
`(p, q) = realSize a b`, built from the canonical homogeneous basis of
`realRep (a + b)`. -/
noncomputable def realFuseDstBasis (a b : ZMod 8) :
    Basis (Fin (((realSize a b).1 + (realSize a b).2)
        * ((realSize a b).1 + (realSize a b).2)
        * realRepDim (a + b).val)) ℝ
      ((realRep (a + b)).matrixSuper (realSize a b).1
        (realSize a b).2).carrier :=
  matrixSuperBasis (realRepBasis (a + b)) (realSize a b).1
    (realSize a b).2

/-- Anchor for the target frame, inherited from
`matrixSuperBasis_apply`. -/
theorem realFuseDstBasis_apply (a b : ZMod 8)
    (r s : Fin (realSize a b).1 ⊕ Fin (realSize a b).2)
    (e : Fin (realRepDim (a + b).val)) :
    realFuseDstBasis a b
        ⟨(e : ℕ) + realRepDim (a + b).val * ((finSumFinEquiv s : ℕ)
            + ((realSize a b).1 + (realSize a b).2)
              * (finSumFinEquiv r : ℕ)),
          matrixSuperIndex_lt _ _ _ r s e⟩
      = Matrix.single r s (realRepBasis (a + b) e) :=
  matrixSuperBasis_apply (realRepBasis (a + b)) (realSize a b).1
    (realSize a b).2 r s e

/-- **The matrix of the fusion isomorphism** `realFuse a b` in the
frames `realFuseSrcBasis a b` / `realFuseDstBasis a b`.  Rows are
target-frame indices, columns are source-frame indices: the matrix acts
on column vectors, matching `scripts/certgen/engine.py`. -/
noncomputable def realFuseMatrix (a b : ZMod 8) :
    Matrix
      (Fin (((realSize a b).1 + (realSize a b).2)
        * ((realSize a b).1 + (realSize a b).2)
        * realRepDim (a + b).val))
      (Fin (realRepDim a.val * realRepDim b.val)) ℝ :=
  LinearMap.toMatrix (realFuseSrcBasis a b) (realFuseDstBasis a b)
    (realFuse a b).toAlgEquiv.toLinearMap

/-- **Tautological entry formula**: entry `(i, j)` of `realFuseMatrix`
is the `i`-th target-frame coordinate of the image of the `j`-th
source-frame vector. -/
theorem realFuseMatrix_apply (a b : ZMod 8)
    (i : Fin (((realSize a b).1 + (realSize a b).2)
      * ((realSize a b).1 + (realSize a b).2)
      * realRepDim (a + b).val))
    (j : Fin (realRepDim a.val * realRepDim b.val)) :
    realFuseMatrix a b i j
      = (realFuseDstBasis a b).repr
          ((realFuse a b).toAlgEquiv (realFuseSrcBasis a b j)) i := by
  rw [realFuseMatrix, LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply]

/-- **Column expansion**: the image of the `j`-th source-frame vector
expands in the target frame with coefficients the `j`-th column of
`realFuseMatrix`. -/
theorem realFuse_apply_srcBasis (a b : ZMod 8)
    (j : Fin (realRepDim a.val * realRepDim b.val)) :
    (realFuse a b).toAlgEquiv (realFuseSrcBasis a b j)
      = ∑ i, realFuseMatrix a b i j • realFuseDstBasis a b i := by
  refine ((realFuseDstBasis a b).sum_repr _).symm.trans ?_
  exact Finset.sum_congr rfl fun i _ => by rw [realFuseMatrix_apply]

/-! ### Extensionality along a frame -/

/-- **Frame extensionality for graded isomorphisms**: two
`SuperAlgEquiv`s that agree on a basis of the source agree everywhere
(via `Basis.ext` on the underlying linear maps). -/
theorem superAlgEquiv_ext_basis {K : Type*} [CommRing K]
    {A B : SuperAlgebra K} {ι : Type*} (e f : SuperAlgEquiv A B)
    (bA : Basis ι K A.carrier)
    (h : ∀ i, e.toAlgEquiv (bA i) = f.toAlgEquiv (bA i)) :
    ∀ x, e.toAlgEquiv x = f.toAlgEquiv x := by
  intro x
  have hl : e.toAlgEquiv.toLinearMap = f.toAlgEquiv.toLinearMap :=
    bA.ext fun i => by
      rw [AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, h i]
  calc e.toAlgEquiv x
      = e.toAlgEquiv.toLinearMap x := (AlgEquiv.toLinearMap_apply _ _).symm
    _ = f.toAlgEquiv.toLinearMap x := by rw [hl]
    _ = f.toAlgEquiv x := AlgEquiv.toLinearMap_apply _ _

end Superfusion

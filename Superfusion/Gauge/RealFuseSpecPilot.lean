/-
Superfusion / Gauge / RealFuseSpecPilot

M15 semantic-bridge PILOT: the first **value-pinning spec theorems** — the
matrix of `realFuse a b` in the explicit frames of `RealFuseMatrix` *is* a
stated literal — for the easiest branches:

* `realFuseMatrix_zero_left_0` … `_7` : `realFuseMatrix 0 b = 1` (the eight
  left-unitor corners), plus the entrywise wrapper
  `realFuseMatrix_zero_left`.
* `realFuseMatrix_zero_right_0` … `_7` : `realFuseMatrix a 0 = 1`, plus the
  wrapper `realFuseMatrix_zero_right`.
* `realFuseMatrix_one_one` :
  `realFuseMatrix 1 1 = !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]` — the
  `Cl_{0,1} ᵍ⊗ Cl_{0,1} ≅ Cl_{0,2}` branch, derived from the Lean chain
  `towerFuse (-1) 1 1 ; matrixSuperOne.symm` (left-major source order
  `1⊗1, 1⊗g, g⊗1, g⊗g` maps to target `e₀, e₂, e₁, e₃`; the sign-free
  permutation is forced by `towerSuccEquiv`/`equivGradedTensor`, whose
  generator formulas carry no Koszul sign on these columns).

**Pilot conclusions for the 64-branch rollout** (the point of this file):

1. *Crossing the `Eq.mpr` layers is free at concrete labels.* At literal
   `(a, b)` the casts inside `realFuse` (`ZMod.val_add`) and inside
   `realFuse_zero_left/right` (`zero_add`/`add_zero`) are casts along
   definitionally equal types, so kernel proof irrelevance dissolves them:
   `realFuse 1 1 = realFuse_one_one` is `rfl`, and a per-branch spec theorem
   is *directly* `exact`-able from a lemma stated against the branch's own
   composite (`(towerFuse (-1) 1 1).trans (matrixSuperOne _).symm`, at
   `divisionTower`-spelled types).  Cost of the crossing:
   `set_option maxRecDepth 8000` and `set_option maxHeartbeats 1000000`
   (the per-corner defeq `realFuseMatrix a b ≡ helper matrix` runs
   ≈ 300–500 k heartbeats, past the 200 k default); the whole file
   elaborates in ≈ 85 s, ≈ 2–4 s per public corner theorem.
2. *Evaluate a column, don't chase entries.*  The working pattern per branch
   is: (i) name each source frame vector via `gtensorBasis_apply_pair`
   `have`-bridged to the literal flat index (the index arithmetic
   `j + n·i`, `e + k·(s' + (p+q)r')` reduces definitionally, so the bridge
   is a bare `exact`/`have` with no `Fin` lemmas); (ii) push it through the
   fusion composite with the `*_tmul` application lemmas below, developed
   `have`-by-`have` (`rw … at h`) and assembled through one `rfl`-proved
   equation (`e1`) that spells out the composite — **never** rewrite library
   lemmas into a hand-written goal, because the `SuperAlgebra`-vs-raw
   spellings (`(P.gtensor Q).grading` vs `tensorGrading …`,
   `divisionTower ε (0+1)` vs `divisionTower ε 1`, `Basis.singleton` at `ℝ`
   vs at `(base ℝ).carrier`) differ syntactically even where they are
   definitionally equal; rewriting *inside* hypotheses that originate from
   the library lemma and closing with a defeq `exact` sidesteps every such
   mismatch; (iii) land on `Matrix.single`, bridge back with
   `matrixSuperBasis_apply_pair`, and pin entries by `Basis.repr_self_apply`
   + `if_congr`/`fin_cases … <;> rfl`.
3. *`symm`-direction values come for free from forward values* via
   `AlgEquiv.symm_apply_eq`; no inverse formulas are ever unfolded.
4. *Statement-shape caveats found by the pilot.*  (a) The literal `1` matrix
   is only *stateable* per concrete corner: at abstract `b` (or abstract
   dimension `k`) the row and column counts are equal but not
   definitionally (`1 * k` vs `k * 1` vs `realRepDim (0+b).val`), so
   `Matrix.one` fails instance synthesis — hence eight literal instances
   plus a dimension-uniform entrywise wrapper.  (b) Constants used inside
   later `rw` patterns must be *declared at the bundled types*
   (`baseBasis`), and `1`/generator arguments must be written at the
   carrier the library lemma expects, or `kabstract` skips the (defeq but
   instance-mismatched) subterm.  (c) `congrArg Fin.val h` needs the
   function domain pinned (`fun x : Fin n => (x : ℕ)`) when source and
   target `Fin` types are defeq-but-distinct.
5. *Expected per-branch cost.*  A `1|0`-target branch (unitor or tower) is
   ≈ 15–25 lines and 2–5 s; the generic-`ε` tower lemmas here
   (`towerFuse_one_one_tmul_*`, `towerSuccEquiv_symm_tmul_*`) are reusable
   for all six in-range same-sign Clifford pairs, and the same skeleton
   (frame vector ↦ composite ↦ `Matrix.single` ↦ frame vector) scales to the
   `p|q ≠ 1|0` branches by replacing `matrixSuperOne_symm_single` with the
   branch's matrix-corner formula.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7).
-/
import Superfusion.Gauge.RealFuseMatrix

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace Superfusion

open Module GradedTensorProduct

/-! ### Application lemmas for the shared pieces -/

/-- `SuperAlgEquiv.refl` acts as the identity (definitional). -/
private theorem superRefl_apply (P : SuperAlgebra ℝ) (x : P.carrier) :
    (SuperAlgEquiv.refl P).toAlgEquiv x = x := rfl

/-- The inverse of `matrixSuperOne` is the constant `1×1` matrix, i.e. the
single-entry matrix at the unique index. -/
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

/-- The left unitor on `1 ᵍ⊗ v` for homogeneous `v`: the Koszul sign of the
underlying braiding vanishes against the even scalar. -/
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

/-- The right unitor on `v ᵍ⊗ 1` (no sign, no homogeneity needed). -/
private theorem gtensorUnitorRight_tmul_one (P : SuperAlgebra ℝ)
    (v : P.carrier) :
    (gtensorUnitorRight P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ v (1 : ℝ)) = v := by
  have h := gunitorRightHom_tmul P.grading v (1 : ℝ)
  rw [map_one, mul_one] at h
  exact h

/-- Left-unitor corner composite on a frame vector: lands on the
single-entry matrix. -/
private theorem unitorL_single (P : SuperAlgebra ℝ) {jp : ZMod 2}
    {v : P.carrier} (hv : v ∈ P.grading jp) :
    ((gtensorUnitorLeft P).trans (matrixSuperOne P).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := P.grading) ℝ (1 : ℝ) v)
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v := by
  show (matrixSuperOne P).symm.toAlgEquiv
      ((gtensorUnitorLeft P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := P.grading) ℝ (1 : ℝ) v))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v
  rw [gtensorUnitorLeft_one_tmul P hv]
  exact matrixSuperOne_symm_single P v

/-- Right-unitor corner composite on a frame vector. -/
private theorem unitorR_single (P : SuperAlgebra ℝ) (v : P.carrier) :
    ((gtensorUnitorRight P).trans (matrixSuperOne P).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ v (1 : ℝ))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v := by
  show (matrixSuperOne P).symm.toAlgEquiv
      ((gtensorUnitorRight P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ v (1 : ℝ)))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v
  rw [gtensorUnitorRight_tmul_one P v]
  exact matrixSuperOne_symm_single P v

/-! ### The generic `M_{1|0}` unitor matrices -/

/-- The singleton basis of the base algebra, *typed at*
`(SuperAlgebra.base ℝ).carrier` (definitionally `Basis.singleton`; the
retyping keeps every coercion instance in rewrite-matching form). -/
private noncomputable def baseBasis :
    Basis (Fin 1) ℝ (SuperAlgebra.base ℝ).carrier :=
  Basis.singleton (Fin 1) ℝ

private theorem baseBasis_apply (i : Fin 1) : baseBasis i = (1 : ℝ) :=
  Basis.singleton_apply (Fin 1) ℝ i

/-- **Generic value pinning, left-unitor shape (entrywise)**: in the pilot
frames the matrix of `gtensorUnitorLeft ; matrixSuperOne.symm` is the
identity, for any homogeneous basis of the right factor.  (Stated
entrywise: at an abstract dimension `k` the row count `(1+0)·(1+0)·k` and
the column count `1·k` are equal but not definitionally, so `Matrix.one`
itself cannot be elaborated; the concrete corners below recover the literal
`1` form.) -/
private theorem zeroLeft_apply (P : SuperAlgebra ℝ) {k : ℕ}
    (bP : Basis (Fin k) ℝ P.carrier) (par : Fin k → ZMod 2)
    (hbP : ∀ e, bP e ∈ P.grading (par e)) :
    ∀ i j, LinearMap.toMatrix
        (gtensorBasis (A := SuperAlgebra.base ℝ) (B := P) baseBasis bP)
        (matrixSuperBasis bP 1 0)
        ((gtensorUnitorLeft P).trans
          (matrixSuperOne P).symm).toAlgEquiv.toLinearMap i j
      = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 := by
  intro i j
  obtain ⟨⟨i₁, j₁⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨r, s, e⟩, rfl⟩ := (matrixSuperIndexEquiv 1 0 k).surjective i
  cases r with
  | inr r => exact r.elim0
  | inl r =>
    cases s with
    | inr s => exact s.elim0
    | inl s =>
      obtain rfl : r = 0 := Subsingleton.elim r 0
      obtain rfl : s = 0 := Subsingleton.elim s 0
      obtain rfl : i₁ = 0 := Subsingleton.elim i₁ 0
      rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply,
        gtensorBasis_apply_pair, baseBasis_apply,
        unitorL_single P (hbP j₁),
        ← matrixSuperBasis_apply_pair bP 1 0 (Sum.inl 0) (Sum.inl 0) j₁,
        Basis.repr_self_apply]
      refine if_congr ⟨fun hc => ?_, fun hc => ?_⟩ rfl rfl
      · have h1 : (j₁ : ℕ) = (e : ℕ) :=
          congrArg (fun x : Fin ((1 + 0) * (1 + 0) * k) => (x : ℕ)) hc
        show (e : ℕ) = (j₁ : ℕ)
        omega
      · have h1 : (e : ℕ) = (j₁ : ℕ) := hc
        exact Fin.ext (show (j₁ : ℕ) = (e : ℕ) by omega)

/-- **Generic value pinning, right-unitor shape (entrywise).** -/
private theorem zeroRight_apply (P : SuperAlgebra ℝ) {k : ℕ}
    (bP : Basis (Fin k) ℝ P.carrier) :
    ∀ i j, LinearMap.toMatrix
        (gtensorBasis (A := P) (B := SuperAlgebra.base ℝ) bP baseBasis)
        (matrixSuperBasis bP 1 0)
        ((gtensorUnitorRight P).trans
          (matrixSuperOne P).symm).toAlgEquiv.toLinearMap i j
      = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 := by
  intro i j
  obtain ⟨⟨j₀, i₁⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨r, s, e⟩, rfl⟩ := (matrixSuperIndexEquiv 1 0 k).surjective i
  cases r with
  | inr r => exact r.elim0
  | inl r =>
    cases s with
    | inr s => exact s.elim0
    | inl s =>
      obtain rfl : r = 0 := Subsingleton.elim r 0
      obtain rfl : s = 0 := Subsingleton.elim s 0
      obtain rfl : i₁ = 0 := Subsingleton.elim i₁ 0
      rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply,
        gtensorBasis_apply_pair, baseBasis_apply,
        unitorR_single P (bP j₀),
        ← matrixSuperBasis_apply_pair bP 1 0 (Sum.inl 0) (Sum.inl 0) j₀,
        Basis.repr_self_apply]
      refine if_congr ⟨fun hc => ?_, fun hc => ?_⟩ rfl rfl
      · have h1 : (j₀ : ℕ) = (e : ℕ) :=
          congrArg (fun x : Fin ((1 + 0) * (1 + 0) * k) => (x : ℕ)) hc
        show (e : ℕ) = 0 + 1 * (j₀ : ℕ)
        omega
      · have h1 : (e : ℕ) = 0 + 1 * (j₀ : ℕ) := hc
        exact Fin.ext (show (j₀ : ℕ) = (e : ℕ) by omega)

/-! ### Deliverable 1: the eight left-unitor corners -/

/-- The shared derivation "entrywise Kronecker delta ⟹ literal `1`", at a
concrete square size. -/
private theorem eq_one_of_entry {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    (h : ∀ i j, M i j = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0) :
    M = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.one_apply, h i j]
  exact if_congr ⟨fun hv => Fin.ext hv, fun hv => congrArg Fin.val hv⟩ rfl rfl

theorem realFuseMatrix_zero_left_0 :
    realFuseMatrix 0 0 = (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
  eq_one_of_entry (zeroLeft_apply (SuperAlgebra.base ℝ) baseBasis
    (fun _ => 0) (fun _ => mem_evenGrading_zero ℝ ℝ _))

theorem realFuseMatrix_zero_left_1 :
    realFuseMatrix 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  eq_one_of_entry (zeroLeft_apply (divisionTower (-1 : ℝ) 1)
    (towerBasis (-1) 1) (towerIndexParity 1) (towerBasis_mem (-1) 1))

theorem realFuseMatrix_zero_left_2 :
    realFuseMatrix 0 2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  eq_one_of_entry (zeroLeft_apply (divisionTower (-1 : ℝ) 2)
    (towerBasis (-1) 2) (towerIndexParity 2) (towerBasis_mem (-1) 2))

theorem realFuseMatrix_zero_left_3 :
    realFuseMatrix 0 3 = (1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  eq_one_of_entry (zeroLeft_apply (divisionTower (-1 : ℝ) 3)
    (towerBasis (-1) 3) (towerIndexParity 3) (towerBasis_mem (-1) 3))

theorem realFuseMatrix_zero_left_4 :
    realFuseMatrix 0 4 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  eq_one_of_entry (zeroLeft_apply quatEvenSuper quatBasis
    (fun _ => 0) quatBasis_mem)

theorem realFuseMatrix_zero_left_5 :
    realFuseMatrix 0 5 = (1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  eq_one_of_entry (zeroLeft_apply (divisionTower (1 : ℝ) 3)
    (towerBasis 1 3) (towerIndexParity 3) (towerBasis_mem 1 3))

theorem realFuseMatrix_zero_left_6 :
    realFuseMatrix 0 6 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  eq_one_of_entry (zeroLeft_apply (divisionTower (1 : ℝ) 2)
    (towerBasis 1 2) (towerIndexParity 2) (towerBasis_mem 1 2))

theorem realFuseMatrix_zero_left_7 :
    realFuseMatrix 0 7 = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  eq_one_of_entry (zeroLeft_apply (divisionTower (1 : ℝ) 1)
    (towerBasis 1 1) (towerIndexParity 1) (towerBasis_mem 1 1))

/-- **Wrapper (deliverable 1)**: entrywise, dimension-uniform statement of
`realFuseMatrix 0 b = 1` over all `b : ZMod 8`.  (The literal matrix `1`
cannot even be *stated* uniformly: at an abstract `b` the row index
`realRepDim (0 + b).val` and the column index `realRepDim b.val` are equal
but not definitionally, so the square instance for `Matrix.one` is
unavailable — the eight instances above carry the literal form.) -/
theorem realFuseMatrix_zero_left (b : ZMod 8) :
    ∀ i j, realFuseMatrix 0 b i j
      = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 8 ∧ b = (n : ZMod 8) :=
    ⟨b.val, ZMod.val_lt b, (ZMod.natCast_zmod_val b).symm⟩
  interval_cases n
  · show ∀ (i j : Fin 1), realFuseMatrix 0 (0 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_0, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 2), realFuseMatrix 0 (1 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_1, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 4), realFuseMatrix 0 (2 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_2, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 8), realFuseMatrix 0 (3 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_3, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 4), realFuseMatrix 0 (4 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_4, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 8), realFuseMatrix 0 (5 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_5, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 4), realFuseMatrix 0 (6 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_6, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 2), realFuseMatrix 0 (7 : ZMod 8) i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_left_7, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl

/-! ### Deliverable 2: the eight right-unitor corners

`realFuseAux` routes `(0, 0)` through `realFuse_zero_left 0`, so the first
right instance *is* the first left instance; `a ≠ 0` dispatches
`realFuse_zero_right a`. -/

theorem realFuseMatrix_zero_right_0 :
    realFuseMatrix 0 0 = (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
  realFuseMatrix_zero_left_0

theorem realFuseMatrix_zero_right_1 :
    realFuseMatrix 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  eq_one_of_entry (zeroRight_apply (divisionTower (-1 : ℝ) 1)
    (towerBasis (-1) 1))

theorem realFuseMatrix_zero_right_2 :
    realFuseMatrix 2 0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  eq_one_of_entry (zeroRight_apply (divisionTower (-1 : ℝ) 2)
    (towerBasis (-1) 2))

theorem realFuseMatrix_zero_right_3 :
    realFuseMatrix 3 0 = (1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  eq_one_of_entry (zeroRight_apply (divisionTower (-1 : ℝ) 3)
    (towerBasis (-1) 3))

theorem realFuseMatrix_zero_right_4 :
    realFuseMatrix 4 0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  eq_one_of_entry (zeroRight_apply quatEvenSuper quatBasis)

theorem realFuseMatrix_zero_right_5 :
    realFuseMatrix 5 0 = (1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  eq_one_of_entry (zeroRight_apply (divisionTower (1 : ℝ) 3)
    (towerBasis 1 3))

theorem realFuseMatrix_zero_right_6 :
    realFuseMatrix 6 0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  eq_one_of_entry (zeroRight_apply (divisionTower (1 : ℝ) 2)
    (towerBasis 1 2))

theorem realFuseMatrix_zero_right_7 :
    realFuseMatrix 7 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  eq_one_of_entry (zeroRight_apply (divisionTower (1 : ℝ) 1)
    (towerBasis 1 1))

/-- **Wrapper (deliverable 2)**: entrywise, dimension-uniform statement of
`realFuseMatrix a 0 = 1` over all `a : ZMod 8`. -/
theorem realFuseMatrix_zero_right (a : ZMod 8) :
    ∀ i j, realFuseMatrix a 0 i j
      = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 8 ∧ a = (n : ZMod 8) :=
    ⟨a.val, ZMod.val_lt a, (ZMod.natCast_zmod_val a).symm⟩
  interval_cases n
  · show ∀ (i j : Fin 1), realFuseMatrix (0 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_0, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 2), realFuseMatrix (1 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_1, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 4), realFuseMatrix (2 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_2, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 8), realFuseMatrix (3 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_3, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 4), realFuseMatrix (4 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_4, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 8), realFuseMatrix (5 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_5, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 4), realFuseMatrix (6 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_6, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl
  · show ∀ (i j : Fin 2), realFuseMatrix (7 : ZMod 8) 0 i j
        = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
    intro i j
    rw [realFuseMatrix_zero_right_7, Matrix.one_apply]
    exact if_congr ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩ rfl rfl

/-! ### The `(1,1)` branch: `Cl_{0,1} ᵍ⊗ Cl_{0,1} ≅ Cl_{0,2}`

Everything below is generic in `ε`; the deliverable instantiates `ε = -1`.
The tower basis dictionary: floor `1` is `{1, g}` (`g` the odd generator),
floor `2` is `{1, g₁, g₂, g₁g₂}` as pairs
`{(1,0), (g,0), (0,1), (0,g)}` of `OddDouble`. -/

private theorem towerBasis_one_zero (ε : ℝ) :
    towerBasis ε 1 0 = (1 : (divisionTower ε 1).carrier) := by
  have h := towerBasis_low ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

private theorem towerBasis_one_one (ε : ℝ) :
    towerBasis ε 1 1 = OddDouble.gen (SuperAlgebra.base ℝ).grading ε := by
  have h := towerBasis_high ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

private theorem towerBasis_two_zero (ε : ℝ) :
    towerBasis ε 2 0 = (1 : (divisionTower ε 2).carrier) := by
  have h := towerBasis_low ε 1 0
  rw [towerBasis_one_zero] at h
  exact h

private theorem towerBasis_two_one (ε : ℝ) :
    towerBasis ε 2 1
      = OddDouble.mk (divisionTower ε 1).grading ε
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0 := by
  have h := towerBasis_low ε 1 1
  rw [towerBasis_one_one] at h
  exact h

private theorem towerBasis_two_two (ε : ℝ) :
    towerBasis ε 2 2
      = OddDouble.mk (divisionTower ε 1).grading ε 0
          (1 : (divisionTower ε 1).carrier) := by
  have h := towerBasis_high ε 1 0
  rw [towerBasis_one_zero] at h
  exact h

private theorem towerBasis_two_three (ε : ℝ) :
    towerBasis ε 2 3
      = OddDouble.mk (divisionTower ε 1).grading ε 0
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) := by
  have h := towerBasis_high ε 1 1
  rw [towerBasis_one_one] at h
  exact h

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

/-- The inverse tower step on `t ᵍ⊗ 1`: back to the `A`-coordinate. -/
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

/-- The inverse tower step on `t ᵍ⊗ g`: to the `A·g`-coordinate, no sign. -/
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

/-- The forward tower step at floor `0` on the unit. -/
private theorem towerSuccEquiv_zero_one (ε : ℝ) :
    (towerSuccEquiv ε 0).toAlgEquiv (1 : (divisionTower ε (0 + 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 0).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (1 : ℝ)
          (1 : (divisionTower ε 1).carrier) := by
  rw [show GradedTensorProduct.tmul (𝒜 := (divisionTower ε 0).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ (1 : ℝ)
        (1 : (divisionTower ε 1).carrier)
      = (1 : ((divisionTower ε 0).gtensor (divisionTower ε 1)).carrier) from
    gtensor_one_one (divisionTower ε 0) (divisionTower ε 1)]
  exact map_one _

/-- The forward tower step at floor `0` on the odd generator. -/
private theorem towerSuccEquiv_zero_gen (ε : ℝ) :
    (towerSuccEquiv ε 0).toAlgEquiv
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 0).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (1 : ℝ)
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) := by
  have h := towerSuccEquiv_symm_tmul_gen ε 0 (1 : ℝ)
  exact ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε 0).toAlgEquiv)).mp h).symm

/-- The associator inverse on nested pure tensors (no sign). -/
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

/-- `towerFuse ε 1 0` is the right unitor on pure tensors. -/
private theorem towerFuse_one_zero_tmul (ε : ℝ)
    (u : (divisionTower ε 1).carrier) :
    (towerFuse ε 1 0).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 0).grading) ℝ u (1 : ℝ)) = u := by
  have h := gunitorRightHom_tmul (divisionTower ε 1).grading u (1 : ℝ)
  rw [map_one, mul_one] at h
  exact h

/-- **The `(1,1)` fusion on `u ᵍ⊗ 1`**: the even column, `u ᵍ⊗ 1 ↦ (u, 0)`. -/
private theorem towerFuse_one_one_tmul_one (ε : ℝ)
    (u : (divisionTower ε 1).carrier) :
    (towerFuse ε 1 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ u
          (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk (divisionTower ε 1).grading ε u 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 1)) (towerSuccEquiv ε 0)
    u (1 : (divisionTower ε (0 + 1)).carrier)
  rw [superRefl_apply, towerSuccEquiv_zero_one] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 1) (divisionTower ε 0)
    (divisionTower ε 1) u (1 : ℝ) (1 : (divisionTower ε 1).carrier)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 1 0)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
      (ℬ := (divisionTower ε 0).grading) ℝ u (1 : ℝ))
    (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, towerFuse_one_zero_tmul] at h3
  have h4 := towerSuccEquiv_symm_tmul_one ε (1 + 0) u
  have e1 : (towerFuse ε 1 1).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ u
        (1 : (divisionTower ε 1).carrier))
      = (towerSuccEquiv ε (1 + 0)).symm.toAlgEquiv
          (((towerFuse ε 1 0).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 1) (divisionTower ε 0)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 1)).gtensorCongr
                  (towerSuccEquiv ε 0)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 1).grading)
                  (ℬ := (divisionTower ε (0 + 1)).grading) ℝ u
                  (1 : (divisionTower ε (0 + 1)).carrier))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-- **The `(1,1)` fusion on `u ᵍ⊗ g`**: the odd column, `u ᵍ⊗ g ↦ (0, u)`. -/
private theorem towerFuse_one_one_tmul_gen (ε : ℝ)
    (u : (divisionTower ε 1).carrier) :
    (towerFuse ε 1 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ u
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = OddDouble.mk (divisionTower ε 1).grading ε 0 u := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 1)) (towerSuccEquiv ε 0)
    u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerSuccEquiv_zero_gen] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 1) (divisionTower ε 0)
    (divisionTower ε 1) u (1 : ℝ)
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 1 0)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
      (ℬ := (divisionTower ε 0).grading) ℝ u (1 : ℝ))
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerFuse_one_zero_tmul] at h3
  have h4 := towerSuccEquiv_symm_tmul_gen ε (1 + 0) u
  have e1 : (towerFuse ε 1 1).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ u
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = (towerSuccEquiv ε (1 + 0)).symm.toAlgEquiv
          (((towerFuse ε 1 0).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 1) (divisionTower ε 0)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 1)).gtensorCongr
                  (towerSuccEquiv ε 0)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 1).grading)
                  (ℬ := (divisionTower ε (0 + 1)).grading) ℝ u
                  (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-! ### The four columns and the `(1,1)` matrix -/

private theorem dst11_0 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 2) 1 0 0
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (1 : (divisionTower ε 2).carrier) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 2) 1 0
    (Sum.inl 0) (Sum.inl 0) 0
  rw [towerBasis_two_zero] at h
  exact h

private theorem dst11_1 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 2) 1 0 1
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 2) 1 0
    (Sum.inl 0) (Sum.inl 0) 1
  rw [towerBasis_two_one] at h
  exact h

private theorem dst11_2 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 2) 1 0 2
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier)) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 2) 1 0
    (Sum.inl 0) (Sum.inl 0) 2
  rw [towerBasis_two_two] at h
  exact h

private theorem dst11_3 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 2) 1 0 3
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 2) 1 0
    (Sum.inl 0) (Sum.inl 0) 3
  rw [towerBasis_two_three] at h
  exact h

private theorem tf11_col0 (ε : ℝ) :
    ((towerFuse ε 1 1).trans
        (matrixSuperOne (divisionTower ε 2)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
          (towerBasis ε 1) (towerBasis ε 1) 0)
      = matrixSuperBasis (towerBasis ε 2) 1 0 0 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
        (towerBasis ε 1) (towerBasis ε 1) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 1 0)
          (towerBasis ε 1 0) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 1) 0 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 2)).symm.toAlgEquiv
      ((towerFuse ε 1 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (1 : (divisionTower ε 1).carrier)
          (1 : (divisionTower ε 1).carrier)))
      = matrixSuperBasis (towerBasis ε 2) 1 0 0
  rw [towerFuse_one_one_tmul_one ε (1 : (divisionTower ε 1).carrier),
    matrixSuperOne_symm_single, dst11_0]
  rfl

private theorem tf11_col1 (ε : ℝ) :
    ((towerFuse ε 1 1).trans
        (matrixSuperOne (divisionTower ε 2)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
          (towerBasis ε 1) (towerBasis ε 1) 1)
      = matrixSuperBasis (towerBasis ε 2) 1 0 2 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
        (towerBasis ε 1) (towerBasis ε 1) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 1 0)
          (towerBasis ε 1 1) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 1) 0 1
  rw [towerBasis_one_zero, towerBasis_one_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 2)).symm.toAlgEquiv
      ((towerFuse ε 1 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (1 : (divisionTower ε 1).carrier)
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = matrixSuperBasis (towerBasis ε 2) 1 0 2
  rw [towerFuse_one_one_tmul_gen ε (1 : (divisionTower ε 1).carrier),
    matrixSuperOne_symm_single, dst11_2]
  rfl

private theorem tf11_col2 (ε : ℝ) :
    ((towerFuse ε 1 1).trans
        (matrixSuperOne (divisionTower ε 2)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
          (towerBasis ε 1) (towerBasis ε 1) 2)
      = matrixSuperBasis (towerBasis ε 2) 1 0 1 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
        (towerBasis ε 1) (towerBasis ε 1) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 1 1)
          (towerBasis ε 1 0) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 1) 1 0
  rw [towerBasis_one_zero, towerBasis_one_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 2)).symm.toAlgEquiv
      ((towerFuse ε 1 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
          (1 : (divisionTower ε 1).carrier)))
      = matrixSuperBasis (towerBasis ε 2) 1 0 1
  rw [towerFuse_one_one_tmul_one ε
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε),
    matrixSuperOne_symm_single, dst11_1]
  rfl

private theorem tf11_col3 (ε : ℝ) :
    ((towerFuse ε 1 1).trans
        (matrixSuperOne (divisionTower ε 2)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
          (towerBasis ε 1) (towerBasis ε 1) 3)
      = matrixSuperBasis (towerBasis ε 2) 1 0 3 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
        (towerBasis ε 1) (towerBasis ε 1) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 1 1)
          (towerBasis ε 1 1) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 1) 1 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 2)).symm.toAlgEquiv
      ((towerFuse ε 1 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = matrixSuperBasis (towerBasis ε 2) 1 0 3
  rw [towerFuse_one_one_tmul_gen ε
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε),
    matrixSuperOne_symm_single, dst11_3]
  rfl

/-- **Generic-`ε` value pinning for the first tower fuse**: the matrix of
`towerFuse ε 1 1 ; matrixSuperOne.symm` in the pilot frames is the
permutation matrix with columns `(e₀, e₂, e₁, e₃)`. -/
private theorem towerFuse_one_one_matrix (ε : ℝ) :
    LinearMap.toMatrix
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
          (towerBasis ε 1) (towerBasis ε 1))
        (matrixSuperBasis (towerBasis ε 2) 1 0)
        (((towerFuse ε 1 1).trans
            (matrixSuperOne (divisionTower ε 2)).symm).toAlgEquiv.toLinearMap)
      = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  have hcol : ∀ j : Fin 4,
      ((towerFuse ε 1 1).trans
          (matrixSuperOne (divisionTower ε 2)).symm).toAlgEquiv
          (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 1)
            (towerBasis ε 1) (towerBasis ε 1) j)
        = matrixSuperBasis (towerBasis ε 2) 1 0 (![0, 2, 1, 3] j) := by
    intro j
    fin_cases j
    · exact tf11_col0 ε
    · exact tf11_col1 ε
    · exact tf11_col2 ε
    · exact tf11_col3 ε
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j,
    Basis.repr_self_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-- **Deliverable 3**: the `(1,1)` branch value-pinning spec.  In the
left-major source frame `(1⊗1, 1⊗g, g⊗1, g⊗g)` and the flattened
`M_{1|0}(Cl_{0,2})` target frame `(1, g₁, g₂, g₁g₂)`, the fusion
isomorphism `realFuse 1 1` is the sign-free permutation sending columns to
`(e₀, e₂, e₁, e₃)`. -/
theorem realFuseMatrix_one_one :
    realFuseMatrix 1 1
      = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] :=
  towerFuse_one_one_matrix (-1)

end Superfusion

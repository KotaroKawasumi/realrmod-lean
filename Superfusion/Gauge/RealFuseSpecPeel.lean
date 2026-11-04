/-
Superfusion / Gauge / RealFuseSpecPeel

M15 semantic-bridge: **value-pinning spec theorems for the `RealFuse2`
peel forwards**.

Landed here (kernel-checked; no proof holes, no kernel-reducing tactics,
no new axioms — each depends only on `propext`, `Classical.choice`,
`Quot.sound`):

* `realFuseMatrix_1_6` (8 × 8), `realFuseMatrix_2_7` (8 × 8),
* `realFuseMatrix_1_5` (16 × 16), `realFuseMatrix_3_7` (16 × 16),
* `realFuseMatrix_2_6` (16 × 16).

Still open: `(2,5)`, `(3,6)` (32 × 32) and `(3,5)` (64 × 64) — see the
"Not yet landed" note at the end of the file.

**The peel evaluation pipeline.**  `peelFuse e` (`RealFuse2` : 393) is the
five-stage composite
`(towerSuccEquiv ⊗ towerSuccEquiv) ; gtensorInterchange ; (e ⊗ hypFuse) ;
gtensorMatrixAbsorb ; unitor ; cast`.  It is evaluated on a source frame
vector in four steps.

1. *Name the frame vector.*  `gtensorBasis_apply_pair` bridges the literal
   flat index to `towerBasis (-1) (m+1) i ᵍ⊗ towerBasis 1 (n+1) j`; the
   `mk`-form dictionary `tb1_*`/`tb2_*`/`tb3_*` (`towerBasis_low`,
   `towerBasis_high`) then splits each factor into its `OddDouble`
   coordinate.  **Always pass the `ε` argument explicitly** in the
   `rw [tb…]`: at `(2,7)`-shaped branches both factors contain a floor-1
   basis vector and an unapplied `tb1_0` rewrites the wrong one.
2. *Cross the peel.*  The four quadrant lemmas `peel_q00`…`peel_q11`
   (packaged as `PG00`…`PG11` for a general seed value, `P00`…`P11` for a
   `M_{1|0}` seed) reduce `peelFuse e (mk … ᵍ⊗ mk …)` to
   `[sgn β •] tailEquiv (e (u' ᵍ⊗ v') ᵍ⊗ W)` with `W ∈ {1, F, E, EF}` the
   `hypFuse` value on the peeled generators and `β = deg v'`.  The only
   Koszul sign in the whole chain is this `sgn β`, from
   `gtensorInterchange_tmul`.
3. *Absorb.*  `tail_single` computes the absorb tail on a pair of
   single-entry matrices; its eight specializations
   `tail_{one,F,E,EF}_{even,odd}` give the two-term value in terms of
   `peelIdx` block indices, keyed by the parity
   `ρ = π r + π s + deg d`.  Seeds with a multi-term value are split first
   with `tail_decL_add`/`tail_decL_sub`.
4. *Land on the target frame.*  The per-branch `d…` dictionaries convert
   `Matrix.single r s (bD e)` to `matrixSuperBasis bD (p+q) (p+q) idx`
   with `idx = e + k·(s' + (p+q)·r')`, and `two_smul_congr`/
   `four_smul_congr` plus the sign-flattening lemmas
   (`pair_*`, `z*_pair_*`, `F_*`/`H_*`/`G_*`) put the column in the
   uniform shape `c₁ • dst i₁ + … + c_r • dst i_r` that the final
   `LinearMap.toMatrix` + `Basis.repr_self_apply` + `fin_cases` step
   consumes.

**Pattern refinements over the pilot** (worth recording):

* *Never `congrArg f h` with `f` left to unification.*  The earlier
  partial development (`scripts/certgen/out/tower_peel_wip.lean.txt`)
  died on `Application type mismatch` in exactly this spot: `congrArg`
  applied to a graded-tensor linearity lemma cannot infer the grading
  arguments before `h` is elaborated.  Every such step here either spells
  `f` out completely or is replaced by a standalone lemma
  (`tail_dec_add`, `tail_decL_add`, …) whose statement fixes the shape.
* *Type-ascribe the carrier before `rw`.*  `x ᵍ⊗ₜ y` elaborated at
  `𝒜 ᵍ⊗[ℝ] ℬ` is defeq to but not usable in place of the same term at
  `(A.gtensor B).carrier`: `rw [map_add]` fails with "target expression is
  not type-correct".  Stating the linearity step as a `have` ascribed to
  `((A.gtensor B).carrier)` fixes the instance spelling once and for all.
* *`Eq.trans`/`exact` instead of `rw` across defeq boundaries.*  `peelIdx
  p q u x` versus the literal `Sum.inl 0`, `Fin (1+0)` versus `Fin 1`,
  `divisionTower ε 0` versus `SuperAlgebra.base ℝ` are all defeq but never
  syntactically equal; chains built from `Eq.trans`, `congrArg₂` and
  term-mode `:=` cross them for free, `rw` does not.
* *Coefficients must be literals.*  `-(-1 : ℝ)` is not defeq to `(1 : ℝ)`,
  so the sign-flattening lemmas are stated with the *result* coefficients
  written out (`F_*`, `G_*`, `H_*`: 24 two-line lemmas) rather than
  computed by `neg`.
* Cost: the whole file elaborates in ≈ 50 s; a `1|0`-seed branch is
  ≈ 25 lines/column, an `M_{p|q}`-seed branch ≈ 35 lines/column.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge).
-/
import Superfusion.Gauge.RealFuseMatrix

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace Superfusion

open Module TensorProduct GradedTensorProduct

/-! ### Shared application lemmas (re-derived from the pilot) -/

private theorem superRefl_apply (P : SuperAlgebra ℝ) (x : P.carrier) :
    (SuperAlgEquiv.refl P).toAlgEquiv x = x := rfl

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

/-! ### Graded-tensor linearity -/

private theorem gtmul_addG {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A]
    [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra ℬ] (x : A) (y y' : B) :
    (x ᵍ⊗ₜ[ℝ] (y + y') : 𝒜 ᵍ⊗[ℝ] ℬ) = x ᵍ⊗ₜ[ℝ] y + x ᵍ⊗ₜ[ℝ] y' := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] (y + y'))
      = GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] y)
        + GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] y')
  rw [← map_add, TensorProduct.tmul_add]

private theorem gtmul_smulG {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A]
    [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra ℬ] (c : ℝ) (x : A) (y : B) :
    (x ᵍ⊗ₜ[ℝ] (c • y) : 𝒜 ᵍ⊗[ℝ] ℬ) = c • (x ᵍ⊗ₜ[ℝ] y) := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] (c • y))
      = c • GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] y)
  rw [← map_smul, TensorProduct.tmul_smul]

private theorem zsmul_gtmul_left {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A)
    [GradedAlgebra 𝒜] (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra ℬ]
    (z : ℤ) (x : A) (y : B) :
    ((z • x) ᵍ⊗ₜ[ℝ] y : 𝒜 ᵍ⊗[ℝ] ℬ) = z • (x ᵍ⊗ₜ[ℝ] y) := by
  rw [show ((z • x) ᵍ⊗ₜ[ℝ] y : 𝒜 ᵍ⊗[ℝ] ℬ)
      = GradedTensorProduct.of ℝ 𝒜 ℬ ((z • x) ⊗ₜ[ℝ] y) from rfl,
    show ((z • x) ⊗ₜ[ℝ] y : A ⊗[ℝ] B) = z • (x ⊗ₜ[ℝ] y) from
      (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

private theorem zsmul_gtmul_right {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A)
    [GradedAlgebra 𝒜] (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra ℬ]
    (z : ℤ) (x : A) (y : B) :
    (x ᵍ⊗ₜ[ℝ] (z • y) : 𝒜 ᵍ⊗[ℝ] ℬ) = z • (x ᵍ⊗ₜ[ℝ] y) := by
  rw [show (x ᵍ⊗ₜ[ℝ] (z • y) : 𝒜 ᵍ⊗[ℝ] ℬ)
      = GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] (z • y)) from rfl,
    show (x ⊗ₜ[ℝ] (z • y) : A ⊗[ℝ] B) = z • (x ⊗ₜ[ℝ] y) from
      TensorProduct.tmul_smul _ _ _,
    map_zsmul]

/-- `(-1)^e`-smul is `((sgn e : ℤˣ) : ℤ)`-smul, generically. -/
private theorem uzpow_smul_eq {M : Type*} [AddCommGroup M] (e : ZMod 2)
    (z : M) :
    (-1 : ℤˣ) ^ e • z = ((sgn e : ℤˣ) : ℤ) • z := by
  rw [← sgn_eq_neg_one_uzpow, Units.smul_def]

private theorem sgnz_zero_smul {M : Type*} [AddCommGroup M] (x : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • x = x := by
  rw [sgn_zero, Units.val_one]
  exact one_zsmul x

private theorem tmul_congr_left {P Q : SuperAlgebra ℝ} {x x' : P.carrier}
    (y : Q.carrier) (h : x = x') :
    GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y
      = GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x' y :=
  by rw [h]

private theorem tmul_congr_right {P Q : SuperAlgebra ℝ} (x : P.carrier)
    {y y' : Q.carrier} (h : y = y') :
    GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y
      = GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y' :=
  by rw [h]

/-! ### Single-entry application lemmas -/

private theorem zmod2_single_mem_fold : ∀ x y j : ZMod 2,
    x + y + j + x + y = j := by decide

private theorem zmod2_tail_sign : ∀ u v ρ : ZMod 2,
    (u + v + 0) * ρ + v * ρ = u * ρ := by decide

/-- A single-entry matrix with homogeneous entry is homogeneous. -/
private theorem single_mem_matrixGradingA {n' : Type*} [Fintype n']
    [DecidableEq n'] (π : n' → ZMod 2) {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] {jd : ZMod 2} {d : A}
    (hd : d ∈ 𝒜 jd) (r s : n') :
    Matrix.single r s d ∈ matrixGradingA π 𝒜 (π r + π s + jd) := by
  intro a b
  by_cases hab : r = a ∧ s = b
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.single_apply_same,
      show π r + π s + jd + π r + π s = jd from
        zmod2_single_mem_fold (π r) (π s) jd]
    exact hd
  · rw [Matrix.single_apply_of_ne (h := hab)]
    exact zero_mem _

/-- `matrixSuperGtensor` on a single-entry matrix tensor a homogeneous
element: the column sign appears. -/
private theorem msg_single (Q P : SuperAlgebra ℝ) (p' q' : ℕ)
    (u v : Fin p' ⊕ Fin q') (x : Q.carrier) {jb : ZMod 2} {b : P.carrier}
    (hb : b ∈ P.grading jb) :
    (matrixSuperGtensor Q P p' q').toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity p' q') Q.grading)
          (ℬ := P.grading) ℝ (Matrix.single u v x) b)
      = ((sgn (sumParity p' q' v * jb) : ℤˣ) : ℤ) •
          Matrix.single u v
            (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ
              x b) := by
  refine Matrix.ext fun a c => ?_
  show matrixTensorSuperHom (sumParity p' q') Q.grading P.grading
      (GradedTensorProduct.tmul
        (𝒜 := matrixGradingA (sumParity p' q') Q.grading)
        (ℬ := P.grading) ℝ (Matrix.single u v x) b) a c
    = (((sgn (sumParity p' q' v * jb) : ℤˣ) : ℤ) •
        Matrix.single u v
          (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ
            x b)) a c
  rw [matrixTensorSuperHom_apply_of_mem (sumParity p' q') Q.grading
    P.grading (Matrix.single u v x) hb a c, Matrix.smul_apply]
  by_cases hac : u = a ∧ v = c
  · obtain ⟨rfl, rfl⟩ := hac
    rw [Matrix.single_apply_same, Matrix.single_apply_same]
  · rw [Matrix.single_apply_of_ne (h := hac),
      Matrix.single_apply_of_ne (h := hac), zero_gtmul, smul_zero,
      smul_zero]

/-- Entrywise functoriality on a single-entry matrix. -/
private theorem matrixSuperMap_single {P Q : SuperAlgebra ℝ}
    (e : SuperAlgEquiv P Q) (p' q' : ℕ) (r s : Fin p' ⊕ Fin q')
    (z : P.carrier) :
    (e.matrixSuper p' q').toAlgEquiv (Matrix.single r s z)
      = Matrix.single r s (e.toAlgEquiv z) := by
  show e.toAlgEquiv.mapMatrix (Matrix.single r s z) = _
  rw [AlgEquiv.mapMatrix_apply, Matrix.map_single]

/-- `matrixSuperComp` on a nested single-entry matrix. -/
private theorem matrixSuperComp_single (P : SuperAlgebra ℝ)
    (p' q' p q : ℕ) (u v : Fin p' ⊕ Fin q') (r s : Fin p ⊕ Fin q)
    (z : P.carrier) :
    (matrixSuperComp P p' q' p q).toAlgEquiv
        (Matrix.single u v (Matrix.single r s z))
      = Matrix.single (collapseIndexEquiv p' q' p q (u, r))
          (collapseIndexEquiv p' q' p q (v, s)) z := by
  show Matrix.reindexAlgEquiv ℝ _ (collapseIndexEquiv p' q' p q)
      ((Matrix.compAlgEquiv _ _ _ ℝ)
        (Matrix.single u v (Matrix.single r s z)))
    = _
  rw [Matrix.compAlgEquiv_apply, Matrix.comp_single_single]
  simp [Matrix.reindex_apply]

/-- `matrixSuperCast` on a single-entry matrix. -/
private theorem matrixSuperCast_single (D : SuperAlgebra ℝ)
    {p q p₂ q₂ : ℕ} (hp : p = p₂) (hq : q = q₂) (r s : Fin p ⊕ Fin q)
    (d : D.carrier) :
    (matrixSuperCast D hp hq).toAlgEquiv (Matrix.single r s d)
      = Matrix.single (Sum.map (finCongr hp) (finCongr hq) r)
          (Sum.map (finCongr hp) (finCongr hq) s) d := by
  subst hp
  subst hq
  have hid : ∀ x : Fin p ⊕ Fin q,
      Sum.map (finCongr rfl) (finCongr rfl) x = x := by
    rintro (x | x) <;> rfl
  rw [hid, hid]
  rfl

/-! ### The interchange on homogeneous pure tensors -/

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

/-- `gtensorInterchange` on pure tensors: the only Koszul sign is the
`b ↔ c` braid. -/
private theorem gtensorInterchange_tmul (A B C D : SuperAlgebra ℝ)
    {jb jc : ZMod 2} (a : A.carrier) {b : B.carrier} {c : C.carrier}
    (d : D.carrier) (hb : b ∈ B.grading jb) (hc : c ∈ C.grading jc) :
    (gtensorInterchange A B C D).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (A.gtensor B).grading)
          (ℬ := (C.gtensor D).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ a b)
          (GradedTensorProduct.tmul (𝒜 := C.grading) (ℬ := D.grading) ℝ c d))
      = ((sgn (jc * jb) : ℤˣ) : ℤ) •
          GradedTensorProduct.tmul (𝒜 := (A.gtensor C).grading)
            (ℬ := (B.gtensor D).grading) ℝ
            (GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := C.grading) ℝ
              a c)
            (GradedTensorProduct.tmul (𝒜 := B.grading) (ℬ := D.grading) ℝ
              b d) := by
  have h1 := gtensorAssoc_tmul A B (C.gtensor D) a b
    (GradedTensorProduct.tmul (𝒜 := C.grading) (ℬ := D.grading) ℝ c d)
  have h2 : ((SuperAlgEquiv.refl A).gtensorCongr
        (gtensorAssoc B C D).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := A.grading)
          (ℬ := (B.gtensor (C.gtensor D)).grading) ℝ a
          (GradedTensorProduct.tmul (𝒜 := B.grading)
            (ℬ := (C.gtensor D).grading) ℝ b
            (GradedTensorProduct.tmul (𝒜 := C.grading)
              (ℬ := D.grading) ℝ c d)))
      = GradedTensorProduct.tmul (𝒜 := A.grading)
          (ℬ := ((B.gtensor C).gtensor D).grading) ℝ a
          (GradedTensorProduct.tmul (𝒜 := (B.gtensor C).grading)
            (ℬ := D.grading) ℝ
            (GradedTensorProduct.tmul (𝒜 := B.grading)
              (ℬ := C.grading) ℝ b c) d) := by
    have hs := SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl A)
      (gtensorAssoc B C D).symm a
      (GradedTensorProduct.tmul (𝒜 := B.grading)
        (ℬ := (C.gtensor D).grading) ℝ b
        (GradedTensorProduct.tmul (𝒜 := C.grading) (ℬ := D.grading) ℝ c d))
    rw [superRefl_apply] at hs
    exact hs.trans (tmul_congr_right a (gtensorAssoc_symm_tmul B C D b c d))
  have h3 := gtensorComm_tmul_of_mem B C hb hc
  rw [uzpow_smul_eq] at h3
  have h3a : ((gtensorComm B C).gtensorCongr
        (SuperAlgEquiv.refl D)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (B.gtensor C).grading)
          (ℬ := D.grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := B.grading)
            (ℬ := C.grading) ℝ b c) d)
      = ((sgn (jc * jb) : ℤˣ) : ℤ) •
          GradedTensorProduct.tmul (𝒜 := (C.gtensor B).grading)
            (ℬ := D.grading) ℝ
            (GradedTensorProduct.tmul (𝒜 := C.grading)
              (ℬ := B.grading) ℝ c b) d := by
    have hs := SuperAlgEquiv.gtensorCongr_tmul (gtensorComm B C)
      (SuperAlgEquiv.refl D)
      (GradedTensorProduct.tmul (𝒜 := B.grading) (ℬ := C.grading) ℝ b c) d
    rw [superRefl_apply] at hs
    exact hs.trans ((tmul_congr_left d h3).trans
      (zsmul_gtmul_left _ _ _ _ _))
  have h3b : ((SuperAlgEquiv.refl A).gtensorCongr
        ((gtensorComm B C).gtensorCongr (SuperAlgEquiv.refl D))).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := A.grading)
          (ℬ := ((B.gtensor C).gtensor D).grading) ℝ a
          (GradedTensorProduct.tmul (𝒜 := (B.gtensor C).grading)
            (ℬ := D.grading) ℝ
            (GradedTensorProduct.tmul (𝒜 := B.grading)
              (ℬ := C.grading) ℝ b c) d))
      = ((sgn (jc * jb) : ℤˣ) : ℤ) •
          GradedTensorProduct.tmul (𝒜 := A.grading)
            (ℬ := ((C.gtensor B).gtensor D).grading) ℝ a
            (GradedTensorProduct.tmul (𝒜 := (C.gtensor B).grading)
              (ℬ := D.grading) ℝ
              (GradedTensorProduct.tmul (𝒜 := C.grading)
                (ℬ := B.grading) ℝ c b) d) := by
    have hs := SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl A)
      ((gtensorComm B C).gtensorCongr (SuperAlgEquiv.refl D)) a
      (GradedTensorProduct.tmul (𝒜 := (B.gtensor C).grading)
        (ℬ := D.grading) ℝ
        (GradedTensorProduct.tmul (𝒜 := B.grading)
          (ℬ := C.grading) ℝ b c) d)
    rw [superRefl_apply] at hs
    exact hs.trans ((tmul_congr_right a h3a).trans
      (zsmul_gtmul_right _ _ _ _ _))
  have h4 : ((SuperAlgEquiv.refl A).gtensorCongr
        (gtensorAssoc C B D)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := A.grading)
          (ℬ := ((C.gtensor B).gtensor D).grading) ℝ a
          (GradedTensorProduct.tmul (𝒜 := (C.gtensor B).grading)
            (ℬ := D.grading) ℝ
            (GradedTensorProduct.tmul (𝒜 := C.grading)
              (ℬ := B.grading) ℝ c b) d))
      = GradedTensorProduct.tmul (𝒜 := A.grading)
          (ℬ := (C.gtensor (B.gtensor D)).grading) ℝ a
          (GradedTensorProduct.tmul (𝒜 := C.grading)
            (ℬ := (B.gtensor D).grading) ℝ c
            (GradedTensorProduct.tmul (𝒜 := B.grading)
              (ℬ := D.grading) ℝ b d)) := by
    have hs := SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl A)
      (gtensorAssoc C B D) a
      (GradedTensorProduct.tmul (𝒜 := (C.gtensor B).grading)
        (ℬ := D.grading) ℝ
        (GradedTensorProduct.tmul (𝒜 := C.grading)
          (ℬ := B.grading) ℝ c b) d)
    rw [superRefl_apply] at hs
    exact hs.trans (tmul_congr_right a (gtensorAssoc_tmul C B D c b d))
  have h5 := gtensorAssoc_symm_tmul A C (B.gtensor D) a c
    (GradedTensorProduct.tmul (𝒜 := B.grading) (ℬ := D.grading) ℝ b d)
  have e1 : (gtensorInterchange A B C D).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (A.gtensor B).grading)
        (ℬ := (C.gtensor D).grading) ℝ
        (GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ a b)
        (GradedTensorProduct.tmul (𝒜 := C.grading) (ℬ := D.grading) ℝ c d))
      = (gtensorAssoc A C (B.gtensor D)).symm.toAlgEquiv
          (((SuperAlgEquiv.refl A).gtensorCongr
              (gtensorAssoc C B D)).toAlgEquiv
            (((SuperAlgEquiv.refl A).gtensorCongr
                ((gtensorComm B C).gtensorCongr
                  (SuperAlgEquiv.refl D))).toAlgEquiv
              (((SuperAlgEquiv.refl A).gtensorCongr
                  (gtensorAssoc B C D).symm).toAlgEquiv
                ((gtensorAssoc A B (C.gtensor D)).toAlgEquiv
                  (GradedTensorProduct.tmul
                    (𝒜 := (A.gtensor B).grading)
                    (ℬ := (C.gtensor D).grading) ℝ
                    (GradedTensorProduct.tmul (𝒜 := A.grading)
                      (ℬ := B.grading) ℝ a b)
                    (GradedTensorProduct.tmul (𝒜 := C.grading)
                      (ℬ := D.grading) ℝ c d)))))) := rfl
  refine e1.trans ?_
  refine (congrArg (fun w => (gtensorAssoc A C (B.gtensor D)).symm.toAlgEquiv
    (((SuperAlgEquiv.refl A).gtensorCongr (gtensorAssoc C B D)).toAlgEquiv
      (((SuperAlgEquiv.refl A).gtensorCongr
          ((gtensorComm B C).gtensorCongr (SuperAlgEquiv.refl D))).toAlgEquiv
        (((SuperAlgEquiv.refl A).gtensorCongr
            (gtensorAssoc B C D).symm).toAlgEquiv w)))) h1).trans ?_
  refine (congrArg (fun w => (gtensorAssoc A C (B.gtensor D)).symm.toAlgEquiv
    (((SuperAlgEquiv.refl A).gtensorCongr (gtensorAssoc C B D)).toAlgEquiv
      (((SuperAlgEquiv.refl A).gtensorCongr
          ((gtensorComm B C).gtensorCongr
            (SuperAlgEquiv.refl D))).toAlgEquiv w))) h2).trans ?_
  refine (congrArg (fun w => (gtensorAssoc A C (B.gtensor D)).symm.toAlgEquiv
    (((SuperAlgEquiv.refl A).gtensorCongr
        (gtensorAssoc C B D)).toAlgEquiv w)) h3b).trans ?_
  refine (congrArg
    (fun w => (gtensorAssoc A C (B.gtensor D)).symm.toAlgEquiv w)
    ((map_zsmul (((SuperAlgEquiv.refl A).gtensorCongr
        (gtensorAssoc C B D)).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn (jc * jb) : ℤˣ) : ℤ) • t) h4))).trans ?_
  exact (map_zsmul ((gtensorAssoc A C (B.gtensor D)).symm.toAlgEquiv)
      _ _).trans
    (congrArg (fun t => ((sgn (jc * jb) : ℤˣ) : ℤ) • t) h5)

/-! ### `hypFuse` on the four generator tensors

The generator data of `hypFuse` is `private` in `RealFuse2`; the two
lifted algebra maps are re-derived here **definitionally equal** to the
originals (all proof arguments are irrelevant), so `hypFuse`'s values on
pure tensors come from `GradedTensorProduct.lift_tmul` by `rfl`-crossing.
This is the pattern of `RealFuseSpecTower`'s `(1,7)` branch. -/

private theorem hyp_eq_mk_p_zero_of_mem_zero {ε : ℝ}
    {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 0) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε
        (OddDouble.p1 (evenGrading ℝ ℝ) ε x) 0 := by
  obtain ⟨-, h2⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [zero_add, evenGrading_one, Submodule.mem_bot] at h2
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h2]

private theorem hyp_eq_mk_zero_q_of_mem_one {ε : ℝ}
    {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 1) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε 0
        (OddDouble.p2 (evenGrading ℝ ℝ) ε x) := by
  obtain ⟨h1, -⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [evenGrading_one, Submodule.mem_bot] at h1
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h1]

/-- `E = [[0,1],[-1,0]]`. -/
private def hypE' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- `F = [[0,1],[1,0]]`. -/
private def hypF' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 0 1 1 0

private theorem hypE'_sq :
    hypE' * hypE'
      = algebraMap ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (-1 : ℝ) := by
  show Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 (-1) 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul]
  rw [map_neg, map_one, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg,
    neg_zero]

private theorem hypF'_sq :
    hypF' * hypF'
      = algebraMap ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (1 : ℝ) := by
  show Matrix.fromBlocks 0 1 1 0 * Matrix.fromBlocks 0 1 1 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_add, add_zero, mul_one]
  rw [map_one, Matrix.fromBlocks_one]

private theorem hypE'_mul_hypF' :
    hypE' * hypF' = Matrix.fromBlocks 1 0 0 (-1) := by
  show Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 1 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_add, add_zero, mul_one]

private theorem hypF'_mul_hypE' :
    hypF' * hypE' = Matrix.fromBlocks (-1) 0 0 1 := by
  show Matrix.fromBlocks 0 1 1 0 * Matrix.fromBlocks 0 1 (-1) 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_add, add_zero, mul_one, mul_neg, neg_zero]

private theorem hypEF'_anti : hypE' * hypF' = -(hypF' * hypE') := by
  rw [hypE'_mul_hypF', hypF'_mul_hypE', Matrix.fromBlocks_neg, neg_neg,
    neg_zero]

private theorem hconjE' (a : ℝ) :
    hypE' * (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) a
      = (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))
          (parityMap (evenGrading ℝ ℝ) a) * hypE' := by
  rw [parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top,
    Algebra.ofId_apply]
  exact (Algebra.commutes a hypE').symm

private theorem hconjF' (a : ℝ) :
    hypF' * (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) a
      = (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))
          (parityMap (evenGrading ℝ ℝ) a) * hypF' := by
  rw [parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top,
    Algebra.ofId_apply]
  exact (Algebra.commutes a hypF').symm

private noncomputable def hypFusePhi' :
    (divisionTower (-1 : ℝ) 1).carrier →ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  OddDouble.lift (evenGrading ℝ ℝ) (-1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypE'
    hypE'_sq hconjE'

private noncomputable def hypFusePsi' :
    (divisionTower (1 : ℝ) 1).carrier →ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  OddDouble.lift (evenGrading ℝ ℝ) (1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypF'
    hypF'_sq hconjF'

private theorem hypFusePhi'_gen :
    hypFusePhi' (OddDouble.gen (SuperAlgebra.base ℝ).grading (-1 : ℝ))
      = hypE' :=
  OddDouble.lift_gen (evenGrading ℝ ℝ) (-1 : ℝ) _ hypE' hypE'_sq hconjE'

private theorem hypFusePsi'_gen :
    hypFusePsi' (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ))
      = hypF' :=
  OddDouble.lift_gen (evenGrading ℝ ℝ) (1 : ℝ) _ hypF' hypF'_sq hconjF'

private theorem hypFusePhi'_mk_p_zero (a : ℝ) :
    hypFusePhi' (OddDouble.mk (evenGrading ℝ ℝ) (-1 : ℝ) a 0)
      = algebraMap ℝ _ a :=
  (OddDouble.lift_inl (evenGrading ℝ ℝ) (-1 : ℝ) _ hypE' hypE'_sq hconjE'
    a).trans (Algebra.ofId_apply _ a)

private theorem hypFusePhi'_mk_zero_q (a : ℝ) :
    hypFusePhi' (OddDouble.mk (evenGrading ℝ ℝ) (-1 : ℝ) 0 a)
      = a • hypE' := by
  rw [Algebra.smul_def]
  have h := OddDouble.lift_mk (evenGrading ℝ ℝ) (-1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypE'
    hypE'_sq hconjE' 0 a
  rw [map_zero, zero_add, Algebra.ofId_apply _] at h
  exact h

private theorem hypFusePsi'_mk_p_zero (a : ℝ) :
    hypFusePsi' (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) a 0)
      = algebraMap ℝ _ a :=
  (OddDouble.lift_inl (evenGrading ℝ ℝ) (1 : ℝ) _ hypF' hypF'_sq hconjF'
    a).trans (Algebra.ofId_apply _ a)

private theorem hypFusePsi'_mk_zero_q (a : ℝ) :
    hypFusePsi' (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) 0 a)
      = a • hypF' := by
  rw [Algebra.smul_def]
  have h := OddDouble.lift_mk (evenGrading ℝ ℝ) (1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypF'
    hypF'_sq hconjF' 0 a
  rw [map_zero, zero_add, Algebra.ofId_apply _] at h
  exact h

private theorem hypFuse_anticommutes' :
    ∀ ⦃i j : ZMod 2⦄ (a : (divisionTower (-1 : ℝ) 1).grading i)
      (b : (divisionTower (1 : ℝ) 1).grading j),
      hypFusePhi' (a : (divisionTower (-1 : ℝ) 1).carrier)
          * hypFusePsi' (b : (divisionTower (1 : ℝ) 1).carrier)
        = (-1 : ℤˣ) ^ (j * i) •
          (hypFusePsi' (b : (divisionTower (1 : ℝ) 1).carrier)
            * hypFusePhi' (a : (divisionTower (-1 : ℝ) 1).carrier)) := by
  intro i j a b
  rw [Units.smul_def, ← sgn_eq_neg_one_uzpow]
  rcases zmod2_cases i with hi | hi <;> subst hi
  · have ha := hyp_eq_mk_p_zero_of_mem_zero a.2
    rw [show (a : (divisionTower (-1 : ℝ) 1).carrier) = _ from ha,
      hypFusePhi'_mk_p_zero, mul_zero, sgn_zero, Units.val_one, one_smul]
    exact Algebra.commutes _ _
  · rcases zmod2_cases j with hj | hj <;> subst hj
    · have hb := hyp_eq_mk_p_zero_of_mem_zero b.2
      rw [show (b : (divisionTower (1 : ℝ) 1).carrier) = _ from hb,
        hypFusePsi'_mk_p_zero, zero_mul, sgn_zero, Units.val_one, one_smul]
      exact (Algebra.commutes _ _).symm
    · have ha := hyp_eq_mk_zero_q_of_mem_one a.2
      have hb := hyp_eq_mk_zero_q_of_mem_one b.2
      rw [show (a : (divisionTower (-1 : ℝ) 1).carrier) = _ from ha,
        show (b : (divisionTower (1 : ℝ) 1).carrier) = _ from hb,
        hypFusePhi'_mk_zero_q, hypFusePsi'_mk_zero_q, mul_one, sgn_one,
        units_sign_eq]
      rw [smul_mul_smul_comm, smul_mul_smul_comm, hypEF'_anti,
        mul_comm (OddDouble.p2 (evenGrading ℝ ℝ) (1 : ℝ)
            (b : (divisionTower (1 : ℝ) 1).carrier))
          (OddDouble.p2 (evenGrading ℝ ℝ) (-1 : ℝ)
            (a : (divisionTower (-1 : ℝ) 1).carrier))]
      rw [zsmul_eq_mul]
      simp

/-- **The `rfl`-crossing for `hypFuse`**. -/
private theorem hypFuse_apply_tmul (a : (divisionTower (-1 : ℝ) 1).carrier)
    (b : (divisionTower (1 : ℝ) 1).carrier) :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ a b)
      = hypFusePhi' a * hypFusePsi' b :=
  GradedTensorProduct.lift_tmul (divisionTower (-1 : ℝ) 1).grading
    (divisionTower (1 : ℝ) 1).grading hypFusePhi' hypFusePsi'
    hypFuse_anticommutes' a b

private theorem hypFuse_val_one_one :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (1 : (divisionTower (-1 : ℝ) 1).carrier)
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier) := by
  rw [hypFuse_apply_tmul, map_one, map_one, one_mul]
  rfl

private theorem hypFuse_val_one_gen :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (1 : (divisionTower (-1 : ℝ) 1).carrier)
          (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)))
      = hypF' := by
  rw [hypFuse_apply_tmul, map_one, hypFusePsi'_gen, one_mul]

private theorem hypFuse_val_gen_one :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading (-1 : ℝ))
          (1 : (divisionTower (1 : ℝ) 1).carrier))
      = hypE' := by
  rw [hypFuse_apply_tmul, hypFusePhi'_gen, map_one, mul_one]

private theorem hypFuse_val_gen_gen :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading (-1 : ℝ))
          (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)))
      = hypE' * hypF' := by
  rw [hypFuse_apply_tmul, hypFusePhi'_gen, hypFusePsi'_gen]

/-! ### The absorb tail of `peelFuse` -/

/-- The tail of `peelFuse` (everything after `e ᵍ⊗ hypFuse`), bundled so
that linearity is available in one step. -/
private noncomputable def tailEquiv (D : SuperAlgebra ℝ) (p q : ℕ) :
    SuperAlgEquiv
      ((D.matrixSuper p q).gtensor ((SuperAlgebra.base ℝ).matrixSuper 1 1))
      (D.matrixSuper (p + q) (p + q)) :=
  (gtensorMatrixAbsorb p q 1 1 (SuperAlgEquiv.refl (D.matrixSuper p q))
      (SuperAlgEquiv.refl ((SuperAlgebra.base ℝ).matrixSuper 1 1))).trans <|
    ((gtensorUnitorRight D).matrixSuper (1 * p + 1 * q) (1 * q + 1 * p)).trans
      (matrixSuperCast D (by ring) (by ring))

/-- The index bookkeeping of the tail: hyperbolic block index and inner
block index collapse to a `(p+q | p+q)` block index. -/
private def peelIdx (p q : ℕ) (u : Fin 1 ⊕ Fin 1) (x : Fin p ⊕ Fin q) :
    Fin (p + q) ⊕ Fin (p + q) :=
  Sum.map (finCongr (by ring : 1 * p + 1 * q = p + q))
    (finCongr (by ring : 1 * q + 1 * p = p + q))
    (collapseIndexEquiv 1 1 p q (u, x))

/-- **The tail on a pair of single-entry matrices** (the core value
computation of the `peelFuse` chain). -/
private theorem tail_single (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (u v : Fin 1 ⊕ Fin 1) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) (Matrix.single u v (1 : ℝ)))
      = ((sgn (sumParity 1 1 u
            * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) •
          Matrix.single (peelIdx p q u r) (peelIdx p q v s) d := by
  have mem1 : (1 : ℝ) ∈ (SuperAlgebra.base ℝ).grading 0 :=
    mem_evenGrading_zero ℝ ℝ 1
  have memP : Matrix.single r s d
      ∈ (D.matrixSuper p q).grading
          (sumParity p q r + sumParity p q s + jd) :=
    single_mem_matrixGradingA (sumParity p q) D.grading hd r s
  have memH : Matrix.single u v (1 : ℝ)
      ∈ ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading
          (sumParity 1 1 u + sumParity 1 1 v + 0) :=
    single_mem_matrixGradingA (sumParity 1 1)
      (SuperAlgebra.base ℝ).grading mem1 u v
  have h0 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (D.matrixSuper p q))
    (SuperAlgEquiv.refl ((SuperAlgebra.base ℝ).matrixSuper 1 1))
    (Matrix.single r s d) (Matrix.single u v (1 : ℝ))
  rw [superRefl_apply, superRefl_apply] at h0
  have h1 := gtensorComm_tmul_of_mem (D.matrixSuper p q)
    ((SuperAlgebra.base ℝ).matrixSuper 1 1) memP memH
  rw [uzpow_smul_eq] at h1
  have h2 := msg_single (SuperAlgebra.base ℝ) (D.matrixSuper p q) 1 1
    u v (1 : ℝ) memP
  have h3e := gtensorComm_tmul_of_mem (SuperAlgebra.base ℝ)
    (D.matrixSuper p q) mem1 memP
  rw [mul_zero, uzpow_zero, one_smul] at h3e
  have h3 : ((gtensorComm (SuperAlgebra.base ℝ)
        (D.matrixSuper p q)).matrixSuper 1 1).toAlgEquiv
        (Matrix.single u v
          (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
            (ℬ := (D.matrixSuper p q).grading) ℝ (1 : ℝ)
            (Matrix.single r s d)))
      = Matrix.single u v
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := (SuperAlgebra.base ℝ).grading) ℝ (Matrix.single r s d)
            (1 : ℝ)) :=
    (matrixSuperMap_single
      (gtensorComm (SuperAlgebra.base ℝ) (D.matrixSuper p q)) 1 1 u v
      (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
        (ℬ := (D.matrixSuper p q).grading) ℝ (1 : ℝ)
        (Matrix.single r s d))).trans
      (congrArg (fun t => Matrix.single u v t) h3e)
  have h4e : (matrixSuperGtensor D (SuperAlgebra.base ℝ) p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity p q) D.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ (Matrix.single r s d)
          (1 : ℝ))
      = Matrix.single r s
          (GradedTensorProduct.tmul (𝒜 := D.grading)
            (ℬ := (SuperAlgebra.base ℝ).grading) ℝ d (1 : ℝ)) :=
    (msg_single D (SuperAlgebra.base ℝ) p q r s d mem1).trans
      (by rw [mul_zero]; exact sgnz_zero_smul _)
  have h4 : ((matrixSuperGtensor D (SuperAlgebra.base ℝ) p q).matrixSuper
        1 1).toAlgEquiv
        (Matrix.single u v
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := (SuperAlgebra.base ℝ).grading) ℝ (Matrix.single r s d)
            (1 : ℝ)))
      = Matrix.single u v
          (Matrix.single r s
            (GradedTensorProduct.tmul (𝒜 := D.grading)
              (ℬ := (SuperAlgebra.base ℝ).grading) ℝ d (1 : ℝ))) :=
    (matrixSuperMap_single
      (matrixSuperGtensor D (SuperAlgebra.base ℝ) p q) 1 1 u v
      (GradedTensorProduct.tmul
        (𝒜 := matrixGradingA (sumParity p q) D.grading)
        (ℬ := (SuperAlgebra.base ℝ).grading) ℝ (Matrix.single r s d)
        (1 : ℝ))).trans
      (congrArg (fun t => Matrix.single u v t) h4e)
  have h5 := matrixSuperComp_single (D.gtensor (SuperAlgebra.base ℝ))
    1 1 p q u v r s
    (GradedTensorProduct.tmul (𝒜 := D.grading)
      (ℬ := (SuperAlgebra.base ℝ).grading) ℝ d (1 : ℝ))
  have h6 : ((gtensorUnitorRight D).matrixSuper (1 * p + 1 * q)
        (1 * q + 1 * p)).toAlgEquiv
        (Matrix.single (collapseIndexEquiv 1 1 p q (u, r))
          (collapseIndexEquiv 1 1 p q (v, s))
          (GradedTensorProduct.tmul (𝒜 := D.grading)
            (ℬ := (SuperAlgebra.base ℝ).grading) ℝ d (1 : ℝ)))
      = Matrix.single (collapseIndexEquiv 1 1 p q (u, r))
          (collapseIndexEquiv 1 1 p q (v, s)) d :=
    (matrixSuperMap_single (gtensorUnitorRight D)
      (1 * p + 1 * q) (1 * q + 1 * p)
      (collapseIndexEquiv 1 1 p q (u, r))
      (collapseIndexEquiv 1 1 p q (v, s))
      (GradedTensorProduct.tmul (𝒜 := D.grading)
        (ℬ := (SuperAlgebra.base ℝ).grading) ℝ d (1 : ℝ))).trans
      (congrArg
        (fun t => Matrix.single (collapseIndexEquiv 1 1 p q (u, r))
          (collapseIndexEquiv 1 1 p q (v, s)) t)
        (gtensorUnitorRight_tmul_one D d))
  have h7 := matrixSuperCast_single D
    (show 1 * p + 1 * q = p + q by ring) (show 1 * q + 1 * p = p + q by ring)
    (collapseIndexEquiv 1 1 p q (u, r)) (collapseIndexEquiv 1 1 p q (v, s)) d
  have hz : ((sgn ((sumParity 1 1 u + sumParity 1 1 v + 0)
          * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ)
        * ((sgn (sumParity 1 1 v
            * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ)
      = ((sgn (sumParity 1 1 u
          * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add, zmod2_tail_sign]
  have e1 : (tailEquiv D p q).toAlgEquiv
      (GradedTensorProduct.tmul
        (𝒜 := (D.matrixSuper p q).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
        (Matrix.single r s d) (Matrix.single u v (1 : ℝ)))
      = (matrixSuperCast D (show 1 * p + 1 * q = p + q by ring)
            (show 1 * q + 1 * p = p + q by ring)).toAlgEquiv
          (((gtensorUnitorRight D).matrixSuper (1 * p + 1 * q)
              (1 * q + 1 * p)).toAlgEquiv
            ((matrixSuperComp (D.gtensor (SuperAlgebra.base ℝ))
                1 1 p q).toAlgEquiv
              (((matrixSuperGtensor D (SuperAlgebra.base ℝ) p q).matrixSuper
                  1 1).toAlgEquiv
                (((gtensorComm (SuperAlgebra.base ℝ)
                    (D.matrixSuper p q)).matrixSuper 1 1).toAlgEquiv
                  ((matrixSuperGtensor (SuperAlgebra.base ℝ)
                      (D.matrixSuper p q) 1 1).toAlgEquiv
                    ((gtensorComm (D.matrixSuper p q)
                        ((SuperAlgebra.base ℝ).matrixSuper 1 1)).toAlgEquiv
                      (((SuperAlgEquiv.refl
                            (D.matrixSuper p q)).gtensorCongr
                          (SuperAlgEquiv.refl
                            ((SuperAlgebra.base ℝ).matrixSuper
                              1 1))).toAlgEquiv
                        (GradedTensorProduct.tmul
                          (𝒜 := (D.matrixSuper p q).grading)
                          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper
                            1 1).grading) ℝ
                          (Matrix.single r s d)
                          (Matrix.single u v (1 : ℝ)))))))))) := rfl
  have b1 : (gtensorComm (D.matrixSuper p q)
        ((SuperAlgebra.base ℝ).matrixSuper 1 1)).toAlgEquiv
        (((SuperAlgEquiv.refl (D.matrixSuper p q)).gtensorCongr
            (SuperAlgEquiv.refl
              ((SuperAlgebra.base ℝ).matrixSuper 1 1))).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (Matrix.single r s d) (Matrix.single u v (1 : ℝ))))
      = ((sgn ((sumParity 1 1 u + sumParity 1 1 v + 0)
            * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) •
          GradedTensorProduct.tmul
            (𝒜 := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading)
            (ℬ := (D.matrixSuper p q).grading) ℝ
            (Matrix.single u v (1 : ℝ)) (Matrix.single r s d) :=
    (congrArg (fun w => (gtensorComm (D.matrixSuper p q)
      ((SuperAlgebra.base ℝ).matrixSuper 1 1)).toAlgEquiv w) h0).trans h1
  have b2 := (congrArg
      (fun w => (matrixSuperGtensor (SuperAlgebra.base ℝ)
        (D.matrixSuper p q) 1 1).toAlgEquiv w) b1).trans
    ((map_zsmul ((matrixSuperGtensor (SuperAlgebra.base ℝ)
        (D.matrixSuper p q) 1 1).toAlgEquiv) _ _).trans
      ((congrArg (fun t => ((sgn ((sumParity 1 1 u + sumParity 1 1 v + 0)
          * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) • t)
        h2).trans
        ((smul_smul _ _ _).trans
          (congrArg (fun t => t • Matrix.single u v
            (GradedTensorProduct.tmul
              (𝒜 := (SuperAlgebra.base ℝ).grading)
              (ℬ := (D.matrixSuper p q).grading) ℝ (1 : ℝ)
              (Matrix.single r s d))) hz))))
  have b3 := (congrArg
      (fun w => ((gtensorComm (SuperAlgebra.base ℝ)
        (D.matrixSuper p q)).matrixSuper 1 1).toAlgEquiv w) b2).trans
    ((map_zsmul (((gtensorComm (SuperAlgebra.base ℝ)
        (D.matrixSuper p q)).matrixSuper 1 1).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn (sumParity 1 1 u
        * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) • t) h3))
  have b4 := (congrArg
      (fun w => ((matrixSuperGtensor D (SuperAlgebra.base ℝ)
        p q).matrixSuper 1 1).toAlgEquiv w) b3).trans
    ((map_zsmul (((matrixSuperGtensor D (SuperAlgebra.base ℝ)
        p q).matrixSuper 1 1).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn (sumParity 1 1 u
        * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) • t) h4))
  have b5 := (congrArg
      (fun w => (matrixSuperComp (D.gtensor (SuperAlgebra.base ℝ))
        1 1 p q).toAlgEquiv w) b4).trans
    ((map_zsmul ((matrixSuperComp (D.gtensor (SuperAlgebra.base ℝ))
        1 1 p q).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn (sumParity 1 1 u
        * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) • t) h5))
  have b6 := (congrArg
      (fun w => ((gtensorUnitorRight D).matrixSuper (1 * p + 1 * q)
        (1 * q + 1 * p)).toAlgEquiv w) b5).trans
    ((map_zsmul (((gtensorUnitorRight D).matrixSuper (1 * p + 1 * q)
        (1 * q + 1 * p)).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn (sumParity 1 1 u
        * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) • t) h6))
  have b7 := (congrArg
      (fun w => (matrixSuperCast D
        (show 1 * p + 1 * q = p + q by ring)
        (show 1 * q + 1 * p = p + q by ring)).toAlgEquiv w) b6).trans
    ((map_zsmul ((matrixSuperCast D
        (show 1 * p + 1 * q = p + q by ring)
        (show 1 * q + 1 * p = p + q by ring)).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn (sumParity 1 1 u
        * (sumParity p q r + sumParity p q s + jd)) : ℤˣ) : ℤ) • t) h7))
  exact e1.trans b7

/-- Tail on the even hyperbolic row (`u = inl`): no sign. -/
private theorem tail_single_L (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (v : Fin 1 ⊕ Fin 1) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) (Matrix.single (Sum.inl 0) v (1 : ℝ)))
      = Matrix.single (peelIdx p q (Sum.inl 0) r) (peelIdx p q v s) d := by
  have h := tail_single D p q hd r s (Sum.inl 0) v
  rw [show sumParity 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) = 0 from rfl,
    zero_mul, sgn_zero, Units.val_one, one_smul] at h
  exact h

/-- Tail on the odd hyperbolic row (`u = inr`), even total inner degree. -/
private theorem tail_single_R_even (D : SuperAlgebra ℝ) (p q : ℕ)
    {jd : ZMod 2} {d : D.carrier} (hd : d ∈ D.grading jd)
    (r s : Fin p ⊕ Fin q) (v : Fin 1 ⊕ Fin 1)
    (hρ : sumParity p q r + sumParity p q s + jd = 0) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) (Matrix.single (Sum.inr 0) v (1 : ℝ)))
      = Matrix.single (peelIdx p q (Sum.inr 0) r) (peelIdx p q v s) d := by
  have h := tail_single D p q hd r s (Sum.inr 0) v
  rw [hρ, mul_zero, sgn_zero, Units.val_one, one_smul] at h
  exact h

/-- Tail on the odd hyperbolic row (`u = inr`), odd total inner degree. -/
private theorem tail_single_R_odd (D : SuperAlgebra ℝ) (p q : ℕ)
    {jd : ZMod 2} {d : D.carrier} (hd : d ∈ D.grading jd)
    (r s : Fin p ⊕ Fin q) (v : Fin 1 ⊕ Fin 1)
    (hρ : sumParity p q r + sumParity p q s + jd = 1) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) (Matrix.single (Sum.inr 0) v (1 : ℝ)))
      = -Matrix.single (peelIdx p q (Sum.inr 0) r) (peelIdx p q v s) d := by
  have h := tail_single D p q hd r s (Sum.inr 0) v
  rw [hρ, show sumParity 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) = 1 from rfl,
    one_mul, sgn_one, units_sign_eq,
    show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_one_zsmul] at h
  exact h

/-! ### The hyperbolic matrices as single-entry sums -/

private theorem gtmul_subG {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A]
    [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra ℬ] (x : A) (y y' : B) :
    (x ᵍ⊗ₜ[ℝ] (y - y') : 𝒜 ᵍ⊗[ℝ] ℬ) = x ᵍ⊗ₜ[ℝ] y - x ᵍ⊗ₜ[ℝ] y' := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] (y - y'))
      = GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] y)
        - GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] y')
  rw [← map_sub, TensorProduct.tmul_sub]

private theorem WDec_one :
    (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
          (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  show (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) = _
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp

private theorem WDec_F :
    hypF'
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
          (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp [hypF', Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

private theorem WDec_E :
    hypE'
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
          (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        - Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp [hypE', Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

private theorem WDec_EF :
    hypE' * hypF'
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
          (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        - Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  rw [hypE'_mul_hypF']
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-! ### The tail on `single ⊗ W` for the four hyperbolic values -/

/-- Split the tail along an additive decomposition of the hyperbolic
factor.  (Stated as a standalone lemma so that the graded-tensor
linearity step never has to be elaborated against a metavariable.) -/
private theorem tail_dec_add (D : SuperAlgebra ℝ) (p q : ℕ)
    (M : (D.matrixSuper p q).carrier)
    (W W₁ W₂ : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)
    (h : W = W₁ + W₂) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W)
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W₁)
        + (tailEquiv D p q).toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
              (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
              M W₂) := by
  subst h
  have hd : (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M (W₁ + W₂)
      : ((D.matrixSuper p q).gtensor
          ((SuperAlgebra.base ℝ).matrixSuper 1 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W₁
        + GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W₂ :=
    gtmul_addG _ _ _ _ _
  rw [hd]
  exact map_add _ _ _

/-- Split the tail along a subtractive decomposition. -/
private theorem tail_dec_sub (D : SuperAlgebra ℝ) (p q : ℕ)
    (M : (D.matrixSuper p q).carrier)
    (W W₁ W₂ : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)
    (h : W = W₁ - W₂) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W)
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W₁)
        - (tailEquiv D p q).toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
              (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
              M W₂) := by
  subst h
  have hd : (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M (W₁ - W₂)
      : ((D.matrixSuper p q).gtensor
          ((SuperAlgebra.base ℝ).matrixSuper 1 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W₁
        - GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W₂ :=
    gtmul_subG _ _ _ _ _
  rw [hd]
  exact map_sub _ _ _

private theorem tail_one_even (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 0) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d)
          (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier))
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inl 0) s) d
        + Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inr 0) s) d := by
  have h1 := tail_dec_add D p q (Matrix.single r s d) _ _ _ WDec_one
  have h2 := tail_single_L D p q hd r s (Sum.inl 0)
  have h3 := tail_single_R_even D p q hd r s (Sum.inr 0) hρ
  exact h1.trans (congrArg₂ (· + ·) h2 h3)

private theorem tail_one_odd (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 1) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d)
          (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier))
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inl 0) s) d
        - Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inr 0) s) d := by
  have h1 := tail_dec_add D p q (Matrix.single r s d) _ _ _ WDec_one
  have h2 := tail_single_L D p q hd r s (Sum.inl 0)
  have h3 := tail_single_R_odd D p q hd r s (Sum.inr 0) hρ
  exact (h1.trans (congrArg₂ (· + ·) h2 h3)).trans (sub_eq_add_neg _ _).symm

private theorem tail_F_even (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 0) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) hypF')
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inr 0) s) d
        + Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inl 0) s) d := by
  have h1 := tail_dec_add D p q (Matrix.single r s d) _ _ _ WDec_F
  have h2 := tail_single_L D p q hd r s (Sum.inr 0)
  have h3 := tail_single_R_even D p q hd r s (Sum.inl 0) hρ
  exact h1.trans (congrArg₂ (· + ·) h2 h3)

private theorem tail_F_odd (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 1) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) hypF')
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inr 0) s) d
        - Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inl 0) s) d := by
  have h1 := tail_dec_add D p q (Matrix.single r s d) _ _ _ WDec_F
  have h2 := tail_single_L D p q hd r s (Sum.inr 0)
  have h3 := tail_single_R_odd D p q hd r s (Sum.inl 0) hρ
  exact (h1.trans (congrArg₂ (· + ·) h2 h3)).trans (sub_eq_add_neg _ _).symm

private theorem tail_E_even (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 0) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) hypE')
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inr 0) s) d
        - Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inl 0) s) d := by
  have h1 := tail_dec_sub D p q (Matrix.single r s d) _ _ _ WDec_E
  have h2 := tail_single_L D p q hd r s (Sum.inr 0)
  have h3 := tail_single_R_even D p q hd r s (Sum.inl 0) hρ
  exact h1.trans (congrArg₂ (· - ·) h2 h3)

private theorem tail_E_odd (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 1) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) hypE')
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inr 0) s) d
        + Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inl 0) s) d := by
  have h1 := tail_dec_sub D p q (Matrix.single r s d) _ _ _ WDec_E
  have h2 := tail_single_L D p q hd r s (Sum.inr 0)
  have h3 := tail_single_R_odd D p q hd r s (Sum.inl 0) hρ
  exact (h1.trans (congrArg₂ (· - ·) h2 h3)).trans (sub_neg_eq_add _ _)

private theorem tail_EF_even (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 0) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) (hypE' * hypF'))
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inl 0) s) d
        - Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inr 0) s) d := by
  have h1 := tail_dec_sub D p q (Matrix.single r s d) _ _ _ WDec_EF
  have h2 := tail_single_L D p q hd r s (Sum.inl 0)
  have h3 := tail_single_R_even D p q hd r s (Sum.inr 0) hρ
  exact h1.trans (congrArg₂ (· - ·) h2 h3)

private theorem tail_EF_odd (D : SuperAlgebra ℝ) (p q : ℕ) {jd : ZMod 2}
    {d : D.carrier} (hd : d ∈ D.grading jd) (r s : Fin p ⊕ Fin q)
    (hρ : sumParity p q r + sumParity p q s + jd = 1) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single r s d) (hypE' * hypF'))
      = Matrix.single (peelIdx p q (Sum.inl 0) r)
          (peelIdx p q (Sum.inl 0) s) d
        + Matrix.single (peelIdx p q (Sum.inr 0) r)
            (peelIdx p q (Sum.inr 0) s) d := by
  have h1 := tail_dec_sub D p q (Matrix.single r s d) _ _ _ WDec_EF
  have h2 := tail_single_L D p q hd r s (Sum.inl 0)
  have h3 := tail_single_R_odd D p q hd r s (Sum.inr 0) hρ
  exact (h1.trans (congrArg₂ (· - ·) h2 h3)).trans (sub_neg_eq_add _ _)

/-! ### The tower step (re-derived from the tower spec file) -/

private theorem equivGradedTensor_tmul_one {A : Type*} [Ring A]
    [Algebra ℝ A] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (ε : ℝ)
    (t : A) :
    OddDouble.equivGradedTensor 𝒜 ε
        (GradedTensorProduct.tmul (𝒜 := 𝒜) (ℬ := AdjoinOdd.grading ε) ℝ t 1)
      = OddDouble.mk 𝒜 ε t 0 := by
  rw [OddDouble.equivGradedTensor_tmul, map_one, mul_one, OddDouble.inl_apply]

private theorem equivGradedTensor_tmul_e {A : Type*} [Ring A]
    [Algebra ℝ A] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (ε : ℝ)
    (t : A) :
    OddDouble.equivGradedTensor 𝒜 ε
        (GradedTensorProduct.tmul (𝒜 := 𝒜) (ℬ := AdjoinOdd.grading ε) ℝ t
          (AdjoinOdd.e ε))
      = OddDouble.mk 𝒜 ε 0 t := by
  rw [OddDouble.equivGradedTensor_tmul, OddDouble.inl_apply, OddDouble.inr_e]
  refine OddDouble.ext 𝒜 ε ?_ ?_ <;> simp [parityMap_one]

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

/-- The forward tower step on the `A`-coordinate: `mk t 0 ↦ t ᵍ⊗ 1`. -/
private theorem towerSuccEquiv_mk_left (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).toAlgEquiv
        (OddDouble.mk (divisionTower ε n).grading ε t 0)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (1 : (divisionTower ε 1).carrier) := by
  have h := towerSuccEquiv_symm_tmul_one ε n t
  exact ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε n).toAlgEquiv)).mp h).symm

/-- The forward tower step on the `A·g`-coordinate: `mk 0 t ↦ t ᵍ⊗ g`. -/
private theorem towerSuccEquiv_mk_right (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).toAlgEquiv
        (OddDouble.mk (divisionTower ε n).grading ε 0 t)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) := by
  have h := towerSuccEquiv_symm_tmul_gen ε n t
  exact ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε n).toAlgEquiv)).mp h).symm

/-! ### The tower-basis dictionary (floors `0`–`3`) -/

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

/-- The odd generator of a length-one tower floor is odd. -/
private theorem gen_mem_one (ε : ℝ) :
    OddDouble.gen (SuperAlgebra.base ℝ).grading ε
      ∈ (divisionTower ε 1).grading 1 := by
  have h := towerBasis_mem ε 1 1
  rw [towerBasis_one_one] at h
  exact h

/-! ### The four quadrant lemmas for `peelFuse` -/

private theorem peel_q00 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (e.toAlgEquiv
              (GradedTensorProduct.tmul
                (𝒜 := (divisionTower (-1 : ℝ) m).grading)
                (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v'))
            (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)) := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (towerSuccEquiv (-1 : ℝ) m) (towerSuccEquiv (1 : ℝ) n)
    (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
    (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0)
  rw [towerSuccEquiv_mk_left, towerSuccEquiv_mk_left] at h1
  have h2 := gtensorInterchange_tmul (divisionTower (-1 : ℝ) m)
    (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
    (divisionTower (1 : ℝ) 1) u' (1 : (divisionTower (1 : ℝ) 1).carrier)
    (SetLike.one_mem_graded (divisionTower (-1 : ℝ) 1).grading) hv'
  rw [mul_zero, sgn_zero, Units.val_one, one_smul] at h2
  have h3 := SuperAlgEquiv.gtensorCongr_tmul e hypFuse
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
      (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v')
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
      (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
      (1 : (divisionTower (-1 : ℝ) 1).carrier)
      (1 : (divisionTower (1 : ℝ) 1).carrier))
  rw [hypFuse_val_one_one] at h3
  have e1 : (peelFuse e).toAlgEquiv
      (GradedTensorProduct.tmul
        (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
        (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
        (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
        (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = (tailEquiv D p q).toAlgEquiv
          ((e.gtensorCongr hypFuse).toAlgEquiv
            ((gtensorInterchange (divisionTower (-1 : ℝ) m)
                (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
                (divisionTower (1 : ℝ) 1)).toAlgEquiv
              (((towerSuccEquiv (-1 : ℝ) m).gtensorCongr
                  (towerSuccEquiv (1 : ℝ) n)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
                  (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
                  (OddDouble.mk (divisionTower (-1 : ℝ) m).grading
                    (-1 : ℝ) u' 0)
                  (OddDouble.mk (divisionTower (1 : ℝ) n).grading
                    (1 : ℝ) v' 0))))) := rfl
  rw [h1, h2, h3] at e1
  exact e1

private theorem peel_q01 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (e.toAlgEquiv
              (GradedTensorProduct.tmul
                (𝒜 := (divisionTower (-1 : ℝ) m).grading)
                (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v'))
            hypF') := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (towerSuccEquiv (-1 : ℝ) m) (towerSuccEquiv (1 : ℝ) n)
    (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
    (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v')
  rw [towerSuccEquiv_mk_left, towerSuccEquiv_mk_right] at h1
  have h2 := gtensorInterchange_tmul (divisionTower (-1 : ℝ) m)
    (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
    (divisionTower (1 : ℝ) 1) u'
    (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ))
    (SetLike.one_mem_graded (divisionTower (-1 : ℝ) 1).grading) hv'
  rw [mul_zero, sgn_zero, Units.val_one, one_smul] at h2
  have h3 := SuperAlgEquiv.gtensorCongr_tmul e hypFuse
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
      (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v')
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
      (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
      (1 : (divisionTower (-1 : ℝ) 1).carrier)
      (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)))
  rw [hypFuse_val_one_gen] at h3
  have e1 : (peelFuse e).toAlgEquiv
      (GradedTensorProduct.tmul
        (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
        (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
        (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
        (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = (tailEquiv D p q).toAlgEquiv
          ((e.gtensorCongr hypFuse).toAlgEquiv
            ((gtensorInterchange (divisionTower (-1 : ℝ) m)
                (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
                (divisionTower (1 : ℝ) 1)).toAlgEquiv
              (((towerSuccEquiv (-1 : ℝ) m).gtensorCongr
                  (towerSuccEquiv (1 : ℝ) n)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
                  (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
                  (OddDouble.mk (divisionTower (-1 : ℝ) m).grading
                    (-1 : ℝ) u' 0)
                  (OddDouble.mk (divisionTower (1 : ℝ) n).grading
                    (1 : ℝ) 0 v'))))) := rfl
  rw [h1, h2, h3] at e1
  exact e1

private theorem peel_q10 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = ((sgn β : ℤˣ) : ℤ) •
          (tailEquiv D p q).toAlgEquiv
            (GradedTensorProduct.tmul
              (𝒜 := (D.matrixSuper p q).grading)
              (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
              (e.toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower (-1 : ℝ) m).grading)
                  (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v'))
              hypE') := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (towerSuccEquiv (-1 : ℝ) m) (towerSuccEquiv (1 : ℝ) n)
    (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
    (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0)
  rw [towerSuccEquiv_mk_right, towerSuccEquiv_mk_left] at h1
  have h2 := gtensorInterchange_tmul (divisionTower (-1 : ℝ) m)
    (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
    (divisionTower (1 : ℝ) 1) u'
    (1 : (divisionTower (1 : ℝ) 1).carrier)
    (gen_mem_one (-1 : ℝ)) hv'
  rw [mul_one] at h2
  have h3 := SuperAlgEquiv.gtensorCongr_tmul e hypFuse
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
      (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v')
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
      (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
      (OddDouble.gen (SuperAlgebra.base ℝ).grading (-1 : ℝ))
      (1 : (divisionTower (1 : ℝ) 1).carrier))
  rw [hypFuse_val_gen_one] at h3
  have e1 : (peelFuse e).toAlgEquiv
      (GradedTensorProduct.tmul
        (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
        (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
        (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
        (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = (tailEquiv D p q).toAlgEquiv
          ((e.gtensorCongr hypFuse).toAlgEquiv
            ((gtensorInterchange (divisionTower (-1 : ℝ) m)
                (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
                (divisionTower (1 : ℝ) 1)).toAlgEquiv
              (((towerSuccEquiv (-1 : ℝ) m).gtensorCongr
                  (towerSuccEquiv (1 : ℝ) n)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
                  (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
                  (OddDouble.mk (divisionTower (-1 : ℝ) m).grading
                    (-1 : ℝ) 0 u')
                  (OddDouble.mk (divisionTower (1 : ℝ) n).grading
                    (1 : ℝ) v' 0))))) := rfl
  have b1 := (congrArg
      (fun w => (gtensorInterchange (divisionTower (-1 : ℝ) m)
        (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
        (divisionTower (1 : ℝ) 1)).toAlgEquiv w) h1).trans h2
  have b2 := (congrArg
      (fun w => (e.gtensorCongr hypFuse).toAlgEquiv w) b1).trans
    ((map_zsmul ((e.gtensorCongr hypFuse).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn β : ℤˣ) : ℤ) • t) h3))
  have b3 := (congrArg
      (fun w => (tailEquiv D p q).toAlgEquiv w) b2).trans
    (map_zsmul ((tailEquiv D p q).toAlgEquiv) _ _)
  exact e1.trans b3

private theorem peel_q11 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = ((sgn β : ℤˣ) : ℤ) •
          (tailEquiv D p q).toAlgEquiv
            (GradedTensorProduct.tmul
              (𝒜 := (D.matrixSuper p q).grading)
              (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
              (e.toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower (-1 : ℝ) m).grading)
                  (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v'))
              (hypE' * hypF')) := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (towerSuccEquiv (-1 : ℝ) m) (towerSuccEquiv (1 : ℝ) n)
    (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
    (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v')
  rw [towerSuccEquiv_mk_right, towerSuccEquiv_mk_right] at h1
  have h2 := gtensorInterchange_tmul (divisionTower (-1 : ℝ) m)
    (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
    (divisionTower (1 : ℝ) 1) u'
    (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ))
    (gen_mem_one (-1 : ℝ)) hv'
  rw [mul_one] at h2
  have h3 := SuperAlgEquiv.gtensorCongr_tmul e hypFuse
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
      (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v')
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
      (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
      (OddDouble.gen (SuperAlgebra.base ℝ).grading (-1 : ℝ))
      (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)))
  rw [hypFuse_val_gen_gen] at h3
  have e1 : (peelFuse e).toAlgEquiv
      (GradedTensorProduct.tmul
        (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
        (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
        (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
        (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = (tailEquiv D p q).toAlgEquiv
          ((e.gtensorCongr hypFuse).toAlgEquiv
            ((gtensorInterchange (divisionTower (-1 : ℝ) m)
                (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
                (divisionTower (1 : ℝ) 1)).toAlgEquiv
              (((towerSuccEquiv (-1 : ℝ) m).gtensorCongr
                  (towerSuccEquiv (1 : ℝ) n)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
                  (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
                  (OddDouble.mk (divisionTower (-1 : ℝ) m).grading
                    (-1 : ℝ) 0 u')
                  (OddDouble.mk (divisionTower (1 : ℝ) n).grading
                    (1 : ℝ) 0 v'))))) := rfl
  have b1 := (congrArg
      (fun w => (gtensorInterchange (divisionTower (-1 : ℝ) m)
        (divisionTower (-1 : ℝ) 1) (divisionTower (1 : ℝ) n)
        (divisionTower (1 : ℝ) 1)).toAlgEquiv w) h1).trans h2
  have b2 := (congrArg
      (fun w => (e.gtensorCongr hypFuse).toAlgEquiv w) b1).trans
    ((map_zsmul ((e.gtensorCongr hypFuse).toAlgEquiv) _ _).trans
      (congrArg (fun t => ((sgn β : ℤˣ) : ℤ) • t) h3))
  have b3 := (congrArg
      (fun w => (tailEquiv D p q).toAlgEquiv w) b2).trans
    (map_zsmul ((tailEquiv D p q).toAlgEquiv) _ _)
  exact e1.trans b3

/-! ### Sign bookkeeping: `ℤ`-signs to `ℝ`-coefficients -/

private theorem pair_add {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) : X + Y = (1 : ℝ) • X + (1 : ℝ) • Y := by
  rw [one_smul, one_smul]

private theorem pair_sub {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) : X - Y = (1 : ℝ) • X + (-1 : ℝ) • Y := by
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg]

private theorem zpos_pair_add {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (X + Y) = (1 : ℝ) • X + (1 : ℝ) • Y := by
  rw [sgn_zero, Units.val_one, one_zsmul, one_smul, one_smul]

private theorem zpos_pair_sub {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (X - Y)
      = (1 : ℝ) • X + (-1 : ℝ) • Y := by
  rw [sgn_zero, Units.val_one, one_zsmul, one_smul, neg_one_smul,
    ← sub_eq_add_neg]

private theorem zneg_pair_add {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (X + Y)
      = (-1 : ℝ) • X + (-1 : ℝ) • Y := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul, neg_one_smul, neg_one_smul, neg_add]

private theorem zneg_pair_sub {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (X - Y)
      = (-1 : ℝ) • X + (1 : ℝ) • Y := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul, neg_one_smul, one_smul, neg_sub, ← sub_eq_neg_add]

/-! ### Peel columns for a `M_{1|0}` seed

Both base seeds (`baseFuseL`, `baseFuseR`) land in `M_{1|0}(D)` and send
a source frame vector to a single-entry matrix `single (inl 0) (inl 0) d`
with `d` a frame vector of `D`.  These eight lemmas turn that into the
peel's value in the `M_{1|1}(D)` single-entry frame. -/

section Seed10

variable {m n : ℕ} {D : SuperAlgebra ℝ}

/-- The seed hypothesis shape. -/
private abbrev SeedVal
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper 1 0))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    (v' : (divisionTower (1 : ℝ) n).carrier) (d : D.carrier) : Prop :=
  e.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
        (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v')
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d

variable
  (e : SuperAlgEquiv
    ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
    (D.matrixSuper 1 0))
  (u' : (divisionTower (-1 : ℝ) m).carrier)

private theorem P00 {β : ZMod 2}
    {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {d : D.carrier}
    (hseed : SeedVal e u' v' d) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = (tailEquiv D 1 0).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper 1 0).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
            (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)) := by
  refine (peel_q00 e u' hv').trans ?_
  exact congrArg (fun M => (tailEquiv D 1 0).toAlgEquiv
    (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper 1 0).grading)
      (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
      (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier))) hseed

private theorem P01 {β : ZMod 2}
    {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {d : D.carrier} (hseed : SeedVal e u' v' d) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = (tailEquiv D 1 0).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper 1 0).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
            hypF') := by
  refine (peel_q01 e u' hv').trans ?_
  exact congrArg (fun M => (tailEquiv D 1 0).toAlgEquiv
    (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper 1 0).grading)
      (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
      hypF')) hseed

private theorem P10 {β : ZMod 2}
    {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {d : D.carrier} (hseed : SeedVal e u' v' d) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = ((sgn β : ℤˣ) : ℤ) • (tailEquiv D 1 0).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper 1 0).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
            hypE') := by
  refine (peel_q10 e u' hv').trans ?_
  exact congrArg (fun M => ((sgn β : ℤˣ) : ℤ) •
    (tailEquiv D 1 0).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper 1 0).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
        hypE')) hseed

private theorem P11 {β : ZMod 2}
    {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {d : D.carrier} (hseed : SeedVal e u' v' d) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = ((sgn β : ℤˣ) : ℤ) • (tailEquiv D 1 0).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper 1 0).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
            (hypE' * hypF')) := by
  refine (peel_q11 e u' hv').trans ?_
  exact congrArg (fun M => ((sgn β : ℤˣ) : ℤ) •
    (tailEquiv D 1 0).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper 1 0).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
        (hypE' * hypF'))) hseed

/-- Tail values at `p = 1`, `q = 0` (all block parities vanish, so the
inner degree is exactly the entry's degree). -/
private theorem T10_one_even {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 0) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
          (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier))
      = Matrix.single (Sum.inl 0) (Sum.inl 0) d
        + Matrix.single (Sum.inr 0) (Sum.inr 0) d :=
  tail_one_even D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

private theorem T10_one_odd {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 1) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
          (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier))
      = Matrix.single (Sum.inl 0) (Sum.inl 0) d
        - Matrix.single (Sum.inr 0) (Sum.inr 0) d :=
  tail_one_odd D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

private theorem T10_F_even {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 0) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d) hypF')
      = Matrix.single (Sum.inl 0) (Sum.inr 0) d
        + Matrix.single (Sum.inr 0) (Sum.inl 0) d :=
  tail_F_even D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

private theorem T10_F_odd {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 1) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d) hypF')
      = Matrix.single (Sum.inl 0) (Sum.inr 0) d
        - Matrix.single (Sum.inr 0) (Sum.inl 0) d :=
  tail_F_odd D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

private theorem T10_E_even {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 0) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d) hypE')
      = Matrix.single (Sum.inl 0) (Sum.inr 0) d
        - Matrix.single (Sum.inr 0) (Sum.inl 0) d :=
  tail_E_even D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

private theorem T10_E_odd {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 1) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d) hypE')
      = Matrix.single (Sum.inl 0) (Sum.inr 0) d
        + Matrix.single (Sum.inr 0) (Sum.inl 0) d :=
  tail_E_odd D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

private theorem T10_EF_even {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 0) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
          (hypE' * hypF'))
      = Matrix.single (Sum.inl 0) (Sum.inl 0) d
        - Matrix.single (Sum.inr 0) (Sum.inr 0) d :=
  tail_EF_even D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

private theorem T10_EF_odd {δ : ZMod 2} {d : D.carrier}
    (hd : d ∈ D.grading δ) (hδ : δ = 1) :
    (tailEquiv D 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper 1 0).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) d)
          (hypE' * hypF'))
      = Matrix.single (Sum.inl 0) (Sum.inl 0) d
        + Matrix.single (Sum.inr 0) (Sum.inr 0) d :=
  tail_EF_odd D 1 0 hd (Sum.inl 0) (Sum.inl 0) (by rw [hδ]; rfl)

end Seed10

/-! ### General-seed peel columns (arbitrary `p|q`) -/

private theorem add_gtmulG {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A]
    [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra ℬ] (x x' : A) (y : B) :
    ((x + x') ᵍ⊗ₜ[ℝ] y : 𝒜 ᵍ⊗[ℝ] ℬ) = x ᵍ⊗ₜ[ℝ] y + x' ᵍ⊗ₜ[ℝ] y := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ ((x + x') ⊗ₜ[ℝ] y)
      = GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] y)
        + GradedTensorProduct.of ℝ 𝒜 ℬ (x' ⊗ₜ[ℝ] y)
  rw [← map_add, TensorProduct.add_tmul]

private theorem sub_gtmulG {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A]
    [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra ℬ] (x x' : A) (y : B) :
    ((x - x') ᵍ⊗ₜ[ℝ] y : 𝒜 ᵍ⊗[ℝ] ℬ) = x ᵍ⊗ₜ[ℝ] y - x' ᵍ⊗ₜ[ℝ] y := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ ((x - x') ⊗ₜ[ℝ] y)
      = GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] y)
        - GradedTensorProduct.of ℝ 𝒜 ℬ (x' ⊗ₜ[ℝ] y)
  rw [← map_sub, TensorProduct.sub_tmul]

/-- Split the tail along an additive decomposition of the matrix factor. -/
private theorem tail_decL_add (D : SuperAlgebra ℝ) (p q : ℕ)
    (M₁ M₂ : (D.matrixSuper p q).carrier)
    (W : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (M₁ + M₂) W)
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            M₁ W)
        + (tailEquiv D p q).toAlgEquiv
            (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            M₂ W) := by
  have hd : (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ (M₁ + M₂) W
      : ((D.matrixSuper p q).gtensor
          ((SuperAlgebra.base ℝ).matrixSuper 1 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M₁ W
        + GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M₂ W :=
    add_gtmulG _ _ _ _ _
  rw [hd]
  exact map_add _ _ _

/-- Split the tail along a subtractive decomposition of the matrix factor. -/
private theorem tail_decL_sub (D : SuperAlgebra ℝ) (p q : ℕ)
    (M₁ M₂ : (D.matrixSuper p q).carrier)
    (W : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            (M₁ - M₂) W)
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            M₁ W)
        - (tailEquiv D p q).toAlgEquiv
            (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ
            M₂ W) := by
  have hd : (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ (M₁ - M₂) W
      : ((D.matrixSuper p q).gtensor
          ((SuperAlgebra.base ℝ).matrixSuper 1 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M₁ W
        - GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M₂ W :=
    sub_gtmulG _ _ _ _ _
  rw [hd]
  exact map_sub _ _ _

private theorem PG00 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {M : (D.matrixSuper p q).carrier}
    (hseed : e.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
          (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v') = M) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
            (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)) := by
  refine (peel_q00 e u' hv').trans ?_
  exact congrArg (fun N => (tailEquiv D p q).toAlgEquiv
    (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
      (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ N
      (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier))) hseed

private theorem PG01 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {M : (D.matrixSuper p q).carrier}
    (hseed : e.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
          (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v') = M) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) u' 0)
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
            hypF') := by
  refine (peel_q01 e u' hv').trans ?_
  exact congrArg (fun N => (tailEquiv D p q).toAlgEquiv
    (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
      (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ N
      hypF')) hseed

private theorem PG10 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {M : (D.matrixSuper p q).carrier}
    (hseed : e.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
          (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v') = M) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) v' 0))
      = ((sgn β : ℤˣ) : ℤ) • (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
            hypE') := by
  refine (peel_q10 e u' hv').trans ?_
  exact congrArg (fun N => ((sgn β : ℤˣ) : ℤ) • (tailEquiv D p q).toAlgEquiv
    (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
      (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ N
      hypE')) hseed

private theorem PG11 {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv
      ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q))
    (u' : (divisionTower (-1 : ℝ) m).carrier)
    {β : ZMod 2} {v' : (divisionTower (1 : ℝ) n).carrier}
    (hv' : v' ∈ (divisionTower (1 : ℝ) n).grading β)
    {M : (D.matrixSuper p q).carrier}
    (hseed : e.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) m).grading)
          (ℬ := (divisionTower (1 : ℝ) n).grading) ℝ u' v') = M) :
    (peelFuse e).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (divisionTower (-1 : ℝ) (m + 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) (n + 1)).grading) ℝ
          (OddDouble.mk (divisionTower (-1 : ℝ) m).grading (-1 : ℝ) 0 u')
          (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 v'))
      = ((sgn β : ℤˣ) : ℤ) • (tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M
            (hypE' * hypF')) := by
  refine (peel_q11 e u' hv').trans ?_
  exact congrArg (fun N => ((sgn β : ℤˣ) : ℤ) • (tailEquiv D p q).toAlgEquiv
    (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
      (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ N
      (hypE' * hypF'))) hseed

private theorem F_ppp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A + B) + (C + D)
      = (1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem F_ppm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A + B) + (C - D)
      = (1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem F_pmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A - B) + (C + D)
      = (1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem F_pmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A - B) + (C - D)
      = (1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem F_mpp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A + B) - (C + D)
      = (1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem F_mpm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A + B) - (C - D)
      = (1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem F_mmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A - B) - (C + D)
      = (1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem F_mmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    (A - B) - (C - D)
      = (1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_ppp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) + (C + D))
      = (1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_ppm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) + (C - D))
      = (1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_pmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) + (C + D))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_pmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) + (C - D))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_mpp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) - (C + D))
      = (1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_mpm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) - (C - D))
      = (1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_mmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) - (C + D))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem H_mmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) - (C - D))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_ppp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) + (C + D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_ppm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) + (C - D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_pmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) + (C + D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_pmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) + (C - D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_mpp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) - (C + D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_mpm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A + B) - (C - D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_mmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) - (C + D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem G_mmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • ((A - B) - (C - D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem four_smul_congr {M : Type*} [AddCommGroup M] [Module ℝ M]
    (a b c d : ℝ) {X X' Y Y' Z Z' W W' : M}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (hW : W = W') :
    a • X + b • Y + c • Z + d • W = a • X' + b • Y' + c • Z' + d • W' := by
  rw [hX, hY, hZ, hW]

/-- The singleton basis of the base algebra, typed at the bundled
carrier (the pilot's `baseBasis`). -/
private noncomputable def baseBasis :
    Basis (Fin 1) ℝ (SuperAlgebra.base ℝ).carrier :=
  Basis.singleton (Fin 1) ℝ

private theorem baseBasis_apply (i : Fin 1) : baseBasis i = (1 : ℝ) :=
  Basis.singleton_apply (Fin 1) ℝ i

private theorem mem_base_one :
    (1 : (SuperAlgebra.base ℝ).carrier) ∈ (SuperAlgebra.base ℝ).grading 0 :=
  mem_evenGrading_zero ℝ ℝ 1


/-! ### Negation and de-scaling helpers for multi-term seeds -/

private theorem neg_congr {M : Type*} [AddCommGroup M] {X Y : M}
    (h : X = Y) : -X = -Y := by rw [h]

private theorem tail_decL_neg (D : SuperAlgebra ℝ) (p q : ℕ)
    (M : (D.matrixSuper p q).carrier)
    (W : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier) :
    (tailEquiv D p q).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (D.matrixSuper p q).grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ (-M) W)
      = -(tailEquiv D p q).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W) := by
  have hd : (GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
        (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ (-M) W
      : ((D.matrixSuper p q).gtensor
          ((SuperAlgebra.base ℝ).matrixSuper 1 1)).carrier)
      = -GradedTensorProduct.tmul (𝒜 := (D.matrixSuper p q).grading)
            (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ M W := by
    have h0 := sub_gtmulG (D.matrixSuper p q).grading
      ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading (0 : (D.matrixSuper p q).carrier) M W
    rw [zero_sub, zero_gtmul, zero_sub] at h0
    exact h0
  rw [hd]
  exact map_neg _ _

private theorem unsmul_pp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) : (1 : ℝ) • X + (1 : ℝ) • Y = X + Y := by
  rw [one_smul, one_smul]

private theorem unsmul_pm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) : (1 : ℝ) • X + (-1 : ℝ) • Y = X - Y := by
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg]

private theorem unsmul_mm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) : (-1 : ℝ) • X + (-1 : ℝ) • Y = -(X + Y) := by
  rw [neg_one_smul, neg_one_smul, ← neg_add]

private theorem unsmul_mp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (X Y : M) : (-1 : ℝ) • X + (1 : ℝ) • Y = -(X - Y) := by
  rw [neg_one_smul, one_smul, neg_sub]
  abel


private theorem N_ppp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A + B) + (C + D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem N_ppm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A + B) + (C - D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem N_pmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A - B) + (C + D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem N_pmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A - B) + (C - D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem N_mpp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A + B) - (C + D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem N_mpm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A + B) - (C - D))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem N_mmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A - B) - (C + D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem N_mmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    -((A - B) - (C - D))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_ppp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) + (C + D)))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_ppm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) + (C - D)))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_pmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) + (C + D)))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_pmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) + (C - D)))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_mpp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) - (C + D)))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_mpm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) - (C - D)))
      = (-1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_mmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) - (C + D)))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem MM_mmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) - (C - D)))
      = (-1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_zero, Units.val_one, one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_ppp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) + (C + D)))
      = (1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_ppm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) + (C - D)))
      = (1 : ℝ) • A + (1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_pmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) + (C + D)))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_pmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) + (C - D)))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_mpp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) - (C + D)))
      = (1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_mpm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A + B) - (C - D)))
      = (1 : ℝ) • A + (1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_mmp {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) - (C + D)))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (-1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

private theorem KK_mmm {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A B C D : M) :
    ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • (-((A - B) - (C - D)))
      = (1 : ℝ) • A + (-1 : ℝ) • B + (-1 : ℝ) • C + (1 : ℝ) • D := by
  rw [sgn_one, units_sign_eq, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
    neg_one_zsmul]
  simp only [one_smul, neg_one_smul]
  abel

/-! ### The two base seeds -/

private theorem baseFuseL_val (n : ℕ) {jv : ZMod 2}
    {v : (divisionTower (1 : ℝ) n).carrier}
    (hv : v ∈ (divisionTower (1 : ℝ) n).grading jv) :
    SeedVal (baseFuseL n) (1 : (divisionTower (-1 : ℝ) 0).carrier) v v :=
  unitorL_single (divisionTower (1 : ℝ) n) hv

private theorem baseFuseR_val (m : ℕ) (v : (divisionTower (-1 : ℝ) m).carrier) :
    SeedVal (baseFuseR m) v (1 : (divisionTower (1 : ℝ) 0).carrier) v :=
  unitorR_single (divisionTower (-1 : ℝ) m) v

/-! ### Tower-basis dictionary in `mk` form -/

private theorem tb1_0 (ε : ℝ) :
    towerBasis ε 1 0
      = OddDouble.mk (divisionTower ε 0).grading ε (1 : ℝ) 0 := by
  have h := towerBasis_low ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

private theorem tb1_1 (ε : ℝ) :
    towerBasis ε 1 1
      = OddDouble.mk (divisionTower ε 0).grading ε 0 (1 : ℝ) := by
  have h := towerBasis_high ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

private theorem tb2_0 (ε : ℝ) :
    towerBasis ε 2 0
      = OddDouble.mk (divisionTower ε 1).grading ε (towerBasis ε 1 0) 0 :=
  towerBasis_low ε 1 0

private theorem tb2_1 (ε : ℝ) :
    towerBasis ε 2 1
      = OddDouble.mk (divisionTower ε 1).grading ε (towerBasis ε 1 1) 0 :=
  towerBasis_low ε 1 1

private theorem tb2_2 (ε : ℝ) :
    towerBasis ε 2 2
      = OddDouble.mk (divisionTower ε 1).grading ε 0 (towerBasis ε 1 0) :=
  towerBasis_high ε 1 0

private theorem tb2_3 (ε : ℝ) :
    towerBasis ε 2 3
      = OddDouble.mk (divisionTower ε 1).grading ε 0 (towerBasis ε 1 1) :=
  towerBasis_high ε 1 1

private theorem tb3_0 (ε : ℝ) :
    towerBasis ε 3 0
      = OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 0) 0 :=
  towerBasis_low ε 2 0

private theorem tb3_1 (ε : ℝ) :
    towerBasis ε 3 1
      = OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 1) 0 :=
  towerBasis_low ε 2 1

private theorem tb3_2 (ε : ℝ) :
    towerBasis ε 3 2
      = OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 2) 0 :=
  towerBasis_low ε 2 2

private theorem tb3_3 (ε : ℝ) :
    towerBasis ε 3 3
      = OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 3) 0 :=
  towerBasis_low ε 2 3

private theorem tb3_4 (ε : ℝ) :
    towerBasis ε 3 4
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 0) :=
  towerBasis_high ε 2 0

private theorem tb3_5 (ε : ℝ) :
    towerBasis ε 3 5
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 1) :=
  towerBasis_high ε 2 1

private theorem tb3_6 (ε : ℝ) :
    towerBasis ε 3 6
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 2) :=
  towerBasis_high ε 2 2

private theorem tb3_7 (ε : ℝ) :
    towerBasis ε 3 7
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 3) :=
  towerBasis_high ε 2 3

/-! ### Concrete parities of the tower frames -/

private theorem tb1_mem0 (ε : ℝ) :
    towerBasis ε 1 0 ∈ (divisionTower ε 1).grading 0 :=
  towerBasis_mem ε 1 0

private theorem tb1_mem1 (ε : ℝ) :
    towerBasis ε 1 1 ∈ (divisionTower ε 1).grading 1 :=
  towerBasis_mem ε 1 1

private theorem tb2_mem0 (ε : ℝ) :
    towerBasis ε 2 0 ∈ (divisionTower ε 2).grading 0 :=
  towerBasis_mem ε 2 0

private theorem tb2_mem1 (ε : ℝ) :
    towerBasis ε 2 1 ∈ (divisionTower ε 2).grading 1 :=
  towerBasis_mem ε 2 1

private theorem tb2_mem2 (ε : ℝ) :
    towerBasis ε 2 2 ∈ (divisionTower ε 2).grading 1 :=
  towerBasis_mem ε 2 2

private theorem tb2_mem3 (ε : ℝ) :
    towerBasis ε 2 3 ∈ (divisionTower ε 2).grading 0 :=
  towerBasis_mem ε 2 3

private theorem one_mem_T0 :
    (1 : (divisionTower (1 : ℝ) 0).carrier)
      ∈ (divisionTower (1 : ℝ) 0).grading 0 :=
  SetLike.one_mem_graded _

/-- Coefficientwise congruence for a two-term expansion. -/
private theorem two_smul_congr {M : Type*} [AddCommGroup M] [Module ℝ M]
    (a b : ℝ) {X X' Y Y' : M} (hX : X = X') (hY : Y = Y') :
    a • X + b • Y = a • X' + b • Y' := by rw [hX, hY]

/-! ### Branch `(1,6)`: `Cl_{0,1} ᵍ⊗ Cl_{2,0} ≅ M_{1|1}(Cl_{1,0})`

`realFuse 1 6 = peelFuse (baseFuseL 1)`: `m = 0`, `n = 1`, `p = 1`,
`q = 0`, `D = T⁺₁`. -/

private theorem d16_0 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (1 : ℝ) 1 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 0 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inl 0) (Sum.inl 0) 0).symm
private theorem d16_1 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (1 : ℝ) 1 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 1 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inl 0) (Sum.inl 0) 1).symm
private theorem d16_2 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (1 : ℝ) 1 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 2 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inl 0) (Sum.inr 0) 0).symm
private theorem d16_3 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (1 : ℝ) 1 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 3 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inl 0) (Sum.inr 0) 1).symm
private theorem d16_4 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (1 : ℝ) 1 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 4 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inr 0) (Sum.inl 0) 0).symm
private theorem d16_5 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (1 : ℝ) 1 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 5 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inr 0) (Sum.inl 0) 1).symm
private theorem d16_6 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (1 : ℝ) 1 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 6 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inr 0) (Sum.inr 0) 0).symm
private theorem d16_7 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (1 : ℝ) 1 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 7 :=
  (matrixSuperBasis_apply_pair (towerBasis (1 : ℝ) 1) 1 1 (Sum.inr 0) (Sum.inr 0) 1).symm

private theorem c16_0 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 0)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 0
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 0 0
  rw [tb1_0, tb2_0] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem0 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem0 (1 : ℝ)))).trans ?_
  refine (T10_one_even (tb1_mem0 (1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d16_0 d16_6)

private theorem c16_1 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 1)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 0 1
  rw [tb1_0, tb2_1] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem1 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem1 (1 : ℝ)))).trans ?_
  refine (T10_one_odd (tb1_mem1 (1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d16_1 d16_7)

private theorem c16_2 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 2)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 2
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 0 2
  rw [tb1_0, tb2_2] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem0 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem0 (1 : ℝ)))).trans ?_
  refine (T10_F_even (tb1_mem0 (1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d16_2 d16_4)

private theorem c16_3 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 3)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 3
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 0 3
  rw [tb1_0, tb2_3] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem1 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem1 (1 : ℝ)))).trans ?_
  refine (T10_F_odd (tb1_mem1 (1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d16_3 d16_5)

private theorem c16_4 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 4)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 1 0
  rw [tb1_1, tb2_0] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem0 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem0 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_even (tb1_mem0 (1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d16_2 d16_4)

private theorem c16_5 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 5)
      = (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 3
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 1 1
  rw [tb1_1, tb2_1] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem1 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem1 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_odd (tb1_mem1 (1 : ℝ)) rfl)).trans ?_
  exact (zneg_pair_add _ _).trans
    (two_smul_congr (-1) (-1) d16_3 d16_5)

private theorem c16_6 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 6)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 0
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 1 2
  rw [tb1_1, tb2_2] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem0 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem0 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_even (tb1_mem0 (1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d16_0 d16_6)

private theorem c16_7 :
    (peelFuse (baseFuseL 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 1) (towerBasis 1 2) 7)
      = (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 2) 1 3
  rw [tb1_1, tb2_3] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseL 1) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb1_mem1 (1 : ℝ)) (baseFuseL_val 1 (tb1_mem1 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_odd (tb1_mem1 (1 : ℝ)) rfl)).trans ?_
  exact (zneg_pair_add _ _).trans
    (two_smul_congr (-1) (-1) d16_1 d16_7)

/-- **Deliverable `(1,6)`**. -/
theorem realFuseMatrix_1_6 :
    realFuseMatrix 1 6 =
  !![1, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, -1;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, -1, 0, 0;
    0, 0, 1, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, -1, 0, 0;
    1, 0, 0, 0, 0, 0, -1, 0;
    0, -1, 0, 0, 0, 0, 0, -1] := by
  have hcol : ∀ j : Fin 8,
      (peelFuse (baseFuseL 1)).toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
            (B := divisionTower (1 : ℝ) 2)
            (towerBasis (-1) 1) (towerBasis 1 2) j)
        = (![1, 1, 1, 1, 1, -1, 1, -1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (1 : ℝ) 1)
                  (towerBasis 1 1) 1 1 (![0, 1, 2, 3, 2, 3, 0, 1] j)
          + (![1, -1, 1, -1, -1, -1, -1, -1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (1 : ℝ) 1)
                  (towerBasis 1 1) 1 1 (![6, 7, 4, 5, 4, 5, 6, 7] j) := by
    intro j
    fin_cases j
    · exact c16_0
    · exact c16_1
    · exact c16_2
    · exact c16_3
    · exact c16_4
    · exact c16_5
    · exact c16_6
    · exact c16_7
  show LinearMap.toMatrix
      (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis (-1) 1) (towerBasis 1 2))
      (matrixSuperBasis (P := divisionTower (1 : ℝ) 1) (towerBasis 1 1) 1 1)
      ((peelFuse (baseFuseL 1)).toAlgEquiv.toLinearMap)
    =
  !![1, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, -1;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, -1, 0, 0;
    0, 0, 1, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, -1, 0, 0;
    1, 0, 0, 0, 0, 0, -1, 0;
    0, -1, 0, 0, 0, 0, 0, -1]
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j, map_add,
    map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]

/-! ### Branch `(2,7)`

`realFuse 2 7 = peelFuse (baseFuseR 1)`: `m = 1`, `n = 0`,
`p = 1`, `q = 0`. -/

private theorem d2_7_0 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 1 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 0 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inl 0) (Sum.inl 0) 0).symm

private theorem d2_7_1 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 1 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 1 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inl 0) (Sum.inl 0) 1).symm

private theorem d2_7_2 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 1 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 2 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inl 0) (Sum.inr 0) 0).symm

private theorem d2_7_3 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 1 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 3 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inl 0) (Sum.inr 0) 1).symm

private theorem d2_7_4 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 1 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 4 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inr 0) (Sum.inl 0) 0).symm

private theorem d2_7_5 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 1 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 5 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inr 0) (Sum.inl 0) 1).symm

private theorem d2_7_6 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 1 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 6 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inr 0) (Sum.inr 0) 0).symm

private theorem d2_7_7 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 1 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 7 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 1) 1 1 (Sum.inr 0) (Sum.inr 0) 1).symm

private theorem c2_7_0 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 0)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 0
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 0 0
  rw [tb2_0 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 0)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 0))).trans ?_
  refine (T10_one_even (tb1_mem0 (-1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d2_7_0 d2_7_6)

private theorem c2_7_1 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 1)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 2
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 0 1
  rw [tb2_0 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 0)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 0))).trans ?_
  refine (T10_F_even (tb1_mem0 (-1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d2_7_2 d2_7_4)

private theorem c2_7_2 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 2)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 1 0
  rw [tb2_1 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 1)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 1))).trans ?_
  refine (T10_one_odd (tb1_mem1 (-1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d2_7_1 d2_7_7)

private theorem c2_7_3 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 3)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 3
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 1 1
  rw [tb2_1 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 1)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 1))).trans ?_
  refine (T10_F_odd (tb1_mem1 (-1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d2_7_3 d2_7_5)

private theorem c2_7_4 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 4)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 2 0
  rw [tb2_2 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 0)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 0))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_even (tb1_mem0 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d2_7_2 d2_7_4)

private theorem c2_7_5 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 5)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 0
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 2 1
  rw [tb2_2 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 0)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 0))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_even (tb1_mem0 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d2_7_0 d2_7_6)

private theorem c2_7_6 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 6)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 3
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 3 0
  rw [tb2_3 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 1)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 1))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_odd (tb1_mem1 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_add _ _).trans
    (two_smul_congr (1) (1) d2_7_3 d2_7_5)

private theorem c2_7_7 :
    (peelFuse (baseFuseR 1)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 7)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 1
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 1) 3 1
  rw [tb2_3 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseR 1) (towerBasis (-1 : ℝ) 1 1)
      one_mem_T0 (baseFuseR_val 1 (towerBasis (-1 : ℝ) 1 1))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_odd (tb1_mem1 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_add _ _).trans
    (two_smul_congr (1) (1) d2_7_1 d2_7_7)

/-- **Deliverable `(2,7)`**. -/
theorem realFuseMatrix_2_7 :
    realFuseMatrix 2 7 =
  !![1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 1, 0;
    0, 1, 0, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 1, 0;
    1, 0, 0, 0, 0, -1, 0, 0;
    0, 0, -1, 0, 0, 0, 0, 1] := by
  have hcol : ∀ j : Fin 8,
      (peelFuse (baseFuseR 1)).toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1) j)
        = (![1, 1, 1, 1, 1, 1, 1, 1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 (![0, 2, 1, 3, 2, 0, 3, 1] j)
          + (![1, 1, -1, -1, -1, -1, 1, 1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1 (![6, 4, 7, 5, 4, 6, 5, 7] j) := by
    intro j
    fin_cases j
    · exact c2_7_0
    · exact c2_7_1
    · exact c2_7_2
    · exact c2_7_3
    · exact c2_7_4
    · exact c2_7_5
    · exact c2_7_6
    · exact c2_7_7
  show LinearMap.toMatrix
      (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 2) (towerBasis 1 1))
      (matrixSuperBasis (P := divisionTower (-1 : ℝ) 1) (towerBasis (-1) 1) 1 1)
      ((peelFuse (baseFuseR 1)).toAlgEquiv.toLinearMap)
    =
  !![1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 1, 0;
    0, 1, 0, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 1, 0;
    1, 0, 0, 0, 0, -1, 0, 0;
    0, 0, -1, 0, 0, 0, 0, 1]
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j, map_add,
    map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]


/-! ### Branch `(1,5)`

`realFuse 1 5 = peelFuse (baseFuseL 2)`: `m = 0`, `n = 2`,
`p = 1`, `q = 0`. -/

private theorem d1_5_0 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 0 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inl 0) 0).symm

private theorem d1_5_1 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 1 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inl 0) 1).symm

private theorem d1_5_2 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 2)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 2 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inl 0) 2).symm

private theorem d1_5_3 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 3)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 3 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inl 0) 3).symm

private theorem d1_5_4 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 4 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inr 0) 0).symm

private theorem d1_5_5 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 5 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inr 0) 1).symm

private theorem d1_5_6 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 2)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 6 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inr 0) 2).symm

private theorem d1_5_7 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 3)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 7 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inl 0) (Sum.inr 0) 3).symm

private theorem d1_5_8 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 8 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inl 0) 0).symm

private theorem d1_5_9 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 9 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inl 0) 1).symm

private theorem d1_5_10 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 2)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 10 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inl 0) 2).symm

private theorem d1_5_11 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis 1 2 3)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 11 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inl 0) 3).symm

private theorem d1_5_12 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 0)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 12 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inr 0) 0).symm

private theorem d1_5_13 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 1)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 13 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inr 0) 1).symm

private theorem d1_5_14 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 2)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 14 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inr 0) 2).symm

private theorem d1_5_15 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis 1 2 3)
      = matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 15 :=
  (matrixSuperBasis_apply_pair (towerBasis 1 2) 1 1 (Sum.inr 0) (Sum.inr 0) 3).symm

private theorem c1_5_0 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 0)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 0
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 0
  rw [tb1_0 (-1 : ℝ), tb3_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem0 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem0 (1 : ℝ)))).trans ?_
  refine (T10_one_even (tb2_mem0 (1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d1_5_0 d1_5_12)

private theorem c1_5_1 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 1)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 1
  rw [tb1_0 (-1 : ℝ), tb3_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem1 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem1 (1 : ℝ)))).trans ?_
  refine (T10_one_odd (tb2_mem1 (1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_1 d1_5_13)

private theorem c1_5_2 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 2)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 2
  rw [tb1_0 (-1 : ℝ), tb3_2 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem2 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem2 (1 : ℝ)))).trans ?_
  refine (T10_one_odd (tb2_mem2 (1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_2 d1_5_14)

private theorem c1_5_3 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 3)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 3
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 3
  rw [tb1_0 (-1 : ℝ), tb3_3 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem3 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem3 (1 : ℝ)))).trans ?_
  refine (T10_one_even (tb2_mem3 (1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d1_5_3 d1_5_15)

private theorem c1_5_4 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 4)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 4
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 4) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 4
  rw [tb1_0 (-1 : ℝ), tb3_4 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem0 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem0 (1 : ℝ)))).trans ?_
  refine (T10_F_even (tb2_mem0 (1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d1_5_4 d1_5_8)

private theorem c1_5_5 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 5)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 5
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 5) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 5
  rw [tb1_0 (-1 : ℝ), tb3_5 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem1 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem1 (1 : ℝ)))).trans ?_
  refine (T10_F_odd (tb2_mem1 (1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_5 d1_5_9)

private theorem c1_5_6 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 6)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 6
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 6) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 6
  rw [tb1_0 (-1 : ℝ), tb3_6 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem2 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem2 (1 : ℝ)))).trans ?_
  refine (T10_F_odd (tb2_mem2 (1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_6 d1_5_10)

private theorem c1_5_7 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 7)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 7
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 3 7) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 0 7
  rw [tb1_0 (-1 : ℝ), tb3_7 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem3 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem3 (1 : ℝ)))).trans ?_
  refine (T10_F_even (tb2_mem3 (1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d1_5_7 d1_5_11)

private theorem c1_5_8 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 8)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 4
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 8
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 0
  rw [tb1_1 (-1 : ℝ), tb3_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem0 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem0 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_even (tb2_mem0 (1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_4 d1_5_8)

private theorem c1_5_9 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 9)
      = (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 5
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 9
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 1
  rw [tb1_1 (-1 : ℝ), tb3_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem1 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem1 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_odd (tb2_mem1 (1 : ℝ)) rfl)).trans ?_
  exact (zneg_pair_add _ _).trans
    (two_smul_congr (-1) (-1) d1_5_5 d1_5_9)

private theorem c1_5_10 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 10)
      = (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 6
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 10
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 2
  rw [tb1_1 (-1 : ℝ), tb3_2 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem2 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem2 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_odd (tb2_mem2 (1 : ℝ)) rfl)).trans ?_
  exact (zneg_pair_add _ _).trans
    (two_smul_congr (-1) (-1) d1_5_6 d1_5_10)

private theorem c1_5_11 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 11)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 7
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 11
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 3
  rw [tb1_1 (-1 : ℝ), tb3_3 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem3 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem3 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_even (tb2_mem3 (1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_7 d1_5_11)

private theorem c1_5_12 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 12)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 0
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 12
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 4) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 4
  rw [tb1_1 (-1 : ℝ), tb3_4 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem0 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem0 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_even (tb2_mem0 (1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_0 d1_5_12)

private theorem c1_5_13 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 13)
      = (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 13
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 5) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 5
  rw [tb1_1 (-1 : ℝ), tb3_5 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem1 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem1 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_odd (tb2_mem1 (1 : ℝ)) rfl)).trans ?_
  exact (zneg_pair_add _ _).trans
    (two_smul_congr (-1) (-1) d1_5_1 d1_5_13)

private theorem c1_5_14 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 14)
      = (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 14
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 6) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 6
  rw [tb1_1 (-1 : ℝ), tb3_6 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem2 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem2 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_odd (tb2_mem2 (1 : ℝ)) rfl)).trans ?_
  exact (zneg_pair_add _ _).trans
    (two_smul_congr (-1) (-1) d1_5_2 d1_5_14)

private theorem c1_5_15 :
    (peelFuse (baseFuseL 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 15)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 3
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) 15
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 3 7) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3) 1 7
  rw [tb1_1 (-1 : ℝ), tb3_7 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseL 2) (1 : (divisionTower (-1 : ℝ) 0).carrier)
      (tb2_mem3 (1 : ℝ)) (baseFuseL_val 2 (tb2_mem3 (1 : ℝ)))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_even (tb2_mem3 (1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d1_5_3 d1_5_15)

/-- **Deliverable `(1,5)`**. -/
theorem realFuseMatrix_1_5 :
    realFuseMatrix 1 5 =
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
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
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by
  have hcol : ∀ j : Fin 16,
      (peelFuse (baseFuseL 2)).toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3) j)
        = (![1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 (![0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 0, 1, 2, 3] j)
          + (![1, -1, -1, 1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1 (![12, 13, 14, 15, 8, 9, 10, 11, 8, 9, 10, 11, 12, 13, 14, 15] j) := by
    intro j
    fin_cases j
    · exact c1_5_0
    · exact c1_5_1
    · exact c1_5_2
    · exact c1_5_3
    · exact c1_5_4
    · exact c1_5_5
    · exact c1_5_6
    · exact c1_5_7
    · exact c1_5_8
    · exact c1_5_9
    · exact c1_5_10
    · exact c1_5_11
    · exact c1_5_12
    · exact c1_5_13
    · exact c1_5_14
    · exact c1_5_15
  show LinearMap.toMatrix
      (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (-1) 1) (towerBasis 1 3))
      (matrixSuperBasis (P := divisionTower (1 : ℝ) 2) (towerBasis 1 2) 1 1)
      ((peelFuse (baseFuseL 2)).toAlgEquiv.toLinearMap)
    =
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
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
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j, map_add,
    map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]


/-! ### Branch `(3,7)`

`realFuse 3 7 = peelFuse (baseFuseR 2)`: `m = 2`, `n = 0`,
`p = 1`, `q = 0`. -/

private theorem d3_7_0 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 0 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inl 0) 0).symm

private theorem d3_7_1 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 1 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inl 0) 1).symm

private theorem d3_7_2 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 2)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 2 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inl 0) 2).symm

private theorem d3_7_3 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 3)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 3 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inl 0) 3).symm

private theorem d3_7_4 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 4 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inr 0) 0).symm

private theorem d3_7_5 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 5 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inr 0) 1).symm

private theorem d3_7_6 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 2)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 6 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inr 0) 2).symm

private theorem d3_7_7 :
    Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 3)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 7 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inl 0) (Sum.inr 0) 3).symm

private theorem d3_7_8 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 8 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inl 0) 0).symm

private theorem d3_7_9 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 9 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inl 0) 1).symm

private theorem d3_7_10 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 2)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 10 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inl 0) 2).symm

private theorem d3_7_11 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis (-1) 2 3)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 11 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inl 0) 3).symm

private theorem d3_7_12 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 0)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 12 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inr 0) 0).symm

private theorem d3_7_13 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 1)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 13 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inr 0) 1).symm

private theorem d3_7_14 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 2)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 14 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inr 0) 2).symm

private theorem d3_7_15 :
    Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis (-1) 2 3)
      = matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 15 :=
  (matrixSuperBasis_apply_pair (towerBasis (-1) 2) 1 1 (Sum.inr 0) (Sum.inr 0) 3).symm

private theorem c3_7_0 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 0)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 0
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 0) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 0 0
  rw [tb3_0 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 0)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 0))).trans ?_
  refine (T10_one_even (tb2_mem0 (-1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_0 d3_7_12)

private theorem c3_7_1 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 1)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 4
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 0) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 0 1
  rw [tb3_0 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 0)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 0))).trans ?_
  refine (T10_F_even (tb2_mem0 (-1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_4 d3_7_8)

private theorem c3_7_2 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 2)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 1) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 1 0
  rw [tb3_1 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 1)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 1))).trans ?_
  refine (T10_one_odd (tb2_mem1 (-1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_1 d3_7_13)

private theorem c3_7_3 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 3)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 5
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 1) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 1 1
  rw [tb3_1 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 1)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 1))).trans ?_
  refine (T10_F_odd (tb2_mem1 (-1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_5 d3_7_9)

private theorem c3_7_4 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 4)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 2) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 2 0
  rw [tb3_2 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 2)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 2))).trans ?_
  refine (T10_one_odd (tb2_mem2 (-1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_2 d3_7_14)

private theorem c3_7_5 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 5)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 6
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 2) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 2 1
  rw [tb3_2 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 2)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 2))).trans ?_
  refine (T10_F_odd (tb2_mem2 (-1 : ℝ)) rfl).trans ?_
  exact (pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_6 d3_7_10)

private theorem c3_7_6 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 6)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 3
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 3) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 3 0
  rw [tb3_3 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P00 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 3)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 3))).trans ?_
  refine (T10_one_even (tb2_mem3 (-1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_3 d3_7_15)

private theorem c3_7_7 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 7)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 7
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 3) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 3 1
  rw [tb3_3 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P01 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 3)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 3))).trans ?_
  refine (T10_F_even (tb2_mem3 (-1 : ℝ)) rfl).trans ?_
  exact (pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_7 d3_7_11)

private theorem c3_7_8 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 8)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 4
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 8
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 4) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 4 0
  rw [tb3_4 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 0)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 0))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_even (tb2_mem0 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_4 d3_7_8)

private theorem c3_7_9 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 9)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 0
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 9
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 4) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 4 1
  rw [tb3_4 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 0)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 0))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_even (tb2_mem0 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_0 d3_7_12)

private theorem c3_7_10 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 10)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 5
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 10
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 5) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 5 0
  rw [tb3_5 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 1)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 1))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_odd (tb2_mem1 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_5 d3_7_9)

private theorem c3_7_11 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 11)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 1
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 11
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 5) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 5 1
  rw [tb3_5 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 1)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 1))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_odd (tb2_mem1 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_1 d3_7_13)

private theorem c3_7_12 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 12)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 6
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 12
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 6) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 6 0
  rw [tb3_6 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 2)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 2))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_odd (tb2_mem2 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_6 d3_7_10)

private theorem c3_7_13 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 13)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 2
        + (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 13
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 6) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 6 1
  rw [tb3_6 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 2)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 2))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_odd (tb2_mem2 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_add _ _).trans
    (two_smul_congr (1) (1) d3_7_2 d3_7_14)

private theorem c3_7_14 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 14)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 7
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 14
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 7) (towerBasis (1 : ℝ) 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 7 0
  rw [tb3_7 (-1 : ℝ), tb1_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P10 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 3)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 3))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_E_even (tb2_mem3 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_7 d3_7_11)

private theorem c3_7_15 :
    (peelFuse (baseFuseR 2)).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 15)
      = (1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 3
        + (-1 : ℝ)
          • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) 15
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 3 7) (towerBasis (1 : ℝ) 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1) 7 1
  rw [tb3_7 (-1 : ℝ), tb1_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (P11 (baseFuseR 2) (towerBasis (-1 : ℝ) 2 3)
      one_mem_T0 (baseFuseR_val 2 (towerBasis (-1 : ℝ) 2 3))).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    (T10_EF_even (tb2_mem3 (-1 : ℝ)) rfl)).trans ?_
  exact (zpos_pair_sub _ _).trans
    (two_smul_congr (1) (-1) d3_7_3 d3_7_15)

/-- **Deliverable `(3,7)`**. -/
theorem realFuseMatrix_3_7 :
    realFuseMatrix 3 7 =
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
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
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by
  have hcol : ∀ j : Fin 16,
      (peelFuse (baseFuseR 2)).toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1) j)
        = (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 (![0, 4, 1, 5, 2, 6, 3, 7, 4, 0, 5, 1, 6, 2, 7, 3] j)
          + (![1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1] j : ℝ)
              • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1 (![12, 8, 13, 9, 14, 10, 15, 11, 8, 12, 9, 13, 10, 14, 11, 15] j) := by
    intro j
    fin_cases j
    · exact c3_7_0
    · exact c3_7_1
    · exact c3_7_2
    · exact c3_7_3
    · exact c3_7_4
    · exact c3_7_5
    · exact c3_7_6
    · exact c3_7_7
    · exact c3_7_8
    · exact c3_7_9
    · exact c3_7_10
    · exact c3_7_11
    · exact c3_7_12
    · exact c3_7_13
    · exact c3_7_14
    · exact c3_7_15
  show LinearMap.toMatrix
      (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 3) (towerBasis 1 1))
      (matrixSuperBasis (P := divisionTower (-1 : ℝ) 2) (towerBasis (-1) 2) 1 1)
      ((peelFuse (baseFuseR 2)).toAlgEquiv.toLinearMap)
    =
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
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
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j, map_add,
    map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]


/-! ### Branch `(2,6)`: `Cl_{0,2} ᵍ⊗ Cl_{2,0} ≅ M_{2|2}(ℝ)`

`realFuse 2 6 = peelFuse hypFuse`: `m = n = p = q = 1`, `D = ℝ`. -/

private theorem hyp26_00 :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 1 0))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier)
        + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier) := by
  rw [towerBasis_one_zero (-1 : ℝ), towerBasis_one_zero (1 : ℝ), hypFuse_val_one_one]
  exact WDec_one

private theorem hyp26_01 :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 1 0) (towerBasis (1 : ℝ) 1 1))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier)
        + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier) := by
  rw [towerBasis_one_zero (-1 : ℝ), towerBasis_one_one (1 : ℝ), hypFuse_val_one_gen]
  exact WDec_F

private theorem hyp26_10 :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 1 0))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier)
        - Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier) := by
  rw [towerBasis_one_one (-1 : ℝ), towerBasis_one_zero (1 : ℝ), hypFuse_val_gen_one]
  exact WDec_E

private theorem hyp26_11 :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (towerBasis (-1 : ℝ) 1 1) (towerBasis (1 : ℝ) 1 1))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier)
        - Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier) := by
  rw [towerBasis_one_one (-1 : ℝ), towerBasis_one_one (1 : ℝ), hypFuse_val_gen_gen]
  exact WDec_EF

private theorem d2_6_0 :
    Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 0 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 0) (Sum.inl 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_1 :
    Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 1 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 0) (Sum.inl 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_2 :
    Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 2 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 0) (Sum.inr 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_3 :
    Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 3 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 0) (Sum.inr 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_4 :
    Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 4 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 1) (Sum.inl 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_5 :
    Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 5 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 1) (Sum.inl 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_6 :
    Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 6 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 1) (Sum.inr 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_7 :
    Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 7 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inl 1) (Sum.inr 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_8 :
    Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 8 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 0) (Sum.inl 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_9 :
    Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 9 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 0) (Sum.inl 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_10 :
    Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 10 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 0) (Sum.inr 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_11 :
    Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 11 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 0) (Sum.inr 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_12 :
    Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 12 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 1) (Sum.inl 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_13 :
    Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 13 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 1) (Sum.inl 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_14 :
    Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 14 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 1) (Sum.inr 0) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem d2_6_15 :
    Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1)
        (1 : (SuperAlgebra.base ℝ).carrier)
      = matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 15 := by
  have h := matrixSuperBasis_apply_pair baseBasis 2 2 (Sum.inr 1) (Sum.inr 1) 0
  rw [baseBasis_apply] at h
  exact h.symm

private theorem c2_6_0 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 0)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 0
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 15
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 10
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 0 0
  rw [tb2_0 (-1 : ℝ), tb2_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG00 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem0 (1 : ℝ))
      hyp26_00).trans ?_
  refine ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)).trans
    (congrArg₂ (· + ·)
      (tail_one_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_one_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide)))).trans ?_
  exact (F_ppp _ _ _ _).trans
    (four_smul_congr (1) (1) (1) (1)
      d2_6_0 d2_6_15 d2_6_10 d2_6_5)

private theorem c2_6_1 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 1)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 13
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 8
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 0 1
  rw [tb2_0 (-1 : ℝ), tb2_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG00 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem1 (1 : ℝ))
      hyp26_01).trans ?_
  refine ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)).trans
    (congrArg₂ (· + ·)
      (tail_one_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_one_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide)))).trans ?_
  exact (F_pmm _ _ _ _).trans
    (four_smul_congr (1) (-1) (1) (-1)
      d2_6_2 d2_6_13 d2_6_8 d2_6_7)

private theorem c2_6_2 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 2)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 3
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 12
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 9
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 0 2
  rw [tb2_0 (-1 : ℝ), tb2_2 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG01 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem0 (1 : ℝ))
      hyp26_00).trans ?_
  refine ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypF').trans
    (congrArg₂ (· + ·)
      (tail_F_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_F_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide)))).trans ?_
  exact (F_ppp _ _ _ _).trans
    (four_smul_congr (1) (1) (1) (1)
      d2_6_3 d2_6_12 d2_6_9 d2_6_6)

private theorem c2_6_3 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 3)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 14
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 11
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 0) (towerBasis (1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 0 3
  rw [tb2_0 (-1 : ℝ), tb2_3 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG01 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem1 (1 : ℝ))
      hyp26_01).trans ?_
  refine ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypF').trans
    (congrArg₂ (· + ·)
      (tail_F_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_F_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide)))).trans ?_
  exact (F_pmm _ _ _ _).trans
    (four_smul_congr (1) (-1) (1) (-1)
      d2_6_1 d2_6_14 d2_6_11 d2_6_4)

private theorem c2_6_4 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 4)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 13
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 8
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 1 0
  rw [tb2_1 (-1 : ℝ), tb2_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG00 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem0 (1 : ℝ))
      hyp26_10).trans ?_
  refine ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)).trans
    (congrArg₂ (· - ·)
      (tail_one_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_one_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide)))).trans ?_
  exact (F_mmm _ _ _ _).trans
    (four_smul_congr (1) (-1) (-1) (1)
      d2_6_2 d2_6_13 d2_6_8 d2_6_7)

private theorem c2_6_5 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 5)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 0
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 15
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 10
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 1 1
  rw [tb2_1 (-1 : ℝ), tb2_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG00 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem1 (1 : ℝ))
      hyp26_11).trans ?_
  refine ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier)).trans
    (congrArg₂ (· - ·)
      (tail_one_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_one_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide)))).trans ?_
  exact (F_mpp _ _ _ _).trans
    (four_smul_congr (1) (1) (-1) (-1)
      d2_6_0 d2_6_15 d2_6_10 d2_6_5)

private theorem c2_6_6 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 6)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 14
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 11
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 1 2
  rw [tb2_1 (-1 : ℝ), tb2_2 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG01 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem0 (1 : ℝ))
      hyp26_10).trans ?_
  refine ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypF').trans
    (congrArg₂ (· - ·)
      (tail_F_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_F_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide)))).trans ?_
  exact (F_mmm _ _ _ _).trans
    (four_smul_congr (1) (-1) (-1) (1)
      d2_6_1 d2_6_14 d2_6_11 d2_6_4)

private theorem c2_6_7 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 7)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 3
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 12
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 9
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 1) (towerBasis (1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 1 3
  rw [tb2_1 (-1 : ℝ), tb2_3 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG01 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem1 (1 : ℝ))
      hyp26_11).trans ?_
  refine ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypF').trans
    (congrArg₂ (· - ·)
      (tail_F_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_F_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide)))).trans ?_
  exact (F_mpp _ _ _ _).trans
    (four_smul_congr (1) (1) (-1) (-1)
      d2_6_3 d2_6_12 d2_6_9 d2_6_6)

private theorem c2_6_8 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 8)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 3
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 12
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 9
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 8
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 2 0
  rw [tb2_2 (-1 : ℝ), tb2_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG10 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem0 (1 : ℝ))
      hyp26_00).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypE').trans
    (congrArg₂ (· + ·)
      (tail_E_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_E_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide))))).trans ?_
  exact (H_pmm _ _ _ _).trans
    (four_smul_congr (1) (-1) (1) (-1)
      d2_6_3 d2_6_12 d2_6_9 d2_6_6)

private theorem c2_6_9 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 9)
      = (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 1
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 14
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 11
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 9
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 2 1
  rw [tb2_2 (-1 : ℝ), tb2_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG10 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem1 (1 : ℝ))
      hyp26_01).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypE').trans
    (congrArg₂ (· + ·)
      (tail_E_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_E_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide))))).trans ?_
  exact (G_ppp _ _ _ _).trans
    (four_smul_congr (-1) (-1) (-1) (-1)
      d2_6_1 d2_6_14 d2_6_11 d2_6_4)

private theorem c2_6_10 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 10)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 0
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 15
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 10
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 10
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 2 2
  rw [tb2_2 (-1 : ℝ), tb2_2 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG11 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem0 (1 : ℝ))
      hyp26_00).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (hypE' * hypF')).trans
    (congrArg₂ (· + ·)
      (tail_EF_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_EF_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide))))).trans ?_
  exact (H_pmm _ _ _ _).trans
    (four_smul_congr (1) (-1) (1) (-1)
      d2_6_0 d2_6_15 d2_6_10 d2_6_5)

private theorem c2_6_11 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 11)
      = (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 2
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 13
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 8
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 11
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 2) (towerBasis (1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 2 3
  rw [tb2_2 (-1 : ℝ), tb2_3 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG11 hypFuse (towerBasis (-1 : ℝ) 1 0) (tb1_mem1 (1 : ℝ))
      hyp26_01).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_add (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (hypE' * hypF')).trans
    (congrArg₂ (· + ·)
      (tail_EF_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_EF_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide))))).trans ?_
  exact (G_ppp _ _ _ _).trans
    (four_smul_congr (-1) (-1) (-1) (-1)
      d2_6_2 d2_6_13 d2_6_8 d2_6_7)

private theorem c2_6_12 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 12)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 1
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 14
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 11
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 4 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 12
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 3 0
  rw [tb2_3 (-1 : ℝ), tb2_0 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG10 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem0 (1 : ℝ))
      hyp26_10).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypE').trans
    (congrArg₂ (· - ·)
      (tail_E_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_E_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide))))).trans ?_
  exact (H_mpp _ _ _ _).trans
    (four_smul_congr (1) (1) (-1) (-1)
      d2_6_1 d2_6_14 d2_6_11 d2_6_4)

private theorem c2_6_13 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 13)
      = (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 3
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 12
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 9
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 6 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 13
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 3 1
  rw [tb2_3 (-1 : ℝ), tb2_1 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG10 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem1 (1 : ℝ))
      hyp26_11).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      hypE').trans
    (congrArg₂ (· - ·)
      (tail_E_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_E_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide))))).trans ?_
  exact (G_mmm _ _ _ _).trans
    (four_smul_congr (-1) (1) (1) (-1)
      d2_6_3 d2_6_12 d2_6_9 d2_6_6)

private theorem c2_6_14 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 14)
      = (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 2
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 13
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 8
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 7 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 14
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 3 2
  rw [tb2_3 (-1 : ℝ), tb2_2 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG11 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem0 (1 : ℝ))
      hyp26_10).trans ?_
  refine (congrArg (fun t => ((sgn (0 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (hypE' * hypF')).trans
    (congrArg₂ (· - ·)
      (tail_EF_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inr 0) (by decide))
      (tail_EF_odd (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inl 0) (by decide))))).trans ?_
  exact (H_mpp _ _ _ _).trans
    (four_smul_congr (1) (1) (-1) (-1)
      d2_6_2 d2_6_13 d2_6_8 d2_6_7)

private theorem c2_6_15 :
    (peelFuse hypFuse).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 15)
      = (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 0
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 15
        + (1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 10
        + (-1 : ℝ)
          • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 5 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) 15
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 2 3) (towerBasis (1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (1 : ℝ) 2) 3 3
  rw [tb2_3 (-1 : ℝ), tb2_3 (1 : ℝ)] at hsrc
  rw [hsrc]
  refine (PG11 hypFuse (towerBasis (-1 : ℝ) 1 1) (tb1_mem1 (1 : ℝ))
      hyp26_11).trans ?_
  refine (congrArg (fun t => ((sgn (1 : ZMod 2) : ℤˣ) : ℤ) • t)
    ((tail_decL_sub (SuperAlgebra.base ℝ) 1 1
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0)
            (1 : (SuperAlgebra.base ℝ).carrier))
      (hypE' * hypF')).trans
    (congrArg₂ (· - ·)
      (tail_EF_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inl 0) (Sum.inl 0) (by decide))
      (tail_EF_even (SuperAlgebra.base ℝ) 1 1
        mem_base_one (Sum.inr 0) (Sum.inr 0) (by decide))))).trans ?_
  exact (G_mmm _ _ _ _).trans
    (four_smul_congr (-1) (1) (1) (-1)
      d2_6_0 d2_6_15 d2_6_10 d2_6_5)

/-- **Deliverable `(2,6)`**. -/
theorem realFuseMatrix_2_6 :
    realFuseMatrix 2 6 =
  !![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
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
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1] := by
  have hcol : ∀ j : Fin 16,
      (peelFuse hypFuse).toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2) j)
          = (![1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1] j : ℝ)
              • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 (![0, 2, 3, 1, 2, 0, 1, 3, 3, 1, 0, 2, 1, 3, 2, 0] j)
          + (![1, -1, 1, -1, -1, 1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1] j : ℝ)
              • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 (![15, 13, 12, 14, 13, 15, 14, 12, 12, 14, 15, 13, 14, 12, 13, 15] j)
          + (![1, 1, 1, 1, -1, -1, -1, -1, 1, -1, 1, -1, -1, 1, -1, 1] j : ℝ)
              • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 (![10, 8, 9, 11, 8, 10, 11, 9, 9, 11, 10, 8, 11, 9, 8, 10] j)
          + (![1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1] j : ℝ)
              • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2 (![5, 7, 6, 4, 7, 5, 4, 6, 6, 4, 5, 7, 4, 6, 7, 5] j) := by
    intro j
    fin_cases j
    · exact c2_6_0
    · exact c2_6_1
    · exact c2_6_2
    · exact c2_6_3
    · exact c2_6_4
    · exact c2_6_5
    · exact c2_6_6
    · exact c2_6_7
    · exact c2_6_8
    · exact c2_6_9
    · exact c2_6_10
    · exact c2_6_11
    · exact c2_6_12
    · exact c2_6_13
    · exact c2_6_14
    · exact c2_6_15
  show LinearMap.toMatrix
      (gtensorBasis (A := divisionTower (-1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis (-1) 2) (towerBasis 1 2))
      (matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 2 2)
      ((peelFuse hypFuse).toAlgEquiv.toLinearMap)
    =
  !![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
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
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1]
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j, map_add,
    map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    Basis.repr_self_apply, Basis.repr_self_apply, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]


/-! ### Not yet landed

The three remaining `RealFuse2` peel forwards `(2,5)`, `(3,6)` (32 × 32)
and `(3,5)` (64 × 64) are **iterated** peels — `peelFuse (peelFuse …)` —
and that is where the pattern above stops scaling.  All the value data is
in place: the seed columns are exactly the `(1,6)`, `(2,7)` and `(2,6)`
matrices landed here, the multi-term machinery below
(`tail_decL_add`/`_sub`/`_neg`, `unsmul_*`, `N_*`/`MM_*`/`KK_*`,
`four_smul_congr`) was written for them, and the resulting column data was
cross-checked against `scripts/certgen/out/lean_literals/fuse_{2_5,3_6}.txt`
outside Lean — every entry agrees.

What fails is the *elaboration*, not the mathematics: at a doubly-peeled
composite the `rfl`-crossing inside `peel_q00`…`peel_q11` (the `e1`
`have … := rfl` that spells out the five-stage chain) exceeds `1000000`
heartbeats with `(deterministic) timeout at isDefEq/whnf`, and the file
takes ≈ 7.5 min before reporting it.  A follow-up should not simply raise
`maxHeartbeats`; the fix is to stop re-deriving the composite by `rfl` at
each column and instead prove the four quadrant identities **once** as
abstract `SuperAlgEquiv` equations (`peelFuse e = tailEquiv ∘ … `), so
that the per-column work is only rewriting, never defeq on a nested
`peelFuse`. -/


end Superfusion

/-
Superfusion / Super / BWTransitivity

Milestone M7e-2: **transitivity of Brauer–Wall equivalence** — the
matrix-of-matrix collapse

  `M_{p'|q'}(M_{p|q}(A)) ≅ M_{p'p+q'q | p'q+q'p}(A)`

as graded algebras (`matrixSuperComp`), whence `IsBWEquivalent` is an
equivalence relation (`IsBWEquivalent.trans`, mirroring mathlib's
`IsBrauerEquivalent.trans` chain `reindex ∘ comp ∘ mapMatrix ∘ …`).

Ingredients: grading-transfer lemmas for the three matrix moves —
entrywise `mapMatrix` along a graded equivalence, `compAlgEquiv`
(nested matrices over the product index, parities adding), and
`reindexAlgEquiv` along a parity-preserving index bijection — plus the
explicit parity-compatible collapse bijection
`(p'|q') × (p|q) ≃ (p'p+q'q | p'q+q'p)` sorting the four blocks by
total parity, and the unit `M_{1|0}(P) ≅ P`.

Corollaries: a graded isomorphism gives BW-equivalence
(`IsBWEquivalent.of_superAlgEquiv`), and mod-8 periodicity becomes a
BW-equivalence statement (`isBWEquivalent_divisionTower`, both signs;
`DReal_isBWEquivalent`, both directions).
-/
import Superfusion.Super.BWPeriodicity
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Unique

namespace Superfusion

/-! ### Grading transfer for the three matrix moves -/

section Transfer

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

private theorem zmod2_comp_index : ∀ i x y z w : ZMod 2,
    i + x + y + z + w = i + (x + z) + (y + w) := by decide +revert

section MapMatrix

variable (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)
variable {n : Type*} [Fintype n] [DecidableEq n] (π : n → ZMod 2)

include hφ in
omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- Entrywise application of a graded equivalence carries the
coefficient matrix grading onto the coefficient matrix grading. -/
theorem mapMatrix_map_matrixGradingA (i : ZMod 2) :
    (matrixGradingA π 𝒜 i).map (φ.mapMatrix :
        Matrix n n A ≃ₐ[K] Matrix n n B).toLinearMap
      = matrixGradingA π ℬ i := by
  ext N
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨M, hM, rfl⟩
    intro a b
    show φ.mapMatrix M a b ∈ ℬ _
    rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply]
    exact (mem_iff_map_mem 𝒜 ℬ φ hφ).mp (hM a b)
  · intro hN
    refine ⟨φ.symm.mapMatrix N, fun a b => ?_, ?_⟩
    · rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply]
      refine (mem_iff_map_mem 𝒜 ℬ φ hφ).mpr ?_
      rw [AlgEquiv.apply_symm_apply]
      exact hN a b
    · show φ.mapMatrix (φ.symm.mapMatrix N) = N
      ext a b
      rw [AlgEquiv.mapMatrix_apply, AlgEquiv.mapMatrix_apply,
        Matrix.map_apply, Matrix.map_apply, AlgEquiv.apply_symm_apply]

end MapMatrix

section Comp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]
variable (π : n → ZMod 2) (ρ : m → ZMod 2)

omit [GradedAlgebra 𝒜] in
/-- Collapsing nested matrices onto the product index adds the
parities: `compAlgEquiv` carries
`matrixGradingA π (matrixGradingA ρ 𝒜)` onto
`matrixGradingA (π + ρ)`. -/
theorem compAlgEquiv_map_matrixGradingA (i : ZMod 2) :
    (matrixGradingA π (matrixGradingA ρ 𝒜) i).map
        (Matrix.compAlgEquiv n m A K).toLinearMap
      = matrixGradingA (fun x : n × m => π x.1 + ρ x.2) 𝒜 i := by
  ext N
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨M, hM, rfl⟩
    rintro ⟨a, c⟩ ⟨b, d⟩
    show M a b c d ∈ 𝒜 (i + (π a + ρ c) + (π b + ρ d))
    have h := hM a b c d
    rwa [zmod2_comp_index] at h
  · intro hN
    refine ⟨(Matrix.compAlgEquiv n m A K).symm N,
      fun a b c d => ?_, ?_⟩
    · show N (a, c) (b, d) ∈ 𝒜 (i + π a + π b + ρ c + ρ d)
      have h := hN (a, c) (b, d)
      rwa [← zmod2_comp_index] at h
    · exact (Matrix.compAlgEquiv n m A K).apply_symm_apply N

end Comp

section Reindex

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]
variable (π : n → ZMod 2) (ρ : m → ZMod 2)

include ρ in
omit [GradedAlgebra 𝒜] in
/-- Reindexing along a parity-preserving bijection carries the
coefficient matrix grading onto the coefficient matrix grading. -/
theorem reindexAlgEquiv_map_matrixGradingA (e : n ≃ m)
    (he : ∀ a, π a = ρ (e a)) (i : ZMod 2) :
    (matrixGradingA π 𝒜 i).map
        (Matrix.reindexAlgEquiv K A e).toLinearMap
      = matrixGradingA ρ 𝒜 i := by
  ext N
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨M, hM, rfl⟩
    intro a b
    show (Matrix.reindexAlgEquiv K A e) M a b ∈ 𝒜 _
    rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    have h := hM (e.symm a) (e.symm b)
    rwa [he (e.symm a), he (e.symm b), Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at h
  · intro hN
    refine ⟨(Matrix.reindexAlgEquiv K A e).symm N, fun a b => ?_, ?_⟩
    · show (Matrix.reindexAlgEquiv K A e).symm N a b ∈ 𝒜 _
      rw [Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv,
        Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      have h := hN (e a) (e b)
      rwa [← he a, ← he b] at h
    · exact (Matrix.reindexAlgEquiv K A e).apply_symm_apply N

end Reindex

end Transfer

/-! ### The parity-compatible collapse bijection -/

/-- The index bijection collapsing `(p'|q') × (p|q)` onto
`(p'p+q'q | p'q+q'p)`: distribute, sort the four blocks by total
parity (even = `p'×p ⊕ q'×q`, odd = `p'×q ⊕ q'×p`), and flatten. -/
def collapseIndexEquiv (p' q' p q : ℕ) :
    (Fin p' ⊕ Fin q') × (Fin p ⊕ Fin q)
      ≃ Fin (p' * p + q' * q) ⊕ Fin (p' * q + q' * p) :=
  (Equiv.sumProdDistrib _ _ _).trans <|
    (Equiv.sumCongr (Equiv.prodSumDistrib _ _ _)
      (Equiv.prodSumDistrib _ _ _)).trans <|
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans <|
    (Equiv.sumSumSumComm _ _ _ _).trans <|
    Equiv.sumCongr
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
        finSumFinEquiv)
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
        finSumFinEquiv)

/-- The collapse bijection preserves parity: the image parity is the
sum of the two block parities. -/
theorem collapseIndexEquiv_parity (p' q' p q : ℕ)
    (x : (Fin p' ⊕ Fin q') × (Fin p ⊕ Fin q)) :
    sumParity p' q' x.1 + sumParity p q x.2
      = sumParity (p' * p + q' * q) (p' * q + q' * p)
          (collapseIndexEquiv p' q' p q x) := by
  obtain ⟨a | a, b | b⟩ := x <;>
    (simp [collapseIndexEquiv, sumParity, Equiv.sumSumSumComm]; try decide)

/-! ### The bundled matrix moves -/

section Bundled

variable {K : Type*} [CommRing K]

/-- Functoriality of matrix stabilization in graded isomorphisms:
`M_{p|q}(P) ≅ M_{p|q}(Q)` entrywise from `P ≅ Q`. -/
noncomputable def SuperAlgEquiv.matrixSuper {P Q : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) (p q : ℕ) :
    SuperAlgEquiv (P.matrixSuper p q) (Q.matrixSuper p q) :=
  ⟨e.toAlgEquiv.mapMatrix,
    fun i => mapMatrix_map_matrixGradingA P.grading Q.grading
      e.toAlgEquiv e.map_grading (sumParity p q) i⟩

/-- **Matrix-of-matrix collapse** (M7e-2):
`M_{p'|q'}(M_{p|q}(P)) ≅ M_{p'p+q'q | p'q+q'p}(P)` as graded
algebras. -/
noncomputable def matrixSuperComp (P : SuperAlgebra K)
    (p' q' p q : ℕ) :
    SuperAlgEquiv ((P.matrixSuper p q).matrixSuper p' q')
      (P.matrixSuper (p' * p + q' * q) (p' * q + q' * p)) :=
  ⟨(Matrix.compAlgEquiv _ _ _ K).trans
      (Matrix.reindexAlgEquiv K _ (collapseIndexEquiv p' q' p q)),
    fun i => by
      show (matrixGradingA (sumParity p' q')
            (matrixGradingA (sumParity p q) P.grading) i).map
          ((Matrix.reindexAlgEquiv K _
              (collapseIndexEquiv p' q' p q)).toLinearMap.comp
            (Matrix.compAlgEquiv _ _ _ K).toLinearMap)
        = matrixGradingA
            (sumParity (p' * p + q' * q) (p' * q + q' * p)) P.grading i
      rw [Submodule.map_comp,
        compAlgEquiv_map_matrixGradingA P.grading (sumParity p' q')
          (sumParity p q) i,
        reindexAlgEquiv_map_matrixGradingA P.grading
          (fun x => sumParity p' q' x.1 + sumParity p q x.2)
          (sumParity (p' * p + q' * q) (p' * q + q' * p))
          (collapseIndexEquiv p' q' p q)
          (collapseIndexEquiv_parity p' q' p q) i]⟩

/-- The unique index of `Fin 1 ⊕ Fin 0`, chosen so that the resulting
`Fintype`/`DecidableEq` instances stay the ambient sum instances (a
custom `Unique (Fin 1 ⊕ Fin 0)` instance would trigger a diamond with
`Matrix.uniqueAlgEquiv`, which bakes in `Unique.fintype`). -/
private def idx10 : Fin 1 ⊕ Fin 0 := Sum.inl 0

private theorem idx10_unique (a : Fin 1 ⊕ Fin 0) : a = idx10 := by
  rcases a with a | a
  · exact congrArg Sum.inl (Subsingleton.elim a 0)
  · exact a.elim0

private theorem sumParity_idx10 : sumParity 1 0 idx10 = 0 := rfl

/-- The entrywise algebra equivalence `M_{1|0}(A) ≃ₐ[K] A`, built by
hand against the index `idx10` (see `idx10` for why
`Matrix.uniqueAlgEquiv` is avoided). -/
noncomputable def matrixOneAlgEquiv (A : Type*) [Ring A] [Algebra K A] :
    Matrix (Fin 1 ⊕ Fin 0) (Fin 1 ⊕ Fin 0) A ≃ₐ[K] A where
  toFun M := M idx10 idx10
  invFun x := Matrix.of fun _ _ => x
  left_inv M := by
    ext a b
    show M idx10 idx10 = M a b
    rw [idx10_unique a, idx10_unique b]
  right_inv _ := rfl
  map_mul' M N := by
    show (M * N) idx10 idx10 = M idx10 idx10 * N idx10 idx10
    rw [Matrix.mul_apply, Fintype.sum_eq_single idx10]
    intro b hb
    exact absurd (idx10_unique b) hb
  map_add' _ _ := rfl
  commutes' r := by
    show (algebraMap K (Matrix (Fin 1 ⊕ Fin 0) (Fin 1 ⊕ Fin 0) A)) r idx10 idx10
        = algebraMap K A r
    simp [Algebra.algebraMap_eq_smul_one]

/-- The unit of matrix stabilization: `M_{1|0}(P) ≅ P`. -/
noncomputable def matrixSuperOne (P : SuperAlgebra K) :
    SuperAlgEquiv (P.matrixSuper 1 0) P :=
  ⟨matrixOneAlgEquiv P.carrier, fun i => by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨M, hM, rfl⟩
      have h := hM idx10 idx10
      have hidx : i + sumParity 1 0 idx10 + sumParity 1 0 idx10 = i := by
        rw [sumParity_idx10, add_zero, add_zero]
      rwa [hidx] at h
    · intro hx
      refine ⟨Matrix.of fun _ _ => x, fun a b => ?_, rfl⟩
      rw [idx10_unique a, idx10_unique b]
      have hidx : i + sumParity 1 0 idx10 + sumParity 1 0 idx10 = i := by
        rw [sumParity_idx10, add_zero, add_zero]
      rw [hidx]
      exact hx⟩

/-- Transport a matrix stabilization along equalities of sizes. -/
noncomputable def matrixSuperCast (P : SuperAlgebra K)
    {p q p₂ q₂ : ℕ} (hp : p = p₂) (hq : q = q₂) :
    SuperAlgEquiv (P.matrixSuper p q) (P.matrixSuper p₂ q₂) := by
  subst hp
  subst hq
  exact SuperAlgEquiv.refl _

/-! ### Transitivity -/

/-- **Brauer–Wall equivalence is transitive** (M7e-2): the mathlib
`IsBrauerEquivalent.trans` chain, with parities carried through every
move. -/
theorem IsBWEquivalent.trans {P Q R : SuperAlgebra K}
    (h₁ : IsBWEquivalent P Q) (h₂ : IsBWEquivalent Q R) :
    IsBWEquivalent P R := by
  obtain ⟨p, q, r, s, hpq, hrs, ⟨e⟩⟩ := h₁
  obtain ⟨p', q', r', s', hpq', hrs', ⟨f⟩⟩ := h₂
  refine ⟨p' * p + q' * q, p' * q + q' * p,
    r * r' + s * s', r * s' + s * r', ?_, ?_, ?_⟩
  · have h : p' * p + q' * q + (p' * q + q' * p)
        = (p' + q') * (p + q) := by ring
    have h2 := Nat.mul_ne_zero hpq' hpq
    omega
  · have h : r * r' + s * s' + (r * s' + s * r')
        = (r + s) * (r' + s') := by ring
    have h2 := Nat.mul_ne_zero hrs hrs'
    omega
  · exact ⟨(matrixSuperComp P p' q' p q).symm.trans <|
      (e.matrixSuper p' q').trans <|
      (matrixSuperComp Q p' q' r s).trans <|
      (matrixSuperCast Q (by ring) (by ring)).trans <|
      (matrixSuperComp Q r s p' q').symm.trans <|
      (f.matrixSuper r s).trans <|
      matrixSuperComp R r s r' s'⟩

/-- `IsBWEquivalent` is an equivalence relation. -/
theorem isBWEquivalent_equivalence :
    Equivalence (IsBWEquivalent (K := K)) :=
  ⟨IsBWEquivalent.refl, IsBWEquivalent.symm, IsBWEquivalent.trans⟩

/-- A graded isomorphism gives Brauer–Wall equivalence. -/
theorem IsBWEquivalent.of_superAlgEquiv {P Q : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) : IsBWEquivalent P Q :=
  ⟨1, 0, 1, 0, one_ne_zero, one_ne_zero, ⟨e.matrixSuper 1 0⟩⟩

/-- A graded isomorphism onto a stabilization gives Brauer–Wall
equivalence. -/
theorem IsBWEquivalent.of_matrixSuper {P Q : SuperAlgebra K}
    {r s : ℕ} (hrs : r + s ≠ 0)
    (e : SuperAlgEquiv P (Q.matrixSuper r s)) : IsBWEquivalent P Q :=
  ⟨1, 0, r, s, one_ne_zero, hrs, ⟨(matrixSuperOne P).trans e⟩⟩

end Bundled

/-! ### Mod-8 periodicity as Brauer–Wall equivalence -/

section Mod8

variable (K : Type*) [Field K] [Invertible (2 : K)]

/-- The `ε = +1` division tower is mod-8 periodic up to Brauer–Wall
equivalence. -/
theorem isBWEquivalent_divisionTower (n : ℕ) :
    IsBWEquivalent (divisionTower (1 : K) (n + 8))
      (divisionTower (1 : K) n) :=
  .of_matrixSuper (by omega) (towerMatrixEquiv K n)

/-- The `ε = -1` division tower is mod-8 periodic up to Brauer–Wall
equivalence. -/
theorem isBWEquivalent_divisionTower_neg (n : ℕ) :
    IsBWEquivalent (divisionTower (-1 : K) (n + 8))
      (divisionTower (-1 : K) n) :=
  .of_matrixSuper (by omega) (towerMatrixEquivNeg K n)

end Mod8

/-- The paper's `D_n` are mod-8 periodic up to Brauer–Wall
equivalence, positive direction. -/
theorem DReal_isBWEquivalent (n : ℤ) (hn : 0 ≤ n) :
    IsBWEquivalent (DReal (n + 8)) (DReal n) := by
  obtain ⟨e⟩ := DReal_bw_mod8 n hn
  exact .of_matrixSuper (by omega) e

/-- The paper's `D_n` are mod-8 periodic up to Brauer–Wall
equivalence, negative direction. -/
theorem DReal_isBWEquivalent_neg (n : ℤ) (hn : n ≤ 0) :
    IsBWEquivalent (DReal (n - 8)) (DReal n) := by
  obtain ⟨e⟩ := DReal_bw_mod8_neg n hn
  exact .of_matrixSuper (by omega) e

end Superfusion

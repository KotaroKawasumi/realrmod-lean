/-
Superfusion / Gauge / RealFuseSpecTower

M15 semantic-bridge GROUP 1: value-pinning spec theorems for

* the remaining `RealFuse1` tower pairs `(1,2), (2,1), (7,7), (6,7),
  (7,6)` — all sign-free permutations, via the pilot's generic-`ε`
  helpers (`Superfusion.Gauge.RealFuseSpecPilot`; the helpers are
  `private` there, so they are re-derived here verbatim), and
* the `RealFuse2` forward mixed-sign pairs `(1,7), (1,6), (1,5), (2,7),
  (2,6), (2,5), (3,7), (3,6), (3,5)` — the hyperbolic core and the
  `peelFuse` chains, with genuine `±1` sign patterns.

Statement shapes follow the M15 contract: dimensions ≤ 16 use the
row-major literal `realFuseMatrix a b = !![...]`; dimensions 32 and 64
use the packed base-3 row encoding `fuseRows_a_b : Fin R → ℕ` with the
generic decoder `decode3` and the entrywise statement
`∀ i j, realFuseMatrix a b i j = fuseLit_a_b i j`.  All literal values
come from `scripts/certgen/fuse.py` via
`scripts/certgen/out/lean_literals/`.

Proof pattern per branch (the pilot's): (i) name each source frame
vector via `gtensorBasis_apply_pair` and the tower-basis dictionary;
(ii) push it through the branch composite `have`-by-`have` with the
`*_tmul` application lemmas, assembling through one `rfl`-proved
spelling of the composite; (iii) land on `Matrix.single`, bridge back
with `matrixSuperBasis_apply_pair`, and pin entries by
`Basis.repr_self_apply`.  Casts across `realFuse`'s dispatch dissolve
by `rfl` at concrete labels (`maxRecDepth 8000`,
`maxHeartbeats 1000000`).

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7).
-/
import Superfusion.Gauge.RealFuseMatrix

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace Superfusion

open Module TensorProduct GradedTensorProduct

/-! ### Shared application lemmas (re-derived from the pilot; the
pilot's copies are `private` there) -/

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

/-- The left unitor on `1 ᵍ⊗ v` for homogeneous `v`. -/
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

/-- The right unitor on `v ᵍ⊗ 1`. -/
private theorem gtensorUnitorRight_tmul_one (P : SuperAlgebra ℝ)
    (v : P.carrier) :
    (gtensorUnitorRight P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ v (1 : ℝ)) = v := by
  have h := gunitorRightHom_tmul P.grading v (1 : ℝ)
  rw [map_one, mul_one] at h
  exact h

/-- Left-unitor corner composite on a frame vector. -/
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

/-! ### The tower-basis dictionary (floors `1`, `2`, `3`) -/

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

private theorem towerBasis_three_0 (ε : ℝ) :
    towerBasis ε 3 0 = (1 : (divisionTower ε 3).carrier) := by
  have h := towerBasis_low ε 2 0
  rw [towerBasis_two_zero] at h
  exact h

private theorem towerBasis_three_1 (ε : ℝ) :
    towerBasis ε 3 1
      = OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 1) 0 :=
  towerBasis_low ε 2 1

private theorem towerBasis_three_2 (ε : ℝ) :
    towerBasis ε 3 2
      = OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 2) 0 :=
  towerBasis_low ε 2 2

private theorem towerBasis_three_3 (ε : ℝ) :
    towerBasis ε 3 3
      = OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 3) 0 :=
  towerBasis_low ε 2 3

private theorem towerBasis_three_4 (ε : ℝ) :
    towerBasis ε 3 4
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 0) :=
  towerBasis_high ε 2 0

private theorem towerBasis_three_5 (ε : ℝ) :
    towerBasis ε 3 5
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 1) :=
  towerBasis_high ε 2 1

private theorem towerBasis_three_6 (ε : ℝ) :
    towerBasis ε 3 6
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 2) :=
  towerBasis_high ε 2 2

private theorem towerBasis_three_7 (ε : ℝ) :
    towerBasis ε 3 7
      = OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 3) :=
  towerBasis_high ε 2 3

/-! ### `OddDouble`/tower-step application lemmas -/

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

/-- The forward tower step on the unit, at any floor. -/
private theorem towerSuccEquiv_one (ε : ℝ) (n : ℕ) :
    (towerSuccEquiv ε n).toAlgEquiv (1 : (divisionTower ε (n + 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (1 : (divisionTower ε n).carrier)
          (1 : (divisionTower ε 1).carrier) := by
  rw [show GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ
        (1 : (divisionTower ε n).carrier)
        (1 : (divisionTower ε 1).carrier)
      = (1 : ((divisionTower ε n).gtensor (divisionTower ε 1)).carrier) from
    gtensor_one_one (divisionTower ε n) (divisionTower ε 1)]
  exact map_one _

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

/-- The forward tower step at floor `0` on the unit. -/
private theorem towerSuccEquiv_zero_one (ε : ℝ) :
    (towerSuccEquiv ε 0).toAlgEquiv (1 : (divisionTower ε (0 + 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 0).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (1 : ℝ)
          (1 : (divisionTower ε 1).carrier) :=
  towerSuccEquiv_one ε 0

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

/-- `towerFuse ε a 0` is the right unitor on pure tensors. -/
private theorem towerFuse_a_zero_tmul (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 0).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 0).grading) ℝ u (1 : ℝ)) = u := by
  have h := gunitorRightHom_tmul (divisionTower ε a).grading u (1 : ℝ)
  rw [map_one, mul_one] at h
  exact h

/-- The `(1,1)` fusion on `u ᵍ⊗ 1`: `u ᵍ⊗ 1 ↦ (u, 0)`. -/
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
  rw [superRefl_apply, towerFuse_a_zero_tmul] at h3
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

/-- The `(1,1)` fusion on `u ᵍ⊗ g`: `u ᵍ⊗ g ↦ (0, u)`. -/
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
  rw [superRefl_apply, towerFuse_a_zero_tmul] at h3
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

/-! ### The `(1,2)` fusion: `towerFuse ε 1 2` on the four right-frame
vectors, generic in the left factor -/

/-- `(1,2)` on `u ᵍ⊗ 1`: to the `(A, 0)`-then-`(·,0)` corner. -/
private theorem towerFuse_one_two_tmul_one (ε : ℝ)
    (u : (divisionTower ε 1).carrier) :
    (towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (1 : (divisionTower ε 2).carrier))
      = OddDouble.mk (divisionTower ε 2).grading ε
          (OddDouble.mk (divisionTower ε 1).grading ε u 0) 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 1)) (towerSuccEquiv ε 1)
    u (1 : (divisionTower ε (1 + 1)).carrier)
  rw [superRefl_apply, towerSuccEquiv_one] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 1) (divisionTower ε 1)
    (divisionTower ε 1) u (1 : (divisionTower ε 1).carrier)
    (1 : (divisionTower ε 1).carrier)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 1 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u
      (1 : (divisionTower ε 1).carrier))
    (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, towerFuse_one_one_tmul_one] at h3
  have h4 := towerSuccEquiv_symm_tmul_one ε (1 + 1)
    (OddDouble.mk (divisionTower ε 1).grading ε u 0)
  have e1 : (towerFuse ε 1 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (1 : (divisionTower ε 2).carrier))
      = (towerSuccEquiv ε (1 + 1)).symm.toAlgEquiv
          (((towerFuse ε 1 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 1) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 1)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 1).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (1 : (divisionTower ε (1 + 1)).carrier))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-- `(1,2)` on `u ᵍ⊗ g₁` (`g₁ = (g, 0)` the low odd generator). -/
private theorem towerFuse_one_two_tmul_g1 (ε : ℝ)
    (u : (divisionTower ε 1).carrier) :
    (towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0))
      = OddDouble.mk (divisionTower ε 2).grading ε
          (OddDouble.mk (divisionTower ε 1).grading ε 0 u) 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 1)) (towerSuccEquiv ε 1)
    u (OddDouble.mk (divisionTower ε 1).grading ε
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0)
  rw [superRefl_apply, towerSuccEquiv_mk_left] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 1) (divisionTower ε 1)
    (divisionTower ε 1) u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
    (1 : (divisionTower ε 1).carrier)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 1 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
    (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, towerFuse_one_one_tmul_gen] at h3
  have h4 := towerSuccEquiv_symm_tmul_one ε (1 + 1)
    (OddDouble.mk (divisionTower ε 1).grading ε 0 u)
  have e1 : (towerFuse ε 1 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (OddDouble.mk (divisionTower ε 1).grading ε
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0))
      = (towerSuccEquiv ε (1 + 1)).symm.toAlgEquiv
          (((towerFuse ε 1 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 1) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 1)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 1).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (OddDouble.mk (divisionTower ε 1).grading ε
                    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0))))) :=
    rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-- `(1,2)` on `u ᵍ⊗ g₂` (`g₂ = (0, 1)` the high odd generator). -/
private theorem towerFuse_one_two_tmul_g2 (ε : ℝ)
    (u : (divisionTower ε 1).carrier) :
    (towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier)))
      = OddDouble.mk (divisionTower ε 2).grading ε 0
          (OddDouble.mk (divisionTower ε 1).grading ε u 0) := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 1)) (towerSuccEquiv ε 1)
    u (OddDouble.mk (divisionTower ε 1).grading ε 0
        (1 : (divisionTower ε 1).carrier))
  rw [superRefl_apply, towerSuccEquiv_mk_right] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 1) (divisionTower ε 1)
    (divisionTower ε 1) u (1 : (divisionTower ε 1).carrier)
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 1 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u
      (1 : (divisionTower ε 1).carrier))
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerFuse_one_one_tmul_one] at h3
  have h4 := towerSuccEquiv_symm_tmul_gen ε (1 + 1)
    (OddDouble.mk (divisionTower ε 1).grading ε u 0)
  have e1 : (towerFuse ε 1 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (OddDouble.mk (divisionTower ε 1).grading ε 0
          (1 : (divisionTower ε 1).carrier)))
      = (towerSuccEquiv ε (1 + 1)).symm.toAlgEquiv
          (((towerFuse ε 1 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 1) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 1)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 1).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (OddDouble.mk (divisionTower ε 1).grading ε 0
                    (1 : (divisionTower ε 1).carrier)))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-- `(1,2)` on `u ᵍ⊗ g₁g₂` (`g₁g₂ = (0, g)`). -/
private theorem towerFuse_one_two_tmul_g1g2 (ε : ℝ)
    (u : (divisionTower ε 1).carrier) :
    (towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = OddDouble.mk (divisionTower ε 2).grading ε 0
          (OddDouble.mk (divisionTower ε 1).grading ε 0 u) := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 1)) (towerSuccEquiv ε 1)
    u (OddDouble.mk (divisionTower ε 1).grading ε 0
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
  rw [superRefl_apply, towerSuccEquiv_mk_right] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 1) (divisionTower ε 1)
    (divisionTower ε 1) u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 1 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerFuse_one_one_tmul_gen] at h3
  have h4 := towerSuccEquiv_symm_tmul_gen ε (1 + 1)
    (OddDouble.mk (divisionTower ε 1).grading ε 0 u)
  have e1 : (towerFuse ε 1 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (OddDouble.mk (divisionTower ε 1).grading ε 0
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = (towerSuccEquiv ε (1 + 1)).symm.toAlgEquiv
          (((towerFuse ε 1 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 1) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 1)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 1).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (OddDouble.mk (divisionTower ε 1).grading ε 0
                    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))))) :=
    rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-! ### The `(2,1)` fusion: `towerFuse ε 2 1` on the two right-frame
vectors, generic in the left factor -/

/-- `(2,1)` on `v ᵍ⊗ 1`: `v ᵍ⊗ 1 ↦ (v, 0)`. -/
private theorem towerFuse_two_one_tmul_one (ε : ℝ)
    (v : (divisionTower ε 2).carrier) :
    (towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ v
          (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk (divisionTower ε 2).grading ε v 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 2)) (towerSuccEquiv ε 0)
    v (1 : (divisionTower ε (0 + 1)).carrier)
  rw [superRefl_apply, towerSuccEquiv_zero_one] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 2) (divisionTower ε 0)
    (divisionTower ε 1) v (1 : ℝ) (1 : (divisionTower ε 1).carrier)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 2 0)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
      (ℬ := (divisionTower ε 0).grading) ℝ v (1 : ℝ))
    (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, towerFuse_a_zero_tmul] at h3
  have h4 := towerSuccEquiv_symm_tmul_one ε (2 + 0) v
  have e1 : (towerFuse ε 2 1).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ v
        (1 : (divisionTower ε 1).carrier))
      = (towerSuccEquiv ε (2 + 0)).symm.toAlgEquiv
          (((towerFuse ε 2 0).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 2) (divisionTower ε 0)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 2)).gtensorCongr
                  (towerSuccEquiv ε 0)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 2).grading)
                  (ℬ := (divisionTower ε (0 + 1)).grading) ℝ v
                  (1 : (divisionTower ε (0 + 1)).carrier))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-- `(2,1)` on `v ᵍ⊗ g`: `v ᵍ⊗ g ↦ (0, v)`. -/
private theorem towerFuse_two_one_tmul_gen (ε : ℝ)
    (v : (divisionTower ε 2).carrier) :
    (towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ v
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = OddDouble.mk (divisionTower ε 2).grading ε 0 v := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε 2)) (towerSuccEquiv ε 0)
    v (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerSuccEquiv_zero_gen] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε 2) (divisionTower ε 0)
    (divisionTower ε 1) v (1 : ℝ)
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε 2 0)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
      (ℬ := (divisionTower ε 0).grading) ℝ v (1 : ℝ))
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerFuse_a_zero_tmul] at h3
  have h4 := towerSuccEquiv_symm_tmul_gen ε (2 + 0) v
  have e1 : (towerFuse ε 2 1).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ v
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = (towerSuccEquiv ε (2 + 0)).symm.toAlgEquiv
          (((towerFuse ε 2 0).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε 2) (divisionTower ε 0)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε 2)).gtensorCongr
                  (towerSuccEquiv ε 0)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε 2).grading)
                  (ℬ := (divisionTower ε (0 + 1)).grading) ℝ v
                  (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-! ### Destination dictionary at `M_{1|0}(T₂)` and `M_{1|0}(T₃)` -/

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

private theorem dst12_0 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 0
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (1 : (divisionTower ε 3).carrier) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 0
  rw [towerBasis_three_0] at h
  exact h

private theorem dst12_1 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 1
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 2).grading ε
            (OddDouble.mk (divisionTower ε 1).grading ε
              (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0) 0) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 1
  rw [towerBasis_three_1, towerBasis_two_one] at h
  exact h

private theorem dst12_2 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 2
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 2).grading ε
            (OddDouble.mk (divisionTower ε 1).grading ε 0
              (1 : (divisionTower ε 1).carrier)) 0) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 2
  rw [towerBasis_three_2, towerBasis_two_two] at h
  exact h

private theorem dst12_3 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 3
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 2).grading ε
            (OddDouble.mk (divisionTower ε 1).grading ε 0
              (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)) 0) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 3
  rw [towerBasis_three_3, towerBasis_two_three] at h
  exact h

private theorem dst12_4 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 4
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 2).grading ε 0
            (1 : (divisionTower ε 2).carrier)) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 4
  rw [towerBasis_three_4, towerBasis_two_zero] at h
  exact h

private theorem dst12_5 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 5
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 2).grading ε 0
            (OddDouble.mk (divisionTower ε 1).grading ε
              (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0)) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 5
  rw [towerBasis_three_5, towerBasis_two_one] at h
  exact h

private theorem dst12_6 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 6
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 2).grading ε 0
            (OddDouble.mk (divisionTower ε 1).grading ε 0
              (1 : (divisionTower ε 1).carrier))) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 6
  rw [towerBasis_three_6, towerBasis_two_two] at h
  exact h

private theorem dst12_7 (ε : ℝ) :
    matrixSuperBasis (towerBasis ε 3) 1 0 7
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (OddDouble.mk (divisionTower ε 2).grading ε 0
            (OddDouble.mk (divisionTower ε 1).grading ε 0
              (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))) := by
  have h := matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0
    (Sum.inl 0) (Sum.inl 0) 7
  rw [towerBasis_three_7, towerBasis_two_three] at h
  exact h

/-! ### The `(1,1)` columns and matrix (pilot's, re-derived) -/

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

/-- Generic-`ε` value pinning for `towerFuse ε 1 1 ; matrixSuperOne.symm`. -/
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

/-! ### The `(1,2)` columns and matrix -/

private theorem tf12_col0 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 0)
      = matrixSuperBasis (towerBasis ε 3) 1 0 0 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 0)
          (towerBasis ε 2 0) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 0 0
  rw [towerBasis_one_zero, towerBasis_two_zero] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (1 : (divisionTower ε 1).carrier)
          (1 : (divisionTower ε 2).carrier)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 0
  rw [towerFuse_one_two_tmul_one ε (1 : (divisionTower ε 1).carrier),
    matrixSuperOne_symm_single, dst12_0]
  rfl

private theorem tf12_col1 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 1)
      = matrixSuperBasis (towerBasis ε 3) 1 0 2 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 0)
          (towerBasis ε 2 1) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 0 1
  rw [towerBasis_one_zero, towerBasis_two_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (1 : (divisionTower ε 1).carrier)
          (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 2
  rw [towerFuse_one_two_tmul_g1 ε (1 : (divisionTower ε 1).carrier),
    matrixSuperOne_symm_single, dst12_2]
  rfl

private theorem tf12_col2 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 2)
      = matrixSuperBasis (towerBasis ε 3) 1 0 4 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 0)
          (towerBasis ε 2 2) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 0 2
  rw [towerBasis_one_zero, towerBasis_two_two] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (1 : (divisionTower ε 1).carrier)
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier))))
      = matrixSuperBasis (towerBasis ε 3) 1 0 4
  rw [towerFuse_one_two_tmul_g2 ε (1 : (divisionTower ε 1).carrier),
    matrixSuperOne_symm_single, dst12_4]
  rfl

private theorem tf12_col3 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 3)
      = matrixSuperBasis (towerBasis ε 3) 1 0 6 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 0)
          (towerBasis ε 2 3) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 0 3
  rw [towerBasis_one_zero, towerBasis_two_three] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (1 : (divisionTower ε 1).carrier)
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))))
      = matrixSuperBasis (towerBasis ε 3) 1 0 6
  rw [towerFuse_one_two_tmul_g1g2 ε (1 : (divisionTower ε 1).carrier),
    matrixSuperOne_symm_single, dst12_6]
  rfl

private theorem tf12_col4 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 4)
      = matrixSuperBasis (towerBasis ε 3) 1 0 1 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 1)
          (towerBasis ε 2 0) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 1 0
  rw [towerBasis_one_one, towerBasis_two_zero] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
          (1 : (divisionTower ε 2).carrier)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 1
  rw [towerFuse_one_two_tmul_one ε
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε),
    matrixSuperOne_symm_single, dst12_1]
  rfl

private theorem tf12_col5 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 5)
      = matrixSuperBasis (towerBasis ε 3) 1 0 3 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 1)
          (towerBasis ε 2 1) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 1 1
  rw [towerBasis_one_one, towerBasis_two_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
          (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 3
  rw [towerFuse_one_two_tmul_g1 ε
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε),
    matrixSuperOne_symm_single, dst12_3]
  rfl

private theorem tf12_col6 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 6)
      = matrixSuperBasis (towerBasis ε 3) 1 0 5 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 1)
          (towerBasis ε 2 2) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 1 2
  rw [towerBasis_one_one, towerBasis_two_two] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier))))
      = matrixSuperBasis (towerBasis ε 3) 1 0 5
  rw [towerFuse_one_two_tmul_g2 ε
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε),
    matrixSuperOne_symm_single, dst12_5]
  rfl

private theorem tf12_col7 (ε : ℝ) :
    ((towerFuse ε 1 2).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2) 7)
      = matrixSuperBasis (towerBasis ε 3) 1 0 7 := by
  have hsrc : gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
        (towerBasis ε 1) (towerBasis ε 2) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (towerBasis ε 1 1)
          (towerBasis ε 2 3) :=
    gtensorBasis_apply_pair (towerBasis ε 1) (towerBasis ε 2) 1 3
  rw [towerBasis_one_one, towerBasis_two_three] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 1 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))))
      = matrixSuperBasis (towerBasis ε 3) 1 0 7
  rw [towerFuse_one_two_tmul_g1g2 ε
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε),
    matrixSuperOne_symm_single, dst12_7]
  rfl

/-- Generic-`ε` value pinning for `towerFuse ε 1 2 ; matrixSuperOne.symm`:
the sign-free permutation with columns `(e₀,e₂,e₄,e₆,e₁,e₃,e₅,e₇)`. -/
private theorem towerFuse_one_two_matrix (ε : ℝ) :
    LinearMap.toMatrix
        (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
          (towerBasis ε 1) (towerBasis ε 2))
        (matrixSuperBasis (towerBasis ε 3) 1 0)
        (((towerFuse ε 1 2).trans
            (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv.toLinearMap)
      = !![1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0;
           0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1] := by
  have hcol : ∀ j : Fin 8,
      ((towerFuse ε 1 2).trans
          (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
          (gtensorBasis (A := divisionTower ε 1) (B := divisionTower ε 2)
            (towerBasis ε 1) (towerBasis ε 2) j)
        = matrixSuperBasis (towerBasis ε 3) 1 0
            (![0, 2, 4, 6, 1, 3, 5, 7] j) := by
    intro j
    fin_cases j
    · exact tf12_col0 ε
    · exact tf12_col1 ε
    · exact tf12_col2 ε
    · exact tf12_col3 ε
    · exact tf12_col4 ε
    · exact tf12_col5 ε
    · exact tf12_col6 ε
    · exact tf12_col7 ε
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j,
    Basis.repr_self_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-! ### The `(2,1)` columns and matrix -/

private theorem tf21_col0 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 0)
      = matrixSuperBasis (towerBasis ε 3) 1 0 0 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 0)
          (towerBasis ε 1 0) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 0 0
  rw [towerBasis_two_zero, towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (1 : (divisionTower ε 2).carrier)
          (1 : (divisionTower ε 1).carrier)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 0
  rw [towerFuse_two_one_tmul_one ε (1 : (divisionTower ε 2).carrier),
    matrixSuperOne_symm_single, dst12_0]
  rfl

private theorem tf21_col1 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 1)
      = matrixSuperBasis (towerBasis ε 3) 1 0 4 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 0)
          (towerBasis ε 1 1) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 0 1
  rw [towerBasis_two_zero, towerBasis_one_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (1 : (divisionTower ε 2).carrier)
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 4
  rw [towerFuse_two_one_tmul_gen ε (1 : (divisionTower ε 2).carrier),
    matrixSuperOne_symm_single, dst12_4]
  rfl

private theorem tf21_col2 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 2)
      = matrixSuperBasis (towerBasis ε 3) 1 0 1 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 1)
          (towerBasis ε 1 0) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 1 0
  rw [towerBasis_two_one, towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0)
          (1 : (divisionTower ε 1).carrier)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 1
  rw [towerFuse_two_one_tmul_one ε
      (OddDouble.mk (divisionTower ε 1).grading ε
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0),
    matrixSuperOne_symm_single, dst12_1]
  rfl

private theorem tf21_col3 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 3)
      = matrixSuperBasis (towerBasis ε 3) 1 0 5 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 1)
          (towerBasis ε 1 1) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 1 1
  rw [towerBasis_two_one, towerBasis_one_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0)
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 5
  rw [towerFuse_two_one_tmul_gen ε
      (OddDouble.mk (divisionTower ε 1).grading ε
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0),
    matrixSuperOne_symm_single, dst12_5]
  rfl

private theorem tf21_col4 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 4)
      = matrixSuperBasis (towerBasis ε 3) 1 0 2 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 2)
          (towerBasis ε 1 0) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 2 0
  rw [towerBasis_two_two, towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier))
          (1 : (divisionTower ε 1).carrier)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 2
  rw [towerFuse_two_one_tmul_one ε
      (OddDouble.mk (divisionTower ε 1).grading ε 0
        (1 : (divisionTower ε 1).carrier)),
    matrixSuperOne_symm_single, dst12_2]
  rfl

private theorem tf21_col5 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 5)
      = matrixSuperBasis (towerBasis ε 3) 1 0 6 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 2)
          (towerBasis ε 1 1) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 2 1
  rw [towerBasis_two_two, towerBasis_one_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier))
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 6
  rw [towerFuse_two_one_tmul_gen ε
      (OddDouble.mk (divisionTower ε 1).grading ε 0
        (1 : (divisionTower ε 1).carrier)),
    matrixSuperOne_symm_single, dst12_6]
  rfl

private theorem tf21_col6 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 6)
      = matrixSuperBasis (towerBasis ε 3) 1 0 3 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 3)
          (towerBasis ε 1 0) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 3 0
  rw [towerBasis_two_three, towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
          (1 : (divisionTower ε 1).carrier)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 3
  rw [towerFuse_two_one_tmul_one ε
      (OddDouble.mk (divisionTower ε 1).grading ε 0
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)),
    matrixSuperOne_symm_single, dst12_3]
  rfl

private theorem tf21_col7 (ε : ℝ) :
    ((towerFuse ε 2 1).trans
        (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1) 7)
      = matrixSuperBasis (towerBasis ε 3) 1 0 7 := by
  have hsrc : gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
        (towerBasis ε 2) (towerBasis ε 1) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε 2 3)
          (towerBasis ε 1 1) :=
    gtensorBasis_apply_pair (towerBasis ε 2) (towerBasis ε 1) 3 1
  rw [towerBasis_two_three, towerBasis_one_one] at hsrc
  rw [hsrc]
  show (matrixSuperOne (divisionTower ε 3)).symm.toAlgEquiv
      ((towerFuse ε 2 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 2).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = matrixSuperBasis (towerBasis ε 3) 1 0 7
  rw [towerFuse_two_one_tmul_gen ε
      (OddDouble.mk (divisionTower ε 1).grading ε 0
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)),
    matrixSuperOne_symm_single, dst12_7]
  rfl

/-- Generic-`ε` value pinning for `towerFuse ε 2 1 ; matrixSuperOne.symm`:
the sign-free permutation with columns `(e₀,e₄,e₁,e₅,e₂,e₆,e₃,e₇)`. -/
private theorem towerFuse_two_one_matrix (ε : ℝ) :
    LinearMap.toMatrix
        (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
          (towerBasis ε 2) (towerBasis ε 1))
        (matrixSuperBasis (towerBasis ε 3) 1 0)
        (((towerFuse ε 2 1).trans
            (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv.toLinearMap)
      = !![1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0;
           0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1] := by
  have hcol : ∀ j : Fin 8,
      ((towerFuse ε 2 1).trans
          (matrixSuperOne (divisionTower ε 3)).symm).toAlgEquiv
          (gtensorBasis (A := divisionTower ε 2) (B := divisionTower ε 1)
            (towerBasis ε 2) (towerBasis ε 1) j)
        = matrixSuperBasis (towerBasis ε 3) 1 0
            (![0, 4, 1, 5, 2, 6, 3, 7] j) := by
    intro j
    fin_cases j
    · exact tf21_col0 ε
    · exact tf21_col1 ε
    · exact tf21_col2 ε
    · exact tf21_col3 ε
    · exact tf21_col4 ε
    · exact tf21_col5 ε
    · exact tf21_col6 ε
    · exact tf21_col7 ε
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j,
    Basis.repr_self_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-! ### Deliverables: the five tower-pair spec theorems -/

/-- `(1,2)`: `Cl_{0,1} ᵍ⊗ Cl_{0,2} ≅ Cl_{0,3}`, sign-free permutation. -/
theorem realFuseMatrix_1_2 :
    realFuseMatrix 1 2
      = !![1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0;
           0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1] :=
  towerFuse_one_two_matrix (-1)

/-- `(7,6)`: `Cl_{1,0} ᵍ⊗ Cl_{2,0} ≅ Cl_{3,0}`, the same permutation. -/
theorem realFuseMatrix_7_6 :
    realFuseMatrix 7 6
      = !![1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0;
           0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1] :=
  towerFuse_one_two_matrix 1

/-- `(2,1)`: `Cl_{0,2} ᵍ⊗ Cl_{0,1} ≅ Cl_{0,3}`, sign-free permutation. -/
theorem realFuseMatrix_2_1 :
    realFuseMatrix 2 1
      = !![1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0;
           0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1] :=
  towerFuse_two_one_matrix (-1)

/-- `(6,7)`: `Cl_{2,0} ᵍ⊗ Cl_{1,0} ≅ Cl_{3,0}`, the same permutation. -/
theorem realFuseMatrix_6_7 :
    realFuseMatrix 6 7
      = !![1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0;
           0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1] :=
  towerFuse_two_one_matrix 1

/-- `(7,7)`: `Cl_{1,0} ᵍ⊗ Cl_{1,0} ≅ Cl_{2,0}` — the pilot's `(1,1)`
permutation at `ε = 1`. -/
theorem realFuseMatrix_7_7 :
    realFuseMatrix 7 7
      = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] :=
  towerFuse_one_one_matrix 1

/-! ### The hyperbolic core `(1,7)`

`realFuse 1 7` is `hypFuse` (`RealFuse2`), whose generator data
(`e ↦ E = [[0,1],[-1,0]]`, `f ↦ F = [[0,1],[1,0]]`) is `private` there;
the two lifted algebra maps are re-derived here **definitionally equal**
to the originals (all proof arguments are irrelevant), so `hypFuse`'s
values on pure tensors come from `GradedTensorProduct.lift_tmul` by
`rfl`-crossing. -/

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

/-- `φ : Cl_{0,1} → M_{1|1}(ℝ)`, `e ↦ E` — definitionally
`RealFuse2.hypFusePhi`. -/
private noncomputable def hypFusePhi' :
    (divisionTower (-1 : ℝ) 1).carrier →ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  OddDouble.lift (evenGrading ℝ ℝ) (-1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypE'
    hypE'_sq hconjE'

/-- `ψ : Cl_{1,0} → M_{1|1}(ℝ)`, `f ↦ F` — definitionally
`RealFuse2.hypFusePsi`. -/
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

/-- **The `rfl`-crossing for `hypFuse`**: its underlying algebra map is
the graded-tensor lift of the (re-derived) `φ, ψ`. -/
private theorem hypFuse_apply_tmul (a : (divisionTower (-1 : ℝ) 1).carrier)
    (b : (divisionTower (1 : ℝ) 1).carrier) :
    hypFuse.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ a b)
      = hypFusePhi' a * hypFusePsi' b :=
  GradedTensorProduct.lift_tmul (divisionTower (-1 : ℝ) 1).grading
    (divisionTower (1 : ℝ) 1).grading hypFusePhi' hypFusePsi'
    hypFuse_anticommutes' a b

/-! ### Single-entry decompositions of `1, F, E, EF` -/

private theorem hyp_oneDec :
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)
      = (1 : ℝ) • Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
            (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        + (1 : ℝ) • Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp

private theorem hyp_FDec :
    hypF'
      = (1 : ℝ) • Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
            (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        + (1 : ℝ) • Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp [hypF', Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

private theorem hyp_EDec :
    hypE'
      = (1 : ℝ) • Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
            (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        + (-1 : ℝ) • Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp [hypE', Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

private theorem hyp_EFDec :
    hypE' * hypF'
      = (1 : ℝ) • Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1)
            (Sum.inl 0 : Fin 1 ⊕ Fin 1) (1 : ℝ)
        + (-1 : ℝ) • Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1)
            (Sum.inr 0 : Fin 1 ⊕ Fin 1) (1 : ℝ) := by
  rw [hypE'_mul_hypF']
  refine Matrix.ext fun r c => ?_
  rcases r with r | r <;> rcases c with c | c <;>
    obtain rfl := Subsingleton.elim r 0 <;>
    (try obtain rfl := Subsingleton.elim c 0) <;>
    simp [Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

/-! ### The `(1,7)` frames and matrix -/

/-- The singleton basis of the base algebra, typed at
`(SuperAlgebra.base ℝ).carrier` (pilot's `baseBasis`). -/
private noncomputable def baseBasis :
    Basis (Fin 1) ℝ (SuperAlgebra.base ℝ).carrier :=
  Basis.singleton (Fin 1) ℝ

private theorem baseBasis_apply (i : Fin 1) : baseBasis i = (1 : ℝ) :=
  Basis.singleton_apply (Fin 1) ℝ i

private theorem dst17_0 :
    matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 0
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (1 : ℝ) := by
  have h := matrixSuperBasis_apply_pair baseBasis 1 1
    (Sum.inl 0) (Sum.inl 0) 0
  rw [baseBasis_apply] at h
  exact h

private theorem dst17_1 :
    matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 1
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (1 : ℝ) := by
  have h := matrixSuperBasis_apply_pair baseBasis 1 1
    (Sum.inl 0) (Sum.inr 0) 0
  rw [baseBasis_apply] at h
  exact h

private theorem dst17_2 :
    matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 2
      = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (1 : ℝ) := by
  have h := matrixSuperBasis_apply_pair baseBasis 1 1
    (Sum.inr 0) (Sum.inl 0) 0
  rw [baseBasis_apply] at h
  exact h

private theorem dst17_3 :
    matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 3
      = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (1 : ℝ) := by
  have h := matrixSuperBasis_apply_pair baseBasis 1 1
    (Sum.inr 0) (Sum.inr 0) 0
  rw [baseBasis_apply] at h
  exact h

private theorem hyp17_col0 :
    hypFuse.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 1) (towerBasis 1 1) 0)
      = (1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 3 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis (-1) 1) (towerBasis 1 1) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis (-1) 1 0)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1) 1) (towerBasis 1 1) 0 0
  rw [towerBasis_one_zero, towerBasis_one_zero] at hsrc
  rw [hsrc, hypFuse_apply_tmul, map_one, map_one, one_mul, dst17_0, dst17_3]
  exact hyp_oneDec

private theorem hyp17_col1 :
    hypFuse.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 1) (towerBasis 1 1) 1)
      = (1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 1
        + (1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 2 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis (-1) 1) (towerBasis 1 1) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis (-1) 1 0)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1) 1) (towerBasis 1 1) 0 1
  rw [towerBasis_one_zero, towerBasis_one_one] at hsrc
  rw [hsrc, hypFuse_apply_tmul, map_one, hypFusePsi'_gen, one_mul,
    dst17_1, dst17_2]
  exact hyp_FDec

private theorem hyp17_col2 :
    hypFuse.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 1) (towerBasis 1 1) 2)
      = (1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 1
        + (-1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 2 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis (-1) 1) (towerBasis 1 1) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis (-1) 1 1)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis (-1) 1) (towerBasis 1 1) 1 0
  rw [towerBasis_one_one, towerBasis_one_zero] at hsrc
  rw [hsrc, hypFuse_apply_tmul, hypFusePhi'_gen, map_one, mul_one,
    dst17_1, dst17_2]
  exact hyp_EDec

private theorem hyp17_col3 :
    hypFuse.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis (-1) 1) (towerBasis 1 1) 3)
      = (1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 0
        + (-1 : ℝ) • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1 3 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis (-1) 1) (towerBasis 1 1) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis (-1) 1 1)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis (-1) 1) (towerBasis 1 1) 1 1
  rw [towerBasis_one_one, towerBasis_one_one] at hsrc
  rw [hsrc, hypFuse_apply_tmul, hypFusePhi'_gen, hypFusePsi'_gen,
    dst17_0, dst17_3]
  exact hyp_EFDec

/-- **Deliverable `(1,7)`**: the hyperbolic core
`Cl_{0,1} ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(ℝ)`. -/
theorem realFuseMatrix_1_7 :
    realFuseMatrix 1 7
      = !![1, 0, 0, 1;
           0, 1, 1, 0;
           0, 1, -1, 0;
           1, 0, 0, -1] := by
  have hcol : ∀ j : Fin 4,
      hypFuse.toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
            (B := divisionTower (1 : ℝ) 1)
            (towerBasis (-1) 1) (towerBasis 1 1) j)
        = (![(1 : ℝ), 1, 1, 1] j)
              • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1
                  (![0, 1, 1, 0] j)
          + (![(1 : ℝ), 1, -1, -1] j)
              • matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1
                  (![3, 2, 2, 3] j) := by
    intro j
    fin_cases j
    · exact hyp17_col0
    · exact hyp17_col1
    · exact hyp17_col2
    · exact hyp17_col3
  show LinearMap.toMatrix
      (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis (-1) 1) (towerBasis 1 1))
      (matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 1 1)
      (hypFuse.toAlgEquiv.toLinearMap)
    = !![1, 0, 0, 1; 0, 1, 1, 0; 0, 1, -1, 0; 1, 0, 0, -1]
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol j, map_add,
    map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
/-! ### Not yet landed

The RealFuse2 forward branches `(1,6),(1,5),(2,7),(2,6),(2,5),(3,7),(3,6),
(3,5)` need the `peelFuse` evaluation machinery (graded-tensor linearity,
single-entry application, the interchange on homogeneous pure tensors,
`hypFuse` on the four generator tensors, the absorb tail and its four
quadrant lemmas).  A partial development of that machinery is preserved
out-of-tree at `scripts/certgen/out/tower_peel_wip.lean.txt` (not
compiled; resume from there). -/

end Superfusion

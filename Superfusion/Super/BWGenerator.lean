/-
Superfusion / Super / BWGenerator

Milestone M7f-4d-2: **the generator `[D_ε]` of the Brauer–Wall
group and its order**.  The division tower realizes the powers of
the generator:

  `[divisionTower ε n] = [D_ε]^n`   (M7c-3: odd double = `ᵍ⊗ D_ε`),

and with the Bott certificate (M7e-1) the eighth power is trivial:
`[D_{±1}]^8 = 1`, so the order of `[D_{±1}]` in `BW K` divides `8`.
Over `ℝ` this is the subgroup `⟨[D₁]⟩ ≤ BW(ℝ)` of the paper;
minimality (order exactly 8) is M7f-5.
-/
import Superfusion.Super.BWGroup
import Superfusion.Super.TensorGradingMap

namespace Superfusion

open Module
open TensorProduct
open GradedTensorProduct

section Generator

universe u

variable {K : Type u} [Field K]

/-- The rank-one Clifford superalgebra `D_ε`, bundled. -/
noncomputable def SuperAlgebra.adjoinOdd (ε : K) : SuperAlgebra K where
  carrier := AdjoinOdd ε
  grading := AdjoinOdd.grading ε

/-- The odd double is `P ᵍ⊗ D_ε`, bundled (M7c-3). -/
noncomputable def oddDoubleGtensor (P : SuperAlgebra.{u, u} K) (ε : K) :
    SuperAlgEquiv (P.gtensor (SuperAlgebra.adjoinOdd ε))
      (P.oddDouble ε) :=
  ⟨OddDouble.equivGradedTensor P.grading ε,
    equivGradedTensor_map_grading P.grading ε⟩

/-- `D_ε` is the first floor of the division tower. -/
noncomputable def adjoinOddEquivTowerOne (ε : K) :
    SuperAlgEquiv (SuperAlgebra.adjoinOdd ε) (divisionTower ε 1) :=
  (gtensorUnitorLeft (SuperAlgebra.adjoinOdd ε)).symm.trans
    (oddDoubleGtensor (.base K) ε)

/-- The inductive step of the tower, as a graded tensor
decomposition: `divisionTower ε (n+1) ≅ divisionTower ε n ᵍ⊗ D_ε`
with `D_ε` identified with the first floor. -/
noncomputable def towerSuccEquiv (ε : K) (n : ℕ) :
    SuperAlgEquiv (divisionTower ε (n + 1))
      ((divisionTower ε n).gtensor (divisionTower ε 1)) :=
  (oddDoubleGtensor (divisionTower ε n) ε).symm.trans
    ((SuperAlgEquiv.refl (divisionTower ε n)).gtensorCongr
      (adjoinOddEquivTowerOne ε))

instance (ε : K) (n : ℕ) :
    FiniteDimensional K (divisionTower ε n).carrier :=
  divisionTower_finite ε n

instance (ε : K) (n : ℕ) :
    Nontrivial (divisionTower ε n).carrier :=
  divisionTower_nontrivial ε n

/-- The tower classes satisfy the recursion
`[T_{n+1}] = [T_n]·[T_1]`. -/
theorem mk_divisionTower_succ (ε : K) (n : ℕ) :
    BWMonoid.mk (divisionTower ε (n + 1))
      = BWMonoid.mk (divisionTower ε n)
        * BWMonoid.mk (divisionTower ε 1) := by
  rw [BWMonoid.mk_mul]
  exact BWMonoid.mk_eq_mk_iff.mpr
    (IsBWEquivalent.of_superAlgEquiv (towerSuccEquiv ε n))

/-- **The division tower realizes the powers of the generator**:
`[divisionTower ε n] = [D_ε]^n` in the Brauer–Wall monoid. -/
theorem mk_divisionTower_pow (ε : K) (n : ℕ) :
    BWMonoid.mk (divisionTower ε n)
      = (BWMonoid.mk (divisionTower ε 1)) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact BWMonoid.one_def.symm
  | succ n ih =>
      rw [mk_divisionTower_succ, ih, pow_succ]

/-- With the Bott certificate, the eighth power of `[D₁]` is
trivial. -/
theorem mk_divisionTower_one_pow_eight [Invertible (2 : K)] :
    (BWMonoid.mk (divisionTower (1 : K) 1)) ^ 8 = 1 := by
  rw [← mk_divisionTower_pow, BWMonoid.one_def]
  exact BWMonoid.mk_eq_mk_iff.mpr (isBWEquivalent_divisionTower K 0)

/-- With the `ε = -1` Bott certificate, the eighth power of
`[D₋₁]` is trivial. -/
theorem mk_divisionTower_neg_one_pow_eight [Invertible (2 : K)] :
    (BWMonoid.mk (divisionTower (-1 : K) 1)) ^ 8 = 1 := by
  rw [← mk_divisionTower_pow, BWMonoid.one_def]
  exact BWMonoid.mk_eq_mk_iff.mpr (isBWEquivalent_divisionTower_neg K 0)

/-- **The generator `[D_ε]` as a unit** of the Brauer–Wall group. -/
noncomputable def bwGen (ε : K) [Invertible (2 : K)] (hε : ε ≠ 0) :
    BW K :=
  haveI := divisionTower_isSuperAzumaya (K := K) hε 1
  BW.ofAzumaya (divisionTower ε 1)

theorem bwGen_val (ε : K) [Invertible (2 : K)] (hε : ε ≠ 0) :
    (bwGen ε hε).val = BWMonoid.mk (divisionTower ε 1) := rfl

/-- `[D₁]^8 = 1` in the Brauer–Wall group. -/
theorem bwGen_one_pow_eight [Invertible (2 : K)] :
    (bwGen (1 : K) one_ne_zero) ^ 8 = 1 := by
  refine Units.ext ?_
  refine (Units.val_pow_eq_pow_val (bwGen (1 : K) one_ne_zero) 8).trans ?_
  rw [bwGen_val]
  exact mk_divisionTower_one_pow_eight

/-- `[D₋₁]^8 = 1` in the Brauer–Wall group. -/
theorem bwGen_neg_one_pow_eight [Invertible (2 : K)] :
    (bwGen (-1 : K) (neg_ne_zero.mpr one_ne_zero)) ^ 8 = 1 := by
  refine Units.ext ?_
  refine (Units.val_pow_eq_pow_val
    (bwGen (-1 : K) (neg_ne_zero.mpr one_ne_zero)) 8).trans ?_
  rw [bwGen_val]
  exact mk_divisionTower_neg_one_pow_eight

/-- **The order of `[D₁]` divides 8** (M7f-4d; minimality is
M7f-5). -/
theorem orderOf_bwGen_one_dvd_eight [Invertible (2 : K)] :
    orderOf (bwGen (1 : K) one_ne_zero) ∣ 8 :=
  orderOf_dvd_of_pow_eq_one bwGen_one_pow_eight

theorem orderOf_bwGen_neg_one_dvd_eight [Invertible (2 : K)] :
    orderOf (bwGen (-1 : K) (neg_ne_zero.mpr one_ne_zero)) ∣ 8 :=
  orderOf_dvd_of_pow_eq_one bwGen_neg_one_pow_eight

end Generator

/-! ### The real case: `⟨[D₁]⟩ ≤ BW(ℝ)` -/

section Real

/-- The generator `[D₁] ∈ BW(ℝ)` of the paper. -/
noncomputable def bwGenReal : BW ℝ := bwGen (1 : ℝ) one_ne_zero

/-- `[D₁]^8 = 1` in `BW(ℝ)`. -/
theorem bwGenReal_pow_eight : bwGenReal ^ 8 = 1 :=
  bwGen_one_pow_eight

/-- The order of `[D₁] ∈ BW(ℝ)` divides 8 (equality is M7f-5). -/
theorem orderOf_bwGenReal_dvd_eight : orderOf bwGenReal ∣ 8 :=
  orderOf_dvd_of_pow_eq_one bwGenReal_pow_eight

end Real

end Superfusion

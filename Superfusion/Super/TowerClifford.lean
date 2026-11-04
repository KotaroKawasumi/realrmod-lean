/-
Superfusion / Super / TowerClifford

Milestone M7e-3 (= M7c-4 revisited): **the division tower is the
Clifford algebra of the diagonal form** —

  `divisionTower ε n ≅ CliffordAlgebra ⟨ε, …, ε⟩`   as graded algebras,

where `⟨ε, …, ε⟩ = QuadraticMap.weightedSumSquares K (fun _ : Fin n => ε)`
on `Fin n → K`, with the `evenOdd` grading on the Clifford side.

Route (no `CliffordAlgebra.prodEquiv`, no graded-tensor functoriality,
no Clifford basis): the iterated lift (M7d-3a) INTO the Clifford
algebra on the generators `γ i = ι (Pi.single i 1)` — squares by
`ι_sq_scalar` + the value of the weighted sum of squares on a basis
vector, anticommutation by `ι_mul_ι_add_swap` + the vanishing of the
polar form on distinct basis vectors, oddness by `ι_mem_evenOdd_one`.
The lift is injective because the tower is graded-simple
(`towerLift_injective`) and surjective by `CliffordAlgebra.induction`
(every generator is hit, by induction up the tower).

Corollary that mathlib lacks: the Clifford algebra of the diagonal
form `⟨ε, …, ε⟩` (any `ε ≠ 0`, field base, `2` invertible) has
dimension `2 ^ n` (`finrank_cliffordAlgebra_diagForm`) — obtained here
with no Clifford basis at all, by transport from the tower.
-/
import Superfusion.Super.TowerLift
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

namespace Superfusion

/-! ### The diagonal form and its values on basis vectors -/

section Diagonal

variable {K : Type*} [CommRing K] (ε : K) (n : ℕ)

/-- The diagonal quadratic form `ε(x₁² + ⋯ + x_n²)` on `Fin n → K`. -/
noncomputable abbrev diagForm : QuadraticForm K (Fin n → K) :=
  QuadraticMap.weightedSumSquares K (fun _ : Fin n => ε)

theorem diagForm_single (i : Fin n) : diagForm ε n (Pi.single i 1) = ε := by
  rw [QuadraticMap.weightedSumSquares_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one, smul_eq_mul, mul_one]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem diagForm_polar_single (i j : Fin n) (hij : i ≠ j) :
    QuadraticMap.polar (diagForm ε n) (Pi.single i 1) (Pi.single j 1)
      = 0 := by
  have key : diagForm ε n (Pi.single i 1 + Pi.single j 1)
      = diagForm ε n (Pi.single i 1) + diagForm ε n (Pi.single j 1) := by
    rw [QuadraticMap.weightedSumSquares_apply,
      QuadraticMap.weightedSumSquares_apply,
      QuadraticMap.weightedSumSquares_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply, Pi.single_apply, smul_eq_mul]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) hij
    · ring
    · ring
    · ring
  rw [QuadraticMap.polar, key]
  ring

/-! ### The Clifford generators -/

/-- The Clifford generators `ι (Pi.single i 1)`, junk-padded beyond
index `n`. -/
noncomputable def gammaCl (k : ℕ) : CliffordAlgebra (diagForm ε n) :=
  if h : k < n then
    CliffordAlgebra.ι (diagForm ε n) (Pi.single ⟨k, h⟩ 1)
  else 0

theorem gammaCl_sq : ∀ i, i < n → gammaCl ε n i * gammaCl ε n i
    = algebraMap K (CliffordAlgebra (diagForm ε n)) ε := by
  intro i h
  rw [gammaCl, dif_pos h, CliffordAlgebra.ι_sq_scalar, diagForm_single]

theorem gammaCl_anti : ∀ i j : ℕ, i < n → j < n → i ≠ j →
    gammaCl ε n i * gammaCl ε n j = -(gammaCl ε n j * gammaCl ε n i) := by
  intro i j hi hj hij
  rw [gammaCl, gammaCl, dif_pos hi, dif_pos hj]
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := diagForm ε n)
    (Pi.single ⟨i, hi⟩ 1) (Pi.single ⟨j, hj⟩ 1)
  rw [diagForm_polar_single ε n ⟨i, hi⟩ ⟨j, hj⟩
      (fun hh => hij (congrArg Fin.val hh)), map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem gammaCl_odd : ∀ k, gammaCl ε n k ∈
    CliffordAlgebra.evenOdd (diagForm ε n) 1 := by
  intro k
  by_cases h : k < n
  · rw [gammaCl, dif_pos h]
    exact CliffordAlgebra.ι_mem_evenOdd_one _ _
  · rw [gammaCl, dif_neg h]
    exact zero_mem _

/-! ### The lift into the Clifford algebra -/

/-- The graded algebra map `D_ε^{⊗̂n} → Cl(⟨ε,…,ε⟩)` from the iterated
lift on the Clifford generators. -/
noncomputable def towerCliffordHom :
    (divisionTower ε n).carrier →ₐ[K] CliffordAlgebra (diagForm ε n) :=
  towerLift ε (gammaCl ε n) n (gammaCl_sq ε n) (gammaCl_anti ε n)
    n le_rfl

theorem towerCliffordHom_isHomogeneous :
    IsHomogeneousHom (divisionTower ε n).grading
      (CliffordAlgebra.evenOdd (diagForm ε n)) (towerCliffordHom ε n) :=
  towerLift_isHomogeneous ε (gammaCl ε n) n (gammaCl_sq ε n)
    (gammaCl_anti ε n) (CliffordAlgebra.evenOdd (diagForm ε n))
    (gammaCl_odd ε n) n le_rfl

/-- Every Clifford generator is in the range of the lift, by induction
up the tower. -/
theorem gammaCl_mem_range :
    ∀ (m : ℕ) (hm : m ≤ n), ∀ k, k < m →
      gammaCl ε n k ∈ (towerLift ε (gammaCl ε n) n (gammaCl_sq ε n)
        (gammaCl_anti ε n) m hm).range
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | m + 1, hm, k, hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
      · obtain ⟨x, hx⟩ := gammaCl_mem_range m (Nat.le_of_succ_le hm) k hk'
        refine ⟨OddDouble.mk (divisionTower ε m).grading ε x 0, ?_⟩
        show towerLift ε (gammaCl ε n) n (gammaCl_sq ε n) (gammaCl_anti ε n)
            (m + 1) hm (OddDouble.mk (divisionTower ε m).grading ε x 0)
          = gammaCl ε n k
        rw [towerLift_succ_mk, map_zero, zero_mul, add_zero]
        exact hx
      · subst hk'
        exact ⟨OddDouble.gen (divisionTower ε k).grading ε,
          towerLift_gen ε (gammaCl ε n) n (gammaCl_sq ε n)
            (gammaCl_anti ε n) k hm⟩

theorem towerCliffordHom_surjective :
    Function.Surjective (towerCliffordHom ε n) := by
  intro y
  suffices h : y ∈ (towerCliffordHom ε n).range by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, hx⟩
  induction y using CliffordAlgebra.induction with
  | algebraMap r =>
      exact ⟨algebraMap K _ r, (towerCliffordHom ε n).commutes r⟩
  | ι m =>
      have hm : CliffordAlgebra.ι (diagForm ε n) m
          = ∑ i : Fin n, m i • CliffordAlgebra.ι (diagForm ε n)
              (Pi.single i 1) := by
        conv_lhs => rw [← Finset.univ_sum_single m]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show Pi.single i (m i) = m i • Pi.single i (1 : K) from by
            rw [← Pi.single_smul, smul_eq_mul, mul_one],
          map_smul]
      rw [hm]
      refine Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ ?_ _
      have h := gammaCl_mem_range ε n n le_rfl i.val i.isLt
      rwa [gammaCl, dif_pos i.isLt, Fin.eta] at h
  | mul a b ha hb => exact mul_mem ha hb
  | add a b ha hb => exact add_mem ha hb

end Diagonal

/-! ### The graded isomorphism, over a field -/

section Field

variable {K : Type*} [Field K] [Invertible (2 : K)] (ε : K) (n : ℕ)

theorem towerCliffordHom_bijective (hε : ε ≠ 0) :
    Function.Bijective (towerCliffordHom ε n) :=
  ⟨towerLift_injective (gammaCl ε n) n (gammaCl_sq ε n)
      (gammaCl_anti ε n) hε (CliffordAlgebra.evenOdd (diagForm ε n))
      (gammaCl_odd ε n) n le_rfl,
    towerCliffordHom_surjective ε n⟩

/-- **The division tower is the Clifford algebra of the diagonal
form** (M7c-4/M7e-3): `D_ε^{⊗̂n} ≅ Cl(ε(x₁² + ⋯ + x_n²))` for any
`ε ≠ 0` over a field with `2` invertible. -/
noncomputable def towerCliffordEquiv (hε : ε ≠ 0) :
    (divisionTower ε n).carrier ≃ₐ[K] CliffordAlgebra (diagForm ε n) :=
  AlgEquiv.ofBijective (towerCliffordHom ε n)
    (towerCliffordHom_bijective ε n hε)

/-- The isomorphism carries the tower grading **onto** the `evenOdd`
grading: it is an isomorphism of superalgebras. -/
theorem towerCliffordHom_map_grading (hε : ε ≠ 0) (i : ZMod 2) :
    ((divisionTower ε n).grading i).map (towerCliffordHom ε n).toLinearMap
      = CliffordAlgebra.evenOdd (diagForm ε n) i :=
  map_grading_of_bijective (divisionTower ε n).grading
    (CliffordAlgebra.evenOdd (diagForm ε n)) (towerCliffordHom ε n)
    (towerCliffordHom_isHomogeneous ε n)
    (towerCliffordHom_bijective ε n hε) i

/-- A corollary mathlib lacks: the Clifford algebra of the diagonal
form `⟨ε, …, ε⟩` has dimension `2 ^ n` — obtained with no Clifford
basis, by transport from the division tower. -/
theorem finrank_cliffordAlgebra_diagForm (hε : ε ≠ 0) :
    Module.finrank K (CliffordAlgebra (diagForm ε n)) = 2 ^ n := by
  rw [← divisionTower_finrank ε n]
  exact ((towerCliffordEquiv ε n hε).toLinearEquiv.finrank_eq).symm

end Field

end Superfusion

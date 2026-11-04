/-
Superfusion / Super / QuaternionTower

Milestone M7f-5a: **the fourth floor of the division tower is the
quaternion matrix superalgebra**:

  `divisionTower (1 : K) 4 ≅ M_{1|1}(ℍ[K])`

as graded algebras — so `[D₁]⁴ = [ℍ]` in the Brauer–Wall relation.
The construction mirrors the Bott certificate (M7e-1): a quaternion
gamma system of four anticommuting odd square-one elements in
`M_{1|1}(ℍ)` (antidiagonal matrices with entries `1, ±i, ±j, ±k`)
feeds the iterated tower lift; injectivity is automatic from graded
simplicity, surjectivity is the dimension count `2⁴ = 2·2·4`.

Over `ℝ` this is the crux of the minimality of the Bott period:
`[D₁]⁴ = [ℍ_ℝ] ≠ 1` (M7f-5b) forces `orderOf [D₁] = 8` (M7f-5c).
-/
import Superfusion.Super.TowerLift
import Superfusion.Super.MatrixSuperCoeff
import Superfusion.Super.BWTransitivity
import Mathlib.Algebra.Quaternion

namespace Superfusion

open Module
open Quaternion

/-! ### The quaternion gamma system -/

section Gamma

variable (K : Type*) [Field K]

/-- The quaternion unit `i`. -/
private def qI : ℍ[K] := ⟨0, 1, 0, 0⟩

/-- The quaternion unit `j`. -/
private def qJ : ℍ[K] := ⟨0, 0, 1, 0⟩

/-- The quaternion unit `k`. -/
private def qK : ℍ[K] := ⟨0, 0, 0, 1⟩

private theorem qI_mul_qI : qI K * qI K = -1 := by
  show (⟨0, 1, 0, 0⟩ : ℍ[K]) * (⟨0, 1, 0, 0⟩ : ℍ[K]) = -1
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp

private theorem qJ_mul_qJ : qJ K * qJ K = -1 := by
  show (⟨0, 0, 1, 0⟩ : ℍ[K]) * (⟨0, 0, 1, 0⟩ : ℍ[K]) = -1
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp

private theorem qK_mul_qK : qK K * qK K = -1 := by
  show (⟨0, 0, 0, 1⟩ : ℍ[K]) * (⟨0, 0, 0, 1⟩ : ℍ[K]) = -1
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp

private theorem qJ_mul_qI : qJ K * qI K = -(qI K * qJ K) := by
  show (⟨0, 0, 1, 0⟩ : ℍ[K]) * (⟨0, 1, 0, 0⟩ : ℍ[K])
      = -((⟨0, 1, 0, 0⟩ : ℍ[K]) * (⟨0, 0, 1, 0⟩ : ℍ[K]))
  rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp

private theorem qK_mul_qI : qK K * qI K = -(qI K * qK K) := by
  show (⟨0, 0, 0, 1⟩ : ℍ[K]) * (⟨0, 1, 0, 0⟩ : ℍ[K])
      = -((⟨0, 1, 0, 0⟩ : ℍ[K]) * (⟨0, 0, 0, 1⟩ : ℍ[K]))
  rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp

private theorem qK_mul_qJ : qK K * qJ K = -(qJ K * qK K) := by
  show (⟨0, 0, 0, 1⟩ : ℍ[K]) * (⟨0, 0, 1, 0⟩ : ℍ[K])
      = -((⟨0, 0, 1, 0⟩ : ℍ[K]) * (⟨0, 0, 0, 1⟩ : ℍ[K]))
  rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp

/-- A `1 × 1` diagonal block. -/
private def qdiag (q : ℍ[K]) : Matrix (Fin 1) (Fin 1) ℍ[K] :=
  Matrix.diagonal fun _ => q

/-- The antidiagonal matrix with blocks `a` (upper) and `b`
(lower). -/
private def offDiag (a b : ℍ[K]) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[K] :=
  Matrix.fromBlocks 0 (qdiag K a) (qdiag K b) 0

private theorem offDiag_mul (a b a' b' : ℍ[K]) :
    offDiag K a b * offDiag K a' b'
      = Matrix.fromBlocks (qdiag K (a * b')) 0 0 (qdiag K (b * a')) := by
  unfold offDiag
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  unfold qdiag
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]

private theorem qdiag_neg (q : ℍ[K]) : qdiag K (-q) = -qdiag K q := by
  unfold qdiag
  rw [Matrix.diagonal_neg]

private theorem offDiag_sq (a b : ℍ[K]) (hab : a * b = 1) (hba : b * a = 1) :
    offDiag K a b * offDiag K a b = 1 := by
  rw [offDiag_mul, hab, hba]
  show Matrix.fromBlocks (qdiag K (1 : ℍ[K])) 0 0 (qdiag K (1 : ℍ[K])) = 1
  rw [show qdiag K (1 : ℍ[K]) = 1 from Matrix.diagonal_one, Matrix.fromBlocks_one]

private theorem offDiag_anti (a b a' b' : ℍ[K])
    (h1 : a * b' = -(a' * b)) (h2 : b * a' = -(b' * a)) :
    offDiag K a b * offDiag K a' b' = -(offDiag K a' b' * offDiag K a b) := by
  rw [offDiag_mul, offDiag_mul, h1, h2, qdiag_neg, qdiag_neg]
  rw [Matrix.fromBlocks_neg, neg_zero]

/-- Off-diagonal anticommutation of two signed pairs `(u, -u)` and
`(v, -v)`, from the single Hamilton relation `v * u = -(u * v)`. -/
private theorem offDiag_anti_of_hamilton (u v : ℍ[K]) (hvu : v * u = -(u * v)) :
    offDiag K u (-u) * offDiag K v (-v) = -(offDiag K v (-v) * offDiag K u (-u)) :=
  offDiag_anti K u (-u) v (-v) (by rw [mul_neg, mul_neg, hvu, neg_neg])
    (by rw [neg_mul, neg_mul, hvu, neg_neg])

/-- The reversed form of `offDiag_anti_of_hamilton`. -/
private theorem offDiag_anti_of_hamilton' (u v : ℍ[K]) (hvu : v * u = -(u * v)) :
    offDiag K v (-v) * offDiag K u (-u) = -(offDiag K u (-u) * offDiag K v (-v)) := by
  rw [offDiag_anti_of_hamilton K u v hvu, neg_neg]

/-- The unit gamma `offDiag 1 1` anticommutes with every signed pair
`(u, -u)`. -/
private theorem offDiag_anti_of_unit (u : ℍ[K]) :
    offDiag K (1 : ℍ[K]) 1 * offDiag K u (-u)
      = -(offDiag K u (-u) * offDiag K (1 : ℍ[K]) 1) :=
  offDiag_anti K 1 1 u (-u) (by rw [one_mul, mul_one])
    (by rw [mul_one, one_mul, neg_neg])

/-- The reversed form of `offDiag_anti_of_unit`. -/
private theorem offDiag_anti_of_unit' (u : ℍ[K]) :
    offDiag K u (-u) * offDiag K (1 : ℍ[K]) 1
      = -(offDiag K (1 : ℍ[K]) 1 * offDiag K u (-u)) :=
  offDiag_anti K u (-u) 1 1 (by rw [mul_one, one_mul, neg_neg])
    (by rw [neg_mul, one_mul, mul_one])

/-- The quaternion gamma system: four anticommuting odd square-one
elements of `M_{1|1}(ℍ[K])`. -/
def quatGamma : ℕ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[K]
  | 0 => offDiag K 1 1
  | 1 => offDiag K (qI K) (-qI K)
  | 2 => offDiag K (qJ K) (-qJ K)
  | 3 => offDiag K (qK K) (-qK K)
  | _ + 4 => 0

theorem quatGamma_sq : ∀ m, m < 4 →
    quatGamma K m * quatGamma K m
      = algebraMap K (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[K])
          (1 : K) := by
  intro m hm
  rw [map_one]
  interval_cases m
  · exact offDiag_sq K 1 1 (one_mul 1) (one_mul 1)
  · exact offDiag_sq K (qI K) (-qI K)
      (by rw [mul_neg, qI_mul_qI, neg_neg]) (by rw [neg_mul, qI_mul_qI, neg_neg])
  · exact offDiag_sq K (qJ K) (-qJ K)
      (by rw [mul_neg, qJ_mul_qJ, neg_neg]) (by rw [neg_mul, qJ_mul_qJ, neg_neg])
  · exact offDiag_sq K (qK K) (-qK K)
      (by rw [mul_neg, qK_mul_qK, neg_neg]) (by rw [neg_mul, qK_mul_qK, neg_neg])

theorem quatGamma_anti : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j →
    quatGamma K i * quatGamma K j = -(quatGamma K j * quatGamma K i) := by
  intro i j hi hj hne
  interval_cases i <;> interval_cases j
  · exact absurd rfl hne
  · exact offDiag_anti_of_unit K _
  · exact offDiag_anti_of_unit K _
  · exact offDiag_anti_of_unit K _
  · exact offDiag_anti_of_unit' K _
  · exact absurd rfl hne
  · exact offDiag_anti_of_hamilton K (qI K) (qJ K) (qJ_mul_qI K)
  · exact offDiag_anti_of_hamilton K (qI K) (qK K) (qK_mul_qI K)
  · exact offDiag_anti_of_unit' K _
  · exact offDiag_anti_of_hamilton' K (qI K) (qJ K) (qJ_mul_qI K)
  · exact absurd rfl hne
  · exact offDiag_anti_of_hamilton K (qJ K) (qK K) (qK_mul_qJ K)
  · exact offDiag_anti_of_unit' K _
  · exact offDiag_anti_of_hamilton' K (qI K) (qK K) (qK_mul_qI K)
  · exact offDiag_anti_of_hamilton' K (qJ K) (qK K) (qK_mul_qJ K)
  · exact absurd rfl hne

/-- The gamma system is odd for the `M_{1|1}` grading with purely
even quaternion coefficients. -/
theorem quatGamma_odd (m : ℕ) :
    quatGamma K m
      ∈ matrixGradingA (sumParity 1 1) (evenGrading K ℍ[K]) 1 := by
  intro a b
  rcases lt_or_ge m 4 with hm | hm
  · interval_cases m <;>
    · rcases a with a | a <;> rcases b with b | b <;>
        simp only [quatGamma, offDiag, qdiag, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₂₂, sumParity, Sum.elim_inl, Sum.elim_inr]
      all_goals first
        | (rw [show (1 + 0 + 0 : ZMod 2) = 1 from by decide, evenGrading_one]
           exact zero_mem _)
        | (rw [show (1 + 1 + 1 : ZMod 2) = 1 from by decide, evenGrading_one]
           exact Submodule.mem_bot _ |>.mpr rfl)
        | (rw [show (1 + 0 + 1 : ZMod 2) = 0 from by decide, evenGrading_zero]
           exact Submodule.mem_top)
        | (rw [show (1 + 1 + 0 : ZMod 2) = 0 from by decide, evenGrading_zero]
           exact Submodule.mem_top)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have h0 : quatGamma K (n + 4) = 0 := rfl
    rw [h0, Matrix.zero_apply]
    exact zero_mem _

end Gamma

/-! ### The certificate: `divisionTower 1 4 ≅ M_{1|1}(ℍ)` -/

section Certificate

variable (K : Type*) [Field K] [Invertible (2 : K)]

/-- The graded algebra map `D₁^{⊗̂4} → M_{1|1}(ℍ[K])` from the
iterated lift on the quaternion gamma system. -/
noncomputable def quatHom :
    (divisionTower (1 : K) 4).carrier →ₐ[K]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[K] :=
  towerLift (1 : K) (quatGamma K) 4 (quatGamma_sq K) (quatGamma_anti K)
    4 le_rfl

theorem quatHom_bijective : Function.Bijective (quatHom K) := by
  haveI := divisionTower_finite (1 : K) 4
  have hinj : Function.Injective (quatHom K) :=
    towerLift_injective (quatGamma K) 4 (quatGamma_sq K)
      (quatGamma_anti K) one_ne_zero
      (matrixGradingA (sumParity 1 1) (evenGrading K ℍ[K]))
      (quatGamma_odd K) 4 le_rfl
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank K (divisionTower (1 : K) 4).carrier
      = Module.finrank K
        (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[K]) := by
    rw [divisionTower_finrank, Module.finrank_matrix,
      Quaternion.finrank_eq_four]
    simp [Fintype.card_sum]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (quatHom K).toLinearMap) hdim).mp hinj

/-- **The fourth floor is the quaternion matrix superalgebra**
(M7f-5a): `D₁^{⊗̂4} ≅ M_{1|1}(ℍ[K])`. -/
noncomputable def quatEquiv :
    (divisionTower (1 : K) 4).carrier ≃ₐ[K]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[K] :=
  AlgEquiv.ofBijective (quatHom K) (quatHom_bijective K)

theorem quatEquiv_map_grading (i : ZMod 2) :
    ((divisionTower (1 : K) 4).grading i).map
        (quatEquiv K).toLinearMap
      = matrixGradingA (sumParity 1 1) (evenGrading K ℍ[K]) i :=
  map_grading_of_bijective (divisionTower (1 : K) 4).grading
    (matrixGradingA (sumParity 1 1) (evenGrading K ℍ[K]))
    (quatHom K)
    (towerLift_isHomogeneous (1 : K) (quatGamma K) 4 (quatGamma_sq K)
      (quatGamma_anti K)
      (matrixGradingA (sumParity 1 1) (evenGrading K ℍ[K]))
      (quatGamma_odd K) 4 le_rfl)
    (quatHom_bijective K) i

/-- The quaternions as a purely even superalgebra. -/
noncomputable def SuperAlgebra.quaternion : SuperAlgebra K where
  carrier := ℍ[K]
  grading := evenGrading K ℍ[K]

/-- `D₁^{⊗̂4} ≅ M_{1|1}(ℍ)`, bundled. -/
noncomputable def towerFourQuatSuper :
    SuperAlgEquiv (divisionTower (1 : K) 4)
      ((SuperAlgebra.quaternion K).matrixSuper 1 1) :=
  ⟨quatEquiv K, quatEquiv_map_grading K⟩

/-- **`[D₁]⁴ = [ℍ]` in the Brauer–Wall relation** (M7f-5a). -/
theorem isBWEquivalent_tower_four_quaternion :
    IsBWEquivalent (divisionTower (1 : K) 4)
      (SuperAlgebra.quaternion K) :=
  .of_matrixSuper (by omega) (towerFourQuatSuper K)

end Certificate

end Superfusion

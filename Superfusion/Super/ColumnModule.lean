/-
Superfusion / Super / ColumnModule

Milestone M7f-5b-1: **the column module of a matrix ring**.  For the
mathlib module structure `Module (Matrix n n R) (n → R)` (via
`mulVec`, `Mathlib/LinearAlgebra/Matrix/Action.lean`):

- over a division ring the column module is **simple**,
- over a field `F` its endomorphism ring is the scalars
  (`finrank F (End (M_n(F)) (F^n)) = 1`),
- over any `k`-algebra `D`, right multiplication embeds `D`
  `k`-linearly into `End (M_n(D)) (D^n)`.

These are the two sides of the Brauer-class invariant that
distinguishes `M_N(ℍ)` from `M_M(ℝ)` (M7f-5b-2): the endomorphism
algebra of the (unique) simple module has dimension 1 for split
matrix algebras and at least 4 on the quaternionic side.
-/
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Superfusion.Conventions

namespace Superfusion

open Module

/-! ### Simplicity over a division ring -/

section Simple

variable {D : Type*} [DivisionRing D]
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- Any nonzero vector generates the column module: the matrix
placing `w j (v i)⁻¹` in column `i` maps `v` to `w`. -/
theorem column_smul_eq {v : n → D} {i : n} (hvi : v i ≠ 0)
    (w : n → D) :
    (Matrix.of fun j k => if k = i then w j * (v i)⁻¹ else 0) • v
      = w := by
  funext j
  rw [Matrix.smul_eq_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [show (fun k => (if k = i then w j * (v i)⁻¹ else 0) * v k)
      = fun k => if k = i then w j * (v i)⁻¹ * v k else 0 from by
      funext k
      by_cases hk : k = i <;> simp [hk]]
  rw [Finset.sum_ite_eq' Finset.univ i
    (fun k => w j * (v i)⁻¹ * v k)]
  simp [inv_mul_cancel₀ hvi, mul_assoc]

/-- **The column module is simple** over a division ring. -/
theorem isSimpleModule_column :
    IsSimpleModule (Matrix n n D) (n → D) := by
  haveI : Nontrivial (n → D) :=
    ⟨Pi.single (Classical.arbitrary n) 1, 0, fun h => by
      have := congr_fun h (Classical.arbitrary n)
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this⟩
  refine { toNontrivial := ?_, eq_bot_or_eq_top := fun S => ?_ }
  · exact ⟨⊥, ⊤, fun h => by
      have h1 : (Pi.single (Classical.arbitrary n) 1 : n → D) ∈
          (⊥ : Submodule (Matrix n n D) (n → D)) :=
        h ▸ Submodule.mem_top
      simp only [Submodule.mem_bot] at h1
      have := congr_fun h1 (Classical.arbitrary n)
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · refine Or.inr ?_
    obtain ⟨v, hvS, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    refine Submodule.eq_top_iff'.mpr fun w => ?_
    rw [← column_smul_eq hvi w]
    exact S.smul_mem _ hvS

end Simple

/-! ### The endomorphisms of the split column module are scalars -/

section EndField

variable (F : Type*) [Field F]
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

private noncomputable def i₀ : n := Classical.arbitrary n

/-- Every endomorphism of the column module over a field is scalar. -/
theorem end_column_eq_smul_id
    (φ : (n → F) →ₗ[Matrix n n F] (n → F)) :
    ∃ c : F, φ = c • LinearMap.id := by
  set s : n → F := Pi.single (i₀ n) 1 with hs
  refine ⟨φ s (i₀ n), ?_⟩
  have hstep : ∀ v : n → F, φ v = φ s (i₀ n) • v := by
    intro v
    have hv : (Matrix.of fun j k => if k = i₀ n then v j else 0) • s
        = v := by
      funext j
      rw [Matrix.smul_eq_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [show (fun k => (if k = i₀ n then v j else 0) * s k)
          = fun k => if k = i₀ n then v j * s k else 0 from by
          funext k
          by_cases hk : k = i₀ n <;> simp [hk]]
      rw [Finset.sum_ite_eq' Finset.univ (i₀ n)
        (fun k => v j * s k)]
      simp [hs, Pi.single_eq_same]
    -- φ v = φ (A • s) = A • φ s; evaluate coordinates.
    have hAφ : φ v
        = (Matrix.of fun j k => if k = i₀ n then v j else 0) • φ s := by
      rw [← map_smul, hv]
    funext j
    rw [hAφ, Matrix.smul_eq_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [show (fun k => (if k = i₀ n then v j else 0) * φ s k)
        = fun k => if k = i₀ n then v j * φ s k else 0 from by
        funext k
        by_cases hk : k = i₀ n <;> simp [hk]]
    rw [Finset.sum_ite_eq' Finset.univ (i₀ n)
      (fun k => v j * φ s k)]
    simp [mul_comm]
  refine LinearMap.ext fun v => ?_
  rw [hstep v]
  rfl

/-- The scalars exhaust the endomorphisms: `c ↦ c • id` is a linear
equivalence `F ≃ End_{M_n(F)}(F^n)`. -/
noncomputable def endColumnEquiv :
    F ≃ₗ[F] Module.End (Matrix n n F) (n → F) := by
  refine LinearEquiv.ofBijective
    { toFun := fun c => c • LinearMap.id
      map_add' := fun c c' => add_smul c c' _
      map_smul' := fun c c' => by
        rw [RingHom.id_apply, smul_assoc] }
    ⟨fun c c' h => ?_, fun φ => ?_⟩
  · have := congr_fun (congrArg (fun ψ => ψ.toFun (Pi.single (i₀ n) 1)) h)
      (i₀ n)
    simpa [Pi.single_eq_same] using this
  · obtain ⟨c, hc⟩ := end_column_eq_smul_id F n φ
    exact ⟨c, hc.symm⟩

theorem finrank_end_column :
    finrank F (Module.End (Matrix n n F) (n → F)) = 1 := by
  rw [← (endColumnEquiv F n).finrank_eq, finrank_self]

end EndField

/-! ### Right multiplication embeds the coefficients -/

section RightMul

variable (k : Type*) [CommRing k]
variable (D : Type*) [Ring D] [Algebra k D]
variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Right multiplication by a coefficient, as an endomorphism of the
column module (it commutes with the left matrix action). -/
noncomputable def rmulEnd (q : D) :
    Module.End (Matrix n n D) (n → D) where
  toFun v := fun i => v i * q
  map_add' v w := by
    funext i
    rw [Pi.add_apply, add_mul, Pi.add_apply]
  map_smul' A v := by
    funext i
    rw [RingHom.id_apply, Matrix.smul_eq_mulVec, Matrix.smul_eq_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _)

@[simp] theorem rmulEnd_apply (q : D) (v : n → D) :
    rmulEnd D n q v = fun i => v i * q := rfl

/-- Right multiplication as a `k`-linear map `D → End(D^n)`. -/
noncomputable def rmulEndHom :
    D →ₗ[k] Module.End (Matrix n n D) (n → D) where
  toFun := rmulEnd D n
  map_add' q q' := by
    refine LinearMap.ext fun v => ?_
    funext i
    show v i * (q + q') = v i * q + v i * q'
    rw [mul_add]
  map_smul' c q := by
    refine LinearMap.ext fun v => ?_
    funext i
    show v i * (c • q) = c • (v i * q)
    rw [mul_smul_comm]

theorem rmulEndHom_injective [Nonempty n] :
    Function.Injective (rmulEndHom k D n) := by
  intro q q' h
  have h' : (rmulEndHom k D n q : (n → D) →ₗ[Matrix n n D] (n → D))
        (Pi.single (Classical.arbitrary n) 1)
      = (rmulEndHom k D n q' : (n → D) →ₗ[Matrix n n D] (n → D))
        (Pi.single (Classical.arbitrary n) 1) := by
    rw [h]
  have h'' : rmulEnd D n q (Pi.single (Classical.arbitrary n) 1)
      = rmulEnd D n q' (Pi.single (Classical.arbitrary n) 1) := h'
  have := congr_fun h'' (Classical.arbitrary n)
  simpa [rmulEnd_apply, Pi.single_eq_same] using this

end RightMul

end Superfusion

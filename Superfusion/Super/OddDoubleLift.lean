/-
Superfusion / Super / OddDoubleLift

Milestone M7d-2: the **universal property of the odd double**.

Given an algebra map `f : A →ₐ[K] C` and an element `γ : C` with

  `γ² = ε`,   `γ · f a = f (J a) · γ`,

there is a unique algebra map `lift : OddDouble 𝒜 ε →ₐ[K] C` with
`a + b·g ↦ f a + f b · γ`; if moreover `C` is graded, `f` is
grade-preserving and `γ` is odd, then `lift` is grade-preserving.

Combined with `injective_of_isGradedSimple` (GradedTransfer): a
grade-preserving `lift` out of a graded-simple odd double into a
nontrivial algebra is automatically **injective** — the tool for the
certificate route to Bott periodicity (M7d-3): eight explicit
anticommuting odd matrices `γ₁, …, γ₈` in `M_{8|8}(ℝ)` will give an
injective graded map from the division tower `D₁^{⊗̂8}`, surjective by
the dimension count `2⁸ = 16²`.
-/
import Superfusion.Super.OddDouble
import Superfusion.Super.SkolemNoether

namespace Superfusion

namespace OddDouble

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K)
variable {C : Type*} [Ring C] [Algebra K C]
variable (f : A →ₐ[K] C) (γ : C)

/-- The linear skeleton of `lift`: `a + b·g ↦ f a + f b · γ`. -/
noncomputable def liftLin : OddDouble 𝒜 ε →ₗ[K] C :=
  f.toLinearMap.comp (p1 𝒜 ε)
    + (LinearMap.mulRight K γ).comp (f.toLinearMap.comp (p2 𝒜 ε))

theorem liftLin_mk (a b : A) :
    liftLin 𝒜 ε f γ (mk 𝒜 ε a b) = f a + f b * γ := by
  rw [liftLin, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, p1_mk, p2_mk,
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    LinearMap.mulRight_apply]

section Lift

variable (hsq : γ * γ = algebraMap K C ε)
variable (hconj : ∀ a : A, γ * f a = f (parityMap 𝒜 a) * γ)

include hsq hconj in
private theorem lift_mul_aux (a b c d : A) :
    (f a + f b * γ) * (f c + f d * γ)
      = f (a * c + ε • (b * parityMap 𝒜 d))
        + f (a * d + b * parityMap 𝒜 c) * γ := by
  have h3 : f b * γ * f c = f b * f (parityMap 𝒜 c) * γ := by
    rw [mul_assoc, hconj, ← mul_assoc]
  have h4 : f b * γ * (f d * γ) = ε • (f b * f (parityMap 𝒜 d)) := by
    rw [mul_assoc, ← mul_assoc γ (f d) γ, hconj,
      mul_assoc (f (parityMap 𝒜 d)) γ γ, hsq,
      ← Algebra.commutes ε (f (parityMap 𝒜 d)), ← mul_assoc,
      ← Algebra.commutes ε (f b), mul_assoc, ← Algebra.smul_def]
  rw [mul_add, add_mul, add_mul, h3, h4, map_add, map_add, map_mul,
    map_smul, map_mul, map_mul, map_mul, add_mul]
  simp only [mul_assoc]
  abel

/-- **The universal property of the odd double** (M7d-2): an algebra
map on `A` together with an element `γ` satisfying `γ² = ε` and
`γ a γ⁻¹ = J a` extends to the odd double. -/
noncomputable def lift : OddDouble 𝒜 ε →ₐ[K] C :=
  AlgHom.ofLinearMap (liftLin 𝒜 ε f γ)
    (by
      rw [show (1 : OddDouble 𝒜 ε) = mk 𝒜 ε 1 0 from rfl, liftLin_mk,
        map_one, map_zero, zero_mul, add_zero])
    (fun x y => by
      conv_lhs => rw [← mk_p1_p2 𝒜 ε x, ← mk_p1_p2 𝒜 ε y, mk_mul_mk,
        liftLin_mk]
      conv_rhs => rw [← mk_p1_p2 𝒜 ε x, ← mk_p1_p2 𝒜 ε y, liftLin_mk,
        liftLin_mk]
      rw [lift_mul_aux 𝒜 ε f γ hsq hconj])

theorem lift_mk (a b : A) :
    lift 𝒜 ε f γ hsq hconj (mk 𝒜 ε a b) = f a + f b * γ :=
  liftLin_mk 𝒜 ε f γ a b

@[simp] theorem lift_inl (a : A) :
    lift 𝒜 ε f γ hsq hconj (mk 𝒜 ε a 0) = f a := by
  rw [lift_mk, map_zero, zero_mul, add_zero]

@[simp] theorem lift_gen :
    lift 𝒜 ε f γ hsq hconj (gen 𝒜 ε) = γ := by
  rw [show gen 𝒜 ε = mk 𝒜 ε 0 1 from rfl, lift_mk, map_zero, map_one,
    one_mul, zero_add]

/-- Every element of the odd double splits as `a + b·g`. -/
theorem mk_split (a b : A) :
    mk 𝒜 ε a b = mk 𝒜 ε a 0 + mk 𝒜 ε b 0 * gen 𝒜 ε := by
  refine ext 𝒜 ε ?_ ?_ <;> simp

/-- The lift is unique: any algebra map agreeing with `f` on `A` and
sending `g` to `γ` is `lift`. -/
theorem lift_unique (φ : OddDouble 𝒜 ε →ₐ[K] C)
    (hφ1 : ∀ a : A, φ (mk 𝒜 ε a 0) = f a) (hφ2 : φ (gen 𝒜 ε) = γ) :
    φ = lift 𝒜 ε f γ hsq hconj := by
  refine AlgHom.ext fun x => ?_
  conv_lhs => rw [← mk_p1_p2 𝒜 ε x, mk_split, map_add, map_mul, hφ1, hφ1,
    hφ2]
  conv_rhs => rw [← mk_p1_p2 𝒜 ε x, lift_mk]

/-- If the target is graded, `f` is grade-preserving and `γ` is odd,
then the lift is grade-preserving — combined with
`injective_of_isGradedSimple`, the injectivity tool for the Bott
certificate (M7d-3). -/
theorem lift_isHomogeneous (ℭ : ZMod 2 → Submodule K C)
    [GradedAlgebra ℭ] (hf : IsHomogeneousHom 𝒜 ℭ f) (hγ : γ ∈ ℭ 1) :
    IsHomogeneousHom (grading 𝒜 ε) ℭ (lift 𝒜 ε f γ hsq hconj) := by
  intro i x hx
  obtain ⟨h1, h2⟩ := (mem_grading 𝒜 ε).mp hx
  rw [← mk_p1_p2 𝒜 ε x, lift_mk]
  refine add_mem (hf i _ h1) ?_
  have h := SetLike.mul_mem_graded (hf (i + 1) _ h2) hγ
  have hidx : ∀ j : ZMod 2, j + 1 + 1 = j := by decide
  rwa [hidx] at h

end Lift

end OddDouble

end Superfusion

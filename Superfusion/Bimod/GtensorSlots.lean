/-
Superfusion / Bimod / GtensorSlots

Milestone M8a-7c-1: **the two slots of a graded tensor product
supercommute** — for homogeneous `x`, `y`,

  `(x ᵍ⊗ 1)(1 ᵍ⊗ y) = (-1)^{|x||y|} (1 ᵍ⊗ y)(x ᵍ⊗ 1)`,

together with the homogeneity of the slot embeddings
`includeLeft`/`includeRight`.  Pushed through any algebra map
`ψ : 𝒜 ᵍ⊗ 𝒞 →ₐ B'` and any `B'`-module, this is the source of the
`SuperCommSMul` hypothesis of the signed middle action (M8a-7a): the
two slot actions of `D_{ab} ⊗̂ D_c` on the paper's `C_{ab,c}`
supercommute.  (A public local replica of the parent's
`gtensor_disjoint_comm`, rebuilt from mathlib's
`tmul_coe_mul_coe_tmul` — the parent's copy lives in the
pentagon-active zone.)
-/
import Superfusion.Bimod.MiddleAction
import Superfusion.Super.TensorGrading

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞]

private theorem zmod2_slots : ∀ i k : ZMod 2, i * k + k * i = 0 := by
  decide

/-- **The two slots of `𝒜 ᵍ⊗ 𝒞` supercommute** on homogeneous
elements. -/
theorem includeLeft_mul_includeRight_supercomm {i k : ZMod 2} {x : A}
    {c : C} (hx : x ∈ 𝒜 i) (hc : c ∈ 𝒞 k) :
    GradedTensorProduct.includeLeft 𝒜 𝒞 x
        * GradedTensorProduct.includeRight 𝒜 𝒞 c
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (GradedTensorProduct.includeRight 𝒜 𝒞 c
            * GradedTensorProduct.includeLeft 𝒜 𝒞 x) := by
  have h1 : GradedTensorProduct.includeLeft 𝒜 𝒞 x
      * GradedTensorProduct.includeRight 𝒜 𝒞 c = x ᵍ⊗ₜ[K] c :=
    GradedTensorProduct.tmul_one_mul_one_tmul 𝒜 𝒞 x c
  have h2 : GradedTensorProduct.includeRight 𝒜 𝒞 c
      * GradedTensorProduct.includeLeft 𝒜 𝒞 x
      = (-1 : ℤˣ) ^ (k * i) • (x ᵍ⊗ₜ[K] c) := by
    have h := GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 𝒞
      (1 : A) (⟨c, hc⟩ : 𝒞 k) (⟨x, hx⟩ : 𝒜 i) (1 : C)
    rw [one_mul, mul_one] at h
    exact h
  rw [h1, h2, Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_slots, sgn_zero, Units.val_one,
    one_smul]

/-- **The mirror of `includeLeft_mul_includeRight_supercomm`**, product
order reversed: `(1 ᵍ⊗ c)(x ᵍ⊗ 1) = (-1)^{|c||x|} (x ᵍ⊗ 1)(1 ᵍ⊗ c)`.
Needed whenever the *right*-embedded slot is the one applied last (e.g.
`B_R`'s `T_a`-slot, M8a-9): unlike `includeLeft_mul_includeRight_supercomm`
this is not a bare corollary (units-squaring to `1` is not directly a
`rw`-lemma), so it is reproved from the same two raw facts
(`tmul_one_mul_one_tmul`/`tmul_coe_mul_coe_tmul`) with the substitution run
in the opposite direction. -/
theorem includeRight_mul_includeLeft_supercomm {i k : ZMod 2} {x : A}
    {c : C} (hx : x ∈ 𝒜 i) (hc : c ∈ 𝒞 k) :
    GradedTensorProduct.includeRight 𝒜 𝒞 c
        * GradedTensorProduct.includeLeft 𝒜 𝒞 x
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (GradedTensorProduct.includeLeft 𝒜 𝒞 x
            * GradedTensorProduct.includeRight 𝒜 𝒞 c) := by
  have h1 : GradedTensorProduct.includeLeft 𝒜 𝒞 x
      * GradedTensorProduct.includeRight 𝒜 𝒞 c = x ᵍ⊗ₜ[K] c :=
    GradedTensorProduct.tmul_one_mul_one_tmul 𝒜 𝒞 x c
  have h2 : GradedTensorProduct.includeRight 𝒜 𝒞 c
      * GradedTensorProduct.includeLeft 𝒜 𝒞 x
      = (-1 : ℤˣ) ^ (k * i) • (x ᵍ⊗ₜ[K] c) := by
    have h := GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 𝒞
      (1 : A) (⟨c, hc⟩ : 𝒞 k) (⟨x, hx⟩ : 𝒜 i) (1 : C)
    rw [one_mul, mul_one] at h
    exact h
  rw [h2, ← h1, ← sgn_eq_neg_one_uzpow, Units.smul_def]

/-- The left slot embedding is homogeneous (into the tensor grading of
M7f-1a). -/
theorem includeLeft_mem_tensorGrading {i : ZMod 2} {x : A}
    (hx : x ∈ 𝒜 i) :
    GradedTensorProduct.includeLeft 𝒜 𝒞 x
      ∈ Superfusion.tensorGrading 𝒜 𝒞 i := by
  have h := tmul_mem_tensorGrading 𝒜 𝒞 hx (SetLike.one_mem_graded 𝒞)
  rwa [add_zero] at h

/-- The right slot embedding is homogeneous. -/
theorem includeRight_mem_tensorGrading {k : ZMod 2} {c : C}
    (hc : c ∈ 𝒞 k) :
    GradedTensorProduct.includeRight 𝒜 𝒞 c
      ∈ Superfusion.tensorGrading 𝒜 𝒞 k := by
  have h := tmul_mem_tensorGrading 𝒜 𝒞 (SetLike.one_mem_graded 𝒜) hc
  rwa [zero_add] at h

/-! ### The supercommutation of pulled-back slot actions

Any algebra map out of `𝒜 ᵍ⊗ 𝒞` turns the two slots into
supercommuting actions on any module — the `SuperCommSMul` input of
the signed middle action. -/

variable {B' : Type*} [Ring B'] [Algebra K B']
variable {N : Type*} [AddCommGroup N] [Module B' N]

/-- Pushing the slot supercommutation through an algebra map
`ψ : 𝒜 ᵍ⊗ 𝒞 →ₐ B'` and a `B'`-action: the pulled-back slot actions
supercommute on any module. -/
theorem superCommSMul_of_algHom (ψ : (𝒜 ᵍ⊗[K] 𝒞) →ₐ[K] B')
    {i k : ZMod 2} {x : A} {c : C} (hx : x ∈ 𝒜 i) (hc : c ∈ 𝒞 k)
    (n : N) :
    ψ (GradedTensorProduct.includeLeft 𝒜 𝒞 x)
        • (ψ (GradedTensorProduct.includeRight 𝒜 𝒞 c) • n)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (ψ (GradedTensorProduct.includeRight 𝒜 𝒞 c)
            • (ψ (GradedTensorProduct.includeLeft 𝒜 𝒞 x) • n)) := by
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul,
    includeLeft_mul_includeRight_supercomm 𝒜 𝒞 hx hc, map_zsmul,
    smul_assoc]

end Bimod

end Superfusion

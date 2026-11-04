/-
Superfusion / Super / ParityConcentration

Milestone M5 (Proposition 2.1), parity half: the supercenter of a
super-bimodule is a *graded* submodule (components of supercentral
elements are supercentral), and a one-dimensional graded submodule is
concentrated in a single parity.  Combined with the dimension half this
completes **Proposition 2.1**.
-/
import Superfusion.Super.Prop21

namespace Superfusion

section ModParts

variable {K : Type*} [CommRing K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]

/-- The even projection of a `ZMod 2`-decomposed module. -/
noncomputable def evenPartMod : M →ₗ[K] M :=
  (ℳ 0).subtype ∘ₗ
    DirectSum.component K (ZMod 2) (fun i => ↥(ℳ i)) 0 ∘ₗ
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

theorem evenPartMod_of_mem_zero {m : M} (hm : m ∈ ℳ 0) :
    evenPartMod ℳ m = m := by
  show (DirectSum.decompose ℳ m 0 : M) = m
  rw [DirectSum.decompose_of_mem_same ℳ hm]

theorem evenPartMod_of_mem_one {m : M} (hm : m ∈ ℳ 1) :
    evenPartMod ℳ m = 0 := by
  show (DirectSum.decompose ℳ m 0 : M) = 0
  rw [DirectSum.decompose_of_mem_ne ℳ hm (by decide)]

theorem evenPartMod_mem (m : M) : evenPartMod ℳ m ∈ ℳ 0 := by
  show (DirectSum.decompose ℳ m 0 : M) ∈ ℳ 0
  exact Submodule.coe_mem _

theorem oddPartMod_mem (m : M) : oddPartMod ℳ m ∈ ℳ 1 := by
  show (DirectSum.decompose ℳ m 1 : M) ∈ ℳ 1
  exact Submodule.coe_mem _

theorem evenPartMod_add_oddPartMod (m : M) :
    evenPartMod ℳ m + oddPartMod ℳ m = m := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => rw [map_zero, map_zero, add_zero]
  | @homogeneous i x =>
      rcases zmod2_cases i with hi | hi <;> subst hi
      · rw [evenPartMod_of_mem_zero ℳ x.2, oddPartMod_of_mem_zero ℳ x.2,
          add_zero]
      · rw [evenPartMod_of_mem_one ℳ x.2, oddPartMod_of_mem_one ℳ x.2,
          zero_add]
  | add x y hx hy => rw [map_add, map_add, add_add_add_comm, hx, hy]

theorem partsMod_eq_of_add_eq {x₀ y₀ x₁ y₁ : M}
    (hx₀ : x₀ ∈ ℳ 0) (hy₀ : y₀ ∈ ℳ 0) (hx₁ : x₁ ∈ ℳ 1) (hy₁ : y₁ ∈ ℳ 1)
    (h : x₀ + x₁ = y₀ + y₁) : x₀ = y₀ ∧ x₁ = y₁ := by
  have comp : ∀ {u₀ u₁ : M}, u₀ ∈ ℳ 0 → u₁ ∈ ℳ 1 →
      (DirectSum.decompose ℳ (u₀ + u₁) 0 : M) = u₀ := by
    intro u₀ u₁ h₀ h₁
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      DirectSum.decompose_of_mem_same ℳ h₀,
      DirectSum.decompose_of_mem_ne ℳ h₁ (by decide), add_zero]
  have h₀ : x₀ = y₀ := by
    have hcast := congrArg (fun z => (DirectSum.decompose ℳ z 0 : M)) h
    rwa [comp hx₀ hx₁, comp hy₀ hy₁] at hcast
  refine ⟨h₀, ?_⟩
  have h' := h
  rw [h₀] at h'
  exact add_left_cancel h'

theorem eq_zero_of_mem_zero_of_mem_one_mod {m : M}
    (h0 : m ∈ ℳ 0) (h1 : m ∈ ℳ 1) : m = 0 := by
  have hm := DirectSum.decompose_of_mem_same ℳ h0
  have h' := DirectSum.decompose_of_mem_ne ℳ h1
    (show (1 : ZMod 2) ≠ 0 from by decide)
  rw [h'] at hm
  exact hm.symm

end ModParts

section Graded

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [Module A M] [Module Aᵐᵒᵖ M]
variable [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower K A M] [IsScalarTower K Aᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul 𝒜 ℳ]

omit [SMulCommClass A Aᵐᵒᵖ M] in
/-- **The supercenter of a super-bimodule is graded**: the even and odd
parts of a supercentral element are supercentral. -/
theorem parts_mem_superCenterBimod {m : M} (hm : m ∈ superCenterBimod 𝒜 ℳ) :
    evenPartMod ℳ m ∈ superCenterBimod 𝒜 ℳ ∧
      oddPartMod ℳ m ∈ superCenterBimod 𝒜 ℳ := by
  set m₀ := evenPartMod ℳ m with hm₀
  set m₁ := oddPartMod ℳ m with hm₁
  have hsum : m₀ + m₁ = m := evenPartMod_add_oddPartMod ℳ m
  have key : ∀ j : ZMod 2, ∀ b ∈ 𝒜 j,
      b • m₀ = signedRSMul 𝒜 ℳ b m₀ ∧ b • m₁ = signedRSMul 𝒜 ℳ b m₁ := by
    intro j b hb
    have h := (mem_superCenterBimod 𝒜 ℳ).mp hm b
    rw [← hsum, smul_add, map_add] at h
    -- memberships of the four summands
    have hL0 : b • m₀ ∈ ℳ (j + 0) := by
      have := SetLike.GradedSMul.smul_mem hb (evenPartMod_mem ℳ m)
      rwa [vadd_eq_add] at this
    have hL1 : b • m₁ ∈ ℳ (j + 1) := by
      have := SetLike.GradedSMul.smul_mem hb (oddPartMod_mem ℳ m)
      rwa [vadd_eq_add] at this
    have hR0 : signedRSMul 𝒜 ℳ b m₀ ∈ ℳ (j + 0) := by
      rw [signedRSMul_of_mem 𝒜 ℳ hb (evenPartMod_mem ℳ m)]
      exact zsmul_mem (GradedRightSMul.smul_mem hb (evenPartMod_mem ℳ m)) _
    have hR1 : signedRSMul 𝒜 ℳ b m₁ ∈ ℳ (j + 1) := by
      rw [signedRSMul_of_mem 𝒜 ℳ hb (oddPartMod_mem ℳ m)]
      exact zsmul_mem (GradedRightSMul.smul_mem hb (oddPartMod_mem ℳ m)) _
    rcases zmod2_cases j with hj | hj <;> subst hj
    · -- grades (0, 1)
      rw [show ((0 : ZMod 2) + 0) = 0 from by decide] at hL0 hR0
      rw [show ((0 : ZMod 2) + 1) = 1 from by decide] at hL1 hR1
      exact partsMod_eq_of_add_eq ℳ hL0 hR0 hL1 hR1 h
    · -- grades (1, 0): swap the roles
      rw [show ((1 : ZMod 2) + 1) = 0 from by decide] at hL1 hR1
      rw [show ((1 : ZMod 2) + 0) = 1 from by decide] at hL0 hR0
      have h' : b • m₁ + b • m₀ =
          signedRSMul 𝒜 ℳ b m₁ + signedRSMul 𝒜 ℳ b m₀ := by
        rw [add_comm (b • m₁), add_comm (signedRSMul 𝒜 ℳ b m₁)]
        exact h
      have hparts := partsMod_eq_of_add_eq ℳ hL1 hR1 hL0 hR0 h'
      exact ⟨hparts.2, hparts.1⟩
  have step : ∀ (m' : M), (∀ j : ZMod 2, ∀ b ∈ 𝒜 j,
      b • m' = signedRSMul 𝒜 ℳ b m') → m' ∈ superCenterBimod 𝒜 ℳ := by
    intro m' hkey
    rw [mem_superCenterBimod]
    intro b
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [zero_smul, map_zero, LinearMap.zero_apply]
    | add u u' hu hu' =>
        rw [add_smul, map_add, LinearMap.add_apply, hu, hu']
    | @homogeneous j x => exact hkey j (x : A) x.2
  exact ⟨step m₀ fun j b hb => (key j b hb).1,
    step m₁ fun j b hb => (key j b hb).2⟩

end Graded

section Concentration

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [Module A M] [Module Aᵐᵒᵖ M]
variable [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower K A M] [IsScalarTower K Aᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul 𝒜 ℳ]

omit [SMulCommClass A Aᵐᵒᵖ M] in
/-- A one-dimensional supercenter is concentrated in a single parity. -/
theorem exists_le_grade_of_finrank_one
    (h1 : Module.finrank K (superCenterBimod 𝒜 ℳ) = 1) :
    ∃ i : ZMod 2, superCenterBimod 𝒜 ℳ ≤ ℳ i := by
  set Z := superCenterBimod 𝒜 ℳ with hZdef
  haveI : FiniteDimensional K Z :=
    FiniteDimensional.of_finrank_pos (by omega)
  set Z₀ := Z ⊓ ℳ 0 with hZ₀
  set Z₁ := Z ⊓ ℳ 1 with hZ₁
  have hZsup : Z = Z₀ ⊔ Z₁ := by
    apply le_antisymm
    · intro z hz
      rw [← evenPartMod_add_oddPartMod ℳ z]
      have hparts := parts_mem_superCenterBimod 𝒜 ℳ hz
      exact Submodule.add_mem_sup ⟨hparts.1, evenPartMod_mem ℳ z⟩
        ⟨hparts.2, oddPartMod_mem ℳ z⟩
    · exact sup_le inf_le_left inf_le_left
  have hdisj : Z₀ ⊓ Z₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h0 : x ∈ ℳ 0 := hx.1.2
    have h1' : x ∈ ℳ 1 := hx.2.2
    simpa using eq_zero_of_mem_zero_of_mem_one_mod ℳ h0 h1'
  haveI : FiniteDimensional K Z₀ :=
    Submodule.finiteDimensional_of_le (inf_le_left : Z₀ ≤ Z)
  haveI : FiniteDimensional K Z₁ :=
    Submodule.finiteDimensional_of_le (inf_le_left : Z₁ ≤ Z)
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq Z₀ Z₁
  rw [hdisj, finrank_bot, add_zero, ← hZsup, h1] at hadd
  have hcases : Module.finrank K Z₀ = 0 ∨ Module.finrank K Z₁ = 0 := by omega
  rcases hcases with h | h
  · refine ⟨1, ?_⟩
    have hbot : Z₀ = ⊥ := Submodule.finrank_eq_zero.mp h
    rw [hZsup, hbot, bot_sup_eq]
    exact inf_le_right
  · refine ⟨0, ?_⟩
    have hbot : Z₁ = ⊥ := Submodule.finrank_eq_zero.mp h
    rw [hZsup, hbot, sup_bot_eq]
    exact inf_le_right

variable [Invertible (2 : K)] [FiniteDimensional K A] [Nontrivial A]
variable [IsSuperCentral 𝒜] [IsGradedSimple 𝒜]

/-- **Proposition 2.1**: over a finite-dimensional central simple
superalgebra (field base, `2` invertible), the supercenter of an
irreducible super-bimodule is one-dimensional and concentrated in a
single parity. -/
theorem prop21 (hM : IsSimpleSuperBimod 𝒜 ℳ) :
    Module.finrank K (superCenterBimod 𝒜 ℳ) = 1 ∧
      ∃ i : ZMod 2, superCenterBimod 𝒜 ℳ ≤ ℳ i := by
  have h1 := finrank_superCenterBimod_of_simple 𝒜 ℳ hM
  exact ⟨h1, exists_le_grade_of_finrank_one 𝒜 ℳ h1⟩

end Concentration

end Superfusion

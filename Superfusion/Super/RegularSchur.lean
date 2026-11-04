/-
Superfusion / Super / RegularSchur

Milestone M4, part 1: **Schur for the regular super-bimodule** — a
`K`-linear endomorphism of `A` commuting with the `E`-action (left
multiplications and signed right multiplications) is a scalar, provided
`A` is supercentral.  This is the `End_E(A) = K` input to the density
proof of Wall's criterion (design record, M4: surjectivity of the Wall
map via Jacobson density, then injectivity by dimension count).

The mathematical heart is `mem_superCenter_of_comm_signed`: an element
`c` satisfying the mixed commutation identity
  `a c = c a - 2 (odd c)(odd a)`   for all `a`
(i.e. commuting with every `a` in the signed sense, without being assumed
homogeneous) lies in the supercenter — its even part commutes with
everything, its odd part commutes with evens and anticommutes with odds.
-/
import Superfusion.Super.Bimodule

namespace Superfusion

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-! ### The even projection and decomposition into parts -/

/-- The even projection of a superalgebra. -/
noncomputable def evenPart : A →ₗ[K] A :=
  (𝒜 0).subtype ∘ₗ
    DirectSum.component K (ZMod 2) (fun i => ↥(𝒜 i)) 0 ∘ₗ
      (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem evenPart_of_mem_zero {a : A} (ha : a ∈ 𝒜 0) : evenPart 𝒜 a = a := by
  show (DirectSum.decompose 𝒜 a 0 : A) = a
  rw [DirectSum.decompose_of_mem_same 𝒜 ha]

theorem evenPart_of_mem_one {a : A} (ha : a ∈ 𝒜 1) : evenPart 𝒜 a = 0 := by
  show (DirectSum.decompose 𝒜 a 0 : A) = 0
  rw [DirectSum.decompose_of_mem_ne 𝒜 ha (by decide)]

theorem evenPart_mem (a : A) : evenPart 𝒜 a ∈ 𝒜 0 := by
  show (DirectSum.decompose 𝒜 a 0 : A) ∈ 𝒜 0
  exact Submodule.coe_mem _

/-- Every element is the sum of its even and odd parts. -/
theorem evenPart_add_oddPart (a : A) : evenPart 𝒜 a + oddPart 𝒜 a = a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero, map_zero, add_zero]
  | @homogeneous i m =>
      rcases zmod2_cases i with hi | hi <;> subst hi
      · rw [evenPart_of_mem_zero 𝒜 m.2, oddPart_of_mem_zero 𝒜 m.2, add_zero]
      · rw [evenPart_of_mem_one 𝒜 m.2, oddPart_of_mem_one 𝒜 m.2, zero_add]
  | add x y hx hy =>
      rw [map_add, map_add, add_add_add_comm, hx, hy]

/-- Elements of `𝒜 0 + 𝒜 1` with equal sums have equal parts
(uniqueness of the decomposition). -/
theorem parts_eq_of_add_eq {x₀ y₀ x₁ y₁ : A}
    (hx₀ : x₀ ∈ 𝒜 0) (hy₀ : y₀ ∈ 𝒜 0) (hx₁ : x₁ ∈ 𝒜 1) (hy₁ : y₁ ∈ 𝒜 1)
    (h : x₀ + x₁ = y₀ + y₁) : x₀ = y₀ ∧ x₁ = y₁ := by
  have comp : ∀ {u₀ u₁ : A}, u₀ ∈ 𝒜 0 → u₁ ∈ 𝒜 1 →
      (DirectSum.decompose 𝒜 (u₀ + u₁) 0 : A) = u₀ := by
    intro u₀ u₁ h₀ h₁
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      DirectSum.decompose_of_mem_same 𝒜 h₀,
      DirectSum.decompose_of_mem_ne 𝒜 h₁ (by decide), add_zero]
  have h₀ : x₀ = y₀ := by
    have := congrArg (fun z => (DirectSum.decompose 𝒜 z 0 : A)) h
    rwa [comp hx₀ hx₁, comp hy₀ hy₁] at this
  refine ⟨h₀, ?_⟩
  have := h
  rw [h₀] at this
  exact add_left_cancel this

/-! ### The mixed commutation identity forces supercentrality -/

/-- An element commuting with every `a` in the signed sense,
`a c = c a - 2 (odd c)(odd a)`, lies in the supercenter (no homogeneity
assumed: the identity forces the even part to commute with everything and
the odd part to supercommute). -/
theorem mem_superCenter_of_comm_signed {c : A}
    (hc : ∀ a : A, a * c = c * a - (2 : ℤ) • (oddPart 𝒜 c * oddPart 𝒜 a)) :
    c ∈ superCenter 𝒜 := by
  set c₀ := evenPart 𝒜 c with hc₀
  set c₁ := oddPart 𝒜 c with hc₁
  have hsum : c₀ + c₁ = c := evenPart_add_oddPart 𝒜 c
  have hmem₀ : c₀ ∈ 𝒜 0 := evenPart_mem 𝒜 c
  have hmem₁ : c₁ ∈ 𝒜 1 := oddPart_mem 𝒜 c
  -- component identities for homogeneous b
  have even_case : ∀ ⦃b : A⦄, b ∈ 𝒜 0 → b * c₀ = c₀ * b ∧ b * c₁ = c₁ * b := by
    intro b hb
    have h := hc b
    rw [oddPart_of_mem_zero 𝒜 hb, mul_zero, smul_zero, sub_zero, ← hsum,
      mul_add, add_mul] at h
    exact parts_eq_of_add_eq 𝒜 (SetLike.mul_mem_graded hb hmem₀)
      (SetLike.mul_mem_graded hmem₀ hb)
      (SetLike.mul_mem_graded hb hmem₁)
      (SetLike.mul_mem_graded hmem₁ hb) h
  have odd_case : ∀ ⦃b : A⦄, b ∈ 𝒜 1 →
      b * c₁ = c₁ * b - (2 : ℤ) • (c₁ * b) ∧ b * c₀ = c₀ * b := by
    intro b hb
    have h := hc b
    rw [oddPart_of_mem_one 𝒜 hb, ← hsum, mul_add, add_mul] at h
    -- rearrange both sides as (grade 0) + (grade 1)
    have h' : b * c₁ + b * c₀ =
        (c₁ * b - (2 : ℤ) • (c₁ * b)) + c₀ * b := by
      rw [add_comm (b * c₁)]
      rw [h]
      abel
    have mem10 : b * c₁ ∈ 𝒜 0 :=
      (show ((1 : ZMod 2) + 1) = 0 from by decide) ▸
        SetLike.mul_mem_graded hb hmem₁
    have mem10' : c₁ * b - (2 : ℤ) • (c₁ * b) ∈ 𝒜 0 := by
      refine Submodule.sub_mem _ ?_ (zsmul_mem ?_ 2) <;>
        exact (show ((1 : ZMod 2) + 1) = 0 from by decide) ▸
          SetLike.mul_mem_graded hmem₁ hb
    have mem01 : b * c₀ ∈ 𝒜 1 :=
      (show ((1 : ZMod 2) + 0) = 1 from by decide) ▸
        SetLike.mul_mem_graded hb hmem₀
    have mem01' : c₀ * b ∈ 𝒜 1 :=
      (show ((0 : ZMod 2) + 1) = 1 from by decide) ▸
        SetLike.mul_mem_graded hmem₀ hb
    exact parts_eq_of_add_eq 𝒜 mem10 mem10' mem01 mem01' h'
  -- assemble supercentrality of the two parts
  have h₀ : IsSupercentral 𝒜 0 c₀ := by
    intro j b hb
    rcases zmod2_cases j with hj | hj <;> subst hj
    · have := (even_case hb).1
      simpa using this.symm
    · have := (odd_case hb).2
      simpa using this.symm
  have h₁ : IsSupercentral 𝒜 1 c₁ := by
    intro j b hb
    rcases zmod2_cases j with hj | hj <;> subst hj
    · have := (even_case hb).2
      simpa using this.symm
    · have h := (odd_case hb).1
      have hneg : c₁ * b = -(b * c₁) := by
        rw [h]
        abel
      rw [show ((1 : ZMod 2) * 1) = 1 from by decide]
      simpa [sgn_one, units_sign_eq, neg_smul] using hneg
  rw [← hsum]
  exact Submodule.add_mem_sup ⟨hmem₀, h₀⟩ ⟨hmem₁, h₁⟩

/-! ### Schur for the regular bimodule -/

/-- **Schur for the regular super-bimodule** (the `End_E(A) = K` half of
Wall's criterion): if `A` is supercentral, a `K`-linear endomorphism of
`A` commuting with all left multiplications and all signed right
multiplications is multiplication by a scalar. -/
theorem exists_algebraMap_of_regular_comm [IsSuperCentral 𝒜]
    (f : Module.End K A)
    (hl : ∀ a x : A, f (a * x) = a * f x)
    (hr : ∀ b x : A, f (SuperOp.mulMap 𝒜 b x) = SuperOp.mulMap 𝒜 b (f x)) :
    ∃ c : K, f = algebraMap K (Module.End K A) c := by
  have hf : ∀ a : A, f a = a * f 1 := fun a => by
    have := hl a 1
    rwa [mul_one] at this
  have hmul1 : ∀ b : A, SuperOp.mulMap 𝒜 b (1 : A) = b := fun b => by
    rw [SuperOp.mulMap_apply, oddPart_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜),
      zero_mul, smul_zero, sub_zero, one_mul]
  have hcomm : ∀ b : A,
      b * f 1 = f 1 * b - (2 : ℤ) • (oddPart 𝒜 (f 1) * oddPart 𝒜 b) := by
    intro b
    have h := hr b 1
    rw [hmul1 b, SuperOp.mulMap_apply, hf b] at h
    exact h
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp
    (IsSuperCentral.superCenter_le_one (mem_superCenter_of_comm_signed 𝒜 hcomm))
  refine ⟨c, LinearMap.ext fun a => ?_⟩
  rw [Module.algebraMap_end_apply, hf a, ← hc, ← Algebra.commutes c a,
    ← Algebra.smul_def]

end Superfusion

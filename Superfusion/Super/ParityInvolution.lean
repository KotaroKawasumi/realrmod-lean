/-
Superfusion / Super / ParityInvolution

Milestone M4, part 2a: the parity involution `J = evenPart - oddPart`
(an algebra automorphism with `J² = id`), and the first half of the
simplicity of the regular super-bimodule: a `J`-stable submodule closed
under left multiplications and signed right multiplications is a
homogeneous two-sided ideal, hence `⊥` or `⊤` when `A` is graded-simple.

This is where the characteristic-2 caveat enters: recovering the even and
odd parts from `J` uses `⅟2` (`Invertible (2 : K)`), which holds for the
paper's fields `ℝ, ℂ`.  (In characteristic 2 the super theory degenerates
and Wall's criterion is a different statement.)

The remaining half of simplicity — a non-`J`-stable submodule leads to an
odd supercentral idempotent-part and a contradiction with supercentrality
— is part 2b.
-/
import Superfusion.Super.RegularSchur

namespace Superfusion

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-! ### Grades are disjoint -/

theorem eq_zero_of_mem_zero_of_mem_one {x : A} (h0 : x ∈ 𝒜 0) (h1 : x ∈ 𝒜 1) :
    x = 0 := by
  have hx := DirectSum.decompose_of_mem_same 𝒜 h0
  have h' := DirectSum.decompose_of_mem_ne 𝒜 h1
    (show (1 : ZMod 2) ≠ 0 from by decide)
  rw [h'] at hx
  exact hx.symm

/-! ### The parity involution -/

/-- The parity involution as a linear map: `x₀ + x₁ ↦ x₀ - x₁`. -/
noncomputable def parityMap : A →ₗ[K] A := evenPart 𝒜 - oddPart 𝒜

theorem parityMap_apply (x : A) :
    parityMap 𝒜 x = evenPart 𝒜 x - oddPart 𝒜 x := rfl

theorem parityMap_of_mem_zero {x : A} (hx : x ∈ 𝒜 0) : parityMap 𝒜 x = x := by
  rw [parityMap_apply, evenPart_of_mem_zero 𝒜 hx, oddPart_of_mem_zero 𝒜 hx,
    sub_zero]

theorem parityMap_of_mem_one {x : A} (hx : x ∈ 𝒜 1) : parityMap 𝒜 x = -x := by
  rw [parityMap_apply, evenPart_of_mem_one 𝒜 hx, oddPart_of_mem_one 𝒜 hx,
    zero_sub]

/-- The parity map preserves the grading. -/
theorem parityMap_mem {i : ZMod 2} {x : A} (hx : x ∈ 𝒜 i) :
    parityMap 𝒜 x ∈ 𝒜 i := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [parityMap_of_mem_zero 𝒜 hx]
    exact hx
  · rw [parityMap_of_mem_one 𝒜 hx]
    exact neg_mem hx

theorem parityMap_one : parityMap 𝒜 1 = 1 :=
  parityMap_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜)

theorem parityMap_algebraMap (r : K) :
    parityMap 𝒜 (algebraMap K A r) = algebraMap K A r :=
  parityMap_of_mem_zero 𝒜 (algebraMap_mem_grade_zero 𝒜 r)

theorem parityMap_parityMap (x : A) : parityMap 𝒜 (parityMap 𝒜 x) = x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero, map_zero]
  | @homogeneous i m =>
      rcases zmod2_cases i with hi | hi <;> subst hi
      · rw [parityMap_of_mem_zero 𝒜 m.2, parityMap_of_mem_zero 𝒜 m.2]
      · rw [parityMap_of_mem_one 𝒜 m.2, map_neg, parityMap_of_mem_one 𝒜 m.2,
          neg_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem parityMap_mul (x y : A) :
    parityMap 𝒜 (x * y) = parityMap 𝒜 x * parityMap 𝒜 y := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add u u' hu hu' => rw [add_mul, map_add, map_add, hu, hu', add_mul]
  | @homogeneous i mu =>
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add v v' hv hv' => rw [mul_add, map_add, map_add, hv, hv', mul_add]
    | @homogeneous j mv =>
        rcases zmod2_cases i with hi | hi <;> rcases zmod2_cases j with hj | hj <;>
            subst hi <;> subst hj
        · rw [parityMap_of_mem_zero 𝒜 mu.2, parityMap_of_mem_zero 𝒜 mv.2,
            parityMap_of_mem_zero 𝒜 (SetLike.mul_mem_graded mu.2 mv.2)]
        · have hmem : (mu : A) * (mv : A) ∈ 𝒜 1 := by
            have := SetLike.mul_mem_graded mu.2 mv.2
            rwa [show ((0 : ZMod 2) + 1) = 1 from by decide] at this
          rw [parityMap_of_mem_zero 𝒜 mu.2, parityMap_of_mem_one 𝒜 mv.2,
            parityMap_of_mem_one 𝒜 hmem, mul_neg]
        · have hmem : (mu : A) * (mv : A) ∈ 𝒜 1 := by
            have := SetLike.mul_mem_graded mu.2 mv.2
            rwa [show ((1 : ZMod 2) + 0) = 1 from by decide] at this
          rw [parityMap_of_mem_one 𝒜 mu.2, parityMap_of_mem_zero 𝒜 mv.2,
            parityMap_of_mem_one 𝒜 hmem, neg_mul]
        · have hmem : (mu : A) * (mv : A) ∈ 𝒜 0 := by
            have := SetLike.mul_mem_graded mu.2 mv.2
            rwa [show ((1 : ZMod 2) + 1) = 0 from by decide] at this
          rw [parityMap_of_mem_one 𝒜 mu.2, parityMap_of_mem_one 𝒜 mv.2,
            parityMap_of_mem_zero 𝒜 hmem, neg_mul_neg]

/-- **The parity involution** `J : A ≃ₐ[K] A`, `J(x₀ + x₁) = x₀ - x₁`. -/
noncomputable def parityInvolution : A ≃ₐ[K] A :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofLinear (parityMap 𝒜) (parityMap 𝒜)
      (LinearMap.ext fun x => parityMap_parityMap 𝒜 x)
      (LinearMap.ext fun x => parityMap_parityMap 𝒜 x))
    (parityMap_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜))
    (parityMap_mul 𝒜)

theorem parityInvolution_apply (x : A) :
    parityInvolution 𝒜 x = evenPart 𝒜 x - oddPart 𝒜 x := rfl

/-- Recovering the even part from `J` (this is where `⅟2` enters). -/
theorem evenPart_eq_of_invertible [Invertible (2 : K)] (x : A) :
    evenPart 𝒜 x = ⅟(2 : K) • (x + parityInvolution 𝒜 x) := by
  have hx := evenPart_add_oddPart 𝒜 x
  have h : x + parityInvolution 𝒜 x = (2 : K) • evenPart 𝒜 x := by
    rw [parityInvolution_apply, two_smul]
    nth_rewrite 1 [← hx]
    abel
  rw [h, invOf_smul_smul]

/-- Recovering the odd part from `J`. -/
theorem oddPart_eq_of_invertible [Invertible (2 : K)] (x : A) :
    oddPart 𝒜 x = ⅟(2 : K) • (x - parityInvolution 𝒜 x) := by
  have hx := evenPart_add_oddPart 𝒜 x
  have h : x - parityInvolution 𝒜 x = (2 : K) • oddPart 𝒜 x := by
    rw [parityInvolution_apply, two_smul]
    nth_rewrite 1 [← hx]
    abel
  rw [h, invOf_smul_smul]

/-! ### J-stable closed submodules are homogeneous two-sided ideals -/

/-- **The `J`-stable half of simplicity**: a submodule closed under left
multiplications, signed right multiplications, and the parity involution
is `⊥` or `⊤` when `A` is graded-simple. -/
theorem eq_bot_or_top_of_closed_of_parity_stable [Invertible (2 : K)]
    [IsGradedSimple 𝒜] (N : Submodule K A)
    (hl : ∀ a : A, ∀ x ∈ N, a * x ∈ N)
    (hr : ∀ b : A, ∀ x ∈ N, SuperOp.mulMap 𝒜 b x ∈ N)
    (hJ : ∀ x ∈ N, parityInvolution 𝒜 x ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  have heven : ∀ x ∈ N, evenPart 𝒜 x ∈ N := fun x hx => by
    rw [evenPart_eq_of_invertible]
    exact N.smul_mem _ (N.add_mem hx (hJ x hx))
  have hodd : ∀ x ∈ N, oddPart 𝒜 x ∈ N := fun x hx => by
    rw [oddPart_eq_of_invertible]
    exact N.smul_mem _ (N.sub_mem hx (hJ x hx))
  -- closure under plain right multiplication, one grade at a time
  have key : ∀ k : ZMod 2, ∀ x ∈ N, x ∈ 𝒜 k → ∀ b : A, x * b ∈ N := by
    intro k x hxN hxk b
    rw [← evenPart_add_oddPart 𝒜 b, mul_add]
    refine N.add_mem ?_ ?_
    · have h := SuperOp.mulMap_of_mem 𝒜 (evenPart_mem 𝒜 b) hxk
      simp only [zero_mul, sgn_zero, Units.val_one, one_smul] at h
      exact h ▸ hr _ x hxN
    · have h := SuperOp.mulMap_of_mem 𝒜 (oddPart_mem 𝒜 b) hxk
      have h2 : x * oddPart 𝒜 b =
          ((sgn (1 * k) : ℤˣ) : ℤ) • SuperOp.mulMap 𝒜 (oddPart 𝒜 b) x := by
        rw [h, smul_smul, ← Units.val_mul, sgn_mul_self', Units.val_one,
          one_smul]
      rw [h2]
      exact zsmul_mem (hr _ x hxN) _
  have hr' : ∀ x ∈ N, ∀ b : A, x * b ∈ N := by
    intro x hx b
    rw [← evenPart_add_oddPart 𝒜 x, add_mul]
    exact N.add_mem (key 0 _ (heven x hx) (evenPart_mem 𝒜 x) b)
      (key 1 _ (hodd x hx) (oddPart_mem 𝒜 x) b)
  -- package as a homogeneous two-sided ideal
  let I : TwoSidedIdeal A := TwoSidedIdeal.mk' N N.zero_mem
    (fun hx hy => N.add_mem hx hy) (fun hx => N.neg_mem hx)
    (fun {x y} hy => hl x y hy) (fun {x y} hx => hr' x hx y)
  have hmemI : ∀ z : A, z ∈ I ↔ z ∈ N := fun z =>
    TwoSidedIdeal.mem_mk' _ _ _ _ _ _ z
  have hIhom : TwoSidedIdeal.IsHomogeneous 𝒜 I := by
    intro a ha i
    rw [hmemI] at ha ⊢
    rcases zmod2_cases i with hi | hi <;> subst hi
    · exact heven a ha
    · exact hodd a ha
  rcases IsGradedSimple.eq_bot_or_eq_top I hIhom with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hzI := (hmemI z).mpr hz
    rw [h] at hzI
    exact (TwoSidedIdeal.mem_bot A).mp hzI
  · right
    rw [Submodule.eq_top_iff']
    intro z
    refine (hmemI z).mp ?_
    rw [h]
    exact TwoSidedIdeal.mem_top A

end Superfusion

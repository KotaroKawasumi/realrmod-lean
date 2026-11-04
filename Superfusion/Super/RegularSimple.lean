/-
Superfusion / Super / RegularSimple

Milestone M4, part 2b: **simplicity of the regular super-bimodule**.
For a central simple superalgebra (with `2` invertible), every submodule
of `A` closed under left multiplications and signed right multiplications
is `⊥` or `⊤`.

Proof.  Let `N' = J(N)`; it is closed as well (`J` conjugates the two
actions into themselves).  `N ⊔ N'` and `N ⊓ N'` are closed and
`J`-stable, so by part 2a each is `⊥` or `⊤`; the only surviving case is
`N ⊔ N' = ⊤`, `N ⊓ N' = ⊥`.  Writing `1 = e + f` with `e ∈ N`, `f ∈ N'`,
uniqueness of decompositions gives `J e = f` and `e f = 0`, whence
`evenPart e = ½` and `e = ½ + e₁` with `e₁` odd.  Closure of `N, N'`
under the two actions then forces `e₁` to commute with even elements and
anticommute with odd ones — an odd supercentral element — so `e₁ ∈ K·1`
by supercentrality, hence `e₁ ∈ 𝒜 0 ⊓ 𝒜 1 = 0`.  Then `e = f = ½` and
`0 = e f = ¼`, so `A` is trivial and `N = ⊥`.  ∎
-/
import Superfusion.Super.ParityInvolution

namespace Superfusion

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-! ### The parity involution and the parts -/

theorem oddPart_parityInvolution (x : A) :
    oddPart 𝒜 (parityInvolution 𝒜 x) = -oddPart 𝒜 x := by
  rw [parityInvolution_apply, map_sub, oddPart_of_mem_zero 𝒜 (evenPart_mem 𝒜 x),
    oddPart_of_mem_one 𝒜 (oddPart_mem 𝒜 x), zero_sub]

theorem parityInvolution_parityInvolution (x : A) :
    parityInvolution 𝒜 (parityInvolution 𝒜 x) = x :=
  parityMap_parityMap 𝒜 x

/-- `J` conjugates the signed right multiplications into themselves. -/
theorem parity_mulMap (b y : A) :
    parityInvolution 𝒜 (SuperOp.mulMap 𝒜 b y) =
      SuperOp.mulMap 𝒜 (parityInvolution 𝒜 b) (parityInvolution 𝒜 y) := by
  rw [SuperOp.mulMap_apply, map_sub, map_zsmul, map_mul, map_mul,
    show parityInvolution 𝒜 (oddPart 𝒜 y) = -oddPart 𝒜 y from
      parityMap_of_mem_one 𝒜 (oddPart_mem 𝒜 y),
    show parityInvolution 𝒜 (oddPart 𝒜 b) = -oddPart 𝒜 b from
      parityMap_of_mem_one 𝒜 (oddPart_mem 𝒜 b),
    neg_mul_neg, SuperOp.mulMap_apply, oddPart_parityInvolution,
    oddPart_parityInvolution, neg_mul_neg]

/-! ### Simplicity of the regular super-bimodule -/

/-- **Simplicity of the regular super-bimodule**: for a supercentral,
graded-simple superalgebra over a base with `2` invertible, every
submodule closed under left multiplications and signed right
multiplications is `⊥` or `⊤`. -/
theorem eq_bot_or_top_of_closed [Invertible (2 : K)]
    [IsGradedSimple 𝒜] [IsSuperCentral 𝒜] (N : Submodule K A)
    (hl : ∀ a : A, ∀ x ∈ N, a * x ∈ N)
    (hr : ∀ b : A, ∀ x ∈ N, SuperOp.mulMap 𝒜 b x ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  set N' : Submodule K A := N.map (parityInvolution 𝒜).toLinearMap with hN'def
  have memN' : ∀ y : A, y ∈ N' ↔ parityInvolution 𝒜 y ∈ N := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : parityInvolution 𝒜 (parityInvolution 𝒜 x) = x :=
        parityMap_parityMap 𝒜 x
      rw [show (parityInvolution 𝒜).toLinearMap x = parityInvolution 𝒜 x
        from rfl, this]
      exact hx
    · intro h
      exact ⟨_, h, parityMap_parityMap 𝒜 y⟩
  have hl' : ∀ a : A, ∀ y ∈ N', a * y ∈ N' := by
    intro a y hy
    rw [memN'] at hy ⊢
    rw [map_mul]
    exact hl _ _ hy
  have hr' : ∀ b : A, ∀ y ∈ N', SuperOp.mulMap 𝒜 b y ∈ N' := by
    intro b y hy
    rw [memN'] at hy ⊢
    rw [parity_mulMap]
    exact hr _ _ hy
  -- the sup and the inf are closed and J-stable
  have hlsup : ∀ a : A, ∀ x ∈ N ⊔ N', a * x ∈ N ⊔ N' := by
    intro a x hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    rw [mul_add]
    exact Submodule.add_mem_sup (hl a u hu) (hl' a v hv)
  have hrsup : ∀ b : A, ∀ x ∈ N ⊔ N', SuperOp.mulMap 𝒜 b x ∈ N ⊔ N' := by
    intro b x hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    rw [map_add]
    exact Submodule.add_mem_sup (hr b u hu) (hr' b v hv)
  have hsupJ : ∀ x ∈ N ⊔ N', parityInvolution 𝒜 x ∈ N ⊔ N' := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    rw [map_add]
    refine (N ⊔ N').add_mem ?_ ?_
    · exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hu)
    · exact Submodule.mem_sup_left ((memN' v).mp hv)
  have hlinf : ∀ a : A, ∀ x ∈ N ⊓ N', a * x ∈ N ⊓ N' :=
    fun a x hx => ⟨hl a x hx.1, hl' a x hx.2⟩
  have hrinf : ∀ b : A, ∀ x ∈ N ⊓ N', SuperOp.mulMap 𝒜 b x ∈ N ⊓ N' :=
    fun b x hx => ⟨hr b x hx.1, hr' b x hx.2⟩
  have hinfJ : ∀ x ∈ N ⊓ N', parityInvolution 𝒜 x ∈ N ⊓ N' := by
    intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    refine ⟨(memN' x).mp hx.2, (memN' _).mpr ?_⟩
    rw [parityInvolution_parityInvolution]
    exact hx.1
  -- dichotomies for the J-stable combinations
  rcases eq_bot_or_top_of_closed_of_parity_stable 𝒜 (N ⊔ N') hlsup hrsup hsupJ
    with hsup | hsup
  · left
    exact le_bot_iff.mp (hsup ▸ le_sup_left)
  rcases eq_bot_or_top_of_closed_of_parity_stable 𝒜 (N ⊓ N') hlinf hrinf hinfJ
    with hinf | hinf
  swap
  · right
    exact top_le_iff.mp (hinf ▸ inf_le_left)
  -- main case: N ⊔ N' = ⊤ and N ⊓ N' = ⊥
  obtain ⟨e, heN, f, hfN', hef⟩ :=
    Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top : (1 : A) ∈ N ⊔ N')
  -- J swaps e and f
  have h1 : parityInvolution 𝒜 e + parityInvolution 𝒜 f = 1 := by
    rw [← map_add, hef, map_one]
  have hJf : parityInvolution 𝒜 f = e := by
    have hdiff : e - parityInvolution 𝒜 f ∈ N ⊓ N' := by
      constructor
      · exact N.sub_mem heN ((memN' f).mp hfN')
      · have heq : e - parityInvolution 𝒜 f = parityInvolution 𝒜 e - f := by
          rw [sub_eq_sub_iff_add_eq_add, hef]
          exact h1.symm
        rw [heq]
        exact N'.sub_mem (Submodule.mem_map_of_mem heN) hfN'
    rw [hinf] at hdiff
    have := (Submodule.mem_bot K).mp hdiff
    exact (sub_eq_zero.mp this).symm
  have hJe : parityInvolution 𝒜 e = f := by
    rw [← hJf, parityInvolution_parityInvolution]
  -- the even part of e is ½
  have he₀ : evenPart 𝒜 e = ⅟(2 : K) • (1 : A) := by
    rw [evenPart_eq_of_invertible, hJe, hef]
  set e₁ := oddPart 𝒜 e with he₁def
  have hesplit : e = ⅟(2 : K) • (1 : A) + e₁ := by
    rw [← he₀]
    exact (evenPart_add_oddPart 𝒜 e).symm
  have hf : f = ⅟(2 : K) • (1 : A) - e₁ := by
    rw [← hJe, parityInvolution_apply, he₀]
  have hscal : ∀ b : A, (⅟(2 : K) • (1 : A)) * b = b * (⅟(2 : K) • (1 : A)) := by
    intro b
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  -- e₁ commutes with even elements
  have hcomm_even : ∀ b ∈ 𝒜 0, e₁ * b = b * e₁ := by
    intro b hb
    have hm : SuperOp.mulMap 𝒜 b e = e * b := by
      rw [SuperOp.mulMap_apply, oddPart_of_mem_zero 𝒜 hb, mul_zero, smul_zero,
        sub_zero]
    have hm' : SuperOp.mulMap 𝒜 b f = f * b := by
      rw [SuperOp.mulMap_apply, oddPart_of_mem_zero 𝒜 hb, mul_zero, smul_zero,
        sub_zero]
    have hN1 : e₁ * b - b * e₁ ∈ N := by
      have h2 : e₁ * b - b * e₁ = e * b - b * e := by
        rw [hesplit, add_mul, mul_add, hscal b]
        abel
      rw [h2, ← hm]
      exact N.sub_mem (hr b e heN) (hl b e heN)
    have hN'1 : e₁ * b - b * e₁ ∈ N' := by
      have h2 : e₁ * b - b * e₁ = -(f * b - b * f) := by
        rw [hf, sub_mul, mul_sub, hscal b]
        abel
      rw [h2, ← hm']
      exact N'.neg_mem (N'.sub_mem (hr' b f hfN') (hl' b f hfN'))
    have hmem : e₁ * b - b * e₁ ∈ N ⊓ N' := ⟨hN1, hN'1⟩
    rw [hinf] at hmem
    exact sub_eq_zero.mp ((Submodule.mem_bot K).mp hmem)
  -- e₁ anticommutes with odd elements
  have hcomm_odd : ∀ b ∈ 𝒜 1, e₁ * b = -(b * e₁) := by
    intro b hb
    have hm : SuperOp.mulMap 𝒜 b e = e * b - (2 : ℤ) • (e₁ * b) := by
      rw [SuperOp.mulMap_apply, oddPart_of_mem_one 𝒜 hb, ← he₁def]
    have hof : oddPart 𝒜 f = -e₁ := by
      rw [hf, map_sub, map_smul, oddPart_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜),
        oddPart_of_mem_one 𝒜 (oddPart_mem 𝒜 e), smul_zero, zero_sub]
    have hm' : SuperOp.mulMap 𝒜 b f = f * b + (2 : ℤ) • (e₁ * b) := by
      rw [SuperOp.mulMap_apply, oddPart_of_mem_one 𝒜 hb, hof, neg_mul, smul_neg,
        sub_neg_eq_add]
    have hN1 : e₁ * b + b * e₁ ∈ N := by
      have h2 : e₁ * b + b * e₁ = b * e - (e * b - (2 : ℤ) • (e₁ * b)) := by
        rw [hesplit, add_mul, mul_add, hscal b]
        abel
      rw [h2, ← hm]
      exact N.sub_mem (hl b e heN) (hr b e heN)
    have hN'1 : e₁ * b + b * e₁ ∈ N' := by
      have h2 : e₁ * b + b * e₁ = (f * b + (2 : ℤ) • (e₁ * b)) - b * f := by
        rw [hf, sub_mul, mul_sub, hscal b]
        abel
      rw [h2, ← hm']
      exact N'.sub_mem (hr' b f hfN') (hl' b f hfN')
    have hmem : e₁ * b + b * e₁ ∈ N ⊓ N' := ⟨hN1, hN'1⟩
    rw [hinf] at hmem
    exact eq_neg_of_add_eq_zero_left ((Submodule.mem_bot K).mp hmem)
  -- e₁ is an odd supercentral element, hence zero
  have hsc : IsSupercentral 𝒜 1 e₁ := by
    intro j b hb
    rcases zmod2_cases j with hj | hj <;> subst hj
    · have := hcomm_even b hb
      simpa using this
    · have := hcomm_odd b hb
      rw [show ((1 : ZMod 2) * 1) = 1 from by decide]
      simpa [sgn_one, units_sign_eq, neg_smul] using this
  have he₁0 : e₁ = 0 := by
    have hmem : e₁ ∈ superCenter 𝒜 :=
      Submodule.mem_sup_right ⟨oddPart_mem 𝒜 e, hsc⟩
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp
      (IsSuperCentral.superCenter_le_one hmem)
    exact eq_zero_of_mem_zero_of_mem_one 𝒜
      (hc ▸ algebraMap_mem_grade_zero 𝒜 c) (oddPart_mem 𝒜 e)
  -- e f = 0 then forces 1 = 0
  have hef0 : e * f = 0 := by
    have hdecomp : e * e + e * f = e := by rw [← mul_add, hef, mul_one]
    have h2 : e * f ∈ N := by
      have : e * f = e - e * e := eq_sub_of_add_eq' hdecomp
      rw [this]
      exact N.sub_mem heN (hl e e heN)
    have hmem : e * f ∈ N ⊓ N' := ⟨h2, hl' e f hfN'⟩
    rw [hinf] at hmem
    exact (Submodule.mem_bot K).mp hmem
  have h10 : (1 : A) = 0 := by
    have he' : e = ⅟(2 : K) • (1 : A) := by rw [hesplit, he₁0, add_zero]
    have hf' : f = ⅟(2 : K) • (1 : A) := by rw [hf, he₁0, sub_zero]
    have hq : ⅟(2 : K) • ⅟(2 : K) • (1 : A) = 0 := by
      calc ⅟(2 : K) • ⅟(2 : K) • (1 : A) = e * f := by
            rw [he', hf', smul_mul_assoc, mul_smul_comm, one_mul]
        _ = 0 := hef0
    have h4 := congrArg (fun z => (2 : K) • (2 : K) • z) hq
    simpa [smul_smul, mul_invOf_self, ← mul_assoc,
      mul_mul_mul_comm (2 : K) (2 : K)] using h4
  left
  rw [Submodule.eq_bot_iff]
  intro x _
  calc x = x * 1 := (mul_one x).symm
    _ = x * 0 := by rw [h10]
    _ = 0 := mul_zero x

end Superfusion

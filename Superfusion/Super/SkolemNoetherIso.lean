/-
Superfusion / Super / SkolemNoetherIso

Milestone M7d-5a: **super Skolem–Noether existence for surjective
homogeneous maps** — the case that powers the pentagon data (p, χ).

For two surjective grade-preserving algebra maps
`φ, φ' : A → B` between central simple superalgebras, the twisted
super-bimodule (`B` with `a • x • b = φ'(a) x φ(b)`, M6) is
IRREDUCIBLE: a submodule closed under the twisted actions is closed
under *all* left and signed right multiplications of `B` (by
surjectivity), so the regular-bimodule simplicity of `B` (M4-2b)
applies.  This removes the obstruction recorded for M7f-3 in the
iso case.  Prop 2.1 (M5) then yields a homogeneous intertwiner `t`,
unique up to scalar, with
`φ'(b) t = (-1)^{|b||t|} t φ(b)`, and `t` is INVERTIBLE: its right
annihilator is a homogeneous two-sided ideal not containing `1`,
hence zero by graded simplicity, so left multiplication by `t` is
injective, hence bijective in finite dimension.

This is the paper's Cor 2.2 existence clause in the surjective
case — with the invertibility argument spelled out (the annihilator
trick), filling the compressed clause noted in the M7f-3 record.
-/
import Superfusion.Super.SkolemNoether
import Superfusion.Super.RegularSimple

namespace Superfusion

open Module

section Iso

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable (φ φ' : A →ₐ[K] B)
variable (hφ : IsHomogeneousHom 𝒜 ℬ φ) (hφ' : IsHomogeneousHom 𝒜 ℬ φ')

/-! ### Parts transfer along homogeneous maps -/

omit [Invertible (2 : K)] in
include hφ in
/-- A homogeneous algebra map commutes with the odd projection. -/
theorem oddPart_apply_of_isHomogeneousHom (b : A) :
    φ (oddPart 𝒜 b) = oddPart ℬ (φ b) := by
  have hsplit : φ b = φ (evenPart 𝒜 b) + φ (oddPart 𝒜 b) := by
    rw [← map_add, evenPart_add_oddPart]
  have h0 : φ (evenPart 𝒜 b) ∈ ℬ 0 := hφ 0 _ (evenPart_mem 𝒜 b)
  have h1 : φ (oddPart 𝒜 b) ∈ ℬ 1 := hφ 1 _ (oddPart_mem 𝒜 b)
  have := parts_eq_of_add_eq ℬ h0 (evenPart_mem ℬ (φ b)) h1 (oddPart_mem ℬ (φ b))
    (by rw [← hsplit, evenPart_add_oddPart])
  exact this.2

/-! ### Irreducibility of the twisted bimodule for surjective maps -/

include hφ hφ' in
/-- **The twisted bimodule of two surjective homogeneous maps is
irreducible** (M7d-5a): the twisted actions sweep out all left and
signed right multiplications of `B`, so regular simplicity applies.
This removes the M7f-3 obstruction in the surjective case. -/
theorem isSimpleSuperBimod_twisted_of_surjective
    [IsSuperCentral ℬ] [IsGradedSimple ℬ] [Nontrivial B]
    (hsφ : Function.Surjective φ) (hsφ' : Function.Surjective φ') :
    IsSimpleSuperBimod 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ') := by
  refine ⟨inferInstanceAs (Nontrivial B), fun N hlN hrN => ?_⟩
  -- read N as a submodule of B and apply regular simplicity
  set N' : Submodule K B := N with hN'
  refine eq_bot_or_top_of_closed ℬ N' ?_ ?_
  · -- left multiplications: c = φ' a
    intro c x hx
    obtain ⟨a, rfl⟩ := hsφ' c
    exact hlN a x hx
  · -- signed right multiplications: c = φ b, translated through the
    -- closed form of the twisted signed action
    intro c x hx
    obtain ⟨b, rfl⟩ := hsφ c
    have h := hrN b x hx
    -- closed forms agree: the twisted op-action is `x * φ b`, and
    -- `φ` commutes with the odd projections
    have htrans : signedRSMul 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')
        b (Twisted.of 𝒜 ℬ φ φ' hφ hφ' x)
        = Twisted.of 𝒜 ℬ φ φ' hφ hφ' (SuperOp.mulMap ℬ (φ b) x) := by
      rw [signedRSMul_apply, SuperOp.mulMap_apply,
        show oddPartMod (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')
            (Twisted.of 𝒜 ℬ φ φ' hφ hφ' x) = Twisted.of 𝒜 ℬ φ φ' hφ hφ' (oddPart ℬ x)
          from rfl,
        Twisted.op_smul_def 𝒜 ℬ φ φ' hφ hφ' b x,
        Twisted.op_smul_def 𝒜 ℬ φ φ' hφ hφ' (oddPart 𝒜 b) (oddPart ℬ x),
        oddPart_apply_of_isHomogeneousHom 𝒜 ℬ φ hφ b, map_sub, map_zsmul]
    have h' : signedRSMul 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')
        b (Twisted.of 𝒜 ℬ φ φ' hφ hφ' x) ∈ N := h
    rw [htrans] at h'
    exact h'

/-! ### Invertibility of a nonzero homogeneous intertwiner -/

omit [Invertible (2 : K)] [GradedAlgebra 𝒜] in
/-- Elements of `sgn` square to `1`, so the intertwining relation can be
rearranged to put `t` on the left. -/
private theorem mul_of_intertwines {j p : ZMod 2} {b : A} {t : B}
    (h : φ' b * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ b)) :
    t * φ b = ((sgn (j * p) : ℤˣ) : ℤ) • (φ' b * t) := by
  rw [h, smul_smul, ← Units.val_mul, sgn_mul_self', Units.val_one, one_smul]

omit [Invertible (2 : K)] in
/-- A nonzero homogeneous intertwiner between surjective homogeneous
maps is invertible: its right annihilator is a homogeneous two-sided
ideal avoiding `1`. -/
theorem isUnit_of_homogeneous_intertwiner
    [IsGradedSimple ℬ] [FiniteDimensional K B] [Nontrivial B]
    (hsφ : Function.Surjective φ)
    {p : ZMod 2} {t : B} (htp : t ∈ ℬ p) (ht0 : t ≠ 0)
    (hint : ∀ ⦃j : ZMod 2⦄ ⦃b : A⦄, b ∈ 𝒜 j →
      φ' b * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ b)) :
    IsUnit t := by
  -- the right annihilator
  set R : Submodule K B :=
    { carrier := {y : B | t * y = 0}
      add_mem' := fun {y} {z} hy hz => by
        show t * (y + z) = 0
        rw [mul_add, hy, hz, add_zero]
      zero_mem' := by show t * 0 = 0; rw [mul_zero]
      smul_mem' := fun c y hy => by
        show t * (c • y) = 0
        rw [mul_smul_comm, hy, smul_zero] } with hR
  have memR : ∀ y : B, y ∈ R ↔ t * y = 0 := fun y => Iff.rfl
  -- R is closed under left multiplication by every φ a (surjectivity of
  -- φ), hence by all of B; on homogeneous a this is the intertwining
  -- relation rearranged with t on the left
  have hleft : ∀ c : B, ∀ y ∈ R, c * y ∈ R := by
    intro c y hy
    obtain ⟨a, rfl⟩ := hsφ c
    have hkey : ∀ i : ZMod 2, ∀ a' ∈ 𝒜 i, t * (φ a' * y) = 0 := by
      intro i a' ha'
      have h := mul_of_intertwines φ φ' (hint ha')
      rw [← mul_assoc, h, smul_mul_assoc, mul_assoc, (memR y).mp hy,
        mul_zero, smul_zero]
    have hsplit : a = evenPart 𝒜 a + oddPart 𝒜 a :=
      (evenPart_add_oddPart 𝒜 a).symm
    show t * (φ a * y) = 0
    conv_lhs => rw [hsplit]
    rw [map_add, add_mul, mul_add,
      hkey 0 _ (evenPart_mem 𝒜 a), hkey 1 _ (oddPart_mem 𝒜 a),
      add_zero]
  have hright : ∀ c : B, ∀ y ∈ R, y * c ∈ R := by
    intro c y hy
    show t * (y * c) = 0
    rw [← mul_assoc, (memR y).mp hy, zero_mul]
  -- R is homogeneous: t is homogeneous, so the graded parts of y
  -- annihilate separately
  have hhom : ∀ y ∈ R, evenPart ℬ y ∈ R ∧ oddPart ℬ y ∈ R := by
    intro y hy
    have h0 : t * evenPart ℬ y ∈ ℬ (p + 0) :=
      SetLike.mul_mem_graded htp (evenPart_mem ℬ y)
    have h1 : t * oddPart ℬ y ∈ ℬ (p + 1) :=
      SetLike.mul_mem_graded htp (oddPart_mem ℬ y)
    have hsum : t * evenPart ℬ y + t * oddPart ℬ y = 0 := by
      rw [← mul_add, evenPart_add_oddPart]
      exact (memR y).mp hy
    rcases zmod2_cases p with hp | hp
    · rw [hp, zero_add] at h0
      rw [hp] at h1
      have h1' : t * oddPart ℬ y ∈ ℬ 1 := by
        have : (0 : ZMod 2) + 1 = 1 := by decide
        rwa [this] at h1
      exact parts_eq_of_add_eq ℬ h0 ((ℬ 0).zero_mem) h1'
        ((ℬ 1).zero_mem) (by rw [hsum, add_zero])
    · rw [hp] at h0 h1
      have h0' : t * evenPart ℬ y ∈ ℬ 1 := by
        have : (1 : ZMod 2) + 0 = 1 := by decide
        rwa [this] at h0
      have h1' : t * oddPart ℬ y ∈ ℬ 0 := by
        have : (1 : ZMod 2) + 1 = 0 := by decide
        rwa [this] at h1
      have := parts_eq_of_add_eq ℬ h1' ((ℬ 0).zero_mem) h0'
        ((ℬ 1).zero_mem) (by rw [add_comm] at hsum; rw [hsum, add_zero])
      exact ⟨this.2, this.1⟩
  -- graded simplicity: R = ⊥ (it misses 1)
  have hRbot : R = ⊥ := by
    -- package R as a homogeneous two-sided ideal of B
    let I : TwoSidedIdeal B := TwoSidedIdeal.mk' R R.zero_mem
      (fun hx hy => R.add_mem hx hy) (fun hx => R.neg_mem hx)
      (fun {x y} hy => hleft x y hy) (fun {x y} hx => hright y x hx)
    have hmemI : ∀ z : B, z ∈ I ↔ z ∈ R := fun z =>
      TwoSidedIdeal.mem_mk' _ _ _ _ _ _ z
    have hIhom : TwoSidedIdeal.IsHomogeneous ℬ I := by
      intro z hz i
      rw [hmemI] at hz ⊢
      rcases zmod2_cases i with hi | hi <;> subst hi
      · have h0 := (hhom z hz).1
        rwa [show evenPart ℬ z = (DirectSum.decompose ℬ z 0 : B) from rfl] at h0
      · have h1 := (hhom z hz).2
        rwa [show oddPart ℬ z = (DirectSum.decompose ℬ z 1 : B) from rfl] at h1
    rcases IsGradedSimple.eq_bot_or_eq_top I hIhom with h | h
    · rw [Submodule.eq_bot_iff]
      intro z hz
      have hzI := (hmemI z).mpr hz
      rw [h] at hzI
      exact (TwoSidedIdeal.mem_bot B).mp hzI
    · exfalso
      have h1 : (1 : B) ∈ I := h ▸ TwoSidedIdeal.mem_top B
      rw [hmemI, memR, mul_one] at h1
      exact ht0 h1
  -- left multiplication by t is injective, hence bijective
  have hinj : Function.Injective (LinearMap.mulLeft K t) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
    have : y ∈ R := by rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hy
    rw [hRbot, Submodule.mem_bot] at this
    exact this
  have hbij : Function.Bijective (LinearMap.mulLeft K t) :=
    ⟨hinj, (LinearMap.injective_iff_surjective
      (f := LinearMap.mulLeft K t)).mp hinj⟩
  obtain ⟨u, hu⟩ := hbij.2 1
  rw [LinearMap.mulLeft_apply] at hu
  -- from t * u = 1, get u * t = 1 by injectivity of left multiplication by t
  have hut : u * t = 1 := by
    have h1 : t * (u * t) = t * 1 := by rw [← mul_assoc, hu, one_mul, mul_one]
    exact hinj (by rwa [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply])
  exact ⟨⟨t, u, hu, hut⟩, rfl⟩

/-! ### The main theorem -/

include hφ hφ' in
/-- **Super Skolem–Noether existence, surjective case** (M7d-5a):
two surjective homogeneous algebra maps between central simple
superalgebras are intertwined by an invertible homogeneous element,
with a well-defined parity. -/
theorem superSkolemNoether_exists_of_surjective
    [FiniteDimensional K A] [Nontrivial A]
    [IsSuperCentral 𝒜] [IsGradedSimple 𝒜]
    [IsSuperCentral ℬ] [IsGradedSimple ℬ] [Nontrivial B]
    [FiniteDimensional K B]
    (hsφ : Function.Surjective φ) (hsφ' : Function.Surjective φ') :
    ∃ (p : ZMod 2) (t : B), t ∈ ℬ p ∧ IsUnit t ∧
      ∀ ⦃j : ZMod 2⦄ ⦃b : A⦄, b ∈ 𝒜 j →
        φ' b * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ b) := by
  have hirr := isSimpleSuperBimod_twisted_of_surjective 𝒜 ℬ φ φ' hφ hφ'
    hsφ hsφ'
  obtain ⟨hdim, i, hconc⟩ := superSkolemNoether_unique 𝒜 ℬ φ φ' hφ hφ' hirr
  -- extract a nonzero element of the one-dimensional supercenter
  have hne : superCenterBimod 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ') ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    exact one_ne_zero hdim.symm
  obtain ⟨z, hzmem, hz0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hne
  -- z is homogeneous of degree i
  have hzi := hconc hzmem
  -- read z back in B
  set t : B := (Twisted.of 𝒜 ℬ φ φ' hφ hφ').symm z with ht
  have htz : Twisted.of 𝒜 ℬ φ φ' hφ hφ' t = z := by
    rw [ht]
    exact (Twisted.of 𝒜 ℬ φ φ' hφ hφ').apply_symm_apply z
  have htp : t ∈ ℬ i := by
    have : z ∈ Twisted.grading 𝒜 ℬ φ φ' hφ hφ' i := hzi
    rwa [← htz] at this
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero] at htz
    exact hz0 htz.symm
  have hint : ∀ ⦃j : ZMod 2⦄ ⦃b : A⦄, b ∈ 𝒜 j →
      φ' b * t = ((sgn (j * i) : ℤˣ) : ℤ) • (t * φ b) := by
    intro j b hb
    exact intertwines_of_mem_superCenterBimod 𝒜 ℬ φ φ' hφ hφ'
      (htz ▸ hzmem) htp hb
  exact ⟨i, t, htp,
    isUnit_of_homogeneous_intertwiner 𝒜 ℬ φ φ' hsφ htp ht0 hint,
    hint⟩

end Iso

end Superfusion

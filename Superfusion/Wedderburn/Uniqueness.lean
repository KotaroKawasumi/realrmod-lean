/-
Superfusion / Wedderburn / Uniqueness

Milestone M10-8 of the graded Wedderburn arc (docs/wedderburn-design.md, "Extension:
M10-8 uniqueness and M10-9"): **Wedderburn uniqueness** — the super division algebra
`D` appearing in the graded Wedderburn theorem (`graded_wedderburn`, `Wedderburn/
MatrixRealization.lean`) is unique up to graded isomorphism.  This is the uniqueness
half; `graded_wedderburn` is the existence half.

Route (recovering `D` intrinsically as `(End_A ↥I)ᵐᵒᵖ` for a minimal homogeneous left
ideal `I`, and comparing the recovery at the two ends of a matrix-stabilized graded
isomorphism):

1. **Ideal transport.**  For minimal homogeneous left ideals `I, I'` of a graded-simple
   `A`, some homogeneous `y ∈ I'` has `I · y ≠ 0` (else `I` would lie in the two-sided
   annihilator of `I'`, forcing `I = ⊥` by graded simplicity — `leftIdealAnnihilator_eq_bot`
   from `Wedderburn/GradedIdeal.lean`).  Right multiplication by `y` is then a bijective,
   degree-`|y|`-shifting `A`-linear map `↥I → ↥I'` (graded Schur applied to its kernel and
   range), and conjugation by it carries `End_A ↥I`'s grading onto `End_A ↥I'`'s, degree for
   degree (the shift by `|y|` cancels).
2. **Column recovery.**  In `D.matrixSuper p q` the column ideal at a fixed index is a
   homogeneous left ideal; it is minimal (a direct matrix-unit argument, not the bimodule
   irreducibility of `Bimod/ColumnSimple.lean`, whose right-action closure hypothesis a
   left ideal does not supply).  Its endomorphism algebra is graded-isomorphic to `Dᵐᵒᵖ`
   (every `A`-endomorphism of the column commutes with left matrix-unit multiplication,
   hence is right multiplication by a fixed scalar; composition reverses the scalar order).
3. **Assembly.**  Transport the column ideal of one side along the given graded
   isomorphism to a minimal homogeneous left ideal of the other side's matrix algebra;
   chain `D ≅ (End_A ↥I_D)ᵐᵒᵖ ≅ (End_A ↥I_{D'})ᵐᵒᵖ ≅ D'` through Step 1's transport
   equivalence and Step 2's column recovery on both ends.
-/
import Superfusion.Wedderburn.MatrixRealization

namespace Superfusion

open Module

/-! ### Part 1: ideal transport between two minimal homogeneous left ideals -/

section IdealTransport

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-! #### The right-annihilator of a single homogeneous element -/

/-- The set of `a` with `a * y = 0`, for a fixed `y` — automatically a left ideal (closed
under left multiplication: `z • (a * y) = (z * a) * y`). -/
def singleAnnihilator (y : A) : Submodule A A where
  carrier := {a | a * y = 0}
  zero_mem' := zero_mul y
  add_mem' {a b} ha hb := by show (a + b) * y = 0; rw [add_mul, ha, hb, add_zero]
  smul_mem' c a ha := by
    show c * a * y = 0
    rw [mul_assoc]
    show c * (a * y) = 0
    rw [show a * y = 0 from ha, mul_zero]

theorem mem_singleAnnihilator {y a : A} : a ∈ singleAnnihilator y ↔ a * y = 0 := Iff.rfl

/-- **`singleAnnihilator y` is homogeneous** when `y` is: an `a` with `a * y = 0` splits as
`a₀ + a₁` (even/odd parts), `a₀ * y` and `a₁ * y` land in complementary grades (shifted by
`|y|`), so both vanish individually (`parts_eq_of_add_eq`). -/
theorem isHomogeneous_singleAnnihilator {y : A} {d : ZMod 2} (hy : y ∈ 𝒜 d) :
    (singleAnnihilator y).IsHomogeneous 𝒜 := by
  intro i a ha
  have han : a * y = 0 := ha
  have hsplit : evenPart 𝒜 a * y + oddPart 𝒜 a * y = 0 := by
    rw [← add_mul, evenPart_add_oddPart, han]
  have key : evenPart 𝒜 a * y = 0 ∧ oddPart 𝒜 a * y = 0 := by
    rcases zmod2_cases d with hd | hd <;> subst hd
    · have h0 : evenPart 𝒜 a * y ∈ 𝒜 0 := by
        have h := SetLike.mul_mem_graded (evenPart_mem 𝒜 a) hy
        rwa [add_zero] at h
      have h1 : oddPart 𝒜 a * y ∈ 𝒜 1 := by
        have h := SetLike.mul_mem_graded (oddPart_mem 𝒜 a) hy
        rwa [show (1 : ZMod 2) + 0 = 1 from by decide] at h
      exact parts_eq_of_add_eq 𝒜 h0 (zero_mem _) h1 (zero_mem _) (by rw [hsplit, zero_add])
    · have h0 : oddPart 𝒜 a * y ∈ 𝒜 0 := by
        have h := SetLike.mul_mem_graded (oddPart_mem 𝒜 a) hy
        rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
      have h1 : evenPart 𝒜 a * y ∈ 𝒜 1 := by
        have h := SetLike.mul_mem_graded (evenPart_mem 𝒜 a) hy
        rwa [show (0 : ZMod 2) + 1 = 1 from by decide] at h
      have hsplit' : oddPart 𝒜 a * y + evenPart 𝒜 a * y = 0 := by
        rw [add_comm]; exact hsplit
      have h01 := parts_eq_of_add_eq 𝒜 h0 (zero_mem _) h1 (zero_mem _)
        (by rw [hsplit', zero_add])
      exact ⟨h01.2, h01.1⟩
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [← evenPart_apply]; exact key.1
  · rw [← oddPart_apply]; exact key.2

/-- The infimum of two homogeneous submodules is homogeneous. -/
theorem isHomogeneous_inf {p q : Submodule A A} (hp : p.IsHomogeneous 𝒜)
    (hq : q.IsHomogeneous 𝒜) : (p ⊓ q).IsHomogeneous 𝒜 := by
  intro i a ha
  rw [Submodule.mem_inf] at ha
  exact Submodule.mem_inf.mpr ⟨hp i ha.1, hq i ha.2⟩

/-- **Deliverable 1b**: for minimal homogeneous nonzero left ideals `I, I'` of a
graded-simple `A`, some homogeneous `y ∈ I'` has `I · y ≠ 0`.  Otherwise `I` would lie
in the (homogeneous, two-sided) annihilator of `I'`, forcing `I = ⊥` by graded
simplicity of `A` (`leftIdealAnnihilator_eq_bot`). -/
theorem exists_homogeneous_right_mult [IsGradedSimple 𝒜] {I I' : Submodule A A}
    (hI'hom : I'.IsHomogeneous 𝒜) (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) :
    ∃ (d : ZMod 2) (y : A), y ∈ 𝒜 d ∧ y ∈ I' ∧ ∃ a ∈ I, a * y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hIne
  rw [Submodule.eq_bot_iff]
  intro a haI
  have hann : a ∈ leftIdealAnnihilator I' := by
    rw [mem_leftIdealAnnihilator_iff]
    intro m hmI'
    have h0 : (DirectSum.decompose 𝒜 m 0 : A) ∈ I' := hI'hom 0 hmI'
    have h1 : (DirectSum.decompose 𝒜 m 1 : A) ∈ I' := hI'hom 1 hmI'
    have he0 : a * (DirectSum.decompose 𝒜 m 0 : A) = 0 :=
      hcon 0 _ (SetLike.coe_mem _) h0 a haI
    have he1 : a * (DirectSum.decompose 𝒜 m 1 : A) = 0 :=
      hcon 1 _ (SetLike.coe_mem _) h1 a haI
    have hm : (DirectSum.decompose 𝒜 m 0 : A) + (DirectSum.decompose 𝒜 m 1 : A) = m := by
      rw [← evenPart_apply, ← oddPart_apply]; exact evenPart_add_oddPart 𝒜 m
    rw [← hm, mul_add, he0, he1, add_zero]
  have h0 : leftIdealAnnihilator I' = ⊥ := leftIdealAnnihilator_eq_bot 𝒜 hI'hom hI'ne
  rw [h0, TwoSidedIdeal.mem_bot] at hann
  exact hann

/-! #### Deliverable 1c: right multiplication as a bijective graded `A`-linear map -/

variable (I I' : Submodule A A)

/-- Right multiplication by `y`, as an `A`-linear map `↥I →ₗ[A] ↥I'`: valid whenever
`y ∈ I'`, since `I'` — a left ideal — is closed under left multiplication by any element
of `A`, in particular by (the coercions of) elements of `I`. -/
def rightMultMap {y : A} (hy : y ∈ I') : ↥I →ₗ[A] ↥I' where
  toFun x := ⟨(x : A) * y, by simpa using I'.smul_mem (x : A) hy⟩
  map_add' x x' := by
    apply Subtype.ext
    show ((x : A) + (x' : A)) * y = (x : A) * y + (x' : A) * y
    rw [add_mul]
  map_smul' a x := by
    apply Subtype.ext
    show ((a • x : ↥I) : A) * y = a * ((x : A) * y)
    rw [Submodule.coe_smul, smul_eq_mul, mul_assoc]

theorem rightMultMap_coe {y : A} (hy : y ∈ I') (x : ↥I) :
    (rightMultMap I I' hy x : A) = (x : A) * y := rfl

variable {I I'}

/-- **Injectivity of `rightMultMap`**: the kernel, pushed to `A`, is `I ⊓ singleAnnihilator y`,
a homogeneous submodule `≤ I` (Deliverable 1's key step); minimality of `I` and the
non-vanishing witness `a * y ≠ 0` force it to `⊥`. -/
theorem rightMultMap_injective (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    {d : ZMod 2} {y : A} (hyd : y ∈ 𝒜 d) (hy : y ∈ I') {a : A} (haI : a ∈ I) (hay : a * y ≠ 0) :
    Function.Injective (rightMultMap I I' hy) := by
  have hJ : I ⊓ singleAnnihilator y = ⊥ := by
    rcases hsimple _ (isHomogeneous_inf 𝒜 hI (isHomogeneous_singleAnnihilator 𝒜 hyd))
        inf_le_left with h | h
    · exact h
    · exfalso
      apply hay
      have hmem : a ∈ I ⊓ singleAnnihilator y := by rw [h]; exact haI
      exact (Submodule.mem_inf.mp hmem).2
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro x hx
  have hxA : (x : A) ∈ I ⊓ singleAnnihilator y := by
    rw [Submodule.mem_inf]
    refine ⟨x.2, ?_⟩
    show (x : A) * y = 0
    have := hx
    rw [LinearMap.mem_ker] at this
    have hcoe : (rightMultMap I I' hy x : A) = 0 := by rw [this]; rfl
    rwa [rightMultMap_coe] at hcoe
  rw [hJ, Submodule.mem_bot] at hxA
  exact Submodule.mem_bot A |>.mpr (Subtype.ext hxA)

private theorem zmod2_shift_cases (d j : ZMod 2) : j = d ∨ j = 1 + d := by decide +revert
private theorem zmod2_d_ne_one_add_d (d : ZMod 2) : d ≠ 1 + d := by decide +revert
private theorem zmod2_double (d : ZMod 2) : d + d = 0 := by decide +revert
private theorem zmod2_one_add_double (d : ZMod 2) : 1 + d + d = 1 := by decide +revert
private theorem zmod2_cancel_right (j d dy : ZMod 2) : j + dy + d + dy = j + d := by decide +revert

/-- **Homogeneity of the range**: the range of `rightMultMap`, pushed to `A` via
`I'.subtype`, is a homogeneous submodule `≤ I'`. -/
theorem isHomogeneous_rightMult_range (hI : I.IsHomogeneous 𝒜) {d : ZMod 2} {y : A}
    (hyd : y ∈ 𝒜 d) (hy : y ∈ I') :
    ((LinearMap.range (rightMultMap I I' hy)).map I'.subtype).IsHomogeneous 𝒜 := by
  intro j z hz
  obtain ⟨w, ⟨x, rfl⟩, rfl⟩ := hz
  set a := (x : A) with ha
  have ha0 : evenPart 𝒜 a ∈ I := hI 0 x.2
  have ha1 : oddPart 𝒜 a ∈ I := hI 1 x.2
  have hsplit : evenPart 𝒜 a * y + oddPart 𝒜 a * y = a * y := by
    rw [← add_mul, evenPart_add_oddPart]
  have hmem0 : evenPart 𝒜 a * y ∈ 𝒜 (0 + d) := SetLike.mul_mem_graded (evenPart_mem 𝒜 a) hyd
  have hmem1 : oddPart 𝒜 a * y ∈ 𝒜 (1 + d) := SetLike.mul_mem_graded (oddPart_mem 𝒜 a) hyd
  rw [zero_add] at hmem0
  have hcoe : ((rightMultMap I I' hy x : ↥I') : A) = a * y := rightMultMap_coe I I' hy x
  rcases zmod2_shift_cases d j with hj | hj
  · rw [hj]
    refine ⟨(rightMultMap I I' hy ⟨evenPart 𝒜 a, ha0⟩ : ↥I'), ⟨⟨evenPart 𝒜 a, ha0⟩, rfl⟩, ?_⟩
    show (rightMultMap I I' hy ⟨evenPart 𝒜 a, ha0⟩ : A)
        = (DirectSum.decompose 𝒜 (((rightMultMap I I' hy x : ↥I') : A)) d : A)
    rw [rightMultMap_coe, hcoe, ← hsplit, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, DirectSum.decompose_of_mem_same 𝒜 hmem0,
      DirectSum.decompose_of_mem_ne 𝒜 hmem1 (zmod2_d_ne_one_add_d d).symm, add_zero]
  · rw [hj]
    refine ⟨(rightMultMap I I' hy ⟨oddPart 𝒜 a, ha1⟩ : ↥I'), ⟨⟨oddPart 𝒜 a, ha1⟩, rfl⟩, ?_⟩
    show (rightMultMap I I' hy ⟨oddPart 𝒜 a, ha1⟩ : A)
        = (DirectSum.decompose 𝒜 (((rightMultMap I I' hy x : ↥I') : A)) (1 + d) : A)
    rw [rightMultMap_coe, hcoe, ← hsplit, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, DirectSum.decompose_of_mem_ne 𝒜 hmem0 (zmod2_d_ne_one_add_d d),
      DirectSum.decompose_of_mem_same 𝒜 hmem1, zero_add]

/-- **Surjectivity of `rightMultMap`**: its range, pushed to `A`, is a nonzero (the
witness `a * y ≠ 0` prevents it from being `⊥`) homogeneous submodule `≤ I'`; minimality
of `I'` forces it to be everything. -/
theorem rightMultMap_surjective (hI : I.IsHomogeneous 𝒜) (hI'sim : IsGradedSimpleIdeal 𝒜 I')
    {d : ZMod 2} {y : A} (hyd : y ∈ 𝒜 d) (hy : y ∈ I') {a : A} (haI : a ∈ I)
    (hay : a * y ≠ 0) : Function.Surjective (rightMultMap I I' hy) := by
  have hhom := isHomogeneous_rightMult_range 𝒜 hI hyd hy
  have hle : (LinearMap.range (rightMultMap I I' hy)).map I'.subtype ≤ I' :=
    Submodule.map_subtype_le I' _
  rcases hI'sim _ hhom hle with h | h
  · exfalso
    apply hay
    have hmem : (rightMultMap I I' hy ⟨a, haI⟩ : A) ∈
        (LinearMap.range (rightMultMap I I' hy)).map I'.subtype :=
      ⟨rightMultMap I I' hy ⟨a, haI⟩, ⟨⟨a, haI⟩, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    rwa [rightMultMap_coe] at hmem
  · rw [← LinearMap.range_eq_top]
    have h' : (LinearMap.range (rightMultMap I I' hy)).map I'.subtype
        = (⊤ : Submodule A ↥I').map I'.subtype := by rw [h, Submodule.map_subtype_top]
    exact (Submodule.map_injective_of_injective (Submodule.injective_subtype I')) h'

/-- **`rightMultMap` is bijective**: injective (Deliverable 1c, kernel argument) and
surjective (range argument), assembling into a genuine `A`-linear equivalence
`↥I ≃ₗ[A] ↥I'`. -/
noncomputable def rightMultEquiv (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hI'sim : IsGradedSimpleIdeal 𝒜 I') {d : ZMod 2} {y : A} (hyd : y ∈ 𝒜 d) (hy : y ∈ I')
    {a : A} (haI : a ∈ I) (hay : a * y ≠ 0) : ↥I ≃ₗ[A] ↥I' :=
  LinearEquiv.ofBijective (rightMultMap I I' hy)
    ⟨rightMultMap_injective 𝒜 hI hsimple hyd hy haI hay,
      rightMultMap_surjective 𝒜 hI hI'sim hyd hy haI hay⟩

theorem rightMultEquiv_apply (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hI'sim : IsGradedSimpleIdeal 𝒜 I') {d : ZMod 2} {y : A} (hyd : y ∈ 𝒜 d) (hy : y ∈ I')
    {a : A} (haI : a ∈ I) (hay : a * y ≠ 0) (x : ↥I) :
    (rightMultEquiv 𝒜 hI hsimple hI'sim hyd hy haI hay x : A) = (x : A) * y := rfl

/-! #### Deliverable 1d: the graded-inverse lemma and `endIdeal_equiv_of_minimal` -/

/-- **The graded-inverse lemma** (referee correction #4): if `g` is a bijective
`A`-linear map shifting degree-`j` layers of `I` into degree-`(j + d)` layers of `I'`,
then `g.symm` shifts degree-`k` layers of `I'` into degree-`(k + d)` layers of `I`
(`ZMod 2`: `-d = d`, so the shift is the same in both directions). -/
theorem mem_idealGrading_symm_apply {I I' : Submodule A A} (hI : I.IsHomogeneous 𝒜)
    (hI' : I'.IsHomogeneous 𝒜) (g : ↥I ≃ₗ[A] ↥I') {d : ZMod 2}
    (hg : ∀ (j : ZMod 2) (x : ↥I), x ∈ idealGrading 𝒜 I j → g x ∈ idealGrading 𝒜 I' (j + d))
    {k : ZMod 2} {z : ↥I'} (hz : z ∈ idealGrading 𝒜 I' k) :
    g.symm z ∈ idealGrading 𝒜 I (k + d) := by
  set x := g.symm z with hxdef
  have hx01 : idealProjAmbient 𝒜 hI 0 x + idealProjAmbient 𝒜 hI 1 x = x :=
    idealProjAmbient_zero_add_idealProjAmbient_one 𝒜 hI x
  have hgx0 : g (idealProjAmbient 𝒜 hI 0 x) ∈ idealGrading 𝒜 I' (0 + d) :=
    hg 0 _ (idealProjAmbient_mem 𝒜 hI 0 x)
  have hgx1 : g (idealProjAmbient 𝒜 hI 1 x) ∈ idealGrading 𝒜 I' (1 + d) :=
    hg 1 _ (idealProjAmbient_mem 𝒜 hI 1 x)
  rw [zero_add] at hgx0
  have hgxsum : g (idealProjAmbient 𝒜 hI 0 x) + g (idealProjAmbient 𝒜 hI 1 x) = z := by
    rw [← map_add, hx01, hxdef, LinearEquiv.apply_symm_apply]
  rcases zmod2_shift_cases d k with hk | hk
  · rw [hk] at hz ⊢
    have hz0 : idealProjAmbient 𝒜 hI' d z = g (idealProjAmbient 𝒜 hI 0 x) := by
      rw [← hgxsum]
      exact idealProjAmbient_add_of_mem_ne hI' hgx0 hgx1 (zmod2_d_ne_one_add_d d)
    have hzeq : idealProjAmbient 𝒜 hI' d z = z := idealProjAmbient_of_mem 𝒜 hI' hz
    have heq0 : g (idealProjAmbient 𝒜 hI 0 x) = z := by rw [← hz0, hzeq]
    have heq1 : g (idealProjAmbient 𝒜 hI 1 x) = 0 := by
      have h2 := hgxsum
      rw [heq0] at h2
      have h3 : z + g (idealProjAmbient 𝒜 hI 1 x) = z + 0 := by rw [h2, add_zero]
      exact add_left_cancel h3
    have hx1 : idealProjAmbient 𝒜 hI 1 x = 0 := g.injective (by rw [heq1, map_zero])
    have hxeq : x = idealProjAmbient 𝒜 hI 0 x := by
      have h4 : idealProjAmbient 𝒜 hI 0 x + 0 = x := by rw [← hx1]; exact hx01
      rw [add_zero] at h4
      exact h4.symm
    show x ∈ idealGrading 𝒜 I (d + d)
    rw [zmod2_double, hxeq]
    exact idealProjAmbient_mem 𝒜 hI 0 x
  · rw [hk] at hz ⊢
    have hz1 : idealProjAmbient 𝒜 hI' (1 + d) z = g (idealProjAmbient 𝒜 hI 1 x) := by
      rw [← hgxsum]
      exact idealProjAmbient_add_of_mem_ne' hI' hgx0 hgx1 (zmod2_d_ne_one_add_d d)
    have hzeq : idealProjAmbient 𝒜 hI' (1 + d) z = z := idealProjAmbient_of_mem 𝒜 hI' hz
    have heq1 : g (idealProjAmbient 𝒜 hI 1 x) = z := by rw [← hz1, hzeq]
    have heq0 : g (idealProjAmbient 𝒜 hI 0 x) = 0 := by
      have h2 := hgxsum
      rw [heq1, add_comm] at h2
      have h3 : z + g (idealProjAmbient 𝒜 hI 0 x) = z + 0 := by rw [h2, add_zero]
      exact add_left_cancel h3
    have hx0 : idealProjAmbient 𝒜 hI 0 x = 0 := g.injective (by rw [heq0, map_zero])
    have hxeq : x = idealProjAmbient 𝒜 hI 1 x := by
      have h4 : 0 + idealProjAmbient 𝒜 hI 1 x = x := by rw [← hx0]; exact hx01
      rw [zero_add] at h4
      exact h4.symm
    show x ∈ idealGrading 𝒜 I (1 + d + d)
    rw [zmod2_one_add_double, hxeq]
    exact idealProjAmbient_mem 𝒜 hI 1 x

/-- `rightMultEquiv` shifts `idealGrading I` layers into `idealGrading I'` layers by
`dy`, the degree of `y` — the input the graded-inverse lemma consumes. -/
theorem rightMultEquiv_mem_idealGrading (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hI'sim : IsGradedSimpleIdeal 𝒜 I') {dy : ZMod 2} {y : A} (hyd : y ∈ 𝒜 dy) (hy : y ∈ I')
    {a : A} (haI : a ∈ I) (hay : a * y ≠ 0) {j : ZMod 2} {x : ↥I} (hx : x ∈ idealGrading 𝒜 I j) :
    rightMultEquiv 𝒜 hI hsimple hI'sim hyd hy haI hay x ∈ idealGrading 𝒜 I' (j + dy) := by
  rw [mem_idealGrading_iff] at hx ⊢
  rw [rightMultEquiv_apply]
  exact SetLike.mul_mem_graded hx hyd

/-- **Deliverable 1d — the assembled theorem**: conjugation by `rightMultEquiv` carries
`End_A ↥I`'s grading onto `End_A ↥I'`'s, degree for degree — the shift by `dy = |y|`
introduced twice (once going in, once coming back through the inverse) cancels
(`ZMod 2`: `dy + dy = 0`). -/
theorem endIdeal_equiv_map_grading (hI : I.IsHomogeneous 𝒜) (hI' : I'.IsHomogeneous 𝒜)
    (hsimple : IsGradedSimpleIdeal 𝒜 I) (hI'sim : IsGradedSimpleIdeal 𝒜 I') {dy : ZMod 2} {y : A}
    (hyd : y ∈ 𝒜 dy) (hy : y ∈ I') {a : A} (haI : a ∈ I) (hay : a * y ≠ 0) (d : ZMod 2) :
    (endIdealGrading 𝒜 hI d).map
        ((rightMultEquiv 𝒜 hI hsimple hI'sim hyd hy haI hay).conjAlgEquiv K).toLinearMap
      = endIdealGrading 𝒜 hI' d := by
  haveI hEalg : GradedAlgebra (endIdealGrading 𝒜 hI) := endIdealGradedAlgebra 𝒜 hI
  haveI hEalg' : GradedAlgebra (endIdealGrading 𝒜 hI') := endIdealGradedAlgebra 𝒜 hI'
  set g := rightMultEquiv 𝒜 hI hsimple hI'sim hyd hy haI hay with hgdef
  refine map_grading_of_bijective (endIdealGrading 𝒜 hI) (endIdealGrading 𝒜 hI')
    (g.conjAlgEquiv K).toAlgHom ?_ (g.conjAlgEquiv K).bijective d
  intro d' f hf j z hz
  have hgz : g.symm z ∈ idealGrading 𝒜 I (j + dy) :=
    mem_idealGrading_symm_apply 𝒜 hI hI' g
      (fun j' x hx => rightMultEquiv_mem_idealGrading 𝒜 hI hsimple hI'sim hyd hy haI hay hx) hz
  have hfz : f (g.symm z) ∈ idealGrading 𝒜 I (j + dy + d') := hf (j + dy) (g.symm z) hgz
  have hgfz : g (f (g.symm z)) ∈ idealGrading 𝒜 I' (j + dy + d' + dy) :=
    rightMultEquiv_mem_idealGrading 𝒜 hI hsimple hI'sim hyd hy haI hay hfz
  rw [zmod2_cancel_right] at hgfz
  show ((g.conjAlgEquiv K).toAlgHom f) z ∈ idealGrading 𝒜 I' (j + d')
  have hcoe : ((g.conjAlgEquiv K).toAlgHom f) z = g (f (g.symm z)) := by
    show (g.conjAlgEquiv K f) z = g (f (g.symm z))
    rw [LinearEquiv.conjAlgEquiv_apply]
    rfl
  rwa [hcoe]

/-- The homogeneous right-multiplication witness of `exists_homogeneous_right_mult`,
extracted as data via `Exists.choose` (a `Prop`-to-`Type` extraction, since the
degree `dy`, element `y`, and witness `a` all feed into the *data* of
`endIdealEquivOfMinimal` below — `obtain`/`rcases` cannot perform this extraction
directly into a `Type`-sorted goal, only `Exists.choose` can). -/
private noncomputable def ermWitness [IsGradedSimple 𝒜] (I I' : Submodule A A)
    (hI'hom : I'.IsHomogeneous 𝒜) (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) :
    Σ' (_dy : ZMod 2) (_y _a : A), True :=
  let h := exists_homogeneous_right_mult 𝒜 hI'hom hIne hI'ne
  let hy := h.choose_spec
  let ha := hy.choose_spec.2.2
  ⟨h.choose, hy.choose, ha.choose, trivial⟩

private theorem ermWitness_yd [IsGradedSimple 𝒜] (I I' : Submodule A A)
    (hI'hom : I'.IsHomogeneous 𝒜) (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) :
    (ermWitness 𝒜 I I' hI'hom hIne hI'ne).2.1 ∈ 𝒜 (ermWitness 𝒜 I I' hI'hom hIne hI'ne).1 :=
  (exists_homogeneous_right_mult 𝒜 hI'hom hIne hI'ne).choose_spec.choose_spec.1

private theorem ermWitness_y' [IsGradedSimple 𝒜] (I I' : Submodule A A)
    (hI'hom : I'.IsHomogeneous 𝒜) (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) :
    (ermWitness 𝒜 I I' hI'hom hIne hI'ne).2.1 ∈ I' :=
  (exists_homogeneous_right_mult 𝒜 hI'hom hIne hI'ne).choose_spec.choose_spec.2.1

private theorem ermWitness_aI [IsGradedSimple 𝒜] (I I' : Submodule A A)
    (hI'hom : I'.IsHomogeneous 𝒜) (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) :
    (ermWitness 𝒜 I I' hI'hom hIne hI'ne).2.2.1 ∈ I :=
  (exists_homogeneous_right_mult 𝒜 hI'hom hIne hI'ne).choose_spec.choose_spec.2.2.choose_spec.1

private theorem ermWitness_ay [IsGradedSimple 𝒜] (I I' : Submodule A A)
    (hI'hom : I'.IsHomogeneous 𝒜) (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) :
    (ermWitness 𝒜 I I' hI'hom hIne hI'ne).2.2.1 *
        (ermWitness 𝒜 I I' hI'hom hIne hI'ne).2.1 ≠ 0 :=
  (exists_homogeneous_right_mult 𝒜 hI'hom hIne hI'ne).choose_spec.choose_spec.2.2.choose_spec.2

/-- **`endIdealEquivOfMinimal`**: `Module.End A ↥I ≃ₐ[K] Module.End A ↥I'`, for two
minimal homogeneous nonzero left ideals `I, I'` of the same graded-simple `A`
(docs/wedderburn-design.md, Deliverable 1d of the M10-8 extension). -/
noncomputable def endIdealEquivOfMinimal [IsGradedSimple 𝒜] (hI : I.IsHomogeneous 𝒜)
    (hI'hom : I'.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hI'sim : IsGradedSimpleIdeal 𝒜 I') (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) :
    Module.End A ↥I ≃ₐ[K] Module.End A ↥I' :=
  (rightMultEquiv 𝒜 hI hsimple hI'sim (ermWitness_yd 𝒜 I I' hI'hom hIne hI'ne)
      (ermWitness_y' 𝒜 I I' hI'hom hIne hI'ne) (ermWitness_aI 𝒜 I I' hI'hom hIne hI'ne)
      (ermWitness_ay 𝒜 I I' hI'hom hIne hI'ne)).conjAlgEquiv K

/-- **`endIdealEquivOfMinimal` respects the gradings**, degree for degree. -/
theorem endIdealEquivOfMinimal_map_grading [IsGradedSimple 𝒜] (hI : I.IsHomogeneous 𝒜)
    (hI'hom : I'.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hI'sim : IsGradedSimpleIdeal 𝒜 I') (hIne : I ≠ ⊥) (hI'ne : I' ≠ ⊥) (d : ZMod 2) :
    (endIdealGrading 𝒜 hI d).map
        (endIdealEquivOfMinimal 𝒜 hI hI'hom hsimple hI'sim hIne hI'ne).toLinearMap
      = endIdealGrading 𝒜 hI'hom d :=
  endIdeal_equiv_map_grading 𝒜 hI hI'hom hsimple hI'sim (ermWitness_yd 𝒜 I I' hI'hom hIne hI'ne)
    (ermWitness_y' 𝒜 I I' hI'hom hIne hI'ne) (ermWitness_aI 𝒜 I I' hI'hom hIne hI'ne)
    (ermWitness_ay 𝒜 I I' hI'hom hIne hI'ne) d

end IdealTransport

/-! ### Part 2: the column ideal of a matrix superalgebra -/

section ColumnIdeal

variable {K : Type*} [Field K]
variable {D : Type*} [Ring D] [Algebra K D] (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]
variable {n : Type*} [Fintype n] [DecidableEq n] (π : n → ZMod 2)

/-- **Deliverable 2a**: the column ideal at index `j₀` — matrices of `Matrix n n D`
supported on column `j₀` — is a left ideal (closed under left matrix multiplication:
`(Z * X) _ k = ∑ Z _ l * X l k = 0` when `X`'s column `k` vanishes). -/
def columnIdeal (j₀ : n) : Submodule (Matrix n n D) (Matrix n n D) where
  carrier := {X | ∀ i k, k ≠ j₀ → X i k = 0}
  zero_mem' _ _ _ := rfl
  add_mem' {X Y} hX hY i k hk := by rw [Matrix.add_apply, hX i k hk, hY i k hk, add_zero]
  smul_mem' Z X hX i k hk := by
    show (Z * X) i k = 0
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [hX l k hk, mul_zero]

theorem mem_columnIdeal {j₀ : n} {X : Matrix n n D} :
    X ∈ columnIdeal (D := D) j₀ ↔ ∀ i k, k ≠ j₀ → X i k = 0 := Iff.rfl

/-- The column ideal is nonzero: the elementary matrix `single j₀ j₀ 1` is a nonzero
member. -/
theorem columnIdeal_ne_bot [Nontrivial D] (j₀ : n) : columnIdeal (D := D) j₀ ≠ ⊥ := by
  intro h
  have h1 : (Matrix.single j₀ j₀ (1 : D)) ∈ columnIdeal (D := D) j₀ := by
    intro r k hk
    rw [Matrix.single_apply, if_neg (fun hp => hk hp.2.symm)]
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrFun (congrFun h1 j₀) j₀
  rw [Matrix.single_apply_same, Matrix.zero_apply] at h2
  exact one_ne_zero h2

/-- **Deliverable 2a (homogeneity)**: the column ideal is homogeneous for the
coefficient matrix grading — masking is entrywise (`matrixMaskA`), and masking a zero
entry stays zero. -/
theorem isHomogeneous_columnIdeal (j₀ : n) :
    (columnIdeal (D := D) j₀).IsHomogeneous (matrixGradingA π 𝒟) := by
  intro i X hX
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [decompose_matrixGradingA_zero_coe]
    intro r k hk
    rw [matrixMaskA_apply, hX r k hk, DirectSum.decompose_zero, DirectSum.zero_apply,
      ZeroMemClass.coe_zero]
  · rw [decompose_matrixGradingA_one_coe]
    intro r k hk
    rw [matrixMaskA_apply, hX r k hk, DirectSum.decompose_zero, DirectSum.zero_apply,
      ZeroMemClass.coe_zero]

/-- **Deliverable 2b — minimality**: a nonzero homogeneous left sub-ideal `J` of the
column ideal is everything.  Direct matrix-unit argument (referee correction #1, not
the bimodule irreducibility of `Bimod/ColumnSimple.lean`, whose right-action closure
hypothesis a mere left ideal does not supply): a nonzero homogeneous `X ∈ J` has a
nonzero entry `X i₁ j₀` in the column, a unit `u` of `D` (homogeneous, `IsSuperDivision`);
for any target `Y` in the column ideal, the matrix `Z` with `Z _ i₁ = Y _ j₀ * u⁻¹`
(else `0`) satisfies `Z * X = Y`, and `Z * X ∈ J` since `J` is a left ideal. -/
theorem isGradedSimpleIdeal_columnIdeal (hdiv : Bimod.IsSuperDivision 𝒟) (j₀ : n) :
    IsGradedSimpleIdeal (matrixGradingA π 𝒟) (columnIdeal (D := D) j₀) := by
  intro J hJhom hJle
  by_cases hJbot : J = ⊥
  · exact Or.inl hJbot
  refine Or.inr (le_antisymm hJle ?_)
  obtain ⟨v, hvJ, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJbot
  have hcomp : ∃ d : ZMod 2, (DirectSum.decompose (matrixGradingA π 𝒟) v d :
      Matrix n n D) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0
    have h0 := hcon 0
    have h1 := hcon 1
    rw [← evenPart_apply] at h0
    rw [← oddPart_apply] at h1
    rw [← evenPart_add_oddPart (matrixGradingA π 𝒟) v, h0, h1, add_zero]
  obtain ⟨d, hd⟩ := hcomp
  set X := (DirectSum.decompose (matrixGradingA π 𝒟) v d : Matrix n n D) with hXdef
  have hXJ : X ∈ J := by rw [hXdef]; exact hJhom d hvJ
  have hXcol : X ∈ columnIdeal (D := D) j₀ := hJle hXJ
  have hXmem : X ∈ matrixGradingA π 𝒟 d := SetLike.coe_mem _
  obtain ⟨i1, hi1⟩ : ∃ i1, X i1 j₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hd
    ext r k
    by_cases hk : k = j₀
    · subst hk; exact hcon r
    · exact hXcol r k hk
  have hXi1 : X i1 j₀ ∈ 𝒟 (d + π i1 + π j₀) := hXmem i1 j₀
  obtain ⟨u, hu⟩ := hdiv hXi1 hi1
  intro Y hY
  set Z : Matrix n n D := Matrix.of (fun r l => if l = i1 then Y r j₀ * ((u⁻¹ : Dˣ) : D) else 0)
    with hZdef
  have hZX : Z * X = Y := by
    ext r b
    rw [Matrix.mul_apply]
    by_cases hb : b = j₀
    · rw [hb]
      rw [Finset.sum_eq_single i1 (fun l _ hl => by
          rw [hZdef]; show (if l = i1 then Y r j₀ * ((u⁻¹ : Dˣ) : D) else 0) * X l j₀ = 0
          rw [if_neg hl, zero_mul])
        (fun h => absurd (Finset.mem_univ i1) h)]
      rw [hZdef]
      show (if i1 = i1 then Y r j₀ * ((u⁻¹ : Dˣ) : D) else 0) * X i1 j₀ = Y r j₀
      rw [if_pos rfl, mul_assoc, ← hu, Units.inv_mul, mul_one]
    · rw [Finset.sum_eq_zero fun l _ => by rw [hXcol l b hb, mul_zero]]
      exact (hY r b hb).symm
  rw [← hZX]
  exact J.smul_mem Z hXJ

/-! ### Deliverable 2c: the column endomorphism algebra is `Dᵐᵒᵖ` -/

variable (j₀ : n)

theorem columnIdeal_eq_sum_single (X : Matrix n n D) (hX : X ∈ columnIdeal (D := D) j₀) :
    X = ∑ r, Matrix.single r j₀ (X r j₀) := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases hb : b = j₀
  · rw [hb, Finset.sum_eq_single a
      (fun r _ hr => Matrix.single_apply_of_row_ne hr j₀ j₀ (X r j₀))
      (fun h => absurd (Finset.mem_univ a) h), Matrix.single_apply_same]
  · rw [hX a b hb,
      Finset.sum_eq_zero fun r _ => Matrix.single_apply_of_col_ne r a (Ne.symm hb) (X r j₀)]

theorem single_mem_columnIdealD (r : n) (d : D) :
    Matrix.single r j₀ d ∈ columnIdeal (D := D) j₀ := by
  intro a k hk
  rw [Matrix.single_apply, if_neg (fun hp => hk hp.2.symm)]

/-- The scalar `d_f := (f E₀) j₀ j₀ ∈ D` reading off an `A`-endomorphism `f` of the
column, where `E₀ := single j₀ j₀ 1` is the diagonal reference element of the column
(degree `0`, since `π j₀ + π j₀ = 0`). -/
noncomputable def columnScalar (f : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) : D :=
  (f ⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ : Matrix n n D) j₀ j₀

/-- **The closed form on single-entry columns**: `f` applied to `single r j₀ d` is
`single r j₀ (d * columnScalar f)` — the matrix-unit computation (referee correction #7,
step 1) pinning `f` to right multiplication by the scalar `columnScalar f`. -/
theorem end_apply_single (f : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) (r : n)
    (d : D) :
    (f ⟨Matrix.single r j₀ d, single_mem_columnIdealD j₀ r d⟩ : Matrix n n D)
      = Matrix.single r j₀ (d * columnScalar j₀ f) := by
  have hsmul : (⟨Matrix.single r j₀ d, single_mem_columnIdealD j₀ r d⟩ :
      ↥(columnIdeal (D := D) j₀))
      = Matrix.single r j₀ d • (⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ :
        ↥(columnIdeal (D := D) j₀)) := by
    apply Subtype.ext
    show Matrix.single r j₀ d = Matrix.single r j₀ d * Matrix.single j₀ j₀ 1
    rw [Matrix.single_mul_single_same, mul_one]
  have hE0mem := (f ⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ :
    ↥(columnIdeal (D := D) j₀)).2
  rw [hsmul, map_smul]
  ext a b
  show (Matrix.single r j₀ d * (f ⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ :
      Matrix n n D)) a b = Matrix.single r j₀ (d * columnScalar j₀ f) a b
  by_cases hra : a = r
  · rw [hra, Matrix.single_mul_apply_same]
    by_cases hb : b = j₀
    · rw [hb, Matrix.single_apply_same]
      rfl
    · rw [hE0mem j₀ b hb, mul_zero,
        Matrix.single_apply_of_col_ne r r (Ne.symm hb) (d * columnScalar j₀ f)]
  · rw [Matrix.single_mul_apply_of_ne (h := hra),
      Matrix.single_apply_of_row_ne (fun h => hra h.symm) j₀ b (d * columnScalar j₀ f)]

/-- **The closed form (Deliverable 2c, referee correction #7)**: every `A`-endomorphism
of the column ideal is right multiplication (entrywise) by the fixed scalar
`columnScalar f` — additivity over the single-entry decomposition of `X`
(`columnIdeal_eq_sum_single`) upgrades `end_apply_single` to all of the column. -/
theorem end_apply_eq (f : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀))
    (X : Matrix n n D) (hX : X ∈ columnIdeal (D := D) j₀) :
    (f ⟨X, hX⟩ : Matrix n n D) = X * Matrix.single j₀ j₀ (columnScalar j₀ f) := by
  have hsub : (⟨X, hX⟩ : ↥(columnIdeal (D := D) j₀))
      = ∑ r, (⟨Matrix.single r j₀ (X r j₀), single_mem_columnIdealD j₀ r (X r j₀)⟩ :
        ↥(columnIdeal (D := D) j₀)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact columnIdeal_eq_sum_single j₀ X hX
  have hstep : ∀ r, (f ⟨Matrix.single r j₀ (X r j₀), single_mem_columnIdealD j₀ r (X r j₀)⟩ :
      Matrix n n D) = Matrix.single r j₀ (X r j₀ * columnScalar j₀ f) :=
    fun r => end_apply_single j₀ f r (X r j₀)
  have hentry : (∑ r, (f ⟨Matrix.single r j₀ (X r j₀), single_mem_columnIdealD j₀ r (X r j₀)⟩ :
      Matrix n n D)) = ∑ r, Matrix.single r j₀ (X r j₀ * columnScalar j₀ f) :=
    Finset.sum_congr rfl fun r _ => hstep r
  rw [hsub, map_sum, Submodule.coe_sum, hentry]
  ext a b
  rw [Matrix.sum_apply]
  by_cases hb : b = j₀
  · rw [hb, Finset.sum_eq_single a
      (fun r _ hr => Matrix.single_apply_of_row_ne hr j₀ j₀ _)
      (fun h => absurd (Finset.mem_univ a) h), Matrix.single_apply_same,
      Matrix.mul_single_apply_same]
  · rw [Finset.sum_eq_zero fun r _ => Matrix.single_apply_of_col_ne r a (Ne.symm hb) _,
      Matrix.mul_single_apply_of_ne (hbj := hb)]

/-- `end_apply_eq`, restated at the subtype level (no explicit membership witness). -/
theorem end_apply_eq' (f : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀))
    (y : ↥(columnIdeal (D := D) j₀)) :
    (f y : Matrix n n D) = (y : Matrix n n D) * Matrix.single j₀ j₀ (columnScalar j₀ f) :=
  end_apply_eq j₀ f (y : Matrix n n D) y.2

variable {K : Type*} [Field K] [Algebra K D]

/-- **`columnScalar` reverses composition** — the input to `Dᵐᵒᵖ`, not `D`. -/
theorem columnScalar_mul (f g : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) :
    columnScalar j₀ (f * g) = columnScalar j₀ g * columnScalar j₀ f := by
  show (((f * g) ⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ :
    Matrix n n D)) j₀ j₀ = columnScalar j₀ g * columnScalar j₀ f
  show ((f (g ⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩) :
    Matrix n n D)) j₀ j₀ = columnScalar j₀ g * columnScalar j₀ f
  rw [end_apply_eq' j₀ f, Matrix.mul_single_apply_same]
  rfl

theorem columnScalar_add (f g : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) :
    columnScalar j₀ (f + g) = columnScalar j₀ f + columnScalar j₀ g := by
  show (((f + g) ⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ :
    Matrix n n D)) j₀ j₀ = columnScalar j₀ f + columnScalar j₀ g
  rfl

theorem columnScalar_one : columnScalar (D := D) j₀ 1 = 1 := by
  show Matrix.single j₀ j₀ (1 : D) j₀ j₀ = 1
  rw [Matrix.single_apply_same]

theorem columnScalar_zero :
    columnScalar j₀ (0 : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) = 0 := rfl

theorem columnScalar_smul (c : K) (f : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) :
    columnScalar j₀ (c • f) = c • columnScalar j₀ f := rfl

/-- **Right multiplication by `d`** (entrywise, on the column), the inverse direction of
`columnScalar`: an `A`-linear endomorphism of the column ideal. -/
def columnRightMul (d : D) : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀) where
  toFun X := ⟨(X : Matrix n n D) * Matrix.single j₀ j₀ d, fun i k hk => by
    rw [Matrix.mul_single_apply_of_ne (hbj := hk)]⟩
  map_add' X Y := by
    apply Subtype.ext
    show ((X : Matrix n n D) + (Y : Matrix n n D)) * Matrix.single j₀ j₀ d
        = (X : Matrix n n D) * Matrix.single j₀ j₀ d + (Y : Matrix n n D) * Matrix.single j₀ j₀ d
    rw [add_mul]
  map_smul' Z X := by
    apply Subtype.ext
    show ((Z • X : ↥(columnIdeal (D := D) j₀)) : Matrix n n D) * Matrix.single j₀ j₀ d
        = Z * ((X : Matrix n n D) * Matrix.single j₀ j₀ d)
    rw [Submodule.coe_smul, smul_eq_mul, mul_assoc]

theorem columnScalar_columnRightMul (d : D) : columnScalar j₀ (columnRightMul j₀ d) = d := by
  show (Matrix.single j₀ j₀ (1 : D) * Matrix.single j₀ j₀ d) j₀ j₀ = d
  rw [Matrix.single_mul_single_same, Matrix.single_apply_same, one_mul]

theorem columnRightMul_columnScalar (f : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) :
    columnRightMul j₀ (columnScalar j₀ f) = f := by
  refine LinearMap.ext fun y => ?_
  apply Subtype.ext
  show (y : Matrix n n D) * Matrix.single j₀ j₀ (columnScalar j₀ f) = (f y : Matrix n n D)
  rw [end_apply_eq' j₀ f y]

end ColumnIdeal

section ColumnAlgEquiv

variable {K : Type*} [Field K]
variable {D : Type*} [Ring D] [Algebra K D] (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]
variable {n : Type*} [Fintype n] [DecidableEq n] (π : n → ZMod 2) (j₀ : n)

/-- **`columnEndHom`**: the `K`-algebra homomorphism `Module.End A ↥(columnIdeal j₀) →ₐ[K]
Dᵐᵒᵖ`, `f ↦ op (columnScalar f)` — a ring hom (not anti-hom) precisely because `Dᵐᵒᵖ`
absorbs the composition reversal (`columnScalar_mul`). -/
noncomputable def columnEndHom :
    Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀) →ₐ[K] Dᵐᵒᵖ where
  toFun f := MulOpposite.op (columnScalar j₀ f)
  map_one' := by rw [columnScalar_one]; rfl
  map_mul' f g := by rw [columnScalar_mul]; exact MulOpposite.op_mul (columnScalar j₀ g) (columnScalar j₀ f)
  map_zero' := by rw [columnScalar_zero]; rfl
  map_add' f g := by rw [columnScalar_add]; rfl
  commutes' c := by
    show MulOpposite.op (columnScalar j₀ (algebraMap K _ c)) = algebraMap K Dᵐᵒᵖ c
    rw [Algebra.algebraMap_eq_smul_one, columnScalar_smul, columnScalar_one,
      ← Algebra.algebraMap_eq_smul_one]
    rfl

theorem columnEndHom_apply (f : Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀)) :
    columnEndHom (K := K) j₀ f = MulOpposite.op (columnScalar j₀ f) := rfl

/-- **`columnEndHom` is bijective**: injective because `columnScalar f = 0 → f =
columnRightMul (columnScalar f) = columnRightMul 0 = 0` (`columnRightMul_columnScalar`);
surjective because `columnEndHom (columnRightMul d) = op d`
(`columnScalar_columnRightMul`). -/
theorem columnEndHom_bijective : Function.Bijective (columnEndHom (D := D) (K := K) j₀) := by
  constructor
  · intro f g hfg
    have h : columnScalar j₀ f = columnScalar j₀ g := MulOpposite.op_injective hfg
    rw [← columnRightMul_columnScalar j₀ f, ← columnRightMul_columnScalar j₀ g, h]
  · intro x
    refine ⟨columnRightMul j₀ x.unop, ?_⟩
    rw [columnEndHom_apply, columnScalar_columnRightMul, MulOpposite.op_unop]

/-- **`endColumn_equiv_op`** (Deliverable 2c): the endomorphism algebra of the column
ideal is `K`-algebra isomorphic to `Dᵐᵒᵖ`. -/
noncomputable def endColumnEquivOp :
    Module.End (Matrix n n D) ↥(columnIdeal (D := D) j₀) ≃ₐ[K] Dᵐᵒᵖ :=
  AlgEquiv.ofBijective (columnEndHom j₀) (columnEndHom_bijective j₀)

/-- **`endColumnEquivOp` is graded**: degree-`d` endomorphisms correspond to `opGrading
𝒟 d` — the diagonal reference element `single j₀ j₀ 1` has `matrixGradingA`-degree `0`
(`π j₀ + π j₀ = 0`), so the column-index shift referee correction #6 warns about is
absorbed by the choice of reference row `= j₀` itself.  Proved directly from `columnScalar`/
`columnRightMul` (not via the generic bijective-graded-transport lemma, whose interaction
with `AlgEquiv.ofBijective`'s noncomputable inverse triggers a deterministic-timeout
elaboration blow-up here). -/
theorem endColumnEquivOp_map_grading (hI : (columnIdeal (D := D) j₀).IsHomogeneous
    (matrixGradingA π 𝒟)) (d : ZMod 2) :
    (endIdealGrading (matrixGradingA π 𝒟) hI d).map (endColumnEquivOp (K := K) j₀).toLinearMap
      = opGrading 𝒟 d := by
  haveI hEalg := endIdealGradedAlgebra (matrixGradingA π 𝒟) hI
  have hE0 : (⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ :
      ↥(columnIdeal (D := D) j₀)) ∈ idealGrading (matrixGradingA π 𝒟) (columnIdeal (D := D) j₀) 0 := by
    rw [mem_idealGrading_iff]
    intro a b
    show Matrix.single j₀ j₀ (1 : D) a b ∈ 𝒟 (0 + π a + π b)
    by_cases hab : j₀ = a ∧ j₀ = b
    · rw [Matrix.single_apply, if_pos hab, ← hab.1, ← hab.2, zero_add, zmod2_double (π j₀)]
      exact SetLike.one_mem_graded 𝒟
    · rw [Matrix.single_apply, if_neg hab]
      exact zero_mem _
  apply le_antisymm
  · rintro y ⟨f, hf, rfl⟩
    show MulOpposite.op (columnScalar j₀ f) ∈ opGrading 𝒟 d
    rw [mem_opGrading_iff]
    have hf0 : f (⟨Matrix.single j₀ j₀ 1, single_mem_columnIdealD j₀ j₀ 1⟩ :
        ↥(columnIdeal (D := D) j₀)) ∈ idealGrading (matrixGradingA π 𝒟)
        (columnIdeal (D := D) j₀) (0 + d) :=
      hf 0 _ hE0
    rw [zero_add, mem_idealGrading_iff] at hf0
    have hscalar : columnScalar j₀ f ∈ 𝒟 (d + π j₀ + π j₀) := hf0 j₀ j₀
    rwa [show d + π j₀ + π j₀ = d from by
      rw [add_assoc, zmod2_double (π j₀), add_zero]] at hscalar
  · intro y hy
    refine ⟨columnRightMul j₀ y.unop, ?_, ?_⟩
    · intro j X hX
      rw [mem_idealGrading_iff] at hX ⊢
      show (X : Matrix n n D) * Matrix.single j₀ j₀ y.unop ∈ matrixGradingA π 𝒟 (j + d)
      intro a b
      by_cases hb : b = j₀
      · rw [hb, Matrix.mul_single_apply_same]
        have hmul := SetLike.mul_mem_graded (hX a j₀) ((mem_opGrading_iff (𝒟 := 𝒟)).mp hy)
        rwa [show j + π a + π j₀ + d = j + d + π a + π j₀ from by ring] at hmul
      · rw [Matrix.mul_single_apply_of_ne (hbj := hb)]
        exact zero_mem _
    · show MulOpposite.op (columnScalar j₀ (columnRightMul j₀ y.unop)) = y
      rw [columnScalar_columnRightMul, MulOpposite.op_unop]

end ColumnAlgEquiv

end Superfusion

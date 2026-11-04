/-
Superfusion / Bimod / SignedMapEquivariance

Milestone M8a-8c′-2b-i (roadmap v3): **equivariance and composition
of the signed amplification** — the `smap` counterpart of the
`RelTensor.map` transport lemmas (M8a-8b′-1), needed for the pentagon
composites to be intertwiners:

* outer left: `smap ∘ L_b = (-1)^{e|b|} L_b ∘ smap` on homogeneous
  `b` (the amplification's parity against the first-slot shift);
* signed middle: `smap ∘ mid_c = s · mid_c ∘ smap` whenever
  `g (c•n) = s (c • g n)` — both signs are scalars, so no parity
  interplay occurs;
* outer right: plain commutation (the sign depends only on the first
  slot);
* degree: `smap e g` with `g` of degree `e'` is homogeneous of
  degree `e'` (the sign does not affect membership);
* **the composition law** `smap e' g' ∘ smap e g =
  smap (e'+e) (g' ∘ g)` (with `signedEquivariant_comp` forming the
  composite hypothesis) — for invertible `g` of parity `e` this
  makes the signed amplification invertible (`e + e = 0`).
-/
import Superfusion.Bimod.SignedMap

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module A N']
variable (g : N →ₗ[K] N') (e : ZMod 2)
variable [GradedRightSMul 𝒜 ℳ]

/-! ### Outer left action -/

section Left

variable {B : Type*} [Ring B] [Algebra K B]
variable [Module B M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower K B M]
variable (ℬ : ZMod 2 → Submodule K B) [SetLike.GradedSMul ℬ ℳ]

private theorem zmod2_smapleft_deg :
    ∀ e i j : ZMod 2, e * i + e * j = e * (i + j) := by decide

/-- `smap` intertwines the outer left action up to the sign
`(-1)^{e|b|}` (its parity against the first-slot shift). -/
theorem smap_comp_leftActionEnd
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    {i : ZMod 2} {b : B} (hb : b ∈ ℬ i) :
    (smap 𝒜 ℳ g e hg).comp (leftActionEnd K A M N b)
      = ((sgn (e * i) : ℤˣ) : ℤ) •
          (leftActionEnd K A M N' b).comp (smap 𝒜 ℳ g e hg) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero =>
      simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | add m m' hm hm' =>
      simp only [map_add, LinearMap.add_apply, hm, hm', smul_add]
  | homogeneous xm =>
      rw [leftActionEnd_mk, smap_mk_of_mem 𝒜 ℳ g e hg
          ((vadd_eq_add (i : ZMod 2) _) ▸
            SetLike.GradedSMul.smul_mem hb xm.2) n,
        smap_mk_of_mem 𝒜 ℳ g e hg xm.2 n, map_zsmul, leftActionEnd_mk,
        smul_smul, ← Units.val_mul, ← sgn_add, zmod2_smapleft_deg]

end Left

/-! ### Outer right action -/

section Right

variable {C : Type*} [Ring C] [Algebra K C]
variable [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N] [IsScalarTower K Cᵐᵒᵖ N]
variable [Module Cᵐᵒᵖ N'] [SMulCommClass A Cᵐᵒᵖ N']
variable [IsScalarTower K Cᵐᵒᵖ N']

/-- `smap` intertwines the outer right action plainly (its sign
depends only on the first slot). -/
theorem smap_comp_rightActionEnd
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    {τ : Cᵐᵒᵖ} (hgE : ∀ n : N, g (τ • n) = τ • g n) :
    (smap 𝒜 ℳ g e hg).comp (rightActionEnd K A M N τ)
      = (rightActionEnd K A M N' τ).comp (smap 𝒜 ℳ g e hg) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, rightActionEnd_mk,
    smap_mk 𝒜 ℳ g e hg, smap_mk 𝒜 ℳ g e hg, smapBilin_apply,
    smapBilin_apply, map_sub, map_zsmul, rightActionEnd_mk,
    rightActionEnd_mk, hgE]

end Right

/-! ### Signed middle action -/

section Middle

variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞]
variable [Module C N] [IsScalarTower K C N]
variable [Module C N'] [IsScalarTower K C N']

/-- `smap` intertwines the signed middle action up to `g`'s own
signed equivariance for it — both signs are scalars, so no parity
interplay occurs. -/
theorem smap_comp_midEnd
    (hsc : SuperCommSMul 𝒜 𝒞 N) (hsc' : SuperCommSMul 𝒜 𝒞 N')
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    {s : ℤ} {k : ZMod 2} {c : C} (hc : c ∈ 𝒞 k)
    (hgC : ∀ n : N, g (c • n) = s • (c • g n)) :
    (smap 𝒜 ℳ g e hg).comp (midEnd 𝒜 ℳ 𝒞 hsc c)
      = s • (midEnd 𝒜 ℳ 𝒞 hsc' c).comp (smap 𝒜 ℳ g e hg) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero =>
      simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | add m m' hm hm' =>
      simp only [map_add, LinearMap.add_apply, hm, hm', smul_add]
  | homogeneous xm =>
      rw [midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc xm.2 hc n, map_zsmul,
        smap_mk_of_mem 𝒜 ℳ g e hg xm.2 (c • n), hgC n, map_zsmul,
        smap_mk_of_mem 𝒜 ℳ g e hg xm.2 n, map_zsmul,
        midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc' xm.2 hc (g n)]
      simp only [smul_smul]
      congr 1
      ring

end Middle

/-! ### Degree-shifted gradedness -/

section Graded

variable (𝒩 : ZMod 2 → Submodule K N) (𝒩' : ZMod 2 → Submodule K N')

private theorem zmod2_smapdeg :
    ∀ j k e' : ZMod 2, j + (k + e') = (j + k) + e' := by
  decide +revert

/-- `smap e g` with `g` of degree `e'` is homogeneous of degree `e'`
(the sign does not affect membership). -/
theorem smap_mem_relGrading_of_degree
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    {e' : ZMod 2} (hgd : ∀ j : ZMod 2, ∀ n ∈ 𝒩 j, g n ∈ 𝒩' (j + e'))
    {i : ZMod 2} {z : M ⊗[A;K] N} (hz : z ∈ relGrading A ℳ 𝒩 i) :
    smap 𝒜 ℳ g e hg z ∈ relGrading A ℳ 𝒩' (i + e') := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒩)
    (balancer K A M N)).mp hz
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w =>
      smap 𝒜 ℳ g e hg (RelTensor.fromTensor K A M N w)
        ∈ relGrading A ℳ 𝒩' (i + e')) hx ?_ ?_ ?_ ?_
  · intro j k m n hjk hm hn
    show smap 𝒜 ℳ g e hg (RelTensor.mk K A M N m n)
        ∈ relGrading A ℳ 𝒩' (i + e')
    rw [smap_mk_of_mem 𝒜 ℳ g e hg hm n]
    refine zsmul_mem ?_ _
    have h := mk_mem_relGrading (A := A) ℳ 𝒩' hm (hgd _ _ hn)
    rwa [zmod2_smapdeg, hjk] at h
  · rw [map_zero, map_zero]
    exact zero_mem _
  · intro x y hx hy
    rw [map_add, map_add]
    exact add_mem hx hy
  · intro k x hx
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ k hx

end Graded

/-! ### The composition law -/

section Compose

variable {N'' : Type*} [AddCommGroup N''] [Module K N''] [Module A N'']
variable (g' : N' →ₗ[K] N'') (e' : ZMod 2)

private theorem zmod2_smapcomp_deg :
    ∀ e e' j : ZMod 2, e * j + e' * j = (e' + e) * j := by
  decide +revert

omit [GradedAlgebra 𝒜] in
/-- The composite of two signed equivariances is signed of the summed
parity (the hypothesis-former for `smap_comp_smap`). -/
theorem signedEquivariant_comp
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    (hg' : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n' : N',
      g' (a • n') = ((sgn (e' * i) : ℤˣ) : ℤ) • (a • g' n')) :
    ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      (g'.comp g) (a • n)
        = ((sgn ((e' + e) * i) : ℤˣ) : ℤ) • (a • (g'.comp g) n) := by
  intro i a ha n
  rw [LinearMap.comp_apply, hg ha n, map_zsmul, hg' ha (g n),
    LinearMap.comp_apply, smul_smul, ← Units.val_mul, ← sgn_add,
    zmod2_smapcomp_deg]

/-- **The composition law of signed amplifications**:
`smap e' g' ∘ smap e g = smap (e'+e) (g' ∘ g)`. -/
theorem smap_comp_smap
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    (hg' : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n' : N',
      g' (a • n') = ((sgn (e' * i) : ℤˣ) : ℤ) • (a • g' n')) :
    (smap 𝒜 ℳ g' e' hg').comp (smap 𝒜 ℳ g e hg)
      = smap 𝒜 ℳ (g'.comp g) (e' + e)
          (signedEquivariant_comp 𝒜 g e g' e' hg hg') := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply]
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero =>
      simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' =>
      simp only [map_add, LinearMap.add_apply, hm, hm']
  | homogeneous xm =>
      rw [smap_mk_of_mem 𝒜 ℳ g e hg xm.2 n, map_zsmul,
        smap_mk_of_mem 𝒜 ℳ g' e' hg' xm.2 (g n),
        smap_mk_of_mem 𝒜 ℳ (g'.comp g) (e' + e)
          (signedEquivariant_comp 𝒜 g e g' e' hg hg') xm.2 n,
        smul_smul, ← Units.val_mul, ← sgn_add, zmod2_smapcomp_deg]
      rfl

end Compose

end Bimod

end Superfusion

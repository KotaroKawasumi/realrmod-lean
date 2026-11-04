/-
Superfusion / Bimod / MapEquivariance

Milestone M8a-8b′-1 (roadmap v3): **equivariance of induced maps**.
The `E`-maps of the pentagon comparison are amplifications
`map t id` / `map id t` of intertwiners; for the composites to live in
the one-dimensional intertwiner spaces they must themselves be
intertwiners.  This file proves the transport of the three action
layers through `RelTensor.map`, for `f` homogeneous of degree `d`:

* outer left: `map f g ∘ L_b = (-1)^{d|b|} L_b ∘ map f g`
  (the sign is `f`'s super-equivariance, passed through unchanged);
* signed middle: `map f g ∘ mid_c = (-1)^{d|c|} mid_c ∘ map f g`
  (here the sign appears even though `g` intertwines `c` plainly —
  the middle sign consumes the `M`-parity, which `f` shifts by `d`;
  sign identity `dk + k(j+d) = kj`);
* right: `map f g ∘ R_e = R_e ∘ map f g` (sign-free);
* the degree-shifted gradedness `map_mem_relGrading_of_degree`
  (`f` of degree `d`, `g` of degree `e` induce degree `d + e`).
-/
import Superfusion.Bimod.MiddleActionHom
import Superfusion.Bimod.RelTensorMap

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {M' : Type*} [AddCommGroup M'] [Module K M'] [Module Aᵐᵒᵖ M']
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module A N']
variable (f : M →ₗ[K] M') (g : N →ₗ[K] N')

/-! ### Outer left action -/

section Left

variable {B : Type*} [Ring B] [Algebra K B]
variable [Module B M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower K B M]
variable [Module B M'] [SMulCommClass B Aᵐᵒᵖ M'] [IsScalarTower K B M']

/-- `map f g` intertwines the outer left action up to `f`'s
super-equivariance sign. -/
theorem map_comp_leftActionEnd
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n)
    {s : ℤ} {b : B} (hfB : ∀ m : M, f (b • m) = s • (b • f m)) :
    (RelTensor.map f g hf hg).comp (leftActionEnd K A M N b)
      = s • (leftActionEnd K A M' N' b).comp (RelTensor.map f g hf hg) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    leftActionEnd_mk, RelTensor.map_mk, hfB m, map_zsmul,
    LinearMap.smul_apply, RelTensor.map_mk, leftActionEnd_mk]

end Left

/-! ### Outer right action -/

section Right

variable {C : Type*} [Ring C] [Algebra K C]
variable [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N] [IsScalarTower K Cᵐᵒᵖ N]
variable [Module Cᵐᵒᵖ N'] [SMulCommClass A Cᵐᵒᵖ N'] [IsScalarTower K Cᵐᵒᵖ N']

/-- `map f g` intertwines the outer right action plainly. -/
theorem map_comp_rightActionEnd
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n)
    {e : Cᵐᵒᵖ} (hgE : ∀ n : N, g (e • n) = e • g n) :
    (RelTensor.map f g hf hg).comp (rightActionEnd K A M N e)
      = (rightActionEnd K A M' N' e).comp (RelTensor.map f g hf hg) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, rightActionEnd_mk,
    RelTensor.map_mk, hgE n, RelTensor.map_mk, rightActionEnd_mk]

end Right

/-! ### Signed middle action -/

section Middle

variable [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable (ℳ' : ZMod 2 → Submodule K M') [DirectSum.Decomposition ℳ']
variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞]
variable [Module C N] [IsScalarTower K C N]
variable [Module C N'] [IsScalarTower K C N']
variable [GradedRightSMul 𝒜 ℳ] [GradedRightSMul 𝒜 ℳ']

private theorem zmod2_mapmid_deg :
    ∀ d k j : ZMod 2, d * k + k * (j + d) = k * j := by
  decide +revert

/-- `map f g` intertwines the signed middle action up to the sign
`(-1)^{d|c|}` produced by `f`'s degree shift of the `M`-parity —
even though `g` intertwines `c` plainly. -/
theorem map_comp_midEnd
    (hsc : SuperCommSMul 𝒜 𝒞 N) (hsc' : SuperCommSMul 𝒜 𝒞 N')
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n)
    {d : ZMod 2} (hfd : ∀ j : ZMod 2, ∀ m ∈ ℳ j, f m ∈ ℳ' (j + d))
    {k : ZMod 2} {c : C} (hc : c ∈ 𝒞 k)
    (hgC : ∀ n : N, g (c • n) = c • g n) :
    (RelTensor.map f g hf hg).comp (midEnd 𝒜 ℳ 𝒞 hsc c)
      = ((sgn (d * k) : ℤˣ) : ℤ) •
        (midEnd 𝒜 ℳ' 𝒞 hsc' c).comp (RelTensor.map f g hf hg) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero =>
      simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | add m m' hm hm' =>
      simp only [map_add, LinearMap.add_apply, hm, hm', smul_add]
  | homogeneous xm =>
      rw [midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc xm.2 hc, map_zsmul,
        RelTensor.map_mk, hgC, RelTensor.map_mk,
        midEnd_mk_of_mem 𝒜 ℳ' 𝒞 hsc' (hfd _ _ xm.2) hc, smul_smul,
        ← Units.val_mul, ← sgn_add, zmod2_mapmid_deg]

end Middle

/-! ### Degree-shifted gradedness -/

section Graded

variable (ℳ : ZMod 2 → Submodule K M) (𝒩 : ZMod 2 → Submodule K N)
variable (ℳ' : ZMod 2 → Submodule K M') (𝒩' : ZMod 2 → Submodule K N')

private theorem zmod2_mapdeg :
    ∀ j k d e : ZMod 2, (j + d) + (k + e) = (j + k) + (d + e) := by
  decide +revert

/-- `map f g` with `f` of degree `d` and `g` of degree `e` is
homogeneous of degree `d + e` for the descended gradings. -/
theorem map_mem_relGrading_of_degree
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n)
    {d e : ZMod 2}
    (hfd : ∀ j : ZMod 2, ∀ m ∈ ℳ j, f m ∈ ℳ' (j + d))
    (hgd : ∀ j : ZMod 2, ∀ n ∈ 𝒩 j, g n ∈ 𝒩' (j + e))
    {i : ZMod 2} {z : M ⊗[A;K] N} (hz : z ∈ relGrading A ℳ 𝒩 i) :
    RelTensor.map f g hf hg z ∈ relGrading A ℳ' 𝒩' (i + (d + e)) := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒩)
    (balancer K A M N)).mp hz
  show RelTensor.map f g hf hg (RelTensor.fromTensor K A M N x)
    ∈ relGrading A ℳ' 𝒩' (i + (d + e))
  rw [RelTensor.map_fromTensor]
  refine fromTensor_mem_relGrading ℳ' 𝒩' ?_
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w =>
      TensorProduct.map f g w ∈ tensorGrading ℳ' 𝒩' (i + (d + e)))
    hx ?_ ?_ ?_ ?_
  · intro j k m n hjk hm hn
    rw [TensorProduct.map_tmul]
    have h := tmul_mem_tensorGrading ℳ' 𝒩' (hfd j m hm) (hgd k n hn)
    rwa [zmod2_mapdeg, hjk] at h
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy
  · intro c x hx
    rw [map_smul]; exact Submodule.smul_mem _ c hx

end Graded

end Bimod

end Superfusion

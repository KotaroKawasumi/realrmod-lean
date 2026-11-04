/-
Superfusion / Bimod / GtensorLeftActionGraded

General-layer companions to `MiddleActionHom.lean`'s
`gtensorLeftActionHom`, needed to ITERATE the two-slot assembly a
further level (M8a-8d′-iii-a): its commutation with a further outer
right action (the `SMulCommClass` hypothesis a further
`leftActionEnd`/`Bimod.Envelope` needs) and its gradedness (the
`[SetLike.GradedSMul …]` hypothesis a further `gtensorLeftActionHom`
invocation needs).

1. **Commutation with a further right action**
   (`gtensorLeftActionHom_comm_rightActionEnd`): combining
   `leftActionEnd_comm_rightActionEnd` (`OuterActions.lean`) and
   `midEnd_comm_rightActionEnd` (`MiddleActionHom.lean`) on generators
   `b ᵍ⊗ₜ c` (`GradedTensorProduct.lift_tmul`, needing no homogeneity
   at all), extended to all of `ℬ ᵍ⊗[K] 𝒞` since `GradedTensorProduct`
   is definitionally the plain `TensorProduct` (`GradedTensorProduct.of
   = LinearEquiv.refl`), so `TensorProduct.induction_on` applies once
   precomposed with `GradedTensorProduct.of`.

2. **Gradedness** (`gtensorLeftActionHom_mem_relGrading`): a double
   induction — the OUTER one over `w`'s membership in the *algebra*
   tensor grading (`Superfusion.tensorGrading_induction`, distinct
   from `Bimod.tensorGrading_induction` below, both in scope
   simultaneously — qualified fully to disambiguate), the INNER one
   (on a homogeneous generator `b ᵍ⊗ₜ c`) over `z`'s membership in
   `relGrading` (`mem_quotGrading_iff` + `Bimod.tensorGrading_induction`,
   mirroring `midEnd_mem_relGrading`'s own proof) — landing via
   `gtensorLeftActionHom_tmul_mk_of_mem` and `mk_mem_relGrading`.
-/
import Superfusion.Bimod.MiddleActionHom

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞]
variable [Module C N] [IsScalarTower K C N]
variable [GradedRightSMul 𝒜 ℳ]
variable {B : Type*} [Ring B] [Algebra K B]
variable [Module B M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower K B M]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable [SetLike.GradedSMul ℬ ℳ]

/-! ### Commutation with a further outer right action -/

section Right

variable {E : Type*} [Ring E] [Algebra K E]
variable [Module Eᵐᵒᵖ N] [SMulCommClass A Eᵐᵒᵖ N] [IsScalarTower K Eᵐᵒᵖ N]
variable [SMulCommClass C Eᵐᵒᵖ N]

/-- **`gtensorLeftActionHom` commutes with a further outer right
action**: the pointwise commutation on generators
(`leftActionEnd_comm_rightActionEnd`, `midEnd_comm_rightActionEnd`)
extends to all of `ℬ ᵍ⊗[K] 𝒞` since `gtensorLeftActionHom` is `K`-linear
and `GradedTensorProduct` is definitionally the plain tensor
product. -/
theorem gtensorLeftActionHom_comm_rightActionEnd (hsc : SuperCommSMul 𝒜 𝒞 N)
    (w : ℬ ᵍ⊗[K] 𝒞) (e : Eᵐᵒᵖ) :
    gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc w * rightActionEnd K A M N e
      = rightActionEnd K A M N e * gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc w := by
  have hgen : ∀ x : B ⊗[K] C,
      gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc (GradedTensorProduct.of K ℬ 𝒞 x)
          * rightActionEnd K A M N e
        = rightActionEnd K A M N e
            * gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc (GradedTensorProduct.of K ℬ 𝒞 x) := by
    intro x
    induction x with
    | zero => simp
    | tmul b c =>
        show gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc (b ᵍ⊗ₜ[K] c) * rightActionEnd K A M N e
          = rightActionEnd K A M N e * gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc (b ᵍ⊗ₜ[K] c)
        rw [gtensorLeftActionHom, GradedTensorProduct.lift_tmul, midAlgHom_apply, mul_assoc,
          midEnd_comm_rightActionEnd 𝒜 ℳ 𝒞 hsc c e, ← mul_assoc,
          leftActionEnd_comm_rightActionEnd K A M N b e, mul_assoc, ← midAlgHom_apply]
    | add x y hx hy =>
        rw [map_add, map_add, add_mul, mul_add, hx, hy]
  have h := hgen ((GradedTensorProduct.of K ℬ 𝒞).symm w)
  rwa [LinearEquiv.apply_symm_apply] at h

end Right

/-! ### Gradedness -/

section Graded

variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]
variable [SetLike.GradedSMul 𝒞 𝒩]

private theorem zmod2_gtensor_deg :
    ∀ j' k' j'' k'' : ZMod 2, (j' + j'') + (k' + k'') = (j' + k') + (j'' + k'') := by
  decide +revert

omit [DirectSum.Decomposition 𝒩] in
/-- **Gradedness of `gtensorLeftActionHom`**: a homogeneous element of
`ℬ ᵍ⊗[K] 𝒞` of degree `i` shifts `relGrading`'s degree by `i`, matching
`leftActionEnd_mem_relGrading`/`midEnd_mem_relGrading`'s combined
content — needed as the `[SetLike.GradedSMul …]` hypothesis of a
further `gtensorLeftActionHom` invocation. -/
theorem gtensorLeftActionHom_mem_relGrading (hsc : SuperCommSMul 𝒜 𝒞 N)
    {i j : ZMod 2} {w : ℬ ᵍ⊗[K] 𝒞} (hw : w ∈ Superfusion.tensorGrading ℬ 𝒞 i)
    {z : M ⊗[A;K] N} (hz : z ∈ relGrading A ℳ 𝒩 j) :
    gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc w z ∈ relGrading A ℳ 𝒩 (i + j) := by
  refine Superfusion.tensorGrading_induction ℬ 𝒞
    (p := fun w' => ∀ z' ∈ relGrading A ℳ 𝒩 j,
      gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc w' z' ∈ relGrading A ℳ 𝒩 (i + j))
    hw ?_ ?_ ?_ ?_ z hz
  · intro j' k' b c hjk hb hc z' hz'
    obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒩)
      (balancer K A M N)).mp hz'
    refine tensorGrading_induction ℳ 𝒩
      (motive := fun w'' =>
        gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc (b ᵍ⊗ₜ[K] c) (RelTensor.fromTensor K A M N w'')
          ∈ relGrading A ℳ 𝒩 (i + j)) hx ?_ ?_ ?_ ?_
    · intro j'' k'' m n hjk' hm hn
      show gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc (b ᵍ⊗ₜ[K] c) (RelTensor.mk K A M N m n)
          ∈ relGrading A ℳ 𝒩 (i + j)
      rw [gtensorLeftActionHom_tmul_mk_of_mem 𝒜 ℳ 𝒞 ℬ hsc b hc hm]
      refine zsmul_mem ?_ _
      have hbm : b • m ∈ ℳ (j' + j'') :=
        (vadd_eq_add j' j'') ▸ SetLike.GradedSMul.smul_mem hb hm
      have hcn : c • n ∈ 𝒩 (k' + k'') :=
        (vadd_eq_add k' k'') ▸ SetLike.GradedSMul.smul_mem hc hn
      have h := mk_mem_relGrading (A := A) ℳ 𝒩 hbm hcn
      rwa [show (j' + j'') + (k' + k'') = i + j from by
        rw [zmod2_gtensor_deg, hjk, hjk']] at h
    · rw [map_zero, map_zero]
      exact zero_mem _
    · intro x' y' hx' hy'
      rw [map_add, map_add]
      exact add_mem hx' hy'
    · intro c' x' hx'
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c' hx'
  · intro z' _
    rw [map_zero, LinearMap.zero_apply]
    exact zero_mem _
  · intro w1 w2 h1 h2 z' hz'
    rw [map_add, LinearMap.add_apply]
    exact add_mem (h1 z' hz') (h2 z' hz')
  · intro c' w1 h1 z' hz'
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ c' (h1 z' hz')

end Graded

end Bimod

end Superfusion

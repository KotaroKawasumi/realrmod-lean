/-
Superfusion / Bimod / RelTensorGraded

Milestone M8a-3b: **the grading descends to the balanced tensor
product**.  For a superalgebra `A` acting gradedly on the right of `M`
and on the left of `N`, the balancing submodule of `M ⊗[K] N` is
homogeneous for the tensor grading — it is spanned by its homogeneous
generators, the balancing differences of homogeneous triples — so the
quotient machinery of M8a-3a equips `M ⊗[A] N` with a
`ZMod 2`-decomposition `relGrading`, in which `mk m n` is homogeneous
of degree `|m| + |n|`.

This is the grading of the paper's `B_L`, `B_R` (§4.1): homogeneous
elements of the fusion of column bimodules are (sums of) balanced
tensors of homogeneous columns.
-/
import Superfusion.Bimod.RelTensor
import Superfusion.Bimod.GradedModule
import Superfusion.Super.TensorGrading

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]

/-! ### The balancing submodule is homogeneous -/

/-- The homogeneous balancing differences. -/
private def homogGens : Set (M ⊗[K] N) :=
  {x | ∃ (i j k : ZMod 2) (a : A) (m : M) (n : N),
    a ∈ 𝒜 i ∧ m ∈ ℳ j ∧ n ∈ 𝒩 k ∧
      x = (MulOpposite.op a • m) ⊗ₜ[K] n - m ⊗ₜ[K] (a • n)}

omit [Algebra K A] in
/-- Additivity of the balancing difference in the algebra slot. -/
private theorem gen_add_algebra (a a' : A) (m : M) (n : N) :
    (MulOpposite.op (a + a') • m) ⊗ₜ[K] n - m ⊗ₜ[K] ((a + a') • n)
      = ((MulOpposite.op a • m) ⊗ₜ[K] n - m ⊗ₜ[K] (a • n))
        + ((MulOpposite.op a' • m) ⊗ₜ[K] n - m ⊗ₜ[K] (a' • n)) := by
  rw [MulOpposite.op_add, add_smul, TensorProduct.add_tmul, add_smul,
    TensorProduct.tmul_add, sub_add_sub_comm]

omit [Algebra K A] in
/-- Additivity of the balancing difference in the left module slot. -/
private theorem gen_add_left (a : A) (m m' : M) (n : N) :
    (MulOpposite.op a • (m + m')) ⊗ₜ[K] n - (m + m') ⊗ₜ[K] (a • n)
      = ((MulOpposite.op a • m) ⊗ₜ[K] n - m ⊗ₜ[K] (a • n))
        + ((MulOpposite.op a • m') ⊗ₜ[K] n - m' ⊗ₜ[K] (a • n)) := by
  rw [smul_add, TensorProduct.add_tmul, TensorProduct.add_tmul,
    sub_add_sub_comm]

omit [Algebra K A] in
/-- Additivity of the balancing difference in the right module slot. -/
private theorem gen_add_right (a : A) (m : M) (n n' : N) :
    (MulOpposite.op a • m) ⊗ₜ[K] (n + n') - m ⊗ₜ[K] (a • (n + n'))
      = ((MulOpposite.op a • m) ⊗ₜ[K] n - m ⊗ₜ[K] (a • n))
        + ((MulOpposite.op a • m) ⊗ₜ[K] n' - m ⊗ₜ[K] (a • n')) := by
  rw [TensorProduct.tmul_add, smul_add, TensorProduct.tmul_add,
    sub_add_sub_comm]

/-- Every balancing difference lies in the span of the homogeneous
ones (expand all three slots into homogeneous components). -/
private theorem gen_mem_span_homogGens (a : A) (m : M) (n : N) :
    (MulOpposite.op a • m) ⊗ₜ[K] n - m ⊗ₜ[K] (a • n)
      ∈ Submodule.span K (homogGens 𝒜 ℳ 𝒩) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
      rw [MulOpposite.op_zero, zero_smul, TensorProduct.zero_tmul,
        zero_smul, TensorProduct.tmul_zero, sub_zero]
      exact zero_mem _
  | add a a' ha ha' =>
      rw [gen_add_algebra]
      exact add_mem ha ha'
  | homogeneous xa =>
      induction m using DirectSum.Decomposition.inductionOn ℳ with
      | zero =>
          rw [smul_zero, TensorProduct.zero_tmul, TensorProduct.zero_tmul,
            sub_self]
          exact zero_mem _
      | add m m' hm hm' =>
          rw [gen_add_left]
          exact add_mem hm hm'
      | homogeneous xm =>
          induction n using DirectSum.Decomposition.inductionOn 𝒩 with
          | zero =>
              rw [TensorProduct.tmul_zero, smul_zero,
                TensorProduct.tmul_zero, sub_self]
              exact zero_mem _
          | add n n' hn hn' =>
              rw [gen_add_right]
              exact add_mem hn hn'
          | homogeneous xn =>
              exact Submodule.subset_span
                ⟨_, _, _, _, _, _, xa.2, xm.2, xn.2, rfl⟩

private theorem zmod2_balance_deg :
    ∀ i j k : ZMod 2, j + (i + k) = i + j + k := by
  decide

/-- **The balancing submodule is homogeneous** for the tensor grading,
when the two `A`-actions are graded. -/
theorem balancer_isHomogeneous
    [GradedRightSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] :
    (balancer K A M N).IsHomogeneous (tensorGrading ℳ 𝒩) := by
  have heq : balancer K A M N = Submodule.span K (homogGens 𝒜 ℳ 𝒩) := by
    refine le_antisymm ?_ ?_
    · rw [balancer, Submodule.span_le]
      rintro x ⟨a, m, n, rfl⟩
      exact gen_mem_span_homogGens 𝒜 ℳ 𝒩 a m n
    · rw [Submodule.span_le]
      rintro x ⟨i, j, k, a, m, n, _, _, _, rfl⟩
      exact Submodule.subset_span ⟨a, m, n, rfl⟩
  rw [heq]
  refine isHomogeneous_span (tensorGrading ℳ 𝒩) ?_
  rintro s ⟨i, j, k, a, m, n, ha, hm, hn, rfl⟩
  refine ⟨i + j + k, sub_mem ?_ ?_⟩
  · exact tmul_mem_tensorGrading ℳ 𝒩 (GradedRightSMul.smul_mem ha hm) hn
  · have h := tmul_mem_tensorGrading ℳ 𝒩 hm (SetLike.GradedSMul.smul_mem ha hn)
    rwa [vadd_eq_add, zmod2_balance_deg] at h

/-! ### The grading on `M ⊗[A] N` -/

variable (A)

/-- The induced grading on the balanced tensor product: the images of
the tensor-grading layers. -/
noncomputable def relGrading (i : ZMod 2) : Submodule K (M ⊗[A;K] N) :=
  quotGrading (tensorGrading ℳ 𝒩) (balancer K A M N) i

variable {A}

omit [Algebra K A] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] in
theorem mk_mem_relGrading {j k : ZMod 2} {m : M} {n : N}
    (hm : m ∈ ℳ j) (hn : n ∈ 𝒩 k) :
    RelTensor.mk K A M N m n ∈ relGrading A ℳ 𝒩 (j + k) :=
  mkQ_mem_quotGrading (tensorGrading ℳ 𝒩) (balancer K A M N)
    (tmul_mem_tensorGrading ℳ 𝒩 hm hn)

omit [Algebra K A] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] in
theorem fromTensor_mem_relGrading {i : ZMod 2} {z : M ⊗[K] N}
    (hz : z ∈ tensorGrading ℳ 𝒩 i) :
    RelTensor.fromTensor K A M N z ∈ relGrading A ℳ 𝒩 i :=
  mkQ_mem_quotGrading (tensorGrading ℳ 𝒩) (balancer K A M N) hz

namespace RelTensor

omit [Algebra K A] [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition 𝒩] in
/-- Induction on an element of a specified relative-tensor grading
layer.

It is enough to prove the motive for homogeneous balanced generators
whose two degrees add to the prescribed degree, and to prove closure
under zero, addition, and scalar multiplication.  No decomposition of
either grading, graded action, or algebra structure on the balancing
ring is required. -/
@[elab_as_elim]
theorem induction_on_grading
    {motive : RelTensor K A M N → Prop}
    {d : ZMod 2} {z : RelTensor K A M N}
    (hz : z ∈ relGrading A ℳ 𝒩 d)
    (mk :
      ∀ (i j : ZMod 2), i + j = d →
        ∀ (m : M) (n : N), m ∈ ℳ i → n ∈ 𝒩 j →
          motive (mk K A M N m n))
    (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (c : K) x, motive x → motive (c • x)) :
    motive z := by
  obtain ⟨x, hx, rfl⟩ :=
    (mem_quotGrading_iff
      (tensorGrading ℳ 𝒩)
      (balancer K A M N)).mp hz
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w =>
      motive (fromTensor K A M N w))
    hx ?_ ?_ ?_ ?_
  · intro i j m n hij hm hn
    exact mk i j hij m n hm hn
  · rwa [map_zero]
  · intro x y hx' hy'
    rw [map_add]
    exact add _ _ hx' hy'
  · intro c x hx'
    rw [map_smul]
    exact smul c _ hx'

omit [Algebra K A] [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition 𝒩] in
/-- To prove that a linear map sends one relative-tensor grading layer
into a submodule, it suffices to check homogeneous balanced
generators of matching total degree. -/
theorem mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (f : RelTensor K A M N →ₗ[K] P) (S : Submodule K P)
    {d : ZMod 2} {z : RelTensor K A M N}
    (hz : z ∈ relGrading A ℳ 𝒩 d)
    (mk :
      ∀ (i j : ZMod 2), i + j = d →
        ∀ (m : M) (n : N), m ∈ ℳ i → n ∈ 𝒩 j →
          f (mk K A M N m n) ∈ S) :
    f z ∈ S := by
  refine induction_on_grading ℳ 𝒩
    (motive := fun w => f w ∈ S) hz mk ?_ ?_ ?_
  · rw [map_zero]
    exact zero_mem S
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro c x hx
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

end RelTensor

/-- **The balanced tensor product of graded modules is decomposed**
(when the two `A`-actions are graded).  An `abbrev` (the superalgebra
grading `𝒜` is not recoverable from the statement), to be activated
with `letI` where needed. -/
noncomputable abbrev relDecomposition
    [GradedRightSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] :
    DirectSum.Decomposition (relGrading A ℳ 𝒩) :=
  quotDecomposition (tensorGrading ℳ 𝒩) (balancer_isHomogeneous 𝒜 ℳ 𝒩)

end Bimod

end Superfusion

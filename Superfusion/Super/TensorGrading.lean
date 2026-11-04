/-
Superfusion / Super / TensorGrading

Milestone M7f-1a: **the graded tensor product of graded algebras is a
graded algebra** — the explicit `TODO` of mathlib's
`Mathlib/LinearAlgebra/TensorProduct/Graded/Internal.lean`, in the
`ZMod 2` case used throughout this project.

`tensorGrading 𝒜 ℬ i` is the span of the homogeneous tensors
`x ᵍ⊗ₜ y` with `|x| + |y| = i`; the `GradedAlgebra` instance comes
from mask projections (`TensorProduct.map` of the grade projections,
the pattern of `EvenGrading`/`MatrixSuperCoeff`) for the
decomposition, and from the homogeneous multiplication formula
`tmul_coe_mul_coe_tmul` (the Koszul sign is a `ℤˣ`-scalar, so it does
not affect membership) for the graded monoid structure.

This is the foundation for M7f: with it, statements like
"`A ᵍ⊗ B` is central simple" become expressible, unlocking the
`ᵍ⊗`-closure of super-Azumaya (Wall-map factorization), the
Brauer–Wall group structure, and super Skolem–Noether existence.
-/
import Superfusion.Super.Basic
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

namespace Superfusion

open TensorProduct
open GradedTensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

private theorem zmod2_mask_index : ∀ i : ZMod 2, 1 + (i + 1) = i := by
  decide

private theorem zmod2_solve_one : ∀ k i : ZMod 2, 1 + k = i → k = i + 1 := by
  decide

private theorem zmod2_succ_ne : ∀ i i' : ZMod 2, i ≠ i' → i + 1 ≠ i' + 1 := by
  decide

private theorem zmod2_tensor_mul :
    ∀ j₁ k₁ j₂ k₂ : ZMod 2,
      (j₁ + j₂) + (k₁ + k₂) = (j₁ + k₁) + (j₂ + k₂) := by
  decide

/-! ### The grade projections -/

/-- The degree-`j` projection of a graded algebra, as a linear
endomorphism. -/
noncomputable def gradeProj (j : ZMod 2) : A →ₗ[K] A :=
  (𝒜 j).subtype ∘ₗ
    DirectSum.component K (ZMod 2) (fun i => ↥(𝒜 i)) j ∘ₗ
      (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem gradeProj_apply (j : ZMod 2) (a : A) :
    gradeProj 𝒜 j a = (DirectSum.decompose 𝒜 a j : A) := rfl

theorem gradeProj_mem (j : ZMod 2) (a : A) : gradeProj 𝒜 j a ∈ 𝒜 j := by
  rw [gradeProj_apply]
  exact Submodule.coe_mem _

theorem gradeProj_of_mem {j : ZMod 2} {a : A} (ha : a ∈ 𝒜 j) :
    gradeProj 𝒜 j a = a := by
  rw [gradeProj_apply, DirectSum.decompose_of_mem_same 𝒜 ha]

theorem gradeProj_of_mem_ne {j k : ZMod 2} {a : A} (ha : a ∈ 𝒜 j)
    (hjk : j ≠ k) : gradeProj 𝒜 k a = 0 := by
  rw [gradeProj_apply, DirectSum.decompose_of_mem_ne 𝒜 ha hjk]

theorem gradeProj_zero_add_gradeProj_one (a : A) :
    gradeProj 𝒜 0 a + gradeProj 𝒜 1 a = a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero, map_zero, add_zero]
  | @homogeneous i m =>
      rcases zmod2_cases i with hi | hi <;> subst hi
      · rw [gradeProj_of_mem 𝒜 m.2,
          gradeProj_of_mem_ne 𝒜 m.2 (by decide), add_zero]
      · rw [gradeProj_of_mem 𝒜 m.2,
          gradeProj_of_mem_ne 𝒜 m.2 (by decide), zero_add]
  | add x y hx hy =>
      rw [map_add, map_add, add_add_add_comm, hx, hy]

/-! ### Bilinearity helpers for `ᵍ⊗ₜ` -/

theorem zero_gtmul (y : B) :
    (0 : A) ᵍ⊗ₜ[K] y = (0 : 𝒜 ᵍ⊗[K] ℬ) := by
  show of K 𝒜 ℬ ((0 : A) ⊗ₜ[K] y) = 0
  rw [TensorProduct.zero_tmul, map_zero]

theorem gtmul_zero (x : A) :
    x ᵍ⊗ₜ[K] (0 : B) = (0 : 𝒜 ᵍ⊗[K] ℬ) := by
  show of K 𝒜 ℬ (x ⊗ₜ[K] (0 : B)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

theorem gtmul_add (x : A) (y y' : B) :
    x ᵍ⊗ₜ[K] (y + y') = (x ᵍ⊗ₜ[K] y + x ᵍ⊗ₜ[K] y' : 𝒜 ᵍ⊗[K] ℬ) := by
  show of K 𝒜 ℬ (x ⊗ₜ[K] (y + y')) = _
  rw [TensorProduct.tmul_add, map_add]

theorem add_gtmul (x x' : A) (y : B) :
    (x + x') ᵍ⊗ₜ[K] y = (x ᵍ⊗ₜ[K] y + x' ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] ℬ) := by
  show of K 𝒜 ℬ ((x + x') ⊗ₜ[K] y) = _
  rw [TensorProduct.add_tmul, map_add]

/-! ### The parity grading on the graded tensor product -/

/-- The parity grading on `𝒜 ᵍ⊗[K] ℬ`: degree `i` is spanned by the
homogeneous tensors `x ᵍ⊗ₜ y` with `|x| + |y| = i`. -/
noncomputable def tensorGrading (i : ZMod 2) : Submodule K (𝒜 ᵍ⊗[K] ℬ) :=
  Submodule.span K
    {z | ∃ (j k : ZMod 2) (x : A) (y : B),
      j + k = i ∧ x ∈ 𝒜 j ∧ y ∈ ℬ k ∧ x ᵍ⊗ₜ[K] y = z}

theorem tmul_mem_tensorGrading {j k : ZMod 2} {x : A} {y : B}
    (hx : x ∈ 𝒜 j) (hy : y ∈ ℬ k) :
    x ᵍ⊗ₜ[K] y ∈ tensorGrading 𝒜 ℬ (j + k) :=
  Submodule.subset_span ⟨j, k, x, y, rfl, hx, hy, rfl⟩

/-- Induction principle for membership in `tensorGrading`. -/
theorem tensorGrading_induction {i : ZMod 2}
    {p : (𝒜 ᵍ⊗[K] ℬ) → Prop} {z : 𝒜 ᵍ⊗[K] ℬ}
    (hz : z ∈ tensorGrading 𝒜 ℬ i)
    (tmul : ∀ (j k : ZMod 2) (x : A) (y : B), j + k = i → x ∈ 𝒜 j →
      y ∈ ℬ k → p (x ᵍ⊗ₜ[K] y))
    (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y))
    (smul : ∀ (c : K) x, p x → p (c • x)) : p z := by
  refine Submodule.span_induction ?_ zero
    (fun x y _ _ hx hy => add x y hx hy)
    (fun c x _ hx => smul c x hx) hz
  rintro z ⟨j, k, x, y, hjk, hx, hy, rfl⟩
  exact tmul j k x y hjk hx hy

/-! ### Masks and the decomposition -/

/-- The degree-`i` mask on the graded tensor product. -/
noncomputable def tensorMask (i : ZMod 2) :
    (𝒜 ᵍ⊗[K] ℬ) →ₗ[K] (𝒜 ᵍ⊗[K] ℬ) :=
  (of K 𝒜 ℬ).toLinearMap ∘ₗ
    (TensorProduct.map (gradeProj 𝒜 0) (gradeProj ℬ i)
      + TensorProduct.map (gradeProj 𝒜 1) (gradeProj ℬ (i + 1))) ∘ₗ
    (of K 𝒜 ℬ).symm.toLinearMap

theorem tensorMask_tmul (i : ZMod 2) (x : A) (y : B) :
    tensorMask 𝒜 ℬ i (x ᵍ⊗ₜ[K] y)
      = (gradeProj 𝒜 0 x) ᵍ⊗ₜ[K] (gradeProj ℬ i y)
        + (gradeProj 𝒜 1 x) ᵍ⊗ₜ[K] (gradeProj ℬ (i + 1) y) := by
  rw [tensorMask]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.add_apply]
  rw [show (of K 𝒜 ℬ).symm (x ᵍ⊗ₜ[K] y) = x ⊗ₜ[K] y from rfl,
    TensorProduct.map_tmul, TensorProduct.map_tmul, map_add]

theorem tensorMask_mem (i : ZMod 2) (z : 𝒜 ᵍ⊗[K] ℬ) :
    tensorMask 𝒜 ℬ i z ∈ tensorGrading 𝒜 ℬ i := by
  have key : ∀ t : A ⊗[K] B,
      tensorMask 𝒜 ℬ i (of K 𝒜 ℬ t) ∈ tensorGrading 𝒜 ℬ i := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | tmul x y =>
        rw [show of K 𝒜 ℬ (x ⊗ₜ[K] y) = x ᵍ⊗ₜ[K] y from rfl,
          tensorMask_tmul]
        refine add_mem ?_ ?_
        · have h := tmul_mem_tensorGrading 𝒜 ℬ (gradeProj_mem 𝒜 0 x)
            (gradeProj_mem ℬ i y)
          rwa [zero_add] at h
        · have h := tmul_mem_tensorGrading 𝒜 ℬ (gradeProj_mem 𝒜 1 x)
            (gradeProj_mem ℬ (i + 1) y)
          rwa [zmod2_mask_index] at h
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  have h := key ((of K 𝒜 ℬ).symm z)
  rwa [symm_of_of] at h

theorem tensorMask_zero_add_tensorMask_one (z : 𝒜 ᵍ⊗[K] ℬ) :
    tensorMask 𝒜 ℬ 0 z + tensorMask 𝒜 ℬ 1 z = z := by
  have key : ∀ t : A ⊗[K] B,
      tensorMask 𝒜 ℬ 0 (of K 𝒜 ℬ t) + tensorMask 𝒜 ℬ 1 (of K 𝒜 ℬ t)
        = of K 𝒜 ℬ t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, add_zero]
    | tmul x y =>
        rw [show of K 𝒜 ℬ (x ⊗ₜ[K] y) = x ᵍ⊗ₜ[K] y from rfl,
          tensorMask_tmul, tensorMask_tmul,
          show (0 : ZMod 2) + 1 = 1 from by decide,
          show (1 : ZMod 2) + 1 = 0 from by decide,
          add_add_add_comm, ← gtmul_add, ← gtmul_add,
          add_comm (gradeProj ℬ 1 y) (gradeProj ℬ 0 y), ← add_gtmul,
          gradeProj_zero_add_gradeProj_one,
          gradeProj_zero_add_gradeProj_one]
    | add x y hx hy =>
        rw [map_add, map_add, map_add, add_add_add_comm, hx, hy]
  have h := key ((of K 𝒜 ℬ).symm z)
  rwa [symm_of_of] at h

theorem tensorMask_of_mem {i : ZMod 2} {z : 𝒜 ᵍ⊗[K] ℬ}
    (hz : z ∈ tensorGrading 𝒜 ℬ i) : tensorMask 𝒜 ℬ i z = z := by
  refine tensorGrading_induction 𝒜 ℬ (p := fun w => tensorMask 𝒜 ℬ i w = w)
    hz ?_ (map_zero (tensorMask 𝒜 ℬ i)) ?_ ?_
  · intro j k x y hjk hx hy
    rw [tensorMask_tmul]
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [zero_add] at hjk
      subst hjk
      rw [gradeProj_of_mem 𝒜 hx, gradeProj_of_mem ℬ hy,
        gradeProj_of_mem_ne 𝒜 hx (by decide), zero_gtmul, add_zero]
    · have hk := zmod2_solve_one k i hjk
      subst hk
      rw [gradeProj_of_mem 𝒜 hx, gradeProj_of_mem ℬ hy,
        gradeProj_of_mem_ne 𝒜 hx (by decide), zero_gtmul, zero_add]
  · intro x y hx hy
    rw [map_add, hx, hy]
  · intro c x hx
    rw [map_smul, hx]

theorem tensorMask_of_mem_ne {i i' : ZMod 2} {z : 𝒜 ᵍ⊗[K] ℬ}
    (hz : z ∈ tensorGrading 𝒜 ℬ i) (hii' : i ≠ i') :
    tensorMask 𝒜 ℬ i' z = 0 := by
  refine tensorGrading_induction 𝒜 ℬ (p := fun w => tensorMask 𝒜 ℬ i' w = 0)
    hz ?_ (map_zero (tensorMask 𝒜 ℬ i')) ?_ ?_
  · intro j k x y hjk hx hy
    rw [tensorMask_tmul]
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [zero_add] at hjk
      subst hjk
      rw [gradeProj_of_mem_ne ℬ hy hii', gtmul_zero,
        gradeProj_of_mem_ne 𝒜 hx (by decide), zero_gtmul, add_zero]
    · have hk := zmod2_solve_one k i hjk
      subst hk
      rw [gradeProj_of_mem_ne 𝒜 hx (by decide), zero_gtmul,
        gradeProj_of_mem_ne ℬ hy (zmod2_succ_ne i i' hii'), gtmul_zero,
        add_zero]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x hx
    rw [map_smul, hx, smul_zero]

/-- The degree-`i` mask, corestricted to the layer. -/
noncomputable def tensorMaskInto (i : ZMod 2) :
    (𝒜 ᵍ⊗[K] ℬ) →ₗ[K] tensorGrading 𝒜 ℬ i :=
  LinearMap.codRestrict (tensorGrading 𝒜 ℬ i) (tensorMask 𝒜 ℬ i)
    (tensorMask_mem 𝒜 ℬ i)

noncomputable instance : DirectSum.Decomposition (tensorGrading 𝒜 ℬ) where
  decompose' z :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(tensorGrading 𝒜 ℬ i)) 0
        (tensorMaskInto 𝒜 ℬ 0 z)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(tensorGrading 𝒜 ℬ i)) 1
        (tensorMaskInto 𝒜 ℬ 1 z)
  left_inv z := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact tensorMask_zero_add_tensorMask_one 𝒜 ℬ z
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        rw [map_zero]
        beta_reduce
        rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | of i b =>
        rcases zmod2_cases i with hi | hi <;> subst hi
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : tensorMaskInto 𝒜 ℬ 0 (b : 𝒜 ᵍ⊗[K] ℬ) = b :=
            Subtype.ext (tensorMask_of_mem 𝒜 ℬ b.2)
          have h2 : tensorMaskInto 𝒜 ℬ 1 (b : 𝒜 ᵍ⊗[K] ℬ) = 0 :=
            Subtype.ext (tensorMask_of_mem_ne 𝒜 ℬ b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : tensorMaskInto 𝒜 ℬ 0 (b : 𝒜 ᵍ⊗[K] ℬ) = 0 :=
            Subtype.ext (tensorMask_of_mem_ne 𝒜 ℬ b.2 (by decide))
          have h2 : tensorMaskInto 𝒜 ℬ 1 (b : 𝒜 ᵍ⊗[K] ℬ) = b :=
            Subtype.ext (tensorMask_of_mem 𝒜 ℬ b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-! ### The graded monoid structure -/

private theorem tmul_mul_mem {j₁ k₁ : ZMod 2} {x : A} {y : B}
    (hx : x ∈ 𝒜 j₁) (hy : y ∈ ℬ k₁) {i : ZMod 2} {z : 𝒜 ᵍ⊗[K] ℬ}
    (hz : z ∈ tensorGrading 𝒜 ℬ i) :
    (x ᵍ⊗ₜ[K] y) * z ∈ tensorGrading 𝒜 ℬ ((j₁ + k₁) + i) := by
  refine tensorGrading_induction 𝒜 ℬ (p := fun w => (x ᵍ⊗ₜ[K] y) * w
    ∈ tensorGrading 𝒜 ℬ ((j₁ + k₁) + i)) hz ?_ ?_ ?_ ?_
  · intro j₂ k₂ c d hjk hc hd
    show (x ᵍ⊗ₜ[K] ((⟨y, hy⟩ : ℬ k₁) : B))
        * ((((⟨c, hc⟩ : 𝒜 j₂) : A)) ᵍ⊗ₜ[K] d) ∈ _
    rw [tmul_coe_mul_coe_tmul, Units.smul_def]
    refine zsmul_mem ?_ _
    have hm := tmul_mem_tensorGrading 𝒜 ℬ
      (SetLike.mul_mem_graded hx hc) (SetLike.mul_mem_graded hy hd)
    rwa [zmod2_tensor_mul, hjk] at hm
  · rw [mul_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [mul_add]
    exact add_mem hu hv
  · intro c u hu
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hu

instance : SetLike.GradedMonoid (tensorGrading 𝒜 ℬ) where
  one_mem := by
    have h := tmul_mem_tensorGrading 𝒜 ℬ
      (SetLike.one_mem_graded 𝒜) (SetLike.one_mem_graded ℬ)
    rw [show ((0 : ZMod 2) + 0) = 0 from by decide] at h
    rwa [show (1 : 𝒜 ᵍ⊗[K] ℬ) = (1 : A) ᵍ⊗ₜ[K] (1 : B) from rfl]
  mul_mem {i j} x y hx hy := by
    refine tensorGrading_induction 𝒜 ℬ (p := fun w => w * y
      ∈ tensorGrading 𝒜 ℬ (i + j)) hx ?_ ?_ ?_ ?_
    · intro j₁ k₁ a b hjk ha hb
      have h := tmul_mul_mem 𝒜 ℬ ha hb hy
      rwa [hjk] at h
    · rw [zero_mul]
      exact zero_mem _
    · intro u v hu hv
      rw [add_mul]
      exact add_mem hu hv
    · intro c u hu
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ hu

/-- **The graded tensor product of graded algebras is a graded
algebra** (M7f-1a) — the `TODO` of mathlib's
`TensorProduct/Graded/Internal.lean`, for `ZMod 2` gradings. -/
noncomputable instance tensorGradedAlgebra :
    GradedAlgebra (tensorGrading 𝒜 ℬ) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

/-! ### The inclusions are homogeneous -/

theorem includeLeft_mem_tensorGrading {j : ZMod 2} {x : A}
    (hx : x ∈ 𝒜 j) :
    GradedTensorProduct.includeLeft 𝒜 ℬ x ∈ tensorGrading 𝒜 ℬ j := by
  have h := tmul_mem_tensorGrading 𝒜 ℬ hx (SetLike.one_mem_graded ℬ)
  rwa [add_zero] at h

theorem includeRight_mem_tensorGrading {k : ZMod 2} {y : B}
    (hy : y ∈ ℬ k) :
    GradedTensorProduct.includeRight 𝒜 ℬ y ∈ tensorGrading 𝒜 ℬ k := by
  have h := tmul_mem_tensorGrading 𝒜 ℬ (SetLike.one_mem_graded 𝒜) hy
  rwa [zero_add] at h

end Superfusion

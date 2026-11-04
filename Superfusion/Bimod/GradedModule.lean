/-
Superfusion / Bimod / GradedModule

Milestone M8a-3a: **graded-module machinery** — the three general
ingredients needed to put a `ZMod 2`-grading on the balanced tensor
product `M ⊗[A] N`:

1. `modProj ℳ j`, the degree-`j` projection of a decomposed module
   (the module-level `gradeProj`; `oddPartMod ℳ = modProj ℳ 1`);
2. spans of homogeneous elements are homogeneous submodules
   (`isHomogeneous_span`, in terms of mathlib's
   `Submodule.IsHomogeneous`), and **the quotient of a decomposed
   module by a homogeneous submodule is decomposed**
   (`quotGrading`/`quotDecomposition`) — quotient gradings of modules
   are absent from mathlib (upstream-plan §8, PR 17);
3. the tensor grading on `M ⊗[K] N` of two decomposed modules
   (`Bimod.tensorGrading`, with its `DirectSum.Decomposition`) — the
   module-level counterpart of `Superfusion.tensorGrading` on `ᵍ⊗`
   (M7f-1a), built by the same mask-projection pattern.

The file also records how `modProj` passes through right multiplication by
a homogeneous coefficient (`modProj_op_smul_of_mem`), a general identity
used by direct Hom masks.

All constructions use the two-layer `ZMod 2` mask skeleton of
`GradedEnd`/`TensorGrading` (decompose = mask₀ + mask₁).
-/
import Superfusion.Super.Bimodule
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]

private theorem zmod2_solve_one : ∀ k i : ZMod 2, 1 + k = i → k = i + 1 := by
  decide

private theorem zmod2_succ_ne : ∀ i i' : ZMod 2, i ≠ i' → i + 1 ≠ i' + 1 := by
  decide

/-! ### The grade projections of a decomposed module -/

/-- The degree-`j` projection of a decomposed module, as a linear
endomorphism (the module-level `gradeProj`). -/
noncomputable def modProj (j : ZMod 2) : M →ₗ[K] M :=
  (ℳ j).subtype ∘ₗ
    DirectSum.component K (ZMod 2) (fun i => ↥(ℳ i)) j ∘ₗ
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

theorem modProj_apply (j : ZMod 2) (m : M) :
    modProj ℳ j m = (DirectSum.decompose ℳ m j : M) := rfl

/-- On the module of a superalgebra-with-odd-part, `modProj` at degree 1
is the odd projection of M3. -/
theorem oddPartMod_eq_modProj : oddPartMod ℳ = modProj ℳ 1 := rfl

theorem modProj_mem (j : ZMod 2) (m : M) : modProj ℳ j m ∈ ℳ j := by
  rw [modProj_apply]
  exact Submodule.coe_mem _

theorem modProj_of_mem {j : ZMod 2} {m : M} (hm : m ∈ ℳ j) :
    modProj ℳ j m = m := by
  rw [modProj_apply, DirectSum.decompose_of_mem_same ℳ hm]

theorem modProj_of_mem_ne {j k : ZMod 2} {m : M} (hm : m ∈ ℳ j)
    (hjk : j ≠ k) : modProj ℳ k m = 0 := by
  rw [modProj_apply, DirectSum.decompose_of_mem_ne ℳ hm hjk]

theorem modProj_zero_add_modProj_one (m : M) :
    modProj ℳ 0 m + modProj ℳ 1 m = m := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => rw [map_zero, map_zero, add_zero]
  | @homogeneous i x =>
      rcases zmod2_cases i with hi | hi <;> subst hi
      · rw [modProj_of_mem ℳ x.2,
          modProj_of_mem_ne ℳ x.2 (by decide), add_zero]
      · rw [modProj_of_mem ℳ x.2,
          modProj_of_mem_ne ℳ x.2 (by decide), zero_add]
  | add x y hx hy =>
      rw [map_add, map_add, add_add_add_comm, hx, hy]

section LinearEquiv

variable {N : Type*} [AddCommGroup N] [Module K N]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]

/-- If a linear equivalence preserves every layer of two `ZMod 2`
decompositions, then its inverse preserves every layer as well. -/
theorem gradedLinearEquiv_symm_mem
    (e : M ≃ₗ[K] N)
    (he : ∀ {i : ZMod 2} {m : M}, m ∈ ℳ i → e m ∈ 𝒩 i)
    {i : ZMod 2} {n : N} (hn : n ∈ 𝒩 i) :
    e.symm n ∈ ℳ i := by
  let m := e.symm n
  have hme : e m = n := e.apply_symm_apply n
  have hm0 : e (modProj ℳ 0 m) ∈ 𝒩 0 :=
    he (modProj_mem ℳ 0 m)
  have hm1 : e (modProj ℳ 1 m) ∈ 𝒩 1 :=
    he (modProj_mem ℳ 1 m)
  have hsplit :
      e (modProj ℳ 0 m) + e (modProj ℳ 1 m) = n := by
    rw [← map_add, modProj_zero_add_modProj_one, hme]
  rcases zmod2_cases i with hi | hi <;> subst hi
  · have h1 : e (modProj ℳ 1 m) = 0 := by
      have h1' :
          modProj 𝒩 1
              (e (modProj ℳ 0 m) + e (modProj ℳ 1 m)) =
            e (modProj ℳ 1 m) := by
        rw [map_add, modProj_of_mem_ne 𝒩 hm0 (by decide),
          modProj_of_mem 𝒩 hm1, zero_add]
      rw [hsplit] at h1'
      rw [← h1']
      exact modProj_of_mem_ne 𝒩 hn (by decide)
    have hm1eq0 : modProj ℳ 1 m = 0 :=
      e.injective (by rw [h1, map_zero])
    have heq : m = modProj ℳ 0 m := by
      have h := modProj_zero_add_modProj_one ℳ m
      rw [hm1eq0, add_zero] at h
      exact h.symm
    change m ∈ ℳ 0
    rw [heq]
    exact modProj_mem ℳ 0 m
  · have h0 : e (modProj ℳ 0 m) = 0 := by
      have h0' :
          modProj 𝒩 0
              (e (modProj ℳ 0 m) + e (modProj ℳ 1 m)) =
            e (modProj ℳ 0 m) := by
        rw [map_add, modProj_of_mem 𝒩 hm0,
          modProj_of_mem_ne 𝒩 hm1 (by decide), add_zero]
      rw [hsplit] at h0'
      rw [← h0']
      exact modProj_of_mem_ne 𝒩 hn (by decide)
    have hm0eq0 : modProj ℳ 0 m = 0 :=
      e.injective (by rw [h0, map_zero])
    have heq : m = modProj ℳ 1 m := by
      have h := modProj_zero_add_modProj_one ℳ m
      rw [hm0eq0, zero_add] at h
      exact h.symm
    change m ∈ ℳ 1
    rw [heq]
    exact modProj_mem ℳ 1 m

end LinearEquiv

/-! ### Grade projections and graded right actions -/

section RightProjection

variable {D : Type*} [Ring D] [Algebra K D]
variable (𝒟 : ZMod 2 → Submodule K D)
variable [Module Dᵐᵒᵖ M] [GradedRightSMul 𝒟 ℳ]

private theorem zmod2_modProj_right_cancel :
    ∀ i j : ZMod 2, (j + i) + j = i := by decide

private theorem zmod2_modProj_right_cancel' :
    ∀ j k : ZMod 2, j + (k + j) = k := by decide

/-- A grade projection passes through right multiplication by a homogeneous
coefficient, with the source projection shifted by the coefficient degree. -/
theorem modProj_op_smul_of_mem {j : ZMod 2} {a : D} (ha : a ∈ 𝒟 j)
    (k : ZMod 2) (m : M) :
    modProj ℳ k (MulOpposite.op a • m) =
      MulOpposite.op a • modProj ℳ (k + j) m := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero =>
      rw [smul_zero, map_zero, map_zero, smul_zero]
  | add x y hx hy =>
      rw [smul_add, map_add, map_add, smul_add, hx, hy]
  | @homogeneous i x =>
      have hax :
          MulOpposite.op a • (x : M) ∈ ℳ (j + i) :=
        GradedRightSMul.smul_mem ha x.2
      by_cases h : j + i = k
      · have hki : k + j = i := by
          rw [← h]
          exact zmod2_modProj_right_cancel i j
        have hax' : MulOpposite.op a • (x : M) ∈ ℳ k := by
          rw [← h]
          exact hax
        have hx' : (x : M) ∈ ℳ (k + j) := by
          rw [hki]
          exact x.2
        rw [modProj_of_mem ℳ hax', modProj_of_mem ℳ hx']
      · have hikj : i ≠ k + j := by
          intro hikj
          apply h
          rw [hikj]
          exact zmod2_modProj_right_cancel' j k
        rw [modProj_of_mem_ne ℳ hax h,
          modProj_of_mem_ne ℳ x.2 hikj, smul_zero]

end RightProjection

/-! ### Spans of homogeneous elements -/

/-- A submodule spanned by homogeneous elements is homogeneous. -/
theorem isHomogeneous_span {S : Set M} (hS : ∀ s ∈ S, ∃ i, s ∈ ℳ i) :
    (Submodule.span K S).IsHomogeneous ℳ := by
  intro i m hm
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
  · intro s hs
    obtain ⟨j, hj⟩ := hS s hs
    by_cases hij : j = i
    · subst hij
      rw [DirectSum.decompose_of_mem_same ℳ hj]
      exact Submodule.subset_span hs
    · rw [DirectSum.decompose_of_mem_ne ℳ hj hij]
      exact zero_mem _
  · rw [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [DirectSum.decompose_smul, DirectSum.smul_apply, SetLike.val_smul]
    exact Submodule.smul_mem _ c hx

/-! ### Quotient gradings

The quotient of a decomposed module by a homogeneous submodule is
decomposed, with layers the images of the layers.  (Absent from
mathlib; the decomposition is by descending the grade projections.) -/

section Quotient

variable (p : Submodule K M)

/-- The grading induced on `M ⧸ p`: the images of the layers. -/
def quotGrading (i : ZMod 2) : Submodule K (M ⧸ p) :=
  (ℳ i).map p.mkQ

omit [DirectSum.Decomposition ℳ] in
theorem mem_quotGrading_iff {i : ZMod 2} {z : M ⧸ p} :
    z ∈ quotGrading ℳ p i ↔ ∃ m ∈ ℳ i, p.mkQ m = z :=
  Submodule.mem_map

omit [DirectSum.Decomposition ℳ] in
theorem mkQ_mem_quotGrading {i : ZMod 2} {m : M} (hm : m ∈ ℳ i) :
    p.mkQ m ∈ quotGrading ℳ p i :=
  Submodule.mem_map_of_mem hm

variable {p}

/-- The grade projections descend to the quotient by a homogeneous
submodule. -/
noncomputable def quotProj (hp : p.IsHomogeneous ℳ) (i : ZMod 2) :
    M ⧸ p →ₗ[K] M ⧸ p :=
  p.liftQ (p.mkQ ∘ₗ modProj ℳ i) (fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, modProj_apply]
    exact hp i hx)

theorem quotProj_mk (hp : p.IsHomogeneous ℳ) (i : ZMod 2) (x : M) :
    quotProj ℳ hp i (p.mkQ x) = p.mkQ (modProj ℳ i x) := rfl

theorem quotProj_mem (hp : p.IsHomogeneous ℳ) (i : ZMod 2) (z : M ⧸ p) :
    quotProj ℳ hp i z ∈ quotGrading ℳ p i := by
  obtain ⟨x, rfl⟩ := p.mkQ_surjective z
  rw [quotProj_mk]
  exact mkQ_mem_quotGrading ℳ p (modProj_mem ℳ i x)

theorem quotProj_of_mem (hp : p.IsHomogeneous ℳ) {i : ZMod 2} {z : M ⧸ p}
    (hz : z ∈ quotGrading ℳ p i) : quotProj ℳ hp i z = z := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff ℳ p).mp hz
  rw [quotProj_mk, modProj_of_mem ℳ hx]

theorem quotProj_of_mem_ne (hp : p.IsHomogeneous ℳ) {i i' : ZMod 2}
    {z : M ⧸ p} (hz : z ∈ quotGrading ℳ p i) (hii' : i ≠ i') :
    quotProj ℳ hp i' z = 0 := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff ℳ p).mp hz
  rw [quotProj_mk, modProj_of_mem_ne ℳ hx hii', map_zero]

theorem quotProj_zero_add_quotProj_one (hp : p.IsHomogeneous ℳ)
    (z : M ⧸ p) :
    quotProj ℳ hp 0 z + quotProj ℳ hp 1 z = z := by
  obtain ⟨x, rfl⟩ := p.mkQ_surjective z
  rw [quotProj_mk, quotProj_mk, ← map_add, modProj_zero_add_modProj_one]

/-- The degree-`i` descent, corestricted to the layer. -/
noncomputable def quotProjInto (hp : p.IsHomogeneous ℳ) (i : ZMod 2) :
    M ⧸ p →ₗ[K] quotGrading ℳ p i :=
  LinearMap.codRestrict (quotGrading ℳ p i) (quotProj ℳ hp i)
    (quotProj_mem ℳ hp i)

/-- **The quotient of a decomposed module by a homogeneous submodule is
decomposed.**  An `abbrev` (the homogeneity is a hypothesis, so this
cannot be an instance), to be activated with `letI` where needed. -/
noncomputable abbrev quotDecomposition (hp : p.IsHomogeneous ℳ) :
    DirectSum.Decomposition (quotGrading ℳ p) where
  decompose' z :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(quotGrading ℳ p i)) 0
        (quotProjInto ℳ hp 0 z)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(quotGrading ℳ p i)) 1
        (quotProjInto ℳ hp 1 z)
  left_inv z := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact quotProj_zero_add_quotProj_one ℳ hp z
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
          have h1 : quotProjInto ℳ hp 0 (b : M ⧸ p) = b :=
            Subtype.ext (quotProj_of_mem ℳ hp b.2)
          have h2 : quotProjInto ℳ hp 1 (b : M ⧸ p) = 0 :=
            Subtype.ext (quotProj_of_mem_ne ℳ hp b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : quotProjInto ℳ hp 0 (b : M ⧸ p) = 0 :=
            Subtype.ext (quotProj_of_mem_ne ℳ hp b.2 (by decide))
          have h2 : quotProjInto ℳ hp 1 (b : M ⧸ p) = b :=
            Subtype.ext (quotProj_of_mem ℳ hp b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

end Quotient

/-! ### The tensor grading of decomposed modules

The module-level counterpart of `Superfusion.tensorGrading` (M7f-1a):
degree `i` of `M ⊗[K] N` is spanned by the homogeneous tensors
`m ⊗ₜ n` with `|m| + |n| = i`. -/

section Tensor

variable {N : Type*} [AddCommGroup N] [Module K N]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]

/-- The parity grading on `M ⊗[K] N` of two decomposed modules. -/
noncomputable def tensorGrading (i : ZMod 2) : Submodule K (M ⊗[K] N) :=
  Submodule.span K
    {z | ∃ (j k : ZMod 2) (m : M) (n : N),
      j + k = i ∧ m ∈ ℳ j ∧ n ∈ 𝒩 k ∧ m ⊗ₜ[K] n = z}

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] in
theorem tmul_mem_tensorGrading {j k : ZMod 2} {m : M} {n : N}
    (hm : m ∈ ℳ j) (hn : n ∈ 𝒩 k) :
    m ⊗ₜ[K] n ∈ tensorGrading ℳ 𝒩 (j + k) :=
  Submodule.subset_span ⟨j, k, m, n, rfl, hm, hn, rfl⟩

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] in
/-- Induction principle for membership in the tensor grading. -/
theorem tensorGrading_induction {i : ZMod 2}
    {motive : M ⊗[K] N → Prop} {z : M ⊗[K] N}
    (hz : z ∈ tensorGrading ℳ 𝒩 i)
    (tmul : ∀ (j k : ZMod 2) (m : M) (n : N), j + k = i → m ∈ ℳ j →
      n ∈ 𝒩 k → motive (m ⊗ₜ[K] n))
    (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (c : K) x, motive x → motive (c • x)) : motive z := by
  refine Submodule.span_induction ?_ zero
    (fun x y _ _ hx hy => add x y hx hy)
    (fun c x _ hx => smul c x hx) hz
  rintro z ⟨j, k, m, n, hjk, hm, hn, rfl⟩
  exact tmul j k m n hjk hm hn

/-- The degree-`i` mask on the tensor product. -/
noncomputable def tensorMask (i : ZMod 2) :
    M ⊗[K] N →ₗ[K] M ⊗[K] N :=
  TensorProduct.map (modProj ℳ 0) (modProj 𝒩 i)
    + TensorProduct.map (modProj ℳ 1) (modProj 𝒩 (i + 1))

theorem tensorMask_tmul (i : ZMod 2) (m : M) (n : N) :
    tensorMask ℳ 𝒩 i (m ⊗ₜ[K] n)
      = (modProj ℳ 0 m) ⊗ₜ[K] (modProj 𝒩 i n)
        + (modProj ℳ 1 m) ⊗ₜ[K] (modProj 𝒩 (i + 1) n) := by
  rw [tensorMask, LinearMap.add_apply, TensorProduct.map_tmul,
    TensorProduct.map_tmul]

private theorem zmod2_mask_index : ∀ i : ZMod 2, 1 + (i + 1) = i := by
  decide

theorem tensorMask_mem (i : ZMod 2) (z : M ⊗[K] N) :
    tensorMask ℳ 𝒩 i z ∈ tensorGrading ℳ 𝒩 i := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul m n =>
      rw [tensorMask_tmul]
      refine add_mem ?_ ?_
      · have h := tmul_mem_tensorGrading ℳ 𝒩 (modProj_mem ℳ 0 m)
          (modProj_mem 𝒩 i n)
        rwa [zero_add] at h
      · have h := tmul_mem_tensorGrading ℳ 𝒩 (modProj_mem ℳ 1 m)
          (modProj_mem 𝒩 (i + 1) n)
        rwa [zmod2_mask_index] at h
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem tensorMask_zero_add_tensorMask_one (z : M ⊗[K] N) :
    tensorMask ℳ 𝒩 0 z + tensorMask ℳ 𝒩 1 z = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, add_zero]
  | tmul m n =>
      rw [tensorMask_tmul, tensorMask_tmul,
        show (0 : ZMod 2) + 1 = 1 from by decide,
        show (1 : ZMod 2) + 1 = 0 from by decide,
        add_add_add_comm, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add,
        add_comm (modProj 𝒩 1 n) (modProj 𝒩 0 n),
        ← TensorProduct.add_tmul, modProj_zero_add_modProj_one,
        modProj_zero_add_modProj_one]
  | add x y hx hy =>
      rw [map_add, map_add, add_add_add_comm, hx, hy]

theorem tensorMask_of_mem {i : ZMod 2} {z : M ⊗[K] N}
    (hz : z ∈ tensorGrading ℳ 𝒩 i) : tensorMask ℳ 𝒩 i z = z := by
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w => tensorMask ℳ 𝒩 i w = w)
    hz ?_ (map_zero (tensorMask ℳ 𝒩 i)) ?_ ?_
  · intro j k m n hjk hm hn
    rw [tensorMask_tmul]
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [zero_add] at hjk
      subst hjk
      rw [modProj_of_mem ℳ hm, modProj_of_mem 𝒩 hn,
        modProj_of_mem_ne ℳ hm (by decide), TensorProduct.zero_tmul,
        add_zero]
    · have hk := zmod2_solve_one k i hjk
      subst hk
      rw [modProj_of_mem ℳ hm, modProj_of_mem 𝒩 hn,
        modProj_of_mem_ne ℳ hm (by decide), TensorProduct.zero_tmul,
        zero_add]
  · intro x y hx hy
    rw [map_add, hx, hy]
  · intro c x hx
    rw [map_smul, hx]

theorem tensorMask_of_mem_ne {i i' : ZMod 2} {z : M ⊗[K] N}
    (hz : z ∈ tensorGrading ℳ 𝒩 i) (hii' : i ≠ i') :
    tensorMask ℳ 𝒩 i' z = 0 := by
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w => tensorMask ℳ 𝒩 i' w = 0)
    hz ?_ (map_zero (tensorMask ℳ 𝒩 i')) ?_ ?_
  · intro j k m n hjk hm hn
    rw [tensorMask_tmul]
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [zero_add] at hjk
      subst hjk
      rw [modProj_of_mem_ne 𝒩 hn hii', TensorProduct.tmul_zero,
        modProj_of_mem_ne ℳ hm (by decide), TensorProduct.zero_tmul,
        add_zero]
    · have hk := zmod2_solve_one k i hjk
      subst hk
      rw [modProj_of_mem_ne ℳ hm (by decide), TensorProduct.zero_tmul,
        modProj_of_mem_ne 𝒩 hn (zmod2_succ_ne i i' hii'),
        TensorProduct.tmul_zero, add_zero]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x hx
    rw [map_smul, hx, smul_zero]

/-- The degree-`i` mask, corestricted to the layer. -/
noncomputable def tensorMaskInto (i : ZMod 2) :
    M ⊗[K] N →ₗ[K] tensorGrading ℳ 𝒩 i :=
  LinearMap.codRestrict (tensorGrading ℳ 𝒩 i) (tensorMask ℳ 𝒩 i)
    (tensorMask_mem ℳ 𝒩 i)

/-- **The tensor product of decomposed modules is decomposed.** -/
noncomputable instance : DirectSum.Decomposition (tensorGrading ℳ 𝒩) where
  decompose' z :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(tensorGrading ℳ 𝒩 i)) 0
        (tensorMaskInto ℳ 𝒩 0 z)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(tensorGrading ℳ 𝒩 i)) 1
        (tensorMaskInto ℳ 𝒩 1 z)
  left_inv z := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact tensorMask_zero_add_tensorMask_one ℳ 𝒩 z
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
          have h1 : tensorMaskInto ℳ 𝒩 0 (b : M ⊗[K] N) = b :=
            Subtype.ext (tensorMask_of_mem ℳ 𝒩 b.2)
          have h2 : tensorMaskInto ℳ 𝒩 1 (b : M ⊗[K] N) = 0 :=
            Subtype.ext (tensorMask_of_mem_ne ℳ 𝒩 b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : tensorMaskInto ℳ 𝒩 0 (b : M ⊗[K] N) = 0 :=
            Subtype.ext (tensorMask_of_mem_ne ℳ 𝒩 b.2 (by decide))
          have h2 : tensorMaskInto ℳ 𝒩 1 (b : M ⊗[K] N) = b :=
            Subtype.ext (tensorMask_of_mem ℳ 𝒩 b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

end Tensor

end Bimod

end Superfusion

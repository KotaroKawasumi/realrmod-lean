/-
Superfusion / Bimod / OuterActions

Milestone M8a-4a: **the outer bimodule structure of the balanced tensor
product**.  For `M` a `(B, A)`-bimodule and `N` an `(A, C)`-bimodule
(sign-free axioms: the outer actions strictly commute with the inner
`A`-actions), the outer actions descend to `M ⊗[A] N`:

* `b · (m ⊗ n) = (b · m) ⊗ n` (`leftActionEnd`, an algebra map
  `B →ₐ End_K`),
* `(m ⊗ n) · c = m ⊗ (n · c)` (`rightActionEnd`, an algebra map
  `Cᵐᵒᵖ →ₐ End_K`),

they commute with each other (`leftActionEnd_comm_rightActionEnd`), and
they are graded for `relGrading` when the outer actions are graded
(`leftActionEnd_mem_relGrading`, `rightActionEnd_mem_relGrading`).
Thus `M ⊗[A] N` is a super `(B, C)`-bimodule in the sense of M8a-1 —
the paper's `B_L`, `B_R` (§4.1) receive their outer structure this way.
Well-definedness is `RelTensor.lift` against the balancing relation
each time; no Koszul sign enters (the signed middle action for
`B ᵍ⊗ C`-shaped outer algebras is deferred to the `B_L` construction).

The `Module` packagings (`leftModule`, `rightModule`) are `abbrev`s to
be activated with `letI`, mirroring `TensorProduct.Algebra.module`.
-/
import Superfusion.Bimod.RelTensorGraded

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]

/-! ### The left outer action -/

section Left

variable {B : Type*} [Ring B] [Algebra K B]
variable [Module B M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower K B M]
variable (K A M N)

private theorem leftBalanced (b : B) :
    RelTensor.IsBalanced A
      ((RelTensor.mk K A M N).comp (Algebra.lsmul K K M b : M →ₗ[K] M)) := by
  intro a m n
  show RelTensor.mk K A M N (b • MulOpposite.op a • m) n
      = RelTensor.mk K A M N (b • m) (a • n)
  rw [smul_comm b (MulOpposite.op a) m, RelTensor.mk_op_smul]

private noncomputable def leftEnd (b : B) :
    (M ⊗[A;K] N) →ₗ[K] M ⊗[A;K] N :=
  RelTensor.lift
    ((RelTensor.mk K A M N).comp (Algebra.lsmul K K M b : M →ₗ[K] M))
    (leftBalanced K A M N b)

private theorem leftEnd_mk (b : B) (m : M) (n : N) :
    leftEnd K A M N b (RelTensor.mk K A M N m n)
      = RelTensor.mk K A M N (b • m) n := by
  show RelTensor.lift _ (leftBalanced K A M N b) (RelTensor.mk K A M N m n)
      = _
  rw [RelTensor.lift_mk]
  rfl

/-- The outer left `B`-action on `M ⊗[A] N`, as an algebra map into the
`K`-endomorphisms: `b · (m ⊗ n) = (b · m) ⊗ n`.  Well-defined by the
sign-free bimodule axiom `SMulCommClass B Aᵐᵒᵖ M`. -/
noncomputable def leftActionEnd :
    B →ₐ[K] Module.End K (M ⊗[A;K] N) where
  toFun := leftEnd K A M N
  map_one' := RelTensor.hom_ext fun m n => by
    simp only [leftEnd_mk, one_smul, Module.End.one_apply]
  map_mul' b b' := RelTensor.hom_ext fun m n => by
    simp only [Module.End.mul_apply, leftEnd_mk, mul_smul]
  map_zero' := RelTensor.hom_ext fun m n => by
    simp only [leftEnd_mk, zero_smul, map_zero, LinearMap.zero_apply]
  map_add' b b' := RelTensor.hom_ext fun m n => by
    simp only [leftEnd_mk, add_smul, map_add, LinearMap.add_apply]
  commutes' r := RelTensor.hom_ext fun m n => by
    simp only [leftEnd_mk, Module.algebraMap_end_apply, algebraMap_smul,
      map_smul, LinearMap.smul_apply]

theorem leftActionEnd_mk (b : B) (m : M) (n : N) :
    leftActionEnd K A M N b (RelTensor.mk K A M N m n)
      = RelTensor.mk K A M N (b • m) n :=
  leftEnd_mk K A M N b m n

/-- The outer left action, packaged as a `Module`.  An `abbrev` to be
activated with `letI`, mirroring `TensorProduct.Algebra.module`. -/
noncomputable abbrev leftModule : Module B (M ⊗[A;K] N) :=
  Module.compHom _ (leftActionEnd K A M N (B := B)).toRingHom

/-- Restriction of the descended left action along `K → B` agrees
with the given `K`-module structure. -/
theorem leftScalarTower :
    letI := leftModule K A M N (B := B)
    IsScalarTower K B (M ⊗[A;K] N) := by
  letI := leftModule K A M N (B := B)
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  change leftActionEnd K A M N (algebraMap K B r) z = r • z
  rw [(leftActionEnd K A M N (B := B)).commutes,
    Module.algebraMap_end_apply]

end Left

/-! ### The right outer action -/

section Right

variable {C : Type*} [Ring C] [Algebra K C]
variable [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N] [IsScalarTower K Cᵐᵒᵖ N]
variable (K A M N)

private theorem rightBalanced (c : Cᵐᵒᵖ) :
    RelTensor.IsBalanced A
      ((RelTensor.mk K A M N).compl₂
        (rsmulBilin (K := K) (MulOpposite.unop c))) := by
  intro a m n
  show RelTensor.mk K A M N (MulOpposite.op a • m)
        (MulOpposite.op (MulOpposite.unop c) • n)
      = RelTensor.mk K A M N m
          (MulOpposite.op (MulOpposite.unop c) • (a • n))
  rw [MulOpposite.op_unop, RelTensor.mk_op_smul, smul_comm a c n]

private noncomputable def rightEnd (c : Cᵐᵒᵖ) :
    (M ⊗[A;K] N) →ₗ[K] M ⊗[A;K] N :=
  RelTensor.lift
    ((RelTensor.mk K A M N).compl₂
      (rsmulBilin (K := K) (MulOpposite.unop c)))
    (rightBalanced K A M N c)

private theorem rightEnd_mk (c : Cᵐᵒᵖ) (m : M) (n : N) :
    rightEnd K A M N c (RelTensor.mk K A M N m n)
      = RelTensor.mk K A M N m (c • n) := by
  show RelTensor.lift _ (rightBalanced K A M N c) (RelTensor.mk K A M N m n)
      = _
  rw [RelTensor.lift_mk]
  show RelTensor.mk K A M N m
      (MulOpposite.op (MulOpposite.unop c) • n) = _
  rw [MulOpposite.op_unop]

/-- The outer right `C`-action on `M ⊗[A] N`, as an algebra map from
`Cᵐᵒᵖ` into the `K`-endomorphisms: `(m ⊗ n) · c = m ⊗ (n · c)`.
Well-defined by the sign-free bimodule axiom
`SMulCommClass A Cᵐᵒᵖ N`. -/
noncomputable def rightActionEnd :
    Cᵐᵒᵖ →ₐ[K] Module.End K (M ⊗[A;K] N) where
  toFun := rightEnd K A M N
  map_one' := RelTensor.hom_ext fun m n => by
    simp only [rightEnd_mk, one_smul, Module.End.one_apply]
  map_mul' c c' := RelTensor.hom_ext fun m n => by
    simp only [Module.End.mul_apply, rightEnd_mk, mul_smul]
  map_zero' := RelTensor.hom_ext fun m n => by
    simp only [rightEnd_mk, zero_smul, map_zero, LinearMap.zero_apply]
  map_add' c c' := RelTensor.hom_ext fun m n => by
    simp only [rightEnd_mk, add_smul, map_add, LinearMap.add_apply]
  commutes' r := RelTensor.hom_ext fun m n => by
    simp only [rightEnd_mk, Module.algebraMap_end_apply, algebraMap_smul,
      map_smul]

theorem rightActionEnd_mk (c : Cᵐᵒᵖ) (m : M) (n : N) :
    rightActionEnd K A M N c (RelTensor.mk K A M N m n)
      = RelTensor.mk K A M N m (c • n) :=
  rightEnd_mk K A M N c m n

/-- The outer right action, packaged as a `Module`.  An `abbrev` to be
activated with `letI`. -/
noncomputable abbrev rightModule : Module Cᵐᵒᵖ (M ⊗[A;K] N) :=
  Module.compHom _ (rightActionEnd K A M N (C := C)).toRingHom

/-- Restriction of the descended right action along `K → Cᵐᵒᵖ`
agrees with the given `K`-module structure. -/
theorem rightScalarTower :
    letI := rightModule K A M N (C := C)
    IsScalarTower K Cᵐᵒᵖ (M ⊗[A;K] N) := by
  letI := rightModule K A M N (C := C)
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  change rightActionEnd K A M N
      (algebraMap K Cᵐᵒᵖ r) z = r • z
  rw [(rightActionEnd K A M N (C := C)).commutes,
    Module.algebraMap_end_apply]

/-- Ground-field scalars commute with the descended right action. -/
theorem rightScalarComm :
    letI := rightModule K A M N (C := C)
    SMulCommClass K Cᵐᵒᵖ (M ⊗[A;K] N) := by
  letI := rightModule K A M N (C := C)
  constructor
  intro r c z
  change r • rightActionEnd K A M N c z =
    rightActionEnd K A M N c (r • z)
  exact ((rightActionEnd K A M N c).map_smul r z).symm

end Right

/-! ### The two outer actions commute (sign-free axiom, descended) -/

section Comm

variable {B : Type*} [Ring B] [Algebra K B]
variable [Module B M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower K B M]
variable {C : Type*} [Ring C] [Algebra K C]
variable [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N] [IsScalarTower K Cᵐᵒᵖ N]
variable (K A M N)

theorem leftActionEnd_comm_rightActionEnd (b : B) (c : Cᵐᵒᵖ) :
    leftActionEnd K A M N b * rightActionEnd K A M N c
      = rightActionEnd K A M N c * leftActionEnd K A M N b := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, rightActionEnd_mk,
    leftActionEnd_mk, leftActionEnd_mk, rightActionEnd_mk]

end Comm

/-! ### Gradedness of the outer actions -/

section Graded

variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]

section LeftGraded

variable {B : Type*} [Ring B] [Algebra K B]
variable [Module B M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower K B M]
variable {ℬ : ZMod 2 → Submodule K B} [SetLike.GradedSMul ℬ ℳ]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] in
/-- The outer left action is graded: the content of
`SetLike.GradedSMul ℬ (relGrading A ℳ 𝒩)` once the `Module` is
activated. -/
theorem leftActionEnd_mem_relGrading {i j : ZMod 2} {b : B}
    (hb : b ∈ ℬ i) {z : M ⊗[A;K] N} (hz : z ∈ relGrading A ℳ 𝒩 j) :
    leftActionEnd K A M N b z ∈ relGrading A ℳ 𝒩 (i + j) := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒩)
    (balancer K A M N)).mp hz
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w =>
      leftActionEnd K A M N b (RelTensor.fromTensor K A M N w)
        ∈ relGrading A ℳ 𝒩 (i + j)) hx ?_ ?_ ?_ ?_
  · intro j' k' m n hjk hm hn
    show leftActionEnd K A M N b (RelTensor.mk K A M N m n)
        ∈ relGrading A ℳ 𝒩 (i + j)
    rw [leftActionEnd_mk]
    have h := mk_mem_relGrading (A := A) ℳ 𝒩 (SetLike.GradedSMul.smul_mem hb hm) hn
    rwa [vadd_eq_add, add_assoc, hjk] at h
  · rw [map_zero, map_zero]
    exact zero_mem _
  · intro x y hx hy
    rw [map_add, map_add]
    exact add_mem hx hy
  · intro c x hx
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ c hx

end LeftGraded

section RightGraded

variable {C : Type*} [Ring C] [Algebra K C]
variable [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N] [IsScalarTower K Cᵐᵒᵖ N]
variable {𝒞 : ZMod 2 → Submodule K C} [GradedRightSMul 𝒞 𝒩]

private theorem zmod2_right_deg :
    ∀ i j' k' : ZMod 2, j' + (i + k') = i + (j' + k') := by
  decide

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] in
/-- The outer right action is graded: the content of
`GradedRightSMul 𝒞 (relGrading A ℳ 𝒩)` once the `Module` is
activated. -/
theorem rightActionEnd_mem_relGrading {i j : ZMod 2} {c : C}
    (hc : c ∈ 𝒞 i) {z : M ⊗[A;K] N} (hz : z ∈ relGrading A ℳ 𝒩 j) :
    rightActionEnd K A M N (MulOpposite.op c) z
      ∈ relGrading A ℳ 𝒩 (i + j) := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒩)
    (balancer K A M N)).mp hz
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w =>
      rightActionEnd K A M N (MulOpposite.op c)
          (RelTensor.fromTensor K A M N w)
        ∈ relGrading A ℳ 𝒩 (i + j)) hx ?_ ?_ ?_ ?_
  · intro j' k' m n hjk hm hn
    show rightActionEnd K A M N (MulOpposite.op c)
        (RelTensor.mk K A M N m n) ∈ relGrading A ℳ 𝒩 (i + j)
    rw [rightActionEnd_mk]
    have h := mk_mem_relGrading (A := A) ℳ 𝒩 hm (GradedRightSMul.smul_mem hc hn)
    rwa [zmod2_right_deg, hjk] at h
  · rw [map_zero, map_zero]
    exact zero_mem _
  · intro x y hx hy
    rw [map_add, map_add]
    exact add_mem hx hy
  · intro c' x hx
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ c' hx

end RightGraded

end Graded

end Bimod

end Superfusion

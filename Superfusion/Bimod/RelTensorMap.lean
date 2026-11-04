/-
Superfusion / Bimod / RelTensorMap

Milestone M8a-4b: **functoriality and the unitors of the balanced
tensor product**.

* `RelTensor.map f g` — a right-`A`-equivariant map `f : M → M'` and a
  left-`A`-equivariant map `g : N → N'` induce
  `M ⊗[A] N →ₗ M' ⊗[A] N'`, functorially (`map_id`, `map_comp`), and
  gradedly when `f`, `g` are homogeneous (`map_mem_relGrading`).
* `RelTensor.lunitor : A ⊗[A] N ≃ₗ N` and
  `RelTensor.runitor : M ⊗[A] A ≃ₗ M` — the unit isomorphisms, with
  their action-equivariance and gradedness.

These are the connecting maps used everywhere in §4: the intertwiners
`t_{a,b,c}` are (in particular) maps between balanced tensor products,
and the unit coherence of the paper's tower uses the unitors.
-/
import Superfusion.Bimod.OuterActions

namespace Superfusion

namespace Bimod

namespace RelTensor

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]

/-! ### Functoriality -/

section Map

variable {M' : Type*} [AddCommGroup M'] [Module K M'] [Module Aᵐᵒᵖ M']
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module A N']
variable (f : M →ₗ[K] M') (g : N →ₗ[K] N')

private theorem map_balanced
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n) :
    IsBalanced A ((mk K A M' N').compl₁₂ f g) := by
  intro a m n
  show mk K A M' N' (f (MulOpposite.op a • m)) (g n)
      = mk K A M' N' (f m) (g (a • n))
  rw [hf, hg, mk_op_smul]

/-- A right-`A`-equivariant map and a left-`A`-equivariant map induce a
map of balanced tensor products, `(m ⊗ n) ↦ (f m ⊗ g n)`. -/
noncomputable def map
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n) :
    (M ⊗[A;K] N) →ₗ[K] M' ⊗[A;K] N' :=
  lift ((mk K A M' N').compl₁₂ f g) (map_balanced f g hf hg)

theorem map_mk
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n) (m : M) (n : N) :
    map f g hf hg (mk K A M N m n) = mk K A M' N' (f m) (g n) := by
  show lift _ (map_balanced f g hf hg) (mk K A M N m n) = _
  rw [lift_mk]
  rfl

theorem map_id :
    map (A := A) (LinearMap.id : M →ₗ[K] M) (LinearMap.id : N →ₗ[K] N)
      (fun _ _ => rfl) (fun _ _ => rfl) = LinearMap.id := by
  refine hom_ext fun m n => ?_
  simp only [map_mk, LinearMap.id_apply]

theorem map_comp {M'' : Type*} [AddCommGroup M''] [Module K M'']
    [Module Aᵐᵒᵖ M'']
    {N'' : Type*} [AddCommGroup N''] [Module K N''] [Module A N'']
    (f' : M' →ₗ[K] M'') (g' : N' →ₗ[K] N'')
    (hf' : ∀ (a : A) (m : M'),
      f' (MulOpposite.op a • m) = MulOpposite.op a • f' m)
    (hg' : ∀ (a : A) (n : N'), g' (a • n) = a • g' n)
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n) :
    map (f'.comp f) (g'.comp g)
        (fun a m => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hf'])
        (fun a n => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hg, hg'])
      = (map f' g' hf' hg').comp (map f g hf hg) := by
  refine hom_ext fun m n => ?_
  simp only [map_mk, LinearMap.comp_apply]

section MapGraded

variable (ℳ : ZMod 2 → Submodule K M) (𝒩 : ZMod 2 → Submodule K N)
variable (ℳ' : ZMod 2 → Submodule K M') (𝒩' : ZMod 2 → Submodule K N')

omit [Module Aᵐᵒᵖ M'] [Module A N'] in
private theorem map_tensorGrading_mem {i : ZMod 2} {x : M ⊗[K] N}
    (hx : x ∈ tensorGrading ℳ 𝒩 i)
    (hfd : ∀ j : ZMod 2, ∀ m ∈ ℳ j, f m ∈ ℳ' j)
    (hgd : ∀ j : ZMod 2, ∀ n ∈ 𝒩 j, g n ∈ 𝒩' j) :
    TensorProduct.map f g x ∈ tensorGrading ℳ' 𝒩' i := by
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w => TensorProduct.map f g w ∈ tensorGrading ℳ' 𝒩' i)
    hx ?_ ?_ ?_ ?_
  · intro j k m n hjk hm hn
    rw [TensorProduct.map_tmul]
    exact hjk ▸ tmul_mem_tensorGrading ℳ' 𝒩' (hfd j m hm) (hgd k n hn)
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy
  · intro c x hx
    rw [map_smul]; exact Submodule.smul_mem _ c hx

end MapGraded

/-- `map` intertwines the projections from the `K`-tensor products. -/
theorem map_fromTensor
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n) (x : M ⊗[K] N) :
    map f g hf hg (fromTensor K A M N x)
      = fromTensor K A M' N' (TensorProduct.map f g x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul m n =>
      rw [TensorProduct.map_tmul]
      exact map_mk f g hf hg m n
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]

section MapGraded2

variable (ℳ : ZMod 2 → Submodule K M) (𝒩 : ZMod 2 → Submodule K N)
variable (ℳ' : ZMod 2 → Submodule K M') (𝒩' : ZMod 2 → Submodule K N')

/-- `map` is graded when `f` and `g` are. -/
theorem map_mem_relGrading
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n)
    (hfd : ∀ j : ZMod 2, ∀ m ∈ ℳ j, f m ∈ ℳ' j)
    (hgd : ∀ j : ZMod 2, ∀ n ∈ 𝒩 j, g n ∈ 𝒩' j)
    {i : ZMod 2} {z : M ⊗[A;K] N} (hz : z ∈ relGrading A ℳ 𝒩 i) :
    map f g hf hg z ∈ relGrading A ℳ' 𝒩' i := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒩)
    (balancer K A M N)).mp hz
  show map f g hf hg (fromTensor K A M N x) ∈ relGrading A ℳ' 𝒩' i
  rw [map_fromTensor]
  exact fromTensor_mem_relGrading ℳ' 𝒩'
    (map_tensorGrading_mem f g ℳ 𝒩 ℳ' 𝒩' hx hfd hgd)

end MapGraded2

end Map

/-! ### The left unitor `A ⊗[A] N ≃ N` -/

section Lunitor

variable (K A N)
variable [Algebra K A] [IsScalarTower K A N]

/-- The left action of `A` on `N` as a `K`-bilinear map. -/
private noncomputable def lsmulBilin : A →ₗ[K] N →ₗ[K] N :=
  LinearMap.mk₂ K (fun a n => a • n)
    (fun a a' n => add_smul a a' n)
    (fun c a n => smul_assoc c a n)
    (fun a n n' => smul_add a n n')
    (fun c a n => smul_comm a c n)

private theorem lsmulBilin_balanced : IsBalanced A (lsmulBilin K A N) := by
  intro a m n
  show (MulOpposite.op a • m) • n = m • (a • n)
  rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_smul]

/-- **The left unitor** `A ⊗[A] N ≃ N`, `a ⊗ n ↦ a • n`. -/
noncomputable def lunitor : (A ⊗[A;K] N) ≃ₗ[K] N :=
  LinearEquiv.ofLinear
    (lift (lsmulBilin K A N) (lsmulBilin_balanced K A N))
    (mk K A A N 1)
    (LinearMap.ext fun n => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      show lift _ (lsmulBilin_balanced K A N) (mk K A A N 1 n) = n
      rw [lift_mk]
      show (1 : A) • n = n
      rw [one_smul])
    (hom_ext fun a n => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      show mk K A A N 1 (lift _ (lsmulBilin_balanced K A N) (mk K A A N a n))
          = mk K A A N a n
      rw [lift_mk]
      show mk K A A N 1 (a • n) = mk K A A N a n
      rw [← mk_op_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        one_mul])

theorem lunitor_mk (a : A) (n : N) :
    lunitor K A N (mk K A A N a n) = a • n := by
  show lift _ (lsmulBilin_balanced K A N) (mk K A A N a n) = a • n
  rw [lift_mk]
  rfl

theorem lunitor_symm_apply (n : N) :
    (lunitor K A N).symm n = mk K A A N 1 n := rfl

/-- The left unitor is graded (with `A` graded as a module over
itself). -/
theorem lunitor_mem (𝒜 : ZMod 2 → Submodule K A)
    (𝒩 : ZMod 2 → Submodule K N) [SetLike.GradedSMul 𝒜 𝒩]
    {i : ZMod 2} {z : A ⊗[A;K] N} (hz : z ∈ relGrading A 𝒜 𝒩 i) :
    lunitor K A N z ∈ 𝒩 i := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading 𝒜 𝒩)
    (balancer K A A N)).mp hz
  refine tensorGrading_induction 𝒜 𝒩
    (motive := fun w => lunitor K A N (fromTensor K A A N w) ∈ 𝒩 i)
    hx ?_ ?_ ?_ ?_
  · intro j k a n hjk ha hn
    show lunitor K A N (mk K A A N a n) ∈ 𝒩 i
    rw [lunitor_mk]
    have h := SetLike.GradedSMul.smul_mem ha hn
    rwa [vadd_eq_add, hjk] at h
  · rw [map_zero, map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add, map_add]; exact add_mem hx hy
  · intro c x hx
    rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hx

end Lunitor

/-! ### The right unitor `M ⊗[A] A ≃ M` -/

section Runitor

variable (K A M)
variable [Algebra K A] [IsScalarTower K Aᵐᵒᵖ M]

private theorem rsmulBilin_balanced :
    IsBalanced A ((rsmulBilin (K := K) (A := A) (M := M)).flip) := by
  intro a m x
  show MulOpposite.op x • MulOpposite.op a • m
      = MulOpposite.op (a • x) • m
  rw [← mul_smul, ← MulOpposite.op_mul]
  rfl

/-- **The right unitor** `M ⊗[A] A ≃ M`, `m ⊗ a ↦ m · a`. -/
noncomputable def runitor : (M ⊗[A;K] A) ≃ₗ[K] M :=
  LinearEquiv.ofLinear
    (lift ((rsmulBilin (K := K) (A := A) (M := M)).flip)
      (rsmulBilin_balanced K A M))
    ((mk K A M A).flip 1)
    (LinearMap.ext fun m => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      show lift _ (rsmulBilin_balanced K A M) (mk K A M A m 1) = m
      rw [lift_mk]
      show MulOpposite.op (1 : A) • m = m
      rw [MulOpposite.op_one, one_smul])
    (hom_ext fun m a => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      show mk K A M A (lift _ (rsmulBilin_balanced K A M) (mk K A M A m a)) 1
          = mk K A M A m a
      rw [lift_mk]
      show mk K A M A (MulOpposite.op a • m) 1 = mk K A M A m a
      rw [mk_op_smul]
      show mk K A M A m (a • 1) = mk K A M A m a
      rw [smul_eq_mul, mul_one])

theorem runitor_mk (m : M) (a : A) :
    runitor K A M (mk K A M A m a) = MulOpposite.op a • m := by
  show lift _ (rsmulBilin_balanced K A M) (mk K A M A m a) = _
  rw [lift_mk]
  rfl

theorem runitor_symm_apply (m : M) :
    (runitor K A M).symm m = mk K A M A m 1 := rfl

/-- The right unitor intertwines the outer right action on
`M ⊗[A] A` with the original right action on `M`. -/
theorem runitor_rightActionEnd (d : A) (z : M ⊗[A;K] A) :
    runitor K A M (rightActionEnd K A M A (MulOpposite.op d) z) =
      MulOpposite.op d • runitor K A M z := by
  induction z using induction_on with
  | zero =>
      simp only [map_zero, smul_zero]
  | mk m a =>
    rw [rightActionEnd_mk, runitor_mk, runitor_mk]
    change MulOpposite.op (a * d) • m =
      MulOpposite.op d • MulOpposite.op a • m
    rw [← mul_smul, ← MulOpposite.op_mul]
  | add x y hx hy =>
      simp only [map_add, smul_add, hx, hy]

/-- The right unitor is graded (with `A` graded as a module over
itself). -/
theorem runitor_mem (ℳ : ZMod 2 → Submodule K M)
    (𝒜 : ZMod 2 → Submodule K A) [GradedRightSMul 𝒜 ℳ]
    {i : ZMod 2} {z : M ⊗[A;K] A} (hz : z ∈ relGrading A ℳ 𝒜 i) :
    runitor K A M z ∈ ℳ i := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒜)
    (balancer K A M A)).mp hz
  refine tensorGrading_induction ℳ 𝒜
    (motive := fun w => runitor K A M (fromTensor K A M A w) ∈ ℳ i)
    hx ?_ ?_ ?_ ?_
  · intro j k m a hjk hm ha
    show runitor K A M (mk K A M A m a) ∈ ℳ i
    rw [runitor_mk]
    have h := GradedRightSMul.smul_mem ha hm
    rwa [add_comm k j, hjk] at h
  · rw [map_zero, map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add, map_add]; exact add_mem hx hy
  · intro c x hx
    rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hx

end Runitor

end RelTensor

end Bimod

end Superfusion

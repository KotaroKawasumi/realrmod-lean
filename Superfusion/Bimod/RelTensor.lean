/-
Superfusion / Bimod / RelTensor

Milestone M8a-2: **the balanced (relative) tensor product `M ⊗[A] N`**
over a noncommutative ring `A` — for `M` a right `A`-module and `N` a
left `A`-module, the quotient of the `K`-linear tensor product
`M ⊗[K] N` by the balancing relations `(m · a) ⊗ n - m ⊗ (a · n)`.

This is the paper's `⊗_{D_{ab}}` of §4.1: the iterated fusions
`B_L = C_{a,b} ⊗_{D_{ab}} C_{ab,c}` and `B_R = C_{b,c} ⊗_{D_{bc}} C_{a,bc}`
are balanced tensor products of column bimodules over the middle super
division algebra.  No grading enters at this stage, and no `K`-algebra
structure on `A` is needed (only the two actions): the construction is
stated in its natural generality.  The descent of the `ZMod 2`-grading
and the outer bimodule structure (with the Koszul sign of the paper's
`B_L` action) are the next milestone.

mathlib has no element-level relative tensor product over a
noncommutative ring (`Mathlib/CategoryTheory/Monoidal/Bimod.lean` is
coequalizer-based, with no element API) — a known gap, recorded in
docs/upstream-plan.md.  Accordingly everything here is built to be
upstreamable: the quotient reuses `Submodule.liftQ`/`mkQ`, and the API
(`mk`, `lift`, `induction_on`, `hom_ext`) mirrors `TensorProduct`'s.
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable (K : Type*) [CommRing K]
variable (A : Type*) [Ring A]
variable (M : Type*) [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (N : Type*) [AddCommGroup N] [Module K N] [Module A N]

/-- The balancing submodule of `M ⊗[K] N`: the span of the differences
`(m · a) ⊗ n - m ⊗ (a · n)`. -/
def balancer : Submodule K (M ⊗[K] N) :=
  Submodule.span K
    {x | ∃ (a : A) (m : M) (n : N),
      x = (MulOpposite.op a • m) ⊗ₜ[K] n - m ⊗ₜ[K] (a • n)}

/-- **The balanced tensor product** `M ⊗[A] N` of a right `A`-module and
a left `A`-module (the paper's `⊗_{D_{ab}}`, §4.1): the quotient of
`M ⊗[K] N` by the balancing relations. -/
def RelTensor : Type _ :=
  (M ⊗[K] N) ⧸ balancer K A M N

@[inherit_doc] scoped notation:100 M " ⊗[" A ";" K "] " N:100 =>
  RelTensor K A M N

namespace RelTensor

instance : AddCommGroup (M ⊗[A;K] N) :=
  inferInstanceAs (AddCommGroup ((M ⊗[K] N) ⧸ balancer K A M N))

instance : Module K (M ⊗[A;K] N) :=
  inferInstanceAs (Module K ((M ⊗[K] N) ⧸ balancer K A M N))

/-- The canonical projection from the `K`-tensor product. -/
def fromTensor : M ⊗[K] N →ₗ[K] M ⊗[A;K] N :=
  (balancer K A M N).mkQ

theorem fromTensor_surjective :
    Function.Surjective (fromTensor K A M N) :=
  Submodule.Quotient.mk_surjective _

/-- The canonical `K`-bilinear map `M → N → M ⊗[A] N`. -/
def mk : M →ₗ[K] N →ₗ[K] M ⊗[A;K] N :=
  (TensorProduct.mk K M N).compr₂ (fromTensor K A M N)

theorem mk_apply (m : M) (n : N) :
    mk K A M N m n = fromTensor K A M N (m ⊗ₜ[K] n) := rfl

/-- **The balancing relation**: `(m · a) ⊗ n = m ⊗ (a · n)` in
`M ⊗[A] N`. -/
theorem mk_op_smul (a : A) (m : M) (n : N) :
    mk K A M N (MulOpposite.op a • m) n = mk K A M N m (a • n) :=
  (Submodule.Quotient.eq _).mpr (Submodule.subset_span ⟨a, m, n, rfl⟩)

/-- Every element of `M ⊗[A] N` is a finite sum of `mk m n`. -/
@[elab_as_elim]
theorem induction_on {motive : M ⊗[A;K] N → Prop} (z : M ⊗[A;K] N)
    (zero : motive 0)
    (mk : ∀ (m : M) (n : N), motive (mk K A M N m n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  obtain ⟨x, rfl⟩ := fromTensor_surjective K A M N z
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero
  | tmul m n => exact mk m n
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

section Lift

variable {P : Type*} [AddCommGroup P] [Module K P]

variable {K M N}

/-- A `K`-bilinear map is **balanced over `A`** if it coequalizes the two
middle actions: `f (m · a) n = f m (a · n)`. -/
def IsBalanced (f : M →ₗ[K] N →ₗ[K] P) : Prop :=
  ∀ (a : A) (m : M) (n : N), f (MulOpposite.op a • m) n = f m (a • n)

variable {A}

/-- **The universal property**: a balanced `K`-bilinear map factors
through `M ⊗[A] N`. -/
def lift (f : M →ₗ[K] N →ₗ[K] P) (hf : IsBalanced A f) :
    M ⊗[A;K] N →ₗ[K] P :=
  Submodule.liftQ _ (TensorProduct.lift f) (by
    rw [balancer, Submodule.span_le]
    rintro x ⟨a, m, n, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub,
      TensorProduct.lift.tmul]
    rw [hf a m n, sub_self])

theorem lift_comp_fromTensor (f : M →ₗ[K] N →ₗ[K] P) (hf : IsBalanced A f) :
    (lift f hf).comp (fromTensor K A M N) = TensorProduct.lift f :=
  Submodule.liftQ_mkQ _ _ _

@[simp] theorem lift_mk (f : M →ₗ[K] N →ₗ[K] P) (hf : IsBalanced A f)
    (m : M) (n : N) :
    lift f hf (mk K A M N m n) = f m n := by
  rw [mk_apply, ← LinearMap.comp_apply, lift_comp_fromTensor,
    TensorProduct.lift.tmul]

/-- Two `K`-linear maps out of `M ⊗[A] N` agreeing on the generators
`mk m n` are equal. -/
@[ext] theorem hom_ext {g h : M ⊗[A;K] N →ₗ[K] P}
    (H : ∀ (m : M) (n : N), g (mk K A M N m n) = h (mk K A M N m n)) :
    g = h := by
  refine LinearMap.ext fun z => ?_
  induction z using induction_on with
  | zero => rw [map_zero, map_zero]
  | mk m n => exact H m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem lift_unique (f : M →ₗ[K] N →ₗ[K] P) (hf : IsBalanced A f)
    {g : M ⊗[A;K] N →ₗ[K] P}
    (H : ∀ (m : M) (n : N), g (mk K A M N m n) = f m n) :
    g = lift f hf :=
  hom_ext fun m n => by rw [H m n, lift_mk]

end Lift

end RelTensor

end Bimod

end Superfusion

/-
Superfusion / Bimod / RelTensorAssoc

Milestone M8a-5: **the associator of balanced tensor products** —

  `assoc : (M ⊗[A] N) ⊗[B] P ≃ₗ (M ⊗[A] (N ⊗[B] P))`,
  `(m ⊗ n) ⊗ p ↦ m ⊗ (n ⊗ p)`,

for `M` right-`A`, `N` an `(A,B)`-bimodule, `P` left-`B`.  The iterated
balanced products are formed through the outer actions of M8a-4a,
activated as low-priority local instances (`Module K` on the quotient
must keep winning for scalar goals).  Both directions are two-stage
`lift`s of the bundled trilinear maps `(m, n, p) ↦ m ⊗ (n ⊗ p)` resp.
`(n, p, m) ↦ (m ⊗ n) ⊗ p` (assembled with `llcomp`/`lflip`/`compl₂`,
so that every application is definitionally an `mk`-expression), with
the balancing conditions reducing to the inner/outer balancing
relations and the outer-action formulas.

This is the associativity of the paper's iterated fusion (§4.1):
`B_L = (C_{a,b} ⊗ C_{ab,c})`-style products may be re-associated at
will.  Gradedness and outer-action equivariance of the associator are
deferred to the milestone that needs them (the `B_L`/pentagon track).
-/
import Superfusion.Bimod.RelTensorMap

namespace Superfusion

namespace Bimod

namespace RelTensor

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [Module Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [IsScalarTower K A N] [IsScalarTower K Bᵐᵒᵖ N]
variable {P : Type*} [AddCommGroup P] [Module K P] [Module B P]

attribute [local instance 500] leftModule rightModule

section Assoc

variable (K A B M N P)

/-! #### The forward direction -/

/-- The bundled trilinear map `(m, n, p) ↦ m ⊗ (n ⊗ p)`. -/
private noncomputable def fwdTri :
    M →ₗ[K] N →ₗ[K] P →ₗ[K] M ⊗[A;K] (N ⊗[B;K] P) :=
  ((LinearMap.llcomp K P (N ⊗[B;K] P) (M ⊗[A;K] (N ⊗[B;K] P))).comp
    (mk K A M (N ⊗[B;K] P))).compl₂ (mk K B N P)

omit [Algebra K B] [IsScalarTower K Bᵐᵒᵖ N] in
private theorem fwdTri_apply (m : M) (n : N) (p : P) :
    fwdTri K A B M N P m n p
      = mk K A M (N ⊗[B;K] P) m (mk K B N P n p) := rfl

omit [Algebra K B] [IsScalarTower K Bᵐᵒᵖ N] in
private theorem fwdTri_balanced : IsBalanced A (fwdTri K A B M N P) := by
  intro a m n
  refine LinearMap.ext fun p => ?_
  show mk K A M (N ⊗[B;K] P) (MulOpposite.op a • m) (mk K B N P n p)
      = mk K A M (N ⊗[B;K] P) m (mk K B N P (a • n) p)
  rw [mk_op_smul]
  refine congrArg _ ?_
  show leftActionEnd K B N P a (mk K B N P n p) = mk K B N P (a • n) p
  rw [leftActionEnd_mk]

private noncomputable def fwdInner :
    (M ⊗[A;K] N) →ₗ[K] P →ₗ[K] M ⊗[A;K] (N ⊗[B;K] P) :=
  lift (fwdTri K A B M N P) (fwdTri_balanced K A B M N P)

omit [Algebra K B] [IsScalarTower K Bᵐᵒᵖ N] in
private theorem fwdInner_mk (m : M) (n : N) (p : P) :
    fwdInner K A B M N P (mk K A M N m n) p
      = mk K A M (N ⊗[B;K] P) m (mk K B N P n p) := by
  show (lift (fwdTri K A B M N P) (fwdTri_balanced K A B M N P)
    (mk K A M N m n)) p = _
  rw [lift_mk]
  rfl

private theorem fwdInner_balanced :
    IsBalanced B (fwdInner K A B M N P) := by
  intro b z p
  induction z using induction_on with
  | zero =>
      rw [smul_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  | mk m n =>
      have hsm : MulOpposite.op b • mk K A M N m n
          = mk K A M N m (MulOpposite.op b • n) := by
        show rightActionEnd K A M N (MulOpposite.op b) (mk K A M N m n) = _
        rw [rightActionEnd_mk]
      rw [hsm, fwdInner_mk, fwdInner_mk]
      refine congrArg _ ?_
      exact mk_op_smul K B N P b n p
  | add x y hx hy =>
      rw [smul_add, map_add, LinearMap.add_apply, hx, hy,
        ← LinearMap.add_apply, ← map_add]

private noncomputable def fwd :
    ((M ⊗[A;K] N) ⊗[B;K] P) →ₗ[K] M ⊗[A;K] (N ⊗[B;K] P) :=
  lift (fwdInner K A B M N P) (fwdInner_balanced K A B M N P)

private theorem fwd_mk (z : M ⊗[A;K] N) (p : P) :
    fwd K A B M N P (mk K B (M ⊗[A;K] N) P z p)
      = fwdInner K A B M N P z p := by
  show lift (fwdInner K A B M N P) (fwdInner_balanced K A B M N P)
      (mk K B (M ⊗[A;K] N) P z p) = _
  rw [lift_mk]

/-! #### The backward direction -/

/-- The bundled trilinear map `(n, p, m) ↦ (m ⊗ n) ⊗ p`. -/
private noncomputable def bwdTri :
    N →ₗ[K] P →ₗ[K] M →ₗ[K] ((M ⊗[A;K] N) ⊗[B;K] P) :=
  LinearMap.lflip.comp
    ((LinearMap.llcomp K M (M ⊗[A;K] N)
        (P →ₗ[K] (M ⊗[A;K] N) ⊗[B;K] P)
        (mk K B (M ⊗[A;K] N) P)).comp
      (mk K A M N).flip)

omit [Algebra K A] [IsScalarTower K A N] in
private theorem bwdTri_apply (n : N) (p : P) (m : M) :
    bwdTri K A B M N P n p m
      = mk K B (M ⊗[A;K] N) P (mk K A M N m n) p := rfl

omit [Algebra K A] [IsScalarTower K A N] in
private theorem bwdTri_balanced : IsBalanced B (bwdTri K A B M N P) := by
  intro b n p
  refine LinearMap.ext fun m => ?_
  show mk K B (M ⊗[A;K] N) P (mk K A M N m (MulOpposite.op b • n)) p
      = mk K B (M ⊗[A;K] N) P (mk K A M N m n) (b • p)
  have hsm : mk K A M N m (MulOpposite.op b • n)
      = MulOpposite.op b • mk K A M N m n := by
    show _ = rightActionEnd K A M N (MulOpposite.op b) (mk K A M N m n)
    rw [rightActionEnd_mk]
  rw [hsm, mk_op_smul]

private noncomputable def bwdInnerFlip :
    (N ⊗[B;K] P) →ₗ[K] M →ₗ[K] ((M ⊗[A;K] N) ⊗[B;K] P) :=
  lift (bwdTri K A B M N P) (bwdTri_balanced K A B M N P)

omit [Algebra K A] [IsScalarTower K A N] in
private theorem bwdInnerFlip_mk (n : N) (p : P) (m : M) :
    bwdInnerFlip K A B M N P (mk K B N P n p) m
      = mk K B (M ⊗[A;K] N) P (mk K A M N m n) p := by
  show (lift (bwdTri K A B M N P) (bwdTri_balanced K A B M N P)
    (mk K B N P n p)) m = _
  rw [lift_mk]
  rfl

private theorem bwdBil_balanced :
    IsBalanced A ((bwdInnerFlip K A B M N P).flip) := by
  intro a m w
  induction w using induction_on with
  | zero =>
      show bwdInnerFlip K A B M N P 0 (MulOpposite.op a • m)
          = bwdInnerFlip K A B M N P (a • 0) m
      rw [smul_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  | mk n p =>
      show bwdInnerFlip K A B M N P (mk K B N P n p) (MulOpposite.op a • m)
          = bwdInnerFlip K A B M N P (a • mk K B N P n p) m
      have hsm : a • mk K B N P n p = mk K B N P (a • n) p := by
        show leftActionEnd K B N P a (mk K B N P n p) = _
        rw [leftActionEnd_mk]
      rw [hsm, bwdInnerFlip_mk, bwdInnerFlip_mk, mk_op_smul]
  | add x y hx hy =>
      show bwdInnerFlip K A B M N P (x + y) (MulOpposite.op a • m)
          = bwdInnerFlip K A B M N P (a • (x + y)) m
      rw [smul_add, map_add, map_add, LinearMap.add_apply,
        LinearMap.add_apply]
      exact congrArg₂ (· + ·) hx hy

private noncomputable def bwd :
    (M ⊗[A;K] (N ⊗[B;K] P)) →ₗ[K] (M ⊗[A;K] N) ⊗[B;K] P :=
  lift ((bwdInnerFlip K A B M N P).flip) (bwdBil_balanced K A B M N P)

private theorem bwd_mk (m : M) (w : N ⊗[B;K] P) :
    bwd K A B M N P (mk K A M (N ⊗[B;K] P) m w)
      = bwdInnerFlip K A B M N P w m := by
  show lift ((bwdInnerFlip K A B M N P).flip) (bwdBil_balanced K A B M N P)
      (mk K A M (N ⊗[B;K] P) m w) = _
  rw [lift_mk]
  rfl

/-! #### The associator -/

private theorem fwd_bwd :
    (fwd K A B M N P).comp (bwd K A B M N P) = LinearMap.id := by
  refine hom_ext fun m w => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, bwd_mk]
  induction w using induction_on with
  | zero =>
      rw [map_zero, LinearMap.zero_apply, map_zero, map_zero]
  | mk n p =>
      rw [bwdInnerFlip_mk, fwd_mk, fwdInner_mk]
  | add x y hx hy =>
      rw [map_add, LinearMap.add_apply, map_add, map_add, hx, hy]

private theorem bwd_fwd :
    (bwd K A B M N P).comp (fwd K A B M N P) = LinearMap.id := by
  refine hom_ext fun z p => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, fwd_mk]
  induction z using induction_on with
  | zero =>
      rw [map_zero, LinearMap.zero_apply, map_zero,
        show mk K B (M ⊗[A;K] N) P 0 p
            = (0 : (M ⊗[A;K] N) ⊗[B;K] P) from by
          rw [map_zero, LinearMap.zero_apply]]
  | mk m n =>
      rw [fwdInner_mk, bwd_mk, bwdInnerFlip_mk]
  | add x y hx hy =>
      rw [LinearMap.map_add₂, map_add, hx, hy, ← LinearMap.map_add₂]

/-- **The associator** of balanced tensor products:
`(m ⊗ n) ⊗ p ↦ m ⊗ (n ⊗ p)`. -/
noncomputable def assoc :
    ((M ⊗[A;K] N) ⊗[B;K] P) ≃ₗ[K] M ⊗[A;K] (N ⊗[B;K] P) :=
  LinearEquiv.ofLinear (fwd K A B M N P) (bwd K A B M N P)
    (fwd_bwd K A B M N P) (bwd_fwd K A B M N P)

theorem assoc_mk (m : M) (n : N) (p : P) :
    assoc K A B M N P
        (mk K B (M ⊗[A;K] N) P (mk K A M N m n) p)
      = mk K A M (N ⊗[B;K] P) m (mk K B N P n p) := by
  show fwd K A B M N P (mk K B (M ⊗[A;K] N) P (mk K A M N m n) p) = _
  rw [fwd_mk, fwdInner_mk]

theorem assoc_symm_mk (m : M) (n : N) (p : P) :
    (assoc K A B M N P).symm
        (mk K A M (N ⊗[B;K] P) m (mk K B N P n p))
      = mk K B (M ⊗[A;K] N) P (mk K A M N m n) p := by
  show bwd K A B M N P (mk K A M (N ⊗[B;K] P) m (mk K B N P n p)) = _
  rw [bwd_mk, bwdInnerFlip_mk]

end Assoc

end RelTensor

end Bimod

end Superfusion

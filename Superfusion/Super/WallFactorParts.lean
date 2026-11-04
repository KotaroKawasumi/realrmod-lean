/-
Superfusion / Super / WallFactorParts

Milestone M7f-2b (part i): **the four innermost identities of the
Wall-map factorization** — equalities in `End K (A ᵍ⊗ B)`:

  `lmul (a ᵍ⊗ 1)        = endInclLeft  (lmul a)`            (La)
  `lmul (1 ᵍ⊗ b)        = endInclRight (lmul b)`            (Lb)
  `sRM (op (a ᵍ⊗ 1))    = endInclLeft  (sRM (op a))`        (Ra)
  `sRM (op (1 ᵍ⊗ b))    = endInclRight (sRM (op b))`        (Rb)

for homogeneous `a`/`b` (`sRM` = signed right multiplication).  These
say: the generators of the Wall map of `A ᵍ⊗ B` act exactly as the
inclusions of the small Wall images — all Koszul signs and
super-opposite signs match, by `∀`-closed `sgn` identities.

Checked pointwise via `end_ext_of_graded` (an endomorphism of a
graded algebra is determined by its values on graded elements, by the
mask decomposition) and `tensorGrading_induction`.

Part ii (next milestone) assembles these into the factorization
`Wall_{A ᵍ⊗ B} = endTensorHom ∘ (Wall_A ᵍ⊗ Wall_B) ∘ reshuffle` and
the super-Azumaya `ᵍ⊗`-closure.
-/
import Superfusion.Super.WallGraded
import Superfusion.Super.TensorGradingSop
import Superfusion.Super.TensorGradingComm

namespace Superfusion

open TensorProduct
open GradedTensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-! ### Sign and scalar helpers -/

private theorem sgn_wall_left : ∀ j k l : ZMod 2,
    ((sgn (j * (k + l)) : ℤˣ) * sgn (l * j)) = sgn (j * k) := by
  decide

private theorem sgn_wall_right : ∀ k l : ZMod 2,
    (sgn (k + l) : ℤˣ) = sgn k * sgn l := by
  decide

private theorem zsmul_gtmul (n : ℤ) (x : A) (y : B) :
    ((n • x) ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] ℬ) = n • (x ᵍ⊗ₜ[K] y) := by
  rw [show (((n • x) ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] ℬ))
      = of K 𝒜 ℬ ((n • x) ⊗ₜ[K] y) from rfl,
    show ((n • x) ⊗ₜ[K] y : A ⊗[K] B) = n • (x ⊗ₜ[K] y) from
      (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

private theorem gtmul_zsmul (n : ℤ) (x : A) (y : B) :
    (x ᵍ⊗ₜ[K] (n • y) : 𝒜 ᵍ⊗[K] ℬ) = n • (x ᵍ⊗ₜ[K] y) := by
  rw [show ((x ᵍ⊗ₜ[K] (n • y) : 𝒜 ᵍ⊗[K] ℬ))
      = of K 𝒜 ℬ (x ⊗ₜ[K] (n • y)) from rfl,
    show (x ⊗ₜ[K] (n • y) : A ⊗[K] B) = n • (x ⊗ₜ[K] y) from by
      rw [← TensorProduct.smul_tmul]
      exact (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

private theorem uzpow_to_sgn_zsmul (e : ZMod 2)
    (z : 𝒜 ᵍ⊗[K] ℬ) :
    (-1 : ℤˣ) ^ e • z = ((sgn e : ℤˣ) : ℤ) • z := by
  rw [← sgn_eq_neg_one_uzpow, Units.smul_def]

/-! ### Extension principle for endomorphisms of a graded algebra -/

/-- Two endomorphisms of `A ᵍ⊗ B` agreeing on all graded elements are
equal (mask decomposition). -/
theorem end_ext_of_graded {F G : Module.End K (𝒜 ᵍ⊗[K] ℬ)}
    (h : ∀ (m : ZMod 2), ∀ w ∈ tensorGrading 𝒜 ℬ m, F w = G w) :
    F = G := by
  refine LinearMap.ext fun w => ?_
  conv_lhs => rw [← tensorMask_zero_add_tensorMask_one 𝒜 ℬ w]
  conv_rhs => rw [← tensorMask_zero_add_tensorMask_one 𝒜 ℬ w]
  rw [map_add, map_add, h 0 _ (tensorMask_mem 𝒜 ℬ 0 w),
    h 1 _ (tensorMask_mem 𝒜 ℬ 1 w)]

/-! ### (La): left multiplication by `a ᵍ⊗ 1` -/

theorem lmul_tmul_one (a : A) :
    Algebra.lmul K (𝒜 ᵍ⊗[K] ℬ) (a ᵍ⊗ₜ[K] (1 : B))
      = endInclLeft 𝒜 ℬ (Algebra.lmul K A a) := by
  refine end_ext_of_graded 𝒜 ℬ fun m w hw => ?_
  refine tensorGrading_induction 𝒜 ℬ hw
    (p := fun v => Algebra.lmul K (𝒜 ᵍ⊗[K] ℬ) (a ᵍ⊗ₜ[K] (1 : B)) v
      = endInclLeft 𝒜 ℬ (Algebra.lmul K A a) v)
    ?_ ?_ ?_ ?_
  · intro k l x y hkl hx hy
    rw [show Algebra.lmul K (𝒜 ᵍ⊗[K] ℬ) (a ᵍ⊗ₜ[K] (1 : B))
        (x ᵍ⊗ₜ[K] y) = (a ᵍ⊗ₜ[K] (1 : B)) * (x ᵍ⊗ₜ[K] y) from rfl,
      show ((a ᵍ⊗ₜ[K] (1 : B)) * (x ᵍ⊗ₜ[K] y) : 𝒜 ᵍ⊗[K] ℬ)
        = (a ᵍ⊗ₜ[K] ((⟨1, SetLike.one_mem_graded ℬ⟩ : ℬ 0) : B))
          * ((((⟨x, hx⟩ : 𝒜 k) : A)) ᵍ⊗ₜ[K] y) from rfl,
      tmul_coe_mul_coe_tmul, zero_mul, uzpow_zero, one_smul,
      endInclLeft_tmul, one_mul]
    rfl
  · rw [map_zero, map_zero]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
  · intro c u hu
    rw [map_smul, map_smul, hu]

/-! ### (Lb): left multiplication by `1 ᵍ⊗ b`, `b` homogeneous -/

theorem lmul_one_tmul {j : ZMod 2} {b : B} (hb : b ∈ ℬ j) :
    Algebra.lmul K (𝒜 ᵍ⊗[K] ℬ) ((1 : A) ᵍ⊗ₜ[K] b)
      = endInclRight 𝒜 ℬ (Algebra.lmul K B b) := by
  refine end_ext_of_graded 𝒜 ℬ fun m w hw => ?_
  refine tensorGrading_induction 𝒜 ℬ hw
    (p := fun v => Algebra.lmul K (𝒜 ᵍ⊗[K] ℬ) ((1 : A) ᵍ⊗ₜ[K] b) v
      = endInclRight 𝒜 ℬ (Algebra.lmul K B b) v)
    ?_ ?_ ?_ ?_
  · intro k l x y hkl hx hy
    have hlmul : Algebra.lmul K B b ∈ endGrading ℬ j :=
      lmul_mem_endGrading ℬ hb
    rw [show Algebra.lmul K (𝒜 ᵍ⊗[K] ℬ) ((1 : A) ᵍ⊗ₜ[K] b)
        (x ᵍ⊗ₜ[K] y) = ((1 : A) ᵍ⊗ₜ[K] b) * (x ᵍ⊗ₜ[K] y) from rfl,
      show (((1 : A) ᵍ⊗ₜ[K] b) * (x ᵍ⊗ₜ[K] y) : 𝒜 ᵍ⊗[K] ℬ)
        = ((1 : A) ᵍ⊗ₜ[K] ((⟨b, hb⟩ : ℬ j) : B))
          * ((((⟨x, hx⟩ : 𝒜 k) : A)) ᵍ⊗ₜ[K] y) from rfl,
      tmul_coe_mul_coe_tmul, one_mul, endInclRight_apply]
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [signedLTensor_of_mem_zero 𝒜 ℬ hlmul,
        show endConj 𝒜 ℬ (TensorProduct.map LinearMap.id
            (Algebra.lmul K B b)) (x ᵍ⊗ₜ[K] y)
          = x ᵍ⊗ₜ[K] (b * y) from rfl,
        zero_mul, uzpow_zero, one_smul]
    · rw [signedLTensor_of_mem_one 𝒜 ℬ hlmul,
        show endConj 𝒜 ℬ (TensorProduct.map (parityMap 𝒜)
            (Algebra.lmul K B b)) (x ᵍ⊗ₜ[K] y)
          = (parityMap 𝒜 x) ᵍ⊗ₜ[K] (b * y) from rfl,
        one_mul, uzpow_to_sgn_zsmul]
      rcases zmod2_cases k with hk | hk <;> subst hk
      · rw [parityMap_of_mem_zero 𝒜 hx, sgn_zero]
        rw [show (((1 : ℤˣ) : ℤ)) = 1 from rfl, one_smul]
      · rw [parityMap_of_mem_one 𝒜 hx, sgn_one,
          units_sign_eq]
        rw [show (((-1 : ℤˣ) : ℤ)) = -1 from rfl, neg_smul, one_smul,
          show ((-x) ᵍ⊗ₜ[K] (b * y) : 𝒜 ᵍ⊗[K] ℬ)
            = -(x ᵍ⊗ₜ[K] (b * y)) from by
            rw [show (-x) = (-1 : ℤ) • x from by rw [neg_smul, one_smul],
              zsmul_gtmul, neg_smul, one_smul]]
  · rw [map_zero, map_zero]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
  · intro c u hu
    rw [map_smul, map_smul, hu]

/-! ### (Ra): signed right multiplication by `op (a ᵍ⊗ 1)`,
`a` homogeneous -/

theorem sRM_op_tmul_one {j : ZMod 2} {a : A} (ha : a ∈ 𝒜 j) :
    signedRightMul (tensorGrading 𝒜 ℬ)
        (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] (1 : B)))
      = endInclLeft 𝒜 ℬ (signedRightMul 𝒜 (SuperOp.op 𝒜 a)) := by
  have hmem : (a ᵍ⊗ₜ[K] (1 : B)) ∈ tensorGrading 𝒜 ℬ j := by
    have h := tmul_mem_tensorGrading 𝒜 ℬ ha (SetLike.one_mem_graded ℬ)
    rwa [add_zero] at h
  refine end_ext_of_graded 𝒜 ℬ fun m w hw => ?_
  refine tensorGrading_induction 𝒜 ℬ hw
    (p := fun v => signedRightMul (tensorGrading 𝒜 ℬ)
        (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] (1 : B))) v
      = endInclLeft 𝒜 ℬ (signedRightMul 𝒜 (SuperOp.op 𝒜 a)) v)
    ?_ ?_ ?_ ?_
  · intro k l x y hkl hx hy
    have hxy : (x ᵍ⊗ₜ[K] y) ∈ tensorGrading 𝒜 ℬ (k + l) :=
      tmul_mem_tensorGrading 𝒜 ℬ hx hy
    rw [signedRightMul_apply, SuperOp.unop_op,
      SuperOp.mulMap_of_mem (tensorGrading 𝒜 ℬ) hmem hxy,
      show ((x ᵍ⊗ₜ[K] y) * (a ᵍ⊗ₜ[K] (1 : B)) : 𝒜 ᵍ⊗[K] ℬ)
        = (x ᵍ⊗ₜ[K] ((⟨y, hy⟩ : ℬ l) : B))
          * ((((⟨a, ha⟩ : 𝒜 j) : A)) ᵍ⊗ₜ[K] (1 : B)) from rfl,
      tmul_coe_mul_coe_tmul, mul_one, uzpow_to_sgn_zsmul,
      endInclLeft_tmul, signedRightMul_apply, SuperOp.unop_op,
      SuperOp.mulMap_of_mem 𝒜 ha hx, zsmul_gtmul, smul_smul,
      ← Units.val_mul, sgn_wall_left j k l]
  · rw [map_zero, map_zero]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
  · intro c u hu
    rw [map_smul, map_smul, hu]

/-! ### (Rb): signed right multiplication by `op (1 ᵍ⊗ b)`,
`b` homogeneous -/

theorem sRM_op_one_tmul {j : ZMod 2} {b : B} (hb : b ∈ ℬ j) :
    signedRightMul (tensorGrading 𝒜 ℬ)
        (SuperOp.op (tensorGrading 𝒜 ℬ) ((1 : A) ᵍ⊗ₜ[K] b))
      = endInclRight 𝒜 ℬ (signedRightMul ℬ (SuperOp.op ℬ b)) := by
  have hmem : ((1 : A) ᵍ⊗ₜ[K] b) ∈ tensorGrading 𝒜 ℬ j := by
    have h := tmul_mem_tensorGrading 𝒜 ℬ (SetLike.one_mem_graded 𝒜) hb
    rwa [zero_add] at h
  have hsrm : signedRightMul ℬ (SuperOp.op ℬ b) ∈ endGrading ℬ j :=
    signedRightMul_mem_endGrading ℬ
      (by rwa [SuperOp.unop_op] : SuperOp.unop ℬ (SuperOp.op ℬ b) ∈ ℬ j)
  refine end_ext_of_graded 𝒜 ℬ fun m w hw => ?_
  refine tensorGrading_induction 𝒜 ℬ hw
    (p := fun v => signedRightMul (tensorGrading 𝒜 ℬ)
        (SuperOp.op (tensorGrading 𝒜 ℬ) ((1 : A) ᵍ⊗ₜ[K] b)) v
      = endInclRight 𝒜 ℬ (signedRightMul ℬ (SuperOp.op ℬ b)) v)
    ?_ ?_ ?_ ?_
  · intro k l x y hkl hx hy
    have hxy : (x ᵍ⊗ₜ[K] y) ∈ tensorGrading 𝒜 ℬ (k + l) :=
      tmul_mem_tensorGrading 𝒜 ℬ hx hy
    rw [signedRightMul_apply, SuperOp.unop_op,
      SuperOp.mulMap_of_mem (tensorGrading 𝒜 ℬ) hmem hxy,
      show ((x ᵍ⊗ₜ[K] y) * ((1 : A) ᵍ⊗ₜ[K] b) : 𝒜 ᵍ⊗[K] ℬ)
        = (x ᵍ⊗ₜ[K] ((⟨y, hy⟩ : ℬ l) : B))
          * ((((⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) : A))
            ᵍ⊗ₜ[K] b) from rfl,
      tmul_coe_mul_coe_tmul, mul_zero, uzpow_zero, one_smul, mul_one,
      endInclRight_apply]
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [signedLTensor_of_mem_zero 𝒜 ℬ hsrm,
        show endConj 𝒜 ℬ (TensorProduct.map LinearMap.id
            (signedRightMul ℬ (SuperOp.op ℬ b))) (x ᵍ⊗ₜ[K] y)
          = x ᵍ⊗ₜ[K] (signedRightMul ℬ (SuperOp.op ℬ b) y) from rfl,
        signedRightMul_apply, SuperOp.unop_op,
        SuperOp.mulMap_of_mem ℬ hb hy,
        show ((0 : ZMod 2) * (k + l)) = 0 from by rw [zero_mul],
        show ((0 : ZMod 2) * l) = 0 from by rw [zero_mul],
        sgn_zero, gtmul_zsmul]
    · rw [signedLTensor_of_mem_one 𝒜 ℬ hsrm,
        show endConj 𝒜 ℬ (TensorProduct.map (parityMap 𝒜)
            (signedRightMul ℬ (SuperOp.op ℬ b))) (x ᵍ⊗ₜ[K] y)
          = (parityMap 𝒜 x) ᵍ⊗ₜ[K]
            (signedRightMul ℬ (SuperOp.op ℬ b) y) from rfl,
        signedRightMul_apply, SuperOp.unop_op,
        SuperOp.mulMap_of_mem ℬ hb hy, one_mul, one_mul, gtmul_zsmul,
        sgn_wall_right k l]
      rcases zmod2_cases k with hk | hk <;> subst hk
      · rw [parityMap_of_mem_zero 𝒜 hx, sgn_zero, one_mul]
      · rw [parityMap_of_mem_one 𝒜 hx, sgn_one, units_sign_eq,
          show (((-1 : ℤˣ) * sgn l : ℤˣ) : ℤ)
            = -((sgn l : ℤˣ) : ℤ) from by
            rw [Units.val_mul]
            simp,
          neg_smul,
          show ((-x) ᵍ⊗ₜ[K] (y * b) : 𝒜 ᵍ⊗[K] ℬ)
            = -(x ᵍ⊗ₜ[K] (y * b)) from by
            rw [show (-x) = (-1 : ℤ) • x from by
                rw [neg_smul, one_smul],
              zsmul_gtmul, neg_smul, one_smul],
          smul_neg]
  · rw [map_zero, map_zero]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
  · intro c u hu
    rw [map_smul, map_smul, hu]

end Superfusion

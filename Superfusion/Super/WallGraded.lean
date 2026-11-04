/-
Superfusion / Super / WallGraded

Milestone M7f-2a: **Wall's map is a map of graded algebras** —

  `superMulLeftRight : A ᵍ⊗ Aˢᵒᵖ →ₐ End K A`

is homogeneous for the M7f-1a grading on the source and the M7f-1e
grading on the target: left multiplication by a degree-`i` element
shifts every grade by `i` (`lmul_mem_endGrading`, M7f-1e), and the
signed right multiplication by a degree-`j` element shifts every grade
by `j` (`signedRightMul_mem_endGrading` — the Koszul sign is a
`ℤ`-scalar, so membership is unaffected).

Consequently, for a super-Azumaya algebra the Wall map is an
isomorphism of **graded** algebras
(`superMulLeftRight_map_grading`) — the precise form of
`A ᵍ⊗ Aˢᵒᵖ ≅ End(A)` used for the inverses of the Brauer–Wall group
(M7f-4), and one arm of the Wall-map factorization (M7f-2b):

  `Wall_{A ᵍ⊗ B} = endTensorHom ∘ (Wall_A ᵍ⊗ Wall_B) ∘ reshuffle`.
-/
import Superfusion.Super.Wall
import Superfusion.Super.GradedEndTensor

namespace Superfusion

open TensorProduct
open GradedTensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-! ### The two factors are homogeneous -/

/-- The signed right multiplication by a degree-`j` element shifts
every grade by `j`. -/
theorem signedRightMul_mem_endGrading {j : ZMod 2} {b : SuperOp 𝒜}
    (hb : SuperOp.unop 𝒜 b ∈ 𝒜 j) :
    signedRightMul 𝒜 b ∈ endGrading 𝒜 j := by
  intro k x hx
  rw [signedRightMul_apply, SuperOp.mulMap_of_mem 𝒜 hb hx]
  exact zsmul_mem (SetLike.mul_mem_graded hx hb) _

/-! ### Wall's map is homogeneous -/

theorem superMulLeftRight_isHomogeneous :
    IsHomogeneousHom (tensorGrading 𝒜 (SuperOp.grading 𝒜))
      (endGrading 𝒜) (superMulLeftRight 𝒜) := by
  intro i z hz
  refine tensorGrading_induction 𝒜 (SuperOp.grading 𝒜) hz
    (p := fun w => superMulLeftRight 𝒜 w ∈ endGrading 𝒜 i)
    ?_ ?_ ?_ ?_
  · intro j k a b hjk ha hb
    rw [show superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b)
        = Algebra.lmul K A a * signedRightMul 𝒜 b from
      GradedTensorProduct.lift_tmul 𝒜 (SuperOp.grading 𝒜)
        (Algebra.lmul K A) (signedRightMul 𝒜)
        (lmul_signedRightMul_anticommutes 𝒜) a b]
    exact hjk ▸ SetLike.mul_mem_graded (lmul_mem_endGrading 𝒜 ha)
      (signedRightMul_mem_endGrading 𝒜 hb)
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- **For a super-Azumaya algebra, Wall's map is an isomorphism of
graded algebras** (M7f-2a): it carries the tensor grading of
`A ᵍ⊗ Aˢᵒᵖ` onto the End grading. -/
theorem superMulLeftRight_map_grading [IsSuperAzumaya 𝒜]
    (i : ZMod 2) :
    (tensorGrading 𝒜 (SuperOp.grading 𝒜) i).map
        (superMulLeftRight 𝒜).toLinearMap
      = endGrading 𝒜 i :=
  map_grading_of_bijective (tensorGrading 𝒜 (SuperOp.grading 𝒜))
    (endGrading 𝒜) (superMulLeftRight 𝒜)
    (superMulLeftRight_isHomogeneous 𝒜) IsSuperAzumaya.bij i

/-! ### Composition with the inclusions (API for the factorization) -/

theorem superMulLeftRight_comp_includeLeft :
    (superMulLeftRight 𝒜).comp (includeLeft 𝒜 (SuperOp.grading 𝒜))
      = Algebra.lmul K A := by
  refine AlgHom.ext fun a => ?_
  show superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] (1 : SuperOp 𝒜))
    = Algebra.lmul K A a
  rw [show superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] (1 : SuperOp 𝒜))
      = Algebra.lmul K A a * signedRightMul 𝒜 (1 : SuperOp 𝒜) from
    GradedTensorProduct.lift_tmul 𝒜 (SuperOp.grading 𝒜)
      (Algebra.lmul K A) (signedRightMul 𝒜)
      (lmul_signedRightMul_anticommutes 𝒜) a 1,
    map_one, mul_one]

theorem superMulLeftRight_comp_includeRight :
    (superMulLeftRight 𝒜).comp (includeRight 𝒜 (SuperOp.grading 𝒜))
      = signedRightMul 𝒜 := by
  refine AlgHom.ext fun b => ?_
  show superMulLeftRight 𝒜 ((1 : A) ᵍ⊗ₜ[K] b) = signedRightMul 𝒜 b
  rw [show superMulLeftRight 𝒜 ((1 : A) ᵍ⊗ₜ[K] b)
      = Algebra.lmul K A (1 : A) * signedRightMul 𝒜 b from
    GradedTensorProduct.lift_tmul 𝒜 (SuperOp.grading 𝒜)
      (Algebra.lmul K A) (signedRightMul 𝒜)
      (lmul_signedRightMul_anticommutes 𝒜) 1 b,
    map_one, one_mul]

end Superfusion

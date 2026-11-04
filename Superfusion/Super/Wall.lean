/-
Superfusion / Super / Wall

Milestone M2: the enveloping superalgebra `E = A ⊗̂ A^sop` and Wall's map
(paper eq. (2))
  `superMulLeftRight : E →ₐ[K] Module.End K A`,
  `a ⊗ b ↦ (x ↦ (-1)^{|b||x|} a x b)`,
mirroring mathlib's `AlgHom.mulLeftRight`/`IsAzumaya` (ungraded Azumaya
template).  **Wall's criterion** — central simplicity of `A` is equivalent
to bijectivity of this map — is stated here as the class `IsSuperAzumaya`;
the proof (from `IsSuperCentral` + `IsGradedSimple`, and conversely) is
milestone M4.

Key economies:
* the signed right multiplication `x ↦ (-1)^{|b||x|} x b` is literally the
  bilinear map `SuperOp.mulMap` of M1 in its other slot, and its
  multiplicativity over `A^sop` is the `unop` of associativity in `A^sop`;
* the graded tensor product and its universal property
  (`GradedTensorProduct.lift`) come from mathlib, with our `sgn` matched to
  mathlib's `(-1 : ℤˣ) ^ (· : ZMod 2)` by `sgn_eq_neg_one_uzpow`.
-/
import Superfusion.Super.SuperOpposite
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

namespace Superfusion

open scoped TensorProduct

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

namespace SuperOp

/-- `mulMap` in its right-multiplication reading: for `b ∈ 𝒜 j`, `x ∈ 𝒜 i`,
`mulMap b x = (-1)^{ji} (x * b)` — the signed right multiplication by `b`. -/
theorem mulMap_of_mem {j i : ZMod 2} {b x : A} (hb : b ∈ 𝒜 j) (hx : x ∈ 𝒜 i) :
    mulMap 𝒜 b x = ((sgn (j * i) : ℤˣ) : ℤ) • (x * b) := by
  have h := op_mul_op_of_mem 𝒜 hb hx
  rw [mul_def, unop_op, unop_op, ← map_zsmul (op 𝒜)] at h
  exact (op 𝒜).injective h

end SuperOp

open SuperOp

/-- The signed right multiplication `b ↦ (x ↦ (-1)^{|b||x|} x b)`, an algebra
map from the super-opposite into the endomorphisms — the Koszul sign is
exactly what makes it multiplicative. -/
noncomputable def signedRightMul : SuperOp 𝒜 →ₐ[K] Module.End K A where
  toFun b := mulMap 𝒜 (unop 𝒜 b)
  map_one' := LinearMap.ext fun x => by
    show mulMap 𝒜 (1 : A) x = x
    rw [mulMap_apply, oddPart_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜),
      mul_zero, smul_zero, sub_zero, mul_one]
  map_mul' b b' := LinearMap.ext fun x =>
    congrArg (unop 𝒜) (mul_assoc (op 𝒜 (unop 𝒜 b)) (op 𝒜 (unop 𝒜 b')) (op 𝒜 x))
  map_zero' := by
    show mulMap 𝒜 (unop 𝒜 0) = 0
    rw [map_zero, map_zero]
  map_add' b b' := by
    show mulMap 𝒜 (unop 𝒜 (b + b')) = _
    rw [map_add, map_add]
  commutes' r := LinearMap.ext fun x => by
    show mulMap 𝒜 (algebraMap K A r) x = algebraMap K (Module.End K A) r x
    rw [mulMap_apply, oddPart_of_mem_zero 𝒜 (algebraMap_mem_grade_zero 𝒜 r),
      mul_zero, smul_zero, sub_zero, ← Algebra.commutes r x, ← Algebra.smul_def,
      Module.algebraMap_end_apply]

theorem signedRightMul_apply (b : SuperOp 𝒜) (x : A) :
    signedRightMul 𝒜 b x = mulMap 𝒜 (unop 𝒜 b) x := rfl

/-- Left multiplications and signed right multiplications supercommute —
the anticommutation hypothesis of `GradedTensorProduct.lift`. -/
theorem lmul_signedRightMul_anticommutes ⦃i j : ZMod 2⦄
    (a : 𝒜 i) (b : SuperOp.grading 𝒜 j) :
    Algebra.lmul K A a * signedRightMul 𝒜 b =
      (-1 : ℤˣ) ^ (j * i) • (signedRightMul 𝒜 b * Algebra.lmul K A a) := by
  have hb : unop 𝒜 (b : SuperOp 𝒜) ∈ 𝒜 j := b.2
  have sign_id : ∀ j i k : ZMod 2, j * i + j * (i + k) = j * k := by decide
  refine LinearMap.ext fun x => ?_
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
      simp only [map_zero]
  | homogeneous m =>
      rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply,
        signedRightMul_apply, signedRightMul_apply,
        mulMap_of_mem 𝒜 hb m.2,
        show Algebra.lmul K A (a : A) (m : A) = (a : A) * (m : A) from rfl,
        mulMap_of_mem 𝒜 hb (SetLike.mul_mem_graded a.2 m.2),
        show ∀ y : A, Algebra.lmul K A (a : A) y = (a : A) * y from fun _ => rfl,
        Units.smul_def, ← sgn_eq_neg_one_uzpow,
        mul_smul_comm, smul_smul, ← Units.val_mul, ← sgn_add, mul_assoc,
        sign_id j i]
  | add m m' hm hm' =>
      simp only [Module.End.mul_apply, LinearMap.smul_apply, map_add] at hm hm' ⊢
      rw [hm, hm']

/-- The enveloping superalgebra `E = A ⊗̂ A^sop` (Koszul-signed tensor
product, from mathlib). -/
noncomputable abbrev SuperEnvelope :=
  𝒜 ᵍ⊗[K] (SuperOp.grading 𝒜)

/-- **Wall's map** (paper eq. (2)): `E → End_K(A)`,
`a ⊗ b ↦ (x ↦ (-1)^{|b||x|} a x b)`. -/
noncomputable def superMulLeftRight : SuperEnvelope 𝒜 →ₐ[K] Module.End K A :=
  GradedTensorProduct.lift 𝒜 (SuperOp.grading 𝒜)
    (Algebra.lmul K A) (signedRightMul 𝒜)
    (lmul_signedRightMul_anticommutes 𝒜)

theorem superMulLeftRight_tmul_apply (a : A) (b : SuperOp 𝒜) (x : A) :
    superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b) x = a * mulMap 𝒜 (unop 𝒜 b) x := by
  rw [superMulLeftRight, GradedTensorProduct.lift_tmul]
  rfl

/-- On homogeneous input the Wall map is `x ↦ (-1)^{|b||x|} a x b`. -/
theorem superMulLeftRight_tmul_apply_of_mem {j i : ZMod 2} (a : A)
    {b : SuperOp 𝒜} (hb : unop 𝒜 b ∈ 𝒜 j) {x : A} (hx : x ∈ 𝒜 i) :
    superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b) x =
      ((sgn (j * i) : ℤˣ) : ℤ) • (a * (x * unop 𝒜 b)) := by
  rw [superMulLeftRight_tmul_apply, mulMap_of_mem 𝒜 hb hx, mul_smul_comm]

/-- **Wall's criterion** (paper eq. (2)), stated in the style of mathlib's
`IsAzumaya`: the superalgebra is *super-Azumaya* when Wall's map is
bijective.  The theorem that for a finite-dimensional superalgebra over a
field this is equivalent to `IsSuperCentral ∧ IsGradedSimple` is milestone
M4 of the superalgebra track. -/
class IsSuperAzumaya : Prop where
  bij : Function.Bijective (superMulLeftRight 𝒜)

end Superfusion

/-
Superfusion / Super / SuperOpposite

The super-opposite `A^sop` of a superalgebra (§2.1): the same underlying
`K`-module with multiplication
  `a ∙ b = (-1)^{|a||b|} (b * a)`   (homogeneous elements).

Since the Koszul sign is `-1` only in bidegree `(1,1)`, the product has the
closed form (valid for all elements, degenerating correctly in
characteristic 2)
  `a ∙ b = b * a - 2 · (oddPart b * oddPart a)`,
which we take as the definition, bundled as a `K`-bilinear map so all
linearity is free.  The sign law on homogeneous elements is
`SuperOp.op_mul_op_of_mem`; associativity and unitality reduce to it by
decomposition induction.

The instance layering (type synonym + `deriving`, then `Mul`, `Monoid`,
`Ring`, `Algebra`) follows mathlib's `GradedTensorProduct`
(`Mathlib/LinearAlgebra/TensorProduct/Graded/Internal.lean`).

Design record: docs/super-track-design.md (milestone M1).  Mathlib has no
signed opposite; the unsigned `Aᵐᵒᵖ` is not the right second factor for
`E = A ⊗̂ A^sop` except in characteristic 2, and no gauge `A^sop ≅ Aᵐᵒᵖ`
exists over `ℝ` (that failure is the period-8 phenomenon itself).
-/
import Superfusion.Super.Basic

namespace Superfusion

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-! ### The odd projection -/

/-- The odd projection `A →ₗ[K] A` of a superalgebra. -/
noncomputable def oddPart : A →ₗ[K] A :=
  (𝒜 1).subtype ∘ₗ
    DirectSum.component K (ZMod 2) (fun i => ↥(𝒜 i)) 1 ∘ₗ
      (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem oddPart_apply (a : A) :
    oddPart 𝒜 a = (DirectSum.decompose 𝒜 a 1 : A) := rfl

theorem oddPart_of_mem_one {a : A} (ha : a ∈ 𝒜 1) : oddPart 𝒜 a = a := by
  rw [oddPart_apply, DirectSum.decompose_of_mem_same 𝒜 ha]

theorem oddPart_of_mem_zero {a : A} (ha : a ∈ 𝒜 0) : oddPart 𝒜 a = 0 := by
  rw [oddPart_apply, DirectSum.decompose_of_mem_ne 𝒜 ha (by decide)]

theorem oddPart_mem (a : A) : oddPart 𝒜 a ∈ 𝒜 1 := by
  rw [oddPart_apply]; exact Submodule.coe_mem _

/-- Scalars are even. -/
theorem algebraMap_mem_grade_zero (r : K) : algebraMap K A r ∈ 𝒜 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ r (SetLike.one_mem_graded 𝒜)

/-! ### The carrier and the signed product -/

/-- The super-opposite of a superalgebra: same carrier, multiplication
`a ∙ b = (-1)^{|a||b|} b a`. -/
def SuperOp (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] : Type _ := A
deriving AddCommGroupWithOne, Module K

namespace SuperOp

/-- Interpret an element of `A` in the super-opposite. -/
def op : A ≃ₗ[K] SuperOp 𝒜 := LinearEquiv.refl K A

/-- The underlying element of `A`. -/
def unop : SuperOp 𝒜 ≃ₗ[K] A := LinearEquiv.refl K A

@[simp] theorem unop_op (a : A) : unop 𝒜 (op 𝒜 a) = a := rfl

@[simp] theorem op_unop (x : SuperOp 𝒜) : op 𝒜 (unop 𝒜 x) = x := rfl

@[simp] theorem unop_one : unop 𝒜 (1 : SuperOp 𝒜) = 1 := rfl

@[simp] theorem op_one : op 𝒜 (1 : A) = 1 := rfl

/-- The grading of the super-opposite: the same homogeneous pieces
(carriers and module structures agree definitionally). -/
def grading : ZMod 2 → Submodule K (SuperOp 𝒜) := 𝒜

instance : DirectSum.Decomposition (grading 𝒜) :=
  inferInstanceAs (DirectSum.Decomposition 𝒜)

theorem mem_grading_iff (i : ZMod 2) (x : SuperOp 𝒜) :
    x ∈ grading 𝒜 i ↔ unop 𝒜 x ∈ 𝒜 i := Iff.rfl

/-- The signed product as a `K`-bilinear map on the underlying module:
`(a, b) ↦ b * a - 2 (oddPart b * oddPart a)`. -/
noncomputable def mulMap : A →ₗ[K] A →ₗ[K] A :=
  (LinearMap.mul K A).flip -
    (2 : ℤ) • ((LinearMap.mul K A).flip.compl₁₂ (oddPart 𝒜) (oddPart 𝒜))

theorem mulMap_apply (a b : A) :
    mulMap 𝒜 a b = b * a - (2 : ℤ) • (oddPart 𝒜 b * oddPart 𝒜 a) := rfl

noncomputable instance : Mul (SuperOp 𝒜) where
  mul x y := op 𝒜 (mulMap 𝒜 (unop 𝒜 x) (unop 𝒜 y))

theorem mul_def (x y : SuperOp 𝒜) :
    x * y = op 𝒜 (mulMap 𝒜 (unop 𝒜 x) (unop 𝒜 y)) := rfl

/-- **The sign law on homogeneous elements**:
`op a * op b = (-1)^{ij} • op (b * a)` for `a ∈ 𝒜 i`, `b ∈ 𝒜 j`. -/
theorem op_mul_op_of_mem {i j : ZMod 2} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    op 𝒜 a * op 𝒜 b = ((sgn (i * j) : ℤˣ) : ℤ) • op 𝒜 (b * a) := by
  rw [mul_def, unop_op, unop_op]
  rcases zmod2_cases i with hi | hi <;> rcases zmod2_cases j with hj | hj <;>
      subst hi <;> subst hj <;>
      rw [mulMap_apply]
  · rw [oddPart_of_mem_zero 𝒜 ha, mul_zero, smul_zero, sub_zero]
    simp
  · rw [oddPart_of_mem_zero 𝒜 ha, mul_zero, smul_zero, sub_zero]
    simp
  · rw [oddPart_of_mem_zero 𝒜 hb, zero_mul, smul_zero, sub_zero]
    simp
  · rw [oddPart_of_mem_one 𝒜 ha, oddPart_of_mem_one 𝒜 hb,
      show (1 : ZMod 2) * 1 = 1 from by decide, ← map_zsmul (op 𝒜)]
    congr 1
    simp only [sgn_one, units_sign_eq, Units.val_neg, Units.val_one, neg_smul,
      one_smul, two_smul]
    abel

/-! ### Ring and algebra structure -/

private theorem mul_add' (x y z : SuperOp 𝒜) : x * (y + z) = x * y + x * z := by
  simp only [mul_def, map_add]

private theorem add_mul' (x y z : SuperOp 𝒜) : (x + y) * z = x * z + y * z := by
  simp only [mul_def, map_add, LinearMap.add_apply]

private theorem zero_mul' (x : SuperOp 𝒜) : 0 * x = 0 := by
  simp only [mul_def, map_zero, LinearMap.zero_apply]

private theorem mul_zero' (x : SuperOp 𝒜) : x * 0 = 0 := by
  simp only [mul_def, map_zero]

private theorem zsmul_mul' (n : ℤ) (x y : SuperOp 𝒜) :
    (n • x) * y = n • (x * y) := by
  simp only [mul_def, map_zsmul, LinearMap.smul_apply]

private theorem mul_zsmul' (n : ℤ) (x y : SuperOp 𝒜) :
    x * (n • y) = n • (x * y) := by
  simp only [mul_def, map_zsmul]

private theorem one_mul' (x : SuperOp 𝒜) : 1 * x = x := by
  have key : ∀ b : A, (1 : SuperOp 𝒜) * op 𝒜 b = op 𝒜 b := by
    intro b
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, mul_zero' 𝒜]
    | homogeneous m =>
        rw [show (1 : SuperOp 𝒜) = op 𝒜 1 from rfl,
          op_mul_op_of_mem 𝒜 (SetLike.one_mem_graded 𝒜) m.2, mul_one]
        simp
    | add m m' hm hm' => rw [map_add, mul_add' 𝒜, hm, hm']
  simpa using key (unop 𝒜 x)

private theorem mul_one' (x : SuperOp 𝒜) : x * 1 = x := by
  have key : ∀ a : A, op 𝒜 a * (1 : SuperOp 𝒜) = op 𝒜 a := by
    intro a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, zero_mul' 𝒜]
    | homogeneous m =>
        rw [show (1 : SuperOp 𝒜) = op 𝒜 1 from rfl,
          op_mul_op_of_mem 𝒜 m.2 (SetLike.one_mem_graded 𝒜), one_mul]
        simp
    | add m m' hm hm' => rw [map_add, add_mul' 𝒜, hm, hm']
  simpa using key (unop 𝒜 x)

private theorem mul_assoc' (x y z : SuperOp 𝒜) : x * y * z = x * (y * z) := by
  have key : ∀ a b c : A,
      op 𝒜 a * op 𝒜 b * op 𝒜 c = op 𝒜 a * (op 𝒜 b * op 𝒜 c) := by
    intro a b c
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp only [map_zero, zero_mul' 𝒜]
    | add m m' hm hm' =>
        simp only [map_add, add_mul' 𝒜, hm, hm']
    | homogeneous ma =>
      induction b using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp only [map_zero, zero_mul' 𝒜, mul_zero' 𝒜]
      | add m m' hm hm' =>
          simp only [map_add, mul_add' 𝒜, add_mul' 𝒜, hm, hm']
      | homogeneous mb =>
        induction c using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp only [map_zero, mul_zero' 𝒜]
        | add m m' hm hm' =>
            simp only [map_add, mul_add' 𝒜, hm, hm']
        | homogeneous mc =>
            rw [op_mul_op_of_mem 𝒜 ma.2 mb.2, zsmul_mul' 𝒜,
              op_mul_op_of_mem 𝒜 (SetLike.mul_mem_graded mb.2 ma.2) mc.2,
              op_mul_op_of_mem 𝒜 mb.2 mc.2, mul_zsmul' 𝒜,
              op_mul_op_of_mem 𝒜 ma.2 (SetLike.mul_mem_graded mc.2 mb.2),
              smul_smul, smul_smul, mul_assoc]
            congr 1
            rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add]
            congr 1
            ring
  simpa using key (unop 𝒜 x) (unop 𝒜 y) (unop 𝒜 z)

noncomputable instance instMonoid : Monoid (SuperOp 𝒜) where
  one_mul := one_mul' 𝒜
  mul_one := mul_one' 𝒜
  mul_assoc := mul_assoc' 𝒜

noncomputable instance instRing : Ring (SuperOp 𝒜) where
  left_distrib := mul_add' 𝒜
  right_distrib := add_mul' 𝒜
  zero_mul := zero_mul' 𝒜
  mul_zero := mul_zero' 𝒜

/-- The scalar inclusion `K →+* A^sop`. -/
noncomputable def algebraMapAux : K →+* SuperOp 𝒜 where
  toFun r := op 𝒜 (algebraMap K A r)
  map_one' := by rw [map_one, op_one]
  map_zero' := by rw [map_zero, map_zero]
  map_add' r r' := by rw [map_add, map_add]
  map_mul' r r' := by
    rw [op_mul_op_of_mem 𝒜 (algebraMap_mem_grade_zero 𝒜 r)
        (algebraMap_mem_grade_zero 𝒜 r'), ← map_mul, mul_comm r']
    simp

private theorem algebraMapAux_mul (r : K) (b : A) :
    algebraMapAux 𝒜 r * op 𝒜 b = op 𝒜 (r • b) := by
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero, mul_zero' 𝒜, smul_zero, map_zero]
  | homogeneous m =>
      rw [show algebraMapAux 𝒜 r = op 𝒜 (algebraMap K A r) from rfl,
        op_mul_op_of_mem 𝒜 (algebraMap_mem_grade_zero 𝒜 r) m.2,
        ← Algebra.commutes r (m : A), ← Algebra.smul_def r (m : A)]
      simp
  | add m m' hm hm' => rw [map_add, mul_add' 𝒜, hm, hm', smul_add, map_add]

private theorem mul_algebraMapAux (r : K) (a : A) :
    op 𝒜 a * algebraMapAux 𝒜 r = op 𝒜 (r • a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero, zero_mul' 𝒜, smul_zero, map_zero]
  | homogeneous m =>
      rw [show algebraMapAux 𝒜 r = op 𝒜 (algebraMap K A r) from rfl,
        op_mul_op_of_mem 𝒜 m.2 (algebraMap_mem_grade_zero 𝒜 r),
        ← Algebra.smul_def r (m : A)]
      simp
  | add m m' hm hm' => rw [map_add, add_mul' 𝒜, hm, hm', smul_add, map_add]

noncomputable instance instAlgebra : Algebra K (SuperOp 𝒜) where
  algebraMap := algebraMapAux 𝒜
  commutes' r x :=
    (algebraMapAux_mul 𝒜 r (unop 𝒜 x)).trans
      (mul_algebraMapAux 𝒜 r (unop 𝒜 x)).symm
  smul_def' r x := (algebraMapAux_mul 𝒜 r (unop 𝒜 x)).symm

/-! ### The grading is multiplicative -/

instance : SetLike.GradedMonoid (grading 𝒜) where
  one_mem := SetLike.one_mem_graded 𝒜
  mul_mem {i j} x y hx hy := by
    show (unop 𝒜 (x * y)) ∈ 𝒜 (i + j)
    rw [mul_def, unop_op, mulMap_apply]
    refine Submodule.sub_mem _ ?_ (zsmul_mem ?_ 2)
    · exact add_comm j i ▸ SetLike.mul_mem_graded hy hx
    · rcases zmod2_cases i with hi | hi <;> rcases zmod2_cases j with hj | hj <;>
        subst hi <;> subst hj
      · rw [oddPart_of_mem_zero 𝒜 (show unop 𝒜 x ∈ 𝒜 0 from hx), mul_zero]
        exact Submodule.zero_mem _
      · rw [oddPart_of_mem_zero 𝒜 (show unop 𝒜 x ∈ 𝒜 0 from hx), mul_zero]
        exact Submodule.zero_mem _
      · rw [oddPart_of_mem_zero 𝒜 (show unop 𝒜 y ∈ 𝒜 0 from hy), zero_mul]
        exact Submodule.zero_mem _
      · rw [oddPart_of_mem_one 𝒜 (show unop 𝒜 x ∈ 𝒜 1 from hx),
          oddPart_of_mem_one 𝒜 (show unop 𝒜 y ∈ 𝒜 1 from hy)]
        exact SetLike.mul_mem_graded (show unop 𝒜 y ∈ 𝒜 1 from hy)
          (show unop 𝒜 x ∈ 𝒜 1 from hx)

/-- The super-opposite is itself a superalgebra. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading 𝒜) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

end SuperOp

end Superfusion

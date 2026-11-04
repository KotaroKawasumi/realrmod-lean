/-
Superfusion / Super / PlainOpposite

The ordinary multiplicative opposite of a superalgebra, with the grading
transported through `op`/`unop`.

This is deliberately distinct from `SuperOp`: the latter changes the
opposite multiplication by the Koszul sign, whereas `Aᵐᵒᵖ` is the ordinary
opposite ring used to encode a native right `A`-module as a left module.

The main structural result is the basis-free algebra equivalence

  `Bᵐᵒᵖ ᵍ⊗ Aᵐᵒᵖ ≃ₐ (A ᵍ⊗ B)ᵐᵒᵖ`,

with the factors reversed and

  `op b ᵍ⊗ₜ op a ↦ op (a ᵍ⊗ₜ b)`.

This is the coefficient-algebra bridge needed for the signed external
tensor product of graded right modules.  No finiteness, freeness, basis,
division, or characteristic assumption is used.
-/
import Superfusion.Super.TensorGradingAssoc
import Mathlib.Algebra.Algebra.Opposite

namespace Superfusion

open TensorProduct
open GradedTensorProduct

/-! ### The transported grading on the ordinary opposite -/

section Grading

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒟 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒟]

/-- The grading on the ordinary multiplicative opposite: degree `i` is
transported unchanged through `unop`. -/
def opGrading (i : ZMod 2) : Submodule K Aᵐᵒᵖ :=
  (𝒟 i).comap (MulOpposite.opLinearEquiv K).symm.toLinearMap

omit [GradedAlgebra 𝒟] in
theorem mem_opGrading_iff {i : ZMod 2} {x : Aᵐᵒᵖ} :
    x ∈ opGrading 𝒟 i ↔ MulOpposite.unop x ∈ 𝒟 i :=
  Iff.rfl

instance : SetLike.GradedMonoid (opGrading 𝒟) where
  one_mem := by
    show MulOpposite.unop (1 : Aᵐᵒᵖ) ∈ 𝒟 0
    rw [MulOpposite.unop_one]
    exact SetLike.one_mem_graded 𝒟
  mul_mem {i j} {a b} ha hb := by
    show MulOpposite.unop (a * b) ∈ 𝒟 (i + j)
    rw [MulOpposite.unop_mul]
    have h := SetLike.mul_mem_graded
      ((mem_opGrading_iff 𝒟).mp hb) ((mem_opGrading_iff 𝒟).mp ha)
    rwa [add_comm j i] at h

/-- The degree projection transported through `op`/`unop`. -/
noncomputable def opMask (i : ZMod 2) : Aᵐᵒᵖ →ₗ[K] Aᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv K).toLinearMap ∘ₗ gradeProj 𝒟 i ∘ₗ
    (MulOpposite.opLinearEquiv K).symm.toLinearMap

theorem opMask_apply (i : ZMod 2) (x : Aᵐᵒᵖ) :
    opMask 𝒟 i x =
      MulOpposite.op (gradeProj 𝒟 i (MulOpposite.unop x)) :=
  rfl

theorem opMask_mem (i : ZMod 2) (x : Aᵐᵒᵖ) :
    opMask 𝒟 i x ∈ opGrading 𝒟 i := by
  rw [mem_opGrading_iff, opMask_apply, MulOpposite.unop_op]
  exact gradeProj_mem 𝒟 i _

theorem opMask_of_mem {i : ZMod 2} {x : Aᵐᵒᵖ}
    (hx : x ∈ opGrading 𝒟 i) :
    opMask 𝒟 i x = x := by
  rw [opMask_apply, gradeProj_of_mem 𝒟 ((mem_opGrading_iff 𝒟).mp hx),
    MulOpposite.op_unop]

theorem opMask_of_mem_ne {i j : ZMod 2} {x : Aᵐᵒᵖ}
    (hx : x ∈ opGrading 𝒟 i) (hij : i ≠ j) :
    opMask 𝒟 j x = 0 := by
  rw [opMask_apply,
    gradeProj_of_mem_ne 𝒟 ((mem_opGrading_iff 𝒟).mp hx) hij,
    MulOpposite.op_zero]

theorem opMask_zero_add_opMask_one (x : Aᵐᵒᵖ) :
    opMask 𝒟 0 x + opMask 𝒟 1 x = x := by
  rw [opMask_apply, opMask_apply, ← MulOpposite.op_add,
    gradeProj_zero_add_gradeProj_one, MulOpposite.op_unop]

/-- The degree mask, corestricted to its selected layer. -/
noncomputable def opMaskInto (i : ZMod 2) :
    Aᵐᵒᵖ →ₗ[K] opGrading 𝒟 i :=
  LinearMap.codRestrict (opGrading 𝒟 i) (opMask 𝒟 i) (opMask_mem 𝒟 i)

noncomputable instance : DirectSum.Decomposition (opGrading 𝒟) where
  decompose' x :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(opGrading 𝒟 i)) 0
        (opMaskInto 𝒟 0 x)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(opGrading 𝒟 i)) 1
        (opMaskInto 𝒟 1 x)
  left_inv x := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact opMask_zero_add_opMask_one 𝒟 x
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
          have h1 : opMaskInto 𝒟 0 (b : Aᵐᵒᵖ) = b :=
            Subtype.ext (opMask_of_mem 𝒟 b.2)
          have h2 : opMaskInto 𝒟 1 (b : Aᵐᵒᵖ) = 0 :=
            Subtype.ext (opMask_of_mem_ne 𝒟 b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : opMaskInto 𝒟 0 (b : Aᵐᵒᵖ) = 0 :=
            Subtype.ext (opMask_of_mem_ne 𝒟 b.2 (by decide))
          have h2 : opMaskInto 𝒟 1 (b : Aᵐᵒᵖ) = b :=
            Subtype.ext (opMask_of_mem 𝒟 b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-- The ordinary opposite, with the grading transported through `unop`, is
again a graded algebra. -/
noncomputable instance opGradedAlgebra :
    GradedAlgebra (opGrading 𝒟) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

end Grading

/-! ### The ordinary opposite reverses graded tensor factors -/

section TensorDistrib

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The `Bᵐᵒᵖ` factor, placed on the right before taking the ordinary
opposite. -/
private noncomputable def opGtensorDistribLeft :
    Bᵐᵒᵖ →ₐ[K] (𝒜 ᵍ⊗[K] ℬ)ᵐᵒᵖ :=
  AlgHom.op (includeRight 𝒜 ℬ)

/-- The `Aᵐᵒᵖ` factor, placed on the left before taking the ordinary
opposite. -/
private noncomputable def opGtensorDistribRight :
    Aᵐᵒᵖ →ₐ[K] (𝒜 ᵍ⊗[K] ℬ)ᵐᵒᵖ :=
  AlgHom.op (includeLeft 𝒜 ℬ)

private theorem opGtensorDistribLeft_op (b : B) :
    opGtensorDistribLeft 𝒜 ℬ (MulOpposite.op b)
      = MulOpposite.op (includeRight 𝒜 ℬ b) :=
  rfl

private theorem opGtensorDistribRight_op (a : A) :
    opGtensorDistribRight 𝒜 ℬ (MulOpposite.op a)
      = MulOpposite.op (includeLeft 𝒜 ℬ a) :=
  rfl

private theorem sgn_self_cancel : ∀ e : ZMod 2,
    ((-1 : ℤˣ) ^ e) * ((-1 : ℤˣ) ^ e) = 1 := by
  decide

private theorem opGtensorDistrib_anticommutes :
    ∀ ⦃i j : ZMod 2⦄ (b : opGrading ℬ i) (a : opGrading 𝒜 j),
      opGtensorDistribLeft 𝒜 ℬ b * opGtensorDistribRight 𝒜 ℬ a
        = (-1 : ℤˣ) ^ (j * i) •
          (opGtensorDistribRight 𝒜 ℬ a
            * opGtensorDistribLeft 𝒜 ℬ b) := by
  intro i j b a
  apply MulOpposite.unop_injective
  have hb : MulOpposite.unop (b : Bᵐᵒᵖ) ∈ ℬ i := b.2
  have ha : MulOpposite.unop (a : Aᵐᵒᵖ) ∈ 𝒜 j := a.2
  rw [show (b : Bᵐᵒᵖ) = MulOpposite.op (MulOpposite.unop b) from rfl,
    show (a : Aᵐᵒᵖ) = MulOpposite.op (MulOpposite.unop a) from rfl,
    opGtensorDistribLeft_op, opGtensorDistribRight_op,
    MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op,
    MulOpposite.unop_smul,
    MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op,
    includeLeft_mul_includeRight,
    includeRight_mul_includeLeft 𝒜 ℬ ha hb,
    show i * j = j * i from mul_comm i j,
    smul_smul, sgn_self_cancel (j * i), one_smul]
  exact (includeLeft_mul_includeRight 𝒜 ℬ _ _).symm

/-- The canonical algebra map
`Bᵐᵒᵖ ᵍ⊗ Aᵐᵒᵖ → (A ᵍ⊗ B)ᵐᵒᵖ`. -/
noncomputable def opGtensorDistribHom :
    ((opGrading ℬ) ᵍ⊗[K] (opGrading 𝒜)) →ₐ[K]
      (𝒜 ᵍ⊗[K] ℬ)ᵐᵒᵖ :=
  lift (opGrading ℬ) (opGrading 𝒜)
    (opGtensorDistribLeft 𝒜 ℬ) (opGtensorDistribRight 𝒜 ℬ)
    (opGtensorDistrib_anticommutes 𝒜 ℬ)

@[simp]
theorem opGtensorDistribHom_tmul (a : A) (b : B) :
    opGtensorDistribHom 𝒜 ℬ
        (MulOpposite.op b ᵍ⊗ₜ[K] MulOpposite.op a)
      = MulOpposite.op (a ᵍ⊗ₜ[K] b) := by
  rw [opGtensorDistribHom, lift_tmul]
  apply MulOpposite.unop_injective
  change
    includeLeft 𝒜 ℬ a * includeRight 𝒜 ℬ b =
      a ᵍ⊗ₜ[K] b
  exact tmul_one_mul_one_tmul 𝒜 ℬ a b

/-- The evident inverse at the underlying linear level:
`op (a ᵍ⊗ b) ↦ op b ᵍ⊗ op a`. -/
private noncomputable def opGtensorDistribInv :
    (𝒜 ᵍ⊗[K] ℬ)ᵐᵒᵖ →ₗ[K]
      ((opGrading ℬ) ᵍ⊗[K] (opGrading 𝒜)) :=
  (of K (opGrading ℬ) (opGrading 𝒜)).toLinearMap
    ∘ₗ (TensorProduct.map
      (MulOpposite.opLinearEquiv K : B ≃ₗ[K] Bᵐᵒᵖ)
      (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ))
    ∘ₗ (TensorProduct.comm K A B).toLinearMap
    ∘ₗ (of K 𝒜 ℬ).symm.toLinearMap
    ∘ₗ (MulOpposite.opLinearEquiv K :
      (𝒜 ᵍ⊗[K] ℬ) ≃ₗ[K] (𝒜 ᵍ⊗[K] ℬ)ᵐᵒᵖ).symm.toLinearMap

@[simp]
private theorem opGtensorDistribInv_tmul (a : A) (b : B) :
    opGtensorDistribInv 𝒜 ℬ (MulOpposite.op (a ᵍ⊗ₜ[K] b))
      = MulOpposite.op b ᵍ⊗ₜ[K] MulOpposite.op a :=
  rfl

theorem opGtensorDistribHom_bijective :
    Function.Bijective (opGtensorDistribHom 𝒜 ℬ) := by
  constructor
  · apply Function.LeftInverse.injective
      (g := opGtensorDistribInv 𝒜 ℬ)
    intro z
    have key : ∀ t : Bᵐᵒᵖ ⊗[K] Aᵐᵒᵖ,
        opGtensorDistribInv 𝒜 ℬ
            (opGtensorDistribHom 𝒜 ℬ
              (of K (opGrading ℬ) (opGrading 𝒜) t))
          = of K (opGrading ℬ) (opGrading 𝒜) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b a =>
          rw [show of K (opGrading ℬ) (opGrading 𝒜)
                (b ⊗ₜ[K] a) = b ᵍ⊗ₜ[K] a from rfl,
            show b = MulOpposite.op (MulOpposite.unop b) from
              (MulOpposite.op_unop b).symm,
            show a = MulOpposite.op (MulOpposite.unop a) from
              (MulOpposite.op_unop a).symm,
            opGtensorDistribHom_tmul, opGtensorDistribInv_tmul]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    have h := key ((of K (opGrading ℬ) (opGrading 𝒜)).symm z)
    rwa [symm_of_of] at h
  · intro w
    refine ⟨opGtensorDistribInv 𝒜 ℬ w, ?_⟩
    have key : ∀ t : A ⊗[K] B,
        opGtensorDistribHom 𝒜 ℬ
            (opGtensorDistribInv 𝒜 ℬ
              (MulOpposite.op (of K 𝒜 ℬ t)))
          = MulOpposite.op (of K 𝒜 ℬ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero, MulOpposite.op_zero]
      | tmul a b =>
          rw [show of K 𝒜 ℬ (a ⊗ₜ[K] b)
                = a ᵍ⊗ₜ[K] b from rfl,
            opGtensorDistribInv_tmul, opGtensorDistribHom_tmul]
      | add x y hx hy =>
          rw [map_add, MulOpposite.op_add, map_add, map_add, hx, hy]
    have h := key ((of K 𝒜 ℬ).symm (MulOpposite.unop w))
    rwa [symm_of_of, MulOpposite.op_unop] at h

/-- The distribution map preserves total parity. -/
theorem opGtensorDistribHom_isHomogeneous :
    IsHomogeneousHom
      (tensorGrading (opGrading ℬ) (opGrading 𝒜))
      (opGrading (tensorGrading 𝒜 ℬ))
      (opGtensorDistribHom 𝒜 ℬ) := by
  intro i z hz
  refine tensorGrading_induction (opGrading ℬ) (opGrading 𝒜) hz
    (p := fun w =>
      opGtensorDistribHom 𝒜 ℬ w ∈
        opGrading (tensorGrading 𝒜 ℬ) i)
    ?_ ?_ ?_ ?_
  · intro j k b a hjk hb ha
    rw [show b = MulOpposite.op (MulOpposite.unop b) from rfl,
      show a = MulOpposite.op (MulOpposite.unop a) from rfl,
      opGtensorDistribHom_tmul, mem_opGrading_iff,
      MulOpposite.unop_op]
    have h := tmul_mem_tensorGrading 𝒜 ℬ
      (ha : MulOpposite.unop a ∈ 𝒜 k)
      (hb : MulOpposite.unop b ∈ ℬ j)
    rwa [add_comm k j, hjk] at h
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- **The ordinary opposite reverses graded tensor factors**:
`Bᵐᵒᵖ ᵍ⊗ Aᵐᵒᵖ ≃ₐ (A ᵍ⊗ B)ᵐᵒᵖ`. -/
noncomputable def opGtensorDistrib :
    ((opGrading ℬ) ᵍ⊗[K] (opGrading 𝒜)) ≃ₐ[K]
      (𝒜 ᵍ⊗[K] ℬ)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (opGtensorDistribHom 𝒜 ℬ)
    (opGtensorDistribHom_bijective 𝒜 ℬ)

@[simp]
theorem opGtensorDistrib_tmul (a : A) (b : B) :
    opGtensorDistrib 𝒜 ℬ
        (MulOpposite.op b ᵍ⊗ₜ[K] MulOpposite.op a)
      = MulOpposite.op (a ᵍ⊗ₜ[K] b) :=
  opGtensorDistribHom_tmul 𝒜 ℬ a b

/-- The distribution equivalence maps every homogeneous layer onto the
corresponding layer of the ordinary opposite. -/
theorem opGtensorDistrib_map_grading (i : ZMod 2) :
    (tensorGrading (opGrading ℬ) (opGrading 𝒜) i).map
        (opGtensorDistrib 𝒜 ℬ).toLinearMap
      = opGrading (tensorGrading 𝒜 ℬ) i :=
  map_grading_of_bijective
    (tensorGrading (opGrading ℬ) (opGrading 𝒜))
    (opGrading (tensorGrading 𝒜 ℬ))
    (opGtensorDistrib 𝒜 ℬ).toAlgHom
    (opGtensorDistribHom_isHomogeneous 𝒜 ℬ)
    (opGtensorDistrib 𝒜 ℬ).bijective i

/-- The inverse sends a pure opposite tensor to the reversed pure tensor
of opposites. -/
@[simp]
theorem opGtensorDistrib_symm_tmul (a : A) (b : B) :
    (opGtensorDistrib 𝒜 ℬ).symm
        (MulOpposite.op (a ᵍ⊗ₜ[K] b))
      = MulOpposite.op b ᵍ⊗ₜ[K] MulOpposite.op a := by
  rw [AlgEquiv.symm_apply_eq, opGtensorDistrib_tmul]

end TensorDistrib

end Superfusion

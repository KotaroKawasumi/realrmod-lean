/-
Superfusion / Super / TensorGradingSop

Milestone M7f-1d: **the super-opposite distributes over the graded
tensor product** —

  `sopDistrib : 𝒜ˢᵒᵖ ᵍ⊗ ℬˢᵒᵖ ≃ₐ (𝒜 ᵍ⊗ ℬ)ˢᵒᵖ`,
  `op a ᵍ⊗ op b ↦ op (a ᵍ⊗ b)`,

with **no sign**: the super-opposite signs and the Koszul signs cancel
identically (checked through `∀`-closed `sgn` identities by `decide`).

Prerequisite: the super-opposite is functorial in homogeneous algebra
maps (`sopMap`, using that grade-preserving homs commute with
`oddPart` — `oddPart_map_of_isHomogeneous`, M7d-2), so the two
inclusions of `𝒜 ᵍ⊗ ℬ` induce maps `SuperOp 𝒜 → SuperOp (𝒜 ᵍ⊗ ℬ)`
etc., and the universal property applies.  The inverse is the evident
linear identification (everything is a type synonym of `A ⊗[K] B`).

This is the last reshuffling piece for M7f-2 (Wall-map factorization
`(A ᵍ⊗ B) ᵍ⊗ (A ᵍ⊗ B)ˢᵒᵖ ≅ (A ᵍ⊗ Aˢᵒᵖ) ᵍ⊗ (B ᵍ⊗ Bˢᵒᵖ)`) and gives
the inverses of the Brauer–Wall group (M7f-4).
-/
import Superfusion.Super.TensorGradingAssoc
import Superfusion.Super.SuperOpposite

namespace Superfusion

open TensorProduct
open GradedTensorProduct

/-! ### Functoriality of the super-opposite -/

section SopMap

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable (h : A →ₐ[K] B) (hh : IsHomogeneousHom 𝒜 ℬ h)

include hh in
private theorem sopMap_mul_aux (x y : SuperOp 𝒜) :
    h (SuperOp.mulMap 𝒜 (SuperOp.unop 𝒜 x) (SuperOp.unop 𝒜 y))
      = SuperOp.mulMap ℬ (h (SuperOp.unop 𝒜 x))
          (h (SuperOp.unop 𝒜 y)) := by
  rw [SuperOp.mulMap_apply, SuperOp.mulMap_apply, map_sub, map_mul,
    map_zsmul, map_mul, oddPart_map_of_isHomogeneous 𝒜 ℬ h hh,
    oddPart_map_of_isHomogeneous 𝒜 ℬ h hh]

/-- The super-opposite of a homogeneous algebra map. -/
noncomputable def sopMap : SuperOp 𝒜 →ₐ[K] SuperOp ℬ :=
  AlgHom.ofLinearMap
    ((SuperOp.op ℬ).toLinearMap ∘ₗ h.toLinearMap
      ∘ₗ (SuperOp.unop 𝒜).toLinearMap)
    (by
      show SuperOp.op ℬ (h (SuperOp.unop 𝒜 1)) = 1
      rw [SuperOp.unop_one, map_one, SuperOp.op_one])
    (fun x y => by
      show SuperOp.op ℬ (h (SuperOp.unop 𝒜 (x * y))) = _
      rw [SuperOp.mul_def, SuperOp.unop_op,
        sopMap_mul_aux 𝒜 ℬ h hh x y]
      rfl)

@[simp] theorem sopMap_op (a : A) :
    sopMap 𝒜 ℬ h hh (SuperOp.op 𝒜 a) = SuperOp.op ℬ (h a) := rfl

theorem sopMap_isHomogeneous :
    IsHomogeneousHom (SuperOp.grading 𝒜) (SuperOp.grading ℬ)
      (sopMap 𝒜 ℬ h hh) :=
  fun i x hx => hh i (SuperOp.unop 𝒜 x) hx

end SopMap

/-! ### Distribution over the graded tensor product -/

section SopDistrib

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

private theorem sgn_cross_cancel : ∀ i j : ZMod 2,
    ((sgn (i * j) : ℤˣ) * sgn (j * i)) = 1 := by
  decide

private theorem sgn_self_cancel : ∀ e : ZMod 2,
    ((sgn e : ℤˣ) * sgn e) = 1 := by
  decide

private theorem op_uzsmul {C : Type*} [Ring C] [Algebra K C]
    (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞] (u : ℤˣ) (w : C) :
    SuperOp.op 𝒞 (u • w) = u • SuperOp.op 𝒞 w := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem gtmul_add' (x : A) (y y' : B) :
    x ᵍ⊗ₜ[K] (y + y') = (x ᵍ⊗ₜ[K] y + x ᵍ⊗ₜ[K] y' : 𝒜 ᵍ⊗[K] ℬ) := by
  show of K 𝒜 ℬ (x ⊗ₜ[K] (y + y')) = _
  rw [TensorProduct.tmul_add, map_add]

private theorem add_gtmul' (x x' : A) (y : B) :
    (x + x') ᵍ⊗ₜ[K] y = (x ᵍ⊗ₜ[K] y + x' ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] ℬ) := by
  show of K 𝒜 ℬ ((x + x') ⊗ₜ[K] y) = _
  rw [TensorProduct.add_tmul, map_add]

/-- The homogeneous case of the key product computation:
`op (a ᵍ⊗ 1) * op (1 ᵍ⊗ b) = op (a ᵍ⊗ b)` in the super-opposite of
the graded tensor product — the super-opposite sign and the Koszul
sign cancel. -/
theorem op_incl_mul_op_incl_of_mem {α β : ZMod 2} {a : A}
    {b : B} (ha : a ∈ 𝒜 α) (hb : b ∈ ℬ β) :
    SuperOp.op (tensorGrading 𝒜 ℬ) (includeLeft 𝒜 ℬ a)
        * SuperOp.op (tensorGrading 𝒜 ℬ) (includeRight 𝒜 ℬ b)
      = SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b) := by
  rw [SuperOp.op_mul_op_of_mem (tensorGrading 𝒜 ℬ)
      (includeLeft_mem_tensorGrading 𝒜 ℬ ha)
      (includeRight_mem_tensorGrading 𝒜 ℬ hb),
    includeRight_mul_includeLeft 𝒜 ℬ ha hb,
    op_uzsmul (tensorGrading 𝒜 ℬ), includeLeft_mul_includeRight,
    ← Units.smul_def, smul_smul, ← sgn_eq_neg_one_uzpow,
    sgn_cross_cancel α β, one_smul]

/-- The general case, by decomposing both factors into homogeneous
parts (both sides are bilinear). -/
theorem op_incl_mul_op_incl (a : A) (b : B) :
    SuperOp.op (tensorGrading 𝒜 ℬ) (includeLeft 𝒜 ℬ a)
        * SuperOp.op (tensorGrading 𝒜 ℬ) (includeRight 𝒜 ℬ b)
      = SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b) := by
  conv_lhs => rw [← evenPart_add_oddPart 𝒜 a,
    ← evenPart_add_oddPart ℬ b]
  conv_rhs => rw [← evenPart_add_oddPart 𝒜 a,
    ← evenPart_add_oddPart ℬ b]
  simp only [map_add, add_mul, mul_add, add_gtmul' 𝒜 ℬ, gtmul_add' 𝒜 ℬ]
  rw [op_incl_mul_op_incl_of_mem 𝒜 ℬ (evenPart_mem 𝒜 a)
      (evenPart_mem ℬ b),
    op_incl_mul_op_incl_of_mem 𝒜 ℬ (evenPart_mem 𝒜 a)
      (oddPart_mem ℬ b),
    op_incl_mul_op_incl_of_mem 𝒜 ℬ (oddPart_mem 𝒜 a)
      (evenPart_mem ℬ b),
    op_incl_mul_op_incl_of_mem 𝒜 ℬ (oddPart_mem 𝒜 a)
      (oddPart_mem ℬ b)]
  abel

/-- The left factor of the distribution map. -/
private noncomputable def sopF :
    SuperOp 𝒜 →ₐ[K] SuperOp (tensorGrading 𝒜 ℬ) :=
  sopMap 𝒜 (tensorGrading 𝒜 ℬ) (includeLeft 𝒜 ℬ)
    (fun _ _ hx => includeLeft_mem_tensorGrading 𝒜 ℬ hx)

/-- The right factor of the distribution map. -/
private noncomputable def sopG :
    SuperOp ℬ →ₐ[K] SuperOp (tensorGrading 𝒜 ℬ) :=
  sopMap ℬ (tensorGrading 𝒜 ℬ) (includeRight 𝒜 ℬ)
    (fun _ _ hy => includeRight_mem_tensorGrading 𝒜 ℬ hy)

private theorem sopF_op (a : A) :
    sopF 𝒜 ℬ (SuperOp.op 𝒜 a)
      = SuperOp.op (tensorGrading 𝒜 ℬ) (includeLeft 𝒜 ℬ a) := rfl

private theorem sopG_op (b : B) :
    sopG 𝒜 ℬ (SuperOp.op ℬ b)
      = SuperOp.op (tensorGrading 𝒜 ℬ) (includeRight 𝒜 ℬ b) := rfl

private theorem sop_anticommutes :
    ∀ ⦃i j : ZMod 2⦄ (x : SuperOp.grading 𝒜 i)
      (y : SuperOp.grading ℬ j),
      sopF 𝒜 ℬ x * sopG 𝒜 ℬ y
        = (-1 : ℤˣ) ^ (j * i) • (sopG 𝒜 ℬ y * sopF 𝒜 ℬ x) := by
  intro i j x y
  have hx : SuperOp.unop 𝒜 (x : SuperOp 𝒜) ∈ 𝒜 i := x.2
  have hy : SuperOp.unop ℬ (y : SuperOp ℬ) ∈ ℬ j := y.2
  rw [show ((x : SuperOp 𝒜)) = SuperOp.op 𝒜 (SuperOp.unop 𝒜 x)
      from rfl,
    show ((y : SuperOp ℬ)) = SuperOp.op ℬ (SuperOp.unop ℬ y)
      from rfl,
    sopF_op, sopG_op, op_incl_mul_op_incl_of_mem 𝒜 ℬ hx hy,
    SuperOp.op_mul_op_of_mem (tensorGrading 𝒜 ℬ)
      (includeRight_mem_tensorGrading 𝒜 ℬ hy)
      (includeLeft_mem_tensorGrading 𝒜 ℬ hx),
    includeLeft_mul_includeRight, ← Units.smul_def, smul_smul,
    ← sgn_eq_neg_one_uzpow, sgn_self_cancel (j * i), one_smul]

/-- The distribution map, from the universal property. -/
noncomputable def sopDistribHom :
    ((SuperOp.grading 𝒜) ᵍ⊗[K] (SuperOp.grading ℬ)) →ₐ[K]
      SuperOp (tensorGrading 𝒜 ℬ) :=
  lift (SuperOp.grading 𝒜) (SuperOp.grading ℬ) (sopF 𝒜 ℬ) (sopG 𝒜 ℬ)
    (sop_anticommutes 𝒜 ℬ)

theorem sopDistribHom_tmul (a : A) (b : B) :
    sopDistribHom 𝒜 ℬ (SuperOp.op 𝒜 a ᵍ⊗ₜ[K] SuperOp.op ℬ b)
      = SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b) := by
  rw [sopDistribHom,
    lift_tmul (SuperOp.grading 𝒜) (SuperOp.grading ℬ) (sopF 𝒜 ℬ)
      (sopG 𝒜 ℬ) (sop_anticommutes 𝒜 ℬ),
    sopF_op, sopG_op, op_incl_mul_op_incl]

/-- The inverse, as the evident linear identification. -/
private noncomputable def sopDistribInv :
    SuperOp (tensorGrading 𝒜 ℬ) →ₗ[K]
      ((SuperOp.grading 𝒜) ᵍ⊗[K] (SuperOp.grading ℬ)) :=
  (of K (SuperOp.grading 𝒜) (SuperOp.grading ℬ)).toLinearMap
    ∘ₗ (TensorProduct.map (SuperOp.op 𝒜).toLinearMap
        (SuperOp.op ℬ).toLinearMap)
    ∘ₗ (of K 𝒜 ℬ).symm.toLinearMap
    ∘ₗ (SuperOp.unop (tensorGrading 𝒜 ℬ)).toLinearMap

theorem sopDistribHom_bijective :
    Function.Bijective (sopDistribHom 𝒜 ℬ) := by
  constructor
  · apply Function.LeftInverse.injective (g := sopDistribInv 𝒜 ℬ)
    intro z
    have key : ∀ t : (SuperOp 𝒜) ⊗[K] (SuperOp ℬ),
        sopDistribInv 𝒜 ℬ (sopDistribHom 𝒜 ℬ
          (of K (SuperOp.grading 𝒜) (SuperOp.grading ℬ) t))
        = of K (SuperOp.grading 𝒜) (SuperOp.grading ℬ) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | tmul x y =>
          rw [show of K (SuperOp.grading 𝒜) (SuperOp.grading ℬ)
              (x ⊗ₜ[K] y) = x ᵍ⊗ₜ[K] y from rfl,
            show (x ᵍ⊗ₜ[K] y :
                (SuperOp.grading 𝒜) ᵍ⊗[K] (SuperOp.grading ℬ))
              = SuperOp.op 𝒜 (SuperOp.unop 𝒜 x)
                ᵍ⊗ₜ[K] SuperOp.op ℬ (SuperOp.unop ℬ y) from rfl,
            sopDistribHom_tmul]
          rfl
      | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
    have h := key
      ((of K (SuperOp.grading 𝒜) (SuperOp.grading ℬ)).symm z)
    rwa [symm_of_of] at h
  · intro w
    refine ⟨sopDistribInv 𝒜 ℬ w, ?_⟩
    have key : ∀ t : A ⊗[K] B,
        sopDistribHom 𝒜 ℬ (sopDistribInv 𝒜 ℬ
          (SuperOp.op (tensorGrading 𝒜 ℬ) (of K 𝒜 ℬ t)))
        = SuperOp.op (tensorGrading 𝒜 ℬ) (of K 𝒜 ℬ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero, map_zero]
      | tmul a b =>
          rw [show of K 𝒜 ℬ (a ⊗ₜ[K] b) = a ᵍ⊗ₜ[K] b from rfl,
            show sopDistribInv 𝒜 ℬ
              (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b))
              = SuperOp.op 𝒜 a ᵍ⊗ₜ[K] SuperOp.op ℬ b from rfl,
            sopDistribHom_tmul]
      | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
    have h := key
      ((of K 𝒜 ℬ).symm (SuperOp.unop (tensorGrading 𝒜 ℬ) w))
    rwa [symm_of_of, SuperOp.op_unop] at h

/-- **The super-opposite distributes over the graded tensor product**
(M7f-1d): `𝒜ˢᵒᵖ ᵍ⊗ ℬˢᵒᵖ ≃ₐ (𝒜 ᵍ⊗ ℬ)ˢᵒᵖ`, `op a ᵍ⊗ op b ↦
op (a ᵍ⊗ b)`, with no sign. -/
noncomputable def sopDistrib :
    ((SuperOp.grading 𝒜) ᵍ⊗[K] (SuperOp.grading ℬ)) ≃ₐ[K]
      SuperOp (tensorGrading 𝒜 ℬ) :=
  AlgEquiv.ofBijective (sopDistribHom 𝒜 ℬ) (sopDistribHom_bijective 𝒜 ℬ)

@[simp] theorem sopDistrib_tmul (a : A) (b : B) :
    sopDistrib 𝒜 ℬ (SuperOp.op 𝒜 a ᵍ⊗ₜ[K] SuperOp.op ℬ b)
      = SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b) :=
  sopDistribHom_tmul 𝒜 ℬ a b

theorem sopDistribHom_isHomogeneous :
    IsHomogeneousHom
      (tensorGrading (SuperOp.grading 𝒜) (SuperOp.grading ℬ))
      (SuperOp.grading (tensorGrading 𝒜 ℬ)) (sopDistribHom 𝒜 ℬ) := by
  intro i z hz
  refine tensorGrading_induction (SuperOp.grading 𝒜)
    (SuperOp.grading ℬ) hz
    (p := fun w => sopDistribHom 𝒜 ℬ w
      ∈ SuperOp.grading (tensorGrading 𝒜 ℬ) i)
    ?_ ?_ ?_ ?_
  · intro j k x y hjk hx hy
    rw [show (x ᵍ⊗ₜ[K] y :
        (SuperOp.grading 𝒜) ᵍ⊗[K] (SuperOp.grading ℬ))
      = SuperOp.op 𝒜 (SuperOp.unop 𝒜 x)
        ᵍ⊗ₜ[K] SuperOp.op ℬ (SuperOp.unop ℬ y) from rfl,
      sopDistribHom_tmul]
    have h := tmul_mem_tensorGrading 𝒜 ℬ
      (hx : SuperOp.unop 𝒜 x ∈ 𝒜 j) (hy : SuperOp.unop ℬ y ∈ ℬ k)
    exact hjk ▸ h
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- The distribution carries the tensor grading of the opposites
**onto** the opposite of the tensor grading. -/
theorem sopDistrib_map_grading (i : ZMod 2) :
    (tensorGrading (SuperOp.grading 𝒜) (SuperOp.grading ℬ) i).map
        (sopDistrib 𝒜 ℬ).toLinearMap
      = SuperOp.grading (tensorGrading 𝒜 ℬ) i :=
  map_grading_of_bijective
    (tensorGrading (SuperOp.grading 𝒜) (SuperOp.grading ℬ))
    (SuperOp.grading (tensorGrading 𝒜 ℬ)) (sopDistrib 𝒜 ℬ).toAlgHom
    (sopDistribHom_isHomogeneous 𝒜 ℬ) (sopDistrib 𝒜 ℬ).bijective i

end SopDistrib

end Superfusion

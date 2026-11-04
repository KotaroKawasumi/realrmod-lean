/-
Superfusion / Super / GradedEndTensor

Milestone M7f-1f (part i): **the graded map
`End(A) ᵍ⊗ End(B) → End(A ᵍ⊗ B)`** —

  `endTensorHom (f ᵍ⊗ g) = endInclLeft f * endInclRight g`,

where `endInclLeft f = f ⊗ₗ id` and `endInclRight` is the **signed**
right inclusion `g ↦ id ⊗ₗ g₀ + J ⊗ₗ g₁` (`J` the parity involution
of `𝒜`, `g₀/g₁` the graded components of `g`).  The sign is forced:
`J² = id` makes the right inclusion multiplicative, and the two
inclusions then anticommute with exactly the Koszul sign, so the
universal property of `ᵍ⊗` applies.  On homogeneous data this is the
physicists' `f ⊗ g` acting with the Koszul sign `(-1)^{|g||x|}`.

The map is homogeneous for the M7f-1a/1e gradings.  Part ii (next
milestone): bijectivity in finite dimensions — the underlying linear
map is mathlib's `homTensorHomEquiv` composed with an involutive
twist, so no simplicity argument is needed.

This is the target-side arm of the Wall-map factorization (M7f-2):
`Wall_{A ᵍ⊗ B} = endTensorHom ∘ (Wall_A ᵍ⊗ Wall_B) ∘ reshuffle`.
-/
import Superfusion.Super.GradedEnd
import Superfusion.Super.TensorGradingAssoc
import Superfusion.Super.ParityInvolution
import Mathlib.LinearAlgebra.Contraction

namespace Superfusion

open TensorProduct
open GradedTensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

private theorem zmod2_endT_left : ∀ k i l : ZMod 2,
    (k + i) + l = (k + l) + i := by
  decide

private theorem zmod2_endT_right : ∀ k l j : ZMod 2,
    k + (l + j) = (k + l) + j := by
  decide

/-! ### The parity involution against homogeneous endomorphisms -/

theorem parityMap_comp_of_mem_zero {f : Module.End K A}
    (hf : f ∈ endGrading 𝒜 0) :
    parityMap 𝒜 ∘ₗ f = f ∘ₗ parityMap 𝒜 := by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [← gradeProj_zero_add_gradeProj_one 𝒜 x]
  conv_rhs => rw [← gradeProj_zero_add_gradeProj_one 𝒜 x]
  have h0 : f (gradeProj 𝒜 0 x) ∈ 𝒜 0 := by
    have h := hf 0 _ (gradeProj_mem 𝒜 0 x)
    rwa [add_zero] at h
  have h1 : f (gradeProj 𝒜 1 x) ∈ 𝒜 1 := by
    have h := hf 1 _ (gradeProj_mem 𝒜 1 x)
    rwa [add_zero] at h
  simp only [LinearMap.comp_apply, map_add]
  rw [parityMap_of_mem_zero 𝒜 h0, parityMap_of_mem_one 𝒜 h1,
    parityMap_of_mem_zero 𝒜 (gradeProj_mem 𝒜 0 x),
    parityMap_of_mem_one 𝒜 (gradeProj_mem 𝒜 1 x), map_neg]

theorem parityMap_comp_of_mem_one {f : Module.End K A}
    (hf : f ∈ endGrading 𝒜 1) :
    parityMap 𝒜 ∘ₗ f = -(f ∘ₗ parityMap 𝒜) := by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [← gradeProj_zero_add_gradeProj_one 𝒜 x]
  conv_rhs => rw [← gradeProj_zero_add_gradeProj_one 𝒜 x]
  have h0 : f (gradeProj 𝒜 0 x) ∈ 𝒜 1 := by
    have h := hf 0 _ (gradeProj_mem 𝒜 0 x)
    rwa [zero_add] at h
  have h1 : f (gradeProj 𝒜 1 x) ∈ 𝒜 0 := by
    have h := hf 1 _ (gradeProj_mem 𝒜 1 x)
    rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_add]
  rw [parityMap_of_mem_one 𝒜 h0, parityMap_of_mem_zero 𝒜 h1,
    parityMap_of_mem_zero 𝒜 (gradeProj_mem 𝒜 0 x),
    parityMap_of_mem_one 𝒜 (gradeProj_mem 𝒜 1 x), map_neg, neg_neg]

theorem parityMap_comp_parityMap :
    parityMap 𝒜 ∘ₗ parityMap 𝒜 = LinearMap.id :=
  LinearMap.ext fun x => parityMap_parityMap 𝒜 x

/-! ### Conjugation to the graded-tensor-product synonym -/

/-- Endomorphisms of `A ⊗[K] B`, transported to the graded tensor
product synonym (conjugation by `of`). -/
noncomputable def endConj :
    Module.End K (A ⊗[K] B) ≃ₐ[K] Module.End K (𝒜 ᵍ⊗[K] ℬ) :=
  AlgEquiv.ofLinearEquiv ((of K 𝒜 ℬ).conj)
    (by
      show (of K 𝒜 ℬ).conj 1 = 1
      exact LinearEquiv.conj_id _)
    (fun f g => by
      refine LinearMap.ext fun z => ?_
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, Module.End.mul_apply,
        LinearEquiv.symm_apply_apply])

theorem endConj_apply (h : Module.End K (A ⊗[K] B)) (z : 𝒜 ᵍ⊗[K] ℬ) :
    endConj 𝒜 ℬ h z = of K 𝒜 ℬ (h ((of K 𝒜 ℬ).symm z)) := rfl

private theorem endConj_uzsmul (u : ℤˣ) (h : Module.End K (A ⊗[K] B)) :
    endConj 𝒜 ℬ (u • h) = u • endConj 𝒜 ℬ h := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-! ### The two inclusions -/

/-- `f ↦ f ⊗ₗ id` as an algebra map `End A →ₐ End (A ⊗ B)`. -/
noncomputable def rTensorEndHom :
    Module.End K A →ₐ[K] Module.End K (A ⊗[K] B) :=
  AlgHom.ofLinearMap
    { toFun := fun f => TensorProduct.map f LinearMap.id
      map_add' := fun f f' => by
        refine TensorProduct.ext' fun x y => ?_
        simp [TensorProduct.add_tmul]
      map_smul' := fun c f => by
        refine TensorProduct.ext' fun x y => ?_
        simp [TensorProduct.smul_tmul'] }
    (by
      show TensorProduct.map (LinearMap.id : A →ₗ[K] A)
          (LinearMap.id : B →ₗ[K] B) = 1
      rw [TensorProduct.map_id, Module.End.one_eq_id])
    (fun f f' => by
      show TensorProduct.map (f ∘ₗ f') LinearMap.id
        = TensorProduct.map f LinearMap.id
          ∘ₗ TensorProduct.map f' LinearMap.id
      rw [← TensorProduct.map_comp, LinearMap.id_comp])

theorem rTensorEndHom_apply (f : Module.End K A) :
    (rTensorEndHom (K := K) (A := A) (B := B) f)
      = TensorProduct.map f LinearMap.id := rfl

/-- The raw signed right inclusion
`g ↦ id ⊗ₗ g₀ + J ⊗ₗ g₁` on `End (A ⊗ B)`. -/
noncomputable def signedLTensor (g : Module.End K B) :
    Module.End K (A ⊗[K] B) :=
  TensorProduct.map LinearMap.id (endMask ℬ 0 g)
    + TensorProduct.map (parityMap 𝒜) (endMask ℬ 1 g)

theorem signedLTensor_of_mem_zero {g : Module.End K B}
    (hg : g ∈ endGrading ℬ 0) :
    signedLTensor 𝒜 ℬ g = TensorProduct.map LinearMap.id g := by
  rw [signedLTensor, endMask_of_mem ℬ hg,
    endMask_of_mem_ne ℬ hg (by decide)]
  refine TensorProduct.ext' fun x y => ?_
  simp [TensorProduct.map_tmul]

theorem signedLTensor_of_mem_one {g : Module.End K B}
    (hg : g ∈ endGrading ℬ 1) :
    signedLTensor 𝒜 ℬ g = TensorProduct.map (parityMap 𝒜) g := by
  rw [signedLTensor, endMask_of_mem ℬ hg,
    endMask_of_mem_ne ℬ hg (by decide)]
  refine TensorProduct.ext' fun x y => ?_
  simp [TensorProduct.map_tmul]

private theorem signedLTensor_mul_of_mem {i j : ZMod 2}
    {g g' : Module.End K B} (hg : g ∈ endGrading ℬ i)
    (hg' : g' ∈ endGrading ℬ j) :
    signedLTensor 𝒜 ℬ (g * g')
      = signedLTensor 𝒜 ℬ g ∘ₗ signedLTensor 𝒜 ℬ g' := by
  have hmul : g * g' ∈ endGrading ℬ (i + j) :=
    SetLike.mul_mem_graded hg hg'
  have hcomp : (g * g' : Module.End K B) = g ∘ₗ g' := rfl
  rcases zmod2_cases i with hi | hi <;>
    rcases zmod2_cases j with hj | hj <;> subst hi <;> subst hj
  · rw [signedLTensor_of_mem_zero 𝒜 ℬ hg,
      signedLTensor_of_mem_zero 𝒜 ℬ hg',
      signedLTensor_of_mem_zero 𝒜 ℬ
        (by rwa [show (0 : ZMod 2) + 0 = 0 from by decide] at hmul),
      hcomp, ← TensorProduct.map_comp, LinearMap.id_comp]
  · rw [signedLTensor_of_mem_zero 𝒜 ℬ hg,
      signedLTensor_of_mem_one 𝒜 ℬ hg',
      signedLTensor_of_mem_one 𝒜 ℬ
        (by rwa [show (0 : ZMod 2) + 1 = 1 from by decide] at hmul),
      hcomp, ← TensorProduct.map_comp, LinearMap.id_comp]
  · rw [signedLTensor_of_mem_one 𝒜 ℬ hg,
      signedLTensor_of_mem_zero 𝒜 ℬ hg',
      signedLTensor_of_mem_one 𝒜 ℬ
        (by rwa [show (1 : ZMod 2) + 0 = 1 from by decide] at hmul),
      hcomp, ← TensorProduct.map_comp, LinearMap.comp_id]
  · rw [signedLTensor_of_mem_one 𝒜 ℬ hg,
      signedLTensor_of_mem_one 𝒜 ℬ hg',
      signedLTensor_of_mem_zero 𝒜 ℬ
        (by rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at hmul),
      hcomp, ← TensorProduct.map_comp, parityMap_comp_parityMap]

private theorem signedLTensor_add (g g' : Module.End K B) :
    signedLTensor 𝒜 ℬ (g + g')
      = signedLTensor 𝒜 ℬ g + signedLTensor 𝒜 ℬ g' := by
  rw [signedLTensor, signedLTensor, signedLTensor, map_add, map_add]
  refine TensorProduct.ext' fun x y => ?_
  simp only [LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.tmul_add]
  abel

/-- The signed right inclusion `End B →ₐ End (A ⊗ B)`:
`g ↦ id ⊗ₗ g₀ + J ⊗ₗ g₁`. -/
noncomputable def signedLTensorEndHom :
    Module.End K B →ₐ[K] Module.End K (A ⊗[K] B) :=
  AlgHom.ofLinearMap
    { toFun := signedLTensor 𝒜 ℬ
      map_add' := signedLTensor_add 𝒜 ℬ
      map_smul' := fun c g => by
        rw [RingHom.id_apply, signedLTensor, signedLTensor, map_smul,
          map_smul]
        refine TensorProduct.ext' fun x y => ?_
        simp only [LinearMap.add_apply, LinearMap.smul_apply,
          TensorProduct.map_tmul, LinearMap.id_apply,
          TensorProduct.tmul_smul, smul_add] }
    (by
      show signedLTensor 𝒜 ℬ 1 = 1
      rw [signedLTensor_of_mem_zero 𝒜 ℬ
        (SetLike.one_mem_graded (endGrading ℬ)),
        show ((1 : Module.End K B) : B →ₗ[K] B) = LinearMap.id from rfl,
        TensorProduct.map_id, Module.End.one_eq_id])
    (fun g g' => by
      show signedLTensor 𝒜 ℬ (g * g')
        = signedLTensor 𝒜 ℬ g ∘ₗ signedLTensor 𝒜 ℬ g'
      conv_lhs => rw [← endMask_zero_add_endMask_one ℬ g,
        ← endMask_zero_add_endMask_one ℬ g']
      conv_rhs => rw [← endMask_zero_add_endMask_one ℬ g,
        ← endMask_zero_add_endMask_one ℬ g']
      rw [add_mul, mul_add, mul_add, signedLTensor_add,
        signedLTensor_add, signedLTensor_add,
        signedLTensor_mul_of_mem 𝒜 ℬ (endMask_mem ℬ 0 g)
          (endMask_mem ℬ 0 g'),
        signedLTensor_mul_of_mem 𝒜 ℬ (endMask_mem ℬ 0 g)
          (endMask_mem ℬ 1 g'),
        signedLTensor_mul_of_mem 𝒜 ℬ (endMask_mem ℬ 1 g)
          (endMask_mem ℬ 0 g'),
        signedLTensor_mul_of_mem 𝒜 ℬ (endMask_mem ℬ 1 g)
          (endMask_mem ℬ 1 g'),
        signedLTensor_add, signedLTensor_add, LinearMap.add_comp,
        LinearMap.comp_add, LinearMap.comp_add])

theorem signedLTensorEndHom_apply (g : Module.End K B) :
    signedLTensorEndHom 𝒜 ℬ g = signedLTensor 𝒜 ℬ g := rfl

/-- The left inclusion into the graded synonym. -/
noncomputable def endInclLeft :
    Module.End K A →ₐ[K] Module.End K (𝒜 ᵍ⊗[K] ℬ) :=
  (endConj 𝒜 ℬ).toAlgHom.comp (rTensorEndHom (K := K) (A := A) (B := B))

/-- The signed right inclusion into the graded synonym. -/
noncomputable def endInclRight :
    Module.End K B →ₐ[K] Module.End K (𝒜 ᵍ⊗[K] ℬ) :=
  (endConj 𝒜 ℬ).toAlgHom.comp (signedLTensorEndHom 𝒜 ℬ)

theorem endInclLeft_tmul (f : Module.End K A) (x : A) (y : B) :
    endInclLeft 𝒜 ℬ f (x ᵍ⊗ₜ[K] y) = (f x) ᵍ⊗ₜ[K] y := rfl

theorem endInclRight_apply (g : Module.End K B) :
    endInclRight 𝒜 ℬ g = endConj 𝒜 ℬ (signedLTensor 𝒜 ℬ g) := rfl

/-! ### Anticommutation and the lift -/

private theorem endTensor_anticommutes :
    ∀ ⦃i j : ZMod 2⦄ (f : endGrading 𝒜 i) (g : endGrading ℬ j),
      endInclLeft 𝒜 ℬ f * endInclRight 𝒜 ℬ g
        = (-1 : ℤˣ) ^ (j * i) •
          (endInclRight 𝒜 ℬ g * endInclLeft 𝒜 ℬ f) := by
  intro i j f g
  have hL : ∀ (X Y : Module.End K (A ⊗[K] B)),
      endConj 𝒜 ℬ X * endConj 𝒜 ℬ Y = endConj 𝒜 ℬ (X ∘ₗ Y) := by
    intro X Y
    rw [← map_mul]
    rfl
  rw [show endInclLeft 𝒜 ℬ (f : Module.End K A)
      = endConj 𝒜 ℬ (TensorProduct.map (f : Module.End K A)
        LinearMap.id) from rfl,
    show endInclRight 𝒜 ℬ (g : Module.End K B)
      = endConj 𝒜 ℬ (signedLTensor 𝒜 ℬ (g : Module.End K B)) from rfl,
    hL, hL, ← endConj_uzsmul]
  refine congrArg (endConj 𝒜 ℬ) ?_
  rcases zmod2_cases j with hj | hj <;> subst hj
  · rw [signedLTensor_of_mem_zero 𝒜 ℬ g.2, ← TensorProduct.map_comp,
      ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
      LinearMap.id_comp, LinearMap.comp_id,
      show (0 : ZMod 2) * i = 0 from by rw [zero_mul],
      ← sgn_eq_neg_one_uzpow, sgn_zero, one_smul]
  · rw [signedLTensor_of_mem_one 𝒜 ℬ g.2, ← TensorProduct.map_comp,
      ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
    rcases zmod2_cases i with hi | hi <;> subst hi
    · rw [parityMap_comp_of_mem_zero 𝒜 f.2,
        show (1 : ZMod 2) * 0 = 0 from by rw [mul_zero],
        ← sgn_eq_neg_one_uzpow, sgn_zero, one_smul]
    · rw [parityMap_comp_of_mem_one 𝒜 f.2,
        show (1 : ZMod 2) * 1 = 1 from by rw [mul_one],
        ← sgn_eq_neg_one_uzpow]
      refine TensorProduct.ext' fun x y => ?_
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply,
        LinearMap.neg_apply, Units.smul_def,
        sgn_one, units_sign_eq, Units.val_neg, Units.val_one,
        neg_smul, one_smul, TensorProduct.neg_tmul, neg_neg]

/-- **The graded End-tensor map** (M7f-1f):
`End(A) ᵍ⊗ End(B) →ₐ End(A ᵍ⊗ B)` from the universal property on the
left inclusion and the signed right inclusion. -/
noncomputable def endTensorHom :
    ((endGrading 𝒜) ᵍ⊗[K] (endGrading ℬ)) →ₐ[K]
      Module.End K (𝒜 ᵍ⊗[K] ℬ) :=
  lift (endGrading 𝒜) (endGrading ℬ) (endInclLeft 𝒜 ℬ)
    (endInclRight 𝒜 ℬ) (endTensor_anticommutes 𝒜 ℬ)

theorem endTensorHom_tmul (f : Module.End K A) (g : Module.End K B) :
    endTensorHom 𝒜 ℬ (f ᵍ⊗ₜ[K] g)
      = endInclLeft 𝒜 ℬ f * endInclRight 𝒜 ℬ g :=
  lift_tmul (endGrading 𝒜) (endGrading ℬ) (endInclLeft 𝒜 ℬ)
    (endInclRight 𝒜 ℬ) (endTensor_anticommutes 𝒜 ℬ) f g

/-! ### Homogeneity -/

theorem endInclLeft_mem {i : ZMod 2} {f : Module.End K A}
    (hf : f ∈ endGrading 𝒜 i) :
    endInclLeft 𝒜 ℬ f ∈ endGrading (tensorGrading 𝒜 ℬ) i := by
  intro m z hz
  refine tensorGrading_induction 𝒜 ℬ hz
    (p := fun w => endInclLeft 𝒜 ℬ f w ∈ tensorGrading 𝒜 ℬ (m + i))
    ?_ ?_ ?_ ?_
  · intro k l x y hkl hx hy
    rw [endInclLeft_tmul]
    have h := tmul_mem_tensorGrading 𝒜 ℬ (hf k x hx) hy
    rwa [zmod2_endT_left, hkl] at h
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

theorem endInclRight_mem {j : ZMod 2} {g : Module.End K B}
    (hg : g ∈ endGrading ℬ j) :
    endInclRight 𝒜 ℬ g ∈ endGrading (tensorGrading 𝒜 ℬ) j := by
  intro m z hz
  refine tensorGrading_induction 𝒜 ℬ hz
    (p := fun w => endInclRight 𝒜 ℬ g w ∈ tensorGrading 𝒜 ℬ (m + j))
    ?_ ?_ ?_ ?_
  · intro k l x y hkl hx hy
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [endInclRight_apply, signedLTensor_of_mem_zero 𝒜 ℬ hg,
        show endConj 𝒜 ℬ (TensorProduct.map LinearMap.id g)
          (x ᵍ⊗ₜ[K] y) = x ᵍ⊗ₜ[K] (g y) from rfl]
      have h := tmul_mem_tensorGrading 𝒜 ℬ hx (hg l y hy)
      rwa [zmod2_endT_right, hkl] at h
    · rw [endInclRight_apply, signedLTensor_of_mem_one 𝒜 ℬ hg,
        show endConj 𝒜 ℬ (TensorProduct.map (parityMap 𝒜) g)
          (x ᵍ⊗ₜ[K] y) = (parityMap 𝒜 x) ᵍ⊗ₜ[K] (g y) from rfl]
      have h := tmul_mem_tensorGrading 𝒜 ℬ (parityMap_mem 𝒜 hx)
        (hg l y hy)
      rwa [zmod2_endT_right, hkl] at h
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

theorem endTensorHom_isHomogeneous :
    IsHomogeneousHom (tensorGrading (endGrading 𝒜) (endGrading ℬ))
      (endGrading (tensorGrading 𝒜 ℬ)) (endTensorHom 𝒜 ℬ) := by
  intro i z hz
  refine tensorGrading_induction (endGrading 𝒜) (endGrading ℬ) hz
    (p := fun w => endTensorHom 𝒜 ℬ w
      ∈ endGrading (tensorGrading 𝒜 ℬ) i)
    ?_ ?_ ?_ ?_
  · intro j k f g hjk hf hg
    rw [endTensorHom_tmul]
    exact hjk ▸ SetLike.mul_mem_graded (endInclLeft_mem 𝒜 ℬ hf)
      (endInclRight_mem 𝒜 ℬ hg)
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-! ### Bijectivity (M7f-1f part ii)

The underlying linear map of `endTensorHom` factors as mathlib's
`homTensorHomEquiv` composed with the involutive twist
`Θ (f ⊗ g) = f ⊗ g₀ + (f∘J) ⊗ g₁` — so bijectivity in the free/finite
case needs no simplicity argument at all. -/

/-- Postcomposition with the parity involution, as a linear map on
endomorphisms. -/
private noncomputable def compJRight :
    Module.End K A →ₗ[K] Module.End K A where
  toFun f := f ∘ₗ parityMap 𝒜
  map_add' _ _ := LinearMap.add_comp _ _ _
  map_smul' c f := LinearMap.smul_comp c f _

private theorem compJRight_apply (f : Module.End K A) :
    compJRight 𝒜 f = f ∘ₗ parityMap 𝒜 := rfl

/-- The involutive twist relating `endTensorHom` to the unsigned
hom-tensor-hom map. -/
noncomputable def endTwist :
    (Module.End K A ⊗[K] Module.End K B) →ₗ[K]
      (Module.End K A ⊗[K] Module.End K B) :=
  TensorProduct.map LinearMap.id (endMask ℬ 0)
    + TensorProduct.map (compJRight 𝒜) (endMask ℬ 1)

theorem endTwist_tmul (f : Module.End K A) (g : Module.End K B) :
    endTwist 𝒜 ℬ (f ⊗ₜ[K] g)
      = f ⊗ₜ[K] (endMask ℬ 0 g)
        + (f ∘ₗ parityMap 𝒜) ⊗ₜ[K] (endMask ℬ 1 g) := by
  rw [endTwist, LinearMap.add_apply, TensorProduct.map_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply, compJRight_apply]

/-- The twist is an involution — mask idempotence plus `J² = id`. -/
theorem endTwist_endTwist (t : Module.End K A ⊗[K] Module.End K B) :
    endTwist 𝒜 ℬ (endTwist 𝒜 ℬ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul f g =>
      rw [endTwist_tmul, map_add, endTwist_tmul, endTwist_tmul,
        endMask_of_mem ℬ (endMask_mem ℬ 0 g),
        endMask_of_mem_ne ℬ (endMask_mem ℬ 0 g) (by decide),
        endMask_of_mem_ne ℬ (endMask_mem ℬ 1 g) (by decide),
        endMask_of_mem ℬ (endMask_mem ℬ 1 g),
        show (f ∘ₗ parityMap 𝒜) ∘ₗ parityMap 𝒜 = f from by
          rw [LinearMap.comp_assoc, parityMap_comp_parityMap,
            LinearMap.comp_id]]
      simp only [TensorProduct.tmul_zero, add_zero, zero_add,
        ← TensorProduct.tmul_add, endMask_zero_add_endMask_one]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

theorem endTwist_bijective : Function.Bijective (endTwist 𝒜 ℬ) :=
  ⟨Function.LeftInverse.injective (g := endTwist 𝒜 ℬ)
      (endTwist_endTwist 𝒜 ℬ),
    Function.RightInverse.surjective (endTwist_endTwist 𝒜 ℬ)⟩

variable [Module.Free K A] [Module.Finite K A]
variable [Module.Free K B] [Module.Finite K B]

/-- The factorization: `endTensorHom` is the (conjugated) unsigned
hom-tensor-hom map composed with the involutive twist. -/
private theorem endTensorHom_factor (z) :
    endTensorHom 𝒜 ℬ z
      = endConj 𝒜 ℬ (homTensorHomEquiv K A B A B
          (endTwist 𝒜 ℬ
            ((of K (endGrading 𝒜) (endGrading ℬ)).symm z))) := by
  have key : ∀ t : Module.End K A ⊗[K] Module.End K B,
      endTensorHom 𝒜 ℬ (of K (endGrading 𝒜) (endGrading ℬ) t)
        = endConj 𝒜 ℬ (homTensorHomEquiv K A B A B
            (endTwist 𝒜 ℬ t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
        show endTensorHom 𝒜 ℬ 0 = endConj 𝒜 ℬ (homTensorHomEquiv K A B A B 0)
        rw [map_zero, map_zero, map_zero]
    | tmul f g =>
        have hmul : endInclLeft 𝒜 ℬ f * endInclRight 𝒜 ℬ g
            = endConj 𝒜 ℬ (TensorProduct.map f LinearMap.id
              ∘ₗ signedLTensor 𝒜 ℬ g) := by
          show endConj 𝒜 ℬ (TensorProduct.map f LinearMap.id)
              * endConj 𝒜 ℬ (signedLTensor 𝒜 ℬ g)
            = endConj 𝒜 ℬ (TensorProduct.map f LinearMap.id
              ∘ₗ signedLTensor 𝒜 ℬ g)
          rw [← map_mul]; rfl
        have hcomp : TensorProduct.map f LinearMap.id ∘ₗ signedLTensor 𝒜 ℬ g
            = TensorProduct.map f ((endMask ℬ 0) g)
              + TensorProduct.map (f ∘ₗ parityMap 𝒜) ((endMask ℬ 1) g) := by
          rw [signedLTensor, LinearMap.comp_add, ← TensorProduct.map_comp,
            ← TensorProduct.map_comp]
          simp only [LinearMap.comp_id, LinearMap.id_comp]
        show endTensorHom 𝒜 ℬ (f ᵍ⊗ₜ[K] g)
            = endConj 𝒜 ℬ (homTensorHomEquiv K A B A B (endTwist 𝒜 ℬ (f ⊗ₜ[K] g)))
        rw [endTensorHom_tmul, hmul, hcomp, endTwist_tmul]
        rw [show homTensorHomEquiv K A B A B
              (f ⊗ₜ[K] (endMask ℬ 0) g + (f ∘ₗ parityMap 𝒜) ⊗ₜ[K] (endMask ℬ 1) g)
            = TensorProduct.map f ((endMask ℬ 0) g)
              + TensorProduct.map (f ∘ₗ parityMap 𝒜) ((endMask ℬ 1) g) from by
          rw [map_add, homTensorHomEquiv_apply, homTensorHomEquiv_apply,
            homTensorHomMap_apply, homTensorHomMap_apply]]
    | add u v hu hv =>
        show endTensorHom 𝒜 ℬ (of K (endGrading 𝒜) (endGrading ℬ) u
            + of K (endGrading 𝒜) (endGrading ℬ) v)
          = endConj 𝒜 ℬ (homTensorHomEquiv K A B A B (endTwist 𝒜 ℬ (u + v)))
        rw [map_add, map_add, hu, hv, map_add, map_add]
  have h := key ((of K (endGrading 𝒜) (endGrading ℬ)).symm z)
  rwa [symm_of_of] at h

theorem endTensorHom_bijective :
    Function.Bijective (endTensorHom 𝒜 ℬ) := by
  have hcomp : ⇑(endTensorHom 𝒜 ℬ)
      = ⇑(endConj 𝒜 ℬ) ∘ ⇑(homTensorHomEquiv K A B A B)
        ∘ ⇑(endTwist 𝒜 ℬ)
        ∘ ⇑(of K (endGrading 𝒜) (endGrading ℬ)).symm :=
    funext (endTensorHom_factor 𝒜 ℬ)
  rw [hcomp]
  exact (endConj 𝒜 ℬ).bijective.comp
    ((homTensorHomEquiv K A B A B).bijective.comp
      ((endTwist_bijective 𝒜 ℬ).comp
        (of K (endGrading 𝒜) (endGrading ℬ)).symm.bijective))

/-- **The graded End-tensor equivalence** (M7f-1f):
`End(A) ᵍ⊗ End(B) ≃ₐ End(A ᵍ⊗ B)` for finite free modules. -/
noncomputable def endTensorEquiv :
    ((endGrading 𝒜) ᵍ⊗[K] (endGrading ℬ)) ≃ₐ[K]
      Module.End K (𝒜 ᵍ⊗[K] ℬ) :=
  AlgEquiv.ofBijective (endTensorHom 𝒜 ℬ) (endTensorHom_bijective 𝒜 ℬ)

/-- The End-tensor map carries the tensor grading of the End gradings
**onto** the End grading of the tensor grading. -/
theorem endTensorHom_map_grading (i : ZMod 2) :
    (tensorGrading (endGrading 𝒜) (endGrading ℬ) i).map
        (endTensorHom 𝒜 ℬ).toLinearMap
      = endGrading (tensorGrading 𝒜 ℬ) i :=
  map_grading_of_bijective
    (tensorGrading (endGrading 𝒜) (endGrading ℬ))
    (endGrading (tensorGrading 𝒜 ℬ)) (endTensorHom 𝒜 ℬ)
    (endTensorHom_isHomogeneous 𝒜 ℬ) (endTensorHom_bijective 𝒜 ℬ) i

end Superfusion

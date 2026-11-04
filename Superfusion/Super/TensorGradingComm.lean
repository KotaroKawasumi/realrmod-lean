/-
Superfusion / Super / TensorGradingComm

Milestone M7f-1g: **the braiding carries the grading, and the
middle-four interchange** —

  `gmiddleFour : (𝒜 ᵍ⊗ ℬ) ᵍ⊗ (𝒞 ᵍ⊗ 𝒟) ≃ₐ (𝒜 ᵍ⊗ 𝒞) ᵍ⊗ (ℬ ᵍ⊗ 𝒟)`,
  `(a ᵍ⊗ b) ᵍ⊗ (c ᵍ⊗ d) ↦ (-1)^{|b||c|} (a ᵍ⊗ c) ᵍ⊗ (b ᵍ⊗ d)`,

assembled from the associator (M7f-1c) and mathlib's Koszul braiding
`GradedTensorProduct.comm`, which we show carries `tensorGrading`
onto `tensorGrading` (`comm_map_grading`).  Together with the
grading-transport helpers `map_grading_symm`/`map_grading_trans`,
this is the final reshuffling piece for the Wall-map factorization
(M7f-2):

  `(A ᵍ⊗ B) ᵍ⊗ (A ᵍ⊗ B)ˢᵒᵖ ≅ (A ᵍ⊗ Aˢᵒᵖ) ᵍ⊗ (B ᵍ⊗ Bˢᵒᵖ)`.
-/
import Superfusion.Super.TensorGradingAssoc

namespace Superfusion

open TensorProduct
open GradedTensorProduct

/-! ### Grading-transport helpers for equivalence composites -/

section Transport

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {C : Type*} [Ring C] [Algebra K C]

/-- Gradings transported by an equivalence come back under the
inverse. -/
theorem map_grading_symm (𝒜 : ZMod 2 → Submodule K A)
    (ℬ : ZMod 2 → Submodule K B) (e : A ≃ₐ[K] B)
    (he : ∀ i, (𝒜 i).map e.toLinearMap = ℬ i) (i : ZMod 2) :
    (ℬ i).map e.symm.toLinearMap = 𝒜 i := by
  rw [← he i, ← Submodule.map_comp]
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp
  rw [h, Submodule.map_id]

/-- Gradings transported along a composite of equivalences. -/
theorem map_grading_trans (𝒜 : ZMod 2 → Submodule K A)
    (ℬ : ZMod 2 → Submodule K B) (𝒞 : ZMod 2 → Submodule K C)
    (e : A ≃ₐ[K] B) (f : B ≃ₐ[K] C)
    (he : ∀ i, (𝒜 i).map e.toLinearMap = ℬ i)
    (hf : ∀ i, (ℬ i).map f.toLinearMap = 𝒞 i) (i : ZMod 2) :
    (𝒜 i).map (e.trans f).toLinearMap = 𝒞 i := by
  rw [show (e.trans f).toLinearMap
      = f.toLinearMap.comp e.toLinearMap from rfl,
    Submodule.map_comp, he, hf]

private theorem algEquiv_uzsmul {e : A ≃ₐ[K] B} (u : ℤˣ) (x : A) :
    e (u • x) = u • e x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

end Transport

/-! ### The braiding carries the grading -/

section Comm

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

theorem comm_isHomogeneous :
    IsHomogeneousHom (tensorGrading 𝒜 ℬ) (tensorGrading ℬ 𝒜)
      (comm 𝒜 ℬ).toAlgHom := by
  intro i z hz
  refine tensorGrading_induction 𝒜 ℬ hz
    (p := fun w => comm 𝒜 ℬ w ∈ tensorGrading ℬ 𝒜 i) ?_ ?_ ?_ ?_
  · intro j k x y hjk hx hy
    rw [show (x ᵍ⊗ₜ[K] y)
        = (((⟨x, hx⟩ : 𝒜 j) : A)) ᵍ⊗ₜ[K] (((⟨y, hy⟩ : ℬ k) : B))
        from rfl,
      comm_coe_tmul_coe, Units.smul_def]
    refine zsmul_mem ?_ _
    have h := tmul_mem_tensorGrading ℬ 𝒜 hy hx
    rwa [show k + j = j + k from add_comm k j, hjk] at h
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- The Koszul braiding carries the tensor grading **onto** the
tensor grading. -/
theorem comm_map_grading (i : ZMod 2) :
    (tensorGrading 𝒜 ℬ i).map (comm 𝒜 ℬ).toLinearMap
      = tensorGrading ℬ 𝒜 i :=
  map_grading_of_bijective (tensorGrading 𝒜 ℬ) (tensorGrading ℬ 𝒜)
    (comm 𝒜 ℬ).toAlgHom (comm_isHomogeneous 𝒜 ℬ)
    (comm 𝒜 ℬ).bijective i

end Comm

/-! ### The middle-four interchange -/

section MiddleFour

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {C : Type*} [Ring C] [Algebra K C]
variable {D : Type*} [Ring D] [Algebra K D]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable (𝒞 : ZMod 2 → Submodule K C) (𝒟 : ZMod 2 → Submodule K D)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

private theorem gassoc_symm_tmul (a : A) (b : B) (c : C) :
    (gassoc 𝒜 ℬ 𝒞).symm (a ᵍ⊗ₜ[K] (b ᵍ⊗ₜ[K] c))
      = (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c := by
  rw [← gassoc_tmul 𝒜 ℬ 𝒞 a b c, AlgEquiv.symm_apply_apply]

private theorem uzsmul_gtmul (u : ℤˣ) (x : A) (y : B) :
    ((u • x) ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] ℬ) = u • (x ᵍ⊗ₜ[K] y) := by
  rw [Units.smul_def, Units.smul_def,
    show ((((u : ℤ) • x) ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] ℬ))
      = of K 𝒜 ℬ (((u : ℤ) • x) ⊗ₜ[K] y) from rfl,
    show (((u : ℤ) • x) ⊗ₜ[K] y : A ⊗[K] B) = (u : ℤ) • (x ⊗ₜ[K] y) from
      (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

private theorem gtmul_uzsmul (u : ℤˣ) (x : A) (y : B) :
    (x ᵍ⊗ₜ[K] (u • y) : 𝒜 ᵍ⊗[K] ℬ) = u • (x ᵍ⊗ₜ[K] y) := by
  rw [Units.smul_def, Units.smul_def,
    show ((x ᵍ⊗ₜ[K] ((u : ℤ) • y) : 𝒜 ᵍ⊗[K] ℬ))
      = of K 𝒜 ℬ (x ⊗ₜ[K] ((u : ℤ) • y)) from rfl,
    show (x ⊗ₜ[K] ((u : ℤ) • y) : A ⊗[K] B) = (u : ℤ) • (x ⊗ₜ[K] y) from by
      rw [← TensorProduct.smul_tmul]; exact (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

/-- Swap the first two factors of `ℬ ᵍ⊗ (𝒞 ᵍ⊗ 𝒟)`. -/
noncomputable def gswapBC :
    (ℬ ᵍ⊗[K] tensorGrading 𝒞 𝒟) ≃ₐ[K]
      (𝒞 ᵍ⊗[K] tensorGrading ℬ 𝒟) :=
  ((gassoc ℬ 𝒞 𝒟).symm).trans <|
    (gcongr (tensorGrading ℬ 𝒞) 𝒟 (tensorGrading 𝒞 ℬ) 𝒟
        (comm ℬ 𝒞) (AlgEquiv.refl)
        (comm_map_grading ℬ 𝒞) (fun _ => Submodule.map_id _)).trans
      (gassoc 𝒞 ℬ 𝒟)

theorem gswapBC_map_grading (i : ZMod 2) :
    (tensorGrading ℬ (tensorGrading 𝒞 𝒟) i).map
        (gswapBC ℬ 𝒞 𝒟).toLinearMap
      = tensorGrading 𝒞 (tensorGrading ℬ 𝒟) i := by
  refine map_grading_trans _ _ _ _ _
    (map_grading_symm _ _ (gassoc ℬ 𝒞 𝒟) (gassoc_map_grading ℬ 𝒞 𝒟))
    (map_grading_trans _ _ _ _ _
      (gcongr_map_grading (tensorGrading ℬ 𝒞) 𝒟 (tensorGrading 𝒞 ℬ) 𝒟
        (comm ℬ 𝒞) (AlgEquiv.refl) (comm_map_grading ℬ 𝒞)
        (fun _ => Submodule.map_id _))
      (gassoc_map_grading 𝒞 ℬ 𝒟)) i

theorem gswapBC_tmul {j k : ZMod 2} {b : B} {c : C} (d : D)
    (hb : b ∈ ℬ j) (hc : c ∈ 𝒞 k) :
    gswapBC ℬ 𝒞 𝒟 (b ᵍ⊗ₜ[K] (c ᵍ⊗ₜ[K] d))
      = (-1 : ℤˣ) ^ (k * j) • (c ᵍ⊗ₜ[K] (b ᵍ⊗ₜ[K] d)) := by
  rw [gswapBC, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    gassoc_symm_tmul,
    gcongr_tmul (tensorGrading ℬ 𝒞) 𝒟 (tensorGrading 𝒞 ℬ) 𝒟
      (comm ℬ 𝒞) (AlgEquiv.refl) (comm_map_grading ℬ 𝒞)
      (fun _ => Submodule.map_id _),
    AlgEquiv.coe_refl, id_eq,
    show comm ℬ 𝒞 (b ᵍ⊗ₜ[K] c)
      = comm ℬ 𝒞 ((((⟨b, hb⟩ : ℬ j) : B)) ᵍ⊗ₜ[K]
          (((⟨c, hc⟩ : 𝒞 k) : C))) from rfl,
    comm_coe_tmul_coe, uzsmul_gtmul, algEquiv_uzsmul,
    gassoc_tmul]

/-- **The middle-four interchange** (M7f-1g):
`(𝒜 ᵍ⊗ ℬ) ᵍ⊗ (𝒞 ᵍ⊗ 𝒟) ≃ₐ (𝒜 ᵍ⊗ 𝒞) ᵍ⊗ (ℬ ᵍ⊗ 𝒟)` as graded
algebras. -/
noncomputable def gmiddleFour :
    ((tensorGrading 𝒜 ℬ) ᵍ⊗[K] (tensorGrading 𝒞 𝒟)) ≃ₐ[K]
      ((tensorGrading 𝒜 𝒞) ᵍ⊗[K] (tensorGrading ℬ 𝒟)) :=
  (gassoc 𝒜 ℬ (tensorGrading 𝒞 𝒟)).trans <|
    (gcongr 𝒜 (tensorGrading ℬ (tensorGrading 𝒞 𝒟))
        𝒜 (tensorGrading 𝒞 (tensorGrading ℬ 𝒟))
        (AlgEquiv.refl) (gswapBC ℬ 𝒞 𝒟)
        (fun _ => Submodule.map_id _)
        (gswapBC_map_grading ℬ 𝒞 𝒟)).trans
      (gassoc 𝒜 𝒞 (tensorGrading ℬ 𝒟)).symm

theorem gmiddleFour_map_grading (i : ZMod 2) :
    (tensorGrading (tensorGrading 𝒜 ℬ) (tensorGrading 𝒞 𝒟) i).map
        (gmiddleFour 𝒜 ℬ 𝒞 𝒟).toLinearMap
      = tensorGrading (tensorGrading 𝒜 𝒞) (tensorGrading ℬ 𝒟) i := by
  refine map_grading_trans _ _ _ _ _
    (gassoc_map_grading 𝒜 ℬ (tensorGrading 𝒞 𝒟))
    (map_grading_trans _ _ _ _ _
      (gcongr_map_grading 𝒜 (tensorGrading ℬ (tensorGrading 𝒞 𝒟))
        𝒜 (tensorGrading 𝒞 (tensorGrading ℬ 𝒟))
        (AlgEquiv.refl) (gswapBC ℬ 𝒞 𝒟)
        (fun _ => Submodule.map_id _) (gswapBC_map_grading ℬ 𝒞 𝒟))
      (map_grading_symm _ _ (gassoc 𝒜 𝒞 (tensorGrading ℬ 𝒟))
        (gassoc_map_grading 𝒜 𝒞 (tensorGrading ℬ 𝒟)))) i

/-- The middle-four interchange on pure tensors with homogeneous
middle pair: the Koszul sign is `(-1)^{|b||c|}`. -/
theorem gmiddleFour_tmul {j k : ZMod 2} (a : A) {b : B} {c : C}
    (d : D) (hb : b ∈ ℬ j) (hc : c ∈ 𝒞 k) :
    gmiddleFour 𝒜 ℬ 𝒞 𝒟 ((a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] (c ᵍ⊗ₜ[K] d))
      = (-1 : ℤˣ) ^ (k * j) •
        ((a ᵍ⊗ₜ[K] c) ᵍ⊗ₜ[K] (b ᵍ⊗ₜ[K] d)) := by
  rw [gmiddleFour, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    gassoc_tmul,
    gcongr_tmul 𝒜 (tensorGrading ℬ (tensorGrading 𝒞 𝒟))
      𝒜 (tensorGrading 𝒞 (tensorGrading ℬ 𝒟))
      (AlgEquiv.refl) (gswapBC ℬ 𝒞 𝒟)
      (fun _ => Submodule.map_id _) (gswapBC_map_grading ℬ 𝒞 𝒟),
    AlgEquiv.coe_refl, id_eq, gswapBC_tmul ℬ 𝒞 𝒟 d hb hc,
    gtmul_uzsmul, algEquiv_uzsmul, gassoc_symm_tmul]

end MiddleFour

end Superfusion

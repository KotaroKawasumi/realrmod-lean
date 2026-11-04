/-
Superfusion / Super / TensorGradingMap

Milestone M7f-1b: **functoriality of the graded tensor product** in
homogeneous algebra maps —

  `gmap φ ψ : 𝒜 ᵍ⊗[K] ℬ →ₐ[K] 𝒜' ᵍ⊗[K] ℬ'`,
  `gmap φ ψ (a ᵍ⊗ₜ b) = φ a ᵍ⊗ₜ ψ b`,

homogeneous for the M7f-1a gradings; for graded equivalences this is
a graded equivalence (`gcongr`, `gcongr_map_grading`).  Also missing
from mathlib alongside the grading itself.

Validation: the M7c-3 identification
`equivGradedTensor : 𝒜 ᵍ⊗ AdjoinOdd ε ≃ₐ OddDouble 𝒜 ε` carries
`tensorGrading` **onto** the `OddDouble` grading
(`equivGradedTensor_map_grading`) — the explicit model used to build
the division tower and the general grading of M7f-1a agree, so the
tower is an iterated graded tensor product *as a graded algebra*.
-/
import Superfusion.Super.TensorGrading
import Superfusion.Super.GradedTransfer
import Superfusion.Super.OddDoubleTensor
import Superfusion.Super.SkolemNoether

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section Map

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {A' : Type*} [Ring A'] [Algebra K A']
variable {B' : Type*} [Ring B'] [Algebra K B']
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable (𝒜' : ZMod 2 → Submodule K A') (ℬ' : ZMod 2 → Submodule K B')
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable [GradedAlgebra 𝒜'] [GradedAlgebra ℬ']

/-- Algebra maps out of a graded tensor product agree once they agree
on the pure tensors. -/
theorem galgHom_ext {C : Type*} [Ring C] [Algebra K C]
    ⦃F G : (𝒜 ᵍ⊗[K] ℬ) →ₐ[K] C⦄
    (h : ∀ (a : A) (b : B), F (a ᵍ⊗ₜ[K] b) = G (a ᵍ⊗ₜ[K] b)) :
    F = G := by
  apply AlgHom.toLinearMap_injective
  refine LinearMap.ext fun z => ?_
  have h2 : F.toLinearMap ∘ₗ (of K 𝒜 ℬ).toLinearMap
      = G.toLinearMap ∘ₗ (of K 𝒜 ℬ).toLinearMap :=
    TensorProduct.ext' fun a b => h a b
  have h3 := LinearMap.congr_fun h2 ((of K 𝒜 ℬ).symm z)
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, symm_of_of] at h3
  exact h3

variable (φ : A →ₐ[K] A') (ψ : B →ₐ[K] B')
variable (hφ : IsHomogeneousHom 𝒜 𝒜' φ) (hψ : IsHomogeneousHom ℬ ℬ' ψ)

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
include hφ hψ in
private theorem gmap_anticommutes : ∀ ⦃i j : ZMod 2⦄ (a : 𝒜 i) (b : ℬ j),
    ((includeLeft 𝒜' ℬ').comp φ) a * ((includeRight 𝒜' ℬ').comp ψ) b
      = (-1 : ℤˣ) ^ (j * i) •
        (((includeRight 𝒜' ℬ').comp ψ) b
          * ((includeLeft 𝒜' ℬ').comp φ) a) := by
  intro i j a b
  simp only [AlgHom.comp_apply]
  rw [show includeLeft 𝒜' ℬ' (φ a) = φ (a : A) ᵍ⊗ₜ[K] (1 : B') from rfl,
    show includeRight 𝒜' ℬ' (ψ b) = (1 : A') ᵍ⊗ₜ[K] ψ (b : B) from rfl,
    tmul_one_mul_one_tmul,
    show ((1 : A') ᵍ⊗ₜ[K] ψ (b : B)) * (φ (a : A) ᵍ⊗ₜ[K] (1 : B'))
      = ((1 : A') ᵍ⊗ₜ[K] ((⟨ψ b, hψ j b b.2⟩ : ℬ' j) : B'))
        * ((((⟨φ a, hφ i a a.2⟩ : 𝒜' i) : A')) ᵍ⊗ₜ[K] (1 : B'))
      from rfl,
    tmul_coe_mul_coe_tmul, smul_smul, Int.units_mul_self, one_smul,
    one_mul, mul_one]

/-- Functoriality of the graded tensor product in homogeneous algebra
maps: `gmap φ ψ (a ᵍ⊗ₜ b) = φ a ᵍ⊗ₜ ψ b`. -/
noncomputable def gmap : (𝒜 ᵍ⊗[K] ℬ) →ₐ[K] (𝒜' ᵍ⊗[K] ℬ') :=
  lift 𝒜 ℬ ((includeLeft 𝒜' ℬ').comp φ) ((includeRight 𝒜' ℬ').comp ψ)
    (gmap_anticommutes 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ)

@[simp] theorem gmap_tmul (a : A) (b : B) :
    gmap 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ (a ᵍ⊗ₜ[K] b) = φ a ᵍ⊗ₜ[K] ψ b := by
  rw [gmap, lift_tmul]
  simp only [AlgHom.comp_apply]
  exact tmul_one_mul_one_tmul 𝒜' ℬ' (φ a) (ψ b)

include hφ hψ in
theorem gmap_isHomogeneous :
    IsHomogeneousHom (tensorGrading 𝒜 ℬ) (tensorGrading 𝒜' ℬ')
      (gmap 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ) := by
  intro i z hz
  refine tensorGrading_induction 𝒜 ℬ hz
    (p := fun w =>
      gmap 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ w ∈ tensorGrading 𝒜' ℬ' i)
    ?_ ?_ ?_ ?_
  · intro j k x y hjk hx hy
    rw [gmap_tmul]
    have h := tmul_mem_tensorGrading 𝒜' ℬ' (hφ j x hx) (hψ k y hy)
    rwa [hjk] at h
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

end Map

/-! ### Graded equivalences -/

section Congr

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {A' : Type*} [Ring A'] [Algebra K A']
variable {B' : Type*} [Ring B'] [Algebra K B']
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable (𝒜' : ZMod 2 → Submodule K A') (ℬ' : ZMod 2 → Submodule K B')
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable [GradedAlgebra 𝒜'] [GradedAlgebra ℬ']
variable (φ : A ≃ₐ[K] A') (ψ : B ≃ₐ[K] B')
variable (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = 𝒜' i)
variable (hψ : ∀ i, (ℬ i).map ψ.toLinearMap = ℬ' i)

omit [GradedAlgebra 𝒜] [GradedAlgebra 𝒜'] in
include hφ in
private theorem congr_hom_fwd : IsHomogeneousHom 𝒜 𝒜' φ.toAlgHom :=
  fun _ _ hx => (mem_iff_map_mem 𝒜 𝒜' φ hφ).mp hx

omit [GradedAlgebra 𝒜] [GradedAlgebra 𝒜'] in
include hφ in
private theorem congr_hom_bwd : IsHomogeneousHom 𝒜' 𝒜 φ.symm.toAlgHom :=
  fun i x hx => (mem_iff_map_mem 𝒜 𝒜' φ hφ (i := i)
    (x := φ.symm x)).mpr (by rwa [AlgEquiv.apply_symm_apply])

/-- The graded tensor product of two graded equivalences. -/
noncomputable def gcongr : (𝒜 ᵍ⊗[K] ℬ) ≃ₐ[K] (𝒜' ᵍ⊗[K] ℬ') :=
  AlgEquiv.ofAlgHom
    (gmap 𝒜 ℬ 𝒜' ℬ' φ.toAlgHom ψ.toAlgHom
      (congr_hom_fwd 𝒜 𝒜' φ hφ) (congr_hom_fwd ℬ ℬ' ψ hψ))
    (gmap 𝒜' ℬ' 𝒜 ℬ φ.symm.toAlgHom ψ.symm.toAlgHom
      (congr_hom_bwd 𝒜 𝒜' φ hφ) (congr_hom_bwd ℬ ℬ' ψ hψ))
    (galgHom_ext 𝒜' ℬ' fun a b => by
      simp only [AlgHom.comp_apply, gmap_tmul, AlgHom.id_apply,
        AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply])
    (galgHom_ext 𝒜 ℬ fun a b => by
      simp only [AlgHom.comp_apply, gmap_tmul, AlgHom.id_apply,
        AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply])

@[simp] theorem gcongr_tmul (a : A) (b : B) :
    gcongr 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ (a ᵍ⊗ₜ[K] b) = φ a ᵍ⊗ₜ[K] ψ b :=
  gmap_tmul 𝒜 ℬ 𝒜' ℬ' φ.toAlgHom ψ.toAlgHom
    (congr_hom_fwd 𝒜 𝒜' φ hφ) (congr_hom_fwd ℬ ℬ' ψ hψ) a b

include hφ hψ in
/-- The graded tensor product of graded equivalences carries the
tensor grading **onto** the tensor grading. -/
theorem gcongr_map_grading (i : ZMod 2) :
    (tensorGrading 𝒜 ℬ i).map
        (gcongr 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ).toLinearMap
      = tensorGrading 𝒜' ℬ' i :=
  map_grading_of_bijective (tensorGrading 𝒜 ℬ) (tensorGrading 𝒜' ℬ')
    (gcongr 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ).toAlgHom
    (gmap_isHomogeneous 𝒜 ℬ 𝒜' ℬ' φ.toAlgHom ψ.toAlgHom
      (congr_hom_fwd 𝒜 𝒜' φ hφ) (congr_hom_fwd ℬ ℬ' ψ hψ))
    (gcongr 𝒜 ℬ 𝒜' ℬ' φ ψ hφ hψ).bijective i

end Congr

/-! ### Validation against the explicit model (M7c-3) -/

section Validate

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K)

theorem equivGradedTensor_isHomogeneous :
    IsHomogeneousHom (tensorGrading 𝒜 (AdjoinOdd.grading ε))
      (OddDouble.grading 𝒜 ε)
      (OddDouble.equivGradedTensor 𝒜 ε).toAlgHom := by
  intro i z hz
  refine tensorGrading_induction 𝒜 (AdjoinOdd.grading ε) hz
    (p := fun w =>
      (OddDouble.equivGradedTensor 𝒜 ε) w ∈ OddDouble.grading 𝒜 ε i)
    ?_ ?_ ?_ ?_
  · intro j k x y hjk hx hy
    have h := OddDouble.equivGradedTensor_tmul_mem 𝒜 ε hx hy
    rwa [hjk] at h
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- The explicit model and the general grading agree: the M7c-3
identification carries `tensorGrading` **onto** the `OddDouble`
grading, so the division tower is an iterated graded tensor product
as a *graded* algebra. -/
theorem equivGradedTensor_map_grading (i : ZMod 2) :
    (tensorGrading 𝒜 (AdjoinOdd.grading ε) i).map
        (OddDouble.equivGradedTensor 𝒜 ε).toLinearMap
      = OddDouble.grading 𝒜 ε i :=
  map_grading_of_bijective (tensorGrading 𝒜 (AdjoinOdd.grading ε))
    (OddDouble.grading 𝒜 ε) (OddDouble.equivGradedTensor 𝒜 ε).toAlgHom
    (equivGradedTensor_isHomogeneous 𝒜 ε)
    (OddDouble.equivGradedTensor 𝒜 ε).bijective i

end Validate

end Superfusion

/-
Superfusion / Super / TensorGradingAssoc

Milestone M7f-1c: **associativity of the graded tensor product** as a
graded algebra equivalence —

  `gassoc : (𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞 ≃ₐ 𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞)`,
  `(a ᵍ⊗ b) ᵍ⊗ c ↦ a ᵍ⊗ (b ᵍ⊗ c)`,

missing from mathlib (the nested gradings only exist thanks to
M7f-1a).  The map has no Koszul sign: the two reassociation signs
agree.  Everything reduces to a single **inclusion commutation** lemma
(`includeRight_mul_includeLeft`, an instance of the homogeneous
multiplication formula): the anticommutation hypothesis of `lift` uses
it twice per side and the accumulated signs cancel by a `∀`-closed
`sgn` identity checked by `decide`; the composite identities are
nested `galgHom_ext` computations through
`a ᵍ⊗ w = includeLeft a * includeRight w`; homogeneity is a
`tensorGrading_induction` plus the graded monoid structure of the
target.

This is the reshuffling engine for M7f-2 (Wall-map factorization) and
for the associativity of the Brauer–Wall group (M7f-4).
-/
import Superfusion.Super.TensorGradingMap

namespace Superfusion

open TensorProduct
open GradedTensorProduct

/-! ### Scalar and sign helpers -/

section Helpers

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]

private theorem algHom_uzsmul (f : A →ₐ[K] B) (u : ℤˣ) (w : A) :
    f (u • w) = u • f w := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem ksmul_uzsmul_comm (c : K) (u : ℤˣ) (w : A) :
    c • u • w = u • c • w := by
  rw [Units.smul_def, Units.smul_def, smul_comm]

private theorem sgn_assoc_cancel₁ : ∀ j j₁ k₁ : ZMod 2,
    ((sgn (j * (j₁ + k₁)) : ℤˣ) * sgn (j * j₁) * sgn (j * k₁)) = 1 := by
  decide

private theorem sgn_assoc_cancel₂ : ∀ i k₁ k₂ : ZMod 2,
    ((sgn ((k₁ + k₂) * i) : ℤˣ) * sgn (k₂ * i) * sgn (k₁ * i)) = 1 := by
  decide

end Helpers

/-! ### Inclusion commutation -/

section InclComm

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The pure tensor as a product of the two inclusions. -/
theorem includeLeft_mul_includeRight (a : A) (b : B) :
    includeLeft 𝒜 ℬ a * includeRight 𝒜 ℬ b = a ᵍ⊗ₜ[K] b :=
  tmul_one_mul_one_tmul 𝒜 ℬ a b

/-- Koszul commutation of the two inclusions on homogeneous
elements. -/
theorem includeRight_mul_includeLeft {i j : ZMod 2} {x : A} {y : B}
    (hx : x ∈ 𝒜 i) (hy : y ∈ ℬ j) :
    includeRight 𝒜 ℬ y * includeLeft 𝒜 ℬ x
      = (-1 : ℤˣ) ^ (j * i) •
        (includeLeft 𝒜 ℬ x * includeRight 𝒜 ℬ y) := by
  rw [includeLeft_mul_includeRight]
  rw [show includeRight 𝒜 ℬ y * includeLeft 𝒜 ℬ x
      = ((1 : A) ᵍ⊗ₜ[K] ((⟨y, hy⟩ : ℬ j) : B))
        * ((((⟨x, hx⟩ : 𝒜 i) : A)) ᵍ⊗ₜ[K] (1 : B)) from rfl,
    tmul_coe_mul_coe_tmul, one_mul, mul_one]

end InclComm

/-! ### The associator -/

section Assoc

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable (𝒞 : ZMod 2 → Submodule K C)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]

/-- `𝒜 ᵍ⊗ ℬ → 𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞)`, `a ᵍ⊗ b ↦ a ᵍ⊗ (b ᵍ⊗ 1)`. -/
noncomputable def assocF₁ :
    (𝒜 ᵍ⊗[K] ℬ) →ₐ[K] (𝒜 ᵍ⊗[K] tensorGrading ℬ 𝒞) :=
  gmap 𝒜 ℬ 𝒜 (tensorGrading ℬ 𝒞) (AlgHom.id K A) (includeLeft ℬ 𝒞)
    (fun _ _ hx => hx)
    (fun _ _ hy => includeLeft_mem_tensorGrading ℬ 𝒞 hy)

/-- `C → 𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞)`, `c ↦ 1 ᵍ⊗ (1 ᵍ⊗ c)`. -/
noncomputable def assocF₂ :
    C →ₐ[K] (𝒜 ᵍ⊗[K] tensorGrading ℬ 𝒞) :=
  (includeRight 𝒜 (tensorGrading ℬ 𝒞)).comp (includeRight ℬ 𝒞)

theorem assocF₁_tmul (a : A) (b : B) :
    assocF₁ 𝒜 ℬ 𝒞 (a ᵍ⊗ₜ[K] b) = a ᵍ⊗ₜ[K] (b ᵍ⊗ₜ[K] (1 : C)) :=
  gmap_tmul 𝒜 ℬ 𝒜 (tensorGrading ℬ 𝒞) (AlgHom.id K A) (includeLeft ℬ 𝒞)
    (fun _ _ hx => hx)
    (fun _ _ hy => includeLeft_mem_tensorGrading ℬ 𝒞 hy) a b

/-- `assocF₁` through the inclusions of the target. -/
theorem assocF₁_tmul' (a : A) (b : B) :
    assocF₁ 𝒜 ℬ 𝒞 (a ᵍ⊗ₜ[K] b)
      = includeLeft 𝒜 (tensorGrading ℬ 𝒞) a
        * includeRight 𝒜 (tensorGrading ℬ 𝒞) (includeLeft ℬ 𝒞 b) := by
  rw [assocF₁_tmul,
    includeLeft_mul_includeRight 𝒜 (tensorGrading ℬ 𝒞) a
      (includeLeft ℬ 𝒞 b),
    show includeLeft ℬ 𝒞 b = b ᵍ⊗ₜ[K] (1 : C) from rfl]

private theorem assocF₂_def (c : C) :
    assocF₂ 𝒜 ℬ 𝒞 c
      = includeRight 𝒜 (tensorGrading ℬ 𝒞) (includeRight ℬ 𝒞 c) := rfl

private theorem assoc_anticommutes :
    ∀ ⦃i j : ZMod 2⦄ (z : tensorGrading 𝒜 ℬ i) (c : 𝒞 j),
      assocF₁ 𝒜 ℬ 𝒞 z * assocF₂ 𝒜 ℬ 𝒞 c
        = (-1 : ℤˣ) ^ (j * i) •
          (assocF₂ 𝒜 ℬ 𝒞 c * assocF₁ 𝒜 ℬ 𝒞 z) := by
  intro i j z c
  refine tensorGrading_induction 𝒜 ℬ z.2
    (p := fun w => assocF₁ 𝒜 ℬ 𝒞 w * assocF₂ 𝒜 ℬ 𝒞 c
      = (-1 : ℤˣ) ^ (j * i) • (assocF₂ 𝒜 ℬ 𝒞 c * assocF₁ 𝒜 ℬ 𝒞 w))
    ?_ ?_ ?_ ?_
  · intro j₁ k₁ x y hjk hx hy
    have hcc : includeRight ℬ 𝒞 (c : C) ∈ tensorGrading ℬ 𝒞 j :=
      includeRight_mem_tensorGrading ℬ 𝒞 c.2
    conv_lhs => rw [assocF₁_tmul' 𝒜 ℬ 𝒞 x y, assocF₂_def, mul_assoc,
      ← map_mul]
    conv_rhs => rw [assocF₁_tmul' 𝒜 ℬ 𝒞 x y, assocF₂_def, ← mul_assoc,
      includeRight_mul_includeLeft 𝒜 (tensorGrading ℬ 𝒞) hx hcc,
      smul_mul_assoc, mul_assoc, ← map_mul,
      includeRight_mul_includeLeft ℬ 𝒞 hy c.2,
      algHom_uzsmul, mul_smul_comm, smul_smul, smul_smul]
    rw [← hjk, ← sgn_eq_neg_one_uzpow, ← sgn_eq_neg_one_uzpow,
      ← sgn_eq_neg_one_uzpow, sgn_assoc_cancel₁ j j₁ k₁, one_smul]
  · rw [map_zero, zero_mul, mul_zero, smul_zero]
  · intro u v hu hv
    rw [map_add, add_mul, mul_add, hu, hv, smul_add]
  · intro k u hu
    rw [map_smul, smul_mul_assoc, mul_smul_comm, hu,
      ksmul_uzsmul_comm]

/-- The forward associator, from the universal property. -/
noncomputable def gassocHom :
    ((tensorGrading 𝒜 ℬ) ᵍ⊗[K] 𝒞) →ₐ[K]
      (𝒜 ᵍ⊗[K] tensorGrading ℬ 𝒞) :=
  lift (tensorGrading 𝒜 ℬ) 𝒞 (assocF₁ 𝒜 ℬ 𝒞) (assocF₂ 𝒜 ℬ 𝒞)
    (assoc_anticommutes 𝒜 ℬ 𝒞)

theorem gassocHom_tmul (z : 𝒜 ᵍ⊗[K] ℬ) (c : C) :
    gassocHom 𝒜 ℬ 𝒞 (z ᵍ⊗ₜ[K] c)
      = assocF₁ 𝒜 ℬ 𝒞 z * assocF₂ 𝒜 ℬ 𝒞 c :=
  lift_tmul (tensorGrading 𝒜 ℬ) 𝒞 (assocF₁ 𝒜 ℬ 𝒞) (assocF₂ 𝒜 ℬ 𝒞)
    (assoc_anticommutes 𝒜 ℬ 𝒞) z c

/-! ### The inverse -/

/-- `A → (𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞`, `a ↦ (a ᵍ⊗ 1) ᵍ⊗ 1`. -/
noncomputable def assocG₁ :
    A →ₐ[K] ((tensorGrading 𝒜 ℬ) ᵍ⊗[K] 𝒞) :=
  (includeLeft (tensorGrading 𝒜 ℬ) 𝒞).comp (includeLeft 𝒜 ℬ)

/-- `ℬ ᵍ⊗ 𝒞 → (𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞`, `b ᵍ⊗ c ↦ (1 ᵍ⊗ b) ᵍ⊗ c`. -/
noncomputable def assocG₂ :
    (ℬ ᵍ⊗[K] 𝒞) →ₐ[K] ((tensorGrading 𝒜 ℬ) ᵍ⊗[K] 𝒞) :=
  gmap ℬ 𝒞 (tensorGrading 𝒜 ℬ) 𝒞 (includeRight 𝒜 ℬ) (AlgHom.id K C)
    (fun _ _ hy => includeRight_mem_tensorGrading 𝒜 ℬ hy)
    (fun _ _ hc => hc)

theorem assocG₂_tmul (b : B) (c : C) :
    assocG₂ 𝒜 ℬ 𝒞 (b ᵍ⊗ₜ[K] c)
      = (includeRight 𝒜 ℬ b) ᵍ⊗ₜ[K] c :=
  gmap_tmul ℬ 𝒞 (tensorGrading 𝒜 ℬ) 𝒞 (includeRight 𝒜 ℬ)
    (AlgHom.id K C)
    (fun _ _ hy => includeRight_mem_tensorGrading 𝒜 ℬ hy)
    (fun _ _ hc => hc) b c

private theorem assocG₁_def (a : A) :
    assocG₁ 𝒜 ℬ 𝒞 a
      = includeLeft (tensorGrading 𝒜 ℬ) 𝒞 (includeLeft 𝒜 ℬ a) := rfl

private theorem assoc_anticommutes' :
    ∀ ⦃i j : ZMod 2⦄ (a : 𝒜 i) (w : tensorGrading ℬ 𝒞 j),
      assocG₁ 𝒜 ℬ 𝒞 a * assocG₂ 𝒜 ℬ 𝒞 w
        = (-1 : ℤˣ) ^ (j * i) •
          (assocG₂ 𝒜 ℬ 𝒞 w * assocG₁ 𝒜 ℬ 𝒞 a) := by
  intro i j a w
  refine tensorGrading_induction ℬ 𝒞 w.2
    (p := fun v => assocG₁ 𝒜 ℬ 𝒞 a * assocG₂ 𝒜 ℬ 𝒞 v
      = (-1 : ℤˣ) ^ (j * i) • (assocG₂ 𝒜 ℬ 𝒞 v * assocG₁ 𝒜 ℬ 𝒞 a))
    ?_ ?_ ?_ ?_
  · intro k₁ k₂ b c hjk hb hc
    have hla : includeLeft 𝒜 ℬ (a : A) ∈ tensorGrading 𝒜 ℬ i :=
      includeLeft_mem_tensorGrading 𝒜 ℬ a.2
    have hsplit : ((includeRight 𝒜 ℬ b) ᵍ⊗ₜ[K] c :
        (tensorGrading 𝒜 ℬ) ᵍ⊗[K] 𝒞)
        = includeLeft (tensorGrading 𝒜 ℬ) 𝒞 (includeRight 𝒜 ℬ b)
          * includeRight (tensorGrading 𝒜 ℬ) 𝒞 c :=
      (includeLeft_mul_includeRight (tensorGrading 𝒜 ℬ) 𝒞
        (includeRight 𝒜 ℬ b) c).symm
    conv_lhs => rw [assocG₂_tmul, hsplit, assocG₁_def, ← mul_assoc,
      ← map_mul]
    conv_rhs => rw [assocG₂_tmul, hsplit, assocG₁_def, mul_assoc,
      includeRight_mul_includeLeft (tensorGrading 𝒜 ℬ) 𝒞 hla hc,
      mul_smul_comm, ← mul_assoc, ← map_mul,
      includeRight_mul_includeLeft 𝒜 ℬ a.2 hb,
      algHom_uzsmul, smul_mul_assoc, smul_smul, smul_smul]
    rw [← hjk, ← sgn_eq_neg_one_uzpow, ← sgn_eq_neg_one_uzpow,
      ← sgn_eq_neg_one_uzpow, sgn_assoc_cancel₂ i k₁ k₂, one_smul]
  · rw [map_zero, mul_zero, zero_mul, smul_zero]
  · intro u v hu hv
    rw [map_add, mul_add, add_mul, hu, hv, smul_add]
  · intro k u hu
    rw [map_smul, mul_smul_comm, smul_mul_assoc, hu,
      ksmul_uzsmul_comm]

/-- The inverse associator. -/
noncomputable def gassocInv :
    (𝒜 ᵍ⊗[K] tensorGrading ℬ 𝒞) →ₐ[K]
      ((tensorGrading 𝒜 ℬ) ᵍ⊗[K] 𝒞) :=
  lift 𝒜 (tensorGrading ℬ 𝒞) (assocG₁ 𝒜 ℬ 𝒞) (assocG₂ 𝒜 ℬ 𝒞)
    (assoc_anticommutes' 𝒜 ℬ 𝒞)

theorem gassocInv_tmul (a : A) (w : ℬ ᵍ⊗[K] 𝒞) :
    gassocInv 𝒜 ℬ 𝒞 (a ᵍ⊗ₜ[K] w)
      = assocG₁ 𝒜 ℬ 𝒞 a * assocG₂ 𝒜 ℬ 𝒞 w :=
  lift_tmul 𝒜 (tensorGrading ℬ 𝒞) (assocG₁ 𝒜 ℬ 𝒞) (assocG₂ 𝒜 ℬ 𝒞)
    (assoc_anticommutes' 𝒜 ℬ 𝒞) a w

/-! ### The composites are the identity -/

private theorem gassocHom_assocG₁ (a : A) :
    gassocHom 𝒜 ℬ 𝒞 (assocG₁ 𝒜 ℬ 𝒞 a)
      = includeLeft 𝒜 (tensorGrading ℬ 𝒞) a := by
  rw [show assocG₁ 𝒜 ℬ 𝒞 a
      = (includeLeft 𝒜 ℬ a) ᵍ⊗ₜ[K] (1 : C) from rfl,
    gassocHom_tmul, map_one, mul_one,
    show includeLeft 𝒜 ℬ a = a ᵍ⊗ₜ[K] (1 : B) from rfl,
    assocF₁_tmul]
  rfl

private theorem gassocHom_comp_assocG₂ :
    (gassocHom 𝒜 ℬ 𝒞).comp (assocG₂ 𝒜 ℬ 𝒞)
      = includeRight 𝒜 (tensorGrading ℬ 𝒞) := by
  refine galgHom_ext ℬ 𝒞 fun b c => ?_
  rw [AlgHom.comp_apply, assocG₂_tmul, gassocHom_tmul,
    show includeRight 𝒜 ℬ b = (1 : A) ᵍ⊗ₜ[K] b from rfl,
    assocF₁_tmul, assocF₂_def,
    show ((1 : A) ᵍ⊗ₜ[K] ((b ᵍ⊗ₜ[K] (1 : C)) : ℬ ᵍ⊗[K] 𝒞))
      = includeRight 𝒜 (tensorGrading ℬ 𝒞) (b ᵍ⊗ₜ[K] (1 : C))
      from rfl,
    ← map_mul,
    show includeRight ℬ 𝒞 c = (1 : B) ᵍ⊗ₜ[K] c from rfl,
    tmul_one_mul_one_tmul]

private theorem gassocInv_comp_assocF₁ :
    (gassocInv 𝒜 ℬ 𝒞).comp (assocF₁ 𝒜 ℬ 𝒞)
      = includeLeft (tensorGrading 𝒜 ℬ) 𝒞 := by
  refine galgHom_ext 𝒜 ℬ fun a b => ?_
  rw [AlgHom.comp_apply, assocF₁_tmul, gassocInv_tmul, assocG₂_tmul,
    assocG₁_def,
    show ((includeRight 𝒜 ℬ b) ᵍ⊗ₜ[K] (1 : C) :
        (tensorGrading 𝒜 ℬ) ᵍ⊗[K] 𝒞)
      = includeLeft (tensorGrading 𝒜 ℬ) 𝒞 (includeRight 𝒜 ℬ b)
      from rfl,
    ← map_mul, includeLeft_mul_includeRight 𝒜 ℬ a b]

private theorem gassocInv_assocF₂ (c : C) :
    gassocInv 𝒜 ℬ 𝒞 (assocF₂ 𝒜 ℬ 𝒞 c)
      = includeRight (tensorGrading 𝒜 ℬ) 𝒞 c := by
  rw [show assocF₂ 𝒜 ℬ 𝒞 c
      = (1 : A) ᵍ⊗ₜ[K] ((1 : B) ᵍ⊗ₜ[K] c) from rfl,
    gassocInv_tmul, map_one, one_mul, assocG₂_tmul, map_one]
  rfl

/-- **Associativity of the graded tensor product** (M7f-1c):
`(𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞 ≃ₐ 𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞)`, `(a ᵍ⊗ b) ᵍ⊗ c ↦ a ᵍ⊗ (b ᵍ⊗ c)`,
with no Koszul sign. -/
noncomputable def gassoc :
    ((tensorGrading 𝒜 ℬ) ᵍ⊗[K] 𝒞) ≃ₐ[K]
      (𝒜 ᵍ⊗[K] tensorGrading ℬ 𝒞) :=
  AlgEquiv.ofAlgHom (gassocHom 𝒜 ℬ 𝒞) (gassocInv 𝒜 ℬ 𝒞)
    (galgHom_ext 𝒜 (tensorGrading ℬ 𝒞) fun a w => by
      have hw : gassocHom 𝒜 ℬ 𝒞 (assocG₂ 𝒜 ℬ 𝒞 w)
          = includeRight 𝒜 (tensorGrading ℬ 𝒞) w :=
        AlgHom.congr_fun (gassocHom_comp_assocG₂ 𝒜 ℬ 𝒞) w
      rw [AlgHom.comp_apply, gassocInv_tmul, map_mul,
        gassocHom_assocG₁, hw,
        includeLeft_mul_includeRight, AlgHom.id_apply])
    (galgHom_ext (tensorGrading 𝒜 ℬ) 𝒞 fun z c => by
      have hz : gassocInv 𝒜 ℬ 𝒞 (assocF₁ 𝒜 ℬ 𝒞 z)
          = includeLeft (tensorGrading 𝒜 ℬ) 𝒞 z :=
        AlgHom.congr_fun (gassocInv_comp_assocF₁ 𝒜 ℬ 𝒞) z
      rw [AlgHom.comp_apply, gassocHom_tmul, map_mul, hz,
        gassocInv_assocF₂,
        includeLeft_mul_includeRight, AlgHom.id_apply])

@[simp] theorem gassoc_tmul (a : A) (b : B) (c : C) :
    gassoc 𝒜 ℬ 𝒞 ((a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c)
      = a ᵍ⊗ₜ[K] (b ᵍ⊗ₜ[K] c) := by
  show gassocHom 𝒜 ℬ 𝒞 ((a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c) = _
  rw [gassocHom_tmul, assocF₁_tmul' 𝒜 ℬ 𝒞 a b, assocF₂_def,
    mul_assoc, ← map_mul, includeLeft_mul_includeRight ℬ 𝒞 b c,
    includeLeft_mul_includeRight]

/-! ### Grading -/

theorem gassocHom_isHomogeneous :
    IsHomogeneousHom (tensorGrading (tensorGrading 𝒜 ℬ) 𝒞)
      (tensorGrading 𝒜 (tensorGrading ℬ 𝒞)) (gassocHom 𝒜 ℬ 𝒞) := by
  intro i z hz
  refine tensorGrading_induction (tensorGrading 𝒜 ℬ) 𝒞 hz
    (p := fun w => gassocHom 𝒜 ℬ 𝒞 w
      ∈ tensorGrading 𝒜 (tensorGrading ℬ 𝒞) i)
    ?_ ?_ ?_ ?_
  · intro j k z' c hjk z'mem hc
    rw [gassocHom_tmul]
    refine hjk ▸ SetLike.mul_mem_graded ?_ ?_
    · exact gmap_isHomogeneous 𝒜 ℬ 𝒜 (tensorGrading ℬ 𝒞)
        (AlgHom.id K A) (includeLeft ℬ 𝒞) (fun _ _ hx => hx)
        (fun _ _ hy => includeLeft_mem_tensorGrading ℬ 𝒞 hy) j z' z'mem
    · rw [assocF₂_def]
      exact includeRight_mem_tensorGrading 𝒜 (tensorGrading ℬ 𝒞)
        (includeRight_mem_tensorGrading ℬ 𝒞 hc)
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- The associator carries the nested grading **onto** the nested
grading. -/
theorem gassoc_map_grading (i : ZMod 2) :
    (tensorGrading (tensorGrading 𝒜 ℬ) 𝒞 i).map
        (gassoc 𝒜 ℬ 𝒞).toLinearMap
      = tensorGrading 𝒜 (tensorGrading ℬ 𝒞) i :=
  map_grading_of_bijective (tensorGrading (tensorGrading 𝒜 ℬ) 𝒞)
    (tensorGrading 𝒜 (tensorGrading ℬ 𝒞)) (gassoc 𝒜 ℬ 𝒞).toAlgHom
    (gassocHom_isHomogeneous 𝒜 ℬ 𝒞) (gassoc 𝒜 ℬ 𝒞).bijective i

end Assoc

end Superfusion

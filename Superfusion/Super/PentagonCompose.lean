/-
Superfusion / Super / PentagonCompose

Milestone M7d-5b-4-iii(a): **composition and the left-tensor
transport** — the last two generic pieces of the intertwiner kit.

- `intertwines_comp`: intertwiners compose along a chain of maps,
  with parities adding — `t₂ t₁` intertwines `(φ₁, φ₃)` with parity
  `p₁ + p₂`.  (This is what makes the K₅ path composites
  intertwiners of the extreme routes, and forces the two paths'
  parities to agree — the cocycle property of `p`.)
- `intertwines_one_gtensor`: the mirror of `intertwines_gtensor_one`
  — `1 ᵍ⊗ₜ t` intertwines the pair extended by the identity on the
  LEFT factor, with the same parity.
-/
import Superfusion.Super.PentagonMatrixTransport

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section Compose

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞]

private theorem sgn_comp_recombine : ∀ j p₁ p₂ : ZMod 2,
    ((sgn (j * p₂) : ℤˣ) : ℤ) * ((sgn (j * p₁) : ℤˣ) : ℤ)
      = ((sgn (j * (p₁ + p₂)) : ℤˣ) : ℤ) := by
  decide

omit [GradedAlgebra 𝒜] in
/-- **Intertwiners compose, parities add** (M7d-5b-4-iii): if `t₁`
intertwines `(φ₁, φ₂)` with parity `p₁` and `t₂` intertwines
`(φ₂, φ₃)` with parity `p₂`, then `t₂ t₁` intertwines `(φ₁, φ₃)`
with parity `p₁ + p₂`. -/
theorem intertwines_comp (φ₁ φ₂ φ₃ : A →ₐ[K] B)
    {p₁ p₂ : ZMod 2} {t₁ t₂ : B}
    (h₁ : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ₂ x * t₁ = ((sgn (j * p₁) : ℤˣ) : ℤ) • (t₁ * φ₁ x))
    (h₂ : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ₃ x * t₂ = ((sgn (j * p₂) : ℤˣ) : ℤ) • (t₂ * φ₂ x)) :
    ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ₃ x * (t₂ * t₁)
        = ((sgn (j * (p₁ + p₂)) : ℤˣ) : ℤ) • ((t₂ * t₁) * φ₁ x) := by
  intro j x hx
  rw [← mul_assoc, h₂ hx, smul_mul_assoc, mul_assoc, h₁ hx,
    mul_smul_comm, smul_smul, sgn_comp_recombine j p₁ p₂, mul_assoc]

private theorem sgn_one_gtensor_recombine : ∀ jx jy p : ZMod 2,
    ((sgn (jy * p) : ℤˣ) : ℤ)
      = ((sgn ((jx + jy) * p) : ℤˣ) : ℤ)
        * ((sgn (p * jx) : ℤˣ) : ℤ) := by
  decide

private theorem uzpow_to_sgn' (e : ZMod 2) (z : 𝒞 ᵍ⊗[K] ℬ) :
    (-1 : ℤˣ) ^ e • z = ((sgn e : ℤˣ) : ℤ) • z := by
  rw [← sgn_eq_neg_one_uzpow, Units.smul_def]

private theorem gtmul_zsmul' (n : ℤ) (x : C) (y : B) :
    (x ᵍ⊗ₜ[K] (n • y) : 𝒞 ᵍ⊗[K] ℬ) = n • (x ᵍ⊗ₜ[K] y) := by
  rw [show ((x ᵍ⊗ₜ[K] (n • y) : 𝒞 ᵍ⊗[K] ℬ))
      = of K 𝒞 ℬ (x ⊗ₜ[K] (n • y)) from rfl,
    show (x ⊗ₜ[K] (n • y) : C ⊗[K] B) = n • (x ⊗ₜ[K] y) from
      TensorProduct.tmul_smul n x y,
    map_zsmul]

/-- **Left-tensor transport**: if `t` intertwines `(φ, φ')` with
parity `p`, then `1 ᵍ⊗ₜ t` intertwines the pair extended by the
identity on the left factor, with the same parity. -/
theorem intertwines_one_gtensor
    (φ φ' : A →ₐ[K] B)
    (hφ : IsHomogeneousHom 𝒜 ℬ φ) (hφ' : IsHomogeneousHom 𝒜 ℬ φ')
    {p : ZMod 2} {t : B} (htp : t ∈ ℬ p)
    (hint : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ' x * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ x)) :
    ∀ ⦃j : ZMod 2⦄ ⦃w : 𝒞 ᵍ⊗[K] 𝒜⦄, w ∈ tensorGrading 𝒞 𝒜 j →
      gmap 𝒞 𝒜 𝒞 ℬ (AlgHom.id K C) φ' (id_isHomogeneous 𝒞) hφ' w
          * (((1 : C) ᵍ⊗ₜ[K] t) : 𝒞 ᵍ⊗[K] ℬ)
        = ((sgn (j * p) : ℤˣ) : ℤ) •
          ((((1 : C) ᵍ⊗ₜ[K] t) : 𝒞 ᵍ⊗[K] ℬ)
            * gmap 𝒞 𝒜 𝒞 ℬ (AlgHom.id K C) φ (id_isHomogeneous 𝒞) hφ
              w) := by
  intro j w hw
  refine tensorGrading_induction 𝒞 𝒜 hw
    (p := fun v =>
      gmap 𝒞 𝒜 𝒞 ℬ (AlgHom.id K C) φ' (id_isHomogeneous 𝒞) hφ' v
          * (((1 : C) ᵍ⊗ₜ[K] t) : 𝒞 ᵍ⊗[K] ℬ)
        = ((sgn (j * p) : ℤˣ) : ℤ) •
          ((((1 : C) ᵍ⊗ₜ[K] t) : 𝒞 ᵍ⊗[K] ℬ)
            * gmap 𝒞 𝒜 𝒞 ℬ (AlgHom.id K C) φ (id_isHomogeneous 𝒞) hφ
              v))
    ?_ ?_ ?_ ?_
  · -- pure homogeneous tensors y ᵍ⊗ x, |y| + |x| = j
    intro jy jx y x hj hy hx
    rw [gmap_tmul, gmap_tmul]
    rw [show ((AlgHom.id K C y) ᵍ⊗ₜ[K] (φ' x) : 𝒞 ᵍ⊗[K] ℬ)
          * (((1 : C) ᵍ⊗ₜ[K] t) : 𝒞 ᵍ⊗[K] ℬ)
        = (((⟨y, hy⟩ : 𝒞 jy) : C) ᵍ⊗ₜ[K]
            ((⟨φ' x, hφ' jx x hx⟩ : ℬ jx) : B))
          * ((((⟨(1 : C), SetLike.one_mem_graded 𝒞⟩ : 𝒞 0) : C))
            ᵍ⊗ₜ[K] (((⟨t, htp⟩ : ℬ p) : B))) from rfl,
      tmul_coe_mul_coe_tmul,
      show (((1 : C) ᵍ⊗ₜ[K] t) : 𝒞 ᵍ⊗[K] ℬ)
          * ((AlgHom.id K C y) ᵍ⊗ₜ[K] (φ x) : 𝒞 ᵍ⊗[K] ℬ)
        = ((((⟨(1 : C), SetLike.one_mem_graded 𝒞⟩ : 𝒞 0) : C))
            ᵍ⊗ₜ[K] (((⟨t, htp⟩ : ℬ p) : B)))
          * (((⟨y, hy⟩ : 𝒞 jy) : C) ᵍ⊗ₜ[K]
            ((⟨φ x, hφ jx x hx⟩ : ℬ jx) : B)) from rfl,
      tmul_coe_mul_coe_tmul]
    rw [show (φ' x * t : B) = ((sgn (jx * p) : ℤˣ) : ℤ) • (t * φ x)
        from hint hx]
    rw [mul_one, one_mul, gtmul_zsmul' ℬ 𝒞]
    -- signs: LHS uzpow exponent jx * 0 = 0 kills; RHS exponent p * jy;
    -- recombine sgn(jx p) into sgn(j p) * sgn(p jy)
    rw [uzpow_to_sgn' ℬ 𝒞, uzpow_to_sgn' ℬ 𝒞, smul_smul, smul_smul]
    rw [show (((sgn (jx * (0 : ZMod 2)) : ℤˣ) : ℤ))
          * (((sgn (jx * p) : ℤˣ) : ℤ))
        = ((sgn (j * p) : ℤˣ) : ℤ) * ((sgn (p * jy) : ℤˣ) : ℤ) from by
      rw [← hj]
      have := sgn_one_gtensor_recombine jy jx p
      -- reorder to the mirrored identity
      rcases zmod2_cases p with hp | hp <;>
        rcases zmod2_cases jx with hjx | hjx <;>
          rcases zmod2_cases jy with hjy | hjy <;>
            subst hp <;> subst hjx <;> subst hjy <;> decide]
  · rw [map_zero, map_zero, zero_mul, mul_zero, smul_zero]
  · intro u v hu hv
    rw [map_add, map_add, add_mul, mul_add, hu, hv, smul_add]
  · intro c u hu
    rw [map_smul, map_smul, smul_mul_assoc, hu, mul_smul_comm, smul_comm]

end Compose

end Superfusion

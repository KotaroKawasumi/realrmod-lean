/-
Superfusion / Super / PentagonExtend

Milestone M7d-5b-4-i: **the intertwiner transport kit** for the
pentagon scalars.  Two reusable transports:

- `intertwines_map`: an intertwiner for a pair of homogeneous maps
  transports along a further homogeneous algebra map (apply it to
  the relation);
- `intertwines_gtensor_one`: if `t` intertwines `(φ, φ')` with
  parity `p`, then `t ᵍ⊗ₜ 1` intertwines `(φ ᵍ⊗ id, φ' ᵍ⊗ id)` with
  the same parity — the Koszul signs of `tmul_coe_mul_coe_tmul`
  against `|1| = 0` recombine to `(-1)^{|w||t|}` on homogeneous
  tensors.

Together these turn the triple intertwiner `pentagonT a b c` into
edge intertwiners of the quadruple pentagon (M7d-5b-4-ii), living in
the common quadruple target.
-/
import Superfusion.Super.PentagonParity

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section Transport

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞]

omit [GradedAlgebra 𝒞] in
/-- The identity algebra map is homogeneous for any grading. -/
theorem id_isHomogeneous : IsHomogeneousHom 𝒞 𝒞 (AlgHom.id K C) :=
  fun _ _ hx => hx

omit [GradedAlgebra 𝒜] in
/-- An intertwining relation transports along a further algebra
map: apply `ψ` to both sides. -/
theorem intertwines_map (φ φ' : A →ₐ[K] B) (ψ : B →ₐ[K] C)
    {p : ZMod 2} {t : B}
    (hint : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ' x * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ x)) :
    ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      (ψ.comp φ') x * ψ t
        = ((sgn (j * p) : ℤˣ) : ℤ) • (ψ t * (ψ.comp φ) x) := by
  intro j x hx
  have h := congrArg ψ (hint hx)
  rw [map_mul, map_zsmul, map_mul] at h
  exact h

/-- Recombine the two `tmul_coe_mul_coe_tmul` signs produced on the
pure-tensor case of `intertwines_gtensor_one`: the `jy * p` sign from
`(φ' x ᵍ⊗ y)(t ᵍ⊗ 1)` and the (trivial) `0 * jx` sign from
`(t ᵍ⊗ 1)(φ x ᵍ⊗ y)` combine, along the already-applied intertwiner
sign `jx * p`, to the single `(jx + jy) * p = j * p` sign. -/
private theorem uzpow_to_sgn (e : ZMod 2) (z : ℬ ᵍ⊗[K] 𝒞) :
    (-1 : ℤˣ) ^ e • z = ((sgn e : ℤˣ) : ℤ) • z := by
  rw [← sgn_eq_neg_one_uzpow, Units.smul_def]

private theorem zsmul_gtmul (n : ℤ) (x : B) (y : C) :
    ((n • x) ᵍ⊗ₜ[K] y : ℬ ᵍ⊗[K] 𝒞) = n • (x ᵍ⊗ₜ[K] y) := by
  rw [show (((n • x) ᵍ⊗ₜ[K] y : ℬ ᵍ⊗[K] 𝒞))
      = of K ℬ 𝒞 ((n • x) ⊗ₜ[K] y) from rfl,
    show ((n • x) ⊗ₜ[K] y : B ⊗[K] C) = n • (x ⊗ₜ[K] y) from
      (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

private theorem sgn_gtensor_one_recombine : ∀ jx jy p : ZMod 2,
    ((sgn (jy * p) : ℤˣ) : ℤ) * ((sgn (jx * p) : ℤˣ) : ℤ)
      = ((sgn ((jx + jy) * p) : ℤˣ) : ℤ) * ((sgn ((0 : ZMod 2) * jx) : ℤˣ) : ℤ) := by
  decide

private theorem uzpow_smul_smul_recombine {jx jy p : ZMod 2} {j : ZMod 2}
    (hj : jx + jy = j) (z : ℬ ᵍ⊗[K] 𝒞) :
    (-1 : ℤˣ) ^ (jy * p) • (((sgn (jx * p) : ℤˣ) : ℤ) • z)
      = ((sgn (j * p) : ℤˣ) : ℤ) •
        ((-1 : ℤˣ) ^ ((0 : ZMod 2) * jx) • z) := by
  subst hj
  rw [uzpow_to_sgn ℬ 𝒞, uzpow_to_sgn ℬ 𝒞, smul_smul, smul_smul,
    sgn_gtensor_one_recombine jx jy p]

/-- Tensoring an intertwiner with `1`: if `t` intertwines `(φ, φ')`
with parity `p`, then `t ᵍ⊗ₜ 1` intertwines the `gmap`-extended
pair with the same parity.  (The Koszul sign of passing `1 ∈ 𝒞 0`
is trivial, and the sign of passing the second factor recombines
with the first-factor relation to `(-1)^{|w| p}` on homogeneous
tensors, extended to all of the graded tensor product by
linearity.) -/
theorem intertwines_gtensor_one
    (φ φ' : A →ₐ[K] B)
    (hφ : IsHomogeneousHom 𝒜 ℬ φ) (hφ' : IsHomogeneousHom 𝒜 ℬ φ')
    {p : ZMod 2} {t : B} (htp : t ∈ ℬ p)
    (hint : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ' x * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ x)) :
    ∀ ⦃j : ZMod 2⦄ ⦃w : 𝒜 ᵍ⊗[K] 𝒞⦄, w ∈ tensorGrading 𝒜 𝒞 j →
      gmap 𝒜 𝒞 ℬ 𝒞 φ' (AlgHom.id K C) hφ'
          (id_isHomogeneous 𝒞) w * ((t ᵍ⊗ₜ[K] (1 : C)) : ℬ ᵍ⊗[K] 𝒞)
        = ((sgn (j * p) : ℤˣ) : ℤ) •
          (((t ᵍ⊗ₜ[K] (1 : C)) : ℬ ᵍ⊗[K] 𝒞)
            * gmap 𝒜 𝒞 ℬ 𝒞 φ (AlgHom.id K C) hφ
              (id_isHomogeneous 𝒞) w) := by
  intro j w hw
  refine tensorGrading_induction 𝒜 𝒞 hw
    (p := fun v =>
      gmap 𝒜 𝒞 ℬ 𝒞 φ' (AlgHom.id K C) hφ' (id_isHomogeneous 𝒞) v
          * ((t ᵍ⊗ₜ[K] (1 : C)) : ℬ ᵍ⊗[K] 𝒞)
        = ((sgn (j * p) : ℤˣ) : ℤ) •
          (((t ᵍ⊗ₜ[K] (1 : C)) : ℬ ᵍ⊗[K] 𝒞)
            * gmap 𝒜 𝒞 ℬ 𝒞 φ (AlgHom.id K C) hφ (id_isHomogeneous 𝒞) v))
    ?_ ?_ ?_ ?_
  · -- pure homogeneous tensors x ᵍ⊗ y, |x| + |y| = j
    intro jx jy x y hj hx hy
    rw [gmap_tmul, gmap_tmul]
    -- (φ' x ᵍ⊗ y)(t ᵍ⊗ 1) = (-1)^{|y||t|} (φ' x · t) ᵍ⊗ y
    -- (t ᵍ⊗ 1)(φ x ᵍ⊗ y) = (φ x is |x|, 1 is 0) = (t · φ x) ᵍ⊗ y
    rw [show ((φ' x) ᵍ⊗ₜ[K] (AlgHom.id K C y) : ℬ ᵍ⊗[K] 𝒞)
          * ((t ᵍ⊗ₜ[K] (1 : C)) : ℬ ᵍ⊗[K] 𝒞)
        = (((⟨φ' x, hφ' jx x hx⟩ : ℬ jx) : B) ᵍ⊗ₜ[K]
            ((⟨(AlgHom.id K C) y, hy⟩ : 𝒞 jy) : C))
          * ((((⟨t, htp⟩ : ℬ p) : B)) ᵍ⊗ₜ[K] (1 : C)) from rfl,
      tmul_coe_mul_coe_tmul,
      show ((t ᵍ⊗ₜ[K] (1 : C)) : ℬ ᵍ⊗[K] 𝒞)
          * ((φ x) ᵍ⊗ₜ[K] (AlgHom.id K C y) : ℬ ᵍ⊗[K] 𝒞)
        = ((((⟨t, htp⟩ : ℬ p) : B)) ᵍ⊗ₜ[K]
            (((⟨(1 : C), SetLike.one_mem_graded 𝒞⟩ : 𝒞 0) : C)))
          * (((⟨φ x, hφ jx x hx⟩ : ℬ jx) : B) ᵍ⊗ₜ[K]
            ((⟨(AlgHom.id K C) y, hy⟩ : 𝒞 jy) : C)) from rfl,
      tmul_coe_mul_coe_tmul]
    -- now push the first-factor relation through and recombine signs
    rw [show (φ' x * t : B) = ((sgn (jx * p) : ℤˣ) : ℤ) • (t * φ x)
        from hint hx]
    rw [mul_one, one_mul, zsmul_gtmul ℬ 𝒞]
    exact uzpow_smul_smul_recombine ℬ 𝒞 hj _
  · rw [map_zero, map_zero, zero_mul, mul_zero, smul_zero]
  · intro u v hu hv
    rw [map_add, map_add, add_mul, mul_add, hu, hv, smul_add]
  · intro c u hu
    rw [map_smul, map_smul, smul_mul_assoc, hu, mul_smul_comm, smul_comm]

end Transport

end Superfusion

/-
Superfusion / Super / PentagonMatrixNat

Milestone M7d-5b-4-iii(b), part 5: **matrix-tensor naturalities** —
the last interchange laws for the cluster edges:

- `gtensorComm_natural_apply`: naturality of the bundled braiding
  (homogeneous congruences preserve degrees, so the Koszul signs on
  the two sides agree);
- `matrixSuperGtensor_natural_apply`: naturality of the
  matrix-stabilization compatibility in the non-matrix slot (the
  signed diagonal `sdiag` commutes with a homogeneous congruence
  because homogeneous maps commute with the parity projections).
-/
import Superfusion.Super.PentagonNaturality

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section MatrixNat

universe u

variable {K : Type u} [CommRing K]

/-- A cast marker re-anchoring `.carrier` of `SuperAlgebra.gtensor`,
matching the idiom of `PentagonNaturality.lean`. -/
private def toC {P Q : SuperAlgebra K}
    (x : P.grading ᵍ⊗[K] Q.grading) : (P.gtensor Q).carrier := x

private theorem gtensorCongr_tmul'' {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (a : P.carrier) (b : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv (toC (a ᵍ⊗ₜ[K] b))
      = toC (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading e.toAlgEquiv
    f.toAlgEquiv e.map_grading f.map_grading a b

/-- `ℤˣ`-scalar multiples commute with any algebra equivalence. -/
private theorem algEquiv_uzsmul' {A B : Type*} [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] (φ : A ≃ₐ[K] B) (u : ℤˣ) (x : A) :
    φ (u • x) = u • φ x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- The braiding on a pure tensor of homogeneous elements, applied
through the bundled `gtensorComm`. -/
private theorem gtensorComm_coe_apply {P Q : SuperAlgebra K}
    {i j : ZMod 2} {x : P.carrier} {y : Q.carrier}
    (hx : x ∈ P.grading i) (hy : y ∈ Q.grading j) :
    (gtensorComm P Q).toAlgEquiv (toC (x ᵍ⊗ₜ[K] y))
      = (-1 : ℤˣ) ^ (j * i) • toC (y ᵍ⊗ₜ[K] x) := by
  have h := comm_coe_tmul_coe (𝒜 := P.grading) (ℬ := Q.grading)
    (⟨x, hx⟩ : P.grading i) (⟨y, hy⟩ : Q.grading j)
  exact h

/-- Naturality of the bundled braiding, on homogeneous pure tensors. -/
private theorem gtensorComm_natural_hom {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    {i j : ZMod 2} {x : P.carrier} {y : Q.carrier}
    (hx : x ∈ P.grading i) (hy : y ∈ Q.grading j) :
    (gtensorComm P' Q').toAlgEquiv
        ((e.gtensorCongr f).toAlgEquiv (toC (x ᵍ⊗ₜ[K] y)))
      = (f.gtensorCongr e).toAlgEquiv
        ((gtensorComm P Q).toAlgEquiv (toC (x ᵍ⊗ₜ[K] y))) := by
  have hex : e.toAlgEquiv x ∈ P'.grading i := by
    rw [← e.map_grading i]; exact Submodule.mem_map_of_mem hx
  have hfy : f.toAlgEquiv y ∈ Q'.grading j := by
    rw [← f.map_grading j]; exact Submodule.mem_map_of_mem hy
  rw [gtensorCongr_tmul'', gtensorComm_coe_apply hex hfy,
    gtensorComm_coe_apply hx hy,
    algEquiv_uzsmul' (f.gtensorCongr e).toAlgEquiv _ _,
    gtensorCongr_tmul'']

/-- Naturality of the bundled braiding, applied form. -/
theorem gtensorComm_natural_apply {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (w : (P.gtensor Q).carrier) :
    (gtensorComm P' Q').toAlgEquiv ((e.gtensorCongr f).toAlgEquiv w)
      = (f.gtensorCongr e).toAlgEquiv
        ((gtensorComm P Q).toAlgEquiv w) := by
  have hhom : ((gtensorComm P' Q').toAlgEquiv.toAlgHom).comp
        ((e.gtensorCongr f).toAlgEquiv.toAlgHom)
      = ((f.gtensorCongr e).toAlgEquiv.toAlgHom).comp
        ((gtensorComm P Q).toAlgEquiv.toAlgHom) := by
    refine galgHom_ext P.grading Q.grading ?_
    intro a b
    change (gtensorComm P' Q').toAlgEquiv
        ((e.gtensorCongr f).toAlgEquiv (toC (a ᵍ⊗ₜ[K] b)))
      = (f.gtensorCongr e).toAlgEquiv
        ((gtensorComm P Q).toAlgEquiv (toC (a ᵍ⊗ₜ[K] b)))
    -- decompose both slots into homogeneous parts: four cases
    set x₀ := evenPart P.grading a
    set x₁ := oddPart P.grading a
    set y₀ := evenPart Q.grading b
    set y₁ := oddPart Q.grading b
    have hx : x₀ + x₁ = a := evenPart_add_oddPart P.grading a
    have hy : y₀ + y₁ = b := evenPart_add_oddPart Q.grading b
    have hx0 : x₀ ∈ P.grading 0 := evenPart_mem P.grading a
    have hx1 : x₁ ∈ P.grading 1 := oddPart_mem P.grading a
    have hy0 : y₀ ∈ Q.grading 0 := evenPart_mem Q.grading b
    have hy1 : y₁ ∈ Q.grading 1 := oddPart_mem Q.grading b
    have hab' : (a ᵍ⊗ₜ[K] b : P.grading ᵍ⊗[K] Q.grading)
        = (x₀ ᵍ⊗ₜ[K] y₀) + (x₀ ᵍ⊗ₜ[K] y₁) + (x₁ ᵍ⊗ₜ[K] y₀) + (x₁ ᵍ⊗ₜ[K] y₁) := by
      rw [← hx, ← hy, add_gtmul, gtmul_add, gtmul_add]
      abel
    have hab : (toC (a ᵍ⊗ₜ[K] b) : (P.gtensor Q).carrier)
        = toC (x₀ ᵍ⊗ₜ[K] y₀) + toC (x₀ ᵍ⊗ₜ[K] y₁)
          + toC (x₁ ᵍ⊗ₜ[K] y₀) + toC (x₁ ᵍ⊗ₜ[K] y₁) :=
      hab'
    rw [hab]
    simp only [map_add]
    rw [gtensorComm_natural_hom e f hx0 hy0, gtensorComm_natural_hom e f hx0 hy1,
      gtensorComm_natural_hom e f hx1 hy0, gtensorComm_natural_hom e f hx1 hy1]
  exact AlgHom.congr_fun hhom w

/-- Entrywise, a homogeneous congruence on the non-matrix slot fixes
`matrixInclLeft` (since it sends `1 ↦ 1`). -/
private theorem mapMatrix_matrixInclLeft {P Q Q' : SuperAlgebra K}
    (f : SuperAlgEquiv Q Q') (n : Type*) [Fintype n] [DecidableEq n]
    (M : Matrix n n P.carrier) :
    (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
        Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P.gtensor Q').carrier)
        (matrixInclLeft P.grading Q.grading M)
      = matrixInclLeft P.grading Q'.grading M := by
  refine Matrix.ext fun r s => ?_
  rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply, matrixInclLeft_apply,
    matrixInclLeft_apply]
  have h := gtensorCongr_tmul'' (SuperAlgEquiv.refl P) f (M r s) (1 : Q.carrier)
  rw [show (SuperAlgEquiv.refl P).toAlgEquiv (M r s) = M r s from rfl,
    show f.toAlgEquiv (1 : Q.carrier) = 1 from map_one f.toAlgEquiv] at h
  exact h

/-- Entrywise, a homogeneous congruence on the non-matrix slot
carries `matrixInclRight y` to `matrixInclRight (f y)` (the signed
diagonal commutes with a homogeneous congruence, since it commutes
with the even/odd parity projections). -/
private theorem mapMatrix_matrixInclRight {P Q Q' : SuperAlgebra K}
    (f : SuperAlgEquiv Q Q') (n : Type*) [Fintype n] [DecidableEq n]
    (π : n → ZMod 2) (y : Q.carrier) :
    (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
        Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P.gtensor Q').carrier)
        (matrixInclRight π P.grading Q.grading y)
      = matrixInclRight π P.grading Q'.grading (f.toAlgEquiv y) := by
  -- reduce to homogeneous `y` via the even/odd decomposition
  have hy := evenPart_add_oddPart Q.grading y
  have hy0 : evenPart Q.grading y ∈ Q.grading 0 := evenPart_mem Q.grading y
  have hy1 : oddPart Q.grading y ∈ Q.grading 1 := oddPart_mem Q.grading y
  have hfy0 : f.toAlgEquiv (evenPart Q.grading y) ∈ Q'.grading 0 := by
    rw [← f.map_grading 0]; exact Submodule.mem_map_of_mem hy0
  have hfy1 : f.toAlgEquiv (oddPart Q.grading y) ∈ Q'.grading 1 := by
    rw [← f.map_grading 1]; exact Submodule.mem_map_of_mem hy1
  have hsplit : ∀ (j : ZMod 2) (z : Q.carrier), z ∈ Q.grading j →
      (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
          Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading z)
        = matrixInclRight π P.grading Q'.grading (f.toAlgEquiv z) := by
    intro j z hz
    have hfz : f.toAlgEquiv z ∈ Q'.grading j := by
      rw [← f.map_grading j]; exact Submodule.mem_map_of_mem hz
    have h := gtensorCongr_tmul'' (SuperAlgEquiv.refl P) f (1 : P.carrier) z
    rw [show (SuperAlgEquiv.refl P).toAlgEquiv (1 : P.carrier) = 1 from rfl] at h
    refine Matrix.ext fun r s => ?_
    rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply, matrixInclRight_apply,
      matrixInclRight_apply, sdiag_of_mem π P.grading Q.grading hz,
      sdiag_of_mem π P.grading Q'.grading hfz, Matrix.diagonal_apply,
      Matrix.diagonal_apply]
    by_cases hrs : r = s
    · rw [if_pos hrs, if_pos hrs]
      have huz : (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv
            (((sgn (π r * j) : ℤˣ) : ℤ) • toC ((1 : P.carrier) ᵍ⊗ₜ[K] z)))
          = ((sgn (π r * j) : ℤˣ) : ℤ) •
            (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv
              (toC ((1 : P.carrier) ᵍ⊗ₜ[K] z))) :=
        map_zsmul (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.toAlgHom) _ _
      show ((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv
          (((sgn (π r * j) : ℤˣ) : ℤ) • toC ((1 : P.carrier) ᵍ⊗ₜ[K] z))
        = ((sgn (π r * j) : ℤˣ) : ℤ) • toC ((1 : P.carrier) ᵍ⊗ₜ[K] f.toAlgEquiv z)
      rw [huz, h]
    · rw [if_neg hrs, if_neg hrs]
      show ((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.toAlgHom
          (toC (0 : P.grading ᵍ⊗[K] Q.grading))
        = toC (0 : P.grading ᵍ⊗[K] Q'.grading)
      exact map_zero _
  have hyR : matrixInclRight π P.grading Q.grading y
      = matrixInclRight π P.grading Q.grading (evenPart Q.grading y)
        + matrixInclRight π P.grading Q.grading (oddPart Q.grading y) := by
    rw [← map_add, hy]
  have hfyR : matrixInclRight π P.grading Q'.grading (f.toAlgEquiv y)
      = matrixInclRight π P.grading Q'.grading (f.toAlgEquiv (evenPart Q.grading y))
        + matrixInclRight π P.grading Q'.grading (f.toAlgEquiv (oddPart Q.grading y)) := by
    rw [← map_add, ← map_add, hy]
  calc (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
        Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading y)
      = (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading (evenPart Q.grading y)
            + matrixInclRight π P.grading Q.grading (oddPart Q.grading y)) := by
        rw [hyR]
    _ = (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading (evenPart Q.grading y))
        + (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading (oddPart Q.grading y)) :=
        map_add _ _ _
    _ = matrixInclRight π P.grading Q'.grading (f.toAlgEquiv (evenPart Q.grading y))
        + matrixInclRight π P.grading Q'.grading (f.toAlgEquiv (oddPart Q.grading y)) := by
        rw [hsplit 0 _ hy0, hsplit 1 _ hy1]
        rfl
    _ = matrixInclRight π P.grading Q'.grading (f.toAlgEquiv y) := by rw [hfyR]

/-- Naturality of the matrix-stabilization compatibility in the
non-matrix slot, applied form. -/
theorem matrixSuperGtensor_natural_apply {P Q Q' : SuperAlgebra K}
    (f : SuperAlgEquiv Q Q') (p q : ℕ)
    (w : ((P.matrixSuper p q).gtensor Q).carrier) :
    (matrixSuperGtensor P Q' p q).toAlgEquiv
        (((SuperAlgEquiv.refl (P.matrixSuper p q)).gtensorCongr
          f).toAlgEquiv w)
      = (((SuperAlgEquiv.refl P).gtensorCongr f).matrixSuper
          p q).toAlgEquiv
        ((matrixSuperGtensor P Q p q).toAlgEquiv w) := by
  have hhom : ((matrixSuperGtensor P Q' p q).toAlgEquiv.toAlgHom).comp
        (((SuperAlgEquiv.refl (P.matrixSuper p q)).gtensorCongr
          f).toAlgEquiv.toAlgHom)
      = ((((SuperAlgEquiv.refl P).gtensorCongr f).matrixSuper
          p q).toAlgEquiv.toAlgHom).comp
        ((matrixSuperGtensor P Q p q).toAlgEquiv.toAlgHom) := by
    refine galgHom_ext (P.matrixSuper p q).grading Q.grading ?_
    intro M₀ y
    -- work with `M` at the raw `Matrix` type throughout, to avoid the
    -- `(P.matrixSuper p q).carrier` synonym defeating `rw`'s matching
    set M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier := M₀ with hM₀
    change (matrixSuperGtensor P Q' p q).toAlgEquiv
        (((SuperAlgEquiv.refl (P.matrixSuper p q)).gtensorCongr
          f).toAlgEquiv (toC (M ᵍ⊗ₜ[K] y)))
      = (((SuperAlgEquiv.refl P).gtensorCongr f).matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensor P Q p q).toAlgEquiv (toC (M ᵍ⊗ₜ[K] y)))
    -- unfold the congruence on the source: `refl` on the matrix slot
    have hlhs1 : (((SuperAlgEquiv.refl (P.matrixSuper p q)).gtensorCongr
          f).toAlgEquiv (toC (M ᵍ⊗ₜ[K] y)))
        = toC (M ᵍ⊗ₜ[K] f.toAlgEquiv y) := by
      have h := gtensorCongr_tmul'' (SuperAlgEquiv.refl (P.matrixSuper p q)) f M y
      rwa [show (SuperAlgEquiv.refl (P.matrixSuper p q)).toAlgEquiv M = M
          from rfl] at h
    rw [hlhs1]
    -- both `matrixSuperGtensor` applications unfold via `matrixTensorSuperHom_tmul`
    have hlhs2 : (matrixSuperGtensor P Q' p q).toAlgEquiv (toC (M ᵍ⊗ₜ[K] f.toAlgEquiv y))
        = matrixInclLeft P.grading Q'.grading M
          * matrixInclRight (sumParity p q) P.grading Q'.grading (f.toAlgEquiv y) := by
      show matrixTensorSuperHom (sumParity p q) P.grading Q'.grading
          (M ᵍ⊗ₜ[K] f.toAlgEquiv y)
        = matrixInclLeft P.grading Q'.grading M
          * matrixInclRight (sumParity p q) P.grading Q'.grading (f.toAlgEquiv y)
      exact matrixTensorSuperHom_tmul (sumParity p q) P.grading Q'.grading M
        (f.toAlgEquiv y)
    have hrhs1 : (matrixSuperGtensor P Q p q).toAlgEquiv (toC (M ᵍ⊗ₜ[K] y))
        = matrixInclLeft P.grading Q.grading M
          * matrixInclRight (sumParity p q) P.grading Q.grading y := by
      show matrixTensorSuperHom (sumParity p q) P.grading Q.grading (M ᵍ⊗ₜ[K] y)
        = matrixInclLeft P.grading Q.grading M
          * matrixInclRight (sumParity p q) P.grading Q.grading y
      exact matrixTensorSuperHom_tmul (sumParity p q) P.grading Q.grading M y
    rw [hlhs2, hrhs1]
    -- the outer map is `mapMatrix` of the congruence, entrywise
    have hprod : (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
            ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q').carrier)
        (matrixInclLeft P.grading Q.grading M
          * matrixInclRight (sumParity p q) P.grading Q.grading y)
      = (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
              ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q').carrier)
          (matrixInclLeft P.grading Q.grading M)
        * (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
              ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q').carrier)
          (matrixInclRight (sumParity p q) P.grading Q.grading y) :=
      map_mul _ _ _
    show matrixInclLeft P.grading Q'.grading M
        * matrixInclRight (sumParity p q) P.grading Q'.grading (f.toAlgEquiv y)
      = (((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
              ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q').carrier)
          (matrixInclLeft P.grading Q.grading M
            * matrixInclRight (sumParity p q) P.grading Q.grading y)
    rw [hprod, mapMatrix_matrixInclLeft f (Fin p ⊕ Fin q) M,
      mapMatrix_matrixInclRight f (Fin p ⊕ Fin q) (sumParity p q) y]
    rfl
  exact AlgHom.congr_fun hhom w

end MatrixNat

end Superfusion

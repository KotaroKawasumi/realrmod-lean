import Superfusion.Super.PentagonMatrixNat2

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section Coherence

set_option maxRecDepth 4000

universe u

variable {K : Type u} [CommRing K]

private def toC3 {P Q : SuperAlgebra K}
    (x : P.grading ᵍ⊗[K] Q.grading) : (P.gtensor Q).carrier := x

private theorem gtensorCongr_tmul3 {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (a : P.carrier) (b : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv (toC3 (a ᵍ⊗ₜ[K] b))
      = toC3 (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading e.toAlgEquiv
    f.toAlgEquiv e.map_grading f.map_grading a b

/-- Scalars pull out of the right slot of a pure tensor in `ᵍ⊗ₜ`. -/
private theorem gtmul_zsmul3 {P Q : SuperAlgebra K} (n : ℤ) (x : P.carrier)
    (y : Q.carrier) :
    (x ᵍ⊗ₜ[K] (n • y) : P.grading ᵍ⊗[K] Q.grading) = n • (x ᵍ⊗ₜ[K] y) := by
  rw [show ((x ᵍ⊗ₜ[K] (n • y) : P.grading ᵍ⊗[K] Q.grading))
      = of K P.grading Q.grading (x ⊗ₜ[K] (n • y)) from rfl,
    show (x ⊗ₜ[K] (n • y) : P.carrier ⊗[K] Q.carrier) = n • (x ⊗ₜ[K] y) from by
      rw [← TensorProduct.smul_tmul]
      exact (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

/-- Entrywise, the outer `.matrixSuper p' q'` of `mSG X D p q` carries
`matrixInclLeft N` to the entrywise `matrixInclLeft` of `N` (each
entry `N r s` gets pushed through `mSG X D p q` via `matrixInclLeft`,
since `matrixInclRight 1 = 1`). -/
private theorem matrixSuper_mSG_matrixInclLeft {X D : SuperAlgebra K}
    (p q p' q' : ℕ)
    (N : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q')
      (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) X.carrier)) :
    ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
        (matrixInclLeft (X.matrixSuper p q).grading D.grading N)
      = N.map (fun M => matrixInclLeft X.grading D.grading M) := by
  show ((matrixInclLeft (X.matrixSuper p q).grading D.grading N).map
    (matrixSuperGtensor X D p q).toAlgEquiv) = N.map (fun M => matrixInclLeft X.grading D.grading M)
  refine Matrix.ext fun r s => ?_
  rw [Matrix.map_apply, matrixInclLeft_apply, Matrix.map_apply]
  show (matrixSuperGtensor X D p q).toAlgEquiv (toC3 (N r s ᵍ⊗ₜ[K] (1 : D.carrier)))
    = matrixInclLeft X.grading D.grading (N r s)
  rw [show (matrixSuperGtensor X D p q).toAlgEquiv (toC3 (N r s ᵍ⊗ₜ[K] (1 : D.carrier)))
      = matrixTensorSuperHom (sumParity p q) X.grading D.grading (N r s ᵍ⊗ₜ[K] (1 : D.carrier))
      from rfl,
    matrixTensorSuperHom_tmul, map_one, mul_one]

/-- Entrywise, the outer `.matrixSuper p' q'` of `mSG X D p q` carries
`matrixInclRight y` to the diagonal matrix of `matrixInclRight y`
constants, signed by the outer index parity (each diagonal entry
`(sgn(π' s) : ...) • (1 ᵍ⊗ y)`, which under `mSG X D p q` is
`matrixInclRight` of the very same scalar multiple of `y`, by
`ℤˣ`-linearity of `mSG`). -/
private theorem matrixSuper_mSG_matrixInclRight_hom {X D : SuperAlgebra K}
    (p q p' q' : ℕ) {j : ZMod 2} {y : D.carrier} (hy : y ∈ D.grading j) :
    ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
        (matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading
          D.grading y)
      = Matrix.diagonal (fun s : Fin p' ⊕ Fin q' =>
          ((sgn (sumParity p' q' s * j) : ℤˣ) : ℤ) •
            matrixInclRight (sumParity p q) X.grading D.grading y) := by
  show ((matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading y).map
    (matrixSuperGtensor X D p q).toAlgEquiv) = _
  refine Matrix.ext fun r s => ?_
  rw [Matrix.map_apply, matrixInclRight_apply,
    sdiag_of_mem (sumParity p' q') (X.matrixSuper p q).grading D.grading hy,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hrs : r = s
  · rw [if_pos hrs, if_pos hrs]
    show (matrixSuperGtensor X D p q).toAlgEquiv
        (((sgn (sumParity p' q' r * j) : ℤˣ) : ℤ) •
          toC3 ((1 : (X.matrixSuper p q).carrier) ᵍ⊗ₜ[K] y))
      = ((sgn (sumParity p' q' r * j) : ℤˣ) : ℤ) •
        matrixInclRight (sumParity p q) X.grading D.grading y
    rw [map_zsmul]
    congr 1
    show matrixTensorSuperHom (sumParity p q) X.grading D.grading
        ((1 : (X.matrixSuper p q).carrier) ᵍ⊗ₜ[K] y)
      = matrixInclRight (sumParity p q) X.grading D.grading y
    rw [matrixTensorSuperHom_tmul,
      show (1 : (X.matrixSuper p q).carrier)
          = (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) X.carrier) from rfl,
      map_one, one_mul]
  · rw [if_neg hrs, if_neg hrs]
    show (matrixSuperGtensor X D p q).toAlgEquiv (toC3 (0 : (X.matrixSuper p q).grading
        ᵍ⊗[K] D.grading)) = 0
    rw [show (toC3 (0 : (X.matrixSuper p q).grading ᵍ⊗[K] D.grading))
        = (0 : ((X.matrixSuper p q).gtensor D).carrier) from rfl, map_zero]

/-- Entrywise, the outer `.matrixSuper p' q'` of `mSG X D p q` carries
`matrixInclRight y` to the diagonal matrix whose `s`-entry is
`matrixInclRight` of `evenPart y + sgn(π' s) • oddPart y` — via
reduction to the homogeneous case `matrixSuper_mSG_matrixInclRight_hom`
on the even/odd parts of `y`. -/
private theorem matrixSuper_mSG_matrixInclRight {X D : SuperAlgebra K}
    (p q p' q' : ℕ) (y : D.carrier) :
    ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
        (matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading
          D.grading y)
      = Matrix.diagonal (fun s : Fin p' ⊕ Fin q' =>
          matrixInclRight (sumParity p q) X.grading D.grading
            (evenPart D.grading y
              + ((sgn (sumParity p' q' s) : ℤˣ) : ℤ) • oddPart D.grading y)) := by
  have hy := evenPart_add_oddPart D.grading y
  have hy0 : evenPart D.grading y ∈ D.grading 0 := evenPart_mem D.grading y
  have hy1 : oddPart D.grading y ∈ D.grading 1 := oddPart_mem D.grading y
  have hR : matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading y
      = matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading
          (evenPart D.grading y)
        + matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading
          (oddPart D.grading y) := by rw [← map_add, hy]
  rw [hR]
  have hsplit : ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
        (matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading
            (evenPart D.grading y)
          + matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading
            (oddPart D.grading y))
      = ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
          (matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading
            (evenPart D.grading y))
        + ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
          (matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading D.grading
            (oddPart D.grading y)) := map_add _ _ _
  rw [hsplit,
    matrixSuper_mSG_matrixInclRight_hom p q p' q' hy0,
    matrixSuper_mSG_matrixInclRight_hom p q p' q' hy1]
  refine Matrix.ext fun r s => ?_
  show (Matrix.diagonal (fun s : Fin p' ⊕ Fin q' => ((sgn (sumParity p' q' s * 0) : ℤˣ) : ℤ) •
        matrixInclRight (sumParity p q) X.grading D.grading (evenPart D.grading y))
      + Matrix.diagonal (fun s : Fin p' ⊕ Fin q' => ((sgn (sumParity p' q' s * 1) : ℤˣ) : ℤ) •
        matrixInclRight (sumParity p q) X.grading D.grading (oddPart D.grading y))) r s
    = Matrix.diagonal (fun s : Fin p' ⊕ Fin q' =>
        matrixInclRight (sumParity p q) X.grading D.grading
          (evenPart D.grading y
            + ((sgn (sumParity p' q' s) : ℤˣ) : ℤ) • oddPart D.grading y)) r s
  rw [Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hrs : r = s
  · rw [if_pos hrs, if_pos hrs, if_pos hrs, mul_zero, sgn_zero,
      show (((1 : ℤˣ) : ℤ)) = 1 from rfl, one_smul, mul_one,
      map_add, map_zsmul]
  · rw [if_neg hrs, if_neg hrs, if_neg hrs, add_zero]

/-- Collapsing nested matrix sizes commutes with distributing over
the graded tensor product (left version). -/
theorem matrixSuperComp_gtensor_apply {X D : SuperAlgebra K}
    (p q p' q' : ℕ)
    (w : (((X.matrixSuper p q).matrixSuper p' q').gtensor D).carrier) :
    (matrixSuperGtensor X D (p' * p + q' * q)
        (p' * q + q' * p)).toAlgEquiv
        (((matrixSuperComp X p' q' p q).gtensorCongr
          (SuperAlgEquiv.refl D)).toAlgEquiv w)
      = (matrixSuperComp (X.gtensor D) p' q' p q).toAlgEquiv
        (((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
          ((matrixSuperGtensor (X.matrixSuper p q) D
            p' q').toAlgEquiv w)) := by
  have hhom : ((matrixSuperGtensor X D (p' * p + q' * q)
        (p' * q + q' * p)).toAlgEquiv.toAlgHom).comp
        (((matrixSuperComp X p' q' p q).gtensorCongr
          (SuperAlgEquiv.refl D)).toAlgEquiv.toAlgHom)
      = ((matrixSuperComp (X.gtensor D) p' q' p q).toAlgEquiv.toAlgHom).comp
        ((((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv.toAlgHom).comp
          ((matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv.toAlgHom)) := by
    refine galgHom_ext ((X.matrixSuper p q).matrixSuper p' q').grading D.grading ?_
    intro N₀ y
    set N : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q')
        (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) X.carrier) := N₀ with hN₀
    change (matrixSuperGtensor X D (p' * p + q' * q) (p' * q + q' * p)).toAlgEquiv
        (((matrixSuperComp X p' q' p q).gtensorCongr
          (SuperAlgEquiv.refl D)).toAlgEquiv (toC3 (N ᵍ⊗ₜ[K] y)))
      = (matrixSuperComp (X.gtensor D) p' q' p q).toAlgEquiv
        (((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
          ((matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv (toC3 (N ᵍ⊗ₜ[K] y))))
    -- LHS: unfold `comp ⊗c refl` on the pure tensor, then `mSG`.
    have hlhs1 : ((matrixSuperComp X p' q' p q).gtensorCongr
          (SuperAlgEquiv.refl D)).toAlgEquiv (toC3 (N ᵍ⊗ₜ[K] y))
        = toC3 (((matrixSuperComp X p' q' p q).toAlgEquiv N) ᵍ⊗ₜ[K] y) := by
      have h := gtensorCongr_tmul3 (matrixSuperComp X p' q' p q)
        (SuperAlgEquiv.refl D) N y
      rwa [show (SuperAlgEquiv.refl D).toAlgEquiv y = y from rfl] at h
    rw [hlhs1]
    have hlhs2 : (matrixSuperGtensor X D (p' * p + q' * q)
          (p' * q + q' * p)).toAlgEquiv
          (toC3 (((matrixSuperComp X p' q' p q).toAlgEquiv N) ᵍ⊗ₜ[K] y))
        = matrixInclLeft X.grading D.grading
            ((matrixSuperComp X p' q' p q).toAlgEquiv N)
          * matrixInclRight (sumParity (p' * p + q' * q) (p' * q + q' * p))
            X.grading D.grading y := by
      show matrixTensorSuperHom (sumParity (p' * p + q' * q) (p' * q + q' * p))
          X.grading D.grading
          (((matrixSuperComp X p' q' p q).toAlgEquiv N) ᵍ⊗ₜ[K] y)
        = matrixInclLeft X.grading D.grading
            ((matrixSuperComp X p' q' p q).toAlgEquiv N)
          * matrixInclRight (sumParity (p' * p + q' * q) (p' * q + q' * p))
            X.grading D.grading y
      exact matrixTensorSuperHom_tmul
        (sumParity (p' * p + q' * q) (p' * q + q' * p)) X.grading D.grading
        ((matrixSuperComp X p' q' p q).toAlgEquiv N) y
    rw [hlhs2]
    -- RHS: unfold the innermost `mSG`, then the entrywise `.matrixSuper`,
    -- then `matrixSuperComp`.
    have hrhs1 : (matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv
          (toC3 (N ᵍ⊗ₜ[K] y))
        = matrixInclLeft (X.matrixSuper p q).grading D.grading N
          * matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading
            D.grading y := by
      show matrixTensorSuperHom (sumParity p' q') (X.matrixSuper p q).grading
          D.grading (N ᵍ⊗ₜ[K] y)
        = matrixInclLeft (X.matrixSuper p q).grading D.grading N
          * matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading
            D.grading y
      exact matrixTensorSuperHom_tmul (sumParity p' q')
        (X.matrixSuper p q).grading D.grading N y
    rw [hrhs1]
    have hrhs2 : ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
          (matrixInclLeft (X.matrixSuper p q).grading D.grading N
            * matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading
              D.grading y)
        = ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
            (matrixInclLeft (X.matrixSuper p q).grading D.grading N)
          * ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
            (matrixInclRight (sumParity p' q') (X.matrixSuper p q).grading
              D.grading y) := map_mul _ _ _
    rw [hrhs2, matrixSuper_mSG_matrixInclLeft p q p' q' N,
      matrixSuper_mSG_matrixInclRight p q p' q' y]
    -- Now both sides are entrywise expressions at the collapsed index
    -- type; unfold `matrixSuperComp` (LHS: applied to a single matrix;
    -- RHS: applied to the product) and compare entries.
    set L : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q')
        (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (X.gtensor D).carrier) :=
      N.map (fun M => matrixInclLeft X.grading D.grading M)
        * Matrix.diagonal (fun s : Fin p' ⊕ Fin q' =>
          matrixInclRight (sumParity p q) X.grading D.grading
            (evenPart D.grading y
              + ((sgn (sumParity p' q' s) : ℤˣ) : ℤ) • oddPart D.grading y))
      with hL
    show (matrixInclLeft X.grading D.grading
        ((matrixSuperComp X p' q' p q).toAlgEquiv N)
      * matrixInclRight (sumParity (p' * p + q' * q) (p' * q + q' * p))
        X.grading D.grading y)
      = (matrixSuperComp (X.gtensor D) p' q' p q).toAlgEquiv L
    refine Matrix.ext fun a b => ?_
    rcases hra : (collapseIndexEquiv p' q' p q).symm a with ⟨r₁, c₁⟩
    rcases hrb : (collapseIndexEquiv p' q' p q).symm b with ⟨r₂, c₂⟩
    have ha : a = (collapseIndexEquiv p' q' p q) (r₁, c₁) := by
      rw [← hra, (collapseIndexEquiv p' q' p q).apply_symm_apply]
    have hb : b = (collapseIndexEquiv p' q' p q) (r₂, c₂) := by
      rw [← hrb, (collapseIndexEquiv p' q' p q).apply_symm_apply]
    rw [ha, hb]
    -- LHS entry, via `matrixInclLeft_mul_matrixInclRight_apply`-style
    -- computation and the raw unfolding of `matrixSuperComp`.
    have hLHS : (matrixInclLeft X.grading D.grading
          ((matrixSuperComp X p' q' p q).toAlgEquiv N)
        * matrixInclRight (sumParity (p' * p + q' * q) (p' * q + q' * p))
          X.grading D.grading y)
        ((collapseIndexEquiv p' q' p q) (r₁, c₁))
        ((collapseIndexEquiv p' q' p q) (r₂, c₂))
      = matrixInclLeft X.grading D.grading (N r₁ r₂) c₁ c₂
        * ((1 : X.carrier) ᵍ⊗ₜ[K] (evenPart D.grading y)
            + ((sgn (sumParity (p' * p + q' * q) (p' * q + q' * p)
                ((collapseIndexEquiv p' q' p q) (r₂, c₂))) : ℤˣ) : ℤ)
              • ((1 : X.carrier) ᵍ⊗ₜ[K] (oddPart D.grading y))) := by
      have h1 : matrixInclLeft X.grading D.grading
            ((matrixSuperComp X p' q' p q).toAlgEquiv N)
          ((collapseIndexEquiv p' q' p q) (r₁, c₁))
          ((collapseIndexEquiv p' q' p q) (r₂, c₂))
        = matrixInclLeft X.grading D.grading (N r₁ r₂) c₁ c₂ := by
        rw [matrixInclLeft_apply, matrixInclLeft_apply]
        congr 1
        show (Matrix.reindexAlgEquiv K X.carrier (collapseIndexEquiv p' q' p q))
            ((Matrix.compAlgEquiv (Fin p' ⊕ Fin q') (Fin p ⊕ Fin q) X.carrier K) N)
            ((collapseIndexEquiv p' q' p q) (r₁, c₁))
            ((collapseIndexEquiv p' q' p q) (r₂, c₂)) = N r₁ r₂ c₁ c₂
        rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.compAlgEquiv_apply,
          Matrix.comp_apply]
      have h : (matrixInclLeft X.grading D.grading
            ((matrixSuperComp X p' q' p q).toAlgEquiv N)
          * matrixInclRight (sumParity (p' * p + q' * q) (p' * q + q' * p))
            X.grading D.grading y)
          = (matrixInclLeft X.grading D.grading
              ((matrixSuperComp X p' q' p q).toAlgEquiv N)
            * Matrix.diagonal (fun s : Fin (p' * p + q' * q) ⊕ Fin (p' * q + q' * p) =>
                (1 : X.carrier) ᵍ⊗ₜ[K] (evenPart D.grading y)
                  + ((sgn (sumParity (p' * p + q' * q) (p' * q + q' * p) s) : ℤˣ) : ℤ)
                    • ((1 : X.carrier) ᵍ⊗ₜ[K] (oddPart D.grading y)))) := rfl
      rw [h, Matrix.mul_diagonal, h1]
    rw [hLHS]
    -- RHS entry, via `matrixSuperComp_natural_apply`-style unfolding of
    -- `matrixSuperComp (X.gtensor D) p' q' p q` and the outer-level
    -- `Matrix.mul_diagonal`.
    have hRHS : (matrixSuperComp (X.gtensor D) p' q' p q).toAlgEquiv L
        ((collapseIndexEquiv p' q' p q) (r₁, c₁))
        ((collapseIndexEquiv p' q' p q) (r₂, c₂))
      = L r₁ r₂ c₁ c₂ := by
      show (Matrix.reindexAlgEquiv K (X.gtensor D).carrier (collapseIndexEquiv p' q' p q))
          ((Matrix.compAlgEquiv (Fin p' ⊕ Fin q') (Fin p ⊕ Fin q) (X.gtensor D).carrier K) L)
          ((collapseIndexEquiv p' q' p q) (r₁, c₁))
          ((collapseIndexEquiv p' q' p q) (r₂, c₂)) = L r₁ r₂ c₁ c₂
      rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.compAlgEquiv_apply,
        Matrix.comp_apply]
    rw [hRHS, hL]
    have hL' : (N.map (fun M => matrixInclLeft X.grading D.grading M)
          * Matrix.diagonal (fun s : Fin p' ⊕ Fin q' =>
            matrixInclRight (sumParity p q) X.grading D.grading
              (evenPart D.grading y
                + ((sgn (sumParity p' q' s) : ℤˣ) : ℤ) • oddPart D.grading y))) r₁ r₂
        = matrixInclLeft X.grading D.grading (N r₁ r₂)
          * matrixInclRight (sumParity p q) X.grading D.grading
              (evenPart D.grading y
                + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y) := by
      rw [Matrix.mul_diagonal, Matrix.map_apply]
    rw [hL']
    have hentry : (matrixInclLeft X.grading D.grading (N r₁ r₂)
          * matrixInclRight (sumParity p q) X.grading D.grading
              (evenPart D.grading y
                + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y)) c₁ c₂
        = matrixInclLeft X.grading D.grading (N r₁ r₂) c₁ c₂
          * ((1 : X.carrier) ᵍ⊗ₜ[K]
              (evenPart D.grading (evenPart D.grading y
                + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y))
            + ((sgn (sumParity p q c₂) : ℤˣ) : ℤ) •
              ((1 : X.carrier) ᵍ⊗ₜ[K]
                (oddPart D.grading (evenPart D.grading y
                  + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y)))) := by
      have h : (matrixInclLeft X.grading D.grading (N r₁ r₂)
            * matrixInclRight (sumParity p q) X.grading D.grading
                (evenPart D.grading y
                  + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y))
          = (matrixInclLeft X.grading D.grading (N r₁ r₂)
            * Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
                (1 : X.carrier) ᵍ⊗ₜ[K]
                    (evenPart D.grading (evenPart D.grading y
                      + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y))
                  + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                    ((1 : X.carrier) ᵍ⊗ₜ[K]
                      (oddPart D.grading (evenPart D.grading y
                        + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y))))) := rfl
      rw [h, Matrix.mul_diagonal]
    rw [hentry]
    congr 1
    have hev : evenPart D.grading (evenPart D.grading y
        + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y)
        = evenPart D.grading y := by
      rw [map_add, map_zsmul, evenPart_of_mem_zero D.grading (evenPart_mem D.grading y),
        evenPart_of_mem_one D.grading (oddPart_mem D.grading y), smul_zero, add_zero]
    have hod : oddPart D.grading (evenPart D.grading y
        + ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y)
        = ((sgn (sumParity p' q' r₂) : ℤˣ) : ℤ) • oddPart D.grading y := by
      rw [map_add, map_zsmul, oddPart_of_mem_zero D.grading (evenPart_mem D.grading y),
        oddPart_of_mem_one D.grading (oddPart_mem D.grading y), zero_add]
    rw [hev, hod, gtmul_zsmul3, smul_smul,
      ← collapseIndexEquiv_parity p' q' p q (r₂, c₂), sgn_add]
    congr 2
    push_cast
    ring
  exact AlgHom.congr_fun hhom w

/-- Entrywise, `.matrixSuper` carries the braiding-naturality square
(a local re-derivation of the private lemma of the same name in
`PentagonMatrixNat2.lean`, needed here to commute `.matrixSuper`
of `gtensorComm` past `matrixSuperComp` naturality). -/
private theorem matrixSuper_gtensorComm_natural_apply3
    {A A' B B' : SuperAlgebra K}
    (g : SuperAlgEquiv A A') (h : SuperAlgEquiv B B') (p q : ℕ)
    (N : ((A.gtensor B).matrixSuper p q).carrier) :
    ((gtensorComm A' B').matrixSuper p q).toAlgEquiv
        (((g.gtensorCongr h).matrixSuper p q).toAlgEquiv N)
      = ((h.gtensorCongr g).matrixSuper p q).toAlgEquiv
        (((gtensorComm A B).matrixSuper p q).toAlgEquiv N) := by
  set N' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (A.gtensor B).carrier := N with hN'
  show (N'.map (g.gtensorCongr h).toAlgEquiv).map (gtensorComm A' B').toAlgEquiv
    = (N'.map (gtensorComm A B).toAlgEquiv).map (h.gtensorCongr g).toAlgEquiv
  rw [Matrix.map_map, Matrix.map_map]
  refine Matrix.ext fun r s => ?_
  simp only [Matrix.map_apply, Function.comp_apply]
  exact gtensorComm_natural_apply g h (N' r s)

/-- Collapsing nested matrix sizes commutes with distributing over
the graded tensor product (right version) — derived from the
braiding naturality, the left version `matrixSuperComp_gtensor_apply`,
and the functoriality of matrix stabilization, following the
derivation of `matrixSuperGtensorRight_full_natural_apply` from
`matrixSuperGtensor_full_natural_apply`. -/
theorem matrixSuperComp_gtensorRight_apply {X D : SuperAlgebra K}
    (p q p' q' : ℕ)
    (w : (D.gtensor
      ((X.matrixSuper p q).matrixSuper p' q')).carrier) :
    (matrixSuperGtensorRight D X (p' * p + q' * q)
        (p' * q + q' * p)).toAlgEquiv
        (((SuperAlgEquiv.refl D).gtensorCongr
          (matrixSuperComp X p' q' p q)).toAlgEquiv w)
      = (matrixSuperComp (D.gtensor X) p' q' p q).toAlgEquiv
        (((matrixSuperGtensorRight D X p q).matrixSuper
          p' q').toAlgEquiv
          ((matrixSuperGtensorRight D (X.matrixSuper p q)
            p' q').toAlgEquiv w)) := by
  -- unfold both `matrixSuperGtensorRight`s to `gtensorComm ≫ mSG ≫
  -- (gtensorComm).matrixSuper`
  show ((gtensorComm X D).matrixSuper (p' * p + q' * q) (p' * q + q' * p)).toAlgEquiv
        ((matrixSuperGtensor X D (p' * p + q' * q) (p' * q + q' * p)).toAlgEquiv
          ((gtensorComm D (X.matrixSuper (p' * p + q' * q) (p' * q + q' * p))).toAlgEquiv
            (((SuperAlgEquiv.refl D).gtensorCongr
              (matrixSuperComp X p' q' p q)).toAlgEquiv w)))
      = (matrixSuperComp (D.gtensor X) p' q' p q).toAlgEquiv
        ((((gtensorComm D (X.matrixSuper p q)).trans
              ((matrixSuperGtensor X D p q).trans
                ((gtensorComm X D).matrixSuper p q))).matrixSuper p' q').toAlgEquiv
          (((gtensorComm D ((X.matrixSuper p q).matrixSuper p' q')).trans
            ((matrixSuperGtensor (X.matrixSuper p q) D p' q').trans
              ((gtensorComm (X.matrixSuper p q) D).matrixSuper p' q'))).toAlgEquiv w))
  -- push `gtensorComm D` through the congruence via braiding naturality
  set w1 : (((X.matrixSuper p q).matrixSuper p' q').gtensor D).carrier :=
      (gtensorComm D ((X.matrixSuper p q).matrixSuper p' q')).toAlgEquiv w
    with hw1
  have hstep1 : (gtensorComm D (X.matrixSuper (p' * p + q' * q) (p' * q + q' * p))).toAlgEquiv
        (((SuperAlgEquiv.refl D).gtensorCongr
          (matrixSuperComp X p' q' p q)).toAlgEquiv w)
      = ((matrixSuperComp X p' q' p q).gtensorCongr
          (SuperAlgEquiv.refl D)).toAlgEquiv w1 :=
    gtensorComm_natural_apply (SuperAlgEquiv.refl D) (matrixSuperComp X p' q' p q) w
  rw [hstep1]
  -- apply the left version to `w1`
  rw [matrixSuperComp_gtensor_apply p q p' q' w1]
  -- reduce the RHS's `.trans` compositions entrywise, then apply
  -- `matrixSuperComp_natural_apply` (naturality in `e := gtensorComm X D`)
  -- to relate the `matrixSuperComp (D.gtensor X)` postcomposite to
  -- `matrixSuperComp (X.gtensor D)` conjugated by `(gtensorComm X D)`
  set u : (((X.gtensor D).matrixSuper p q).matrixSuper p' q').carrier :=
      ((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
        ((matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv w1)
    with hu
  show ((gtensorComm X D).matrixSuper (p' * p + q' * q) (p' * q + q' * p)).toAlgEquiv
      ((matrixSuperComp (X.gtensor D) p' q' p q).toAlgEquiv u)
      = (matrixSuperComp (D.gtensor X) p' q' p q).toAlgEquiv
        ((((gtensorComm D (X.matrixSuper p q)).trans
              ((matrixSuperGtensor X D p q).trans
                ((gtensorComm X D).matrixSuper p q))).matrixSuper p' q').toAlgEquiv
          (((gtensorComm D ((X.matrixSuper p q).matrixSuper p' q')).trans
            ((matrixSuperGtensor (X.matrixSuper p q) D p' q').trans
              ((gtensorComm (X.matrixSuper p q) D).matrixSuper p' q'))).toAlgEquiv w))
  have hv : ((((gtensorComm D (X.matrixSuper p q)).trans
              ((matrixSuperGtensor X D p q).trans
                ((gtensorComm X D).matrixSuper p q))).matrixSuper p' q').toAlgEquiv
          (((gtensorComm D ((X.matrixSuper p q).matrixSuper p' q')).trans
            ((matrixSuperGtensor (X.matrixSuper p q) D p' q').trans
              ((gtensorComm (X.matrixSuper p q) D).matrixSuper p' q'))).toAlgEquiv w))
      = (((gtensorComm X D).matrixSuper p q).matrixSuper p' q').toAlgEquiv u := by
    -- `.matrixSuper` distributes over `.trans` definitionally; unfold
    -- both sides to a chain of `.toAlgEquiv` applications, cancel the
    -- `gtensorComm` pair (`e.symm.matrixSuper = (e.matrixSuper).symm`)
    show (((gtensorComm X D).matrixSuper p q).matrixSuper p' q').toAlgEquiv
        (((matrixSuperGtensor X D p q).matrixSuper p' q').toAlgEquiv
          (((gtensorComm D (X.matrixSuper p q)).matrixSuper p' q').toAlgEquiv
            (((gtensorComm (X.matrixSuper p q) D).matrixSuper p' q').toAlgEquiv
              ((matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv w1))))
      = (((gtensorComm X D).matrixSuper p q).matrixSuper p' q').toAlgEquiv u
    have hcancel : ((gtensorComm D (X.matrixSuper p q)).matrixSuper p' q').toAlgEquiv
          (((gtensorComm (X.matrixSuper p q) D).matrixSuper p' q').toAlgEquiv
            ((matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv w1))
        = (matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv w1 := by
      show ((gtensorComm (X.matrixSuper p q) D).matrixSuper p' q').symm.toAlgEquiv
          (((gtensorComm (X.matrixSuper p q) D).matrixSuper p' q').toAlgEquiv
            ((matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv w1))
        = (matrixSuperGtensor (X.matrixSuper p q) D p' q').toAlgEquiv w1
      exact AlgEquiv.symm_apply_apply _ _
    rw [hcancel, hu]
  rw [hv, matrixSuperComp_natural_apply (gtensorComm X D) p q p' q' u]

end Coherence

end Superfusion

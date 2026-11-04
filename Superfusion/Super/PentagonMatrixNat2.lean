/-
Superfusion / Super / PentagonMatrixNat2

Milestone M7d-5b-4-iii(b), part 6: **the full matrix-tensor
naturalities** — both-slot versions:

- `matrixSuperGtensor_full_natural_apply`: naturality of the
  matrix-stabilization compatibility in BOTH slots
  (`mSG ∘ (e.matrixSuper ⊗c f) = (e ⊗c f).matrixSuper ∘ mSG`);
- `matrixSuperGtensorRight_full_natural_apply`: the right version,
  derived from the braiding naturality, the left version, and the
  functoriality of matrix stabilization (following its definition
  `comm ≫ mSG ≫ comm.matrixSuper`);
- `matrixSuperComp_natural_apply`: naturality of the matrix-size
  composition.

These complete the interchange laws needed to factor the pentagon
vertex routes for the cluster edges.
-/
import Superfusion.Super.PentagonMatrixNat

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section MatrixNat2

universe u

variable {K : Type u} [CommRing K]

/-- A cast marker re-anchoring `.carrier` of `SuperAlgebra.gtensor`,
matching the idiom of `PentagonMatrixNat.lean`. -/
private def toC2 {P Q : SuperAlgebra K}
    (x : P.grading ᵍ⊗[K] Q.grading) : (P.gtensor Q).carrier := x

private theorem gtensorCongr_tmul2 {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (a : P.carrier) (b : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv (toC2 (a ᵍ⊗ₜ[K] b))
      = toC2 (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading e.toAlgEquiv
    f.toAlgEquiv e.map_grading f.map_grading a b

/-- Entrywise, a homogeneous congruence `e ᵍ⊗c f` carries
`matrixInclLeft M` to `matrixInclLeft (e-entrywise M)` (both slots
generalize `mapMatrix_matrixInclLeft`, replacing `refl` in the matrix
slot by `e`). -/
private theorem mapMatrix_matrixInclLeft2 {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (n : Type*) [Fintype n] [DecidableEq n]
    (M : Matrix n n P.carrier) :
    ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
        Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P'.gtensor Q').carrier)
        (matrixInclLeft P.grading Q.grading M)
      = matrixInclLeft P'.grading Q'.grading (M.map e.toAlgEquiv) := by
  refine Matrix.ext fun r s => ?_
  rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply, matrixInclLeft_apply,
    matrixInclLeft_apply, Matrix.map_apply]
  have h := gtensorCongr_tmul2 e f (M r s) (1 : Q.carrier)
  rwa [show f.toAlgEquiv (1 : Q.carrier) = 1 from map_one f.toAlgEquiv] at h

/-- Entrywise, a homogeneous congruence `e ᵍ⊗c f` carries
`matrixInclRight y` to `matrixInclRight (f y)` (both slots
generalize `mapMatrix_matrixInclRight`, replacing `refl` in the
matrix slot by `e`; the signed diagonal only sees the parity of `y`,
so the argument is identical modulo inserting `map_one e.toAlgEquiv`
in the slot-1 entries). -/
private theorem mapMatrix_matrixInclRight2 {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (n : Type*) [Fintype n] [DecidableEq n]
    (π : n → ZMod 2) (y : Q.carrier) :
    ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
        Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P'.gtensor Q').carrier)
        (matrixInclRight π P.grading Q.grading y)
      = matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv y) := by
  -- reduce to homogeneous `y` via the even/odd decomposition
  have hy := evenPart_add_oddPart Q.grading y
  have hy0 : evenPart Q.grading y ∈ Q.grading 0 := evenPart_mem Q.grading y
  have hy1 : oddPart Q.grading y ∈ Q.grading 1 := oddPart_mem Q.grading y
  have hfy0 : f.toAlgEquiv (evenPart Q.grading y) ∈ Q'.grading 0 := by
    rw [← f.map_grading 0]; exact Submodule.mem_map_of_mem hy0
  have hfy1 : f.toAlgEquiv (oddPart Q.grading y) ∈ Q'.grading 1 := by
    rw [← f.map_grading 1]; exact Submodule.mem_map_of_mem hy1
  have hsplit : ∀ (j : ZMod 2) (z : Q.carrier), z ∈ Q.grading j →
      ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
          Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P'.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading z)
        = matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv z) := by
    intro j z hz
    have hfz : f.toAlgEquiv z ∈ Q'.grading j := by
      rw [← f.map_grading j]; exact Submodule.mem_map_of_mem hz
    have h := gtensorCongr_tmul2 e f (1 : P.carrier) z
    rw [show e.toAlgEquiv (1 : P.carrier) = 1 from map_one e.toAlgEquiv] at h
    refine Matrix.ext fun r s => ?_
    rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply, matrixInclRight_apply,
      matrixInclRight_apply, sdiag_of_mem π P.grading Q.grading hz,
      sdiag_of_mem π P'.grading Q'.grading hfz, Matrix.diagonal_apply,
      Matrix.diagonal_apply]
    by_cases hrs : r = s
    · rw [if_pos hrs, if_pos hrs]
      have huz : ((e.gtensorCongr f).toAlgEquiv
            (((sgn (π r * j) : ℤˣ) : ℤ) • toC2 ((1 : P.carrier) ᵍ⊗ₜ[K] z)))
          = ((sgn (π r * j) : ℤˣ) : ℤ) •
            ((e.gtensorCongr f).toAlgEquiv
              (toC2 ((1 : P.carrier) ᵍ⊗ₜ[K] z))) :=
        map_zsmul ((e.gtensorCongr f).toAlgEquiv.toAlgHom) _ _
      show (e.gtensorCongr f).toAlgEquiv
          (((sgn (π r * j) : ℤˣ) : ℤ) • toC2 ((1 : P.carrier) ᵍ⊗ₜ[K] z))
        = ((sgn (π r * j) : ℤˣ) : ℤ) • toC2 ((1 : P'.carrier) ᵍ⊗ₜ[K] f.toAlgEquiv z)
      rw [huz, h]
    · rw [if_neg hrs, if_neg hrs]
      show (e.gtensorCongr f).toAlgEquiv.toAlgHom
          (toC2 (0 : P.grading ᵍ⊗[K] Q.grading))
        = toC2 (0 : P'.grading ᵍ⊗[K] Q'.grading)
      exact map_zero _
  have hyR : matrixInclRight π P.grading Q.grading y
      = matrixInclRight π P.grading Q.grading (evenPart Q.grading y)
        + matrixInclRight π P.grading Q.grading (oddPart Q.grading y) := by
    rw [← map_add, hy]
  have hfyR : matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv y)
      = matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv (evenPart Q.grading y))
        + matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv (oddPart Q.grading y)) := by
    rw [← map_add, ← map_add, hy]
  calc ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
        Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P'.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading y)
      = ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P'.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading (evenPart Q.grading y)
            + matrixInclRight π P.grading Q.grading (oddPart Q.grading y)) := by
        rw [hyR]
    _ = ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P'.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading (evenPart Q.grading y))
        + ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix n n (P.gtensor Q).carrier ≃ₐ[K] Matrix n n (P'.gtensor Q').carrier)
          (matrixInclRight π P.grading Q.grading (oddPart Q.grading y)) :=
        map_add _ _ _
    _ = matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv (evenPart Q.grading y))
        + matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv (oddPart Q.grading y)) := by
        rw [hsplit 0 _ hy0, hsplit 1 _ hy1]
        rfl
    _ = matrixInclRight π P'.grading Q'.grading (f.toAlgEquiv y) := by rw [hfyR]

/-- Naturality of the matrix-stabilization compatibility, both
slots. -/
theorem matrixSuperGtensor_full_natural_apply
    {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q') (p q : ℕ)
    (w : ((P.matrixSuper p q).gtensor Q).carrier) :
    (matrixSuperGtensor P' Q' p q).toAlgEquiv
        (((e.matrixSuper p q).gtensorCongr f).toAlgEquiv w)
      = ((e.gtensorCongr f).matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensor P Q p q).toAlgEquiv w) := by
  have hhom : ((matrixSuperGtensor P' Q' p q).toAlgEquiv.toAlgHom).comp
        (((e.matrixSuper p q).gtensorCongr f).toAlgEquiv.toAlgHom)
      = (((e.gtensorCongr f).matrixSuper p q).toAlgEquiv.toAlgHom).comp
        ((matrixSuperGtensor P Q p q).toAlgEquiv.toAlgHom) := by
    refine galgHom_ext (P.matrixSuper p q).grading Q.grading ?_
    intro M₀ y
    -- work with `M` at the raw `Matrix` type throughout, to avoid the
    -- `(P.matrixSuper p q).carrier` synonym defeating `rw`'s matching
    set M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier := M₀ with hM₀
    change (matrixSuperGtensor P' Q' p q).toAlgEquiv
        (((e.matrixSuper p q).gtensorCongr f).toAlgEquiv (toC2 (M ᵍ⊗ₜ[K] y)))
      = ((e.gtensorCongr f).matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensor P Q p q).toAlgEquiv (toC2 (M ᵍ⊗ₜ[K] y)))
    -- unfold the congruence on the source: `e.matrixSuper p q` is
    -- entrywise `e` on the matrix slot
    have hlhs1 : ((e.matrixSuper p q).gtensorCongr f).toAlgEquiv
          (toC2 (M ᵍ⊗ₜ[K] y))
        = toC2 ((M.map e.toAlgEquiv) ᵍ⊗ₜ[K] f.toAlgEquiv y) := by
      have h := gtensorCongr_tmul2 (e.matrixSuper p q) f M y
      rwa [show (e.matrixSuper p q).toAlgEquiv M = M.map e.toAlgEquiv from rfl] at h
    rw [hlhs1]
    -- both `matrixSuperGtensor` applications unfold via `matrixTensorSuperHom_tmul`
    have hlhs2 : (matrixSuperGtensor P' Q' p q).toAlgEquiv
          (toC2 ((M.map e.toAlgEquiv) ᵍ⊗ₜ[K] f.toAlgEquiv y))
        = matrixInclLeft P'.grading Q'.grading (M.map e.toAlgEquiv)
          * matrixInclRight (sumParity p q) P'.grading Q'.grading (f.toAlgEquiv y) := by
      show matrixTensorSuperHom (sumParity p q) P'.grading Q'.grading
          ((M.map e.toAlgEquiv) ᵍ⊗ₜ[K] f.toAlgEquiv y)
        = matrixInclLeft P'.grading Q'.grading (M.map e.toAlgEquiv)
          * matrixInclRight (sumParity p q) P'.grading Q'.grading (f.toAlgEquiv y)
      exact matrixTensorSuperHom_tmul (sumParity p q) P'.grading Q'.grading
        (M.map e.toAlgEquiv) (f.toAlgEquiv y)
    have hrhs1 : (matrixSuperGtensor P Q p q).toAlgEquiv (toC2 (M ᵍ⊗ₜ[K] y))
        = matrixInclLeft P.grading Q.grading M
          * matrixInclRight (sumParity p q) P.grading Q.grading y := by
      show matrixTensorSuperHom (sumParity p q) P.grading Q.grading (M ᵍ⊗ₜ[K] y)
        = matrixInclLeft P.grading Q.grading M
          * matrixInclRight (sumParity p q) P.grading Q.grading y
      exact matrixTensorSuperHom_tmul (sumParity p q) P.grading Q.grading M y
    rw [hlhs2, hrhs1]
    -- the outer map is `mapMatrix` of the congruence, entrywise
    have hprod : ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
            ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P'.gtensor Q').carrier)
        (matrixInclLeft P.grading Q.grading M
          * matrixInclRight (sumParity p q) P.grading Q.grading y)
      = ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
              ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P'.gtensor Q').carrier)
          (matrixInclLeft P.grading Q.grading M)
        * ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
              ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P'.gtensor Q').carrier)
          (matrixInclRight (sumParity p q) P.grading Q.grading y) :=
      map_mul _ _ _
    show matrixInclLeft P'.grading Q'.grading (M.map e.toAlgEquiv)
        * matrixInclRight (sumParity p q) P'.grading Q'.grading (f.toAlgEquiv y)
      = ((e.gtensorCongr f).toAlgEquiv.mapMatrix :
            Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P.gtensor Q).carrier
              ≃ₐ[K] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (P'.gtensor Q').carrier)
          (matrixInclLeft P.grading Q.grading M
            * matrixInclRight (sumParity p q) P.grading Q.grading y)
    rw [hprod, mapMatrix_matrixInclLeft2 e f (Fin p ⊕ Fin q) M,
      mapMatrix_matrixInclRight2 e f (Fin p ⊕ Fin q) (sumParity p q) y]
    rfl
  exact AlgHom.congr_fun hhom w

/-- Entrywise, `.matrixSuper` carries the braiding-naturality square:
applying `(gtensorComm ·).matrixSuper` after `(g.gtensorCongr h)
.matrixSuper` entrywise agrees with applying it in the other order,
since both are literally entrywise applications of the underlying
scalar equation `gtensorComm_natural_apply`. -/
private theorem matrixSuper_gtensorComm_natural_apply
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

/-- Naturality of the right matrix-stabilization compatibility, both
slots — derived from the braiding naturality, the left version, and
the functoriality of matrix stabilization. -/
theorem matrixSuperGtensorRight_full_natural_apply
    {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q') (p q : ℕ)
    (w : (P.gtensor (Q.matrixSuper p q)).carrier) :
    (matrixSuperGtensorRight P' Q' p q).toAlgEquiv
        ((e.gtensorCongr (f.matrixSuper p q)).toAlgEquiv w)
      = ((e.gtensorCongr f).matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensorRight P Q p q).toAlgEquiv w) := by
  show ((gtensorComm P' (Q'.matrixSuper p q)).trans
        ((matrixSuperGtensor Q' P' p q).trans ((gtensorComm Q' P').matrixSuper p q))).toAlgEquiv
        ((e.gtensorCongr (f.matrixSuper p q)).toAlgEquiv w)
      = ((e.gtensorCongr f).matrixSuper p q).toAlgEquiv
        (((gtensorComm P (Q.matrixSuper p q)).trans
          ((matrixSuperGtensor Q P p q).trans
            ((gtensorComm Q P).matrixSuper p q))).toAlgEquiv w)
  show ((gtensorComm Q' P').matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensor Q' P' p q).toAlgEquiv
          ((gtensorComm P' (Q'.matrixSuper p q)).toAlgEquiv
            ((e.gtensorCongr (f.matrixSuper p q)).toAlgEquiv w)))
      = ((e.gtensorCongr f).matrixSuper p q).toAlgEquiv
        (((gtensorComm Q P).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor Q P p q).toAlgEquiv
            ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv w)))
  rw [gtensorComm_natural_apply e (f.matrixSuper p q) w,
    matrixSuperGtensor_full_natural_apply f e p q
      ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv w),
    matrixSuper_gtensorComm_natural_apply f e p q
      ((matrixSuperGtensor Q P p q).toAlgEquiv
        ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv w))]

/-- Naturality of the matrix-size composition. -/
theorem matrixSuperComp_natural_apply {P P' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (p q p' q' : ℕ)
    (M : ((P.matrixSuper p q).matrixSuper p' q').carrier) :
    (matrixSuperComp P' p' q' p q).toAlgEquiv
        (((e.matrixSuper p q).matrixSuper p' q').toAlgEquiv M)
      = (e.matrixSuper (p' * p + q' * q)
          (p' * q + q' * p)).toAlgEquiv
        ((matrixSuperComp P p' q' p q).toAlgEquiv M) := by
  set M' : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q')
      (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) := M with hM'
  -- both `.matrixSuper` applications unfold entrywise via `rfl`, and
  -- `matrixSuperComp`'s `.toAlgEquiv` unfolds as the
  -- `compAlgEquiv ≫ reindexAlgEquiv` composite
  show (Matrix.reindexAlgEquiv K P'.carrier (collapseIndexEquiv p' q' p q))
      ((Matrix.compAlgEquiv (Fin p' ⊕ Fin q') (Fin p ⊕ Fin q) P'.carrier K)
        (M'.map (fun N => N.map e.toAlgEquiv)))
    = ((Matrix.reindexAlgEquiv K P.carrier (collapseIndexEquiv p' q' p q))
        ((Matrix.compAlgEquiv (Fin p' ⊕ Fin q') (Fin p ⊕ Fin q) P.carrier K) M')).map e.toAlgEquiv
  rw [Matrix.compAlgEquiv_apply, Matrix.compAlgEquiv_apply, Matrix.comp_map_map,
    Matrix.coe_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_map]

end MatrixNat2

end Superfusion

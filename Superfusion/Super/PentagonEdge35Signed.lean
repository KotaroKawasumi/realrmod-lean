/-
Superfusion / Super / PentagonEdge35Signed

Milestone M7d-5b-4-iii(c), part 5: **the signed factorization of
vertex 3 through the (cd)-cluster, and the e35 edge intertwining**.

`PentagonEdge35.lean` constructed the signed swap unit `swapSign`
(the Koszul-signed sorting permutation between the two stabilization
orders of `M_σ(T_{a+b}) ᵍ⊗ M_γ(T_{c+d})`).  This file proves the
corrected factorization

  `(cluster35Tail3 ∘ cluster35Prefix)(w)
     = swapSign · quadRoute3(w) · swapSign`   (F3′ signed)

and derives the e35 edge intertwining of `(alignedRoute5,
quadRoute3)` from it and the landed `edge35Core_intertwines`.

The proof of the signed F3′ factors both sides through the common
bifusion `Φ := (stdFuse a b ᵍ⊗c stdFuse c d) ∘ gassoc`:

- the `(cd)`-side (`tail3_prefix_eq`) reorders through the landed
  `matrixSuperGtensorRight` full naturality;
- the `(ab)`-side (`quadRoute3_prefix_eq`) needs the **left-slot
  stabilization hexagon** (`matrixSuperGtensor_gassoc_left_apply`,
  new in this file: the mirror of the right-slot hexagon of
  `PentagonFactor35.lean`), the landed `matrixSuperGtensor` full
  naturality and the associator naturality;
- the two reduced tails differ by the honest Koszul-signed layer
  transposition, certified on the standard fusion sizes by kernel
  `decide` after the `fuseSize` dichotomy.
-/
import Superfusion.Super.PentagonEdge35

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

/-! ### The generic kit (local copies of the private helpers of
`PentagonFactor35.lean`) and the left-slot hexagon -/

section KitSigned

universe u

variable {K : Type u} [CommRing K]

private def toCA {P Q : SuperAlgebra K} (x : P.grading ᵍ⊗[K] Q.grading) :
    (P.gtensor Q).carrier := x

private theorem gtensorCongr_tmulCA {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (a : P.carrier) (b : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv (toCA (a ᵍ⊗ₜ[K] b))
      = toCA (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading e.toAlgEquiv
    f.toAlgEquiv e.map_grading f.map_grading a b

private theorem gtensorAssoc_tmulCA {P Q R : SuperAlgebra K}
    (a : P.carrier) (b : Q.carrier) (c : R.carrier) :
    (gtensorAssoc P Q R).toAlgEquiv
        (toCA (toCA (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c))
      = toCA (a ᵍ⊗ₜ[K] toCA (b ᵍ⊗ₜ[K] c)) :=
  gassoc_tmul P.grading Q.grading R.grading a b c

private theorem toCA_one_one {P Q : SuperAlgebra K} :
    toCA ((1 : P.carrier) ᵍ⊗ₜ[K] (1 : Q.carrier))
      = (1 : (P.gtensor Q).carrier) := by
  show ((1 : P.carrier) ᵍ⊗ₜ[K] (1 : Q.carrier)
      : P.grading ᵍ⊗[K] Q.grading) = 1
  rw [show ((1 : P.carrier) ᵍ⊗ₜ[K] (1 : Q.carrier)
        : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading ((1 : P.carrier) ⊗ₜ[K] (1 : Q.carrier))
      from rfl,
    show ((1 : P.carrier) ⊗ₜ[K] (1 : Q.carrier)
        : P.carrier ⊗[K] Q.carrier) = 1 from
      Algebra.TensorProduct.one_def.symm,
    of_one]

private theorem add_gtmulCA {P Q : SuperAlgebra K}
    (u v : P.carrier) (z : Q.carrier) :
    toCA ((u + v) ᵍ⊗ₜ[K] z) = toCA (u ᵍ⊗ₜ[K] z) + toCA (v ᵍ⊗ₜ[K] z) := by
  show ((u + v) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading)
    = (u ᵍ⊗ₜ[K] z) + (v ᵍ⊗ₜ[K] z)
  rw [show ((u + v) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading ((u + v) ⊗ₜ[K] z) from rfl,
    TensorProduct.add_tmul, map_add]
  rfl

private theorem gtmulCA_add {P Q : SuperAlgebra K}
    (x : P.carrier) (u v : Q.carrier) :
    toCA (x ᵍ⊗ₜ[K] (u + v)) = toCA (x ᵍ⊗ₜ[K] u) + toCA (x ᵍ⊗ₜ[K] v) := by
  show (x ᵍ⊗ₜ[K] (u + v) : P.grading ᵍ⊗[K] Q.grading)
    = (x ᵍ⊗ₜ[K] u) + (x ᵍ⊗ₜ[K] v)
  rw [show (x ᵍ⊗ₜ[K] (u + v) : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading (x ⊗ₜ[K] (u + v)) from rfl,
    TensorProduct.tmul_add, map_add]
  rfl

private theorem zsmul_gtmulCA {P Q : SuperAlgebra K}
    (n : ℤ) (x : P.carrier) (z : Q.carrier) :
    toCA ((n • x) ᵍ⊗ₜ[K] z) = n • toCA (x ᵍ⊗ₜ[K] z) := by
  show ((n • x) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading) = n • (x ᵍ⊗ₜ[K] z)
  rw [show ((n • x) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading ((n • x) ⊗ₜ[K] z) from rfl,
    show ((n • x) ⊗ₜ[K] z : P.carrier ⊗[K] Q.carrier) = n • (x ⊗ₜ[K] z)
      from (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]
  rfl

private theorem gtmulCA_zsmul {P Q : SuperAlgebra K}
    (n : ℤ) (x : P.carrier) (z : Q.carrier) :
    toCA (x ᵍ⊗ₜ[K] (n • z)) = n • toCA (x ᵍ⊗ₜ[K] z) := by
  show (x ᵍ⊗ₜ[K] (n • z) : P.grading ᵍ⊗[K] Q.grading) = n • (x ᵍ⊗ₜ[K] z)
  rw [show (x ᵍ⊗ₜ[K] (n • z) : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading (x ⊗ₜ[K] (n • z)) from rfl,
    show (x ⊗ₜ[K] (n • z) : P.carrier ⊗[K] Q.carrier) = n • (x ⊗ₜ[K] z)
      from by
        rw [← TensorProduct.smul_tmul]
        exact (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]
  rfl

private theorem zero_gtmulCA {P Q : SuperAlgebra K} (z : Q.carrier) :
    toCA ((0 : P.carrier) ᵍ⊗ₜ[K] z) = 0 := by
  show ((0 : P.carrier) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading) = 0
  rw [show ((0 : P.carrier) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading ((0 : P.carrier) ⊗ₜ[K] z) from rfl,
    TensorProduct.zero_tmul, map_zero]

private theorem gtmulCA_zero {P Q : SuperAlgebra K} (x : P.carrier) :
    toCA (x ᵍ⊗ₜ[K] (0 : Q.carrier)) = 0 := by
  show (x ᵍ⊗ₜ[K] (0 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading) = 0
  rw [show (x ᵍ⊗ₜ[K] (0 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading (x ⊗ₜ[K] (0 : Q.carrier)) from rfl,
    TensorProduct.tmul_zero, map_zero]

/-- The braiding on `x ᵍ⊗ 1` is sign-free (local copy of the private
helper of `PentagonFactor.lean`). -/
private theorem gtensorComm_tmul_one {P Q : SuperAlgebra K}
    (x : P.carrier) :
    (gtensorComm P Q).toAlgEquiv (toCA (x ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K] x) := by
  have hsplit : ∀ (j : ZMod 2) (y : P.carrier), y ∈ P.grading j →
      (gtensorComm P Q).toAlgEquiv (toCA (y ᵍ⊗ₜ[K] (1 : Q.carrier)))
        = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K] y) := by
    intro j y hy
    show comm P.grading Q.grading (y ᵍ⊗ₜ[K] (1 : Q.carrier))
      = ((1 : Q.carrier) ᵍ⊗ₜ[K] y)
    rw [show (y ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading)
        = (((⟨y, hy⟩ : P.grading j) : P.carrier) ᵍ⊗ₜ[K]
            ((⟨(1 : Q.carrier), SetLike.one_mem_graded Q.grading⟩ :
              Q.grading 0) : Q.carrier)) from rfl,
      comm_coe_tmul_coe, zero_mul,
      show ((-1 : ℤˣ) ^ (0 : ZMod 2)) = 1 from
        (sgn_eq_neg_one_uzpow 0).symm.trans sgn_zero,
      one_smul]
  calc (gtensorComm P Q).toAlgEquiv (toCA (x ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = (gtensorComm P Q).toAlgEquiv
          (toCA ((evenPart P.grading x + oddPart P.grading x)
            ᵍ⊗ₜ[K] (1 : Q.carrier))) := by
        rw [evenPart_add_oddPart]
    _ = (gtensorComm P Q).toAlgEquiv
          (toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier)))
        + (gtensorComm P Q).toAlgEquiv
          (toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))) := by
        rw [add_gtmulCA, map_add]
    _ = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K] evenPart P.grading x)
        + toCA ((1 : Q.carrier) ᵍ⊗ₜ[K] oddPart P.grading x) := by
        rw [hsplit 0 _ (evenPart_mem P.grading x),
          hsplit 1 _ (oddPart_mem P.grading x)]
    _ = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K] x) := by
        rw [← gtmulCA_add, evenPart_add_oddPart]

/-- The braiding on `1 ᵍ⊗ y` is sign-free. -/
private theorem gtensorComm_one_tmul {P Q : SuperAlgebra K}
    (y : Q.carrier) :
    (gtensorComm P Q).toAlgEquiv (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] y))
      = toCA (y ᵍ⊗ₜ[K] (1 : P.carrier)) := by
  have hsplit : ∀ (j : ZMod 2) (z : Q.carrier), z ∈ Q.grading j →
      (gtensorComm P Q).toAlgEquiv (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] z))
        = toCA (z ᵍ⊗ₜ[K] (1 : P.carrier)) := by
    intro j z hz
    show comm P.grading Q.grading ((1 : P.carrier) ᵍ⊗ₜ[K] z)
      = (z ᵍ⊗ₜ[K] (1 : P.carrier))
    rw [show ((1 : P.carrier) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading)
        = (((⟨(1 : P.carrier), SetLike.one_mem_graded P.grading⟩ :
              P.grading 0) : P.carrier) ᵍ⊗ₜ[K]
            ((⟨z, hz⟩ : Q.grading j) : Q.carrier)) from rfl,
      comm_coe_tmul_coe, mul_zero,
      show ((-1 : ℤˣ) ^ (0 : ZMod 2)) = 1 from
        (sgn_eq_neg_one_uzpow 0).symm.trans sgn_zero,
      one_smul]
  calc (gtensorComm P Q).toAlgEquiv (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] y))
      = (gtensorComm P Q).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K]
            (evenPart Q.grading y + oddPart Q.grading y))) := by
        rw [evenPart_add_oddPart]
    _ = (gtensorComm P Q).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] evenPart Q.grading y))
        + (gtensorComm P Q).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] oddPart Q.grading y)) := by
        rw [gtmulCA_add, map_add]
    _ = toCA ((evenPart Q.grading y) ᵍ⊗ₜ[K] (1 : P.carrier))
        + toCA ((oddPart Q.grading y) ᵍ⊗ₜ[K] (1 : P.carrier)) := by
        rw [hsplit 0 _ (evenPart_mem Q.grading y),
          hsplit 1 _ (oddPart_mem Q.grading y)]
    _ = toCA (y ᵍ⊗ₜ[K] (1 : P.carrier)) := by
        rw [← add_gtmulCA, evenPart_add_oddPart]

/-- `mSGR` on `x ᵍ⊗ 1`: the signed diagonal of `x` (local copy). -/
private theorem matrixSuperGtensorRight_tmul_one {P Q : SuperAlgebra K}
    (p q : ℕ) (x : P.carrier) :
    (matrixSuperGtensorRight P Q p q).toAlgEquiv
        (toCA (x ᵍ⊗ₜ[K] (1 : (Q.matrixSuper p q).carrier)))
      = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
          toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
            + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
              toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))) := by
  show ((gtensorComm Q P).matrixSuper p q).toAlgEquiv
      ((matrixSuperGtensor Q P p q).toAlgEquiv
        ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv
          (toCA (x ᵍ⊗ₜ[K] (1 : (Q.matrixSuper p q).carrier)))))
    = _
  rw [gtensorComm_tmul_one,
    show (matrixSuperGtensor Q P p q).toAlgEquiv
        (toCA ((1 : (Q.matrixSuper p q).carrier) ᵍ⊗ₜ[K] x))
      = matrixInclLeft Q.grading P.grading
          (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
        * matrixInclRight (sumParity p q) Q.grading P.grading x from
      matrixTensorSuperHom_tmul (sumParity p q) Q.grading P.grading 1 x,
    map_one, one_mul, matrixInclRight_apply]
  refine Matrix.ext fun r s => ?_
  show (gtensorComm Q P).toAlgEquiv
      (sdiag (sumParity p q) Q.grading P.grading x r s)
    = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
        toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
          + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
            toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))) r s
  rw [show sdiag (sumParity p q) Q.grading P.grading x
      = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
          ((1 : Q.carrier) ᵍ⊗ₜ[K] evenPart P.grading x
            : Q.grading ᵍ⊗[K] P.grading)
            + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
              ((1 : Q.carrier) ᵍ⊗ₜ[K] oddPart P.grading x)) from rfl]
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    show (gtensorComm Q P).toAlgEquiv
        (toCA ((1 : Q.carrier) ᵍ⊗ₜ[K] evenPart P.grading x)
          + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
            toCA ((1 : Q.carrier) ᵍ⊗ₜ[K] oddPart P.grading x))
      = toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
        + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
          toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
    rw [map_add, map_zsmul, gtensorComm_one_tmul, gtensorComm_one_tmul]
  · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs]
    exact map_zero _

/-- `mSGR` on `1 ᵍ⊗ N`: entrywise `1 ᵍ⊗ ·` (local copy). -/
private theorem matrixSuperGtensorRight_one_tmul {P Q : SuperAlgebra K}
    (p q : ℕ) (N₀ : (Q.matrixSuper p q).carrier) :
    (matrixSuperGtensorRight P Q p q).toAlgEquiv
        (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] N₀))
      = Matrix.map
          (N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
          (fun z => toCA ((1 : P.carrier) ᵍ⊗ₜ[K] z)) := by
  show ((gtensorComm Q P).matrixSuper p q).toAlgEquiv
      ((matrixSuperGtensor Q P p q).toAlgEquiv
        ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] N₀))))
    = _
  rw [gtensorComm_one_tmul,
    show (matrixSuperGtensor Q P p q).toAlgEquiv
        (toCA (N₀ ᵍ⊗ₜ[K] (1 : P.carrier)))
      = matrixInclLeft Q.grading P.grading
          (N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
        * matrixInclRight (sumParity p q) Q.grading P.grading
          (1 : P.carrier) from
      matrixTensorSuperHom_tmul (sumParity p q) Q.grading P.grading N₀ 1,
    map_one, mul_one]
  show (matrixInclLeft Q.grading P.grading
      (N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)).map
      (gtensorComm Q P).toAlgEquiv = _
  refine Matrix.ext fun r s => ?_
  rw [Matrix.map_apply, matrixInclLeft_apply, Matrix.map_apply]
  exact gtensorComm_tmul_one
    ((N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier) r s)

/-! #### Parity projections of pure tensors with a `1`-slot -/

private theorem evenPart_tmulCA_one {P Q : SuperAlgebra K}
    (x : P.carrier) :
    evenPart (P.gtensor Q).grading (toCA (x ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier)) := by
  have h0 : toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
      ∈ (P.gtensor Q).grading 0 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (evenPart_mem P.grading x)
      (SetLike.one_mem_graded Q.grading)
    rwa [add_zero] at h
  have h1 : toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
      ∈ (P.gtensor Q).grading 1 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (oddPart_mem P.grading x)
      (SetLike.one_mem_graded Q.grading)
    rwa [add_zero] at h
  have hx : toCA (x ᵍ⊗ₜ[K] (1 : Q.carrier))
      = toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
        + toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier)) := by
    rw [← add_gtmulCA, evenPart_add_oddPart]
  rw [hx, map_add, evenPart_of_mem_zero _ h0, evenPart_of_mem_one _ h1,
    add_zero]

private theorem oddPart_tmulCA_one {P Q : SuperAlgebra K}
    (x : P.carrier) :
    oddPart (P.gtensor Q).grading (toCA (x ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier)) := by
  have h0 : toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
      ∈ (P.gtensor Q).grading 0 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (evenPart_mem P.grading x)
      (SetLike.one_mem_graded Q.grading)
    rwa [add_zero] at h
  have h1 : toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
      ∈ (P.gtensor Q).grading 1 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (oddPart_mem P.grading x)
      (SetLike.one_mem_graded Q.grading)
    rwa [add_zero] at h
  have hx : toCA (x ᵍ⊗ₜ[K] (1 : Q.carrier))
      = toCA ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
        + toCA ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier)) := by
    rw [← add_gtmulCA, evenPart_add_oddPart]
  rw [hx, map_add, oddPart_of_mem_zero _ h0, oddPart_of_mem_one _ h1,
    zero_add]

private theorem evenPart_one_tmulCA {P Q : SuperAlgebra K}
    (y : Q.carrier) :
    evenPart (P.gtensor Q).grading (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] y))
      = toCA ((1 : P.carrier) ᵍ⊗ₜ[K] evenPart Q.grading y) := by
  have h0 : toCA ((1 : P.carrier) ᵍ⊗ₜ[K] evenPart Q.grading y)
      ∈ (P.gtensor Q).grading 0 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (SetLike.one_mem_graded P.grading)
      (evenPart_mem Q.grading y)
    rwa [zero_add] at h
  have h1 : toCA ((1 : P.carrier) ᵍ⊗ₜ[K] oddPart Q.grading y)
      ∈ (P.gtensor Q).grading 1 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (SetLike.one_mem_graded P.grading)
      (oddPart_mem Q.grading y)
    rwa [zero_add] at h
  have hy : toCA ((1 : P.carrier) ᵍ⊗ₜ[K] y)
      = toCA ((1 : P.carrier) ᵍ⊗ₜ[K] evenPart Q.grading y)
        + toCA ((1 : P.carrier) ᵍ⊗ₜ[K] oddPart Q.grading y) := by
    rw [← gtmulCA_add, evenPart_add_oddPart]
  rw [hy, map_add, evenPart_of_mem_zero _ h0, evenPart_of_mem_one _ h1,
    add_zero]

private theorem oddPart_one_tmulCA {P Q : SuperAlgebra K}
    (y : Q.carrier) :
    oddPart (P.gtensor Q).grading (toCA ((1 : P.carrier) ᵍ⊗ₜ[K] y))
      = toCA ((1 : P.carrier) ᵍ⊗ₜ[K] oddPart Q.grading y) := by
  have h0 : toCA ((1 : P.carrier) ᵍ⊗ₜ[K] evenPart Q.grading y)
      ∈ (P.gtensor Q).grading 0 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (SetLike.one_mem_graded P.grading)
      (evenPart_mem Q.grading y)
    rwa [zero_add] at h
  have h1 : toCA ((1 : P.carrier) ᵍ⊗ₜ[K] oddPart Q.grading y)
      ∈ (P.gtensor Q).grading 1 := by
    have h := tmul_mem_tensorGrading P.grading Q.grading
      (SetLike.one_mem_graded P.grading)
      (oddPart_mem Q.grading y)
    rwa [zero_add] at h
  have hy : toCA ((1 : P.carrier) ᵍ⊗ₜ[K] y)
      = toCA ((1 : P.carrier) ᵍ⊗ₜ[K] evenPart Q.grading y)
        + toCA ((1 : P.carrier) ᵍ⊗ₜ[K] oddPart Q.grading y) := by
    rw [← gtmulCA_add, evenPart_add_oddPart]
  rw [hy, map_add, oddPart_of_mem_zero _ h0, oddPart_of_mem_one _ h1,
    zero_add]

/-! #### Congruence bookkeeping -/

private theorem gtensorCongr_refl_refl_apply {P Q : SuperAlgebra K}
    (w : (P.gtensor Q).carrier) :
    ((SuperAlgEquiv.refl P).gtensorCongr
      (SuperAlgEquiv.refl Q)).toAlgEquiv w = w := by
  have hhom : (((SuperAlgEquiv.refl P).gtensorCongr
        (SuperAlgEquiv.refl Q)).toAlgEquiv.toAlgHom)
      = AlgHom.id K _ := by
    refine galgHom_ext P.grading Q.grading ?_
    intro a b
    change ((SuperAlgEquiv.refl P).gtensorCongr
        (SuperAlgEquiv.refl Q)).toAlgEquiv (toCA (a ᵍ⊗ₜ[K] b))
      = toCA (a ᵍ⊗ₜ[K] b)
    rw [gtensorCongr_tmulCA]
    rfl
  exact AlgHom.congr_fun hhom w

/-- One step of `gtensorCongr_trans_apply`, specialized to `refl` on
the fixed first factor (local copy of the private helper of
`PentagonFactor.lean`). -/
private theorem gtensorCongr_refl_trans_apply {D Q Q' Q'' : SuperAlgebra K}
    (f : SuperAlgEquiv Q Q') (f' : SuperAlgEquiv Q' Q'')
    (w : (D.gtensor Q).carrier) :
    ((SuperAlgEquiv.refl D).gtensorCongr (f.trans f')).toAlgEquiv w
      = ((SuperAlgEquiv.refl D).gtensorCongr f').toAlgEquiv
        (((SuperAlgEquiv.refl D).gtensorCongr f).toAlgEquiv w) :=
  gtensorCongr_trans_apply (SuperAlgEquiv.refl D) (SuperAlgEquiv.refl D)
    f f' w

/-- `(refl ⊗c refl) ⊗c f` acts as `refl ⊗c f`, applied form. -/
private theorem gtensorCongr_reflpair_apply {P Q S S' : SuperAlgebra K}
    (f : SuperAlgEquiv S S') (w : ((P.gtensor Q).gtensor S).carrier) :
    (((SuperAlgEquiv.refl P).gtensorCongr
        (SuperAlgEquiv.refl Q)).gtensorCongr f).toAlgEquiv w
      = ((SuperAlgEquiv.refl (P.gtensor Q)).gtensorCongr f).toAlgEquiv
        w := by
  have hhom : ((((SuperAlgEquiv.refl P).gtensorCongr
        (SuperAlgEquiv.refl Q)).gtensorCongr f).toAlgEquiv.toAlgHom)
      = (((SuperAlgEquiv.refl (P.gtensor Q)).gtensorCongr
        f).toAlgEquiv.toAlgHom) := by
    refine galgHom_ext (P.gtensor Q).grading S.grading ?_
    intro u s
    change (((SuperAlgEquiv.refl P).gtensorCongr
        (SuperAlgEquiv.refl Q)).gtensorCongr f).toAlgEquiv
        (toCA (u ᵍ⊗ₜ[K] s))
      = ((SuperAlgEquiv.refl (P.gtensor Q)).gtensorCongr f).toAlgEquiv
        (toCA (u ᵍ⊗ₜ[K] s))
    rw [gtensorCongr_tmulCA, gtensorCongr_tmulCA,
      gtensorCongr_refl_refl_apply]
    rfl
  exact AlgHom.congr_fun hhom w


/-- One step of `gtensorCongr_trans_apply`, specialized to `refl` on
the fixed second factor. -/
private theorem gtensorCongr_trans_refl_apply {P P' P'' D : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (e' : SuperAlgEquiv P' P'')
    (w : (P.gtensor D).carrier) :
    ((e.trans e').gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv w
      = (e'.gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv
        ((e.gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv w) :=
  gtensorCongr_trans_apply e e' (SuperAlgEquiv.refl D)
    (SuperAlgEquiv.refl D) w

/-- The bundled congruence only depends on the pointwise action of
its first slot. -/
private theorem gtensorCongr_left_eq_apply {P P' Q Q' : SuperAlgebra K}
    (e e' : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (he : ∀ x, e.toAlgEquiv x = e'.toAlgEquiv x)
    (w : (P.gtensor Q).carrier) :
    (e.gtensorCongr f).toAlgEquiv w
      = (e'.gtensorCongr f).toAlgEquiv w := by
  have hhom : (e.gtensorCongr f).toAlgEquiv.toAlgHom
      = (e'.gtensorCongr f).toAlgEquiv.toAlgHom := by
    refine galgHom_ext P.grading Q.grading ?_
    intro p₀ q₀
    change (e.gtensorCongr f).toAlgEquiv (toCA (p₀ ᵍ⊗ₜ[K] q₀))
      = (e'.gtensorCongr f).toAlgEquiv (toCA (p₀ ᵍ⊗ₜ[K] q₀))
    rw [gtensorCongr_tmulCA, gtensorCongr_tmulCA, he]
  exact AlgHom.congr_fun hhom w

/-- The bundled congruence only depends on the pointwise action of
its second slot. -/
private theorem gtensorCongr_right_eq_apply {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f f' : SuperAlgEquiv Q Q')
    (hf : ∀ y, f.toAlgEquiv y = f'.toAlgEquiv y)
    (w : (P.gtensor Q).carrier) :
    (e.gtensorCongr f).toAlgEquiv w
      = (e.gtensorCongr f').toAlgEquiv w := by
  have hhom : (e.gtensorCongr f).toAlgEquiv.toAlgHom
      = (e.gtensorCongr f').toAlgEquiv.toAlgHom := by
    refine galgHom_ext P.grading Q.grading ?_
    intro p₀ q₀
    change (e.gtensorCongr f).toAlgEquiv (toCA (p₀ ᵍ⊗ₜ[K] q₀))
      = (e.gtensorCongr f').toAlgEquiv (toCA (p₀ ᵍ⊗ₜ[K] q₀))
    rw [gtensorCongr_tmulCA, gtensorCongr_tmulCA, hf]
  exact AlgHom.congr_fun hhom w

/-- `refl.trans e` acts as `e`, applied form. -/
private theorem refl_trans_apply {P Q : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) (x : P.carrier) :
    ((SuperAlgEquiv.refl P).trans e).toAlgEquiv x
      = e.toAlgEquiv x := rfl

/-- `e.trans refl` acts as `e`, applied form. -/
private theorem trans_refl_apply {P Q : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) (x : P.carrier) :
    (e.trans (SuperAlgEquiv.refl Q)).toAlgEquiv x
      = e.toAlgEquiv x := rfl

/-- `refl.matrixSuper` acts as the identity, applied form. -/
private theorem matrixSuper_refl_apply {P : SuperAlgebra K} (p q : ℕ)
    (M : (P.matrixSuper p q).carrier) :
    ((SuperAlgEquiv.refl P).matrixSuper p q).toAlgEquiv M = M := rfl

/-- `e ⊗c (refl ⊗c refl)` acts as `e ⊗c refl`, applied form. -/
private theorem gtensorCongr_reflpair_right_apply
    {P P' Q S : SuperAlgebra K} (e : SuperAlgEquiv P P')
    (w : (P.gtensor (Q.gtensor S)).carrier) :
    (e.gtensorCongr ((SuperAlgEquiv.refl Q).gtensorCongr
        (SuperAlgEquiv.refl S))).toAlgEquiv w
      = (e.gtensorCongr
          (SuperAlgEquiv.refl (Q.gtensor S))).toAlgEquiv w :=
  gtensorCongr_right_eq_apply e _ _
    (fun y => gtensorCongr_refl_refl_apply y) w

/-- `mSG` on `M₀ ᵍ⊗ 1`: the entrywise left inclusion. -/
private theorem matrixSuperGtensor_tmul_one {P Q : SuperAlgebra K}
    (p q : ℕ) (M₀ : (P.matrixSuper p q).carrier) :
    (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCA (M₀ ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = matrixInclLeft P.grading Q.grading
          (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) := by
  rw [show (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCA (M₀ ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = matrixInclLeft P.grading Q.grading
          (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier)
        * matrixInclRight (sumParity p q) P.grading Q.grading
          (1 : Q.carrier) from
      matrixTensorSuperHom_tmul (sumParity p q) P.grading Q.grading
        M₀ 1,
    map_one, mul_one]

/-- `mSG` on `1 ᵍ⊗ y`: the signed diagonal. -/
private theorem matrixSuperGtensor_one_tmul {P Q : SuperAlgebra K}
    (p q : ℕ) (y : Q.carrier) :
    (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCA ((1 : (P.matrixSuper p q).carrier) ᵍ⊗ₜ[K] y))
      = matrixInclRight (sumParity p q) P.grading Q.grading y := by
  rw [show (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCA ((1 : (P.matrixSuper p q).carrier) ᵍ⊗ₜ[K] y))
      = matrixInclLeft P.grading Q.grading
          (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier)
        * matrixInclRight (sumParity p q) P.grading Q.grading y from
      matrixTensorSuperHom_tmul (sumParity p q) P.grading Q.grading
        1 y,
    map_one, one_mul]

/-- **The left-slot stabilization hexagon**: pulling the matrix
layer out of the left slot of `(M_σ(X) ⊗ C) ⊗ D` twice and
reassociating entrywise agrees with reassociating first and pulling
the layer out of the left slot once.  Both sides are algebra maps,
so it suffices to compare them on the generators `(M ᵍ⊗ 1) ᵍ⊗ 1`,
`(1 ᵍ⊗ c) ᵍ⊗ 1` and `1 ᵍ⊗ d`, where no Koszul sign can arise. -/
theorem matrixSuperGtensor_gassoc_left_apply
    {X C D : SuperAlgebra K} (p q : ℕ)
    (w : (((X.matrixSuper p q).gtensor C).gtensor D).carrier) :
    ((gtensorAssoc X C D).matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensor (X.gtensor C) D p q).toAlgEquiv
          (((matrixSuperGtensor X C p q).gtensorCongr
            (SuperAlgEquiv.refl D)).toAlgEquiv w))
      = (matrixSuperGtensor X (C.gtensor D) p q).toAlgEquiv
        ((gtensorAssoc (X.matrixSuper p q) C D).toAlgEquiv w) := by
  set F : (((X.matrixSuper p q).gtensor C).gtensor D).carrier →ₐ[K]
      ((X.gtensor (C.gtensor D)).matrixSuper p q).carrier :=
    (((gtensorAssoc X C D).matrixSuper p q).toAlgEquiv.toAlgHom).comp
      (((matrixSuperGtensor (X.gtensor C) D p q).toAlgEquiv.toAlgHom).comp
        (((matrixSuperGtensor X C p q).gtensorCongr
          (SuperAlgEquiv.refl D)).toAlgEquiv.toAlgHom)) with hF
  set G : (((X.matrixSuper p q).gtensor C).gtensor D).carrier →ₐ[K]
      ((X.gtensor (C.gtensor D)).matrixSuper p q).carrier :=
    ((matrixSuperGtensor X (C.gtensor D) p q).toAlgEquiv.toAlgHom).comp
      ((gtensorAssoc (X.matrixSuper p q) C D).toAlgEquiv.toAlgHom)
    with hG
  -- the `M`-generator: both sides give the entrywise left inclusion.
  have hC1 : ∀ M₀ : (X.matrixSuper p q).carrier,
      F (toCA (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = G (toCA (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier))) := by
    intro M₀
    have h1 : F (toCA (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) X.carrier)
            (fun z => toCA (z ᵍ⊗ₜ[K] (1 : (C.gtensor D).carrier))) := by
      show ((gtensorAssoc X C D).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor (X.gtensor C) D p q).toAlgEquiv
            (((matrixSuperGtensor X C p q).gtensorCongr
              (SuperAlgEquiv.refl D)).toAlgEquiv
              (toCA (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))
                ᵍ⊗ₜ[K] (1 : D.carrier)))))
        = _
      rw [gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl D).toAlgEquiv (1 : D.carrier) = 1
          from rfl,
        matrixSuperGtensor_tmul_one p q M₀,
        matrixSuperGtensor_tmul_one (P := X.gtensor C) (Q := D) p q
          (matrixInclLeft X.grading C.grading
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) X.carrier))]
      refine Matrix.ext fun r s => ?_
      show (gtensorAssoc X C D).toAlgEquiv
          (toCA (toCA ((M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
              X.carrier) r s ᵍ⊗ₜ[K] (1 : C.carrier))
            ᵍ⊗ₜ[K] (1 : D.carrier)))
        = toCA ((M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
            X.carrier) r s ᵍ⊗ₜ[K] (1 : (C.gtensor D).carrier))
      rw [gtensorAssoc_tmulCA, toCA_one_one]
    have h3 : G (toCA (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) X.carrier)
            (fun z => toCA (z ᵍ⊗ₜ[K] (1 : (C.gtensor D).carrier))) := by
      show (matrixSuperGtensor X (C.gtensor D) p q).toAlgEquiv
          ((gtensorAssoc (X.matrixSuper p q) C D).toAlgEquiv
            (toCA (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))
              ᵍ⊗ₜ[K] (1 : D.carrier))))
        = _
      rw [gtensorAssoc_tmulCA, toCA_one_one,
        matrixSuperGtensor_tmul_one p q M₀]
      rfl
    exact h1.trans h3.symm
  -- the `c`-generator: both sides give the reassociated signed
  -- diagonal of `c₀`.
  have hC2 : ∀ c₀ : C.carrier,
      F (toCA (toCA ((1 : (X.matrixSuper p q).carrier) ᵍ⊗ₜ[K] c₀)
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = G (toCA (toCA ((1 : (X.matrixSuper p q).carrier) ᵍ⊗ₜ[K] c₀)
          ᵍ⊗ₜ[K] (1 : D.carrier))) := by
    intro c₀
    have h1 : F (toCA (toCA ((1 : (X.matrixSuper p q).carrier)
          ᵍ⊗ₜ[K] c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((evenPart C.grading c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                  toCA ((oddPart C.grading c₀) ᵍ⊗ₜ[K]
                    (1 : D.carrier)))) := by
      show ((gtensorAssoc X C D).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor (X.gtensor C) D p q).toAlgEquiv
            (((matrixSuperGtensor X C p q).gtensorCongr
              (SuperAlgEquiv.refl D)).toAlgEquiv
              (toCA (toCA ((1 : (X.matrixSuper p q).carrier)
                ᵍ⊗ₜ[K] c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))))
        = _
      rw [gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl D).toAlgEquiv (1 : D.carrier) = 1
          from rfl,
        matrixSuperGtensor_one_tmul p q c₀,
        matrixSuperGtensor_tmul_one (P := X.gtensor C) (Q := D) p q
          (matrixInclRight (sumParity p q) X.grading C.grading c₀)]
      refine Matrix.ext fun r s => ?_
      rw [show ((matrixInclRight (sumParity p q) X.grading C.grading
            c₀ : ((X.gtensor C).matrixSuper p q).carrier) :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
            (X.gtensor C).carrier)
          = sdiag (sumParity p q) X.grading C.grading c₀ from rfl]
      rw [show sdiag (sumParity p q) X.grading C.grading c₀
          = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              ((1 : X.carrier) ᵍ⊗ₜ[K] evenPart C.grading c₀
                : X.grading ᵍ⊗[K] C.grading)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  ((1 : X.carrier) ᵍ⊗ₜ[K] oddPart C.grading c₀))
          from rfl]
      show (gtensorAssoc X C D).toAlgEquiv
          (matrixInclLeft (X.gtensor C).grading D.grading
            (Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              ((1 : X.carrier) ᵍ⊗ₜ[K] evenPart C.grading c₀
                : (X.gtensor C).carrier)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  ((1 : X.carrier) ᵍ⊗ₜ[K] oddPart C.grading c₀))) r s)
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((evenPart C.grading c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                  toCA ((oddPart C.grading c₀) ᵍ⊗ₜ[K]
                    (1 : D.carrier)))) r s
      by_cases hrs : r = s
      · subst hrs
        rw [matrixInclLeft_apply, Matrix.diagonal_apply_eq,
          Matrix.diagonal_apply_eq]
        show (gtensorAssoc X C D).toAlgEquiv
            (toCA ((toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                evenPart C.grading c₀)
              + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
                toCA ((1 : X.carrier) ᵍ⊗ₜ[K] oddPart C.grading c₀))
              ᵍ⊗ₜ[K] (1 : D.carrier)))
          = toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
              toCA ((evenPart C.grading c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
            + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
              toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((oddPart C.grading c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
        rw [add_gtmulCA, zsmul_gtmulCA, map_add, map_zsmul,
          gtensorAssoc_tmulCA, gtensorAssoc_tmulCA]
      · rw [matrixInclLeft_apply, Matrix.diagonal_apply_ne _ hrs,
          Matrix.diagonal_apply_ne _ hrs]
        show (gtensorAssoc X C D).toAlgEquiv
            (toCA ((0 : (X.gtensor C).carrier) ᵍ⊗ₜ[K]
              (1 : D.carrier))) = 0
        rw [zero_gtmulCA]
        exact map_zero _
    have h3 : G (toCA (toCA ((1 : (X.matrixSuper p q).carrier)
          ᵍ⊗ₜ[K] c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((evenPart C.grading c₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                  toCA ((oddPart C.grading c₀) ᵍ⊗ₜ[K]
                    (1 : D.carrier)))) := by
      show (matrixSuperGtensor X (C.gtensor D) p q).toAlgEquiv
          ((gtensorAssoc (X.matrixSuper p q) C D).toAlgEquiv
            (toCA (toCA ((1 : (X.matrixSuper p q).carrier)
              ᵍ⊗ₜ[K] c₀) ᵍ⊗ₜ[K] (1 : D.carrier))))
        = _
      rw [gtensorAssoc_tmulCA,
        matrixSuperGtensor_one_tmul p q (toCA (c₀ ᵍ⊗ₜ[K]
          (1 : D.carrier)))]
      refine Matrix.ext fun r s => ?_
      rw [show (matrixInclRight (sumParity p q) X.grading
            (C.gtensor D).grading (toCA (c₀ ᵍ⊗ₜ[K] (1 : D.carrier))) :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
            (X.gtensor (C.gtensor D)).carrier)
          = sdiag (sumParity p q) X.grading (C.gtensor D).grading
            (toCA (c₀ ᵍ⊗ₜ[K] (1 : D.carrier))) from rfl,
        show sdiag (sumParity p q) X.grading (C.gtensor D).grading
            (toCA (c₀ ᵍ⊗ₜ[K] (1 : D.carrier)))
          = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              ((1 : X.carrier) ᵍ⊗ₜ[K] evenPart (C.gtensor D).grading
                  (toCA (c₀ ᵍ⊗ₜ[K] (1 : D.carrier)))
                : X.grading ᵍ⊗[K] (C.gtensor D).grading)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  ((1 : X.carrier) ᵍ⊗ₜ[K]
                    oddPart (C.gtensor D).grading
                      (toCA (c₀ ᵍ⊗ₜ[K] (1 : D.carrier)))))
          from rfl,
        evenPart_tmulCA_one, oddPart_tmulCA_one]
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        rfl
      · rw [Matrix.diagonal_apply_ne _ hrs,
          Matrix.diagonal_apply_ne _ hrs]
        rfl
    exact h1.trans h3.symm
  -- the `d`-generator: both sides give the reassociated signed
  -- diagonal of `d₀`.
  have hR : ∀ d₀ : D.carrier,
      F (toCA ((1 : ((X.matrixSuper p q).gtensor C).carrier)
          ᵍ⊗ₜ[K] d₀))
        = G (toCA ((1 : ((X.matrixSuper p q).gtensor C).carrier)
          ᵍ⊗ₜ[K] d₀)) := by
    intro d₀
    have h1 : F (toCA ((1 : ((X.matrixSuper p q).gtensor C).carrier)
          ᵍ⊗ₜ[K] d₀))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : C.carrier) ᵍ⊗ₜ[K] evenPart D.grading d₀))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                  toCA ((1 : C.carrier) ᵍ⊗ₜ[K]
                    oddPart D.grading d₀))) := by
      show ((gtensorAssoc X C D).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor (X.gtensor C) D p q).toAlgEquiv
            (((matrixSuperGtensor X C p q).gtensorCongr
              (SuperAlgEquiv.refl D)).toAlgEquiv
              (toCA ((1 : ((X.matrixSuper p q).gtensor C).carrier)
                ᵍ⊗ₜ[K] d₀))))
        = _
      rw [show (1 : ((X.matrixSuper p q).gtensor C).carrier)
          = toCA ((1 : (X.matrixSuper p q).carrier)
            ᵍ⊗ₜ[K] (1 : C.carrier)) from toCA_one_one.symm,
        gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl D).toAlgEquiv d₀ = d₀ from rfl,
        matrixSuperGtensor_one_tmul p q (1 : C.carrier), map_one]
      show ((gtensorAssoc X C D).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor (X.gtensor C) D p q).toAlgEquiv
            (toCA ((1 : ((X.gtensor C).matrixSuper p q).carrier)
              ᵍ⊗ₜ[K] d₀)))
        = _
      rw [matrixSuperGtensor_one_tmul (P := X.gtensor C) (Q := D)
          p q d₀]
      refine Matrix.ext fun r s => ?_
      rw [show (matrixInclRight (sumParity p q) (X.gtensor C).grading
            D.grading d₀ :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
            ((X.gtensor C).gtensor D).carrier)
          = sdiag (sumParity p q) (X.gtensor C).grading D.grading d₀
          from rfl,
        show sdiag (sumParity p q) (X.gtensor C).grading D.grading d₀
          = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              ((1 : (X.gtensor C).carrier) ᵍ⊗ₜ[K]
                  evenPart D.grading d₀
                : (X.gtensor C).grading ᵍ⊗[K] D.grading)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  ((1 : (X.gtensor C).carrier) ᵍ⊗ₜ[K]
                    oddPart D.grading d₀)) from rfl]
      show (gtensorAssoc X C D).toAlgEquiv
          (Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              (toCA ((1 : (X.gtensor C).carrier) ᵍ⊗ₜ[K]
                  evenPart D.grading d₀)
                : ((X.gtensor C).gtensor D).carrier)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  toCA ((1 : (X.gtensor C).carrier) ᵍ⊗ₜ[K]
                    oddPart D.grading d₀)) r s)
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : C.carrier) ᵍ⊗ₜ[K] evenPart D.grading d₀))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                  toCA ((1 : C.carrier) ᵍ⊗ₜ[K]
                    oddPart D.grading d₀))) r s
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        show (gtensorAssoc X C D).toAlgEquiv
            (toCA ((1 : (X.gtensor C).carrier) ᵍ⊗ₜ[K]
                evenPart D.grading d₀)
              + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
                toCA ((1 : (X.gtensor C).carrier) ᵍ⊗ₜ[K]
                  oddPart D.grading d₀))
          = toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
              toCA ((1 : C.carrier) ᵍ⊗ₜ[K] evenPart D.grading d₀))
            + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
              toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : C.carrier) ᵍ⊗ₜ[K] oddPart D.grading d₀))
        rw [map_add, map_zsmul,
          show (1 : (X.gtensor C).carrier)
            = toCA ((1 : X.carrier) ᵍ⊗ₜ[K] (1 : C.carrier)) from
            toCA_one_one.symm,
          gtensorAssoc_tmulCA, gtensorAssoc_tmulCA]
      · rw [Matrix.diagonal_apply_ne _ hrs,
          Matrix.diagonal_apply_ne _ hrs]
        exact map_zero _
    have h3 : G (toCA ((1 : ((X.matrixSuper p q).gtensor C).carrier)
          ᵍ⊗ₜ[K] d₀))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : C.carrier) ᵍ⊗ₜ[K] evenPart D.grading d₀))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : X.carrier) ᵍ⊗ₜ[K]
                  toCA ((1 : C.carrier) ᵍ⊗ₜ[K]
                    oddPart D.grading d₀))) := by
      show (matrixSuperGtensor X (C.gtensor D) p q).toAlgEquiv
          ((gtensorAssoc (X.matrixSuper p q) C D).toAlgEquiv
            (toCA ((1 : ((X.matrixSuper p q).gtensor C).carrier)
              ᵍ⊗ₜ[K] d₀)))
        = _
      rw [show (1 : ((X.matrixSuper p q).gtensor C).carrier)
          = toCA ((1 : (X.matrixSuper p q).carrier)
            ᵍ⊗ₜ[K] (1 : C.carrier)) from toCA_one_one.symm,
        gtensorAssoc_tmulCA,
        matrixSuperGtensor_one_tmul p q
          (toCA ((1 : C.carrier) ᵍ⊗ₜ[K] d₀))]
      refine Matrix.ext fun r s => ?_
      rw [show (matrixInclRight (sumParity p q) X.grading
            (C.gtensor D).grading
            (toCA ((1 : C.carrier) ᵍ⊗ₜ[K] d₀)) :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
            (X.gtensor (C.gtensor D)).carrier)
          = sdiag (sumParity p q) X.grading (C.gtensor D).grading
            (toCA ((1 : C.carrier) ᵍ⊗ₜ[K] d₀)) from rfl,
        show sdiag (sumParity p q) X.grading (C.gtensor D).grading
            (toCA ((1 : C.carrier) ᵍ⊗ₜ[K] d₀))
          = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              ((1 : X.carrier) ᵍ⊗ₜ[K] evenPart (C.gtensor D).grading
                  (toCA ((1 : C.carrier) ᵍ⊗ₜ[K] d₀))
                : X.grading ᵍ⊗[K] (C.gtensor D).grading)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  ((1 : X.carrier) ᵍ⊗ₜ[K]
                    oddPart (C.gtensor D).grading
                      (toCA ((1 : C.carrier) ᵍ⊗ₜ[K] d₀)))) from rfl,
        evenPart_one_tmulCA, oddPart_one_tmulCA]
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        rfl
      · rw [Matrix.diagonal_apply_ne _ hrs,
          Matrix.diagonal_apply_ne _ hrs]
        rfl
    exact h1.trans h3.symm
  -- assemble: agree on both inclusions, hence everywhere.
  have hLhom : F.comp (includeLeft
        ((X.matrixSuper p q).gtensor C).grading D.grading)
      = G.comp (includeLeft
        ((X.matrixSuper p q).gtensor C).grading D.grading) := by
    refine galgHom_ext (X.matrixSuper p q).grading C.grading ?_
    intro M₀ c₀
    show F (includeLeft ((X.matrixSuper p q).gtensor C).grading
        D.grading (toCA (M₀ ᵍ⊗ₜ[K] c₀)))
      = G (includeLeft ((X.matrixSuper p q).gtensor C).grading
        D.grading (toCA (M₀ ᵍ⊗ₜ[K] c₀)))
    have e1 : F (includeLeft ((X.matrixSuper p q).gtensor C).grading
          D.grading (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))))
        = G (includeLeft ((X.matrixSuper p q).gtensor C).grading
          D.grading (toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier)))) :=
      hC1 M₀
    have e2 : F (includeLeft ((X.matrixSuper p q).gtensor C).grading
          D.grading
          (toCA ((1 : (X.matrixSuper p q).carrier) ᵍ⊗ₜ[K] c₀)))
        = G (includeLeft ((X.matrixSuper p q).gtensor C).grading
          D.grading
          (toCA ((1 : (X.matrixSuper p q).carrier) ᵍ⊗ₜ[K] c₀))) :=
      hC2 c₀
    rw [show toCA (M₀ ᵍ⊗ₜ[K] c₀)
        = toCA (M₀ ᵍ⊗ₜ[K] (1 : C.carrier))
          * toCA ((1 : (X.matrixSuper p q).carrier) ᵍ⊗ₜ[K] c₀) from
      (includeLeft_mul_includeRight (X.matrixSuper p q).grading
        C.grading M₀ c₀).symm,
      map_mul]
    exact (map_mul F _ _).trans
      (by rw [e1, e2]; exact (map_mul G _ _).symm)
  have hRhom : F.comp (includeRight
        ((X.matrixSuper p q).gtensor C).grading D.grading)
      = G.comp (includeRight
        ((X.matrixSuper p q).gtensor C).grading D.grading) :=
    AlgHom.ext fun d₀ => hR d₀
  have hhom : F = G :=
    GradedTensorProduct.algHom_ext
      (𝒜 := ((X.matrixSuper p q).gtensor C).grading)
      (ℬ := D.grading) hLhom hRhom
  exact AlgHom.congr_fun hhom w

end KitSigned

/-! ### The two factorizations through the bifusion -/

section Signed

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The flat-spelled size identity of the cluster route cast. -/
private theorem castR_cl (a b c d : ZMod 8) :
    ((fuseSize c d).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize c d).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).1)
      = sizeL (a + b) c d :=
  (sizeL_eq_sizeR (a + b) c d).symm

/-- **The (cd)-side factorization through the bifusion**: the landed
`cluster35Tail3 ∘ cluster35Prefix` composite equals the shared tail
applied to the `γ`-first stabilization order `E2` of the bifused
pair. -/
theorem tail3_prefix_eq (a b c d : ZMod 8)
    (w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).carrier) :
    (cluster35Tail3 a b c d).toAlgEquiv
        ((cluster35Prefix a b c d).toAlgEquiv w)
      = (cluster35SharedTail a b c d).toAlgEquiv
        (((matrixSuperComp (stdTower (a + b + (c + d)))
            (fuseSize a b).1 (fuseSize a b).2
            (fuseSize (a + b) (c + d)).1
            (fuseSize (a + b) (c + d)).2).matrixSuper
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
          ((((stdFuse (a + b) (c + d)).matrixSuper (fuseSize a b).1
              (fuseSize a b).2).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv
            (((matrixSuperGtensor (stdTower (a + b))
                (stdTower (c + d)) (fuseSize a b).1
                (fuseSize a b).2).matrixSuper
                (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
              ((matrixSuperGtensorRight
                  ((stdTower (a + b)).matrixSuper (fuseSize a b).1
                    (fuseSize a b).2)
                  (stdTower (c + d)) (fuseSize c d).1
                  (fuseSize c d).2).toAlgEquiv
                (((stdFuse a b).gtensorCongr
                    (stdFuse c d)).toAlgEquiv
                  ((gtensorAssoc ((stdTower a).gtensor (stdTower b))
                      (stdTower c)
                      (stdTower d)).toAlgEquiv w)))))) := by
  show (cluster35SharedTail a b c d).toAlgEquiv
      (((routeL a b (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv
        ((matrixSuperGtensorRight ((stdTower a).gtensor (stdTower b))
            (stdTower (c + d)) (fuseSize c d).1
            (fuseSize c d).2).toAlgEquiv
          (((SuperAlgEquiv.refl ((stdTower a).gtensor
              (stdTower b))).gtensorCongr (stdFuse c d)).toAlgEquiv
            ((gtensorAssoc ((stdTower a).gtensor (stdTower b))
                (stdTower c) (stdTower d)).toAlgEquiv w))))
    = _
  have hRL : ∀ V : ((((stdTower (K := K) a).gtensor
        (stdTower b)).gtensor (stdTower (c + d))).matrixSuper
        (fuseSize c d).1 (fuseSize c d).2).carrier,
      ((routeL a b (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv V
      = ((matrixSuperComp (stdTower (a + b + (c + d)))
            (fuseSize a b).1 (fuseSize a b).2
            (fuseSize (a + b) (c + d)).1
            (fuseSize (a + b) (c + d)).2).matrixSuper
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
          ((((stdFuse (a + b) (c + d)).matrixSuper (fuseSize a b).1
              (fuseSize a b).2).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv
            (((matrixSuperGtensor (stdTower (a + b))
                (stdTower (c + d)) (fuseSize a b).1
                (fuseSize a b).2).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).toAlgEquiv
              ((((stdFuse a b).gtensorCongr
                  (SuperAlgEquiv.refl
                    (stdTower (c + d)))).matrixSuper
                  (fuseSize c d).1
                  (fuseSize c d).2).toAlgEquiv V))) :=
    fun V => rfl
  rw [hRL]
  have hNat := matrixSuperGtensorRight_full_natural_apply
    (stdFuse a b) (SuperAlgEquiv.refl (stdTower (c + d)))
    (fuseSize c d).1 (fuseSize c d).2
    (((SuperAlgEquiv.refl ((stdTower a).gtensor
        (stdTower b))).gtensorCongr (stdFuse c d)).toAlgEquiv
      ((gtensorAssoc ((stdTower a).gtensor (stdTower b))
          (stdTower c) (stdTower d)).toAlgEquiv w))
  rw [← hNat]
  -- collapse the two congruence stages onto the bifusion
  rw [gtensorCongr_right_eq_apply (stdFuse a b)
    ((SuperAlgEquiv.refl (stdTower (c + d))).matrixSuper
      (fuseSize c d).1 (fuseSize c d).2)
    (SuperAlgEquiv.refl ((stdTower (c + d)).matrixSuper
      (fuseSize c d).1 (fuseSize c d).2))
    (fun y => matrixSuper_refl_apply (fuseSize c d).1
      (fuseSize c d).2 y)]
  have htrans := gtensorCongr_trans_apply
    (SuperAlgEquiv.refl ((stdTower (K := K) a).gtensor (stdTower b)))
    (stdFuse a b) (stdFuse c d)
    (SuperAlgEquiv.refl ((stdTower (c + d)).matrixSuper
      (fuseSize c d).1 (fuseSize c d).2))
    ((gtensorAssoc ((stdTower a).gtensor (stdTower b)) (stdTower c)
        (stdTower d)).toAlgEquiv w)
  rw [← htrans,
    gtensorCongr_left_eq_apply
      ((SuperAlgEquiv.refl ((stdTower (K := K) a).gtensor
        (stdTower b))).trans (stdFuse a b)) (stdFuse a b)
      ((stdFuse c d).trans (SuperAlgEquiv.refl
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2)))
      (fun x => rfl),
    gtensorCongr_right_eq_apply (stdFuse a b)
      ((stdFuse c d).trans (SuperAlgEquiv.refl
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2))) (stdFuse c d)
      (fun y => rfl)]

/-- **The (ab)-side factorization through the bifusion**: the landed
`quadRoute3` equals the `(ab)`-cluster shared tail applied to the
`σ`-first stabilization order `E1` of the bifused pair. -/
theorem quadRoute3_prefix_eq (a b c d : ZMod 8)
    (w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).carrier) :
    (quadRoute3 a b c d).toAlgEquiv w
      = (cluster13SharedTail a b c d).toAlgEquiv
        (((stdMatrixCast (add_assoc (a + b) c d).symm
              (castR_cl a b c d)).matrixSuper (fuseSize a b).1
            (fuseSize a b).2).toAlgEquiv
          (((matrixSuperComp (stdTower (a + b + (c + d)))
                (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1
                (fuseSize (a + b) (c + d)).2).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
            ((((stdFuse (a + b) (c + d)).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).matrixSuper
                (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
              (((matrixSuperGtensorRight (stdTower (a + b))
                    (stdTower (c + d)) (fuseSize c d).1
                    (fuseSize c d).2).matrixSuper (fuseSize a b).1
                  (fuseSize a b).2).toAlgEquiv
                ((matrixSuperGtensor (stdTower (a + b))
                    ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                      (fuseSize c d).2) (fuseSize a b).1
                    (fuseSize a b).2).toAlgEquiv
                  (((stdFuse a b).gtensorCongr
                      (stdFuse c d)).toAlgEquiv
                    ((gtensorAssoc ((stdTower a).gtensor
                        (stdTower b)) (stdTower c)
                        (stdTower d)).toAlgEquiv w))))))) := by
  show (cluster13SharedTail a b c d).toAlgEquiv
      (((routeR (a + b) c d).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower (a + b)).gtensor (stdTower c))
            (stdTower d) (fuseSize a b).1
            (fuseSize a b).2).toAlgEquiv
          (((matrixSuperGtensor (stdTower (a + b)) (stdTower c)
                (fuseSize a b).1 (fuseSize a b).2).gtensorCongr
              (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv
            ((((stdFuse a b).gtensorCongr
                (SuperAlgEquiv.refl (stdTower c))).gtensorCongr
              (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w))))
    = _
  have hRR : ∀ V : ((((stdTower (K := K) (a + b)).gtensor
        (stdTower c)).gtensor (stdTower d)).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).carrier,
      ((routeR (a + b) c d).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).toAlgEquiv V
      = ((stdMatrixCast (add_assoc (a + b) c d).symm
            (castR_cl a b c d)).matrixSuper (fuseSize a b).1
            (fuseSize a b).2).toAlgEquiv
          (((matrixSuperComp (stdTower (a + b + (c + d)))
                (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1
                (fuseSize (a + b) (c + d)).2).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
            ((((stdFuse (a + b) (c + d)).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).matrixSuper
                (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
              (((matrixSuperGtensorRight (stdTower (a + b))
                    (stdTower (c + d)) (fuseSize c d).1
                    (fuseSize c d).2).matrixSuper (fuseSize a b).1
                  (fuseSize a b).2).toAlgEquiv
                ((((SuperAlgEquiv.refl
                      (stdTower (a + b))).gtensorCongr
                    (stdFuse c d)).matrixSuper (fuseSize a b).1
                    (fuseSize a b).2).toAlgEquiv
                  (((gtensorAssoc (stdTower (a + b)) (stdTower c)
                        (stdTower d)).matrixSuper (fuseSize a b).1
                      (fuseSize a b).2).toAlgEquiv V))))) :=
    fun V => rfl
  rw [hRR]
  -- the left-slot stabilization hexagon
  have hHexL := matrixSuperGtensor_gassoc_left_apply
    (X := stdTower (K := K) (a + b)) (C := stdTower c)
    (D := stdTower d) (fuseSize a b).1 (fuseSize a b).2
    ((((stdFuse a b).gtensorCongr
        (SuperAlgEquiv.refl (stdTower c))).gtensorCongr
      (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w)
  rw [hHexL]
  -- mSG full naturality moves the cluster fusion inside
  have hNat := matrixSuperGtensor_full_natural_apply
    (SuperAlgEquiv.refl (stdTower (K := K) (a + b))) (stdFuse c d)
    (fuseSize a b).1 (fuseSize a b).2
    ((gtensorAssoc ((stdTower (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2) (stdTower c) (stdTower d)).toAlgEquiv
      ((((stdFuse a b).gtensorCongr
          (SuperAlgEquiv.refl (stdTower c))).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w))
  rw [← hNat]
  -- naturality of the associator against the (ab)-fusion
  have hAssocNat := gassoc_natural_apply (stdFuse a b)
    (SuperAlgEquiv.refl (stdTower c))
    (SuperAlgEquiv.refl (stdTower d)) w
  rw [hAssocNat, gtensorCongr_reflpair_right_apply]
  -- collapse the congruence stages onto the bifusion
  rw [gtensorCongr_left_eq_apply
    ((SuperAlgEquiv.refl (stdTower (K := K) (a + b))).matrixSuper
      (fuseSize a b).1 (fuseSize a b).2)
    (SuperAlgEquiv.refl ((stdTower (a + b)).matrixSuper
      (fuseSize a b).1 (fuseSize a b).2))
    (stdFuse c d)
    (fun x => matrixSuper_refl_apply (fuseSize a b).1
      (fuseSize a b).2 x)]
  have htrans := gtensorCongr_trans_apply (stdFuse a b)
    (SuperAlgEquiv.refl ((stdTower (K := K) (a + b)).matrixSuper
      (fuseSize a b).1 (fuseSize a b).2))
    (SuperAlgEquiv.refl ((stdTower c).gtensor (stdTower d)))
    (stdFuse c d)
    ((gtensorAssoc ((stdTower a).gtensor (stdTower b)) (stdTower c)
        (stdTower d)).toAlgEquiv w)
  rw [← htrans,
    gtensorCongr_left_eq_apply
      ((stdFuse a b).trans (SuperAlgEquiv.refl
        ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2))) (stdFuse a b)
      ((SuperAlgEquiv.refl ((stdTower c).gtensor
        (stdTower d))).trans (stdFuse c d))
      (fun x => rfl),
    gtensorCongr_right_eq_apply (stdFuse a b)
      ((SuperAlgEquiv.refl ((stdTower c).gtensor
        (stdTower d))).trans (stdFuse c d)) (stdFuse c d)
      (fun y => rfl)]

end Signed

end Superfusion

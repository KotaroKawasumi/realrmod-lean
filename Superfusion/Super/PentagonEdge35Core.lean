/-
Superfusion / Super / PentagonEdge35Core

Milestone M7d-5b-4-iii(c), part 6: **the core layer-swap comparison
and the closing e35 theorems** — `quadRoute3_factor35_signed` and
`edgeT35_intertwines`.

Both sides of the signed F3′ factor through the bifusion (the landed
`tail3_prefix_eq` / `quadRoute3_prefix_eq`); this file compares the
two stabilization orders on `M_σ(T_{a+b}) ᵍ⊗ M_γ(T_{c+d})` on the
slot generators, with the tail-decode compatibilities derived
structurally from the landed swap-unit certificates (no new large
kernel certificates: `φ ∘ encodeL = encodeR` is definitional and the
involution is extracted from the landed `swapSign_mul_self`).
-/
import Superfusion.Super.PentagonEdge35Signed

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

/-! ### Local copies of landed private helpers -/

section CoreKit

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


end CoreKit

/-! ### The swap-index machinery (local copies, definitionally equal
to the landed private ones) -/

section SwapCopies

/-- Cast of a flat `p|q`-index along an equality of size pairs. -/
private def sumFinCast {s t : ℕ × ℕ} (h : s = t) :
    Fin s.1 ⊕ Fin s.2 → Fin t.1 ⊕ Fin t.2 :=
  Sum.map (Fin.cast (congrArg Prod.fst h))
    (Fin.cast (congrArg Prod.snd h))

/-- The generic layer-swap index map: decode the flat pentagon-frame
index through the `(s,t,r)`-grouping (the `(ab)`-cluster shared
tail), transpose the two outer layers, and re-encode through the
`(g,m,n)`-grouping (the `(cd)`-cluster shared tail).  Here
`s,g,k,t,r,m,n` play `σ,γ,κ,τ,ρ,μ,ν′`. -/
private def swapIdxGen (s g k t r m n : ℕ × ℕ)
    (hcl : (t.1 * r.1 + t.2 * r.2, t.1 * r.2 + t.2 * r.1)
      = (g.1 * k.1 + g.2 * k.2, g.1 * k.2 + g.2 * k.1))
    (h35 : (s.1 * k.1 + s.2 * k.2, s.1 * k.2 + s.2 * k.1)
      = (m.1 * n.1 + m.2 * n.2, m.1 * n.2 + m.2 * n.1))
    (hout : ((g.1 * m.1 + g.2 * m.2) * n.1
          + (g.1 * m.2 + g.2 * m.1) * n.2,
        (g.1 * m.1 + g.2 * m.2) * n.2
          + (g.1 * m.2 + g.2 * m.1) * n.1)
      = ((s.1 * t.1 + s.2 * t.2) * r.1
          + (s.1 * t.2 + s.2 * t.1) * r.2,
        (s.1 * t.1 + s.2 * t.2) * r.2
          + (s.1 * t.2 + s.2 * t.1) * r.1))
    (i : Fin ((s.1 * t.1 + s.2 * t.2) * r.1
        + (s.1 * t.2 + s.2 * t.1) * r.2)
      ⊕ Fin ((s.1 * t.1 + s.2 * t.2) * r.2
        + (s.1 * t.2 + s.2 * t.1) * r.1)) :
    Fin ((s.1 * t.1 + s.2 * t.2) * r.1
        + (s.1 * t.2 + s.2 * t.1) * r.2)
      ⊕ Fin ((s.1 * t.1 + s.2 * t.2) * r.2
        + (s.1 * t.2 + s.2 * t.1) * r.1) :=
  let zr := (collapseIndexEquiv (s.1 * t.1 + s.2 * t.2)
      (s.1 * t.2 + s.2 * t.1) r.1 r.2).symm i
  let It := (collapseIndexEquiv s.1 s.2 t.1 t.2).symm zr.1
  let Kn := (collapseIndexEquiv g.1 g.2 k.1 k.2).symm
    (sumFinCast hcl (collapseIndexEquiv t.1 t.2 r.1 r.2 (It.2, zr.2)))
  let mn := (collapseIndexEquiv m.1 m.2 n.1 n.2).symm
    (sumFinCast h35 (collapseIndexEquiv s.1 s.2 k.1 k.2 (It.1, Kn.2)))
  sumFinCast hout
    (collapseIndexEquiv (g.1 * m.1 + g.2 * m.2) (g.1 * m.2 + g.2 * m.1)
      n.1 n.2 (collapseIndexEquiv g.1 g.2 m.1 m.2 (Kn.1, mn.1), mn.2))

/-- The Koszul sign exponent of the layer swap at a flat
pentagon-frame index: the product of the `σ`-parity and the
`γ`-parity of its decoding. -/
private def swapParityGen (s g k t r : ℕ × ℕ)
    (hcl : (t.1 * r.1 + t.2 * r.2, t.1 * r.2 + t.2 * r.1)
      = (g.1 * k.1 + g.2 * k.2, g.1 * k.2 + g.2 * k.1))
    (i : Fin ((s.1 * t.1 + s.2 * t.2) * r.1
        + (s.1 * t.2 + s.2 * t.1) * r.2)
      ⊕ Fin ((s.1 * t.1 + s.2 * t.2) * r.2
        + (s.1 * t.2 + s.2 * t.1) * r.1)) : ZMod 2 :=
  let zr := (collapseIndexEquiv (s.1 * t.1 + s.2 * t.2)
      (s.1 * t.2 + s.2 * t.1) r.1 r.2).symm i
  let It := (collapseIndexEquiv s.1 s.2 t.1 t.2).symm zr.1
  let Kn := (collapseIndexEquiv g.1 g.2 k.1 k.2).symm
    (sumFinCast hcl (collapseIndexEquiv t.1 t.2 r.1 r.2 (It.2, zr.2)))
  sumParity s.1 s.2 It.1 * sumParity g.1 g.2 Kn.1


end SwapCopies

section CoreField

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The standard fusion sizes take exactly two values (local copy of
the private helper of `PentagonEdge24.lean`). -/
private theorem fuseSize_cases (a b : ZMod 8) :
    fuseSize a b = (1, 0) ∨ fuseSize a b = (8, 8) := by
  unfold fuseSize
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The `(σ,τ,ρ)`-to-`(γ,κ)` cast identity of the `(ab)`-cluster
tail, flat-spelled. -/
private theorem swapCast_cl (a b c d : ZMod 8) :
    ((fuseSize (a + b) c).1 * (fuseSize (a + b + c) d).1
        + (fuseSize (a + b) c).2 * (fuseSize (a + b + c) d).2,
      (fuseSize (a + b) c).1 * (fuseSize (a + b + c) d).2
        + (fuseSize (a + b) c).2 * (fuseSize (a + b + c) d).1)
      = ((fuseSize c d).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize c d).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).1) :=
  sizeL_eq_sizeR (a + b) c d

/-- The `(σ,κ)`-to-`(μ,ν′)` cast identity of the `(cd)`-cluster
tail, flat-spelled. -/
private theorem swapCast_35 (a b c d : ZMod 8) :
    ((fuseSize a b).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize a b).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize a b).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize a b).2 * (fuseSize (a + b) (c + d)).1)
      = ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2,
      (fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1) :=
  sizeL_eq_sizeR a b (c + d)

/-- The `(γ,μ,ν′)`-to-`(σ,τ,ρ)` output cast identity, flat-spelled
(a 4096-case kernel `decide`). -/
private theorem swapCast_out : ∀ a b c d : ZMod 8,
    (((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          * (fuseSize a (b + (c + d))).1
        + ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)
          * (fuseSize a (b + (c + d))).2,
      ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          * (fuseSize a (b + (c + d))).2
        + ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)
          * (fuseSize a (b + (c + d))).1)
      = (((fuseSize a b).1 * (fuseSize (a + b) c).1
          + (fuseSize a b).2 * (fuseSize (a + b) c).2)
          * (fuseSize (a + b + c) d).1
        + ((fuseSize a b).1 * (fuseSize (a + b) c).2
          + (fuseSize a b).2 * (fuseSize (a + b) c).1)
          * (fuseSize (a + b + c) d).2,
      ((fuseSize a b).1 * (fuseSize (a + b) c).1
          + (fuseSize a b).2 * (fuseSize (a + b) c).2)
          * (fuseSize (a + b + c) d).2
        + ((fuseSize a b).1 * (fuseSize (a + b) c).2
          + (fuseSize a b).2 * (fuseSize (a + b) c).1)
          * (fuseSize (a + b + c) d).1) := by
  decide

/-- The layer-swap index involution at the pentagon frame. -/
private def swapIdx35 (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2 :=
  swapIdxGen (fuseSize a b) (fuseSize c d) (fuseSize (a + b) (c + d))
    (fuseSize (a + b) c) (fuseSize (a + b + c) d) (fuseSize b (c + d))
    (fuseSize a (b + (c + d))) (swapCast_cl a b c d)
    (swapCast_35 a b c d) (swapCast_out a b c d) i

/-- The Koszul sign exponent at the pentagon frame. -/
private def swapParity35 (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) : ZMod 2 :=
  swapParityGen (fuseSize a b) (fuseSize c d)
    (fuseSize (a + b) (c + d)) (fuseSize (a + b) c)
    (fuseSize (a + b + c) d) (swapCast_cl a b c d) i


/-- The flat-spelled size identity of the cluster route cast (local
copy of the private helper of `PentagonEdge35Signed.lean`). -/
private theorem castR_clC (a b c d : ZMod 8) :
    ((fuseSize c d).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize c d).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).1)
      = sizeL (a + b) c d :=
  (sizeL_eq_sizeR (a + b) c d).symm

private theorem zmod2_zero_add_add_selfC : ∀ x : ZMod 2,
    (0 : ZMod 2) + x + x = 0 := by decide

/-- The signed swap unit, at the raw matrix type (local copy of the
landed private `swapSignM`, verbatim). -/
private noncomputable def swapSignMC (a b c d : ZMod 8) :
    Matrix
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (stdTower (K := K) (a + b + c + d)).carrier :=
  Matrix.of fun i j =>
    if j = swapIdx35 a b c d i
    then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
      (1 : (stdTower (K := K) (a + b + c + d)).carrier)
    else 0

omit [Invertible (2 : K)] in
/-- The local `swapSign`-matrix is the landed `swapSign`, by `rfl`:
both `swapSignM`/`swapSignMC` unfold to the identical `Matrix.of`
term once the (defeq) local copies of `swapIdx35`/`swapParity35` are
substituted. -/
theorem swapSign_eq (a b c d : ZMod 8) :
    (swapSign (K := K) a b c d : Matrix _ _ _) = swapSignMC a b c d := rfl

omit [Invertible (2 : K)] in
/-- Every entry of `swapSignMC * swapSignMC` at `(i, φ(φ i))` is `0`
unless `φ(φ i) = i`, in which case it is the nonzero signed unit — a
restatement of `swapSignM_mul_self`'s proof, entrywise, kept generic
in the target index `k`. -/
private theorem swapSignMC_mul_apply (a b c d : ZMod 8)
    (i k : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    ((swapSignMC (K := K) a b c d * swapSignMC a b c d :
        Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier)) i k
      = if k = swapIdx35 a b c d (swapIdx35 a b c d i)
        then (((sgn (swapParity35 a b c d i)
            * sgn (swapParity35 a b c d (swapIdx35 a b c d i)) : ℤˣ) : ℤ)) •
          (1 : (stdTower (K := K) (a + b + c + d)).carrier)
        else 0 := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (swapIdx35 a b c d i)
      (fun j _ hj => by
        show (if j = swapIdx35 a b c d i
            then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
              (1 : (stdTower (K := K) (a + b + c + d)).carrier)
            else 0) * swapSignMC a b c d j k = 0
        rw [if_neg hj, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
  show (if swapIdx35 a b c d i = swapIdx35 a b c d i
      then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
        (1 : (stdTower (K := K) (a + b + c + d)).carrier)
      else 0)
    * (if k = swapIdx35 a b c d (swapIdx35 a b c d i)
        then ((sgn (swapParity35 a b c d
            (swapIdx35 a b c d i)) : ℤˣ) : ℤ) •
          (1 : (stdTower (K := K) (a + b + c + d)).carrier)
        else 0)
    = if k = swapIdx35 a b c d (swapIdx35 a b c d i)
      then (((sgn (swapParity35 a b c d i)
          * sgn (swapParity35 a b c d (swapIdx35 a b c d i)) : ℤˣ) : ℤ)) •
        (1 : (stdTower (K := K) (a + b + c + d)).carrier)
      else 0
  rw [if_pos rfl]
  by_cases hk : k = swapIdx35 a b c d (swapIdx35 a b c d i)
  · rw [if_pos hk, if_pos hk, smul_mul_smul_comm, one_mul, ← Units.val_mul]
  · rw [if_neg hk, if_neg hk, mul_zero]

/-- **The layer-swap index involution** (extracted from the landed
public `swapSign_mul_self`, no new large `decide`). -/
theorem phi_invol (K : Type u) [Field K] [Invertible (2 : K)]
    (a b c d : ZMod 8) :
    ∀ i, swapIdx35 a b c d (swapIdx35 a b c d i) = i := by
  intro i
  by_contra hne
  have hmul0 := swapSign_mul_self (K := K) a b c d
  have hcast : ((swapSign (K := K) a b c d * swapSign a b c d :
        ((stdTower (K := K) (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).carrier) :
      Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier)
      = swapSignMC a b c d * swapSignMC a b c d := by
    rw [← swapSign_eq]; rfl
  have hmul : ((swapSignMC a b c d * swapSignMC a b c d :
        Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier)) i
      (swapIdx35 a b c d (swapIdx35 a b c d i))
      = (1 : Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier) i
        (swapIdx35 a b c d (swapIdx35 a b c d i)) :=
    congrFun (congrFun (hcast ▸ (congrArg (fun M =>
      (M : Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier))
      hmul0)) i) (swapIdx35 a b c d (swapIdx35 a b c d i))
  rw [swapSignMC_mul_apply, if_pos rfl,
    Matrix.one_apply_ne (Ne.symm hne)] at hmul
  rcases Int.units_eq_one_or (sgn (swapParity35 a b c d i)
      * sgn (swapParity35 a b c d (swapIdx35 a b c d i)) : ℤˣ) with h1 | h1 <;>
    rw [h1] at hmul <;>
    simp only [Units.val_one, Units.val_neg, one_smul, neg_smul] at hmul
  · exact one_ne_zero hmul
  · exact one_ne_zero (neg_eq_zero.mp hmul)

omit [Invertible (2 : K)] in
/-- **Sign compatibility of the involution** (extracted from the
landed public `swapSign_mul_self`, no new large `decide`): if the
signs at `i` disagreed, the `(i,i)`-entry of `W * W` would compute to
`-1`, contradicting `Invertible (2 : K)` (which forces `1 ≠ -1` in
every `K`-algebra). -/
theorem eps_phi (K : Type u) [Field K] [Invertible (2 : K)]
    (a b c d : ZMod 8) :
    ∀ i, swapParity35 a b c d (swapIdx35 a b c d i)
      = swapParity35 a b c d i := by
  intro i
  have hmul0 := swapSign_mul_self (K := K) a b c d
  have hcast : ((swapSign (K := K) a b c d * swapSign a b c d :
        ((stdTower (K := K) (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).carrier) :
      Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier)
      = swapSignMC a b c d * swapSignMC a b c d := by
    rw [← swapSign_eq]; rfl
  have hmul : ((swapSignMC a b c d * swapSignMC a b c d :
        Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier)) i i
      = (1 : Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier) i i :=
    congrFun (congrFun (hcast ▸ (congrArg (fun M =>
      (M : Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier))
      hmul0)) i) i
  rw [swapSignMC_mul_apply, if_pos (phi_invol K a b c d i).symm,
    Matrix.one_apply_eq] at hmul
  by_contra hne
  -- `Invertible (2 : K)` forces `1 ≠ -1` in the carrier.
  haveI : Invertible (2 : (stdTower (K := K) (a + b + c + d)).carrier) :=
    (Invertible.map (algebraMap K
      (stdTower (K := K) (a + b + c + d)).carrier) 2).copy 2
      (by rw [map_ofNat])
  have hne1 : (1 : (stdTower (K := K) (a + b + c + d)).carrier) ≠ -1 := by
    intro hcontra
    have h2 : (2 : (stdTower (K := K) (a + b + c + d)).carrier) = 0 := by
      have h21 : (2 : (stdTower (K := K) (a + b + c + d)).carrier) = 1 + 1 :=
        by norm_num
      have h1n1 : (1 : (stdTower (K := K) (a + b + c + d)).carrier)
          + (-1 : (stdTower (K := K) (a + b + c + d)).carrier) = 0 :=
        add_neg_cancel 1
      rw [h21]
      nth_rewrite 2 [hcontra]
      exact h1n1
    exact Invertible.ne_zero
      (2 : (stdTower (K := K) (a + b + c + d)).carrier) h2
  rcases Int.units_eq_one_or (sgn (swapParity35 a b c d i)
      * sgn (swapParity35 a b c d (swapIdx35 a b c d i)) : ℤˣ) with h1 | h1 <;>
    rw [h1] at hmul <;>
    simp only [Units.val_one, Units.val_neg, one_smul, neg_smul] at hmul
  · -- signs agree: `sgn εᵢ * sgn ε_{φi} = 1`, giving `εᵢ = ε_{φi}`,
    -- contradicting `hne : parities differ`.
    apply hne
    rcases zmod2_cases (swapParity35 a b c d i) with he | he <;>
      rcases zmod2_cases (swapParity35 a b c d (swapIdx35 a b c d i))
        with he' | he' <;>
      simp_all [sgn]
  · exact hne1 hmul.symm

omit [Invertible (2 : K)] in
/-- Left multiplication by `swapSign` reindexes rows through `φ`,
picking up the sign at the source row (raw `Matrix`-level entry
formula, transported by `swapSign_eq`). -/
theorem swapSign_mul_apply (a b c d : ZMod 8)
    (M : Matrix
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (stdTower (K := K) (a + b + c + d)).carrier)
    (i j : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    ((swapSignMC (K := K) a b c d * M)) i j
      = ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
        M (swapIdx35 a b c d i) j := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (swapIdx35 a b c d i)
      (fun k _ hk => by
        show (if k = swapIdx35 a b c d i
            then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
              (1 : (stdTower (K := K) (a + b + c + d)).carrier)
            else 0) * M k j = 0
        rw [if_neg hk, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
  show (if swapIdx35 a b c d i = swapIdx35 a b c d i
      then ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
        (1 : (stdTower (K := K) (a + b + c + d)).carrier)
      else 0) * M (swapIdx35 a b c d i) j
    = ((sgn (swapParity35 a b c d i) : ℤˣ) : ℤ) •
      M (swapIdx35 a b c d i) j
  rw [if_pos rfl, smul_mul_assoc, one_mul]

/-- Right multiplication by `swapSign` reindexes columns through
`φ`, picking up the sign at the target column. -/
theorem mul_swapSign_apply (a b c d : ZMod 8)
    (M : Matrix
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (Fin (extSize (sizeL a b c) (a + b + c) d).1
        ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2)
      (stdTower (K := K) (a + b + c + d)).carrier)
    (i j : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    ((M * swapSignMC (K := K) a b c d)) i j
      = ((sgn (swapParity35 a b c d j) : ℤˣ) : ℤ) •
        M i (swapIdx35 a b c d j) := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (swapIdx35 a b c d j)
      (fun k _ hk => by
        show M i k * (if j = swapIdx35 a b c d k
            then ((sgn (swapParity35 a b c d k) : ℤˣ) : ℤ) •
              (1 : (stdTower (K := K) (a + b + c + d)).carrier)
            else 0) = 0
        rw [if_neg (fun h => hk (by
          rw [← phi_invol K a b c d k, h]))]
        exact mul_zero _)
      (fun h => absurd (Finset.mem_univ _) h)]
  show M i (swapIdx35 a b c d j)
      * (if j = swapIdx35 a b c d (swapIdx35 a b c d j)
        then ((sgn (swapParity35 a b c d
            (swapIdx35 a b c d j)) : ℤˣ) : ℤ) •
          (1 : (stdTower (K := K) (a + b + c + d)).carrier)
        else 0)
    = ((sgn (swapParity35 a b c d j) : ℤˣ) : ℤ) •
      M i (swapIdx35 a b c d j)
  rw [if_pos (phi_invol K a b c d j).symm, eps_phi K a b c d j,
    mul_smul_comm, mul_one]

omit [Invertible (2 : K)] in
/-- **Conjugation by `swapSign`**, as an algebra homomorphism of the
pentagon-frame matrix superalgebra: `x ↦ W * x * W`.  Well-defined
since `W * W = 1` (`map_one` via `swapSign_mul_self`; `map_mul` by
inserting `W * W = 1` in the middle; `commutes'` since the image of
`algebraMap` is central and `W * W = 1`). -/
noncomputable def conjSwapHom (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier →ₐ[K]
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier where
  toFun x := swapSign a b c d * x * swapSign a b c d
  map_one' := by rw [mul_one, swapSign_mul_self]
  map_mul' x y := by
    rw [show swapSign (K := K) a b c d * (x * y) * swapSign a b c d
        = swapSign a b c d * x
          * (swapSign a b c d * swapSign a b c d) * y * swapSign a b c d
        from by rw [swapSign_mul_self]; noncomm_ring]
    noncomm_ring
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' x y := by rw [mul_add, add_mul]
  commutes' r := by
    show swapSign (K := K) a b c d * algebraMap K _ r * swapSign a b c d
      = algebraMap K _ r
    rw [← Algebra.commutes, mul_assoc, swapSign_mul_self, mul_one]

end CoreField

/-! ### The matrix parity projection entry lemma -/

section ParityEntry

universe u

variable {K : Type u} [CommRing K]

/-- The even part of a matrix in `M_{p|q}(P)` is computed entrywise:
the `(r,s)`-entry is the even or odd part of the `(r,s)`-entry of the
underlying matrix, according to the flat-index parity. -/
theorem evenPart_matrixSuper_apply {P : SuperAlgebra K} (p q : ℕ)
    (M : (P.matrixSuper p q).carrier) (r s : Fin p ⊕ Fin q) :
    (evenPart (P.matrixSuper p q).grading M) r s
      = if sumParity p q r + sumParity p q s = 0
        then evenPart P.grading (M r s) else oddPart P.grading (M r s) := by
  set E' : (P.matrixSuper p q).carrier := Matrix.of (fun r s =>
    if sumParity p q r + sumParity p q s = 0
      then evenPart P.grading (M r s) else oddPart P.grading (M r s))
    with hE'
  set O' : (P.matrixSuper p q).carrier := Matrix.of (fun r s =>
    if sumParity p q r + sumParity p q s = 0
      then oddPart P.grading (M r s) else evenPart P.grading (M r s))
    with hO'
  have hzero : ∀ x y : ZMod 2, x + y = 0 → (0 : ZMod 2) + x + y = 0 := by
    decide
  have hone : ∀ x y : ZMod 2, x + y = 0 → (1 : ZMod 2) + x + y = 1 := by
    decide
  have hzero' : ∀ x y : ZMod 2, ¬ x + y = 0 → (0 : ZMod 2) + x + y = 1 := by
    decide
  have hone' : ∀ x y : ZMod 2, ¬ x + y = 0 → (1 : ZMod 2) + x + y = 0 := by
    decide
  have hE'mem : E' ∈ (P.matrixSuper p q).grading 0 := by
    intro a b
    show (if sumParity p q a + sumParity p q b = 0
        then evenPart P.grading (M a b) else oddPart P.grading (M a b))
      ∈ P.grading (0 + sumParity p q a + sumParity p q b)
    by_cases hab : sumParity p q a + sumParity p q b = 0
    · rw [if_pos hab, hzero _ _ hab]
      exact evenPart_mem P.grading (M a b)
    · rw [if_neg hab, hzero' _ _ hab]
      exact oddPart_mem P.grading (M a b)
  have hO'mem : O' ∈ (P.matrixSuper p q).grading 1 := by
    intro a b
    show (if sumParity p q a + sumParity p q b = 0
        then oddPart P.grading (M a b) else evenPart P.grading (M a b))
      ∈ P.grading (1 + sumParity p q a + sumParity p q b)
    by_cases hab : sumParity p q a + sumParity p q b = 0
    · rw [if_pos hab, hone _ _ hab]
      exact oddPart_mem P.grading (M a b)
    · rw [if_neg hab, hone' _ _ hab]
      exact evenPart_mem P.grading (M a b)
  have hsum : E' + O' = M := by
    refine Matrix.ext fun a b => ?_
    show (if sumParity p q a + sumParity p q b = 0
        then evenPart P.grading (M a b) else oddPart P.grading (M a b))
      + (if sumParity p q a + sumParity p q b = 0
        then oddPart P.grading (M a b) else evenPart P.grading (M a b))
      = M a b
    by_cases hab : sumParity p q a + sumParity p q b = 0
    · rw [if_pos hab, if_pos hab, evenPart_add_oddPart]
    · rw [if_neg hab, if_neg hab, add_comm, evenPart_add_oddPart]
  have hcalc : evenPart (P.matrixSuper p q).grading M = E' := by
    rw [← hsum, map_add, evenPart_of_mem_zero _ hE'mem,
      evenPart_of_mem_one _ hO'mem, add_zero]
  rw [hcalc]
  show (if sumParity p q r + sumParity p q s = 0
      then evenPart P.grading (M r s) else oddPart P.grading (M r s)) = _
  rfl

/-- The odd part of a matrix in `M_{p|q}(P)` is computed entrywise,
complementarily to `evenPart_matrixSuper_apply`. -/
theorem oddPart_matrixSuper_apply {P : SuperAlgebra K} (p q : ℕ)
    (M : (P.matrixSuper p q).carrier) (r s : Fin p ⊕ Fin q) :
    (oddPart (P.matrixSuper p q).grading M) r s
      = if sumParity p q r + sumParity p q s = 0
        then oddPart P.grading (M r s) else evenPart P.grading (M r s) := by
  set E' : (P.matrixSuper p q).carrier := Matrix.of (fun r s =>
    if sumParity p q r + sumParity p q s = 0
      then evenPart P.grading (M r s) else oddPart P.grading (M r s))
    with hE'
  set O' : (P.matrixSuper p q).carrier := Matrix.of (fun r s =>
    if sumParity p q r + sumParity p q s = 0
      then oddPart P.grading (M r s) else evenPart P.grading (M r s))
    with hO'
  have hzero : ∀ x y : ZMod 2, x + y = 0 → (0 : ZMod 2) + x + y = 0 := by
    decide
  have hone : ∀ x y : ZMod 2, x + y = 0 → (1 : ZMod 2) + x + y = 1 := by
    decide
  have hzero' : ∀ x y : ZMod 2, ¬ x + y = 0 → (0 : ZMod 2) + x + y = 1 := by
    decide
  have hone' : ∀ x y : ZMod 2, ¬ x + y = 0 → (1 : ZMod 2) + x + y = 0 := by
    decide
  have hE'mem : E' ∈ (P.matrixSuper p q).grading 0 := by
    intro a b
    show (if sumParity p q a + sumParity p q b = 0
        then evenPart P.grading (M a b) else oddPart P.grading (M a b))
      ∈ P.grading (0 + sumParity p q a + sumParity p q b)
    by_cases hab : sumParity p q a + sumParity p q b = 0
    · rw [if_pos hab, hzero _ _ hab]
      exact evenPart_mem P.grading (M a b)
    · rw [if_neg hab, hzero' _ _ hab]
      exact oddPart_mem P.grading (M a b)
  have hO'mem : O' ∈ (P.matrixSuper p q).grading 1 := by
    intro a b
    show (if sumParity p q a + sumParity p q b = 0
        then oddPart P.grading (M a b) else evenPart P.grading (M a b))
      ∈ P.grading (1 + sumParity p q a + sumParity p q b)
    by_cases hab : sumParity p q a + sumParity p q b = 0
    · rw [if_pos hab, hone _ _ hab]
      exact oddPart_mem P.grading (M a b)
    · rw [if_neg hab, hone' _ _ hab]
      exact evenPart_mem P.grading (M a b)
  have hsum : E' + O' = M := by
    refine Matrix.ext fun a b => ?_
    show (if sumParity p q a + sumParity p q b = 0
        then evenPart P.grading (M a b) else oddPart P.grading (M a b))
      + (if sumParity p q a + sumParity p q b = 0
        then oddPart P.grading (M a b) else evenPart P.grading (M a b))
      = M a b
    by_cases hab : sumParity p q a + sumParity p q b = 0
    · rw [if_pos hab, if_pos hab, evenPart_add_oddPart]
    · rw [if_neg hab, if_neg hab, add_comm, evenPart_add_oddPart]
  have hcalc : oddPart (P.matrixSuper p q).grading M = O' := by
    rw [← hsum, map_add, oddPart_of_mem_zero _ hE'mem,
      oddPart_of_mem_one _ hO'mem, zero_add]
  rw [hcalc]
  show (if sumParity p q r + sumParity p q s = 0
      then oddPart P.grading (M r s) else evenPart P.grading (M r s)) = _
  rfl

end ParityEntry

/-! ### Tail entry formulas and decode relations -/

section TailEntry

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- Entry formula for a `stdMatrixCast`: reindexing along the flat
cast, by `subst` (the statement is phrased with the cast of `M`'s
value baked into the equation via `h ▸`, since `x` and `y` genuinely
differ as `ZMod 8` terms before `subst`). -/
theorem stdMatrixCast_entry {x y : ZMod 8} (h : x = y) {s t : ℕ × ℕ}
    (hs : s = t)
    (M : ((stdTower (K := K) x).matrixSuper s.1 s.2).carrier)
    (i j : Fin t.1 ⊕ Fin t.2) :
    (stdMatrixCast h hs).toAlgEquiv M i j
      = (h ▸ (M (sumFinCast hs.symm i) (sumFinCast hs.symm j)) :
        (stdTower (K := K) y).carrier) := by
  subst h
  subst hs
  show M i j = M (sumFinCast rfl i) (sumFinCast rfl j)
  have hi : sumFinCast (rfl : s = s) i = i := by
    rcases i with i | i <;> simp [sumFinCast]
  have hj : sumFinCast (rfl : s = s) j = j := by
    rcases j with j | j <;> simp [sumFinCast]
  rw [hi, hj]

/-- The composite index bijection of the inverse
collapse-reassociation bridge (local copy of the private helper of
`PentagonEdge24.lean`). -/
private def assocIdxC (p q p' q' p'' q'' : ℕ)
    (I : Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
      ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p)) :
    Fin (p'' * (p' * p + q' * q) + q'' * (p' * q + q' * p))
      ⊕ Fin (p'' * (p' * q + q' * p) + q'' * (p' * p + q' * q)) :=
  collapseIndexEquiv p'' q'' (p' * p + q' * q) (p' * q + q' * p)
    (((collapseIndexEquiv p'' q'' p' q').symm
        (((collapseIndexEquiv (p'' * p' + q'' * q')
          (p'' * q' + q'' * p') p q).symm I).1)).1,
      collapseIndexEquiv p' q' p q
        ((((collapseIndexEquiv p'' q'' p' q').symm
            (((collapseIndexEquiv (p'' * p' + q'' * q')
              (p'' * q' + q'' * p') p q).symm I).1)).2),
          ((collapseIndexEquiv (p'' * p' + q'' * q')
            (p'' * q' + q'' * p') p q).symm I).2))

omit [Invertible (2 : K)] in
/-- Entry formula for the inverse collapse-reassociation bridge: a
pure reindexing along `assocIdxC` (local copy of the private helper
of `PentagonEdge24.lean`). -/
theorem matrixSuperCompAssoc_symm_entryC {P : SuperAlgebra K}
    (p q p' q' p'' q'' : ℕ)
    (X : (P.matrixSuper
      (p'' * (p' * p + q' * q) + q'' * (p' * q + q' * p))
      (p'' * (p' * q + q' * p) + q'' * (p' * p + q' * q))).carrier)
    (I J : Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
      ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p)) :
    (matrixSuperCompAssoc P p q p' q' p'' q'').symm.toAlgEquiv X I J
      = X (assocIdxC p q p' q' p'' q'' I) (assocIdxC p q p' q' p'' q'' J) :=
  rfl

end TailEntry

end Superfusion

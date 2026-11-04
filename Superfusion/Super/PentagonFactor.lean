/-
Superfusion / Super / PentagonFactor

Milestone M7d-5b-4-iii(b), part 8: **the cluster-edge factorization
and the middle edge e24**.  With `s := b + c`, `f := fuseSize b c`:

- the common prefix
  `Π := ((refl_a ⊗c stdFuse b c) ⊗c refl_d) ∘ (gassoc ⊗c refl_d)`,
- the matrix-frame change
  `Ξ := mSG ∘ (mSGR ⊗c refl_d) : (A ⊗ M_f(T_s)) ⊗ D ≅ M_f((A⊗T_s)⊗D)`,
- the factored tails
  `T2/T4 := Ξ ≫ (routeL/routeR a s d).matrixSuper f ≫ comp ≫ leg`,
  where the final leg is the collapse-reassociation bridge
  `matrixSuperCompAssoc⁻¹` (the two association orders of the
  three-layer matrix collapse differ by a genuine sorting
  permutation, so a bare cast is *false* — see
  `PentagonCompAssoc.lean`) followed by the index/size cast,

satisfy the factorization equalities `quadRoute2 = T2 ∘ Π` and
`alignedRoute4 = T4 ∘ Π`.  The second one additionally needs the
**stabilization associator hexagon**
(`matrixSuperGtensorRight_gassoc_apply`): pulling the matrix layer
out of the middle slot after reassociating agrees with pulling it out
of the left pair and reassociating entrywise — proved on the three
algebra generators, where no Koszul sign can arise.
-/
import Superfusion.Super.PentagonCompAssoc

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

/-! ### The stabilization associator hexagon -/

section StabAssoc

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

/-- The braiding on `x ᵍ⊗ 1` is sign-free, for arbitrary `x` — via
the even/odd split (the passing slot holds `1`, of degree `0`). -/
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

/-- The braiding on `1 ᵍ⊗ y` is sign-free, for arbitrary `y`. -/
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

/-- `mSGR` on `x ᵍ⊗ 1`: the signed diagonal of `x`. -/
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

/-- `mSGR` on `1 ᵍ⊗ N`: entrywise `1 ᵍ⊗ ·`. -/
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

/-- **The stabilization associator hexagon**: pulling the matrix
layer out of the middle slot after reassociating agrees with pulling
it out of the left pair and reassociating entrywise.  Both sides are
algebra maps, so it suffices to compare them on the generators
`(a ᵍ⊗ 1) ᵍ⊗ 1`, `(1 ᵍ⊗ M) ᵍ⊗ 1` and `1 ᵍ⊗ d`, where no Koszul sign
can arise (every commutation passes a slot holding `1`). -/
private theorem matrixSuperGtensorRight_gassoc_apply
    {A S D : SuperAlgebra K} (p q : ℕ)
    (w : ((A.gtensor (S.matrixSuper p q)).gtensor D).carrier) :
    (matrixSuperGtensorRight A (S.gtensor D) p q).toAlgEquiv
        (((SuperAlgEquiv.refl A).gtensorCongr
          (matrixSuperGtensor S D p q)).toAlgEquiv
          ((gtensorAssoc A (S.matrixSuper p q) D).toAlgEquiv w))
      = ((gtensorAssoc A S D).matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv
          (((matrixSuperGtensorRight A S p q).gtensorCongr
            (SuperAlgEquiv.refl D)).toAlgEquiv w)) := by
  set F : ((A.gtensor (S.matrixSuper p q)).gtensor D).carrier →ₐ[K]
      ((A.gtensor (S.gtensor D)).matrixSuper p q).carrier :=
    ((matrixSuperGtensorRight A (S.gtensor D) p q).toAlgEquiv.toAlgHom).comp
      ((((SuperAlgEquiv.refl A).gtensorCongr
          (matrixSuperGtensor S D p q)).toAlgEquiv.toAlgHom).comp
        ((gtensorAssoc A (S.matrixSuper p q) D).toAlgEquiv.toAlgHom))
    with hF
  set G : ((A.gtensor (S.matrixSuper p q)).gtensor D).carrier →ₐ[K]
      ((A.gtensor (S.gtensor D)).matrixSuper p q).carrier :=
    (((gtensorAssoc A S D).matrixSuper p q).toAlgEquiv.toAlgHom).comp
      (((matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv.toAlgHom).comp
        (((matrixSuperGtensorRight A S p q).gtensorCongr
          (SuperAlgEquiv.refl D)).toAlgEquiv.toAlgHom))
    with hG
  -- the `a`-generator: both sides give the signed diagonal of `a`.
  have hC1 : ∀ a₀ : A.carrier,
      F (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = G (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier))) := by
    intro a₀
    have h1 : F (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = (matrixSuperGtensorRight A (S.gtensor D) p q).toAlgEquiv
          (toCA (a₀ ᵍ⊗ₜ[K]
            (1 : ((S.gtensor D).matrixSuper p q).carrier))) := by
      show (matrixSuperGtensorRight A (S.gtensor D) p q).toAlgEquiv
          (((SuperAlgEquiv.refl A).gtensorCongr
            (matrixSuperGtensor S D p q)).toAlgEquiv
            ((gtensorAssoc A (S.matrixSuper p q) D).toAlgEquiv
              (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))
                ᵍ⊗ₜ[K] (1 : D.carrier)))))
        = _
      rw [gtensorAssoc_tmulCA, gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl A).toAlgEquiv a₀ = a₀ from rfl,
        toCA_one_one, map_one]
    have h3 : G (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K]
                (1 : (S.gtensor D).carrier))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K]
                  (1 : (S.gtensor D).carrier))) := by
      show ((gtensorAssoc A S D).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv
            (((matrixSuperGtensorRight A S p q).gtensorCongr
              (SuperAlgEquiv.refl D)).toAlgEquiv
              (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))
                ᵍ⊗ₜ[K] (1 : D.carrier)))))
        = _
      rw [gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl D).toAlgEquiv (1 : D.carrier) = 1
          from rfl,
        matrixSuperGtensorRight_tmul_one p q a₀]
      set N₁ : ((A.gtensor S).matrixSuper p q).carrier :=
        Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
          toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K] (1 : S.carrier))
            + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
              toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
        with hN₁
      rw [show (matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv
            (toCA (N₁ ᵍ⊗ₜ[K] (1 : D.carrier)))
          = matrixInclLeft (A.gtensor S).grading D.grading N₁
            * matrixInclRight (sumParity p q) (A.gtensor S).grading
              D.grading (1 : D.carrier) from
        matrixTensorSuperHom_tmul (sumParity p q) (A.gtensor S).grading
          D.grading N₁ 1,
        map_one, mul_one]
      refine Matrix.ext fun r s => ?_
      show (gtensorAssoc A S D).toAlgEquiv
          (matrixInclLeft (A.gtensor S).grading D.grading N₁ r s)
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K]
                (1 : (S.gtensor D).carrier))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K]
                  (1 : (S.gtensor D).carrier))) r s
      rw [matrixInclLeft_apply, hN₁]
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        show (gtensorAssoc A S D).toAlgEquiv
            (toCA ((toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K] (1 : S.carrier))
              + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
                toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
              ᵍ⊗ₜ[K] (1 : D.carrier)))
          = toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K]
              (1 : (S.gtensor D).carrier))
            + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
              toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K]
                (1 : (S.gtensor D).carrier))
        rw [add_gtmulCA, zsmul_gtmulCA, map_add, map_zsmul,
          gtensorAssoc_tmulCA, gtensorAssoc_tmulCA, toCA_one_one]
      · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs]
        show (gtensorAssoc A S D).toAlgEquiv
            (toCA ((0 : (A.gtensor S).carrier) ᵍ⊗ₜ[K] (1 : D.carrier)))
          = 0
        rw [zero_gtmulCA]
        exact map_zero _
    exact (h1.trans (matrixSuperGtensorRight_tmul_one p q a₀)).trans
      h3.symm
  -- the `M`-generator: both sides give the entrywise pure tensors.
  have hC2 : ∀ M₀ : (S.matrixSuper p q).carrier,
      F (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀) ᵍ⊗ₜ[K] (1 : D.carrier)))
        = G (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀)
          ᵍ⊗ₜ[K] (1 : D.carrier))) := by
    intro M₀
    have h1 : F (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀)
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA (z ᵍ⊗ₜ[K] (1 : D.carrier)))) := by
      show (matrixSuperGtensorRight A (S.gtensor D) p q).toAlgEquiv
          (((SuperAlgEquiv.refl A).gtensorCongr
            (matrixSuperGtensor S D p q)).toAlgEquiv
            ((gtensorAssoc A (S.matrixSuper p q) D).toAlgEquiv
              (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀)
                ᵍ⊗ₜ[K] (1 : D.carrier)))))
        = _
      rw [gtensorAssoc_tmulCA, gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl A).toAlgEquiv (1 : A.carrier) = 1
          from rfl,
        show (matrixSuperGtensor S D p q).toAlgEquiv
            (toCA (M₀ ᵍ⊗ₜ[K] (1 : D.carrier)))
          = matrixInclLeft S.grading D.grading
              (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            * matrixInclRight (sumParity p q) S.grading D.grading
              (1 : D.carrier) from
          matrixTensorSuperHom_tmul (sumParity p q) S.grading D.grading
            M₀ 1,
        map_one, mul_one,
        matrixSuperGtensorRight_one_tmul (P := A) (Q := S.gtensor D) p q
          (matrixInclLeft S.grading D.grading
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier))]
      rw [show (matrixInclLeft S.grading D.grading
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier) :
            Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (S.gtensor D).carrier)
          = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA (z ᵍ⊗ₜ[K] (1 : D.carrier))) from rfl,
        Matrix.map_map]
      rfl
    have h3 : G (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀)
          ᵍ⊗ₜ[K] (1 : D.carrier)))
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA (z ᵍ⊗ₜ[K] (1 : D.carrier)))) := by
      show ((gtensorAssoc A S D).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv
            (((matrixSuperGtensorRight A S p q).gtensorCongr
              (SuperAlgEquiv.refl D)).toAlgEquiv
              (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀)
                ᵍ⊗ₜ[K] (1 : D.carrier)))))
        = _
      rw [gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl D).toAlgEquiv (1 : D.carrier) = 1
          from rfl,
        matrixSuperGtensorRight_one_tmul p q M₀]
      set N₂ : ((A.gtensor S).matrixSuper p q).carrier :=
        Matrix.map
          (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
          (fun z => toCA ((1 : A.carrier) ᵍ⊗ₜ[K] z)) with hN₂
      rw [show (matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv
            (toCA (N₂ ᵍ⊗ₜ[K] (1 : D.carrier)))
          = matrixInclLeft (A.gtensor S).grading D.grading N₂
            * matrixInclRight (sumParity p q) (A.gtensor S).grading
              D.grading (1 : D.carrier) from
        matrixTensorSuperHom_tmul (sumParity p q) (A.gtensor S).grading
          D.grading N₂ 1,
        map_one, mul_one]
      refine Matrix.ext fun r s => ?_
      show (gtensorAssoc A S D).toAlgEquiv
          (matrixInclLeft (A.gtensor S).grading D.grading N₂ r s)
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA (z ᵍ⊗ₜ[K] (1 : D.carrier)))) r s
      rw [matrixInclLeft_apply, hN₂, Matrix.map_apply, Matrix.map_apply]
      exact gtensorAssoc_tmulCA (1 : A.carrier)
        ((M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier) r s)
        (1 : D.carrier)
    exact h1.trans h3.symm
  -- the `d`-generator: both sides give the signed diagonal of `d`.
  have hR : ∀ dd : D.carrier,
      F (toCA ((1 : (A.gtensor (S.matrixSuper p q)).carrier) ᵍ⊗ₜ[K] dd))
        = G (toCA ((1 : (A.gtensor (S.matrixSuper p q)).carrier)
          ᵍ⊗ₜ[K] dd)) := by
    intro dd
    have h1 : F (toCA ((1 : (A.gtensor (S.matrixSuper p q)).carrier)
          ᵍ⊗ₜ[K] dd))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : S.carrier) ᵍ⊗ₜ[K] evenPart D.grading dd))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                  toCA ((1 : S.carrier) ᵍ⊗ₜ[K] oddPart D.grading dd))) := by
      show (matrixSuperGtensorRight A (S.gtensor D) p q).toAlgEquiv
          (((SuperAlgEquiv.refl A).gtensorCongr
            (matrixSuperGtensor S D p q)).toAlgEquiv
            ((gtensorAssoc A (S.matrixSuper p q) D).toAlgEquiv
              (toCA ((1 : (A.gtensor (S.matrixSuper p q)).carrier)
                ᵍ⊗ₜ[K] dd))))
        = _
      rw [show (1 : (A.gtensor (S.matrixSuper p q)).carrier)
          = toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
            (1 : (S.matrixSuper p q).carrier)) from toCA_one_one.symm,
        gtensorAssoc_tmulCA, gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl A).toAlgEquiv (1 : A.carrier) = 1
          from rfl,
        show (matrixSuperGtensor S D p q).toAlgEquiv
            (toCA ((1 : (S.matrixSuper p q).carrier) ᵍ⊗ₜ[K] dd))
          = matrixInclLeft S.grading D.grading
              (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            * matrixInclRight (sumParity p q) S.grading D.grading dd from
          matrixTensorSuperHom_tmul (sumParity p q) S.grading D.grading
            1 dd,
        map_one, one_mul, matrixInclRight_apply,
        matrixSuperGtensorRight_one_tmul (P := A) (Q := S.gtensor D) p q
          (sdiag (sumParity p q) S.grading D.grading dd)]
      refine Matrix.ext fun r s => ?_
      rw [Matrix.map_apply,
        show sdiag (sumParity p q) S.grading D.grading dd
          = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              ((1 : S.carrier) ᵍ⊗ₜ[K] evenPart D.grading dd
                : S.grading ᵍ⊗[K] D.grading)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  ((1 : S.carrier) ᵍ⊗ₜ[K] oddPart D.grading dd))
          from rfl]
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        show toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
            (toCA ((1 : S.carrier) ᵍ⊗ₜ[K] evenPart D.grading dd)
              + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
                toCA ((1 : S.carrier) ᵍ⊗ₜ[K] oddPart D.grading dd)))
          = toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA ((1 : S.carrier) ᵍ⊗ₜ[K] evenPart D.grading dd))
            + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
              toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : S.carrier) ᵍ⊗ₜ[K] oddPart D.grading dd))
        rw [gtmulCA_add, gtmulCA_zsmul]
      · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs]
        exact gtmulCA_zero (1 : A.carrier)
    have h3 : G (toCA ((1 : (A.gtensor (S.matrixSuper p q)).carrier)
          ᵍ⊗ₜ[K] dd))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : S.carrier) ᵍ⊗ₜ[K] evenPart D.grading dd))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                  toCA ((1 : S.carrier) ᵍ⊗ₜ[K] oddPart D.grading dd))) := by
      show ((gtensorAssoc A S D).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv
            (((matrixSuperGtensorRight A S p q).gtensorCongr
              (SuperAlgEquiv.refl D)).toAlgEquiv
              (toCA ((1 : (A.gtensor (S.matrixSuper p q)).carrier)
                ᵍ⊗ₜ[K] dd))))
        = _
      rw [gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl D).toAlgEquiv dd = dd from rfl,
        map_one,
        show (matrixSuperGtensor (A.gtensor S) D p q).toAlgEquiv
            (toCA ((1 : ((A.gtensor S).matrixSuper p q).carrier)
              ᵍ⊗ₜ[K] dd))
          = matrixInclLeft (A.gtensor S).grading D.grading
              (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
                (A.gtensor S).carrier)
            * matrixInclRight (sumParity p q) (A.gtensor S).grading
              D.grading dd from
          matrixTensorSuperHom_tmul (sumParity p q)
            (A.gtensor S).grading D.grading 1 dd,
        map_one, one_mul, matrixInclRight_apply]
      refine Matrix.ext fun r s => ?_
      show (gtensorAssoc A S D).toAlgEquiv
          (sdiag (sumParity p q) (A.gtensor S).grading D.grading dd r s)
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : S.carrier) ᵍ⊗ₜ[K] evenPart D.grading dd))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                  toCA ((1 : S.carrier) ᵍ⊗ₜ[K] oddPart D.grading dd))) r s
      rw [show sdiag (sumParity p q) (A.gtensor S).grading D.grading dd
          = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
              ((1 : (A.gtensor S).carrier) ᵍ⊗ₜ[K] evenPart D.grading dd
                : (A.gtensor S).grading ᵍ⊗[K] D.grading)
                + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                  ((1 : (A.gtensor S).carrier) ᵍ⊗ₜ[K]
                    oddPart D.grading dd)) from rfl]
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        show (gtensorAssoc A S D).toAlgEquiv
            (toCA ((1 : (A.gtensor S).carrier) ᵍ⊗ₜ[K]
                evenPart D.grading dd)
              + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
                toCA ((1 : (A.gtensor S).carrier) ᵍ⊗ₜ[K]
                  oddPart D.grading dd))
          = toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA ((1 : S.carrier) ᵍ⊗ₜ[K] evenPart D.grading dd))
            + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
              toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((1 : S.carrier) ᵍ⊗ₜ[K] oddPart D.grading dd))
        rw [map_add, map_zsmul,
          show (1 : (A.gtensor S).carrier)
            = toCA ((1 : A.carrier) ᵍ⊗ₜ[K] (1 : S.carrier)) from
            toCA_one_one.symm,
          gtensorAssoc_tmulCA, gtensorAssoc_tmulCA]
      · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs]
        exact map_zero _
    exact h1.trans h3.symm
  -- assemble: agree on both inclusions, hence everywhere.
  have hLhom : F.comp (includeLeft
        (A.gtensor (S.matrixSuper p q)).grading D.grading)
      = G.comp (includeLeft
        (A.gtensor (S.matrixSuper p q)).grading D.grading) := by
    refine galgHom_ext A.grading (S.matrixSuper p q).grading ?_
    intro a₀ M₀
    show F (includeLeft (A.gtensor (S.matrixSuper p q)).grading D.grading
        (toCA (a₀ ᵍ⊗ₜ[K] M₀)))
      = G (includeLeft (A.gtensor (S.matrixSuper p q)).grading D.grading
        (toCA (a₀ ᵍ⊗ₜ[K] M₀)))
    have e1 : F (includeLeft (A.gtensor (S.matrixSuper p q)).grading
          D.grading (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))))
        = G (includeLeft (A.gtensor (S.matrixSuper p q)).grading
          D.grading
          (toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))) :=
      hC1 a₀
    have e2 : F (includeLeft (A.gtensor (S.matrixSuper p q)).grading
          D.grading (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀)))
        = G (includeLeft (A.gtensor (S.matrixSuper p q)).grading
          D.grading (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀))) :=
      hC2 M₀
    rw [show toCA (a₀ ᵍ⊗ₜ[K] M₀)
        = toCA (a₀ ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))
          * toCA ((1 : A.carrier) ᵍ⊗ₜ[K] M₀) from
      (includeLeft_mul_includeRight A.grading
        (S.matrixSuper p q).grading a₀ M₀).symm,
      map_mul]
    exact (map_mul F _ _).trans
      (by rw [e1, e2]; exact (map_mul G _ _).symm)
  have hRhom : F.comp (includeRight
        (A.gtensor (S.matrixSuper p q)).grading D.grading)
      = G.comp (includeRight
        (A.gtensor (S.matrixSuper p q)).grading D.grading) :=
    AlgHom.ext fun dd => hR dd
  have hhom : F = G :=
    GradedTensorProduct.algHom_ext
      (𝒜 := (A.gtensor (S.matrixSuper p q)).grading)
      (ℬ := D.grading) hLhom hRhom
  exact AlgHom.congr_fun hhom w

end StabAssoc

section Factor

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The common cluster-fusion prefix of the routes through `(bc)`. -/
noncomputable def clusterPrefix (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      (((stdTower a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d)) :=
  ((gtensorAssoc (stdTower a) (stdTower b)
      (stdTower c)).gtensorCongr (SuperAlgEquiv.refl (stdTower d))).trans
    (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
      (stdFuse b c)).gtensorCongr (SuperAlgEquiv.refl (stdTower d)))

/-- The matrix-frame change: pull the `f`-matrix layer out of the
middle. -/
noncomputable def clusterFrame (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d))
      ((((stdTower a).gtensor (stdTower (b + c))).gtensor
        (stdTower d)).matrixSuper (fuseSize b c).1 (fuseSize b c).2) :=
  ((matrixSuperGtensorRight (stdTower a) (stdTower (b + c))
      (fuseSize b c).1 (fuseSize b c).2).gtensorCongr
    (SuperAlgEquiv.refl (stdTower d))).trans
    (matrixSuperGtensor ((stdTower a).gtensor (stdTower (b + c)))
      (stdTower d) (fuseSize b c).1 (fuseSize b c).2)

/-- Composed sizes of the factored tails agree with the pentagon
target sizes: the `(fτ)·κ` grouping of the collapsed layers is
`extSize` of the right route's composite size, which the route size
identity and reassociation carry to the pentagon target. -/
private theorem clusterSize_eq₂ (a b c d : ZMod 8) :
    extSize (sizeR a b c) (a + (b + c)) d
      = extSize (sizeL a b c) (a + b + c) d := by
  rw [sizeL_eq_sizeR, ← add_assoc]

/-- Index identity for the factored tails. -/
private theorem clusterIndex_eq (a b c d : ZMod 8) :
    a + (b + c) + d = a + b + c + d := by ring

/-- The factored tail through the left-associated cluster triple:
frame change, stabilized left route, collapse, then the
collapse-reassociation bridge and the index/size cast. -/
noncomputable def clusterTail2 (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (clusterFrame a b c d).trans
    (((routeL a (b + c) d).matrixSuper (fuseSize b c).1
        (fuseSize b c).2).trans
      ((matrixSuperComp (stdTower (a + (b + c) + d))
          (fuseSize b c).1 (fuseSize b c).2
          (sizeL a (b + c) d).1 (sizeL a (b + c) d).2).trans
        (((matrixSuperCompAssoc (stdTower (a + (b + c) + d))
            (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2
            (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
            (fuseSize b c).1 (fuseSize b c).2).symm).trans
          (stdMatrixCast (clusterIndex_eq a b c d)
            (clusterSize_eq₂ a b c d)))))

/-- Index identity for the right-tail cast. -/
private theorem clusterIndex_eq₄ (a b c d : ZMod 8) :
    a + (b + c + d) = a + (b + c) + d :=
  (add_assoc a (b + c) d).symm

/-- Size identity for the right-tail cast. -/
private theorem clusterSize_eq₄ (a b c d : ZMod 8) :
    ((fuseSize b c).1 * (sizeR a (b + c) d).1
        + (fuseSize b c).2 * (sizeR a (b + c) d).2,
      (fuseSize b c).1 * (sizeR a (b + c) d).2
        + (fuseSize b c).2 * (sizeR a (b + c) d).1)
      = ((fuseSize b c).1 * (sizeL a (b + c) d).1
        + (fuseSize b c).2 * (sizeL a (b + c) d).2,
      (fuseSize b c).1 * (sizeL a (b + c) d).2
        + (fuseSize b c).2 * (sizeL a (b + c) d).1) := by
  rw [sizeL_eq_sizeR]

/-- The factored tail through the right-associated cluster triple:
frame change, stabilized right route, collapse, then the
collapse-reassociation bridge (transported back to the
`a + (b+c+d)`-frame, where the right route's own layers live) and the
final pentagon cast. -/
noncomputable def clusterTail4 (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (clusterFrame a b c d).trans
    (((routeR a (b + c) d).matrixSuper (fuseSize b c).1
        (fuseSize b c).2).trans
      ((matrixSuperComp (stdTower (a + (b + c) + d))
          (fuseSize b c).1 (fuseSize b c).2
          (sizeL a (b + c) d).1 (sizeL a (b + c) d).2).trans
        (((stdMatrixCast (clusterIndex_eq₄ a b c d)
            (clusterSize_eq₄ a b c d)).symm).trans
          (((matrixSuperCompAssoc (stdTower (a + (b + c + d)))
              (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2
              (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
              (fuseSize b c).1 (fuseSize b c).2).symm).trans
            (stdMatrixCast
              (show a + (b + c + d) = a + b + c + d by ring)
              (quadSize_eq a b c d).symm)))))

/-! ### Local helper kit: `gtensorCongr` unfolding and cast slides -/

private def toCF {P Q : SuperAlgebra K} (x : P.grading ᵍ⊗[K] Q.grading) :
    (P.gtensor Q).carrier := x

omit [Invertible (2 : K)] in
private theorem gtensorCongr_tmulF {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (a : P.carrier) (b : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv (toCF (a ᵍ⊗ₜ[K] b))
      = toCF (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading e.toAlgEquiv
    f.toAlgEquiv e.map_grading f.map_grading a b

omit [Invertible (2 : K)] in
/-- `refl ᵍ⊗c refl` acts as the identity, applied form: needed to
peel `gtensorCongr_trans_apply` one step at a time along a chain
`(X.trans Y).gtensorCongr refl`. -/
private theorem gtensorCongr_refl_refl_apply {P Q : SuperAlgebra K}
    (w : (P.gtensor Q).carrier) :
    ((SuperAlgEquiv.refl P).gtensorCongr (SuperAlgEquiv.refl Q)).toAlgEquiv w
      = w := by
  have hhom : (((SuperAlgEquiv.refl P).gtensorCongr
        (SuperAlgEquiv.refl Q)).toAlgEquiv.toAlgHom)
      = AlgHom.id K _ := by
    refine galgHom_ext P.grading Q.grading ?_
    intro a b
    change ((SuperAlgEquiv.refl P).gtensorCongr
        (SuperAlgEquiv.refl Q)).toAlgEquiv (toCF (a ᵍ⊗ₜ[K] b))
      = toCF (a ᵍ⊗ₜ[K] b)
    rw [gtensorCongr_tmulF]
    rfl
  exact AlgHom.congr_fun hhom w

omit [Invertible (2 : K)] in
/-- One step of `gtensorCongr_trans_apply`, specialized to `refl` on
the fixed second factor: peels the outermost `.trans` of a chain
tensored (via `⊗c`) with `refl`. -/
private theorem gtensorCongr_trans_refl_apply {P P' P'' D : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (e' : SuperAlgEquiv P' P'')
    (w : (P.gtensor D).carrier) :
    ((e.trans e').gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv w
      = (e'.gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv
        ((e.gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv w) :=
  gtensorCongr_trans_apply e e' (SuperAlgEquiv.refl D) (SuperAlgEquiv.refl D) w

omit [Invertible (2 : K)] in
/-- One step of `gtensorCongr_trans_apply`, specialized to `refl` on
the fixed first factor: peels the outermost `.trans` of a chain
tensored (via `⊗c`) with `refl` on the left. -/
private theorem gtensorCongr_refl_trans_apply {D Q Q' Q'' : SuperAlgebra K}
    (f : SuperAlgEquiv Q Q') (f' : SuperAlgEquiv Q' Q'')
    (w : (D.gtensor Q).carrier) :
    ((SuperAlgEquiv.refl D).gtensorCongr (f.trans f')).toAlgEquiv w
      = ((SuperAlgEquiv.refl D).gtensorCongr f').toAlgEquiv
        (((SuperAlgEquiv.refl D).gtensorCongr f).toAlgEquiv w) :=
  gtensorCongr_trans_apply (SuperAlgEquiv.refl D) (SuperAlgEquiv.refl D) f f' w

/-- A `stdMatrixCast` slides past `extTail`, applied form: proved
generically (for arbitrary index/size equalities) by `subst`,
reducing both sides to the identity via
`gtensorCongr_refl_refl_apply`. -/
private theorem stdMatrixCast_extTail_apply {x y : ZMod 8} (h : x = y)
    {s t : ℕ × ℕ} (hs : s = t) (d : ZMod 8)
    (v : (((stdTower (K := K) x).matrixSuper s.1 s.2).gtensor
      (stdTower d)).carrier) :
    (extTail y t d).toAlgEquiv
        (((stdMatrixCast h hs).gtensorCongr
          (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv v)
      = (stdMatrixCast (show x + d = y + d by rw [h])
          (show extSize s x d = extSize t y d by rw [h, hs])).toAlgEquiv
        ((extTail x s d).toAlgEquiv v) := by
  subst h
  subst hs
  show (extTail x s d).toAlgEquiv
      (((SuperAlgEquiv.refl _).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv v)
    = (extTail x s d).toAlgEquiv v
  rw [gtensorCongr_refl_refl_apply]

omit [Invertible (2 : K)] in
/-- A `stdMatrixCast` slides past `matrixSuperComp` (with the cast on
the inner layer), applied form: proved generically by `subst`. -/
private theorem stdMatrixCast_matrixSuperComp_apply {x y : ZMod 8}
    (h : x = y) {s t : ℕ × ℕ} (hs : s = t) (p q : ℕ)
    (M : (((stdTower (K := K) x).matrixSuper s.1 s.2).matrixSuper
      p q).carrier) :
    (matrixSuperComp (stdTower y) p q t.1 t.2).toAlgEquiv
        (((stdMatrixCast h hs).matrixSuper p q).toAlgEquiv M)
      = (stdMatrixCast h
          (show (p * s.1 + q * s.2, p * s.2 + q * s.1)
              = (p * t.1 + q * t.2, p * t.2 + q * t.1) by
            rw [hs])).toAlgEquiv
        ((matrixSuperComp (stdTower x) p q s.1 s.2).toAlgEquiv M) := by
  subst h
  subst hs
  rfl

/-- **Factorization of vertex 2** through the cluster prefix. -/
theorem quadRoute2_factor (a b c d : ZMod 8)
    (w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).carrier) :
    (quadRoute2 a b c d).toAlgEquiv w
      = (clusterTail2 a b c d).toAlgEquiv
        ((clusterPrefix a b c d).toAlgEquiv w) := by
  show (extTail (a + b + c) (sizeL a b c) d).toAlgEquiv
      (((routeR a b c).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w)
    = (clusterTail2 a b c d).toAlgEquiv
      ((clusterPrefix a b c d).toAlgEquiv w)
  show (extTail (a + b + c) (sizeL a b c) d).toAlgEquiv
      ((((gtensorAssoc (stdTower a) (stdTower b) (stdTower c)).trans
          (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (stdFuse b c)).trans
            ((matrixSuperGtensorRight (stdTower a) (stdTower (b + c))
                (fuseSize b c).1 (fuseSize b c).2).trans
              (((stdFuse a (b + c)).matrixSuper (fuseSize b c).1
                  (fuseSize b c).2).trans
                ((matrixSuperComp (stdTower (a + (b + c)))
                    (fuseSize b c).1 (fuseSize b c).2
                    (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).trans
                  (stdMatrixCast (add_assoc a b c).symm
                    (sizeL_eq_sizeR a b c).symm)))))).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w)
    = (clusterTail2 a b c d).toAlgEquiv
      ((clusterPrefix a b c d).toAlgEquiv w)
  rw [gtensorCongr_trans_refl_apply, gtensorCongr_trans_refl_apply,
    gtensorCongr_trans_refl_apply, gtensorCongr_trans_refl_apply,
    gtensorCongr_trans_refl_apply]
  have hPre : (clusterPrefix a b c d).toAlgEquiv w
      = (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (stdFuse b c)).gtensorCongr
            (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv
          (((gtensorAssoc (stdTower a) (stdTower b)
                (stdTower c)).gtensorCongr
              (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w) := rfl
  rw [hPre]
  have hFrame : ∀ v : (((stdTower (K := K) a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d)).carrier,
      (clusterFrame a b c d).toAlgEquiv v
      = (matrixSuperGtensor ((stdTower a).gtensor (stdTower (b + c)))
            (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
          (((matrixSuperGtensorRight (stdTower a) (stdTower (b + c))
                (fuseSize b c).1 (fuseSize b c).2).gtensorCongr
              (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv v) := fun v => rfl
  have hTail2 : ∀ v : (((stdTower (K := K) a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d)).carrier,
      (clusterTail2 a b c d).toAlgEquiv v
      = (stdMatrixCast (clusterIndex_eq a b c d)
            (clusterSize_eq₂ a b c d)).toAlgEquiv
          ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + c) + d))
              (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2
              (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
              (fuseSize b c).1 (fuseSize b c).2).symm.toAlgEquiv
            ((matrixSuperComp (stdTower (a + (b + c) + d)) (fuseSize b c).1
                (fuseSize b c).2 (sizeL a (b + c) d).1
                (sizeL a (b + c) d).2).toAlgEquiv
              (((routeL a (b + c) d).matrixSuper (fuseSize b c).1
                    (fuseSize b c).2).toAlgEquiv
                ((clusterFrame a b c d).toAlgEquiv v)))) := fun v => rfl
  rw [hTail2, hFrame]
  set w' : (((stdTower (K := K) a).gtensor
      ((stdTower (b + c)).matrixSuper (fuseSize b c).1
        (fuseSize b c).2)).gtensor (stdTower d)).carrier :=
    (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            (stdFuse b c)).gtensorCongr
          (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv
      (((gtensorAssoc (stdTower a) (stdTower b)
            (stdTower c)).gtensorCongr
          (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w) with hw'
  set u : ((((stdTower (K := K) a).gtensor (stdTower (b + c))).matrixSuper
      (fuseSize b c).1 (fuseSize b c).2).gtensor (stdTower d)).carrier :=
    ((matrixSuperGtensorRight (stdTower a) (stdTower (b + c))
          (fuseSize b c).1 (fuseSize b c).2).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w' with hu
  -- step A: naturality of `mSG` moving the matrix-slot congruence
  -- `stdFuse a s` past it (with `refl_d` fixed on the other slot)
  have hA := matrixSuperGtensor_full_natural_apply (stdFuse a (b + c))
    (SuperAlgEquiv.refl (stdTower d)) (fuseSize b c).1 (fuseSize b c).2 u
  set L2L3L4 : SuperAlgEquiv
      (((stdTower (K := K) (a + (b + c))).matrixSuper
          (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).gtensor
        (stdTower d))
      ((stdTower (K := K) (a + (b + c) + d)).matrixSuper
        (sizeL a (b + c) d).1 (sizeL a (b + c) d).2) :=
    (matrixSuperGtensor (stdTower (K := K) (a + (b + c))) (stdTower d)
        (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).trans
      (((stdFuse (a + (b + c)) d).matrixSuper (fuseSize a (b + c)).1
          (fuseSize a (b + c)).2).trans
        (matrixSuperComp (stdTower (a + (b + c) + d))
          (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
          (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2))
    with hL2L3L4
  have hroute : routeL a (b + c) d
      = ((stdFuse a (b + c)).gtensorCongr
          (SuperAlgEquiv.refl (stdTower d))).trans L2L3L4 := rfl
  have hAstep : (((routeL a (b + c) d).matrixSuper (fuseSize b c).1
        (fuseSize b c).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower a).gtensor (stdTower (b + c)))
            (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u))
      = (L2L3L4.matrixSuper (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
          ((((stdFuse a (b + c)).gtensorCongr
                (SuperAlgEquiv.refl (stdTower d))).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((matrixSuperGtensor ((stdTower a).gtensor (stdTower (b + c)))
                (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u)) := by
    rw [hroute]
    rfl
  rw [hAstep]
  conv_rhs => rw [← hA]
  set u2 : ((((stdTower (K := K) (a + (b + c))).matrixSuper
        (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).matrixSuper
        (fuseSize b c).1 (fuseSize b c).2).gtensor (stdTower d)).carrier :=
    (((stdFuse a (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv u with hu2
  have hB := matrixSuperComp_gtensor_apply (X := stdTower (K := K) (a + (b + c)))
    (D := stdTower d) (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
    (fuseSize b c).1 (fuseSize b c).2 u2
  have hB2 := (matrixSuperComp ((stdTower (K := K) (a + (b + c))).gtensor (stdTower d))
        (fuseSize b c).1 (fuseSize b c).2 (fuseSize a (b + c)).1
        (fuseSize a (b + c)).2).toAlgEquiv.symm_apply_eq.mpr hB
  have hCC := congrArg
    ((((stdFuse (a + (b + c)) d).matrixSuper (fuseSize a (b + c)).1
          (fuseSize a (b + c)).2).matrixSuper (fuseSize b c).1
        (fuseSize b c).2).toAlgEquiv)
    hB2
  have hD := congrArg
    ((matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
        (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
        (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2).matrixSuper
        (fuseSize b c).1 (fuseSize b c).2 |>.toAlgEquiv)
    hCC
  have hCstep : (L2L3L4.matrixSuper (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower (K := K) (a + (b + c))).matrixSuper
              (fuseSize a (b + c)).1 (fuseSize a (b + c)).2)
            (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u2)
      = ((matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
              (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
              (fuseSize (a + (b + c)) d).1
              (fuseSize (a + (b + c)) d).2).matrixSuper (fuseSize b c).1
            (fuseSize b c).2).toAlgEquiv
          ((((stdFuse (a + (b + c)) d).matrixSuper (fuseSize a (b + c)).1
                  (fuseSize a (b + c)).2).matrixSuper (fuseSize b c).1
                (fuseSize b c).2).toAlgEquiv
            ((matrixSuperComp ((stdTower (K := K) (a + (b + c))).gtensor
                    (stdTower d)) (fuseSize b c).1 (fuseSize b c).2
                  (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).toAlgEquiv.symm
              ((matrixSuperGtensor (stdTower (K := K) (a + (b + c))) (stdTower d)
                    ((fuseSize b c).1 * (fuseSize a (b + c)).1
                      + (fuseSize b c).2 * (fuseSize a (b + c)).2)
                    ((fuseSize b c).1 * (fuseSize a (b + c)).2
                      + (fuseSize b c).2 * (fuseSize a (b + c)).1)).toAlgEquiv
                (((matrixSuperComp (stdTower (K := K) (a + (b + c)))
                      (fuseSize b c).1 (fuseSize b c).2 (fuseSize a (b + c)).1
                      (fuseSize a (b + c)).2).gtensorCongr
                    (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv u2)))) := by
    show (L2L3L4.matrixSuper (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower (K := K) (a + (b + c))).matrixSuper
              (fuseSize a (b + c)).1 (fuseSize a (b + c)).2)
            (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u2)
      = _
    rw [hL2L3L4]
    exact hD.symm
  rw [hCstep]
  have hE := matrixSuperComp_natural_apply (stdFuse (a + (b + c)) d)
    (fuseSize a (b + c)).1 (fuseSize a (b + c)).2 (fuseSize b c).1 (fuseSize b c).2
    (((matrixSuperGtensor (stdTower (K := K) (a + (b + c))) (stdTower d)
          (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).matrixSuper
        (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
      ((matrixSuperGtensor ((stdTower (K := K) (a + (b + c))).matrixSuper
            (fuseSize a (b + c)).1 (fuseSize a (b + c)).2)
          (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u2))
  have hR6a := stdMatrixCast_extTail_apply (add_assoc a b c).symm
    (sizeL_eq_sizeR a b c).symm d
    (((matrixSuperComp (stdTower (K := K) (a + (b + c))) (fuseSize b c).1
          (fuseSize b c).2 (fuseSize a (b + c)).1
          (fuseSize a (b + c)).2).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv u2)
  have hR6b0 : (extTail (a + (b + c)) (sizeR a b c) d).toAlgEquiv
      (((matrixSuperComp (stdTower (K := K) (a + (b + c))) (fuseSize b c).1
            (fuseSize b c).2 (fuseSize a (b + c)).1
            (fuseSize a (b + c)).2).gtensorCongr
          (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv u2)
      = (matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
            ((fuseSize b c).1 * (fuseSize a (b + c)).1
              + (fuseSize b c).2 * (fuseSize a (b + c)).2)
            ((fuseSize b c).1 * (fuseSize a (b + c)).2
              + (fuseSize b c).2 * (fuseSize a (b + c)).1)
            (fuseSize (a + (b + c)) d).1
            (fuseSize (a + (b + c)) d).2).toAlgEquiv
        (((stdFuse (a + (b + c)) d).matrixSuper
              ((fuseSize b c).1 * (fuseSize a (b + c)).1
                + (fuseSize b c).2 * (fuseSize a (b + c)).2)
              ((fuseSize b c).1 * (fuseSize a (b + c)).2
                + (fuseSize b c).2 * (fuseSize a (b + c)).1)).toAlgEquiv
          ((matrixSuperComp ((stdTower (K := K) (a + (b + c))).gtensor (stdTower d))
                (fuseSize b c).1 (fuseSize b c).2 (fuseSize a (b + c)).1
                (fuseSize a (b + c)).2).toAlgEquiv
            (((matrixSuperGtensor (stdTower (K := K) (a + (b + c))) (stdTower d)
                  (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).matrixSuper
                (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
              ((matrixSuperGtensor ((stdTower (K := K) (a + (b + c))).matrixSuper
                    (fuseSize a (b + c)).1 (fuseSize a (b + c)).2)
                  (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u2)))) := by
    show (extTail (a + (b + c)) (sizeR a b c) d).toAlgEquiv
        (((matrixSuperComp (stdTower (K := K) (a + (b + c))) (fuseSize b c).1
              (fuseSize b c).2 (fuseSize a (b + c)).1
              (fuseSize a (b + c)).2).gtensorCongr
            (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv u2)
      = (matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
            ((fuseSize b c).1 * (fuseSize a (b + c)).1
              + (fuseSize b c).2 * (fuseSize a (b + c)).2)
            ((fuseSize b c).1 * (fuseSize a (b + c)).2
              + (fuseSize b c).2 * (fuseSize a (b + c)).1)
            (fuseSize (a + (b + c)) d).1
            (fuseSize (a + (b + c)) d).2).toAlgEquiv
        (((stdFuse (a + (b + c)) d).matrixSuper
              ((fuseSize b c).1 * (fuseSize a (b + c)).1
                + (fuseSize b c).2 * (fuseSize a (b + c)).2)
              ((fuseSize b c).1 * (fuseSize a (b + c)).2
                + (fuseSize b c).2 * (fuseSize a (b + c)).1)).toAlgEquiv
          ((matrixSuperComp ((stdTower (K := K) (a + (b + c))).gtensor (stdTower d))
                (fuseSize b c).1 (fuseSize b c).2 (fuseSize a (b + c)).1
                (fuseSize a (b + c)).2).toAlgEquiv
            (((matrixSuperGtensor (stdTower (K := K) (a + (b + c))) (stdTower d)
                  (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).matrixSuper
                (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
              ((matrixSuperGtensor ((stdTower (K := K) (a + (b + c))).matrixSuper
                    (fuseSize a (b + c)).1 (fuseSize a (b + c)).2)
                  (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u2))))
    unfold sizeR extTail
    dsimp only
    exact congrArg
      ((((stdFuse (a + (b + c)) d).matrixSuper
            ((fuseSize b c).1 * (fuseSize a (b + c)).1
              + (fuseSize b c).2 * (fuseSize a (b + c)).2)
            ((fuseSize b c).1 * (fuseSize a (b + c)).2
              + (fuseSize b c).2 * (fuseSize a (b + c)).1)).trans
          (matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
            ((fuseSize b c).1 * (fuseSize a (b + c)).1
              + (fuseSize b c).2 * (fuseSize a (b + c)).2)
            ((fuseSize b c).1 * (fuseSize a (b + c)).2
              + (fuseSize b c).2 * (fuseSize a (b + c)).1)
            (fuseSize (a + (b + c)) d).1
            (fuseSize (a + (b + c)) d).2)).toAlgEquiv)
      hB
  refine hR6a.trans ?_
  rw [hR6b0, hB2]
  set W : (((stdTower (K := K) (a + (b + c) + d)).matrixSuper
      (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2).matrixSuper
      (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).matrixSuper
      (fuseSize b c).1 (fuseSize b c).2 |>.carrier :=
    (((stdFuse (a + (b + c)) d).matrixSuper (fuseSize a (b + c)).1
          (fuseSize a (b + c)).2).matrixSuper (fuseSize b c).1
        (fuseSize b c).2).toAlgEquiv
      (((matrixSuperGtensor (stdTower (K := K) (a + (b + c))) (stdTower d)
            (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).matrixSuper
          (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower (K := K) (a + (b + c))).matrixSuper
              (fuseSize a (b + c)).1 (fuseSize a (b + c)).2)
            (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv u2))
  have hAssoc :
      (matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
          (fuseSize b c).1 (fuseSize b c).2
          (sizeL a (b + c) d).1 (sizeL a (b + c) d).2).toAlgEquiv
        (((matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
              (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
              (fuseSize (a + (b + c)) d).1
              (fuseSize (a + (b + c)) d).2).matrixSuper
            (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv W)
      = (matrixSuperCompAssoc (stdTower (K := K) (a + (b + c) + d))
          (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2
          (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
          (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
        ((matrixSuperComp (stdTower (K := K) (a + (b + c) + d))
            ((fuseSize b c).1 * (fuseSize a (b + c)).1
              + (fuseSize b c).2 * (fuseSize a (b + c)).2)
            ((fuseSize b c).1 * (fuseSize a (b + c)).2
              + (fuseSize b c).2 * (fuseSize a (b + c)).1)
            (fuseSize (a + (b + c)) d).1
            (fuseSize (a + (b + c)) d).2).toAlgEquiv
          ((matrixSuperComp ((stdTower (K := K) (a + (b + c) + d)).matrixSuper
                (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2)
              (fuseSize b c).1 (fuseSize b c).2
              (fuseSize a (b + c)).1 (fuseSize a (b + c)).2).toAlgEquiv W)) :=
    matrixSuperComp_assoc_apply (fuseSize (a + (b + c)) d).1
      (fuseSize (a + (b + c)) d).2 (fuseSize a (b + c)).1
      (fuseSize a (b + c)).2 (fuseSize b c).1 (fuseSize b c).2 W
  rw [hAssoc]
  have hcanc : ∀ X, ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + c) + d))
        (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2
        (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
        (fuseSize b c).1 (fuseSize b c).2).symm).toAlgEquiv
      ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + c) + d))
        (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2
        (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
        (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv X) = X := fun X =>
    AlgEquiv.symm_apply_apply _ X
  rw [hcanc, hE, ← hB]

/-- **Factorization of vertex 4** through the cluster prefix. -/
theorem alignedRoute4_factor (a b c d : ZMod 8)
    (w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).carrier) :
    (alignedRoute4 a b c d).toAlgEquiv w
      = (clusterTail4 a b c d).toAlgEquiv
        ((clusterPrefix a b c d).toAlgEquiv w) := by
  show (stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
      (quadSize_eq a b c d).symm).toAlgEquiv
      ((matrixSuperComp (stdTower (a + (b + c + d))) (sizeL b c d).1
          (sizeL b c d).2 (fuseSize a (b + c + d)).1
          (fuseSize a (b + c + d)).2).toAlgEquiv
        (((stdFuse a (b + c + d)).matrixSuper (sizeL b c d).1
            (sizeL b c d).2).toAlgEquiv
          ((matrixSuperGtensorRight (stdTower a) (stdTower (b + c + d))
              (sizeL b c d).1 (sizeL b c d).2).toAlgEquiv
            (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                (((stdFuse b c).gtensorCongr
                    (SuperAlgEquiv.refl (stdTower d))).trans
                  ((matrixSuperGtensor (stdTower (b + c)) (stdTower d)
                      (fuseSize b c).1 (fuseSize b c).2).trans
                    (((stdFuse (b + c) d).matrixSuper (fuseSize b c).1
                        (fuseSize b c).2).trans
                      (matrixSuperComp (stdTower (b + c + d))
                        (fuseSize b c).1 (fuseSize b c).2
                        (fuseSize (b + c) d).1
                        (fuseSize (b + c) d).2))))).toAlgEquiv
              ((gtensorAssoc (stdTower a)
                  ((stdTower b).gtensor (stdTower c))
                  (stdTower d)).toAlgEquiv
                (((gtensorAssoc (stdTower a) (stdTower b)
                      (stdTower c)).gtensorCongr
                    (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w))))))
    = (clusterTail4 a b c d).toAlgEquiv
      ((clusterPrefix a b c d).toAlgEquiv w)
  rw [gtensorCongr_refl_trans_apply, gtensorCongr_refl_trans_apply,
    gtensorCongr_refl_trans_apply]
  have hSwap := gassoc_natural_apply (SuperAlgEquiv.refl (stdTower a))
    (stdFuse b c) (SuperAlgEquiv.refl (stdTower d))
    (((gtensorAssoc (stdTower a) (stdTower b)
        (stdTower c)).gtensorCongr
      (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w)
  rw [← hSwap]
  have hPre : (clusterPrefix a b c d).toAlgEquiv w
      = (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (stdFuse b c)).gtensorCongr
            (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv
          (((gtensorAssoc (stdTower a) (stdTower b)
                (stdTower c)).gtensorCongr
              (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w) := rfl
  rw [← hPre]
  have hFrame : ∀ v : (((stdTower (K := K) a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d)).carrier,
      (clusterFrame a b c d).toAlgEquiv v
      = (matrixSuperGtensor ((stdTower a).gtensor (stdTower (b + c)))
            (stdTower d) (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
          (((matrixSuperGtensorRight (stdTower a) (stdTower (b + c))
                (fuseSize b c).1 (fuseSize b c).2).gtensorCongr
              (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv v) := fun v => rfl
  have hTail4 : ∀ v : (((stdTower (K := K) a).gtensor
        ((stdTower (b + c)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2)).gtensor (stdTower d)).carrier,
      (clusterTail4 a b c d).toAlgEquiv v
      = (stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
            (quadSize_eq a b c d).symm).toAlgEquiv
          ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + c + d)))
              (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2
              (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
              (fuseSize b c).1 (fuseSize b c).2).symm.toAlgEquiv
            (((stdMatrixCast (clusterIndex_eq₄ a b c d)
                (clusterSize_eq₄ a b c d)).symm).toAlgEquiv
              ((matrixSuperComp (stdTower (a + (b + c) + d))
                  (fuseSize b c).1 (fuseSize b c).2
                  (sizeL a (b + c) d).1 (sizeL a (b + c) d).2).toAlgEquiv
                (((routeR a (b + c) d).matrixSuper (fuseSize b c).1
                      (fuseSize b c).2).toAlgEquiv
                  ((clusterFrame a b c d).toAlgEquiv v))))) := fun v => rfl
  rw [hTail4, hFrame]
  set w' : (((stdTower (K := K) a).gtensor
      ((stdTower (b + c)).matrixSuper (fuseSize b c).1
        (fuseSize b c).2)).gtensor (stdTower d)).carrier :=
    (clusterPrefix a b c d).toAlgEquiv w with hw'
  have hRR : ∀ V : ((((stdTower (K := K) a).gtensor
        (stdTower (b + c))).gtensor (stdTower d)).matrixSuper
        (fuseSize b c).1 (fuseSize b c).2).carrier,
      ((routeR a (b + c) d).matrixSuper (fuseSize b c).1
          (fuseSize b c).2).toAlgEquiv V
      = ((stdMatrixCast (add_assoc a (b + c) d).symm
            (sizeL_eq_sizeR a (b + c) d).symm).matrixSuper
          (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
        (((matrixSuperComp (stdTower (a + (b + c + d)))
              (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
              (fuseSize a (b + c + d)).1
              (fuseSize a (b + c + d)).2).matrixSuper (fuseSize b c).1
            (fuseSize b c).2).toAlgEquiv
          ((((stdFuse a (b + c + d)).matrixSuper (fuseSize (b + c) d).1
                (fuseSize (b + c) d).2).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            (((matrixSuperGtensorRight (stdTower a) (stdTower (b + c + d))
                  (fuseSize (b + c) d).1
                  (fuseSize (b + c) d).2).matrixSuper (fuseSize b c).1
                (fuseSize b c).2).toAlgEquiv
              ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                    (stdFuse (b + c) d)).matrixSuper (fuseSize b c).1
                  (fuseSize b c).2).toAlgEquiv
                (((gtensorAssoc (stdTower a) (stdTower (b + c))
                      (stdTower d)).matrixSuper (fuseSize b c).1
                    (fuseSize b c).2).toAlgEquiv V))))) := fun V => rfl
  rw [hRR]
  -- interchange the head-side stabilizations on the aligned route
  have hA1 :
      (matrixSuperGtensorRight (stdTower (K := K) a) (stdTower (b + c + d))
          (sizeL b c d).1 (sizeL b c d).2).toAlgEquiv
        (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            (matrixSuperComp (stdTower (b + c + d)) (fuseSize b c).1
              (fuseSize b c).2 (fuseSize (b + c) d).1
              (fuseSize (b + c) d).2)).toAlgEquiv
          (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              ((stdFuse (b + c) d).matrixSuper (fuseSize b c).1
                (fuseSize b c).2)).toAlgEquiv
            (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                (matrixSuperGtensor (stdTower (b + c)) (stdTower d)
                  (fuseSize b c).1 (fuseSize b c).2)).toAlgEquiv
              ((gtensorAssoc (stdTower a)
                  ((stdTower (b + c)).matrixSuper (fuseSize b c).1
                    (fuseSize b c).2) (stdTower d)).toAlgEquiv w'))))
      = (matrixSuperComp ((stdTower a).gtensor (stdTower (b + c + d)))
            (fuseSize b c).1 (fuseSize b c).2 (fuseSize (b + c) d).1
            (fuseSize (b + c) d).2).toAlgEquiv
        (((matrixSuperGtensorRight (stdTower a) (stdTower (b + c + d))
              (fuseSize (b + c) d).1 (fuseSize (b + c) d).2).matrixSuper
            (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
          ((matrixSuperGtensorRight (stdTower a)
              ((stdTower (b + c + d)).matrixSuper (fuseSize (b + c) d).1
                (fuseSize (b + c) d).2)
              (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
            (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                ((stdFuse (b + c) d).matrixSuper (fuseSize b c).1
                  (fuseSize b c).2)).toAlgEquiv
              (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                  (matrixSuperGtensor (stdTower (b + c)) (stdTower d)
                    (fuseSize b c).1 (fuseSize b c).2)).toAlgEquiv
                ((gtensorAssoc (stdTower a)
                    ((stdTower (b + c)).matrixSuper (fuseSize b c).1
                      (fuseSize b c).2) (stdTower d)).toAlgEquiv w'))))) :=
    matrixSuperComp_gtensorRight_apply (fuseSize (b + c) d).1
      (fuseSize (b + c) d).2 (fuseSize b c).1 (fuseSize b c).2 _
  rw [hA1]
  have hA2 :
      (matrixSuperGtensorRight (stdTower (K := K) a)
          ((stdTower (b + c + d)).matrixSuper (fuseSize (b + c) d).1
            (fuseSize (b + c) d).2)
          (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
        (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            ((stdFuse (b + c) d).matrixSuper (fuseSize b c).1
              (fuseSize b c).2)).toAlgEquiv
          (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (matrixSuperGtensor (stdTower (b + c)) (stdTower d)
                (fuseSize b c).1 (fuseSize b c).2)).toAlgEquiv
            ((gtensorAssoc (stdTower a)
                ((stdTower (b + c)).matrixSuper (fuseSize b c).1
                  (fuseSize b c).2) (stdTower d)).toAlgEquiv w')))
      = (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            (stdFuse (b + c) d)).matrixSuper (fuseSize b c).1
          (fuseSize b c).2).toAlgEquiv
        ((matrixSuperGtensorRight (stdTower a)
            ((stdTower (b + c)).gtensor (stdTower d))
            (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
          (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (matrixSuperGtensor (stdTower (b + c)) (stdTower d)
                (fuseSize b c).1 (fuseSize b c).2)).toAlgEquiv
            ((gtensorAssoc (stdTower a)
                ((stdTower (b + c)).matrixSuper (fuseSize b c).1
                  (fuseSize b c).2) (stdTower d)).toAlgEquiv w'))) :=
    matrixSuperGtensorRight_full_natural_apply
      (SuperAlgEquiv.refl (stdTower a)) (stdFuse (b + c) d)
      (fuseSize b c).1 (fuseSize b c).2 _
  rw [hA2]
  have hHex := matrixSuperGtensorRight_gassoc_apply
    (A := stdTower (K := K) a) (S := stdTower (b + c)) (D := stdTower d)
    (fuseSize b c).1 (fuseSize b c).2 w'
  rw [hHex]
  have hA4 :
      (matrixSuperComp ((stdTower (K := K) (a + (b + c + d))).matrixSuper
            (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2)
          (fuseSize b c).1 (fuseSize b c).2 (fuseSize (b + c) d).1
          (fuseSize (b + c) d).2).toAlgEquiv
        ((((stdFuse a (b + c + d)).matrixSuper (fuseSize (b + c) d).1
              (fuseSize (b + c) d).2).matrixSuper (fuseSize b c).1
            (fuseSize b c).2).toAlgEquiv
          (((matrixSuperGtensorRight (stdTower a) (stdTower (b + c + d))
                (fuseSize (b + c) d).1
                (fuseSize (b + c) d).2).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                  (stdFuse (b + c) d)).matrixSuper (fuseSize b c).1
                (fuseSize b c).2).toAlgEquiv
              (((gtensorAssoc (stdTower a) (stdTower (b + c))
                    (stdTower d)).matrixSuper (fuseSize b c).1
                  (fuseSize b c).2).toAlgEquiv
                ((matrixSuperGtensor ((stdTower a).gtensor
                      (stdTower (b + c))) (stdTower d)
                    (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
                  (((matrixSuperGtensorRight (stdTower a)
                        (stdTower (b + c)) (fuseSize b c).1
                        (fuseSize b c).2).gtensorCongr
                      (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w'))))))
      = ((stdFuse a (b + c + d)).matrixSuper (sizeL b c d).1
          (sizeL b c d).2).toAlgEquiv
        ((matrixSuperComp ((stdTower a).gtensor (stdTower (b + c + d)))
            (fuseSize b c).1 (fuseSize b c).2 (fuseSize (b + c) d).1
            (fuseSize (b + c) d).2).toAlgEquiv
          (((matrixSuperGtensorRight (stdTower a) (stdTower (b + c + d))
                (fuseSize (b + c) d).1
                (fuseSize (b + c) d).2).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                  (stdFuse (b + c) d)).matrixSuper (fuseSize b c).1
                (fuseSize b c).2).toAlgEquiv
              (((gtensorAssoc (stdTower a) (stdTower (b + c))
                    (stdTower d)).matrixSuper (fuseSize b c).1
                  (fuseSize b c).2).toAlgEquiv
                ((matrixSuperGtensor ((stdTower a).gtensor
                      (stdTower (b + c))) (stdTower d)
                    (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
                  (((matrixSuperGtensorRight (stdTower a)
                        (stdTower (b + c)) (fuseSize b c).1
                        (fuseSize b c).2).gtensorCongr
                      (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w')))))) :=
    matrixSuperComp_natural_apply (stdFuse a (b + c + d))
      (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
      (fuseSize b c).1 (fuseSize b c).2 _
  rw [← hA4]
  set W4 : ((((stdTower (K := K) (a + (b + c + d))).matrixSuper
      (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2).matrixSuper
      (fuseSize (b + c) d).1 (fuseSize (b + c) d).2).matrixSuper
      (fuseSize b c).1 (fuseSize b c).2).carrier :=
    (((stdFuse a (b + c + d)).matrixSuper (fuseSize (b + c) d).1
          (fuseSize (b + c) d).2).matrixSuper (fuseSize b c).1
        (fuseSize b c).2).toAlgEquiv
      (((matrixSuperGtensorRight (stdTower a) (stdTower (b + c + d))
            (fuseSize (b + c) d).1
            (fuseSize (b + c) d).2).matrixSuper (fuseSize b c).1
          (fuseSize b c).2).toAlgEquiv
        ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (stdFuse (b + c) d)).matrixSuper (fuseSize b c).1
            (fuseSize b c).2).toAlgEquiv
          (((gtensorAssoc (stdTower a) (stdTower (b + c))
                (stdTower d)).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((matrixSuperGtensor ((stdTower a).gtensor
                  (stdTower (b + c))) (stdTower d)
                (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
              (((matrixSuperGtensorRight (stdTower a)
                    (stdTower (b + c)) (fuseSize b c).1
                    (fuseSize b c).2).gtensorCongr
                  (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w')))))
  have hSlide := stdMatrixCast_matrixSuperComp_apply
    (add_assoc a (b + c) d).symm (sizeL_eq_sizeR a (b + c) d).symm
    (fuseSize b c).1 (fuseSize b c).2
    (((matrixSuperComp (stdTower (K := K) (a + (b + c + d)))
          (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
          (fuseSize a (b + c + d)).1
          (fuseSize a (b + c + d)).2).matrixSuper (fuseSize b c).1
        (fuseSize b c).2).toAlgEquiv W4)
  rw [hSlide]
  have hcanc₅ : ∀ X, ((stdMatrixCast (K := K) (clusterIndex_eq₄ a b c d)
        (clusterSize_eq₄ a b c d)).symm).toAlgEquiv
      ((stdMatrixCast (K := K) (clusterIndex_eq₄ a b c d)
        (clusterSize_eq₄ a b c d)).toAlgEquiv X) = X := fun X =>
    AlgEquiv.symm_apply_apply _ X
  rw [hcanc₅]
  have hAssoc4 :
      (matrixSuperComp (stdTower (K := K) (a + (b + c + d)))
          (fuseSize b c).1 (fuseSize b c).2
          (sizeR a (b + c) d).1 (sizeR a (b + c) d).2).toAlgEquiv
        (((matrixSuperComp (stdTower (K := K) (a + (b + c + d)))
              (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
              (fuseSize a (b + c + d)).1
              (fuseSize a (b + c + d)).2).matrixSuper (fuseSize b c).1
            (fuseSize b c).2).toAlgEquiv W4)
      = (matrixSuperCompAssoc (stdTower (K := K) (a + (b + c + d)))
          (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2
          (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
          (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv
        ((matrixSuperComp (stdTower (K := K) (a + (b + c + d)))
            (sizeL b c d).1 (sizeL b c d).2
            (fuseSize a (b + c + d)).1
            (fuseSize a (b + c + d)).2).toAlgEquiv
          ((matrixSuperComp ((stdTower (K := K)
                (a + (b + c + d))).matrixSuper
                (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2)
              (fuseSize b c).1 (fuseSize b c).2
              (fuseSize (b + c) d).1
              (fuseSize (b + c) d).2).toAlgEquiv W4)) :=
    matrixSuperComp_assoc_apply (fuseSize a (b + c + d)).1
      (fuseSize a (b + c + d)).2 (fuseSize (b + c) d).1
      (fuseSize (b + c) d).2 (fuseSize b c).1 (fuseSize b c).2 W4
  rw [hAssoc4]
  have hcancA : ∀ X, ((matrixSuperCompAssoc
        (stdTower (K := K) (a + (b + c + d)))
        (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2
        (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
        (fuseSize b c).1 (fuseSize b c).2).symm).toAlgEquiv
      ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + c + d)))
        (fuseSize a (b + c + d)).1 (fuseSize a (b + c + d)).2
        (fuseSize (b + c) d).1 (fuseSize (b + c) d).2
        (fuseSize b c).1 (fuseSize b c).2).toAlgEquiv X) = X := fun X =>
    AlgEquiv.symm_apply_apply _ X
  rw [hcancA]

end Factor

end Superfusion

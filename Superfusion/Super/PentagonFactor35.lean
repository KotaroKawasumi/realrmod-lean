/-
Superfusion / Super / PentagonFactor35

Milestone M7d-5b-4-iii(c), part 3: **the (cd)-cluster prefix and the
factorization of vertex 5**.  With `γ := fuseSize c d`:

- the common prefix
  `Π := (refl_{a⊗b} ⊗c stdFuse c d) ∘ gassoc (a⊗b) c d`,
- the matrix-frame change
  `Ξ := mSGR : (A⊗B) ⊗ M_γ(T_{c+d}) ≅ M_γ((A⊗B) ⊗ T_{c+d})`,
- the factored tails
  `T3/T5 := Ξ ≫ (routeL/routeR a b (c+d)).matrixSuper γ ≫ Θ`,
  where the shared tail `Θ` collapses the `γ`-layer onto the cluster
  route size and lands on the pentagon target through the
  collapse-reassociation bridge `matrixSuperCompAssoc⁻¹` and the
  index/size casts (final-leg latitude of the design brief, mirroring
  `clusterTail4` of `PentagonFactor.lean`),

satisfy the factorization equality `alignedRoute5 = T5 ∘ Π` (F5).
The proof needs two NEW sign-free coherences, both proved on
generators where every commutation passes a slot holding `1`:

- the **pentagon of associators** (`gassoc_pentagon_apply`): the two
  rebracketing routes `((PQ)R)S ≅ P(Q(RS))` agree — on a full pure
  tensor this is a chain of `gassoc_tmul` computations, extended to
  all elements by a two-level `TensorProduct.induction_on`;
- the **right-slot stabilization hexagon**
  (`matrixSuperGtensorRight_gassoc_right_apply`): pulling the matrix
  layer out of the right slot of `(A⊗B) ⊗ M_γ(S)` and reassociating
  entrywise agrees with reassociating first and pulling the layer
  out of the two nested right slots.

**Caveat discovered in this round (F3′)**: the companion
factorization `quadRoute3 = T3 ∘ Π` of the design brief is *false*.
Reducing both sides through the naturality kit and the two hexagons
leaves the two orders of stabilizing
`M_σ(T_{a+b}) ᵍ⊗ M_γ(T_{c+d})` (`σ` out first vs `γ` out first),
whose honest comparison `E2 ∘ E1⁻¹` is the *Koszul-signed* layer
transposition: on the entry at position `(I,J),(K,L)` it carries the
sign `(-1)^{π_σ(I)π_γ(K) + π_σ(J)π_γ(L)}`.  Since every admissible
final leg (`matrixSuperComp`, `matrixSuperCompAssoc`, `stdMatrixCast`)
is a sign-free reindexing, the factorization identity would force
this sign to vanish, which fails exactly when
`fuseSize a b = fuseSize c d = (8,8)` (both clusters wrap — e.g.
`a = b = c = d = 4`); on the other nine realizable size combinations
the index-level coincidence and the sign both hold.  This was checked
end-to-end in a faithful model of the kit (which reproduces the
landed `quadRoute2_factor` and `alignedRoute4_factor` exactly).  The
e35 edge therefore needs a sign-corrected bridge (conjugation by the
even diagonal sign unit `D_ε(I,K) = (-1)^{π_σ(I)π_γ(K)}` composed
with the honest transposition), not a plain factorization.
-/
import Superfusion.Super.PentagonEdge13

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

/-! ### The generic kit: markers, parity projections, and the two
new sign-free coherences -/

section Kit35

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

/-! #### The pentagon of associators -/

/-- `v ↦ toCA v ᵍ⊗ c` as a `LinearMap`, for fixed `c` (local copy of
the private helper of `PentagonNaturality.lean`). -/
private noncomputable def tmulRightFixCA {P Q R : SuperAlgebra K}
    (c : R.carrier) :
    (P.grading ᵍ⊗[K] Q.grading) →ₗ[K]
      ((P.gtensor Q).grading ᵍ⊗[K] R.grading) :=
  (GradedTensorProduct.of K (P.gtensor Q).grading
      R.grading).toLinearMap ∘ₗ
    (TensorProduct.mk K (P.gtensor Q).carrier R.carrier).flip c

private theorem tmulRightFixCA_apply {P Q R : SuperAlgebra K}
    (c : R.carrier) (v : P.grading ᵍ⊗[K] Q.grading) :
    tmulRightFixCA c v = toCA v ᵍ⊗ₜ[K] c := rfl

/-- **The pentagon of associators** for the graded tensor product,
applied form: the two rebracketing routes `((PQ)R)S ≅ P(Q(RS))`
agree.  On a full pure tensor this is a chain of `gassoc_tmul` /
`gcongr_tmul` computations, where no Koszul sign can arise; the
extension to all elements is a two-level
`TensorProduct.induction_on` through the `tmulRightFixCA` linear
maps, as in `gassoc_natural_apply`. -/
private theorem gassoc_pentagon_apply {P Q R S : SuperAlgebra K}
    (w : (((P.gtensor Q).gtensor R).gtensor S).carrier) :
    ((SuperAlgEquiv.refl P).gtensorCongr
        (gtensorAssoc Q R S)).toAlgEquiv
        ((gtensorAssoc P (Q.gtensor R) S).toAlgEquiv
          (((gtensorAssoc P Q R).gtensorCongr
            (SuperAlgEquiv.refl S)).toAlgEquiv w))
      = (gtensorAssoc P Q (R.gtensor S)).toAlgEquiv
        ((gtensorAssoc (P.gtensor Q) R S).toAlgEquiv w) := by
  set F : (((P.gtensor Q).gtensor R).gtensor S).carrier →ₐ[K]
      (P.gtensor (Q.gtensor (R.gtensor S))).carrier :=
    (((SuperAlgEquiv.refl P).gtensorCongr
        (gtensorAssoc Q R S)).toAlgEquiv.toAlgHom).comp
      (((gtensorAssoc P (Q.gtensor R) S).toAlgEquiv.toAlgHom).comp
        (((gtensorAssoc P Q R).gtensorCongr
          (SuperAlgEquiv.refl S)).toAlgEquiv.toAlgHom)) with hF
  set G : (((P.gtensor Q).gtensor R).gtensor S).carrier →ₐ[K]
      (P.gtensor (Q.gtensor (R.gtensor S))).carrier :=
    ((gtensorAssoc P Q (R.gtensor S)).toAlgEquiv.toAlgHom).comp
      ((gtensorAssoc (P.gtensor Q) R S).toAlgEquiv.toAlgHom) with hG
  have hpure : ∀ (p₀ : P.carrier) (q₀ : Q.carrier) (r₀ : R.carrier)
      (s₀ : S.carrier),
      F (toCA (toCA (toCA (p₀ ᵍ⊗ₜ[K] q₀) ᵍ⊗ₜ[K] r₀) ᵍ⊗ₜ[K] s₀))
        = G (toCA (toCA (toCA (p₀ ᵍ⊗ₜ[K] q₀) ᵍ⊗ₜ[K] r₀)
          ᵍ⊗ₜ[K] s₀)) := by
    intro p₀ q₀ r₀ s₀
    have hFv : F (toCA (toCA (toCA (p₀ ᵍ⊗ₜ[K] q₀) ᵍ⊗ₜ[K] r₀)
          ᵍ⊗ₜ[K] s₀))
        = toCA (p₀ ᵍ⊗ₜ[K] toCA (q₀ ᵍ⊗ₜ[K] toCA (r₀ ᵍ⊗ₜ[K] s₀))) := by
      show ((SuperAlgEquiv.refl P).gtensorCongr
          (gtensorAssoc Q R S)).toAlgEquiv
          ((gtensorAssoc P (Q.gtensor R) S).toAlgEquiv
            (((gtensorAssoc P Q R).gtensorCongr
              (SuperAlgEquiv.refl S)).toAlgEquiv
              (toCA (toCA (toCA (p₀ ᵍ⊗ₜ[K] q₀) ᵍ⊗ₜ[K] r₀)
                ᵍ⊗ₜ[K] s₀))))
        = _
      rw [gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl S).toAlgEquiv s₀ = s₀ from rfl,
        gtensorAssoc_tmulCA, gtensorAssoc_tmulCA, gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl P).toAlgEquiv p₀ = p₀ from rfl,
        gtensorAssoc_tmulCA]
    have hGv : G (toCA (toCA (toCA (p₀ ᵍ⊗ₜ[K] q₀) ᵍ⊗ₜ[K] r₀)
          ᵍ⊗ₜ[K] s₀))
        = toCA (p₀ ᵍ⊗ₜ[K] toCA (q₀ ᵍ⊗ₜ[K] toCA (r₀ ᵍ⊗ₜ[K] s₀))) := by
      show (gtensorAssoc P Q (R.gtensor S)).toAlgEquiv
          ((gtensorAssoc (P.gtensor Q) R S).toAlgEquiv
            (toCA (toCA (toCA (p₀ ᵍ⊗ₜ[K] q₀) ᵍ⊗ₜ[K] r₀) ᵍ⊗ₜ[K] s₀)))
        = _
      rw [gtensorAssoc_tmulCA, gtensorAssoc_tmulCA]
    rw [hFv, hGv]
  have hhom : F = G := by
    refine galgHom_ext ((P.gtensor Q).gtensor R).grading S.grading ?_
    intro u s₀
    have key1 : F.toLinearMap
          ∘ₗ tmulRightFixCA (P := P.gtensor Q) (Q := R) (R := S) s₀
        = G.toLinearMap ∘ₗ tmulRightFixCA s₀ := by
      apply LinearMap.ext
      intro v
      refine TensorProduct.induction_on
        (motive := fun v : (P.gtensor Q).grading ᵍ⊗[K] R.grading =>
          (F.toLinearMap ∘ₗ tmulRightFixCA (R := S) s₀) v
            = (G.toLinearMap ∘ₗ tmulRightFixCA s₀) v) v ?_ ?_ ?_
      · exact (map_zero (F.toLinearMap ∘ₗ tmulRightFixCA s₀)).trans
          (map_zero (G.toLinearMap ∘ₗ tmulRightFixCA s₀)).symm
      · intro u' r₀
        show F (tmulRightFixCA s₀ (u' ᵍ⊗ₜ[K] r₀))
          = G (tmulRightFixCA s₀ (u' ᵍ⊗ₜ[K] r₀))
        have key2 : (F.toLinearMap
              ∘ₗ tmulRightFixCA (P := P.gtensor Q) (Q := R) (R := S) s₀)
              ∘ₗ tmulRightFixCA (P := P) (Q := Q) (R := R) r₀
            = (G.toLinearMap ∘ₗ tmulRightFixCA s₀)
              ∘ₗ tmulRightFixCA r₀ := by
          apply LinearMap.ext
          intro v'
          refine TensorProduct.induction_on
            (motive := fun v' : P.grading ᵍ⊗[K] Q.grading =>
              ((F.toLinearMap ∘ₗ tmulRightFixCA (R := S) s₀)
                ∘ₗ tmulRightFixCA (R := R) r₀) v'
                = ((G.toLinearMap ∘ₗ tmulRightFixCA s₀)
                  ∘ₗ tmulRightFixCA r₀) v') v' ?_ ?_ ?_
          · exact (map_zero ((F.toLinearMap ∘ₗ tmulRightFixCA s₀)
                ∘ₗ tmulRightFixCA r₀)).trans
              (map_zero ((G.toLinearMap ∘ₗ tmulRightFixCA s₀)
                ∘ₗ tmulRightFixCA r₀)).symm
          · intro p₀ q₀
            show F (tmulRightFixCA s₀
                (tmulRightFixCA r₀ (p₀ ᵍ⊗ₜ[K] q₀)))
              = G (tmulRightFixCA s₀
                (tmulRightFixCA r₀ (p₀ ᵍ⊗ₜ[K] q₀)))
            rw [tmulRightFixCA_apply, tmulRightFixCA_apply]
            exact hpure p₀ q₀ r₀ s₀
          · intro x y hx hy
            exact (map_add ((F.toLinearMap ∘ₗ tmulRightFixCA s₀)
                ∘ₗ tmulRightFixCA r₀) x y).trans <|
              hx ▸ hy ▸ (map_add ((G.toLinearMap ∘ₗ tmulRightFixCA s₀)
                ∘ₗ tmulRightFixCA r₀) x y).symm
        exact LinearMap.congr_fun key2 u'
      · intro x y hx hy
        exact (map_add (F.toLinearMap ∘ₗ tmulRightFixCA s₀) x y).trans <|
          hx ▸ hy ▸ (map_add (G.toLinearMap ∘ₗ tmulRightFixCA s₀)
            x y).symm
    exact LinearMap.congr_fun key1 u
  exact AlgHom.congr_fun hhom w

/-! #### The right-slot stabilization hexagon -/

/-- **The right-slot stabilization hexagon**: pulling the matrix
layer out of the right slot of `(A ⊗ B) ⊗ M_γ(S)` and reassociating
entrywise agrees with reassociating first and pulling the layer out
of the two nested right slots.  Both sides are algebra maps, so it
suffices to compare them on the generators `(a ᵍ⊗ 1) ᵍ⊗ 1`,
`(1 ᵍ⊗ b) ᵍ⊗ 1` and `1 ᵍ⊗ M`, where no Koszul sign can arise. -/
private theorem matrixSuperGtensorRight_gassoc_right_apply
    {A B S : SuperAlgebra K} (p q : ℕ)
    (w : ((A.gtensor B).gtensor (S.matrixSuper p q)).carrier) :
    (matrixSuperGtensorRight A (B.gtensor S) p q).toAlgEquiv
        (((SuperAlgEquiv.refl A).gtensorCongr
          (matrixSuperGtensorRight B S p q)).toAlgEquiv
          ((gtensorAssoc A B (S.matrixSuper p q)).toAlgEquiv w))
      = ((gtensorAssoc A B S).matrixSuper p q).toAlgEquiv
        ((matrixSuperGtensorRight (A.gtensor B) S p q).toAlgEquiv
          w) := by
  set F : ((A.gtensor B).gtensor (S.matrixSuper p q)).carrier →ₐ[K]
      ((A.gtensor (B.gtensor S)).matrixSuper p q).carrier :=
    ((matrixSuperGtensorRight A (B.gtensor S) p q).toAlgEquiv.toAlgHom).comp
      ((((SuperAlgEquiv.refl A).gtensorCongr
          (matrixSuperGtensorRight B S p q)).toAlgEquiv.toAlgHom).comp
        ((gtensorAssoc A B (S.matrixSuper p q)).toAlgEquiv.toAlgHom))
    with hF
  set G : ((A.gtensor B).gtensor (S.matrixSuper p q)).carrier →ₐ[K]
      ((A.gtensor (B.gtensor S)).matrixSuper p q).carrier :=
    (((gtensorAssoc A B S).matrixSuper p q).toAlgEquiv.toAlgHom).comp
      ((matrixSuperGtensorRight (A.gtensor B) S
        p q).toAlgEquiv.toAlgHom) with hG
  -- the `a`-generator: both sides give the signed diagonal of `a₀`.
  have hC1 : ∀ a₀ : A.carrier,
      F (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))
        = G (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))) := by
    intro a₀
    have h1 : F (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))
        = (matrixSuperGtensorRight A (B.gtensor S) p q).toAlgEquiv
          (toCA (a₀ ᵍ⊗ₜ[K]
            (1 : ((B.gtensor S).matrixSuper p q).carrier))) := by
      show (matrixSuperGtensorRight A (B.gtensor S) p q).toAlgEquiv
          (((SuperAlgEquiv.refl A).gtensorCongr
            (matrixSuperGtensorRight B S p q)).toAlgEquiv
            ((gtensorAssoc A B (S.matrixSuper p q)).toAlgEquiv
              (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))
                ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))))
        = _
      rw [gtensorAssoc_tmulCA, gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl A).toAlgEquiv a₀ = a₀ from rfl,
        toCA_one_one, map_one]
    have h3 : G (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K]
                (1 : (B.gtensor S).carrier))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K]
                  (1 : (B.gtensor S).carrier))) := by
      show ((gtensorAssoc A B S).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensorRight (A.gtensor B) S p q).toAlgEquiv
            (toCA (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))
              ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))))
        = _
      rw [matrixSuperGtensorRight_tmul_one p q
        (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier)))]
      refine Matrix.ext fun r s => ?_
      show (gtensorAssoc A B S).toAlgEquiv
          (Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((evenPart (A.gtensor B).grading
                (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier)))) ᵍ⊗ₜ[K]
                (1 : S.carrier))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((oddPart (A.gtensor B).grading
                  (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier)))) ᵍ⊗ₜ[K]
                  (1 : S.carrier))) r s)
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K]
                (1 : (B.gtensor S).carrier))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K]
                  (1 : (B.gtensor S).carrier))) r s
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
          evenPart_tmulCA_one, oddPart_tmulCA_one]
        show (gtensorAssoc A B S).toAlgEquiv
            (toCA (toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K]
                (1 : B.carrier)) ᵍ⊗ₜ[K] (1 : S.carrier))
              + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
                toCA (toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K]
                  (1 : B.carrier)) ᵍ⊗ₜ[K] (1 : S.carrier)))
          = toCA ((evenPart A.grading a₀) ᵍ⊗ₜ[K]
              (1 : (B.gtensor S).carrier))
            + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
              toCA ((oddPart A.grading a₀) ᵍ⊗ₜ[K]
                (1 : (B.gtensor S).carrier))
        rw [map_add, map_zsmul, gtensorAssoc_tmulCA,
          gtensorAssoc_tmulCA, toCA_one_one]
      · rw [Matrix.diagonal_apply_ne _ hrs,
          Matrix.diagonal_apply_ne _ hrs]
        exact map_zero _
    exact (h1.trans (matrixSuperGtensorRight_tmul_one (P := A)
      (Q := B.gtensor S) p q a₀)).trans h3.symm
  -- the `b`-generator: both sides give the reassociated signed
  -- diagonal of `b₀`.
  have hC2 : ∀ b₀ : B.carrier,
      F (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀)
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))
        = G (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀)
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))) := by
    intro b₀
    have h1 : F (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀)
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((evenPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                  toCA ((oddPart B.grading b₀) ᵍ⊗ₜ[K]
                    (1 : S.carrier)))) := by
      show (matrixSuperGtensorRight A (B.gtensor S) p q).toAlgEquiv
          (((SuperAlgEquiv.refl A).gtensorCongr
            (matrixSuperGtensorRight B S p q)).toAlgEquiv
            ((gtensorAssoc A B (S.matrixSuper p q)).toAlgEquiv
              (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀)
                ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))))
        = _
      rw [gtensorAssoc_tmulCA, gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl A).toAlgEquiv (1 : A.carrier) = 1
          from rfl,
        matrixSuperGtensorRight_tmul_one p q b₀,
        matrixSuperGtensorRight_one_tmul (P := A) (Q := B.gtensor S)
          p q
          (Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((evenPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((oddPart B.grading b₀) ᵍ⊗ₜ[K]
                  (1 : S.carrier))))]
      refine Matrix.ext fun r s => ?_
      rw [Matrix.map_apply]
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        rw [gtmulCA_add, gtmulCA_zsmul]
      · rw [Matrix.diagonal_apply_ne _ hrs,
          Matrix.diagonal_apply_ne _ hrs]
        exact gtmulCA_zero (1 : A.carrier)
    have h3 : G (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀)
          ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier)))
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((evenPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                  toCA ((oddPart B.grading b₀) ᵍ⊗ₜ[K]
                    (1 : S.carrier)))) := by
      show ((gtensorAssoc A B S).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensorRight (A.gtensor B) S p q).toAlgEquiv
            (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀)
              ᵍ⊗ₜ[K] (1 : (S.matrixSuper p q).carrier))))
        = _
      rw [matrixSuperGtensorRight_tmul_one p q
        (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀))]
      refine Matrix.ext fun r s => ?_
      show (gtensorAssoc A B S).toAlgEquiv
          (Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((evenPart (A.gtensor B).grading
                (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀))) ᵍ⊗ₜ[K]
                (1 : S.carrier))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((oddPart (A.gtensor B).grading
                  (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀))) ᵍ⊗ₜ[K]
                  (1 : S.carrier))) r s)
        = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
            toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((evenPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
              + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
                toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                  toCA ((oddPart B.grading b₀) ᵍ⊗ₜ[K]
                    (1 : S.carrier)))) r s
      by_cases hrs : r = s
      · subst hrs
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
          evenPart_one_tmulCA, oddPart_one_tmulCA]
        show (gtensorAssoc A B S).toAlgEquiv
            (toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                evenPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier))
              + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
                toCA (toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                  oddPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
          = toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA ((evenPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
            + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
              toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
                toCA ((oddPart B.grading b₀) ᵍ⊗ₜ[K] (1 : S.carrier)))
        rw [map_add, map_zsmul, gtensorAssoc_tmulCA,
          gtensorAssoc_tmulCA]
      · rw [Matrix.diagonal_apply_ne _ hrs,
          Matrix.diagonal_apply_ne _ hrs]
        exact map_zero _
    exact h1.trans h3.symm
  -- the `M`-generator: both sides give the entrywise pure tensors.
  have hR : ∀ M₀ : (S.matrixSuper p q).carrier,
      F (toCA ((1 : (A.gtensor B).carrier) ᵍ⊗ₜ[K] M₀))
        = G (toCA ((1 : (A.gtensor B).carrier) ᵍ⊗ₜ[K] M₀)) := by
    intro M₀
    have h1 : F (toCA ((1 : (A.gtensor B).carrier) ᵍ⊗ₜ[K] M₀))
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA ((1 : B.carrier) ᵍ⊗ₜ[K] z))) := by
      show (matrixSuperGtensorRight A (B.gtensor S) p q).toAlgEquiv
          (((SuperAlgEquiv.refl A).gtensorCongr
            (matrixSuperGtensorRight B S p q)).toAlgEquiv
            ((gtensorAssoc A B (S.matrixSuper p q)).toAlgEquiv
              (toCA ((1 : (A.gtensor B).carrier) ᵍ⊗ₜ[K] M₀))))
        = _
      rw [show (1 : (A.gtensor B).carrier)
          = toCA ((1 : A.carrier) ᵍ⊗ₜ[K] (1 : B.carrier)) from
          toCA_one_one.symm,
        gtensorAssoc_tmulCA, gtensorCongr_tmulCA,
        show (SuperAlgEquiv.refl A).toAlgEquiv (1 : A.carrier) = 1
          from rfl,
        matrixSuperGtensorRight_one_tmul p q M₀,
        matrixSuperGtensorRight_one_tmul (P := A) (Q := B.gtensor S)
          p q
          (Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : B.carrier) ᵍ⊗ₜ[K] z)))]
      rw [show ((Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : B.carrier) ᵍ⊗ₜ[K] z)) :
            ((B.gtensor S).matrixSuper p q).carrier) :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
            (B.gtensor S).carrier)
          = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : B.carrier) ᵍ⊗ₜ[K] z)) from rfl,
        Matrix.map_map]
      rfl
    have h3 : G (toCA ((1 : (A.gtensor B).carrier) ᵍ⊗ₜ[K] M₀))
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA ((1 : B.carrier) ᵍ⊗ₜ[K] z))) := by
      show ((gtensorAssoc A B S).matrixSuper p q).toAlgEquiv
          ((matrixSuperGtensorRight (A.gtensor B) S p q).toAlgEquiv
            (toCA ((1 : (A.gtensor B).carrier) ᵍ⊗ₜ[K] M₀)))
        = _
      rw [matrixSuperGtensorRight_one_tmul p q M₀]
      refine Matrix.ext fun r s => ?_
      show (gtensorAssoc A B S).toAlgEquiv
          (Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : (A.gtensor B).carrier) ᵍ⊗ₜ[K] z))
            r s)
        = Matrix.map
            (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier)
            (fun z => toCA ((1 : A.carrier) ᵍ⊗ₜ[K]
              toCA ((1 : B.carrier) ᵍ⊗ₜ[K] z))) r s
      rw [Matrix.map_apply, Matrix.map_apply,
        show (1 : (A.gtensor B).carrier)
          = toCA ((1 : A.carrier) ᵍ⊗ₜ[K] (1 : B.carrier)) from
          toCA_one_one.symm]
      exact gtensorAssoc_tmulCA (1 : A.carrier) (1 : B.carrier)
        ((M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) S.carrier) r s)
    exact h1.trans h3.symm
  -- assemble: agree on both inclusions, hence everywhere.
  have hLhom : F.comp (includeLeft
        (A.gtensor B).grading (S.matrixSuper p q).grading)
      = G.comp (includeLeft
        (A.gtensor B).grading (S.matrixSuper p q).grading) := by
    refine galgHom_ext A.grading B.grading ?_
    intro a₀ b₀
    show F (includeLeft (A.gtensor B).grading
        (S.matrixSuper p q).grading (toCA (a₀ ᵍ⊗ₜ[K] b₀)))
      = G (includeLeft (A.gtensor B).grading
        (S.matrixSuper p q).grading (toCA (a₀ ᵍ⊗ₜ[K] b₀)))
    have e1 : F (includeLeft (A.gtensor B).grading
          (S.matrixSuper p q).grading
          (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))))
        = G (includeLeft (A.gtensor B).grading
          (S.matrixSuper p q).grading
          (toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier)))) :=
      hC1 a₀
    have e2 : F (includeLeft (A.gtensor B).grading
          (S.matrixSuper p q).grading
          (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀)))
        = G (includeLeft (A.gtensor B).grading
          (S.matrixSuper p q).grading
          (toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀))) :=
      hC2 b₀
    rw [show toCA (a₀ ᵍ⊗ₜ[K] b₀)
        = toCA (a₀ ᵍ⊗ₜ[K] (1 : B.carrier))
          * toCA ((1 : A.carrier) ᵍ⊗ₜ[K] b₀) from
      (includeLeft_mul_includeRight A.grading B.grading a₀ b₀).symm,
      map_mul]
    exact (map_mul F _ _).trans
      (by rw [e1, e2]; exact (map_mul G _ _).symm)
  have hRhom : F.comp (includeRight
        (A.gtensor B).grading (S.matrixSuper p q).grading)
      = G.comp (includeRight
        (A.gtensor B).grading (S.matrixSuper p q).grading) :=
    AlgHom.ext fun M₀ => hR M₀
  have hhom : F = G :=
    GradedTensorProduct.algHom_ext
      (𝒜 := (A.gtensor B).grading)
      (ℬ := (S.matrixSuper p q).grading) hLhom hRhom
  exact AlgHom.congr_fun hhom w

end Kit35

/-! ### The (cd)-cluster prefix, frame, sizes, and tails -/

section Factor35

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The common cluster-fusion prefix of the routes through `(cd)`:
reassociate onto the pair of pairs and fuse the tail cluster. -/
noncomputable def cluster35Prefix (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      (((stdTower a).gtensor (stdTower b)).gtensor
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2)) :=
  (gtensorAssoc ((stdTower a).gtensor (stdTower b)) (stdTower c)
      (stdTower d)).trans
    ((SuperAlgEquiv.refl ((stdTower a).gtensor
        (stdTower b))).gtensorCongr (stdFuse c d))

/-- The matrix-frame change: pull the `γ`-matrix layer out of the
right slot. -/
noncomputable def cluster35Frame (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2))
      ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower (c + d))).matrixSuper (fuseSize c d).1
        (fuseSize c d).2) :=
  matrixSuperGtensorRight ((stdTower a).gtensor (stdTower b))
    (stdTower (c + d)) (fuseSize c d).1 (fuseSize c d).2

/-- Composed sizes of the `(cd)`-cluster factorization agree with the
pentagon target sizes: the wrap count is bracketing-independent
(a 4096-case kernel `decide`). -/
theorem size35_eq : ∀ a b c d : ZMod 8,
    ((fuseSize c d).1 * (sizeL a b (c + d)).1
        + (fuseSize c d).2 * (sizeL a b (c + d)).2,
      (fuseSize c d).1 * (sizeL a b (c + d)).2
        + (fuseSize c d).2 * (sizeL a b (c + d)).1)
      = extSize (sizeL a b c) (a + b + c) d := by
  decide

/-- Index identity for the inner cast of the shared tail. -/
private theorem cluster35Index_eq (a b c d : ZMod 8) :
    a + (b + (c + d)) = a + b + (c + d) :=
  (add_assoc a b (c + d)).symm

/-- The composed size of the right route of `(b, c, d)`, flat-spelled
(the spelling produced by the interchange lemmas), agrees with the
left route's composite size. -/
private theorem sizeR_flat_eq_bcd (b c d : ZMod 8) :
    ((fuseSize c d).1 * (fuseSize b (c + d)).1
        + (fuseSize c d).2 * (fuseSize b (c + d)).2,
      (fuseSize c d).1 * (fuseSize b (c + d)).2
        + (fuseSize c d).2 * (fuseSize b (c + d)).1)
      = sizeL b c d :=
  (sizeL_eq_sizeR b c d).symm

/-- The composed size of the right route of `(a, b, c+d)`,
flat-spelled. -/
private theorem sizeR_flat_eq_35 (a b c d : ZMod 8) :
    ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2,
      (fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1)
      = sizeL a b (c + d) :=
  (sizeL_eq_sizeR a b (c + d)).symm

/-- Size identity for the inner cast of the shared tail. -/
private theorem cluster35Size_eq (a b c d : ZMod 8) :
    ((fuseSize c d).1 * ((fuseSize b (c + d)).1
          * (fuseSize a (b + (c + d))).1
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2)
        + (fuseSize c d).2 * ((fuseSize b (c + d)).1
          * (fuseSize a (b + (c + d))).2
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1),
      (fuseSize c d).1 * ((fuseSize b (c + d)).1
          * (fuseSize a (b + (c + d))).2
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1)
        + (fuseSize c d).2 * ((fuseSize b (c + d)).1
          * (fuseSize a (b + (c + d))).1
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2))
      = ((fuseSize c d).1 * (sizeL a b (c + d)).1
        + (fuseSize c d).2 * (sizeL a b (c + d)).2,
      (fuseSize c d).1 * (sizeL a b (c + d)).2
        + (fuseSize c d).2 * (sizeL a b (c + d)).1) := by
  rw [← sizeR_flat_eq_35 a b c d]

/-- Size identity for the final cast of the shared tail. -/
private theorem cluster35Size_final (a b c d : ZMod 8) :
    preSize (sizeR b c d) a (b + (c + d))
      = extSize (sizeL a b c) (a + b + c) d := by
  rw [← sizeL_eq_sizeR b c d, ← add_assoc b c d, ← quadSize_eq]

/-- **The shared tail** of the `(cd)`-cluster factorizations: the
collapse of the `γ`-matrix layer onto the cluster route size,
transported back to the `a + (b + (c + d))`-frame (where the right
route's own layers live), reassociated through the
collapse-reassociation bridge `matrixSuperCompAssoc⁻¹`, and cast onto
the pentagon target (the final-leg latitude of the design brief,
mirroring `clusterTail4` of `PentagonFactor.lean`). -/
noncomputable def cluster35SharedTail (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) (a + b + (c + d))).matrixSuper
        (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).matrixSuper
        (fuseSize c d).1 (fuseSize c d).2)
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (matrixSuperComp (stdTower (a + b + (c + d)))
      (fuseSize c d).1 (fuseSize c d).2
      (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).trans
    (((stdMatrixCast (cluster35Index_eq a b c d)
        (cluster35Size_eq a b c d)).symm).trans
      (((matrixSuperCompAssoc (stdTower (a + (b + (c + d))))
          (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
          (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
          (fuseSize c d).1 (fuseSize c d).2).symm).trans
        (stdMatrixCast (show a + (b + (c + d)) = a + b + c + d by ring)
          (cluster35Size_final a b c d))))

/-- The factored tail through the left-associated cluster triple
`(a, b, c+d)`: frame change, stabilized left route, shared tail. -/
noncomputable def cluster35Tail3 (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (cluster35Frame a b c d).trans
    (((routeL a b (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).trans
      (cluster35SharedTail a b c d))

/-- The factored tail through the right-associated cluster triple:
frame change, stabilized right route (which already lands on the left
route's target via its built-in cast), shared tail. -/
noncomputable def cluster35Tail5 (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (cluster35Frame a b c d).trans
    (((routeR a b (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).trans
      (cluster35SharedTail a b c d))

/-! ### Cast slides -/

/-- A `stdMatrixCast` slides past `preTail`, applied form: proved
generically (for arbitrary index/size equalities) by `subst`,
reducing both sides to the identity via
`gtensorCongr_refl_refl_apply`. -/
private theorem stdMatrixCast_preTail_apply {x y : ZMod 8} (h : x = y)
    {s t : ℕ × ℕ} (hs : s = t) (c : ZMod 8)
    (v : ((stdTower (K := K) c).gtensor
      ((stdTower x).matrixSuper s.1 s.2)).carrier) :
    (preTail c y t).toAlgEquiv
        (((SuperAlgEquiv.refl (stdTower c)).gtensorCongr
          (stdMatrixCast h hs)).toAlgEquiv v)
      = (stdMatrixCast (show c + x = c + y by rw [h])
          (show preSize s c x = preSize t c y by rw [h, hs])).toAlgEquiv
        ((preTail c x s).toAlgEquiv v) := by
  subst h
  subst hs
  show (preTail c x s).toAlgEquiv
      (((SuperAlgEquiv.refl (stdTower c)).gtensorCongr
        (SuperAlgEquiv.refl _)).toAlgEquiv v)
    = (preTail c x s).toAlgEquiv v
  rw [gtensorCongr_refl_refl_apply]

omit [Invertible (2 : K)] in
/-- A `stdMatrixCast` slides past `matrixSuperComp` (with the cast on
the inner layer), applied form (local copy of the private helper of
`PentagonFactor.lean`). -/
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

omit [Invertible (2 : K)] in
/-- Two `stdMatrixCast`s merge, applied form. -/
private theorem stdMatrixCast_trans_apply {x y z : ZMod 8}
    (h₁ : x = y) (h₂ : y = z) {s t u : ℕ × ℕ}
    (hs₁ : s = t) (hs₂ : t = u)
    (X : ((stdTower (K := K) x).matrixSuper s.1 s.2).carrier) :
    (stdMatrixCast h₂ hs₂).toAlgEquiv
        ((stdMatrixCast h₁ hs₁).toAlgEquiv X)
      = (stdMatrixCast (h₁.trans h₂) (hs₁.trans hs₂)).toAlgEquiv X := by
  subst h₁
  subst hs₁
  subst h₂
  subst hs₂
  rfl

/-! ### Factorization of vertex 5 -/

/-- **Factorization of vertex 5** through the `(cd)`-cluster prefix
(F5): the right-nested route also factors through `Π`, with the tail
replaced by the stabilized right route of the cluster triple
`(a, b, c+d)`.  The gassoc bookkeeping is the pentagon of
associators; the frame interchange is the right-slot stabilization
hexagon; the collapse reorder is `matrixSuperComp_assoc_apply` on
`(ν, μ, γ)`; and the two cast legs of the right routes slide to the
ends by the generic `subst` lemmas. -/
theorem alignedRoute5_factor (a b c d : ZMod 8)
    (w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).carrier) :
    (alignedRoute5 a b c d).toAlgEquiv w
      = (cluster35Tail5 a b c d).toAlgEquiv
        ((cluster35Prefix a b c d).toAlgEquiv w) := by
  show (stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
      (quadSize_eq a b c d).symm).toAlgEquiv
      ((preTail a (b + c + d) (sizeL b c d)).toAlgEquiv
        (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            ((gtensorAssoc (stdTower b) (stdTower c)
                (stdTower d)).trans
              (((SuperAlgEquiv.refl (stdTower b)).gtensorCongr
                  (stdFuse c d)).trans
                ((matrixSuperGtensorRight (stdTower b)
                    (stdTower (c + d))
                    (fuseSize c d).1 (fuseSize c d).2).trans
                  (((stdFuse b (c + d)).matrixSuper (fuseSize c d).1
                      (fuseSize c d).2).trans
                    ((matrixSuperComp (stdTower (b + (c + d)))
                        (fuseSize c d).1 (fuseSize c d).2
                        (fuseSize b (c + d)).1
                        (fuseSize b (c + d)).2).trans
                      (stdMatrixCast (add_assoc b c d).symm
                        (sizeR_flat_eq_bcd b c d)))))))).toAlgEquiv
          ((gtensorAssoc (stdTower a)
              ((stdTower b).gtensor (stdTower c))
              (stdTower d)).toAlgEquiv
            (((gtensorAssoc (stdTower a) (stdTower b)
                  (stdTower c)).gtensorCongr
                (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w))))
    = (cluster35Tail5 a b c d).toAlgEquiv
      ((cluster35Prefix a b c d).toAlgEquiv w)
  rw [gtensorCongr_refl_trans_apply, gtensorCongr_refl_trans_apply,
    gtensorCongr_refl_trans_apply, gtensorCongr_refl_trans_apply,
    gtensorCongr_refl_trans_apply]
  -- the pentagon of associators rebrackets the source
  have hPent := gassoc_pentagon_apply (P := stdTower (K := K) a)
    (Q := stdTower b) (R := stdTower c) (S := stdTower d) w
  rw [hPent]
  -- slide the cluster fusion below the last associator
  have hSlide1 := gassoc_natural_apply
    (SuperAlgEquiv.refl (stdTower (K := K) a))
    (SuperAlgEquiv.refl (stdTower b)) (stdFuse c d)
    ((gtensorAssoc ((stdTower a).gtensor (stdTower b)) (stdTower c)
        (stdTower d)).toAlgEquiv w)
  rw [← hSlide1, gtensorCongr_reflpair_apply]
  have hPre : (cluster35Prefix a b c d).toAlgEquiv w
      = ((SuperAlgEquiv.refl ((stdTower (K := K) a).gtensor
            (stdTower b))).gtensorCongr (stdFuse c d)).toAlgEquiv
          ((gtensorAssoc ((stdTower a).gtensor (stdTower b))
              (stdTower c) (stdTower d)).toAlgEquiv w) := rfl
  rw [← hPre]
  set w' : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).carrier :=
    (cluster35Prefix a b c d).toAlgEquiv w with hw'
  -- slide the built-in cast of `routeR b c d` through the head tail
  rw [stdMatrixCast_preTail_apply (K := K) (add_assoc b c d).symm
    (sizeR_flat_eq_bcd b c d) a, stdMatrixCast_trans_apply]
  -- expand the head tail at the right route's own spelling
  have hPT : ∀ v : ((stdTower (K := K) a).gtensor
        ((stdTower (b + (c + d))).matrixSuper
          ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1))).carrier,
      (preTail a (b + (c + d))
          ((fuseSize c d).1 * (fuseSize b (c + d)).1
              + (fuseSize c d).2 * (fuseSize b (c + d)).2,
            (fuseSize c d).1 * (fuseSize b (c + d)).2
              + (fuseSize c d).2 * (fuseSize b (c + d)).1)).toAlgEquiv v
      = (matrixSuperComp (stdTower (a + (b + (c + d))))
          ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)
          (fuseSize a (b + (c + d))).1
          (fuseSize a (b + (c + d))).2).toAlgEquiv
        (((stdFuse a (b + (c + d))).matrixSuper
            ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
            ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)).toAlgEquiv
          ((matrixSuperGtensorRight (stdTower a)
              (stdTower (b + (c + d)))
              ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
              ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)).toAlgEquiv v)) :=
    fun v => rfl
  rw [hPT]
  -- interchange the head-side stabilization with the inner collapse
  have hA1 :
      (matrixSuperGtensorRight (stdTower (K := K) a)
          (stdTower (b + (c + d)))
          ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)).toAlgEquiv
        (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            (matrixSuperComp (stdTower (b + (c + d)))
              (fuseSize c d).1 (fuseSize c d).2
              (fuseSize b (c + d)).1
              (fuseSize b (c + d)).2)).toAlgEquiv
          (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              ((stdFuse b (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2)).toAlgEquiv
            (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                (matrixSuperGtensorRight (stdTower b)
                  (stdTower (c + d))
                  (fuseSize c d).1 (fuseSize c d).2)).toAlgEquiv
              ((gtensorAssoc (stdTower a) (stdTower b)
                  ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                    (fuseSize c d).2)).toAlgEquiv w'))))
      = (matrixSuperComp ((stdTower a).gtensor
            (stdTower (b + (c + d))))
            (fuseSize c d).1 (fuseSize c d).2
            (fuseSize b (c + d)).1 (fuseSize b (c + d)).2).toAlgEquiv
        (((matrixSuperGtensorRight (stdTower a)
              (stdTower (b + (c + d)))
              (fuseSize b (c + d)).1
              (fuseSize b (c + d)).2).matrixSuper
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
          ((matrixSuperGtensorRight (stdTower a)
              ((stdTower (b + (c + d))).matrixSuper
                (fuseSize b (c + d)).1 (fuseSize b (c + d)).2)
              (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
            (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                ((stdFuse b (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2)).toAlgEquiv
              (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                  (matrixSuperGtensorRight (stdTower b)
                    (stdTower (c + d))
                    (fuseSize c d).1 (fuseSize c d).2)).toAlgEquiv
                ((gtensorAssoc (stdTower a) (stdTower b)
                    ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                      (fuseSize c d).2)).toAlgEquiv w'))))) :=
    matrixSuperComp_gtensorRight_apply (fuseSize b (c + d)).1
      (fuseSize b (c + d)).2 (fuseSize c d).1 (fuseSize c d).2 _
  rw [hA1]
  -- move the pair fusion past the head-side stabilization
  have hA2 :
      (matrixSuperGtensorRight (stdTower (K := K) a)
          ((stdTower (b + (c + d))).matrixSuper
            (fuseSize b (c + d)).1 (fuseSize b (c + d)).2)
          (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
        (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            ((stdFuse b (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2)).toAlgEquiv
          (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (matrixSuperGtensorRight (stdTower b) (stdTower (c + d))
                (fuseSize c d).1 (fuseSize c d).2)).toAlgEquiv
            ((gtensorAssoc (stdTower a) (stdTower b)
                ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2)).toAlgEquiv w')))
      = (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
            (stdFuse b (c + d))).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv
        ((matrixSuperGtensorRight (stdTower a)
            ((stdTower b).gtensor (stdTower (c + d)))
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
          (((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
              (matrixSuperGtensorRight (stdTower b) (stdTower (c + d))
                (fuseSize c d).1 (fuseSize c d).2)).toAlgEquiv
            ((gtensorAssoc (stdTower a) (stdTower b)
                ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2)).toAlgEquiv w'))) :=
    matrixSuperGtensorRight_full_natural_apply
      (SuperAlgEquiv.refl (stdTower a)) (stdFuse b (c + d))
      (fuseSize c d).1 (fuseSize c d).2 _
  rw [hA2]
  -- the right-slot stabilization hexagon
  have hHexR := matrixSuperGtensorRight_gassoc_right_apply
    (A := stdTower (K := K) a) (B := stdTower b)
    (S := stdTower (c + d)) (fuseSize c d).1 (fuseSize c d).2 w'
  rw [hHexR]
  -- collapse naturality for the pair fusion `stdFuse a (b+(c+d))`
  have hE :
      ((stdFuse a (b + (c + d))).matrixSuper
          ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
          ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)).toAlgEquiv
        ((matrixSuperComp ((stdTower (K := K) a).gtensor
              (stdTower (b + (c + d))))
            (fuseSize c d).1 (fuseSize c d).2
            (fuseSize b (c + d)).1
            (fuseSize b (c + d)).2).toAlgEquiv
          (((matrixSuperGtensorRight (stdTower a)
                (stdTower (b + (c + d)))
                (fuseSize b (c + d)).1
                (fuseSize b (c + d)).2).matrixSuper
              (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
            ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                  (stdFuse b (c + d))).matrixSuper
                (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
              (((gtensorAssoc (stdTower a) (stdTower b)
                    (stdTower (c + d))).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
                ((matrixSuperGtensorRight
                    ((stdTower a).gtensor (stdTower b))
                    (stdTower (c + d)) (fuseSize c d).1
                    (fuseSize c d).2).toAlgEquiv w')))))
      = (matrixSuperComp ((stdTower (K := K)
            (a + (b + (c + d)))).matrixSuper
            (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2)
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize b (c + d)).1 (fuseSize b (c + d)).2).toAlgEquiv
        ((((stdFuse a (b + (c + d))).matrixSuper
              (fuseSize b (c + d)).1
              (fuseSize b (c + d)).2).matrixSuper
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
          (((matrixSuperGtensorRight (stdTower a)
                (stdTower (b + (c + d)))
                (fuseSize b (c + d)).1
                (fuseSize b (c + d)).2).matrixSuper
              (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
            ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                  (stdFuse b (c + d))).matrixSuper
                (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
              (((gtensorAssoc (stdTower a) (stdTower b)
                    (stdTower (c + d))).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
                ((matrixSuperGtensorRight
                    ((stdTower a).gtensor (stdTower b))
                    (stdTower (c + d)) (fuseSize c d).1
                    (fuseSize c d).2).toAlgEquiv w'))))) :=
    (matrixSuperComp_natural_apply (stdFuse a (b + (c + d)))
      (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
      (fuseSize c d).1 (fuseSize c d).2 _).symm
  rw [hE]
  -- unfold the factored tail on the right-hand side
  have hTail5 : ∀ v : (((stdTower (K := K) a).gtensor
        (stdTower b)).gtensor
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2)).carrier,
      (cluster35Tail5 a b c d).toAlgEquiv v
      = (stdMatrixCast (show a + (b + (c + d)) = a + b + c + d by ring)
            (cluster35Size_final a b c d)).toAlgEquiv
          ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + (c + d))))
              (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
              (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
              (fuseSize c d).1 (fuseSize c d).2).symm.toAlgEquiv
            (((stdMatrixCast (cluster35Index_eq a b c d)
                (cluster35Size_eq a b c d)).symm).toAlgEquiv
              ((matrixSuperComp (stdTower (a + b + (c + d)))
                  (fuseSize c d).1 (fuseSize c d).2
                  (sizeL a b (c + d)).1
                  (sizeL a b (c + d)).2).toAlgEquiv
                (((routeR a b (c + d)).matrixSuper (fuseSize c d).1
                      (fuseSize c d).2).toAlgEquiv
                  ((matrixSuperGtensorRight
                      ((stdTower a).gtensor (stdTower b))
                      (stdTower (c + d)) (fuseSize c d).1
                      (fuseSize c d).2).toAlgEquiv v))))) :=
    fun v => rfl
  rw [hTail5]
  -- expand the stabilized right route of the cluster triple
  have hRR : ∀ V : ((((stdTower (K := K) a).gtensor
        (stdTower b)).gtensor (stdTower (c + d))).matrixSuper
        (fuseSize c d).1 (fuseSize c d).2).carrier,
      ((routeR a b (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv V
      = ((stdMatrixCast (add_assoc a b (c + d)).symm
            (sizeR_flat_eq_35 a b c d)).matrixSuper
          (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
        (((matrixSuperComp (stdTower (a + (b + (c + d))))
              (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
              (fuseSize a (b + (c + d))).1
              (fuseSize a (b + (c + d))).2).matrixSuper
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
          ((((stdFuse a (b + (c + d))).matrixSuper
                (fuseSize b (c + d)).1
                (fuseSize b (c + d)).2).matrixSuper
              (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
            (((matrixSuperGtensorRight (stdTower a)
                  (stdTower (b + (c + d)))
                  (fuseSize b (c + d)).1
                  (fuseSize b (c + d)).2).matrixSuper
                (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
              ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                    (stdFuse b (c + d))).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
                (((gtensorAssoc (stdTower a) (stdTower b)
                      (stdTower (c + d))).matrixSuper
                    (fuseSize c d).1
                    (fuseSize c d).2).toAlgEquiv V))))) :=
    fun V => rfl
  rw [hRR]
  -- slide the right route's built-in cast out of the collapse
  rw [stdMatrixCast_matrixSuperComp_apply (K := K)
    (add_assoc a b (c + d)).symm (sizeR_flat_eq_35 a b c d)
    (fuseSize c d).1 (fuseSize c d).2]
  have hcanc : ∀ X : ((stdTower (K := K)
        (a + (b + (c + d)))).matrixSuper
        ((fuseSize c d).1 * ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
          + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2)
          + (fuseSize c d).2 * ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
          + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1))
        ((fuseSize c d).1 * ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
          + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1)
          + (fuseSize c d).2 * ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
          + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2))).carrier,
      ((stdMatrixCast (K := K) (cluster35Index_eq a b c d)
          (cluster35Size_eq a b c d)).symm).toAlgEquiv
        ((stdMatrixCast (cluster35Index_eq a b c d)
          (cluster35Size_eq a b c d)).toAlgEquiv X) = X := fun X =>
    AlgEquiv.symm_apply_apply _ X
  rw [hcanc]
  -- reassociate the three-layer collapse
  have hAssoc :
      (matrixSuperComp (stdTower (K := K) (a + (b + (c + d))))
          (fuseSize c d).1 (fuseSize c d).2
          ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
          + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2)
          ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
          + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1)).toAlgEquiv
        (((matrixSuperComp (stdTower (a + (b + (c + d))))
              (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
              (fuseSize a (b + (c + d))).1
              (fuseSize a (b + (c + d))).2).matrixSuper
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
          ((((stdFuse a (b + (c + d))).matrixSuper
                (fuseSize b (c + d)).1
                (fuseSize b (c + d)).2).matrixSuper
              (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
            (((matrixSuperGtensorRight (stdTower a)
                  (stdTower (b + (c + d)))
                  (fuseSize b (c + d)).1
                  (fuseSize b (c + d)).2).matrixSuper
                (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
              ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                    (stdFuse b (c + d))).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
                (((gtensorAssoc (stdTower a) (stdTower b)
                      (stdTower (c + d))).matrixSuper
                    (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
                  ((matrixSuperGtensorRight
                      ((stdTower a).gtensor (stdTower b))
                      (stdTower (c + d)) (fuseSize c d).1
                      (fuseSize c d).2).toAlgEquiv w'))))))
      = (matrixSuperCompAssoc (stdTower (K := K) (a + (b + (c + d))))
          (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
          (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
          (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
        ((matrixSuperComp (stdTower (K := K) (a + (b + (c + d))))
            ((fuseSize c d).1 * (fuseSize b (c + d)).1
          + (fuseSize c d).2 * (fuseSize b (c + d)).2)
            ((fuseSize c d).1 * (fuseSize b (c + d)).2
          + (fuseSize c d).2 * (fuseSize b (c + d)).1)
            (fuseSize a (b + (c + d))).1
            (fuseSize a (b + (c + d))).2).toAlgEquiv
          ((matrixSuperComp ((stdTower (K := K)
                (a + (b + (c + d)))).matrixSuper
                (fuseSize a (b + (c + d))).1
                (fuseSize a (b + (c + d))).2)
              (fuseSize c d).1 (fuseSize c d).2
              (fuseSize b (c + d)).1
              (fuseSize b (c + d)).2).toAlgEquiv
            ((((stdFuse a (b + (c + d))).matrixSuper
                  (fuseSize b (c + d)).1
                  (fuseSize b (c + d)).2).matrixSuper
                (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
              (((matrixSuperGtensorRight (stdTower a)
                    (stdTower (b + (c + d)))
                    (fuseSize b (c + d)).1
                    (fuseSize b (c + d)).2).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
                ((((SuperAlgEquiv.refl (stdTower a)).gtensorCongr
                      (stdFuse b (c + d))).matrixSuper
                    (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
                  (((gtensorAssoc (stdTower a) (stdTower b)
                        (stdTower (c + d))).matrixSuper
                      (fuseSize c d).1
                      (fuseSize c d).2).toAlgEquiv
                    ((matrixSuperGtensorRight
                        ((stdTower a).gtensor (stdTower b))
                        (stdTower (c + d)) (fuseSize c d).1
                        (fuseSize c d).2).toAlgEquiv w'))))))) :=
    matrixSuperComp_assoc_apply (fuseSize a (b + (c + d))).1
      (fuseSize a (b + (c + d))).2 (fuseSize b (c + d)).1
      (fuseSize b (c + d)).2 (fuseSize c d).1 (fuseSize c d).2 _
  rw [hAssoc]
  have hcancA : ∀ X, ((matrixSuperCompAssoc
        (stdTower (K := K) (a + (b + (c + d))))
        (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
        (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
        (fuseSize c d).1 (fuseSize c d).2).symm).toAlgEquiv
      ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + (c + d))))
        (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
        (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
        (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv X) = X :=
    fun X => AlgEquiv.symm_apply_apply _ X
  rw [hcancA]
  rfl

end Factor35

end Superfusion

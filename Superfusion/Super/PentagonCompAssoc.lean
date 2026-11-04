/-
Superfusion / Super / PentagonCompAssoc

Milestone M7d-5b-4-iii(b), part 9: **associativity of the matrix
size collapse** — the missing coherence discovered in the
factorization round.  Collapsing three nested matrix layers in the
two possible groupings agrees, both giving `M_{N|M}(P)` for the same
pair `(N, M)` of sizes (`compSize_assoc₁`, `compSize_assoc₂`, pure
`ring`-level identities).

**Caveat discovered in this round**: the two groupings do *not* agree
via the naive index identity (`Fin.cast` along the size identity, i.e.
a bare `matrixSuperCast`) — `collapseIndexEquiv` sorts each collapsed
layer by *total parity*, and iterating this sort in the two different
association orders produces two different (though equinumerous, in
each parity class) enumerations of the same finite set of matrix
units. This was checked directly: `decide` refutes the naive
`Fin.cast`-only statement already at the smallest nontrivial instance
(`p=2,q=1,p'=q'=p''=q''=1`).

The mathematically honest bridging equivalence is instead built
*compositionally* from the same `matrixSuperComp` / `.matrixSuper`
pieces used on both sides (`matrixSuperCompAssoc`), i.e. literally
`grouping1⁻¹ ∘ grouping1` unfolded through `grouping2`'s pieces; the
applied coherence `matrixSuperComp_assoc_apply` then follows from pure
`AlgEquiv`/`SuperAlgEquiv` composition laws (`trans`, `symm`,
`apply_symm_apply`), no combinatorics needed. Reusable in the
factorizations of all three cluster edges and in the quintuple
coherence (5c).
-/
import Superfusion.Super.PentagonCoherence

namespace Superfusion

section CompAssoc

universe u

variable {K : Type u} [CommRing K]

/-- The two total sizes agree (documentation / available for callers
that need the raw `ring` fact). -/
theorem compSize_assoc₁ (p q p' q' p'' q'' : ℕ) :
    p'' * (p' * p + q' * q) + q'' * (p' * q + q' * p)
      = (p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q := by
  ring

theorem compSize_assoc₂ (p q p' q' p'' q'' : ℕ) :
    p'' * (p' * q + q' * p) + q'' * (p' * p + q' * q)
      = (p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p := by
  ring

/-- **Associativity of the matrix size collapse**, as a bridging
equivalence built from the collapse pieces themselves: the composite
`(collapse the outer two first, then the inner)⁻¹ ∘
(collapse the inner two first, then the outer)`, which by
construction transports one triple-collapse into the other. -/
noncomputable def matrixSuperCompAssoc (P : SuperAlgebra K)
    (p q p' q' p'' q'' : ℕ) :
    SuperAlgEquiv
      (P.matrixSuper ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
        ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p))
      (P.matrixSuper (p'' * (p' * p + q' * q) + q'' * (p' * q + q' * p))
        (p'' * (p' * q + q' * p) + q'' * (p' * p + q' * q))) :=
  (matrixSuperComp P (p'' * p' + q'' * q') (p'' * q' + q'' * p') p q).symm.trans
    (((matrixSuperComp (P.matrixSuper p q) p'' q'' p' q').symm.trans
        ((matrixSuperComp P p' q' p q).matrixSuper p'' q'')).trans
      (matrixSuperComp P p'' q'' (p' * p + q' * q) (p' * q + q' * p)))

private theorem SuperAlgEquiv_symm_toAlgEquiv {P Q : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) :
    e.symm.toAlgEquiv = e.toAlgEquiv.symm := rfl

private theorem SuperAlgEquiv_trans_toAlgEquiv {P Q R : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) (f : SuperAlgEquiv Q R) :
    (e.trans f).toAlgEquiv = e.toAlgEquiv.trans f.toAlgEquiv := rfl

/-- **Associativity of the matrix size collapse**, applied form:
collapsing the inner two layers first and then the outer agrees with
collapsing the outer two layers first and then the inner, up to the
bridging equivalence `matrixSuperCompAssoc`. -/
theorem matrixSuperComp_assoc_apply {P : SuperAlgebra K}
    (p q p' q' p'' q'' : ℕ)
    (M : (((P.matrixSuper p q).matrixSuper p' q').matrixSuper
      p'' q'').carrier) :
    (matrixSuperComp P p'' q'' (p' * p + q' * q)
        (p' * q + q' * p)).toAlgEquiv
        (((matrixSuperComp P p' q' p q).matrixSuper
          p'' q'').toAlgEquiv M)
      = (matrixSuperCompAssoc P p q p' q' p'' q'').toAlgEquiv
        ((matrixSuperComp P (p'' * p' + q'' * q')
            (p'' * q' + q'' * p') p q).toAlgEquiv
          ((matrixSuperComp (P.matrixSuper p q) p'' q''
            p' q').toAlgEquiv M)) := by
  show _ = (matrixSuperCompAssoc P p q p' q' p'' q'').toAlgEquiv _
  rw [matrixSuperCompAssoc, SuperAlgEquiv_trans_toAlgEquiv, SuperAlgEquiv_trans_toAlgEquiv,
    SuperAlgEquiv_trans_toAlgEquiv, SuperAlgEquiv_symm_toAlgEquiv, SuperAlgEquiv_symm_toAlgEquiv,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

end CompAssoc

end Superfusion

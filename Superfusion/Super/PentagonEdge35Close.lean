/-
Superfusion / Super / PentagonEdge35Close

Milestone M7d-5b-4-iii(c), part 7: **the closing theorems of the e35
edge** — the signed factorization `quadRoute3_factor35_signed` and
the edge intertwining `edgeT35_intertwines`, assembled from the
landed bifusion reduction (`tail3_prefix_eq`, `quadRoute3_prefix_eq`),
the landed entry-formula layer (`PentagonEdge35Core.lean`), and the
decode-relation lemmas for the two shared tails.
-/
import Superfusion.Super.PentagonEdge35Core

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

/-! ### Stage A: decode-relation lemmas -/

section DecodeA

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- Local copy of the cast of a flat `p|q`-index along an equality of
size pairs (private in `PentagonEdge35Core.lean`; recopied
verbatim). -/
private def sumFinCast {s t : ℕ × ℕ} (h : s = t) :
    Fin s.1 ⊕ Fin s.2 → Fin t.1 ⊕ Fin t.2 :=
  Sum.map (Fin.cast (congrArg Prod.fst h))
    (Fin.cast (congrArg Prod.snd h))

/-- Local copy of the composite index bijection of the inverse
collapse-reassociation bridge (private in `PentagonEdge24.lean` /
`PentagonEdge35Core.lean`; recopied verbatim — definitionally equal to
the landed ones, so `matrixSuperCompAssoc_symm_entryC` rewrites
transparently against it). -/
private def assocIdxCC (p q p' q' p'' q'' : ℕ)
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
/-- Local copy of `matrixSuperComp`'s entry formula: a pure reindexing
along the collapse bijection (mirrors `matrixSuperCompAssoc_symm_entryC`
of `PentagonEdge35Core.lean`). -/
private theorem matrixSuperComp_entryC {P : SuperAlgebra K}
    (p' q' p q : ℕ) (M : ((P.matrixSuper p q).matrixSuper p' q').carrier)
    (I J : Fin (p' * p + q' * q) ⊕ Fin (p' * q + q' * p)) :
    (matrixSuperComp P p' q' p q).toAlgEquiv M I J
      = M ((collapseIndexEquiv p' q' p q).symm I).1
          ((collapseIndexEquiv p' q' p q).symm J).1
          ((collapseIndexEquiv p' q' p q).symm I).2
          ((collapseIndexEquiv p' q' p q).symm J).2 := rfl

omit [Invertible (2 : K)] in
/-- Transport along `stdTower`-index equalities composes: two nested
`▸`s along `x = y` then `y = z` collapse to one `▸` along `x = z`
(any two proofs of the same `ZMod 8` equation give the same
transport, by `subst`). -/
theorem stdTower_cast_trans {x y z : ZMod 8} (h1 : x = y) (h2 : y = z)
    (v : (stdTower (K := K) x).carrier) :
    h2 ▸ (h1 ▸ v : (stdTower (K := K) y).carrier)
      = ((h1.trans h2) ▸ v : (stdTower (K := K) z).carrier) := by
  subst h1; subst h2; rfl

omit [Invertible (2 : K)] in
/-- Entry formula for the inverse of a `stdMatrixCast`: by `subst`,
`(stdMatrixCast h hs).symm` reduces to `SuperAlgEquiv.refl`, so the
inverse reindexes along `sumFinCast hs` (the forward direction of the
cast used in `stdMatrixCast_entry`). -/
theorem stdMatrixCast_symm_entry {x y : ZMod 8} (h : x = y) {s t : ℕ × ℕ}
    (hs : s = t) (M : ((stdTower (K := K) y).matrixSuper t.1 t.2).carrier)
    (i j : Fin s.1 ⊕ Fin s.2) :
    (stdMatrixCast h hs).symm.toAlgEquiv M i j
      = (h ▸ (M (sumFinCast hs i) (sumFinCast hs j)) :
        (stdTower (K := K) x).carrier) := by
  subst h
  subst hs
  show M i j = M (sumFinCast rfl i) (sumFinCast rfl j)
  have hi : sumFinCast (rfl : s = s) i = i := by
    rcases i with i | i <;> simp [sumFinCast]
  have hj : sumFinCast (rfl : s = s) j = j := by
    rcases j with j | j <;> simp [sumFinCast]
  rw [hi, hj]

/-- The "clean" pair-decode of a flat `assocIdxCC`-frame index into the
outer-layer index and the re-collapsed `(inner two layers)` index —
the composite that survives after the redundant collapse/decollapse
pair inside `matrixSuperComp_entryC ∘ matrixSuperCompAssoc_symm_entryC`
cancels via `Equiv.symm_apply_apply`.  Matches `swapIdxGen`'s
`(It.1, collapse τ ρ (It.2, zr.2))` naming with `p=ρ,q'=τ,p''=σ` (the
`(ab)`-cluster tail: outer layer `σ`, inner collapsed layer `τρ`). -/
private def cleanDecL (p q p' q' p'' q'' : ℕ)
    (I : Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
      ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p)) :
    (Fin p'' ⊕ Fin q'') × (Fin (p' * p + q' * q) ⊕ Fin (p' * q + q' * p)) :=
  let zr := (collapseIndexEquiv (p'' * p' + q'' * q')
      (p'' * q' + q'' * p') p q).symm I
  let It := (collapseIndexEquiv p'' q'' p' q').symm zr.1
  (It.1, collapseIndexEquiv p' q' p q (It.2, zr.2))

/-- **The redundant collapse/decollapse cancellation**: the composite
decode of `cluster13SharedTail`'s two legs (`matrixSuperComp` then
`matrixSuperCompAssoc.symm`, entrywise via `matrixSuperComp_entryC`
and `matrixSuperCompAssoc_symm_entryC`) is exactly `cleanDecL`, by
`Equiv.symm_apply_apply` cancelling the reindex/collapse round trip
baked into `assocIdxCC`. -/
private theorem decL_eq_clean (p q p' q' p'' q'' : ℕ)
    (I : Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
      ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p)) :
    (collapseIndexEquiv p'' q''
        (p' * p + q' * q) (p' * q + q' * p)).symm
      (assocIdxCC p q p' q' p'' q'' I)
      = cleanDecL p q p' q' p'' q'' I := by
  show (collapseIndexEquiv p'' q'' (p' * p + q' * q)
      (p' * q + q' * p)).symm
      (collapseIndexEquiv p'' q'' (p' * p + q' * q) (p' * q + q' * p)
        (((collapseIndexEquiv p'' q'' p' q').symm
            (((collapseIndexEquiv (p'' * p' + q'' * q')
              (p'' * q' + q'' * p') p q).symm I).1)).1,
          collapseIndexEquiv p' q' p q
            ((((collapseIndexEquiv p'' q'' p' q').symm
                (((collapseIndexEquiv (p'' * p' + q'' * q')
                  (p'' * q' + q'' * p') p q).symm I).1)).2),
              ((collapseIndexEquiv (p'' * p' + q'' * q')
                (p'' * q' + q'' * p') p q).symm I).2)))
    = cleanDecL p q p' q' p'' q'' I
  rw [Equiv.symm_apply_apply]
  rfl

omit [Invertible (2 : K)] in
/-- **The `(ab)`-cluster shared-tail entry formula**: `cluster13SharedTail`
applied entrywise decodes through `cleanDecL` — the outer `σ`-layer
index and the re-collapsed `τρ`-layer index, exactly the `(It, zr)`
pair consumed by `swapIdxGen`'s `Kn`-leg. -/
private theorem cluster13SharedTail_entry (a b c d : ZMod 8)
    (V : (((stdTower (K := K) (a + b + c + d)).matrixSuper
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).carrier)
    (i j : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    (cluster13SharedTail a b c d).toAlgEquiv V i j
      = V (cleanDecL (fuseSize (a + b + c) d).1
            (fuseSize (a + b + c) d).2
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
            (fuseSize a b).1 (fuseSize a b).2 i).1
          (cleanDecL (fuseSize (a + b + c) d).1
            (fuseSize (a + b + c) d).2
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
            (fuseSize a b).1 (fuseSize a b).2 j).1
          (cleanDecL (fuseSize (a + b + c) d).1
            (fuseSize (a + b + c) d).2
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
            (fuseSize a b).1 (fuseSize a b).2 i).2
          (cleanDecL (fuseSize (a + b + c) d).1
            (fuseSize (a + b + c) d).2
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
            (fuseSize a b).1 (fuseSize a b).2 j).2 := by
  show V (((collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).symm
      (assocIdxCC (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 i))).1
      (((collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).symm
      (assocIdxCC (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 j))).1
      (((collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).symm
      (assocIdxCC (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 i))).2
      (((collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).symm
      (assocIdxCC (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 j))).2
    = V (cleanDecL (fuseSize (a + b + c) d).1
          (fuseSize (a + b + c) d).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize a b).1 (fuseSize a b).2 i).1
        (cleanDecL (fuseSize (a + b + c) d).1
          (fuseSize (a + b + c) d).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize a b).1 (fuseSize a b).2 j).1
        (cleanDecL (fuseSize (a + b + c) d).1
          (fuseSize (a + b + c) d).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize a b).1 (fuseSize a b).2 i).2
        (cleanDecL (fuseSize (a + b + c) d).1
          (fuseSize (a + b + c) d).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize a b).1 (fuseSize a b).2 j).2
  rw [show ((collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).symm
      (assocIdxCC (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 i))
      = cleanDecL (fuseSize (a + b + c) d).1
          (fuseSize (a + b + c) d).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize a b).1 (fuseSize a b).2 i from
      decL_eq_clean (fuseSize (a + b + c) d).1
        (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 i,
    show ((collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).symm
      (assocIdxCC (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 j))
      = cleanDecL (fuseSize (a + b + c) d).1
          (fuseSize (a + b + c) d).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize a b).1 (fuseSize a b).2 j from
      decL_eq_clean (fuseSize (a + b + c) d).1
        (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2 j]

/-- Local copy of the index identity for the inner cast of the
`(cd)`-cluster shared tail (private in `PentagonFactor35.lean`). -/
private theorem cluster35Index_eqC (a b c d : ZMod 8) :
    a + (b + (c + d)) = a + b + (c + d) :=
  (add_assoc a b (c + d)).symm

/-- Local copy of the composed size of the right route of
`(a, b, c+d)`, flat-spelled (private in `PentagonFactor35.lean`). -/
private theorem sizeR_flat_eq_35C (a b c d : ZMod 8) :
    ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2,
      (fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
        + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1)
      = sizeL a b (c + d) :=
  (sizeL_eq_sizeR a b (c + d)).symm

/-- Local copy of the size identity for the inner cast of the
`(cd)`-cluster shared tail. -/
private theorem cluster35Size_eqC (a b c d : ZMod 8) :
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
  rw [← sizeR_flat_eq_35C a b c d]

/-- Local copy of the size identity for the final cast of the
`(cd)`-cluster shared tail. -/
private theorem cluster35Size_finalC (a b c d : ZMod 8) :
    preSize (sizeR b c d) a (b + (c + d))
      = extSize (sizeL a b c) (a + b + c) d := by
  rw [← sizeL_eq_sizeR b c d, ← add_assoc b c d, ← quadSize_eq]

/-- The composite decode of `cluster35SharedTail`'s three re-indexing
legs (`matrixSuperCompAssoc.symm`'s `assocIdxCC`, sandwiched between
the two `sumFinCast`s of the flat-frame `stdMatrixCast`s), landing at
the flat index consumed by `matrixSuperComp_entryC`'s final collapse
decode. -/
private def cleanDec35 (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    Fin ((fuseSize c d).1 * (sizeL a b (c + d)).1
        + (fuseSize c d).2 * (sizeL a b (c + d)).2)
      ⊕ Fin ((fuseSize c d).1 * (sizeL a b (c + d)).2
        + (fuseSize c d).2 * (sizeL a b (c + d)).1) :=
  sumFinCast (cluster35Size_eqC a b c d)
    (assocIdxCC (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
      (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
      (fuseSize c d).1 (fuseSize c d).2
      (sumFinCast (cluster35Size_finalC a b c d).symm i))

omit [Invertible (2 : K)] in
/-- **The `(cd)`-cluster shared-tail entry formula**: `cluster35SharedTail`
applied entrywise decodes through `matrixSuperComp`'s collapse of
`cleanDec35`'s flat index, transported along the frame identity
`a+(b+(c+d)) = a+b+c+d`. -/
private theorem cluster35SharedTail_entry (a b c d : ZMod 8)
    (V : (((stdTower (K := K) (a + b + (c + d))).matrixSuper
        (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).matrixSuper
        (fuseSize c d).1 (fuseSize c d).2).carrier)
    (i j : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    (cluster35SharedTail a b c d).toAlgEquiv V i j
      = (show a + b + (c + d) = a + b + c + d by ring) ▸
        (V ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
            (cleanDec35 a b c d i)).1
          ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
            (cleanDec35 a b c d j)).1
          ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
            (cleanDec35 a b c d i)).2
          ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
            (cleanDec35 a b c d j)).2) := by
  show (stdMatrixCast (show a + (b + (c + d)) = a + b + c + d by ring)
      (cluster35Size_finalC a b c d)).toAlgEquiv
      ((matrixSuperCompAssoc (stdTower (K := K) (a + (b + (c + d))))
          (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
          (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
          (fuseSize c d).1 (fuseSize c d).2).symm.toAlgEquiv
        ((stdMatrixCast (cluster35Index_eqC a b c d)
              (cluster35Size_eqC a b c d)).symm.toAlgEquiv
          ((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
              (fuseSize c d).1 (fuseSize c d).2
              (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).toAlgEquiv V)))
      i j
    = _
  rw [stdMatrixCast_entry, matrixSuperCompAssoc_symm_entryC,
    stdMatrixCast_symm_entry, matrixSuperComp_entryC, stdTower_cast_trans]
  rfl

end DecodeA

section Close

universe u

/-! ### Local copies of the swap-index machinery (verbatim, `rfl`-defeq
to the landed private ones in `PentagonEdge35.lean` /
`PentagonEdge35Core.lean`) -/

/-- The generic layer-swap index map (local copy). -/
private def swapIdxGenC (s g k t r m n : ℕ × ℕ)
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

/-- The Koszul sign exponent of the layer swap (local copy). -/
private def swapParityGenC (s g k t r : ℕ × ℕ)
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

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The flat-spelled size identity of the cluster route cast (local
copy of the private helper of `PentagonEdge35Signed.lean` /
`PentagonEdge35Core.lean`). -/
private theorem castR_clC (a b c d : ZMod 8) :
    ((fuseSize c d).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize c d).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).1)
      = sizeL (a + b) c d :=
  (sizeL_eq_sizeR (a + b) c d).symm

/-- The `(σ,τ,ρ)`-to-`(γ,κ)` cast identity, flat-spelled (local copy).
-/
private theorem swapCast_clC (a b c d : ZMod 8) :
    ((fuseSize (a + b) c).1 * (fuseSize (a + b + c) d).1
        + (fuseSize (a + b) c).2 * (fuseSize (a + b + c) d).2,
      (fuseSize (a + b) c).1 * (fuseSize (a + b + c) d).2
        + (fuseSize (a + b) c).2 * (fuseSize (a + b + c) d).1)
      = ((fuseSize c d).1 * (fuseSize (a + b) (c + d)).1
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).2,
      (fuseSize c d).1 * (fuseSize (a + b) (c + d)).2
        + (fuseSize c d).2 * (fuseSize (a + b) (c + d)).1) :=
  sizeL_eq_sizeR (a + b) c d

/-- The `(σ,κ)`-to-`(μ,ν′)` cast identity, flat-spelled (local copy).
-/
private theorem swapCast_35C (a b c d : ZMod 8) :
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
(local copy; a 4096-case kernel `decide`, matching the landed one). -/
private theorem swapCast_outC : ∀ a b c d : ZMod 8,
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

/-- The layer-swap index involution at the pentagon frame (local
copy, `rfl`-defeq to the landed private `swapIdx35`). -/
private def swapIdx35C (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2 :=
  swapIdxGenC (fuseSize a b) (fuseSize c d) (fuseSize (a + b) (c + d))
    (fuseSize (a + b) c) (fuseSize (a + b + c) d) (fuseSize b (c + d))
    (fuseSize a (b + (c + d))) (swapCast_clC a b c d)
    (swapCast_35C a b c d) (swapCast_outC a b c d) i

/-- The Koszul sign exponent at the pentagon frame (local copy,
`rfl`-defeq to the landed private `swapParity35`). -/
private def swapParity35C (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) : ZMod 2 :=
  swapParityGenC (fuseSize a b) (fuseSize c d)
    (fuseSize (a + b) (c + d)) (fuseSize (a + b) c)
    (fuseSize (a + b + c) d) (swapCast_clC a b c d) i

/-- The local `swapIdx35C` is an involution — extracted from the
landed `phi_invol` (`exact` unifies `swapIdx35C` with the private
`swapIdx35` by `rfl`, since both unfold to the identical term).
`K` is bound explicitly since the statement of `swapIdx35C`'s
involution property does not itself mention `K`. -/
private theorem phi_involC (K : Type u) [Field K] [Invertible (2 : K)]
    (a b c d : ZMod 8) :
    ∀ i, swapIdx35C a b c d (swapIdx35C a b c d i) = i :=
  phi_invol K a b c d

/-- Sign compatibility of the local involution — extracted from the
landed `eps_phi`. -/
private theorem eps_phiC (K : Type u) [Field K] [Invertible (2 : K)]
    (a b c d : ZMod 8) :
    ∀ i, swapParity35C a b c d (swapIdx35C a b c d i)
      = swapParity35C a b c d i :=
  eps_phi K a b c d

/-- **The swap-parity factorization certificate at the pentagon
frame**: `swapParity35C a b c d i` equals `sumParity (fuseSize a b) A *
sumParity (fuseSize c d) Chat.1`, where `A := cleanDecL (...)
(swapIdx35C a b c d i) .1` and `Chat.1` is the `(cd)`-cluster outer
slot obtained by collapsing `A`'s companion `.2`-slot at the
`swapCast_clC` cast (exactly `CORE`'s own `A`/`Chat` construction).
Proved **algebraically** (no new `decide`): both
`swapParityGenC`-internal `It.1`/`Kn.1`, evaluated at `swapIdx35C i`,
unfold (by `rfl`, matching term-by-term) to `A`/`Chat.1`, so
`swapParity35C (swapIdx35C i) = sumParity A * sumParity Chat.1`
directly from the DEFINITION of `swapParity35C`; combined with the
already-landed involution-compatibility `eps_phiC` (`swapParity35C
(swapIdx35C i) = swapParity35C i`), this identifies `swapParity35C i`
itself. -/
private theorem swapParity35C_factor (K : Type u) [Field K]
    [Invertible (2 : K)] (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    swapParity35C a b c d i
      = sumParity (fuseSize a b).1 (fuseSize a b).2
          (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
            (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).1
        * sumParity (fuseSize c d).1 (fuseSize c d).2
          ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
            (sumFinCast (swapCast_clC a b c d)
              (cleanDecL (fuseSize (a + b + c) d).1
                (fuseSize (a + b + c) d).2
                (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                (fuseSize a b).1 (fuseSize a b).2
                (swapIdx35C a b c d i)).2)).1 := by
  have hunfold : swapParity35C a b c d (swapIdx35C a b c d i)
      = sumParity (fuseSize a b).1 (fuseSize a b).2
          (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
            (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).1
        * sumParity (fuseSize c d).1 (fuseSize c d).2
          ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
            (sumFinCast (swapCast_clC a b c d)
              (cleanDecL (fuseSize (a + b + c) d).1
                (fuseSize (a + b + c) d).2
                (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                (fuseSize a b).1 (fuseSize a b).2
                (swapIdx35C a b c d i)).2)).1 := rfl
  rw [← hunfold]
  exact (eps_phiC K a b c d i).symm

omit [Invertible (2 : K)] in
/-- **Generic scalar-transport-through-application lemma**: if two
`matrixSuper`-of-`matrixSuper` values `V W` satisfy `V = n • m • W` at
the UN-CAST/UN-APPLIED level, then after transporting BOTH along the
SAME proof `h` of an index equality and applying at the SAME row/col
pair, the SCALARS commute out to the FRONT — i.e. `(h ▸ V) r s = n • m
• ((h ▸ W) r s)`.  Proved generically by `subst h` (avoiding the
`instances`-transparency snag that direct `rw [Matrix.smul_apply]` on
a large ambient CORE goal repeatedly tripped in this file — the
snag is sidestepped entirely since this lemma's OWN elaboration never
touches the ambient goal). -/
private theorem castTransportSmul {x y : ZMod 8} (h : x = y) (p q : ℕ) (n m : ℤ)
    (V W : ((stdTower (K := K) x).matrixSuper p q).carrier)
    (hVW : V = n • m • W) (r s : Fin p ⊕ Fin q) :
    (h ▸ V : ((stdTower (K := K) y).matrixSuper p q).carrier) r s
      = n • m • ((h ▸ W : ((stdTower (K := K) y).matrixSuper p q).carrier) r s) := by
  subst h
  subst hVW
  rfl

omit [Invertible (2 : K)] in
/-- Single-scalar variant of `castTransportSmul` (for cases where the
coefficient is already a single combined `ℤ`-scalar `n`, not a
product). -/
private theorem castTransportSmul1 {x y : ZMod 8} (h : x = y) (p q : ℕ) (n : ℤ)
    (V W : ((stdTower (K := K) x).matrixSuper p q).carrier)
    (hVW : V = n • W) (r s : Fin p ⊕ Fin q) :
    (h ▸ V : ((stdTower (K := K) y).matrixSuper p q).carrier) r s
      = n • ((h ▸ W : ((stdTower (K := K) y).matrixSuper p q).carrier) r s) := by
  subst h
  subst hVW
  rfl

omit [Invertible (2 : K)] in
/-- MATRIX-level variant of `castTransportSmul1` (no row/column indices
in the STATEMENT — the conclusion is an equality of MATRICES, not
entries).  This is essential when the target's `hcastAB ▸ (...)` was
built as a matrix-level cast (e.g. via `congrArg (fun x => hcastAB ▸ x)`
on a matrix-typed equality) FIRST, with `Matrix`/entry application
performed AFTERWARD via a SEPARATE `congrFun`/`congrFun` step: unlike
`castTransportSmul1`, whose STATEMENT already applies `r s` to the cast
expression, the `▸`-notation elaborator can choose a DIFFERENT
(entry-level) MOTIVE for `castTransportSmul1`'s OWN cast than for a
matrix-level-then-applied cast, even though both print identically —
this variant sidesteps that mismatch by keeping the cast's motive
matrix-level throughout, matching the `congrArg (fun x => h ▸ x) e`
idiom used to build `hLcast`/`step1`/`step2`. -/
private theorem castTransportSmul1M {x y : ZMod 8} (h : x = y) (p q : ℕ) (n : ℤ)
    (V W : ((stdTower (K := K) x).matrixSuper p q).carrier)
    (hVW : V = n • W) :
    (h ▸ V : ((stdTower (K := K) y).matrixSuper p q).carrier)
      = n • (h ▸ W : ((stdTower (K := K) y).matrixSuper p q).carrier) := by
  subst h
  subst hVW
  rfl

omit [Invertible (2 : K)] in
/-- ENTRY-level (no matrix / row-column indices at all) variant of
`castTransportSmul1`, for when the ambient goal's `h ▸ (...)` cast is
applied to an ALREADY-INDEXED element of `(stdTower y).carrier` (i.e.
the smul AND the row/column application both happened BEFORE the
cast) rather than to a whole matrix that is indexed afterward — this
is a THIRD, genuinely different `▸`-elaboration shape from
`castTransportSmul1`/`castTransportSmul1M`, confirmed via `pp.all`
token-diffing against the ambient goal at the point of use. -/
private theorem castTransportSmul1' {x y : ZMod 8} (h : x = y) (n : ℤ)
    (V W : (stdTower (K := K) x).carrier) (hVW : V = n • W) :
    (h ▸ V : (stdTower (K := K) y).carrier)
      = n • (h ▸ W : (stdTower (K := K) y).carrier) := by
  subst h
  subst hVW
  rfl

omit [Invertible (2 : K)] in
/-- Left multiplication by `swapSign` reindexes rows through the local
`φ` (`swapIdx35C`), picking up the sign at the source row — restated
against the local index/parity copies via the `show`+`swapSign_eq`
cast trick (avoids naming the private `swapSignMC`/`swapIdx35`/
`swapParity35` of `PentagonEdge35Core.lean` directly). -/
private theorem swapSign_mul_applyC (a b c d : ZMod 8)
    (X : ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier)
    (i j : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    (swapSign (K := K) a b c d * X) i j
      = ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ) •
        X (swapIdx35C a b c d i) j := by
  rw [show (swapSign (K := K) a b c d * X) i j
      = (swapSign (K := K) a b c d * X : Matrix _ _ _) i j from rfl,
    swapSign_eq]
  exact swapSign_mul_apply a b c d X i j

/-- Right multiplication by `swapSign` reindexes columns through the
local `φ`, picking up the sign at the target column (mirror of
`swapSign_mul_applyC`). -/
private theorem mul_swapSign_applyC (a b c d : ZMod 8)
    (X : ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier)
    (i j : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    (X * swapSign (K := K) a b c d) i j
      = ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ) •
        X i (swapIdx35C a b c d j) := by
  rw [show (X * swapSign (K := K) a b c d) i j
      = (X * swapSign (K := K) a b c d : Matrix _ _ _) i j from rfl,
    swapSign_eq]
  exact mul_swapSign_apply a b c d X i j

private theorem assocIdxCC_eq_collapse_cleanDecL (p q p' q' p'' q'' : ℕ)
    (I : Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
      ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p)) :
    assocIdxCC p q p' q' p'' q'' I
      = collapseIndexEquiv p'' q'' (p' * p + q' * q) (p' * q + q' * p)
        (cleanDecL p q p' q' p'' q'' I) := rfl

/-- `cleanDecL`, packaged as a genuine `Equiv`: the composite of the
outer `(p''q'',(p'p+q'q))`-collapse, the `(p''q'',p'q'')`-uncollapse of
the first factor, and the re-collapse of the second factor with the
`(p,q)`-block — precisely `cleanDecL`'s three-step decode, so its
`toFun` is `cleanDecL` by `rfl` and its `invFun`/inverse facts are free
`Equiv` lemmas. -/
private def cleanDecLEquiv (p q p' q' p'' q'' : ℕ) :
    (Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
        ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p))
      ≃ (Fin p'' ⊕ Fin q'') × (Fin (p' * p + q' * q) ⊕ Fin (p' * q + q' * p)) :=
  (collapseIndexEquiv (p'' * p' + q'' * q') (p'' * q' + q'' * p') p q).symm.trans
    ((collapseIndexEquiv p'' q'' p' q').symm.prodCongr (Equiv.refl _)
      |>.trans
        (Equiv.prodAssoc _ _ _
          |>.trans
            ((Equiv.refl (Fin p'' ⊕ Fin q'')).prodCongr
              (collapseIndexEquiv p' q' p q))))

private theorem cleanDecLEquiv_apply (p q p' q' p'' q'' : ℕ)
    (I : Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
      ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p)) :
    cleanDecLEquiv p q p' q' p'' q'' I = cleanDecL p q p' q' p'' q'' I := rfl

/-- The encode direction (`cleanDecLEquiv.symm`), spelled out: split
`n` back into its `(p',q')`-block and `(p,q)`-block, collapse the
`(p'',q'')`-index with the `(p',q')`-block, and collapse the result
with the `(p,q)`-block — the exact composite consumed by `swapIdxGen`'s
final two `let`s (`mn` then the output). -/
private theorem cleanDecLEquiv_symm_apply (p q p' q' p'' q'' : ℕ)
    (I : Fin p'' ⊕ Fin q'') (n : Fin (p' * p + q' * q) ⊕ Fin (p' * q + q' * p)) :
    (cleanDecLEquiv p q p' q' p'' q'').symm (I, n)
      = collapseIndexEquiv (p'' * p' + q'' * q') (p'' * q' + q'' * p') p q
        (collapseIndexEquiv p'' q'' p' q' (I, ((collapseIndexEquiv p' q' p q).symm n).1),
          ((collapseIndexEquiv p' q' p q).symm n).2) := rfl

/-- **`swapIdxGenC`'s output, in terms of `cleanDecLEquiv`**: decode `i`
through the `(s,t,r)`-grouping via `cleanDecLEquiv`, transport the
inner `τρ`-part to a `γκ`-index (the `hcl`-cast), take its `γ`-part
together with the `σ`-part to make an `sκ`-index (the `h35`-cast), and
re-encode through the `(g,m,n)`-grouping via `cleanDecLEquiv.symm` —
matching `swapIdxGen`'s five-step index computation term-by-term. -/
private theorem swapIdxGenC_eq_cleanDecLEquiv (s g k t r m n : ℕ × ℕ)
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
    swapIdxGenC s g k t r m n hcl h35 hout i
      = sumFinCast hout
        ((cleanDecLEquiv n.1 n.2 m.1 m.2 g.1 g.2).symm
          (((collapseIndexEquiv g.1 g.2 k.1 k.2).symm
              (sumFinCast hcl (cleanDecLEquiv r.1 r.2 t.1 t.2 s.1 s.2 i).2)).1,
            sumFinCast h35
              (collapseIndexEquiv s.1 s.2 k.1 k.2
                ((cleanDecLEquiv r.1 r.2 t.1 t.2 s.1 s.2 i).1,
                  ((collapseIndexEquiv g.1 g.2 k.1 k.2).symm
                    (sumFinCast hcl
                      (cleanDecLEquiv r.1 r.2 t.1 t.2 s.1 s.2 i).2)).2)))) := rfl

/-- **`cleanDec35`, in terms of `cleanDecLEquiv`**: the `(γ,μ,ν′)`-decode
of `cleanDec35` (via `assocIdxCC`) is exactly the outer `γ`-collapse of
`cleanDecLEquiv`'s decode of the size/index-cast input — matching
`swapIdxGenC_eq_cleanDecLEquiv`'s output shape after unwinding the
outer `sumFinCast (cluster35Size_eqC ..)`. -/
private theorem cleanDec35_eq_cleanDecLEquiv (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    cleanDec35 a b c d i
      = sumFinCast (cluster35Size_eqC a b c d)
        (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
          ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
              + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2)
          ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
              + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1)
          (cleanDecLEquiv (fuseSize a (b + (c + d))).1
            (fuseSize a (b + (c + d))).2
            (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
            (fuseSize c d).1 (fuseSize c d).2
            (sumFinCast (cluster35Size_finalC a b c d).symm i))) := rfl

/-- `sumFinCast` round-trips: casting along `h` then along `h.symm`
recovers the original value. -/
private theorem sumFinCast_symm_apply {s t : ℕ × ℕ} (h : s = t)
    (x : Fin s.1 ⊕ Fin s.2) : sumFinCast h.symm (sumFinCast h x) = x := by
  subst h
  rcases x with x | x <;> simp [sumFinCast]

/-- **`sumFinCast` composes**: casting along `h1 : s = t` then along
`h2 : t = u` equals casting once along the composed proof `h1.trans h2`
(any two proofs of `s = u` give the same cast, by proof irrelevance —
this is the generic form of the `swapCast_35C`/`sizeR_flat_eq_35C`
round-trip cancellation needed to identify `CORE`'s `Ê`/`F̂` indices
with `A`/`B` directly). -/
private theorem sumFinCast_trans {s t u : ℕ × ℕ} (h1 : s = t) (h2 : t = u)
    (x : Fin s.1 ⊕ Fin s.2) :
    sumFinCast h2 (sumFinCast h1 x) = sumFinCast (h1.trans h2) x := by
  subst h1; subst h2
  rcases x with x | x <;> simp [sumFinCast]

/-- **`sumFinCast` along a proof of `s = s` is the identity** (proof
irrelevance: any proof of `s = s` equals `rfl`). -/
private theorem sumFinCast_rfl_eq_id {s : ℕ × ℕ} (h : s = s)
    (x : Fin s.1 ⊕ Fin s.2) : sumFinCast h x = x := by
  rw [show h = rfl from Subsingleton.elim _ _]
  rcases x with x | x <;> simp [sumFinCast]

/-- **`collapseIndexEquiv` commutes with an inner-size `sumFinCast`
round trip**: collapsing at the old inner size `s`, casting the flat
result along the induced product-cast `hpq` (built from `hs : s = t`
by scaling by `(p, q)`), then un-collapsing at the new inner size `t`,
recovers the direct collapse of `(x.1, sumFinCast hs x.2)`.  The
generic form of the cancellation baked into `phi_encode`/`decR_phi`,
extracted so the final flat-index alignment of `CORE`'s two shared-tail
decodes can be closed without re-deriving the cancellation by hand. -/
private theorem collapseIndexEquiv_symm_sumFinCast_collapse (p q : ℕ)
    {s t : ℕ × ℕ} (hs : s = t)
    (hpq : (p * s.1 + q * s.2, p * s.2 + q * s.1)
      = (p * t.1 + q * t.2, p * t.2 + q * t.1))
    (x : (Fin p ⊕ Fin q) × (Fin s.1 ⊕ Fin s.2)) :
    (collapseIndexEquiv p q t.1 t.2).symm
        (sumFinCast hpq (collapseIndexEquiv p q s.1 s.2 x))
      = (x.1, sumFinCast hs x.2) := by
  subst hs
  simp [sumFinCast]

/-- **Double-cast form of `collapseIndexEquiv_symm_sumFinCast_collapse`**:
un-collapsing after TWO successive `sumFinCast`s of the inner size (used
in `CORE`'s `hM`/`hN` to relate the RHS's `A`-slot to the LHS's own
inner-collapse index `Ê`, which passes through both `swapCast_35C` and
`sizeR_flat_eq_35C`) still just replaces the inner component. -/
private theorem collapseIndexEquiv_symm_sumFinCast2_collapse (p q : ℕ)
    {s t u : ℕ × ℕ} (hs : s = t) (ht : t = u)
    (hpq : (p * s.1 + q * s.2, p * s.2 + q * s.1)
      = (p * t.1 + q * t.2, p * t.2 + q * t.1))
    (hpq' : (p * t.1 + q * t.2, p * t.2 + q * t.1)
      = (p * u.1 + q * u.2, p * u.2 + q * u.1))
    (x : (Fin p ⊕ Fin q) × (Fin s.1 ⊕ Fin s.2)) :
    (collapseIndexEquiv p q u.1 u.2).symm
        (sumFinCast hpq' (sumFinCast hpq (collapseIndexEquiv p q s.1 s.2 x)))
      = (x.1, sumFinCast (hs.trans ht) x.2) := by
  subst hs
  subst ht
  simp [sumFinCast]

/-- **`swapCast_outC` and `cluster35Size_finalC` are proofs of the same
equation** (both unfold, after `preSize`/`sizeR`, to the identical flat
`ℕ × ℕ` equality `(γμ)ν′ = extSize (sizeL a b c) (a+b+c) d`); hence by
proof irrelevance the two casts coincide. -/
private theorem swapCast_outC_eq_cluster35Size_finalC (a b c d : ZMod 8) :
    swapCast_outC a b c d = cluster35Size_finalC a b c d := rfl

/-- **`phi_encode`**: decoding `cleanDec35`'s frame at `φ(i)` recovers
exactly the `(γ,κ,μν′)`-recombination of `cleanDecL`'s decode of `i`
at the `(σ,τ,ρ)`-grouping — the key structural fact making `φ` the
honest realignment of the two shared-tail groupings. Proved by
unfolding `swapIdx35C` via `swapIdxGenC_eq_cleanDecLEquiv`, cancelling
the `sumFinCast`/`cleanDecLEquiv.symm` round trips by the generic
`Equiv`/cast lemmas, and using `swapCast_outC_eq_cluster35Size_finalC`
to identify the two final casts. -/
private theorem phi_encode (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    cleanDecLEquiv (fuseSize a (b + (c + d))).1 (fuseSize a (b + (c + d))).2
        (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
        (fuseSize c d).1 (fuseSize c d).2
        (sumFinCast (cluster35Size_finalC a b c d).symm
          (swapIdx35C a b c d i))
      = (((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (swapCast_clC a b c d)
            (cleanDecLEquiv (fuseSize (a + b + c) d).1
              (fuseSize (a + b + c) d).2
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
              (fuseSize a b).1 (fuseSize a b).2 i).2)).1,
        sumFinCast (swapCast_35C a b c d)
          (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
            ((cleanDecLEquiv (fuseSize (a + b + c) d).1
                (fuseSize (a + b + c) d).2
                (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                (fuseSize a b).1 (fuseSize a b).2 i).1,
              ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                  (fuseSize (a + b) (c + d)).1
                  (fuseSize (a + b) (c + d)).2).symm
                (sumFinCast (swapCast_clC a b c d)
                  (cleanDecLEquiv (fuseSize (a + b + c) d).1
                    (fuseSize (a + b + c) d).2
                    (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                    (fuseSize a b).1 (fuseSize a b).2 i).2)).2))) := by
  have hunfold : swapIdx35C a b c d i
      = sumFinCast (cluster35Size_finalC a b c d)
        ((cleanDecLEquiv (fuseSize a (b + (c + d))).1
            (fuseSize a (b + (c + d))).2
            (fuseSize b (c + d)).1 (fuseSize b (c + d)).2
            (fuseSize c d).1 (fuseSize c d).2).symm
          (((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (fuseSize (a + b) (c + d)).1
              (fuseSize (a + b) (c + d)).2).symm
              (sumFinCast (swapCast_clC a b c d)
                (cleanDecLEquiv (fuseSize (a + b + c) d).1
                  (fuseSize (a + b + c) d).2
                  (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                  (fuseSize a b).1 (fuseSize a b).2 i).2)).1,
            sumFinCast (swapCast_35C a b c d)
              (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
                (fuseSize (a + b) (c + d)).1
                (fuseSize (a + b) (c + d)).2
                ((cleanDecLEquiv (fuseSize (a + b + c) d).1
                    (fuseSize (a + b + c) d).2
                    (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                    (fuseSize a b).1 (fuseSize a b).2 i).1,
                  ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                      (fuseSize (a + b) (c + d)).1
                      (fuseSize (a + b) (c + d)).2).symm
                    (sumFinCast (swapCast_clC a b c d)
                      (cleanDecLEquiv (fuseSize (a + b + c) d).1
                        (fuseSize (a + b + c) d).2
                        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                        (fuseSize a b).1 (fuseSize a b).2 i).2)).2)))) :=
    swapIdxGenC_eq_cleanDecLEquiv (fuseSize a b) (fuseSize c d)
      (fuseSize (a + b) (c + d)) (fuseSize (a + b) c) (fuseSize (a + b + c) d)
      (fuseSize b (c + d)) (fuseSize a (b + (c + d))) (swapCast_clC a b c d)
      (swapCast_35C a b c d) (cluster35Size_finalC a b c d) i
  rw [hunfold, sumFinCast_symm_apply, Equiv.apply_symm_apply]

/-- **`decR_phi`**: `cleanDec35`'s decode of `φ(i)` (the `(cd)`-cluster
grouping's `(γ,κ)`-pair), fully spelled — the entry-level fact
consumed by `cluster35SharedTail_entry` at `φ(i)`, in terms of
`cleanDecL`'s decode of `i` (the `(ab)`-cluster grouping's
`(σ,τ,ρ)`-pair). Assembled from `phi_encode` and
`cleanDec35_eq_cleanDecLEquiv`. -/
private theorem decR_phi (a b c d : ZMod 8)
    (i : Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) :
    cleanDec35 a b c d (swapIdx35C a b c d i)
      = sumFinCast (cluster35Size_eqC a b c d)
        (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
          ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).1
              + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).2)
          ((fuseSize b (c + d)).1 * (fuseSize a (b + (c + d))).2
              + (fuseSize b (c + d)).2 * (fuseSize a (b + (c + d))).1)
          (((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
              (sumFinCast (swapCast_clC a b c d)
                (cleanDecL (fuseSize (a + b + c) d).1
                  (fuseSize (a + b + c) d).2
                  (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                  (fuseSize a b).1 (fuseSize a b).2 i).2)).1,
            sumFinCast (swapCast_35C a b c d)
              (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
                (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
                ((cleanDecL (fuseSize (a + b + c) d).1
                    (fuseSize (a + b + c) d).2
                    (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                    (fuseSize a b).1 (fuseSize a b).2 i).1,
                  ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                      (fuseSize (a + b) (c + d)).1
                      (fuseSize (a + b) (c + d)).2).symm
                    (sumFinCast (swapCast_clC a b c d)
                      (cleanDecL (fuseSize (a + b + c) d).1
                        (fuseSize (a + b + c) d).2
                        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                        (fuseSize a b).1 (fuseSize a b).2 i).2)).2)))) := by
  rw [cleanDec35_eq_cleanDecLEquiv, phi_encode, cleanDecLEquiv_apply]

omit [Invertible (2 : K)] in
/-- Local copy of `stdMatrixCast_entry` (verbatim from
`PentagonEdge35Core.lean`), stated with THIS FILE's own `sumFinCast`
(rather than the module-local copy from `PentagonEdge35Core.lean`) so
downstream `rw`/`show`/`exact` calls against expressions built from
THIS file's `sumFinCast`-abstracted locals (e.g. `Chat`/`Dhat`, built
via `set ... := ... (sumFinCast (swapCast_clC ...) ...)`) can match
syntactically, avoiding the cross-copy `isDefEq` obstruction (the two
`sumFinCast` definitions are byte-identical and hence
propositionally/definitionally interchangeable in principle, but the
ambient goal's sheer size defeats `isDefEq`'s congruence check in
practice when the two copies are mixed). -/
private theorem stdMatrixCast_entryC {x y : ZMod 8} (h : x = y) {s t : ℕ × ℕ}
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

/-! ### Stage B: local copies of the generator entry-formula kit
(verbatim, from `PentagonEdge35Core.lean`'s `CoreKit` /
`PentagonEdge35Signed.lean`'s `mSG` lemmas) -/

section CoreKitB

private def toCB {P Q : SuperAlgebra K} (x : P.grading ᵍ⊗[K] Q.grading) :
    (P.gtensor Q).carrier := x

omit [Invertible (2 : K)] in
private theorem gtensorCongr_tmulCB {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (a : P.carrier) (b : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv (toCB (a ᵍ⊗ₜ[K] b))
      = toCB (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading e.toAlgEquiv
    f.toAlgEquiv e.map_grading f.map_grading a b

omit [Invertible (2 : K)] in
private theorem add_gtmulCB {P Q : SuperAlgebra K}
    (u v : P.carrier) (z : Q.carrier) :
    toCB ((u + v) ᵍ⊗ₜ[K] z) = toCB (u ᵍ⊗ₜ[K] z) + toCB (v ᵍ⊗ₜ[K] z) := by
  show ((u + v) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading)
    = (u ᵍ⊗ₜ[K] z) + (v ᵍ⊗ₜ[K] z)
  rw [show ((u + v) ᵍ⊗ₜ[K] z : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading ((u + v) ⊗ₜ[K] z) from rfl,
    TensorProduct.add_tmul, map_add]
  rfl

omit [Invertible (2 : K)] in
private theorem gtmulCB_add {P Q : SuperAlgebra K}
    (x : P.carrier) (u v : Q.carrier) :
    toCB (x ᵍ⊗ₜ[K] (u + v)) = toCB (x ᵍ⊗ₜ[K] u) + toCB (x ᵍ⊗ₜ[K] v) := by
  show (x ᵍ⊗ₜ[K] (u + v) : P.grading ᵍ⊗[K] Q.grading)
    = (x ᵍ⊗ₜ[K] u) + (x ᵍ⊗ₜ[K] v)
  rw [show (x ᵍ⊗ₜ[K] (u + v) : P.grading ᵍ⊗[K] Q.grading)
      = of K P.grading Q.grading (x ⊗ₜ[K] (u + v)) from rfl,
    TensorProduct.tmul_add, map_add]
  rfl

omit [Invertible (2 : K)] in
/-- The braiding on `x ᵍ⊗ 1` is sign-free, for arbitrary `x`. -/
private theorem gtensorComm_tmul_oneB {P Q : SuperAlgebra K}
    (x : P.carrier) :
    (gtensorComm P Q).toAlgEquiv (toCB (x ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = toCB ((1 : Q.carrier) ᵍ⊗ₜ[K] x) := by
  have hsplit : ∀ (j : ZMod 2) (y : P.carrier), y ∈ P.grading j →
      (gtensorComm P Q).toAlgEquiv (toCB (y ᵍ⊗ₜ[K] (1 : Q.carrier)))
        = toCB ((1 : Q.carrier) ᵍ⊗ₜ[K] y) := by
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
  calc (gtensorComm P Q).toAlgEquiv (toCB (x ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = (gtensorComm P Q).toAlgEquiv
          (toCB ((evenPart P.grading x + oddPart P.grading x)
            ᵍ⊗ₜ[K] (1 : Q.carrier))) := by
        rw [evenPart_add_oddPart]
    _ = (gtensorComm P Q).toAlgEquiv
          (toCB ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier)))
        + (gtensorComm P Q).toAlgEquiv
          (toCB ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))) := by
        rw [add_gtmulCB, map_add]
    _ = toCB ((1 : Q.carrier) ᵍ⊗ₜ[K] evenPart P.grading x)
        + toCB ((1 : Q.carrier) ᵍ⊗ₜ[K] oddPart P.grading x) := by
        rw [hsplit 0 _ (evenPart_mem P.grading x),
          hsplit 1 _ (oddPart_mem P.grading x)]
    _ = toCB ((1 : Q.carrier) ᵍ⊗ₜ[K] x) := by
        rw [← gtmulCB_add, evenPart_add_oddPart]

omit [Invertible (2 : K)] in
/-- The braiding on `1 ᵍ⊗ y` is sign-free, for arbitrary `y`. -/
private theorem gtensorComm_one_tmulB {P Q : SuperAlgebra K}
    (y : Q.carrier) :
    (gtensorComm P Q).toAlgEquiv (toCB ((1 : P.carrier) ᵍ⊗ₜ[K] y))
      = toCB (y ᵍ⊗ₜ[K] (1 : P.carrier)) := by
  have hsplit : ∀ (j : ZMod 2) (z : Q.carrier), z ∈ Q.grading j →
      (gtensorComm P Q).toAlgEquiv (toCB ((1 : P.carrier) ᵍ⊗ₜ[K] z))
        = toCB (z ᵍ⊗ₜ[K] (1 : P.carrier)) := by
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
  calc (gtensorComm P Q).toAlgEquiv (toCB ((1 : P.carrier) ᵍ⊗ₜ[K] y))
      = (gtensorComm P Q).toAlgEquiv
          (toCB ((1 : P.carrier) ᵍ⊗ₜ[K]
            (evenPart Q.grading y + oddPart Q.grading y))) := by
        rw [evenPart_add_oddPart]
    _ = (gtensorComm P Q).toAlgEquiv
          (toCB ((1 : P.carrier) ᵍ⊗ₜ[K] evenPart Q.grading y))
        + (gtensorComm P Q).toAlgEquiv
          (toCB ((1 : P.carrier) ᵍ⊗ₜ[K] oddPart Q.grading y)) := by
        rw [gtmulCB_add, map_add]
    _ = toCB ((evenPart Q.grading y) ᵍ⊗ₜ[K] (1 : P.carrier))
        + toCB ((oddPart Q.grading y) ᵍ⊗ₜ[K] (1 : P.carrier)) := by
        rw [hsplit 0 _ (evenPart_mem Q.grading y),
          hsplit 1 _ (oddPart_mem Q.grading y)]
    _ = toCB (y ᵍ⊗ₜ[K] (1 : P.carrier)) := by
        rw [← add_gtmulCB, evenPart_add_oddPart]

omit [Invertible (2 : K)] in
/-- `mSGR` on `x ᵍ⊗ 1`: the signed diagonal of `x`. -/
private theorem matrixSuperGtensorRight_tmul_oneB {P Q : SuperAlgebra K}
    (p q : ℕ) (x : P.carrier) :
    (matrixSuperGtensorRight P Q p q).toAlgEquiv
        (toCB (x ᵍ⊗ₜ[K] (1 : (Q.matrixSuper p q).carrier)))
      = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
          toCB ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
            + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
              toCB ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))) := by
  show ((gtensorComm Q P).matrixSuper p q).toAlgEquiv
      ((matrixSuperGtensor Q P p q).toAlgEquiv
        ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv
          (toCB (x ᵍ⊗ₜ[K] (1 : (Q.matrixSuper p q).carrier)))))
    = _
  rw [gtensorComm_tmul_oneB,
    show (matrixSuperGtensor Q P p q).toAlgEquiv
        (toCB ((1 : (Q.matrixSuper p q).carrier) ᵍ⊗ₜ[K] x))
      = matrixInclLeft Q.grading P.grading
          (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
        * matrixInclRight (sumParity p q) Q.grading P.grading x from
      matrixTensorSuperHom_tmul (sumParity p q) Q.grading P.grading 1 x,
    map_one, one_mul, matrixInclRight_apply]
  refine Matrix.ext fun r s => ?_
  show (gtensorComm Q P).toAlgEquiv
      (sdiag (sumParity p q) Q.grading P.grading x r s)
    = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
        toCB ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
          + ((sgn (sumParity p q s) : ℤˣ) : ℤ) •
            toCB ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))) r s
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
        (toCB ((1 : Q.carrier) ᵍ⊗ₜ[K] evenPart P.grading x)
          + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
            toCB ((1 : Q.carrier) ᵍ⊗ₜ[K] oddPart P.grading x))
      = toCB ((evenPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
        + ((sgn (sumParity p q r) : ℤˣ) : ℤ) •
          toCB ((oddPart P.grading x) ᵍ⊗ₜ[K] (1 : Q.carrier))
    rw [map_add, map_zsmul, gtensorComm_one_tmulB, gtensorComm_one_tmulB]
  · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs]
    exact map_zero _

omit [Invertible (2 : K)] in
/-- `mSGR` on `1 ᵍ⊗ N`: entrywise `1 ᵍ⊗ ·`. -/
private theorem matrixSuperGtensorRight_one_tmulB {P Q : SuperAlgebra K}
    (p q : ℕ) (N₀ : (Q.matrixSuper p q).carrier) :
    (matrixSuperGtensorRight P Q p q).toAlgEquiv
        (toCB ((1 : P.carrier) ᵍ⊗ₜ[K] N₀))
      = Matrix.map
          (N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
          (fun z => toCB ((1 : P.carrier) ᵍ⊗ₜ[K] z)) := by
  show ((gtensorComm Q P).matrixSuper p q).toAlgEquiv
      ((matrixSuperGtensor Q P p q).toAlgEquiv
        ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv
          (toCB ((1 : P.carrier) ᵍ⊗ₜ[K] N₀))))
    = _
  rw [gtensorComm_one_tmulB,
    show (matrixSuperGtensor Q P p q).toAlgEquiv
        (toCB (N₀ ᵍ⊗ₜ[K] (1 : P.carrier)))
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
  exact gtensorComm_tmul_oneB
    ((N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier) r s)

omit [Invertible (2 : K)] in
/-- `mSG` on `M₀ ᵍ⊗ 1`: the entrywise left inclusion. -/
private theorem matrixSuperGtensor_tmul_oneB {P Q : SuperAlgebra K}
    (p q : ℕ) (M₀ : (P.matrixSuper p q).carrier) :
    (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCB (M₀ ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = matrixInclLeft P.grading Q.grading
          (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) := by
  rw [show (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCB (M₀ ᵍ⊗ₜ[K] (1 : Q.carrier)))
      = matrixInclLeft P.grading Q.grading
          (M₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier)
        * matrixInclRight (sumParity p q) P.grading Q.grading
          (1 : Q.carrier) from
      matrixTensorSuperHom_tmul (sumParity p q) P.grading Q.grading
        M₀ 1,
    map_one, mul_one]

omit [Invertible (2 : K)] in
/-- `mSG` on `1 ᵍ⊗ y`: the signed diagonal. -/
private theorem matrixSuperGtensor_one_tmulB {P Q : SuperAlgebra K}
    (p q : ℕ) (y : Q.carrier) :
    (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCB ((1 : (P.matrixSuper p q).carrier) ᵍ⊗ₜ[K] y))
      = matrixInclRight (sumParity p q) P.grading Q.grading y := by
  rw [show (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCB ((1 : (P.matrixSuper p q).carrier) ᵍ⊗ₜ[K] y))
      = matrixInclLeft P.grading Q.grading
          (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier)
        * matrixInclRight (sumParity p q) P.grading Q.grading y from
      matrixTensorSuperHom_tmul (sumParity p q) P.grading Q.grading
        1 y,
    map_one, one_mul]

omit [Invertible (2 : K)] in
/-- Entry formula for the functorial matrix lift of an equivalence:
`e.matrixSuper` acts entrywise. -/
private theorem matrixSuper_applyB {P Q : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) (p q : ℕ) (M : (P.matrixSuper p q).carrier)
    (r s : Fin p ⊕ Fin q) :
    (e.matrixSuper p q).toAlgEquiv M r s = e.toAlgEquiv (M r s) := rfl

/-- The canonical (`rfl`) identification of `(P.matrixSuper p q).carrier`
with the raw `Matrix` type, packaged as a function so applying it forces
the elaborator to display the target in `Matrix`-form (works around a
transparency snag when passing `evenPart`/`oddPart` values of a matrix
superalgebra straight into `matrixInclLeft`). -/
private def toRawMatrixB {P : SuperAlgebra K} (p q : ℕ)
    (M : (P.matrixSuper p q).carrier) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier := M

omit [Invertible (2 : K)] in
private theorem toRawMatrixB_apply {P : SuperAlgebra K} (p q : ℕ)
    (M : (P.matrixSuper p q).carrier) (r s : Fin p ⊕ Fin q) :
    toRawMatrixB p q M r s = M r s := rfl

omit [Invertible (2 : K)] in
/-- Pushing a `SuperAlgEquiv` through `matrixSuper` on a
`Matrix.diagonal (fun t => x t + c t • y t)`-shaped value.  Entirely
abstract in `x`, `y`, `e`'s domain/codomain — the statement never
names the concrete gtensor/matrixSuper carrier type directly (only
through `e.matrixSuper p q`'s own elaborated type), which avoids the
`instances`-transparency snag that a direct `rw`/`show` on such a
value would trip. -/
private theorem matrixSuper_diagonal_add_zsmulB {P Q : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) (p q : ℕ)
    (x y : Fin p ⊕ Fin q → P.carrier) (c : Fin p ⊕ Fin q → ℤ) :
    (e.matrixSuper p q).toAlgEquiv
        (Matrix.diagonal (fun t => x t + (c t) • y t))
      = Matrix.diagonal (fun t => e.toAlgEquiv (x t) + (c t) • e.toAlgEquiv (y t)) := by
  refine Matrix.ext fun t u => ?_
  rw [matrixSuper_applyB]
  by_cases htu : t = u
  · subst htu
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_add, map_zsmul]
  · rw [Matrix.diagonal_apply_ne _ htu, Matrix.diagonal_apply_ne _ htu, map_zero]

end CoreKitB

/-! ### Stage B: the CORE comparison -/

section CoreB

/-- The `(cd)`-first stabilization order of `M_σ(T_{a+b}) ᵍ⊗ M_γ(T_{c+d})`,
landing on the pentagon-frame matrix superalgebra, as a plain `AlgHom`
(named so the `galgHom_ext` generator computation can `show F35 ... =
G13 ...` instead of restating the four-layer composite by hand). -/
private noncomputable def F35 (a b c d : ZMod 8) :
    (((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).carrier →ₐ[K]
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  (cluster35SharedTail a b c d).toAlgEquiv.toAlgHom.comp
    ((((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
          (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv.toAlgHom.comp
      ((((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
            (fuseSize a b).2).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).toAlgEquiv.toAlgHom.comp
        (((matrixSuperGtensor (stdTower (K := K) (a + b))
              (stdTower (c + d)) (fuseSize a b).1
              (fuseSize a b).2).matrixSuper
              (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv.toAlgHom.comp
          (matrixSuperGtensorRight
              ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
                (fuseSize a b).2)
              (stdTower (c + d)) (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv.toAlgHom))))

/-- The `(ab)`-first stabilization order, conjugated by `swapSign`, as
a plain `AlgHom` (see `F35`). -/
private noncomputable def G13 (a b c d : ZMod 8) :
    (((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).carrier →ₐ[K]
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  (conjSwapHom a b c d).comp
      ((cluster13SharedTail a b c d).toAlgEquiv.toAlgHom.comp
        (((stdMatrixCast (add_assoc (a + b) c d).symm
              (castR_clC a b c d)).matrixSuper (fuseSize a b).1
              (fuseSize a b).2).toAlgEquiv.toAlgHom.comp
          ((((matrixSuperComp (stdTower (a + b + (c + d)))
                (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1
                (fuseSize (a + b) (c + d)).2).matrixSuper
                (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv.toAlgHom.comp
            ((((stdFuse (a + b) (c + d)).matrixSuper
                  (fuseSize c d).1 (fuseSize c d).2).matrixSuper
                  (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv.toAlgHom.comp
              (((matrixSuperGtensorRight (stdTower (a + b))
                    (stdTower (c + d)) (fuseSize c d).1
                    (fuseSize c d).2).matrixSuper (fuseSize a b).1
                    (fuseSize a b).2).toAlgEquiv.toAlgHom.comp
                (matrixSuperGtensor (stdTower (a + b))
                    ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                      (fuseSize c d).2) (fuseSize a b).1
                    (fuseSize a b).2).toAlgEquiv.toAlgHom))))))

private theorem F35_eq (a b c d : ZMod 8)
    (v : (((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).carrier) :
    F35 a b c d v
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
                  (fuseSize c d).2).toAlgEquiv v)))) := rfl

private theorem G13_eq (a b c d : ZMod 8)
    (v : (((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).carrier) :
    G13 a b c d v
      = swapSign a b c d
        * (cluster13SharedTail a b c d).toAlgEquiv
          (((stdMatrixCast (add_assoc (a + b) c d).symm
                (castR_clC a b c d)).matrixSuper (fuseSize a b).1
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
                      (fuseSize a b).2).toAlgEquiv v)))))
        * swapSign a b c d := rfl

/-- Standalone extraction of `CORE`'s `hM` case (the `M₀ ᵍ⊗ 1`
generator, `σ`-slot only) into a top-level lemma with a fresh local
context, mirroring `F35`/`G13`'s agreement on `includeLeft ... M₀`. -/
private theorem CORE_left (a b c d : ZMod 8)
    (M₀ : ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).carrier) :
    F35 (K := K) a b c d
      (includeLeft (((stdTower (K := K) (a + b)).matrixSuper
          (fuseSize a b).1 (fuseSize a b).2).grading)
        (((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading) M₀)
    = G13 (K := K) a b c d
      (includeLeft (((stdTower (K := K) (a + b)).matrixSuper
          (fuseSize a b).1 (fuseSize a b).2).grading)
        (((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading) M₀) := by
  rw [includeLeft_apply, F35_eq, G13_eq]
  have hL1 : (matrixSuperGtensorRight
        ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2)
        (stdTower (c + d)) (fuseSize c d).1
        (fuseSize c d).2).toAlgEquiv
      (M₀ ᵍ⊗ₜ[K] (1 : ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).carrier))
    = Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
        toCB ((evenPart ((stdTower (K := K) (a + b)).matrixSuper
            (fuseSize a b).1 (fuseSize a b).2).grading M₀)
            ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
            toCB ((oddPart ((stdTower (K := K) (a + b)).matrixSuper
                (fuseSize a b).1 (fuseSize a b).2).grading M₀)
              ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))) :=
    matrixSuperGtensorRight_tmul_oneB (fuseSize c d).1 (fuseSize c d).2 M₀
  rw [hL1]
  have hL2 : ((matrixSuperGtensor (stdTower (K := K) (a + b))
          (stdTower (c + d)) (fuseSize a b).1
          (fuseSize a b).2).matrixSuper
          (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
      (Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
          toCB ((evenPart ((stdTower (K := K) (a + b)).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).grading M₀)
              ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))
            + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
              toCB ((oddPart ((stdTower (K := K) (a + b)).matrixSuper
                  (fuseSize a b).1 (fuseSize a b).2).grading M₀)
                ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))))
      = Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
          matrixInclLeft (stdTower (K := K) (a + b)).grading
              (stdTower (c + d)).grading
              (toRawMatrixB (fuseSize a b).1 (fuseSize a b).2
                (evenPart ((stdTower (K := K) (a + b)).matrixSuper
                  (fuseSize a b).1 (fuseSize a b).2).grading M₀))
            + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
              matrixInclLeft (stdTower (K := K) (a + b)).grading
                (stdTower (c + d)).grading
                (toRawMatrixB (fuseSize a b).1 (fuseSize a b).2
                  (oddPart ((stdTower (K := K) (a + b)).matrixSuper
                    (fuseSize a b).1 (fuseSize a b).2).grading M₀))) := by
    refine Matrix.ext fun r s => ?_
    rw [matrixSuper_applyB]
    by_cases hrs : r = s
    · subst hrs
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_add, map_zsmul,
        matrixSuperGtensor_tmul_oneB, matrixSuperGtensor_tmul_oneB]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs]
      exact map_zero _
  rw [hL2]
  -- LHS is now fully entrywise-computed; continue peeling the
  -- outer `stdFuse` and `matrixSuperComp` layers.  Generalize the
  -- even/odd parts of `M₀` (cast to plain `Matrix` via `toRawMatrixB`)
  -- to fresh matrix variables first (works around a transparency
  -- snag in unifying `matrixInclLeft`'s domain against
  -- `(P.matrixSuper p q).carrier`).
  generalize hEv : toRawMatrixB (fuseSize a b).1 (fuseSize a b).2
      (evenPart ((stdTower (K := K) (a + b)).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).grading M₀) = Mev
  generalize hOd : toRawMatrixB (fuseSize a b).1 (fuseSize a b).2
      (oddPart ((stdTower (K := K) (a + b)).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).grading M₀) = Mod
  have hFuseE : (((stdFuse (K := K) (a + b) (c + d)).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2)).toAlgEquiv
      (matrixInclLeft (stdTower (K := K) (a + b)).grading
          (stdTower (c + d)).grading Mev)
    = Matrix.map Mev (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
          (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))) := by
    refine Matrix.ext fun r s => ?_
    rw [matrixSuper_applyB, matrixInclLeft_apply, Matrix.map_apply]
    rfl
  have hFuseO : (((stdFuse (K := K) (a + b) (c + d)).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2)).toAlgEquiv
      (matrixInclLeft (stdTower (K := K) (a + b)).grading
          (stdTower (c + d)).grading Mod)
    = Matrix.map Mod (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
          (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))) := by
    refine Matrix.ext fun r s => ?_
    rw [matrixSuper_applyB, matrixInclLeft_apply, Matrix.map_apply]
    rfl
  have hL3 : (((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv
      (Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
          matrixInclLeft (stdTower (K := K) (a + b)).grading
              (stdTower (c + d)).grading Mev
            + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
              matrixInclLeft (stdTower (K := K) (a + b)).grading
                (stdTower (c + d)).grading Mod))
      = Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
          Matrix.map Mev (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))))
            + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
              Matrix.map Mod (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                  (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))))) := by
    refine Matrix.ext fun r s => ?_
    rw [matrixSuper_applyB]
    by_cases hrs : r = s
    · subst hrs
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      have step1 := map_add (((stdFuse (K := K) (a + b) (c + d)).matrixSuper
            (fuseSize a b).1 (fuseSize a b).2)).toAlgEquiv
          (matrixInclLeft (stdTower (K := K) (a + b)).grading
              (stdTower (c + d)).grading Mev :
            (((stdTower (K := K) (a + b)).gtensor (stdTower (c + d))).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).carrier)
          (((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 r) : ℤˣ) : ℤ) •
              matrixInclLeft (stdTower (K := K) (a + b)).grading
                (stdTower (c + d)).grading Mod :
            (((stdTower (K := K) (a + b)).gtensor (stdTower (c + d))).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).carrier)
      have step2 := map_zsmul (((stdFuse (K := K) (a + b) (c + d)).matrixSuper
            (fuseSize a b).1 (fuseSize a b).2)).toAlgEquiv
          (((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 r) : ℤˣ) : ℤ))
          (matrixInclLeft (stdTower (K := K) (a + b)).grading
              (stdTower (c + d)).grading Mod :
            (((stdTower (K := K) (a + b)).gtensor (stdTower (c + d))).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).carrier)
      exact step1.trans (congrArg₂ (· + ·) hFuseE
        (step2.trans (congrArg _ hFuseO)))
    · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs]
      exact map_zero _
  show (cluster35SharedTail a b c d).toAlgEquiv
      (((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
          (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
        ((((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
            (fuseSize a b).2).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).toAlgEquiv
          (Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
            matrixInclLeft (stdTower (K := K) (a + b)).grading
                (stdTower (c + d)).grading Mev
              + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
                matrixInclLeft (stdTower (K := K) (a + b)).grading
                  (stdTower (c + d)).grading Mod))))
    = _
  rw [hL3]
  -- Mirror chain for the RHS (`G13`-side): reduce
  -- `(cluster13SharedTail ...).toAlgEquiv (... M₀ ᵍ⊗ 1 ...)` through
  -- its own four layers, in the (γ outer, σ inner) order.  First
  -- generalize `M₀` to a raw `Matrix` (via `toRawMatrixB`) so that
  -- `M r s`-style entry applications never re-enter `.carrier`-opaque
  -- form (same workaround as the LHS's `Mev`/`Mod`).
  have hM0eq : (M₀ : Matrix (Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2)
      (Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2)
      (stdTower (K := K) (a + b)).carrier)
    = toRawMatrixB (fuseSize a b).1 (fuseSize a b).2 M₀ := rfl
  rw [hM0eq]
  generalize hM0 : toRawMatrixB (fuseSize a b).1 (fuseSize a b).2 M₀ = M
  have hR1 : (matrixSuperGtensor (stdTower (K := K) (a + b))
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2) (fuseSize a b).1
        (fuseSize a b).2).toAlgEquiv
      (M ᵍ⊗ₜ[K] (1 : ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).carrier))
    = matrixInclLeft (stdTower (K := K) (a + b)).grading
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading M :=
    matrixSuperGtensor_tmul_oneB (fuseSize a b).1 (fuseSize a b).2 M
  have hR2 : ((matrixSuperGtensorRight (stdTower (K := K) (a + b))
        (stdTower (c + d)) (fuseSize c d).1 (fuseSize c d).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      (matrixInclLeft (stdTower (K := K) (a + b)).grading
          ((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading M)
    = Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
        Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
          toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
              (1 : (stdTower (K := K) (c + d)).carrier))
            + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
              toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                (1 : (stdTower (K := K) (c + d)).carrier)))) := by
    refine Matrix.ext fun r s => ?_
    rw [matrixSuper_applyB, matrixInclLeft_apply]
    exact matrixSuperGtensorRight_tmul_oneB (fuseSize c d).1 (fuseSize c d).2 (M r s)
  rw [hR1, hR2]
  have hR3 : (((stdFuse (K := K) (a + b) (c + d)).matrixSuper
          (fuseSize c d).1 (fuseSize c d).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      (Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
          Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
            toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                (1 : (stdTower (K := K) (c + d)).carrier))
              + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
                toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                  (1 : (stdTower (K := K) (c + d)).carrier)))))
    = Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
        Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
          (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                  (1 : (stdTower (K := K) (c + d)).carrier)))
            + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
              (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                  (1 : (stdTower (K := K) (c + d)).carrier))))) := by
    refine Matrix.ext fun r s => ?_
    rw [matrixSuper_applyB]
    exact matrixSuper_diagonal_add_zsmulB (stdFuse (K := K) (a + b) (c + d))
      (fuseSize c d).1 (fuseSize c d).2
      (fun t => toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
        (1 : (stdTower (K := K) (c + d)).carrier)))
      (fun t => toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
        (1 : (stdTower (K := K) (c + d)).carrier)))
      (fun t => ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ))
  -- Push `hR3` through the remaining outer layers (`matrixSuperComp`,
  -- `stdMatrixCast`, `cluster13SharedTail`, then `* swapSign` on
  -- both sides) via term-mode `congrArg`/`congrArg₂` composition —
  -- `rw [hR3]` itself trips the `instances`-transparency snag when
  -- re-elaborating the whole (LHS-included) goal to build the
  -- rewrite motive, even though `hR3` alone typechecks fine.
  have hRcomp : ((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      ((((stdFuse (K := K) (a + b) (c + d)).matrixSuper
            (fuseSize c d).1 (fuseSize c d).2).matrixSuper
          (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
        (Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
            Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
              toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                  (1 : (stdTower (K := K) (c + d)).carrier))
                + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
                  toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier))))))
    = ((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      (Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
          Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
            (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier)))
              + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
                (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                  (toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier)))))) :=
    congrArg _ hR3
  have hRcast := congrArg ((stdMatrixCast (add_assoc (a + b) c d).symm
      (castR_clC a b c d)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).toAlgEquiv hRcomp
  have hRtail := congrArg (cluster13SharedTail a b c d).toAlgEquiv hRcast
  have hRfull := congrArg (· * swapSign (K := K) a b c d)
    (congrArg (swapSign (K := K) a b c d * ·) hRtail)
  refine Matrix.ext fun i j => ?_
  have hRentry := congrFun (congrFun hRfull i) j
  refine Eq.trans ?_ hRentry.symm
  rw [cluster35SharedTail_entry, mul_swapSign_applyC, swapSign_mul_applyC,
    cluster13SharedTail_entry]
  -- Align the two decodes: `decR_phi` at `φ(i)`/`φ(j)`, combined
  -- with the involution `φ(φ(i)) = i`, expresses `cleanDec35 i`
  -- (the LHS's decode) in terms of `cleanDecL (φ i)` (the RHS's
  -- decode after the sign-peel reindexed through `φ`).
  have hdecRi := decR_phi a b c d (swapIdx35C a b c d i)
  have hdecRj := decR_phi a b c d (swapIdx35C a b c d j)
  rw [phi_involC K a b c d i] at hdecRi
  rw [phi_involC K a b c d j] at hdecRj
  -- Simplify the LHS's outer `(collapseIndexEquiv (fuseSize c d)
  -- (sizeL a b (c+d))).symm` applied to `cleanDec35 i` (via
  -- `hdecRi`) using the generic collapse/sumFinCast cancellation —
  -- collapses the whole nested `sumFinCast (collapseIndexEquiv ...)`
  -- decode down to a plain pair `(outer, sumFinCast inner)`.
  have hdecRi2 : (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
        (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
      (cleanDec35 a b c d i)
    = ((((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1
            (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (swapCast_clC a b c d)
            (cleanDecL (fuseSize (a + b + c) d).1
              (fuseSize (a + b + c) d).2
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
              (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).2)).1,
        sumFinCast (sizeR_flat_eq_35C a b c d)
          (sumFinCast (swapCast_35C a b c d)
            (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
              ((cleanDecL (fuseSize (a + b + c) d).1
                  (fuseSize (a + b + c) d).2
                  (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                  (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).1,
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1
                    (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (swapCast_clC a b c d)
                    (cleanDecL (fuseSize (a + b + c) d).1
                      (fuseSize (a + b + c) d).2
                      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                      (fuseSize a b).1 (fuseSize a b).2
                      (swapIdx35C a b c d i)).2)).2))))) := by
    rw [hdecRi]
    exact collapseIndexEquiv_symm_sumFinCast_collapse (fuseSize c d).1 (fuseSize c d).2
      (sizeR_flat_eq_35C a b c d) (cluster35Size_eqC a b c d) _
  have hdecRj2 : (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
        (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
      (cleanDec35 a b c d j)
    = ((((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1
            (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (swapCast_clC a b c d)
            (cleanDecL (fuseSize (a + b + c) d).1
              (fuseSize (a + b + c) d).2
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
              (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).2)).1,
        sumFinCast (sizeR_flat_eq_35C a b c d)
          (sumFinCast (swapCast_35C a b c d)
            (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
              ((cleanDecL (fuseSize (a + b + c) d).1
                  (fuseSize (a + b + c) d).2
                  (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                  (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).1,
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1
                    (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (swapCast_clC a b c d)
                    (cleanDecL (fuseSize (a + b + c) d).1
                      (fuseSize (a + b + c) d).2
                      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                      (fuseSize a b).1 (fuseSize a b).2
                      (swapIdx35C a b c d j)).2)).2))))) := by
    rw [hdecRj]
    exact collapseIndexEquiv_symm_sumFinCast_collapse (fuseSize c d).1 (fuseSize c d).2
      (sizeR_flat_eq_35C a b c d) (cluster35Size_eqC a b c d) _
  rw [hdecRi2, hdecRj2]
  -- Peel `stdMatrixCast`'s outer `(fuseSize a b)`-matrix layer,
  -- then its own entry formula, then `matrixSuperComp`'s entry
  -- formula — each applied as a direct TERM (never `rw` on the
  -- ambient goal) to sidestep the `instances`-transparency snag
  -- that a blanket `rw [stdMatrixCast_entry, ...]` trips here.
  set A := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).1
    with hAdef
  set B := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).1
    with hBdef
  set C := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).2
    with hCdef
  set D := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).2
    with hDdef
  set Chat := (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
      (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
      (sumFinCast (swapCast_clC a b c d) C)
    with hChatdef
  set Dhat := (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
      (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
      (sumFinCast (swapCast_clC a b c d) D)
    with hDhatdef
  have hRAB := matrixSuper_applyB
    (stdMatrixCast (add_assoc (a + b) c d).symm (castR_clC a b c d))
    (fuseSize a b).1 (fuseSize a b).2
    (((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      (Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
          Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
            (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier)))
              + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
                (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                  (toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier)))))))
    A B
  rw [hRAB]
  have hRcastEntry := stdMatrixCast_entry (add_assoc (a + b) c d).symm
    (castR_clC a b c d)
    ((((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      (Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
          Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
            (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier)))
              + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
                (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                  (toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier)))))) A B))
    C D
  have hRAB2 := matrixSuper_applyB
    (matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2)
    (fuseSize a b).1 (fuseSize a b).2
    (Matrix.of (fun r s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
        Matrix.diagonal (fun t : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
          (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB ((evenPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                  (1 : (stdTower (K := K) (c + d)).carrier)))
            + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 t) : ℤˣ) : ℤ) •
              (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((oddPart (stdTower (K := K) (a + b)).grading (M r s)) ᵍ⊗ₜ[K]
                  (1 : (stdTower (K := K) (c + d)).carrier))))))
    A B
  rw [hRcastEntry, hRAB2, matrixSuperComp_entryC]
  -- Both sides are now raw flat-index comparisons in
  -- `(stdTower (a+b+c+d)).carrier`: the LHS is a `Matrix.diagonal`
  -- (outer `fuseSize c d` layer) applied to a `▸`-transported
  -- `matrixSuperComp`-collapsed index quadruple built from `A B C D`
  -- via `collapseIndexEquiv`/`sumFinCast`; the RHS is `sgn • sgn •`
  -- of a `▸`-transported `Matrix.of`/`Matrix.diagonal` (outer
  -- `fuseSize a b` layer, i.e. `A B` directly) applied to the
  -- INNER two components of the same `C`/`D`-built collapse.
  -- Remaining: show the outer-diagonal gating condition on each
  -- side coincides (both should reduce to "does `i`'s and `j`'s
  -- shared-tail decode land in the same outer slot", by
  -- `Matrix.diagonal_apply_eq`/`_ne`), then match the resulting
  -- scalar values via `evenPart_matrixSuper_apply`/
  -- `oddPart_matrixSuper_apply` (relating `Mev`/`Mod`'s raw entries
  -- back to `evenPart`/`oddPart (M r s)`) and a `ZMod 2`
  -- sign-recombination `decide`.  BLOCKED here: the index algebra
  -- connecting the two `collapseIndexEquiv`/`sumFinCast` nestings
  -- (LHS's outer-γ/inner-σ split vs RHS's outer-σ/inner-γ split)
  -- has not been closed.
  -- The double cast `sumFinCast (sizeR_flat_eq_35C) ∘ sumFinCast
  -- (swapCast_35C)` composes (via `sumFinCast_trans`) to a single
  -- cast along `(swapCast_35C).trans (sizeR_flat_eq_35C)`, a proof
  -- of `X = X` for the literal same `X` — hence, by proof
  -- irrelevance (`sumFinCast_rfl_eq_id`), the double cast is the
  -- identity.  This identifies the LHS's inner `matrixSuperComp`
  -- index directly with `collapse (A, Chat.2)` (no residual cast),
  -- matching the RHS's own `A B Chat.1 Dhat.1 Chat.2 Dhat.2`
  -- structure via the SAME `Chat`/`Dhat`.
  have hEsimp : sumFinCast (sizeR_flat_eq_35C a b c d)
        (sumFinCast (swapCast_35C a b c d)
          (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
            (A, Chat.2)))
      = collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (A, Chat.2) := by
    rw [sumFinCast_trans]
    exact sumFinCast_rfl_eq_id _ _
  have hFsimp : sumFinCast (sizeR_flat_eq_35C a b c d)
        (sumFinCast (swapCast_35C a b c d)
          (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
            (B, Dhat.2)))
      = collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (B, Dhat.2) := by
    rw [sumFinCast_trans]
    exact sumFinCast_rfl_eq_id _ _
  have hLAB2 := matrixSuper_applyB
    (matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2)
    (fuseSize c d).1 (fuseSize c d).2
    (Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
        (Mev.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
            (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
            (Mod.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))))))
    Chat.1 Dhat.1
  have hLAB3 := matrixSuperComp_entryC (P := stdTower (K := K) (a + b + (c + d)))
    (fuseSize a b).1 (fuseSize a b).2
    (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
    (Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
        (Mev.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
            (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
            (Mod.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))))))
      Chat.1 Dhat.1)
    (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (A, Chat.2))
    (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (B, Dhat.2))
  have hLAB4unsimp := congrFun (congrFun hLAB2
    (sumFinCast (sizeR_flat_eq_35C a b c d)
      (sumFinCast (swapCast_35C a b c d)
        (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (A, Chat.2)))))
    (sumFinCast (sizeR_flat_eq_35C a b c d)
      (sumFinCast (swapCast_35C a b c d)
        (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (B, Dhat.2))))
  have hLAB4simp := congrArg₂
    ((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).toAlgEquiv
      ((Matrix.diagonal (fun s : Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2 =>
        (Mev.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
            (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 s) : ℤˣ) : ℤ) •
            (Mod.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))))))
        Chat.1 Dhat.1)))
    hEsimp hFsimp
  have hLAB4 := hLAB4unsimp.trans hLAB4simp
  have hLAB5 := hLAB4.trans hLAB3
  set hcastAB : a + b + (c + d) = a + b + c + d := by ring with hcastAB_def
  have hLcast := congrArg
    (fun x => hcastAB ▸ x) hLAB5
  refine hLcast.trans ?_
  simp only [Equiv.symm_apply_apply]
  have key : ∀ {x y : ZMod 8} (h : x = y) (p q p' q' : ℕ)
      (r s : Fin p' ⊕ Fin q') (t u : Fin p ⊕ Fin q),
      (h ▸ ((0 : (((stdTower (K := K) x).matrixSuper p q).matrixSuper p' q').carrier)
        r s t u) : (stdTower (K := K) y).carrier)
      = (0 : (stdTower (K := K) y).carrier) := by
    intro x y h p q p' q' r s t u
    subst h
    rfl
  by_cases hgate : Chat.1 = Dhat.1
  · rw [hgate, Matrix.diagonal_apply_eq]
    simp only [Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with hgate2
    · have hCD1 : ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (castR_clC a b c d).symm C)).1 = Dhat.1 := by
        rw [show ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
            (sumFinCast (castR_clC a b c d).symm C)).1 = Chat.1 from rfl]
        exact hgate
      have step1 : ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
            (toCB ((evenPart (stdTower (K := K) (a + b)).grading (M A B)) ᵍ⊗ₜ[K]
                (1 : (stdTower (K := K) (c + d)).carrier)))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (castR_clC a b c d).symm C)).1) : ℤˣ) : ℤ) •
            (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB ((oddPart (stdTower (K := K) (a + b)).grading (M A B)) ᵍ⊗ₜ[K]
                (1 : (stdTower (K := K) (c + d)).carrier))))
        = ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
            (toCB ((evenPart (stdTower (K := K) (a + b)).grading (M A B)) ᵍ⊗ₜ[K]
                (1 : (stdTower (K := K) (c + d)).carrier)))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1) : ℤˣ) : ℤ) •
            (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB ((oddPart (stdTower (K := K) (a + b)).grading (M A B)) ᵍ⊗ₜ[K]
                (1 : (stdTower (K := K) (c + d)).carrier)))) := by
        rw [hCD1]
      have step2 := congrFun (congrFun step1 Chat.2) Dhat.2
      refine Eq.trans ?_ (congrArg
        (fun v => ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ) •
          ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ) •
            (hcastAB ▸ v)) step2.symm)
      have hMevAB : Mev A B = if sumParity (fuseSize a b).1 (fuseSize a b).2 A
          + sumParity (fuseSize a b).1 (fuseSize a b).2 B = 0
        then evenPart (stdTower (K := K) (a + b)).grading (M A B)
        else oddPart (stdTower (K := K) (a + b)).grading (M A B) := by
        rw [← hEv, ← hM0, toRawMatrixB_apply, toRawMatrixB_apply]
        exact evenPart_matrixSuper_apply (fuseSize a b).1 (fuseSize a b).2 M₀ A B
      have hModAB : Mod A B = if sumParity (fuseSize a b).1 (fuseSize a b).2 A
          + sumParity (fuseSize a b).1 (fuseSize a b).2 B = 0
        then oddPart (stdTower (K := K) (a + b)).grading (M A B)
        else evenPart (stdTower (K := K) (a + b)).grading (M A B) := by
        rw [← hOd, ← hM0, toRawMatrixB_apply, toRawMatrixB_apply]
        exact oddPart_matrixSuper_apply (fuseSize a b).1 (fuseSize a b).2 M₀ A B
      rw [show (Mev.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
            (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1) : ℤˣ) : ℤ) •
            Mod.map (fun z => (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB (z ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))))
          A B
        = (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv (toCB (Mev A B ᵍ⊗ₜ[K]
            (1 : (stdTower (K := K) (c + d)).carrier)))
          + ((sgn (sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1) : ℤˣ) : ℤ) •
            (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv (toCB (Mod A B ᵍ⊗ₜ[K]
              (1 : (stdTower (K := K) (c + d)).carrier))) from by
          rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply]]
      have hsignA' : swapParity35C a b c d i
          = sumParity (fuseSize a b).1 (fuseSize a b).2 A
            * sumParity (fuseSize c d).1 (fuseSize c d).2 Chat.1 :=
        swapParity35C_factor K a b c d i
      have hsignB' : swapParity35C a b c d j
          = sumParity (fuseSize a b).1 (fuseSize a b).2 B
            * sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1 :=
        swapParity35C_factor K a b c d j
      have hCDeq : sumParity (fuseSize c d).1 (fuseSize c d).2 Chat.1
          = sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1 := by
        rw [hgate]
      -- `swapParity_i + swapParity_j = sumParity(Dhat.1) * (sumParity
      -- A + sumParity B)`, unconditionally (both `hpar` branches).
      have hsumsign : swapParity35C a b c d i + swapParity35C a b c d j
          = sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1
            * (sumParity (fuseSize a b).1 (fuseSize a b).2 A
              + sumParity (fuseSize a b).1 (fuseSize a b).2 B) := by
        rw [hsignA', hsignB', hCDeq]
        ring
      have hsgnmul : ((sgn (swapParity35C a b c d i
            + swapParity35C a b c d j) : ℤˣ) : ℤ)
          = ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
            * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ) := by
        rw [← Units.val_mul, ← sgn_add, add_comm]
      by_cases hpar : sumParity (fuseSize a b).1 (fuseSize a b).2 A
          + sumParity (fuseSize a b).1 (fuseSize a b).2 B = 0
      · rw [hMevAB, hModAB, if_pos hpar, if_pos hpar]
        rw [show swapParity35C a b c d i + swapParity35C a b c d j = 0 by
          rw [hsumsign, hpar, mul_zero]] at hsgnmul
        have hsgnmul' : ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
            * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ) = 1 := by
          rw [← hsgnmul, sgn_zero, Units.val_one]
        rw [smul_smul, hsgnmul', one_smul]
      · have hpsum : sumParity (fuseSize a b).1 (fuseSize a b).2 A
            + sumParity (fuseSize a b).1 (fuseSize a b).2 B = 1 := by
          rcases zmod2_cases (sumParity (fuseSize a b).1 (fuseSize a b).2 A
              + sumParity (fuseSize a b).1 (fuseSize a b).2 B) with h | h
          · exact absurd h hpar
          · exact h
        rw [show swapParity35C a b c d i + swapParity35C a b c d j
              = sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1 by
          rw [hsumsign, hpsum, mul_one]] at hsgnmul
        rw [smul_smul, hsgnmul]
        -- Build the closing scalar identity at the ENTRY level (in
        -- `(stdTower (a+b+c+d)).carrier`), using the LITERAL,
        -- UNABBREVIATED scalar expression throughout (never `set`
        -- to a fresh `n : ℤ`) — abstracting the scalar via `set`
        -- caused `n • v` to resolve to a DIFFERENT `SMul ℤ`
        -- instance (`SubNegMonoid.toZSMul`) than the ambient goal's
        -- own (`SemigroupAction.toSMul`), a genuine (non-display)
        -- typeclass-diamond mismatch confirmed via `pp.all` token
        -- diffing — using the literal expression lets Lean re-derive
        -- the SAME canonical instance the ambient goal already uses.
        have hMevAB' : Mev A B = oddPart (stdTower (K := K) (a + b)).grading (M A B) := by
          rw [hMevAB, if_neg hpar]
        have hModAB' : Mod A B = evenPart (stdTower (K := K) (a + b)).grading (M A B) := by
          rw [hModAB, if_neg hpar]
        have hsq : ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
            * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)
            * (((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
              * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) = 1 := by
          rw [← hsgnmul, ← Units.val_mul, sgn_mul_self', Units.val_one]
        have hVW : ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB (Mev A B ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier)))
            + (((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
                * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) •
              (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB (Mod A B ᵍ⊗ₜ[K] (1 : (stdTower (K := K) (c + d)).carrier))))
          = (((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
              * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) •
              ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                  (toCB (evenPart (stdTower (K := K) (a + b)).grading (M A B) ᵍ⊗ₜ[K]
                    (1 : (stdTower (K := K) (c + d)).carrier)))
                + (((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
                    * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) •
                  (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                    (toCB (oddPart (stdTower (K := K) (a + b)).grading (M A B) ᵍ⊗ₜ[K]
                      (1 : (stdTower (K := K) (c + d)).carrier)))) := by
          rw [hMevAB', hModAB', smul_add, smul_smul, hsq, one_smul]
          exact add_comm _ _
        -- Prove the closing identity INLINE (not via a separately
        -- elaborated theorem call) so the `•`'s `SMul ℤ` instance is
        -- resolved in the SAME elaboration problem as the ambient
        -- goal, avoiding the `SubNegMonoid.toZSMul` vs
        -- `SemigroupAction.toSMul` diamond mismatch confirmed above
        -- (a separately-elaborated `castTransportSmul1` call picks a
        -- DIFFERENT — though propositionally, not syntactically,
        -- equal — canonical instance than the ambient goal's own).
        simp only [hVW]
        generalize hW2 : ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB (evenPart (stdTower (K := K) (a + b)).grading (M A B) ᵍ⊗ₜ[K]
                (1 : (stdTower (K := K) (c + d)).carrier)))
            + (((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
                * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) •
              (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB (oddPart (stdTower (K := K) (a + b)).grading (M A B) ᵍ⊗ₜ[K]
                  (1 : (stdTower (K := K) (c + d)).carrier))))
          = W2
        -- The ambient goal's `hcastAB ▸ (n • W2) Chat.2 Dhat.2` is
        -- NOT `(hcastAB ▸ (n • W2)) Chat.2 Dhat.2` (matrix cast then
        -- applied) — `pp.all` token diffing shows its `Eq.rec` MOTIVE
        -- closes at `(stdTower x).carrier` (ENTRY level) with the
        -- `HSMul.hSMul` OUTSIDE, i.e. it is `hcastAB ▸ ((n • W2)
        -- Chat.2 Dhat.2)`: the smul AND entry-application both
        -- happen BEFORE the cast, contrary to every previous
        -- attempt's assumption. Build the matching ENTRY-level
        -- identity directly via `Matrix.smul_apply` (safe here,
        -- since `W2` is fully opaque with no `gtensor`/provenance
        -- baggage) BEFORE invoking `castTransportSmul1`.
        have hW2entry : ((((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
              * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) • W2) Chat.2 Dhat.2
            = (((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
                * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) • (W2 Chat.2 Dhat.2) :=
          Matrix.smul_apply _ W2 Chat.2 Dhat.2
        exact castTransportSmul1' hcastAB
          (((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
            * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ))
          (((((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
              * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ)) • W2) Chat.2 Dhat.2)
          (W2 Chat.2 Dhat.2) hW2entry
    · exact absurd hgate hgate2
  · rw [Matrix.diagonal_apply_ne _ hgate]
    simp only [Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with hgate2
    · exact absurd hgate2 hgate
    · refine Eq.trans ?_ (congrArg
        (fun v => ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ) •
          ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ) • v)
        (key (show a + b + (c + d) = a + b + c + d by ring)
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (fuseSize a b).1 (fuseSize a b).2 A B
          ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
            (sumFinCast (castR_clC a b c d).symm C)).2
          ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
            (sumFinCast (castR_clC a b c d).symm D)).2).symm)
      rw [smul_zero, smul_zero]
      exact key (show a + b + (c + d) = a + b + c + d by ring)
        (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
        (fuseSize a b).1 (fuseSize a b).2 A B Chat.2 Dhat.2

/-- Standalone extraction of `CORE`'s `hN` case (the `1 ᵍ⊗ N₀`
generator, `γ`-slot only) into a top-level lemma with a fresh local
context, mirroring `F35`/`G13`'s agreement on `includeRight ... N₀`. -/
private theorem CORE_right (a b c d : ZMod 8)
    (N₀ : ((stdTower (K := K) (c + d)).matrixSuper (fuseSize c d).1
      (fuseSize c d).2).carrier) :
    F35 (K := K) a b c d
      (includeRight (((stdTower (K := K) (a + b)).matrixSuper
          (fuseSize a b).1 (fuseSize a b).2).grading)
        (((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading) N₀)
    = G13 (K := K) a b c d
      (includeRight (((stdTower (K := K) (a + b)).matrixSuper
          (fuseSize a b).1 (fuseSize a b).2).grading)
        (((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading) N₀) := by
  rw [includeRight_apply, F35_eq, G13_eq]
  have hRN1test : (matrixSuperGtensor (stdTower (K := K) (a + b))
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2) (fuseSize a b).1
        (fuseSize a b).2).toAlgEquiv
      ((1 : ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).carrier) ᵍ⊗ₜ[K] N₀)
    = matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
        (stdTower (K := K) (a + b)).grading
        ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N₀ :=
    matrixSuperGtensor_one_tmulB (fuseSize a b).1 (fuseSize a b).2 N₀
  have hL1' : (matrixSuperGtensorRight
        ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2)
        (stdTower (c + d)) (fuseSize c d).1
        (fuseSize c d).2).toAlgEquiv
      ((1 : ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).carrier) ᵍ⊗ₜ[K] N₀)
    = Matrix.map (N₀ : Matrix (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2)
        (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2) (stdTower (K := K) (c + d)).carrier)
        (fun z => toCB ((1 : ((stdTower (K := K) (a + b)).matrixSuper
            (fuseSize a b).1 (fuseSize a b).2).carrier) ᵍ⊗ₜ[K] z)) :=
    matrixSuperGtensorRight_one_tmulB (fuseSize c d).1 (fuseSize c d).2 N₀
  rw [hL1']
  have hL2' : ((matrixSuperGtensor (stdTower (K := K) (a + b))
          (stdTower (c + d)) (fuseSize a b).1
          (fuseSize a b).2).matrixSuper
          (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
      (Matrix.map (N₀ : Matrix (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2)
          (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2) (stdTower (K := K) (c + d)).carrier)
          (fun z => toCB ((1 : ((stdTower (K := K) (a + b)).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).carrier) ᵍ⊗ₜ[K] z)))
      = Matrix.map (N₀ : Matrix (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2)
          (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2) (stdTower (K := K) (c + d)).carrier)
          (fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
            (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z) := by
    refine Matrix.ext fun r s => ?_
    rw [matrixSuper_applyB, Matrix.map_apply, Matrix.map_apply]
    exact matrixSuperGtensor_one_tmulB (fuseSize a b).1 (fuseSize a b).2 (N₀ r s)
  rw [hL2']
  have hN0eq : (N₀ : Matrix (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2)
      (Fin (fuseSize c d).1 ⊕ Fin (fuseSize c d).2)
      (stdTower (K := K) (c + d)).carrier)
    = toRawMatrixB (fuseSize c d).1 (fuseSize c d).2 N₀ := rfl
  rw [hN0eq]
  generalize hN0 : toRawMatrixB (fuseSize c d).1 (fuseSize c d).2 N₀ = N
  have hRN1 := matrixSuperGtensor_one_tmulB (P := stdTower (K := K) (a + b))
    (Q := (stdTower (c + d)).matrixSuper (fuseSize c d).1 (fuseSize c d).2)
    (fuseSize a b).1 (fuseSize a b).2 N
  have hRN2 := matrixSuper_diagonal_add_zsmulB
    (matrixSuperGtensorRight (stdTower (K := K) (a + b)) (stdTower (c + d))
      (fuseSize c d).1 (fuseSize c d).2)
    (fuseSize a b).1 (fuseSize a b).2
    (fun _ : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
      toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
        evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading N))
    (fun _ : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
      toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
        oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading N))
    (fun s => ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 s) : ℤˣ) : ℤ))
  have hRN1eq : matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
      (stdTower (K := K) (a + b)).grading
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading N
    = Matrix.diagonal (fun s : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
        toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
            evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading N)
          + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 s) : ℤˣ) : ℤ) •
            toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
              oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N)) := rfl
  have hRN2' := (congrArg
    ((matrixSuperGtensorRight (stdTower (K := K) (a + b)) (stdTower (c + d))
      (fuseSize c d).1 (fuseSize c d).2).matrixSuper
      (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
    hRN1eq).trans hRN2
  have hRN3 := (congrArg
    ((matrixSuperGtensorRight (stdTower (K := K) (a + b)) (stdTower (c + d))
      (fuseSize c d).1 (fuseSize c d).2).matrixSuper
      (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
    hRN1).trans hRN2'
  have hRNevX := matrixSuperGtensorRight_one_tmulB (fuseSize c d).1 (fuseSize c d).2
    (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
      (fuseSize c d).2).grading N) (P := stdTower (K := K) (a + b))
  have hRNodX := matrixSuperGtensorRight_one_tmulB (fuseSize c d).1 (fuseSize c d).2
    (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
      (fuseSize c d).2).grading N) (P := stdTower (K := K) (a + b))
  have hRN4target : (Matrix.diagonal fun t : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
        (matrixSuperGtensorRight (stdTower (K := K) (a + b)) (stdTower (c + d))
            (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
            (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
              evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N))
          + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 t) : ℤˣ) : ℤ) •
            (matrixSuperGtensorRight (stdTower (K := K) (a + b)) (stdTower (c + d))
                (fuseSize c d).1 (fuseSize c d).2).toAlgEquiv
              (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2).grading N)))
    = Matrix.diagonal (fun t : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
        Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
              ᵍ⊗ₜ[K] z))
          + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 t) : ℤˣ) : ℤ) •
            Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                  ᵍ⊗ₜ[K] z))) := by
    refine Matrix.ext fun t u => ?_
    by_cases htu : t = u
    · subst htu
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hRNevX, hRNodX]
      rfl
    · rw [Matrix.diagonal_apply_ne _ htu, Matrix.diagonal_apply_ne _ htu]
      rfl
  have hRN4 := hRN3.trans hRN4target
  have hRN5 := matrixSuper_diagonal_add_zsmulB
    ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1 (fuseSize c d).2)
    (fuseSize a b).1 (fuseSize a b).2
    (fun t : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
      Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
            ᵍ⊗ₜ[K] z)))
    (fun t : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
      Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
            ᵍ⊗ₜ[K] z)))
    (fun t => ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 t) : ℤˣ) : ℤ))
  have hRN6 := (congrArg
    (((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).matrixSuper (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
    hRN4).trans hRN5
  have hRNcomp := congrArg
    ((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
    hRN6
  have hRNcast := congrArg ((stdMatrixCast (add_assoc (a + b) c d).symm
      (castR_clC a b c d)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).toAlgEquiv hRNcomp
  have hRNtail := congrArg (cluster13SharedTail a b c d).toAlgEquiv hRNcast
  have hRNfull := congrArg (· * swapSign (K := K) a b c d)
    (congrArg (swapSign (K := K) a b c d * ·) hRNtail)
  refine Matrix.ext fun i j => ?_
  have hRNentry := congrFun (congrFun hRNfull i) j
  refine Eq.trans ?_ hRNentry.symm
  rw [cluster35SharedTail_entry, mul_swapSign_applyC, swapSign_mul_applyC,
    cluster13SharedTail_entry]
  have hdecRi := decR_phi a b c d (swapIdx35C a b c d i)
  have hdecRj := decR_phi a b c d (swapIdx35C a b c d j)
  rw [phi_involC K a b c d i] at hdecRi
  rw [phi_involC K a b c d j] at hdecRj
  have hdecRi2 : (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
        (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
      (cleanDec35 a b c d i)
    = ((((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1
            (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (swapCast_clC a b c d)
            (cleanDecL (fuseSize (a + b + c) d).1
              (fuseSize (a + b + c) d).2
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
              (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).2)).1,
        sumFinCast (sizeR_flat_eq_35C a b c d)
          (sumFinCast (swapCast_35C a b c d)
            (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
              ((cleanDecL (fuseSize (a + b + c) d).1
                  (fuseSize (a + b + c) d).2
                  (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                  (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).1,
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1
                    (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (swapCast_clC a b c d)
                    (cleanDecL (fuseSize (a + b + c) d).1
                      (fuseSize (a + b + c) d).2
                      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                      (fuseSize a b).1 (fuseSize a b).2
                      (swapIdx35C a b c d i)).2)).2))))) := by
    rw [hdecRi]
    exact collapseIndexEquiv_symm_sumFinCast_collapse (fuseSize c d).1 (fuseSize c d).2
      (sizeR_flat_eq_35C a b c d) (cluster35Size_eqC a b c d) _
  have hdecRj2 : (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
        (sizeL a b (c + d)).1 (sizeL a b (c + d)).2).symm
      (cleanDec35 a b c d j)
    = ((((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1
            (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (swapCast_clC a b c d)
            (cleanDecL (fuseSize (a + b + c) d).1
              (fuseSize (a + b + c) d).2
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
              (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).2)).1,
        sumFinCast (sizeR_flat_eq_35C a b c d)
          (sumFinCast (swapCast_35C a b c d)
            (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
              (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
              ((cleanDecL (fuseSize (a + b + c) d).1
                  (fuseSize (a + b + c) d).2
                  (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                  (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).1,
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1
                    (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (swapCast_clC a b c d)
                    (cleanDecL (fuseSize (a + b + c) d).1
                      (fuseSize (a + b + c) d).2
                      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
                      (fuseSize a b).1 (fuseSize a b).2
                      (swapIdx35C a b c d j)).2)).2))))) := by
    rw [hdecRj]
    exact collapseIndexEquiv_symm_sumFinCast_collapse (fuseSize c d).1 (fuseSize c d).2
      (sizeR_flat_eq_35C a b c d) (cluster35Size_eqC a b c d) _
  rw [hdecRi2, hdecRj2]
  set A := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).1
    with hAdef
  set B := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).1
    with hBdef
  set C := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d i)).2
    with hCdef
  set D := (cleanDecL (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2 (swapIdx35C a b c d j)).2
    with hDdef
  set Chat := (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
      (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
      (sumFinCast (swapCast_clC a b c d) C)
    with hChatdef
  set Dhat := (collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
      (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
      (sumFinCast (swapCast_clC a b c d) D)
    with hDhatdef
  have hRNAB := matrixSuper_applyB
    (stdMatrixCast (add_assoc (a + b) c d).symm (castR_clC a b c d))
    (fuseSize a b).1 (fuseSize a b).2
    (((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      (Matrix.diagonal (fun t : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
          ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv
            (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                  ᵍ⊗ₜ[K] z)))
            + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 t) : ℤˣ) : ℤ) •
              ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2).toAlgEquiv
                (Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                    (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                      ᵍ⊗ₜ[K] z))))))
    A B
  rw [hRNAB]
  have hRNcastEntry := stdMatrixCast_entryC (add_assoc (a + b) c d).symm
    (castR_clC a b c d)
    ((((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      (Matrix.diagonal (fun t : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
          ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv
            (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                  ᵍ⊗ₜ[K] z)))
            + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 t) : ℤˣ) : ℤ) •
              ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2).toAlgEquiv
                (Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                    (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                      ᵍ⊗ₜ[K] z))))) A B))
    C D
  have hRNAB2 := matrixSuper_applyB
    (matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2)
    (fuseSize a b).1 (fuseSize a b).2
    (Matrix.diagonal (fun t : Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2 =>
        ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).toAlgEquiv
          (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                ᵍ⊗ₜ[K] z)))
          + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 t) : ℤˣ) : ℤ) •
            ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).toAlgEquiv
              (Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                    ᵍ⊗ₜ[K] z)))))
    A B
  rw [hRNcastEntry, hRNAB2, matrixSuperComp_entryC]
  have hLNAB2 := matrixSuper_applyB
    (matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2)
    (fuseSize c d).1 (fuseSize c d).2
    ((((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).toAlgEquiv
      (N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
        (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z))
    Chat.1 Dhat.1
  have hLNAB3 := matrixSuperComp_entryC (P := stdTower (K := K) (a + b + (c + d)))
    (fuseSize a b).1 (fuseSize a b).2
    (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
    ((((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).toAlgEquiv
      (N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
        (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
      Chat.1 Dhat.1)
    (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (A, Chat.2))
    (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (B, Dhat.2))
  have hEsimp : sumFinCast (sizeR_flat_eq_35C a b c d)
        (sumFinCast (swapCast_35C a b c d)
          (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
            (A, Chat.2)))
      = collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (A, Chat.2) := by
    rw [sumFinCast_trans]
    exact sumFinCast_rfl_eq_id _ _
  have hFsimp : sumFinCast (sizeR_flat_eq_35C a b c d)
        (sumFinCast (swapCast_35C a b c d)
          (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
            (B, Dhat.2)))
      = collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (B, Dhat.2) := by
    rw [sumFinCast_trans]
    exact sumFinCast_rfl_eq_id _ _
  have hLNAB4unsimp := congrFun (congrFun hLNAB2
    (sumFinCast (sizeR_flat_eq_35C a b c d)
      (sumFinCast (swapCast_35C a b c d)
        (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (A, Chat.2)))))
    (sumFinCast (sizeR_flat_eq_35C a b c d)
      (sumFinCast (swapCast_35C a b c d)
        (collapseIndexEquiv (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2
          (B, Dhat.2))))
  have hLNAB4simp := congrArg₂
    ((matrixSuperComp (stdTower (K := K) (a + b + (c + d)))
          (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) (c + d)).1
          (fuseSize (a + b) (c + d)).2).toAlgEquiv
      ((((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
            (fuseSize a b).2).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv
        (N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
          (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
        Chat.1 Dhat.1))
    hEsimp hFsimp
  have hLNAB4 := hLNAB4unsimp.trans hLNAB4simp
  have hLNAB5 := hLNAB4.trans hLNAB3
  set hcastAB : a + b + (c + d) = a + b + c + d := by ring with hcastAB_def
  have hLNcast := congrArg (fun x => hcastAB ▸ x) hLNAB5
  refine hLNcast.trans ?_
  simp only [Equiv.symm_apply_apply]
  by_cases hgateAB : A = B
  · rw [hgateAB, Matrix.diagonal_apply_eq]
    have hLvalInner : (N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
          (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
        Chat.1 Dhat.1 B B
      = toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
            evenPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1))
          + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
            toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
              oddPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1)) := by
      rw [Matrix.map_apply, matrixInclRight_apply, sdiag, Matrix.diagonal_apply_eq]
      rfl
    have hLvalOuter := matrixSuper_applyB
      (((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2)) (fuseSize c d).1 (fuseSize c d).2
      (N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
          (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
      Chat.1 Dhat.1
    have hLvalAB := matrixSuper_applyB
      (stdFuse (K := K) (a + b) (c + d))
      (fuseSize a b).1 (fuseSize a b).2
      ((N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
          (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
        Chat.1 Dhat.1)
      B B
    have hLvalOuterAB := congrFun (congrFun hLvalOuter B) B
    have hLval := (hLvalOuterAB.trans hLvalAB).trans
      (congrArg (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv hLvalInner)
    rw [map_add, map_zsmul] at hLval
    have hLvalEntry := congrFun (congrFun hLval Chat.2) Dhat.2
    have hLval2 := congrArg (fun v => hcastAB ▸ v) hLvalEntry
    refine hLval2.trans ?_
    -- Bridge the RHS's `(stdFuse.matrixSuper(fuseSize c d)).toAlgEquiv(Matrix.map ...) `
    -- entries (via `matrixSuperComp_entryC`'s 4-index split) down to plain
    -- `stdFuse.toAlgEquiv(toCB(1 ⊗ (evenPart/oddPart N) at the SAME two
    -- outer indices))`, using `matrixSuper_applyB`/`Matrix.map_apply`
    -- entrywise (mirrors `hRNAB`'s own construction, now run "backwards"
    -- against the entry-extracted goal).
    have hbridgeEv := (matrixSuper_applyB (stdFuse (K := K) (a + b) (c + d))
        (fuseSize c d).1 (fuseSize c d).2
        (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
              ᵍ⊗ₜ[K] z)))
        ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (castR_clC a b c d).symm C)).1
        ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (castR_clC a b c d).symm D)).1).trans
      (congrArg (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
        (rfl : (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N)
              (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K] z)))
            ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
              (sumFinCast (castR_clC a b c d).symm C)).1
            ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
              (sumFinCast (castR_clC a b c d).symm D)).1
          = toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
              (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N)
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (castR_clC a b c d).symm C)).1
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (castR_clC a b c d).symm D)).1)))
    have hbridgeOd := (matrixSuper_applyB (stdFuse (K := K) (a + b) (c + d))
        (fuseSize c d).1 (fuseSize c d).2
        (Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
              ᵍ⊗ₜ[K] z)))
        ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (castR_clC a b c d).symm C)).1
        ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
            (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
          (sumFinCast (castR_clC a b c d).symm D)).1).trans
      (congrArg (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
        (rfl : (Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N)
              (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K] z)))
            ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
              (sumFinCast (castR_clC a b c d).symm C)).1
            ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
              (sumFinCast (castR_clC a b c d).symm D)).1
          = toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
              (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N)
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (castR_clC a b c d).symm C)).1
                ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
                    (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
                  (sumFinCast (castR_clC a b c d).symm D)).1)))
    have hCC1 : ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
        (sumFinCast (castR_clC a b c d).symm C)).1 = Chat.1 := rfl
    have hDD1 : ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
        (sumFinCast (castR_clC a b c d).symm D)).1 = Dhat.1 := rfl
    have hCC2 : ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
        (sumFinCast (castR_clC a b c d).symm C)).2 = Chat.2 := rfl
    have hDD2 : ((collapseIndexEquiv (fuseSize c d).1 (fuseSize c d).2
          (fuseSize (a + b) (c + d)).1 (fuseSize (a + b) (c + d)).2).symm
        (sumFinCast (castR_clC a b c d).symm D)).2 = Dhat.2 := rfl
    rw [hCC1, hDD1] at hbridgeEv hbridgeOd
    rw [Matrix.map_apply] at hbridgeEv hbridgeOd
    have hsignA' : swapParity35C a b c d i
        = sumParity (fuseSize a b).1 (fuseSize a b).2 A
          * sumParity (fuseSize c d).1 (fuseSize c d).2 Chat.1 :=
      swapParity35C_factor K a b c d i
    have hsignB' : swapParity35C a b c d j
        = sumParity (fuseSize a b).1 (fuseSize a b).2 B
          * sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1 :=
      swapParity35C_factor K a b c d j
    have hABeq : sumParity (fuseSize a b).1 (fuseSize a b).2 A
        = sumParity (fuseSize a b).1 (fuseSize a b).2 B := by
      rw [hgateAB]
    have hsumsign : swapParity35C a b c d i + swapParity35C a b c d j
        = sumParity (fuseSize a b).1 (fuseSize a b).2 B
          * (sumParity (fuseSize c d).1 (fuseSize c d).2 Chat.1
            + sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1) := by
      rw [hsignA', hsignB', hABeq]
      ring
    have hsgnmul : ((sgn (swapParity35C a b c d i
          + swapParity35C a b c d j) : ℤˣ) : ℤ)
        = ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
          * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ) := by
      rw [← Units.val_mul, ← sgn_add, add_comm]
    have hfinalPre : ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv
        (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
              ᵍ⊗ₜ[K] z))
          + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
            Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                  ᵍ⊗ₜ[K] z)))
        Chat.1 Dhat.1
      = (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
          (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
              (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N) Chat.1 Dhat.1))
          + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
              (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                  (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                    (fuseSize c d).2).grading N) Chat.1 Dhat.1)) := by
      rw [matrixSuper_applyB, Matrix.add_apply, Matrix.smul_apply, map_add, map_zsmul,
        Matrix.map_apply, Matrix.map_apply]
    have hfinalPreM := congrFun (congrFun hfinalPre Chat.2) Dhat.2
    -- Matches the AMBIENT goal's actual shape: `matrixSuper.toAlgEquiv`
    -- distributed over the OUTER sum BEFORE any index application (not
    -- `hfinalPre`'s shape, which distributes only at the `stdFuse`
    -- level, i.e. AFTER `Chat.1 Dhat.1` is applied). Stated at the
    -- MATRIX level (no `Chat.1 Dhat.1` applied at all) so
    -- `Matrix.add_apply`/`Matrix.smul_apply` fire cleanly without the
    -- extra trailing `Chat.2 Dhat.2` applications confusing `rw`'s
    -- arity matching.
    have hfinalPreM2 : ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv
        (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
              ᵍ⊗ₜ[K] z)))
      + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
          ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).toAlgEquiv
            (Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                  ᵍ⊗ₜ[K] z)))
      = ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).toAlgEquiv
          (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                ᵍ⊗ₜ[K] z))
            + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
              Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
                  (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                    ᵍ⊗ₜ[K] z))) := by
      have := map_add ((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize c d).1
          (fuseSize c d).2).toAlgEquiv
        (Matrix.map (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
              ᵍ⊗ₜ[K] z)))
        (((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
          Matrix.map (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading N) (fun z => toCB ((1 : (stdTower (K := K) (a + b)).carrier)
                ᵍ⊗ₜ[K] z)))
      rw [map_zsmul] at this
      exact this.symm
    have hfinalPreM2' := congrFun (congrFun
      (congrFun (congrFun hfinalPreM2 Chat.1) Dhat.1) Chat.2) Dhat.2
    by_cases hpar : sumParity (fuseSize c d).1 (fuseSize c d).2 Chat.1
        + sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1 = 0
    · have hEvEq : (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) Chat.1 Dhat.1
          = evenPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1) := by
        rw [evenPart_matrixSuper_apply, if_pos hpar]
      have hOdEq : (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) Chat.1 Dhat.1
          = oddPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1) := by
        rw [oddPart_matrixSuper_apply, if_pos hpar]
      rw [show swapParity35C a b c d i + swapParity35C a b c d j = 0 by
        rw [hsumsign, hpar, mul_zero]] at hsgnmul
      have hsgnmul' : ((sgn (swapParity35C a b c d j) : ℤˣ) : ℤ)
          * ((sgn (swapParity35C a b c d i) : ℤˣ) : ℤ) = 1 := by
        rw [← hsgnmul, sgn_zero, Units.val_one]
      rw [hCC1, hDD1, hCC2, hDD2, ← hEvEq, ← hOdEq, ← (hfinalPreM2'.trans hfinalPreM),
        smul_smul, hsgnmul', one_smul]
    · have hppar : sumParity (fuseSize c d).1 (fuseSize c d).2 Chat.1
          + sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1 = 1 := by
        rcases zmod2_cases (sumParity (fuseSize c d).1 (fuseSize c d).2 Chat.1
            + sumParity (fuseSize c d).1 (fuseSize c d).2 Dhat.1) with h | h
        · exact absurd h hpar
        · exact h
      have hEvEq : (evenPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) Chat.1 Dhat.1
          = oddPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1) := by
        rw [evenPart_matrixSuper_apply, if_neg (by rw [hppar]; decide)]
      have hOdEq : (oddPart ((stdTower (c + d)).matrixSuper (fuseSize c d).1
            (fuseSize c d).2).grading N) Chat.1 Dhat.1
          = evenPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1) := by
        rw [oddPart_matrixSuper_apply, if_neg (by rw [hppar]; decide)]
      rw [show swapParity35C a b c d i + swapParity35C a b c d j
            = sumParity (fuseSize a b).1 (fuseSize a b).2 B by
          rw [hsumsign, hppar, mul_one]] at hsgnmul
      rw [hCC1, hDD1, hCC2, hDD2]
      have hW2entry : ((((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ)) •
            ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                    oddPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1)))
              + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
                (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                  (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                    evenPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1)))))
          = ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                    evenPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1)))
              + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
                (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                  (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                    oddPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1)))) := by
        rw [smul_add, smul_smul, show ((sgn (sumParity (fuseSize a b).1
            (fuseSize a b).2 B) : ℤˣ) : ℤ)
            * ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) = 1 by
          rw [← Units.val_mul, sgn_mul_self', Units.val_one], one_smul]
        exact add_comm _ _
      rw [← hW2entry]
      generalize hXgen : ((stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
              (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                  oddPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1)))
            + ((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ) •
              (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv
                (toCB ((1 : (stdTower (K := K) (a + b)).carrier) ᵍ⊗ₜ[K]
                  evenPart (stdTower (K := K) (c + d)).grading (N Chat.1 Dhat.1))))
        = X'
      have hX'entry : ((((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ)) •
            X') Chat.2 Dhat.2
          = (((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ)) •
            (X' Chat.2 Dhat.2) :=
        Matrix.smul_apply _ X' Chat.2 Dhat.2
      refine Eq.trans (castTransportSmul1' hcastAB
        (((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ))
        (((((sgn (sumParity (fuseSize a b).1 (fuseSize a b).2 B) : ℤˣ) : ℤ)) •
            X') Chat.2 Dhat.2)
        (X' Chat.2 Dhat.2) hX'entry) ?_
      rw [← hXgen, ← hOdEq, ← hEvEq, ← (hfinalPreM2'.trans hfinalPreM), smul_smul, hsgnmul]
  · rw [Matrix.diagonal_apply_ne _ hgateAB]
    have hLzeroInner : (N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
          (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
        Chat.1 Dhat.1 A B
      = 0 := by
      rw [Matrix.map_apply, matrixInclRight_apply, sdiag, Matrix.diagonal_apply_ne _ hgateAB]
    have hLzeroOuter := matrixSuper_applyB
      (((stdFuse (K := K) (a + b) (c + d)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2)) (fuseSize c d).1 (fuseSize c d).2
      (N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
          (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
      Chat.1 Dhat.1
    have hLzeroAB := matrixSuper_applyB
      (stdFuse (K := K) (a + b) (c + d))
      (fuseSize a b).1 (fuseSize a b).2
      ((N.map fun z => matrixInclRight (sumParity (fuseSize a b).1 (fuseSize a b).2)
          (stdTower (K := K) (a + b)).grading (stdTower (K := K) (c + d)).grading z)
        Chat.1 Dhat.1)
      A B
    have hLzeroOuterAB := congrFun (congrFun hLzeroOuter A) B
    have hLzero := (hLzeroOuterAB.trans hLzeroAB).trans
      ((congrArg (stdFuse (K := K) (a + b) (c + d)).toAlgEquiv hLzeroInner).trans (map_zero _))
    have hLzeroEntry := congrFun (congrFun hLzero Chat.2) Dhat.2
    have hLzero2 := congrArg (fun v => hcastAB ▸ v) hLzeroEntry
    refine hLzero2.trans ?_
    have keyEntry2 : ∀ {x y : ZMod 8} (h : x = y) (p q : ℕ)
        (t u : Fin p ⊕ Fin q),
        (h ▸ ((0 : ((stdTower (K := K) x).matrixSuper p q).carrier)
          t u) : (stdTower (K := K) y).carrier)
        = (0 : (stdTower (K := K) y).carrier) := by
      intro x y h p q t u
      subst h
      rfl
    have keyEntry4 : ∀ {x y : ZMod 8} (h : x = y) (p q p' q' : ℕ)
        (r s : Fin p' ⊕ Fin q') (t u : Fin p ⊕ Fin q),
        (h ▸ ((0 : (((stdTower (K := K) x).matrixSuper p q).matrixSuper p' q').carrier)
          r s t u) : (stdTower (K := K) y).carrier)
        = (0 : (stdTower (K := K) y).carrier) := by
      intro x y h p q p' q' r s t u
      subst h
      rfl
    rw [keyEntry2 hcastAB (fuseSize (a + b) (c + d)).1
      (fuseSize (a + b) (c + d)).2 Chat.2 Dhat.2]
    symm
    rw [keyEntry4]
    rw [smul_zero, smul_zero]

private theorem CORE (a b c d : ZMod 8)
    (u : (((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).gtensor
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2)).carrier) :
    (cluster35SharedTail a b c d).toAlgEquiv
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
                  (fuseSize c d).2).toAlgEquiv u))))
      = swapSign a b c d
        * (cluster13SharedTail a b c d).toAlgEquiv
          (((stdMatrixCast (add_assoc (a + b) c d).symm
                (castR_clC a b c d)).matrixSuper (fuseSize a b).1
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
                      (fuseSize a b).2).toAlgEquiv u)))))
        * swapSign a b c d := by
  rw [← F35_eq, ← G13_eq]
  have key : F35 (K := K) a b c d = G13 (K := K) a b c d := by
    refine galgHom_ext
      (𝒜 := ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).grading)
      (ℬ := ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).grading) ?_
    intro M₀ N₀
    -- goal here: agreement of `F35`/`G13` on the pure tensor generator
    -- `M₀ ᵍ⊗ N₀`; split via `includeLeft_mul_includeRight` into the
    -- `gM`/`gN` cases and compute each side entrywise.
    rw [← includeLeft_mul_includeRight
      ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).grading
      ((stdTower (c + d)).matrixSuper (fuseSize c d).1
        (fuseSize c d).2).grading M₀ N₀,
      map_mul, map_mul]
    have hM : F35 (K := K) a b c d
          (includeLeft (((stdTower (K := K) (a + b)).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).grading)
            (((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading) M₀)
        = G13 (K := K) a b c d
          (includeLeft (((stdTower (K := K) (a + b)).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).grading)
            (((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading) M₀) :=
      CORE_left a b c d M₀
    have hN : F35 (K := K) a b c d
          (includeRight (((stdTower (K := K) (a + b)).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).grading)
            (((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading) N₀)
        = G13 (K := K) a b c d
          (includeRight (((stdTower (K := K) (a + b)).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).grading)
            (((stdTower (c + d)).matrixSuper (fuseSize c d).1
              (fuseSize c d).2).grading) N₀) :=
      CORE_right a b c d N₀
    exact congrArg₂ (· * ·) hM hN
  exact AlgHom.congr_fun key u

/-! ### Stage C/D: the closing theorems of the e35 edge -/

/-- **STEP C**: the signed factorization of the `(cd)`-cluster
composite `cluster35Tail3 ∘ cluster35Prefix` through the `(ab)`-cluster
route `quadRoute3`, conjugated by the signed swap unit `swapSign`.
Assembled from the landed bifusion reductions `tail3_prefix_eq` /
`quadRoute3_prefix_eq` (which factor both sides through their
respective shared tails on the common generator
`u := ((stdFuse a b).gtensorCongr (stdFuse c d)).toAlgEquiv
  ((gtensorAssoc _ _ _).toAlgEquiv w)`) and the now sorry-free `CORE`
(which compares the two shared-tail values of `u` up to `swapSign`
conjugation), plus `stdMatrixCast_symm_entry`-style equalities
identifying `castR_clC`/`add_assoc` with the landed `castR_cl` (both
proofs of the identical proposition, hence interchangeable by proof
irrelevance). -/
theorem quadRoute3_factor35_signed (a b c d : ZMod 8) :
    ∀ w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier,
      (cluster35Tail3 a b c d).toAlgEquiv
        ((cluster35Prefix a b c d).toAlgEquiv w)
      = swapSign a b c d * (quadRoute3 a b c d).toAlgEquiv w
        * swapSign a b c d := by
  intro w
  rw [tail3_prefix_eq, quadRoute3_prefix_eq]
  exact CORE a b c d
    (((stdFuse a b).gtensorCongr (stdFuse c d)).toAlgEquiv
      ((gtensorAssoc ((stdTower (K := K) a).gtensor (stdTower b))
          (stdTower c) (stdTower d)).toAlgEquiv w))

/-- **STEP D**: the `edgeT35`-intertwining of `(alignedRoute5,
quadRoute3)` at the pentagon frame, obtained from the landed
pre-swap intertwiner `edge35Core_intertwines` by post-composing with
`quadRoute3_factor35_signed` (rewriting the `(cluster35Tail3 ∘
cluster35Prefix)`-factor) and cancelling the resulting `swapSign ·
swapSign = 1` via `swapSign_mul_self`, using `edgeT35 := edge35Core *
swapSign`. -/
theorem edgeT35_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (alignedRoute5 a b c d).toAlgEquiv w * edgeT35 a b c d
        = ((sgn (j * pentagonParity (K := K) a b (c + d)) : ℤˣ) : ℤ) •
          (edgeT35 a b c d * (quadRoute3 a b c d).toAlgEquiv w) := by
  intro j w hw
  have h1 := edge35Core_intertwines a b c d hw
  rw [quadRoute3_factor35_signed a b c d w] at h1
  -- `edge35Core` is `private` to `PentagonEdge35.lean`, so it cannot be
  -- named here; the closing algebra is proved GENERICALLY over an
  -- opaque `E : (stdTower (a+b+c+d)).matrixSuper _ _ .carrier` (whose
  -- value Lean unifies with `edge35Core a b c d` automatically when
  -- this generic fact is applied to `h1`, whose type already contains
  -- that private term). `edgeT35 = E * swapSign` is supplied as a
  -- HYPOTHESIS `hE` rather than unfolded by name.
  have key : ∀ (E : ((stdTower (K := K) (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2).carrier),
      (alignedRoute5 a b c d).toAlgEquiv w * E
        = ((sgn (j * pentagonParity (K := K) a b (c + d)) : ℤˣ) : ℤ) •
          (E * (swapSign a b c d * (quadRoute3 a b c d).toAlgEquiv w
            * swapSign a b c d)) →
      (alignedRoute5 a b c d).toAlgEquiv w * (E * swapSign a b c d)
        = ((sgn (j * pentagonParity (K := K) a b (c + d)) : ℤˣ) : ℤ) •
          ((E * swapSign a b c d) * (quadRoute3 a b c d).toAlgEquiv w) := by
    intro E hE'
    rw [show (alignedRoute5 a b c d).toAlgEquiv w * (E * swapSign a b c d)
          = ((alignedRoute5 a b c d).toAlgEquiv w * E) * swapSign a b c d
        from (mul_assoc _ _ _).symm, hE', smul_mul_assoc,
      show E * (swapSign a b c d * (quadRoute3 a b c d).toAlgEquiv w
            * swapSign a b c d) * swapSign a b c d
          = E * swapSign a b c d
            * ((quadRoute3 a b c d).toAlgEquiv w
              * (swapSign a b c d * swapSign a b c d))
        by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc],
      swapSign_mul_self, mul_one]
  exact key _ h1

end CoreB

end Close

end Superfusion

/-
### Resumption notes (Stage B, in progress — session 5)

**Session 5 summary (current state)**: performed the STEP 1/STEP 2/STEP 3
refactor recommended at the end of session 4. `CORE`'s `hM` and `hN`
cases are now extracted as standalone top-level lemmas `CORE_left`
(fully closed, verbatim cut of session 4's `hM` proof) and
`CORE_right` (the `1 ᵍ⊗ N₀` case), each taking `a b c d` and `M₀`/`N₀`
as explicit arguments with a FRESH local context — this eliminated the
`whnf` timeout that blocked `hN` at the end of session 4 (confirmed by
direct experiment: the SAME `hRN1`-style lemma application that timed
out inside `CORE`'s shared context compiles in ~10s once `hM`'s ~40
accumulated locals are no longer in scope). `CORE`'s own proof body
now reads `have hM := CORE_left a b c d M₀` / `have hN := CORE_right
a b c d N₀` and is otherwise unchanged. `CORE_right` is ~95% complete:
its LHS chain (`hL1'`/`hL2'`, `matrixSuperGtensor_one_tmulB`-based),
its RHS chain (`hRN1`-`hRNfull`, `hRNAB`-`matrixSuperComp_entryC`,
mirroring `hM`'s `hR1`-`hRentry`), the shared index-decode block
(`hdecRi`/`hdecRj`/`hdecRi2`/`hdecRj2`/the `A B C D Chat Dhat` `set`s,
copied verbatim from `hM` since it never depended on `M`/`N`), and the
LHS-side `matrixSuperComp`/`stdFuse` reduction (`hLNAB2`-`hLNAB5`,
`hcastAB`, `hLNcast`) are ALL landed and compile in ~10s. The final
`by_cases hgateAB : A = B` gate split (the `hN`-analogue of `hM`'s
`hgate`/`hpar` split, but gated on `A = B` since `matrixInclRight`'s
`sdiag` diagonal is over the OUTER `Fin (fuseSize a b)` index, unlike
`hM`'s inner-gated `Mev`/`Mod` sum) has its `neg` branch (`A ≠ B`)
FULLY CLOSED (via `hLzeroInner`/`hLzeroOuter`/`hLzeroAB`/`hLzero`/
`hLzeroEntry`/`hLzero2` then two bare `keyEntry2`/`keyEntry4` zero-
transport lemmas applied via UNQUALIFIED `rw [keyEntryN]` — letting
Lean's own unification find the right instantiation, since supplying
the indices explicitly hit a `sumFinCast`-shadowing mismatch, see
"rule 5" below). The ONE remaining `sorry` is the `pos` branch
(`hgateAB : A = B`, further split on `hpar : sumParity Chat.1 +
sumParity Dhat.1 = 0`); the `hpar`-TRUE case is ~90% built (`hLvalInner`
through `hbridgeEv`/`hbridgeOd` all compile; the sign algebra
`hsignC'`/`hsignD'`/`hsumsign`/`hsgnmul` is landed) but the FINAL
`Eq.trans`/`congrArg` stitching connecting `hLval2`'s (cast, 6-index)
shape to the RHS's (cast, 4-collapse-index) shape has NOT been
correctly assembled — every attempt so far produces a "type mismatch"
between the un-cast `hfinal` (built from `hbridgeEv`/`hbridgeOd`) and
the AMBIENT (cast + `Chat.2 Dhat.2`-applied on the left,
`(collapse C/D).1/.2`-applied on the right) goal; the missing piece is
a `congrFun`/`congrFun (at Chat.2 Dhat.2)` + `hcastAB ▸`-lift of
`hfinal` FOLLOWED BY relating the resulting `(collapse C).1`-shaped
RHS indices back to `A`/`B` (both trivially `rfl`, analogous to
`hCcast`/`hDcast` used earlier in the same branch for `Chat.1`/`Dhat.1`)
— this bridging step was attempted several times and kept failing on
`rw`-pattern-matching against the WRONG copy of a `sumFinCast`
(module-local vs. `PentagonEdge35Core`'s, per rule 5) or against
un-reduced `Matrix.map(...) i j` forms (needing an EXTRA
`rw [Matrix.map_apply]` at exactly the right point, discovered only
after a `generalize hCC1 : (collapse ...).1 = C1 at hbridgeEv
hbridgeOd` diagnostic — see "new diagnostic" below); the `hpar`-FALSE
case (mirroring `hM`'s own `hpar`-false, needing `castTransportSmul1'`)
is NOT YET STARTED. `CORE_right`'s `pos` branch is a comparably-sized
derivation to `hM`'s own `hpar`-true branch (session 4's hardest single
piece) — budget a full session for it, using the SAME `generalize`+
diagnostic technique that worked for the `neg` branch below.

**NEW diagnostic technique (session 5, generalizes rule 6)**: when a
`rw [lemma] at hyp` fails to find `lemma`'s LHS pattern inside `hyp`
even though `hyp`'s DISPLAYED type visually contains it, first try
`generalize hEq : (the suspected subterm, EXACTLY as it appears in the
goal/hyp printout) = freshVar at hyp` — if this SUCCEEDS (no "motive
is not type correct" error and `hyp`'s displayed type actually
changes), it confirms the subterm occurrence is real and `freshVar` is
now a clean handle for it; THEN derive `freshVar = target` as a
SEPARATE small lemma (e.g. via `hEq.symm.trans rfl` if the two are
defeq) and `rw` that in — this two-step "generalize, then equate the
opaque var" pattern succeeded (`hCC1`/`hDD1`/`hC1eqChat`/`hD1eqDhat` in
the `hpar`-true branch) where a direct `rw [show ... = ... from rfl]`
kept failing, apparently because the FULL nested `sumFinCast`-cast
expression's outer syntactic wrapper (built by `matrixSuperComp_entryC`
+ `.trans`-chaining through `matrixSuper_applyB`) doesn't literally
contain the naive `(collapseIndexEquiv ...).symm (sumFinCast ...)`
sub-expression as WRITTEN, even though it is provably equal to it —
`generalize` (which works up to SYNTACTIC occurrence, not defeq) is
the fastest way to confirm/deny this before spending time on a
`rw [show ... from rfl]` that will silently fail to match.

**IMPORTANT non-obvious gotcha found this session**: after using
`generalize ... at hbridgeEv hbridgeOd` to substitute `(collapse C).1`
→ `Chat.1` inside two ALREADY-`.trans`-chained hypotheses (each built
as `(matrixSuper_applyB ...).trans (congrArg ... (rfl : Matrix.map_apply
...))`), the hypothesis's DISPLAYED type reverts to using
`Matrix.map (...) (...) Chat.1 Dhat.1` (UN-reduced, i.e. the
`Matrix.map_apply`-based `rfl` fold from the ORIGINAL construction is
LOST) rather than staying in the already-folded `toCB (1 ⊗ (...) Chat.1
Dhat.1)` form — Lean's `generalize` re-elaborates/normalizes the
hypothesis type when substituting, and does NOT preserve a `rfl`-only
unfolding that was merely a matter of transparency in the original
term. The fix: re-apply `rw [Matrix.map_apply] at hbridgeEv hbridgeOd`
AGAIN immediately after the `generalize`+cast-substitution step, even
though the ORIGINAL (pre-`generalize`) construction of `hbridgeEv`
already "had" this fold.

Original session 4 material (still valid, describes `hM`'s closing and
the general `▸`/cast-timing diagnostic methodology) follows below.

Session 4 CLOSED `hM` completely (both `hpar` branches, no `sorry`
anywhere inside `hM`) after an extended investigation into the
session-3 blocker (an `Eq.rec`-motive mismatch on `hcastAB ▸ (...)`
that resisted `exact`/`show`/`convert`/`rw`/`simp` despite
byte-identical `pp.all` output).  Exactly ONE `sorry` remains in the
whole file, inside `hN` (the `1 ᵍ⊗ N₀` generator case), which is
UNSTARTED beyond `rw [hL1', hL2']` due to a genuinely SEPARATE
(non-elaboration-motive) performance blocker described below.

**Root cause of the session-3 `hM` blocker, FOUND**: the `▸` notation's
elaborator chooses a DIFFERENT motive for `h ▸ e` depending on WHETHER
`e`'s surrounding syntax is "matrix, then applied to `r s`" versus
"already fully applied to `r s`, cast the resulting entry" — these are
NOT interchangeable even when the two resulting terms print identically
via `pp.all` at default settings; the discrepancy only becomes visible
by (a) forcing FULL, non-elided `pp.all` output (`pp.maxSteps`/
`pp.deepTerms` bumped well above default) and (b) diffing the two
sides TOKEN-BY-TOKEN (a Python `kabstract`-style balanced-paren parser
was used, see "Diagnostic methodology" below) — casual visual
inspection of even quite large `pp.all` dumps missed it repeatedly
across three-plus attempts in this session alone, since the ELIDED
(`⋯`) portions hid the actual divergence point.  Concretely, for the
`CORE`/`hM` `hpar`-false branch, the AMBIENT goal's `hcastAB ▸ (n • W)
Chat.2 Dhat.2` (`W` a matrix value) is `hcastAB ▸ ((n • W) Chat.2
Dhat.2)` — smul AND entry-application BOTH happen BEFORE the cast,
casting a bare ENTRY of `(stdTower y).carrier` — NOT `(hcastAB ▸ (n •
W)) Chat.2 Dhat.2` (cast the whole matrix, apply after) as every
previous attempt (sessions 1-3, and most of session 4) assumed.

**The fix that worked**: after `generalize`-abstracting the matrix
value being cast to a FULLY OPAQUE local variable (so no
`gtensor`/`stdFuse`-provenance baggage remains attached to it — this
step, `generalize hW2 : (the exact matrix expression) = W2`, was
ITSELF only discoverable by first checking whether `generalize`
actually found an occurrence in the goal: earlier attempts to
`generalize` the OUTER `hcastAB ▸ (...)` expression silently found ZERO
occurrences and added a useless unused hypothesis, which is the tell
that the assumed term shape was wrong), the residual scalar goal
became small enough to `pp.all`-diff cleanly, revealing the true
entry-vs-matrix cast-timing distinction above.  The closing proof:
1. Prove the algebraic identity `X + n • Y = n • Y + X` at the
   PRE-CAST level via `add_comm` (no cast anywhere).
2. Lift through the cast via `congrArg (fun v => hcastAB ▸ v)`
   (matrix-level, ONE shared `hcastAB ▸`).
3. Apply `congrFun`/`congrFun` at `Chat.2 Dhat.2` (mirroring the
   `step1`/`step2` idiom used successfully in the `hgate2`-true
   sub-branch since session ≤2 — matrix-level cast, THEN
   `congrFun`/`congrFun`, NEVER the reverse order).
4. Use a NEW entry-level lemma `castTransportSmul1'` (stated with NO
   row/column indices at all, only `(stdTower x).carrier`-typed `V W`)
   to commute the outer `hcastAB ▸ (n • v)` (`v` already an ENTRY, from
   step 3) past the smul — this is the lemma whose SHAPE matches the
   AMBIENT goal's actual (entry-level-cast) structure, unlike
   `castTransportSmul1`/`castTransportSmul1M` (both matrix-level-cast,
   which is what sessions 1-3 assumed and kept failing against).

**New declarations this session** (`section CoreB`, right after
`swapParity35C_factor`/`castTransportSmul1`):
- `castTransportSmul1M` (matrix-level, no indices — `h ▸ V = n • (h ▸
  W)` as a MATRIX equality). Proven, general-purpose, but turned out
  NOT to be what `hM`'s ambient goal needed (kept for potential future
  use / documentation of the three DISTINCT cast-shapes now
  characterized).
- `castTransportSmul1'` (entry-level, no matrix/indices at all — `h ▸
  V = n • (h ▸ W)` for `V W : (stdTower x).carrier` directly). THIS is
  the one that closed `hM`'s `hpar`-false branch, via `keyM :=
  castTransportSmul1' hcastAB n ((n•W2)) W2 (Matrix.smul_apply-derived
  entry equality)`.

**Diagnostic methodology used this session** (recommended for any
future `Eq.rec`-motive mismatch in this file): (1) isolate the failing
`exact`/`rw` to a SINGLE, SMALL sub-goal (ideally with any large
opaque subterms `generalize`d to fresh variables first, to shrink the
`pp.all` dump); (2) wrap the failing tactic in
`set_option pp.all true in set_option pp.maxSteps 1000000 in
set_option pp.deepTerms true in set_option maxRecDepth 8000 in
trace_state` immediately before it, and capture the FULL (non-elided)
output to a scratch file; (3) parse the captured `@Eq.{u} type LHS RHS`
(or, for a "Type mismatch" error, the "has type"/"but is expected to
have type" blocks) with a small Python balanced-paren splitter,
normalize whitespace, tokenize on spaces, and diff the two sides
TOKEN-BY-TOKEN to find the exact first divergence — this is far more
reliable than eyeballing the (often 10,000+ line) raw dump, which
reliably hides the real divergence behind elided (`⋯`) or merely
visually-similar-but-different subterms. `generalize`'s SILENT
no-occurrence-found behavior (it just adds an unused hypothesis rather
than erroring, unlike `rw`) is itself a useful diagnostic: if a
`generalize` of the EXACT expression you believe is in the goal adds
an hypothesis that doesn't appear in the resulting goal, your assumed
term shape is wrong.

**`hN` (`1 ᵍ⊗ N₀`) status — the ONE remaining `sorry`**: LHS reduced
through `hL1'` (`matrixSuperGtensorRight_one_tmulB`) → `hL2'`
(`matrixSuperGtensor_one_tmulB` entrywise, giving `matrixInclRight`) →
`generalize hN0 : toRawMatrixB ... N₀ = N` (mirroring `hM`'s `hM0`).
The NEXT step, `hRN1` (the direct `matrixSuperGtensor_one_tmulB`
application giving the RHS's `matrixInclRight (sumParity (fuseSize
a b)) (stdTower a+b).grading Q.grading N` value — mathematically
TRIVIAL, a one-line lemma application exactly mirroring `hM`'s `hR1`)
is BLOCKED, but by a COMPLETELY DIFFERENT kind of problem than `hM`'s:
elaborating `hRN1` at this point in the proof (with `hM`'s ~40
accumulated local hypotheses/`generalize`s still in scope, since `hM`
and `hN` are sibling `have`s inside the same `CORE` proof) triggers a
`(deterministic) timeout at whnf`, confirmed to persist even under
`set_option maxHeartbeats 0` (unlimited) — a live test run for 4+
minutes of continuous CPU (2.7 GB resident) with no sign of
completing before being killed. This is a genuine SCALE/PERFORMANCE
problem, not a mismatch: `hRN1`'s STATEMENT typechecks fine in
isolation reasoning (it is exactly `matrixSuperGtensor_one_tmulB
(fuseSize a b).1 (fuseSize a b).2 N`), the cost is purely in `whnf`-ing
it against the ~40-hypothesis ambient context.

**Recommended fix for `hN`** (only remaining practical option,
NOT YET TRIED): refactor `hM` and `hN` out of `CORE`'s proof body into
two separate TOP-LEVEL `private theorem`s (e.g. `CORE_hM`, `CORE_hN`),
each taking `M₀`/`N₀` plus the shared index data (`Chat`, `Dhat`, `i`,
`j`, `C`, `D`, `A`, `B`, and whatever `Fin`/`ZMod 8` parameters they
close over) as EXPLICIT arguments, then have `CORE`'s proof body call
`exact congrArg₂ (· * ·) (CORE_hM ...) (CORE_hN ...)`. This makes
`hN`'s elaboration start from a FRESH, small local context instead of
inheriting `hM`'s ~40 accumulated locals, which should eliminate the
`whnf` blow-up. `hM`'s proof is ALREADY fully self-contained (it never
references `N₀` or anything `hN`-specific), so extracting it verbatim
as `CORE_hM` should be mechanical; `hN`'s proof (once `hRN1` no longer
times out) needs the FULL new derivation sketched in-place at the
`hN` `sorry` site (search for "`hRN1`" and "`hRN2`" comments in the
proof body above): `hRN1`→`hRN2` (push `matrixSuperGtensorRight`
through `matrixInclRight N`'s `sdiag`, gated on the OUTER `Fin (fuseSize
a b)` index rather than `hM`'s INNER `Fin (fuseSize c d)` — the
`evenPart`/`oddPart` split is on `N r s`, connected via the
already-landed `evenPart_matrixSuper_apply`/`oddPart_matrixSuper_apply`)
→ `hRN3` (push `stdFuse` through via `matrixSuper_diagonal_
add_zsmulB`) → `hRNcomp`/`hRNcast`/`hRNtail`/`hRNfull`/`hRNentry`
(term-mode `congrArg` chain through `matrixSuperComp`/`stdMatrixCast`/
`cluster13SharedTail`/`swapSign`, EXACTLY mirroring `hRcomp`-`hRentry`)
→ match the LHS via `cluster35SharedTail_entry`/`matrixSuperComp_entryC`
and an `hEsimp`/`hFsimp`-style double-`sumFinCast`-collapse (`Ê = C`/
`F̂ = D` this time). Given `matrixInclRight`'s gating is on the OUTER
index (unlike `hM`'s inner-gated `Mev`/`Mod` split), it is NOT yet
clear whether an `hpar`-style case split (`by_cases` on a parity sum)
is needed for `hN` at all — this should become apparent once `hRN2` is
built and its gate is compared against the RHS's own `Chat.1 = Dhat.1`
structure, analogous to `hM`'s `hgate` identification.

**Cumulative hard-won engineering discoveries (rules 1-5 from sessions
1-3, all still valid and were used again this session)**:
  1. Build every intermediate equality as a **term-mode `have`**
     (`congrArg e h`, `congrArg (· * c) h`, direct lemma application),
     NEVER via `rw [...]` on the ambient (both-sides-present) goal.
  2. When `rw [lemma]` fails on the ambient goal even though `lemma`
     typechecks standalone, replace it with `refine Eq.trans ?_
     h.symm` or a `congrFun`/`.trans` term chain — never `rw`. This can
     ITSELF fail if the goal's motive is already "poisoned"; the only
     reliable fix is to avoid the poisoning step in the first place.
  3. Generic helper lemmas should never name the concrete composite
     `.carrier` type directly in their own statement.
  4. `by_cases`/`Matrix.diagonal_apply_eq`/`_ne` splits on a `set`
     local do NOT `subst`; use `split_ifs`/`exact absurd` instead.
  5. Module-local `private` lemmas from `PentagonEdge35Core.lean` use
     THEIR OWN `sumFinCast` constant (shadowing this file's copy) —
     `rfl`-identical but syntactically distinct; bridge via term-mode
     `show`/construction, not `rw`.
  6. **NEW rule 6 (session 4)**: the `▸`/`Eq.rec` cast's MOTIVE depends
     on the EXACT syntactic shape of the surrounding expression at the
     point `▸` is elaborated (matrix-then-applied vs.
     applied-then-cast-the-entry are DIFFERENT, non-interchangeable
     motives even for propositionally/definitionally-equal results);
     when in doubt, use the token-diff diagnostic methodology above
     BEFORE guessing at a fix, and use `generalize`'s silent
     no-occurrence behavior to sanity-check the assumed term shape.

Stage C (`quadRoute3_factor35_signed`) and Stage D
(`edgeT35_intertwines`) are STILL NOT started (as of end of session 5);
they assemble from `CORE` (which needs `CORE_right`'s ONE remaining
`sorry`, in the `pos`/`hpar`-true branch, closed first) plus the
already-landed `tail3_prefix_eq`, `quadRoute3_prefix_eq`, and
`edge35Core_intertwines`, per the original task brief.
-/

/-
Superfusion / Super / PentagonEdge24

Milestone M7d-5b-4-iii(b), part 8': **the middle cluster edge e24**.
The triple intertwiner `pentagonT a (b+c) d` is amplified to the
`f`-matrix layer by the signed diagonal (`sdiagAmp`, M7d-5b-4-ii) and
pushed through the **shared tail** of the two cluster factorizations:

- `clusterTail2 = Ξ ≫ (routeL a (b+c) d).matrixSuper f ≫ Θ₂`,
- `clusterTail4 = Ξ ≫ (routeR a (b+c) d).matrixSuper f ≫ Θ₄`,

where `Θ₂` (the tail of `clusterTail2`) and `Θ₄` (the tail of
`clusterTail4`) are **equal as maps** — but *not* syntactically:
`Θ₂` sorts the left-split layers `(f_{a,bc}, f_{(a+bc),d})` in the
`a+(b+c)+d`-frame while `Θ₄` sorts the right-split layers
`(f_{(bc),d}, f_{a,(bc+d)})` in the `a+(b+c+d)`-frame.  Their equality
(`theta_gen`) is the remaining coherence of this milestone.  It is
proved by classifying the standard fusion sizes (`fuseSize ∈
{(1,0), (8,8)}`): in the *aligned* splits the two bridges agree by
proof irrelevance, and in the two *crossed* one-wrap splits the
composite sorting permutations agree — a kernel `decide` over the
concrete index sets (the naive `Fin.cast` bridge is false, see
`PentagonCompAssoc.lean`, but the two honest bridges coincide).

The edge `edgeT24 := Θ₂ (sdiagAmp (sumParity f) p(a,bc,d)
(pentagonT a (b+c) d))` is homogeneous of parity `p(a, b+c, d)`,
invertible, and intertwines `(quadRoute2, alignedRoute4)` — the
`routeL`-based vertex on the `φ`-side and the `routeR`-based vertex on
the `φ'`-side, matching the orientation of `pentagonT_intertwines`.
-/
import Superfusion.Super.PentagonFactor

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

section Edge24

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The standard fusion sizes take exactly two values. -/
private theorem fuseSize_cases (a b : ZMod 8) :
    fuseSize a b = (1, 0) ∨ fuseSize a b = (8, 8) := by
  unfold fuseSize
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Index identity of the shared tail's final cast (local copy of the
private `clusterIndex_eq` of `PentagonFactor.lean`). -/
private theorem clusterIndex_eq' (a b c d : ZMod 8) :
    a + (b + c) + d = a + b + c + d := by ring

/-- Size identity of the shared tail's final cast (local copy of the
private `clusterSize_eq₂` of `PentagonFactor.lean`). -/
private theorem clusterSize_eq₂' (a b c d : ZMod 8) :
    extSize (sizeR a b c) (a + (b + c)) d
      = extSize (sizeL a b c) (a + b + c) d := by
  rw [sizeL_eq_sizeR, ← add_assoc]

/-- **The shared tail** of the cluster factorizations: everything in
`clusterTail2` after the stabilized route leg — the collapse of the
`f`-matrix layer, the collapse-reassociation bridge, and the final
pentagon cast. -/
private noncomputable def clusterSharedTail (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) (a + (b + c) + d)).matrixSuper
        (sizeL a (b + c) d).1 (sizeL a (b + c) d).2).matrixSuper
        (fuseSize b c).1 (fuseSize b c).2)
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (matrixSuperComp (stdTower (a + (b + c) + d))
      (fuseSize b c).1 (fuseSize b c).2
      (sizeL a (b + c) d).1 (sizeL a (b + c) d).2).trans
    (((matrixSuperCompAssoc (stdTower (a + (b + c) + d))
        (fuseSize (a + (b + c)) d).1 (fuseSize (a + (b + c)) d).2
        (fuseSize a (b + c)).1 (fuseSize a (b + c)).2
        (fuseSize b c).1 (fuseSize b c).2).symm).trans
      (stdMatrixCast (clusterIndex_eq' a b c d)
        (clusterSize_eq₂' a b c d)))

/-! ### The bridge coherence `Θ₂ = Θ₄` -/

/-- The composite index bijection of the inverse collapse-reassociation
bridge: unpack the flat index through the outer-first grouping, then
repack it through the inner-first grouping. -/
private def assocIdx (p q p' q' p'' q'' : ℕ)
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
/-- Entry formula for the inverse collapse-reassociation bridge: a pure
reindexing along `assocIdx`. -/
private theorem matrixSuperCompAssoc_symm_entry {P : SuperAlgebra K}
    (p q p' q' p'' q'' : ℕ)
    (X : (P.matrixSuper
      (p'' * (p' * p + q' * q) + q'' * (p' * q + q' * p))
      (p'' * (p' * q + q' * p) + q'' * (p' * p + q' * q))).carrier)
    (I J : Fin ((p'' * p' + q'' * q') * p + (p'' * q' + q'' * p') * q)
      ⊕ Fin ((p'' * p' + q'' * q') * q + (p'' * q' + q'' * p') * p)) :
    (matrixSuperCompAssoc P p q p' q' p'' q'').symm.toAlgEquiv X I J
      = X (assocIdx p q p' q' p'' q'' I) (assocIdx p q p' q' p'' q'' J) :=
  rfl

/-- The crossed one-wrap sorting coincidence, index level, full
`f`-layer: sorting the left-split layers `((8,8), (1,0))` agrees with
sorting the right-split layers `((1,0), (8,8))`. -/
private theorem crossIdx8 :
    ∀ I : Fin ((8 * 8 + 8 * 8) * 1 + (8 * 8 + 8 * 8) * 0)
        ⊕ Fin ((8 * 8 + 8 * 8) * 0 + (8 * 8 + 8 * 8) * 1),
      assocIdx 1 0 8 8 8 8 I = assocIdx 8 8 1 0 8 8 I := by
  decide

/-- The crossed one-wrap sorting coincidence, index level, trivial
`f`-layer. -/
private theorem crossIdx1 :
    ∀ I : Fin ((1 * 8 + 0 * 8) * 1 + (1 * 8 + 0 * 8) * 0)
        ⊕ Fin ((1 * 8 + 0 * 8) * 0 + (1 * 8 + 0 * 8) * 1),
      assocIdx 1 0 8 8 1 0 I = assocIdx 8 8 1 0 1 0 I := by
  decide

omit [Invertible (2 : K)] in
/-- The crossed one-wrap bridge coincidence, algebra level, full
`f`-layer. -/
private theorem cross8 (P : SuperAlgebra K)
    (X : (P.matrixSuper (8 * (8 * 1 + 8 * 0) + 8 * (8 * 0 + 8 * 1))
      (8 * (8 * 0 + 8 * 1) + 8 * (8 * 1 + 8 * 0))).carrier) :
    (matrixSuperCompAssoc P 1 0 8 8 8 8).symm.toAlgEquiv X
      = (matrixSuperCompAssoc P 8 8 1 0 8 8).symm.toAlgEquiv X := by
  refine Matrix.ext fun I J => ?_
  rw [matrixSuperCompAssoc_symm_entry, matrixSuperCompAssoc_symm_entry,
    crossIdx8 I, crossIdx8 J]

omit [Invertible (2 : K)] in
/-- The crossed one-wrap bridge coincidence, algebra level, trivial
`f`-layer. -/
private theorem cross1 (P : SuperAlgebra K)
    (X : (P.matrixSuper (1 * (8 * 1 + 8 * 0) + 0 * (8 * 0 + 8 * 1))
      (1 * (8 * 0 + 8 * 1) + 0 * (8 * 1 + 8 * 0))).carrier) :
    (matrixSuperCompAssoc P 1 0 8 8 1 0).symm.toAlgEquiv X
      = (matrixSuperCompAssoc P 8 8 1 0 1 0).symm.toAlgEquiv X := by
  refine Matrix.ext fun I J => ?_
  rw [matrixSuperCompAssoc_symm_entry, matrixSuperCompAssoc_symm_entry,
    crossIdx1 I, crossIdx1 J]

omit [Invertible (2 : K)] in
/-- **The bridge coherence**: the tail of `clusterTail4` (inner cast to
the `y`-frame, right-split bridge, pentagon cast) agrees with the tail
of `clusterTail2` (left-split bridge, pentagon cast), for the standard
fusion sizes.  Proved by classifying the sizes: aligned splits agree by
proof irrelevance of the casts, crossed splits by the kernel-checked
sorting coincidence. -/
private theorem theta_gen (x y z : ZMod 8) (hyx : y = x) (hxz : x = z)
    (hyz : y = z) (u v w v' w' : ℕ × ℕ)
    (hu : u = (1, 0) ∨ u = (8, 8))
    (hv : v = (1, 0) ∨ v = (8, 8)) (hw : w = (1, 0) ∨ w = (8, 8))
    (hv' : v' = (1, 0) ∨ v' = (8, 8)) (hw' : w' = (1, 0) ∨ w' = (8, 8))
    (hσ : (v.1 * w.1 + v.2 * w.2, v.1 * w.2 + v.2 * w.1)
      = (v'.1 * w'.1 + v'.2 * w'.2, v'.1 * w'.2 + v'.2 * w'.1))
    (hs₄ : (u.1 * (v'.1 * w'.1 + v'.2 * w'.2)
          + u.2 * (v'.1 * w'.2 + v'.2 * w'.1),
        u.1 * (v'.1 * w'.2 + v'.2 * w'.1)
          + u.2 * (v'.1 * w'.1 + v'.2 * w'.2))
      = (u.1 * (v.1 * w.1 + v.2 * w.2) + u.2 * (v.1 * w.2 + v.2 * w.1),
        u.1 * (v.1 * w.2 + v.2 * w.1) + u.2 * (v.1 * w.1 + v.2 * w.2)))
    {τ : ℕ × ℕ}
    (hs₂ : ((u.1 * v.1 + u.2 * v.2) * w.1 + (u.1 * v.2 + u.2 * v.1) * w.2,
        (u.1 * v.1 + u.2 * v.2) * w.2 + (u.1 * v.2 + u.2 * v.1) * w.1)
      = τ)
    (hs₄c : ((u.1 * v'.1 + u.2 * v'.2) * w'.1
          + (u.1 * v'.2 + u.2 * v'.1) * w'.2,
        (u.1 * v'.1 + u.2 * v'.2) * w'.2
          + (u.1 * v'.2 + u.2 * v'.1) * w'.1)
      = τ)
    (X : ((stdTower (K := K) x).matrixSuper
      (u.1 * (v.1 * w.1 + v.2 * w.2) + u.2 * (v.1 * w.2 + v.2 * w.1))
      (u.1 * (v.1 * w.2 + v.2 * w.1)
        + u.2 * (v.1 * w.1 + v.2 * w.2))).carrier) :
    (stdMatrixCast hxz hs₂).toAlgEquiv
        ((matrixSuperCompAssoc (stdTower x) w.1 w.2 v.1 v.2
          u.1 u.2).symm.toAlgEquiv X)
      = (stdMatrixCast hyz hs₄c).toAlgEquiv
          ((matrixSuperCompAssoc (stdTower y) w'.1 w'.2 v'.1 v'.2
            u.1 u.2).symm.toAlgEquiv
            ((stdMatrixCast hyx hs₄).symm.toAlgEquiv X)) := by
  subst hyx
  subst hxz
  subst hs₂
  by_cases hvv : v = v' ∧ w = w'
  · -- aligned splits: after identifying the layers, both bridges are
    -- the same term and every cast is along a reflexive equality
    obtain ⟨rfl, rfl⟩ := hvv
    rfl
  · -- crossed splits: classify the sizes; the impossible combinations
    -- contradict the size identity or the alignment hypothesis, and
    -- the four surviving one-wrap crossings are settled by the
    -- kernel-checked sorting coincidence
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        rcases hw with rfl | rfl <;> rcases hv' with rfl | rfl <;>
        rcases hw' with rfl | rfl <;>
      first
        | exact absurd hσ (by decide)
        | exact absurd ⟨rfl, rfl⟩ hvv
        | skip
    · exact (cross1 _ X).symm
    · exact cross1 _ X
    · exact (cross8 _ X).symm
    · exact cross8 _ X

/-- `clusterTail2` factors through the shared tail — definitionally. -/
private theorem clusterTail2_factor_shared (a b c d : ZMod 8)
    (v : (((stdTower (K := K) a).gtensor
      ((stdTower (b + c)).matrixSuper (fuseSize b c).1
        (fuseSize b c).2)).gtensor (stdTower d)).carrier) :
    (clusterTail2 a b c d).toAlgEquiv v
      = (clusterSharedTail a b c d).toAlgEquiv
          (((routeL a (b + c) d).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((clusterFrame a b c d).toAlgEquiv v)) :=
  rfl

/-- `clusterTail4` factors through the shared tail — via the bridge
coherence `theta_gen`. -/
private theorem clusterTail4_factor_shared (a b c d : ZMod 8)
    (v : (((stdTower (K := K) a).gtensor
      ((stdTower (b + c)).matrixSuper (fuseSize b c).1
        (fuseSize b c).2)).gtensor (stdTower d)).carrier) :
    (clusterTail4 a b c d).toAlgEquiv v
      = (clusterSharedTail a b c d).toAlgEquiv
          (((routeR a (b + c) d).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((clusterFrame a b c d).toAlgEquiv v)) := by
  have h := theta_gen (K := K) (a + (b + c) + d) (a + (b + c + d))
    (a + b + c + d)
    ((add_assoc a (b + c) d).symm)
    (clusterIndex_eq' a b c d)
    (show a + (b + c + d) = a + b + c + d by ring)
    (fuseSize b c) (fuseSize a (b + c)) (fuseSize (a + (b + c)) d)
    (fuseSize (b + c) d) (fuseSize a (b + c + d))
    (fuseSize_cases b c) (fuseSize_cases a (b + c))
    (fuseSize_cases (a + (b + c)) d) (fuseSize_cases (b + c) d)
    (fuseSize_cases a (b + c + d))
    (sizeL_eq_sizeR a (b + c) d)
    (congrArg (fun s : ℕ × ℕ =>
        ((fuseSize b c).1 * s.1 + (fuseSize b c).2 * s.2,
          (fuseSize b c).1 * s.2 + (fuseSize b c).2 * s.1))
      (sizeL_eq_sizeR a (b + c) d).symm)
    (clusterSize_eq₂' a b c d)
    ((quadSize_eq a b c d).symm)
    ((matrixSuperComp (stdTower (a + (b + c) + d))
        (fuseSize b c).1 (fuseSize b c).2
        (sizeL a (b + c) d).1 (sizeL a (b + c) d).2).toAlgEquiv
      (((routeR a (b + c) d).matrixSuper (fuseSize b c).1
          (fuseSize b c).2).toAlgEquiv
        ((clusterFrame a b c d).toAlgEquiv v)))
  exact h.symm

/-! ### The middle edge -/

/-- **The middle cluster-edge intertwiner** of the pentagon: the triple
intertwiner of `(a, b+c, d)`, amplified to the `f`-matrix layer by the
signed diagonal and pushed through the shared cluster tail. -/
noncomputable def edgeT24 (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  (clusterSharedTail a b c d).toAlgEquiv
    (sdiagAmp (sumParity (fuseSize b c).1 (fuseSize b c).2)
      (pentagonParity (K := K) a (b + c) d)
      (pentagonT a (b + c) d))

theorem edgeT24_mem (a b c d : ZMod 8) :
    edgeT24 (K := K) a b c d
      ∈ ((stdTower (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) a (b + c) d) := by
  rw [edgeT24, ← (clusterSharedTail a b c d).map_grading]
  exact Submodule.mem_map_of_mem
    (sdiagAmp_mem _ _ (pentagonT_mem a (b + c) d))

theorem edgeT24_isUnit (a b c d : ZMod 8) :
    IsUnit (edgeT24 (K := K) a b c d) := by
  rw [edgeT24]
  exact IsUnit.map _
    (sdiagAmp_isUnit _ (pentagonT_isUnit a (b + c) d))

/-- **The middle edge intertwines the two cluster vertex routes**, with
parity `p(a, b+c, d)`: `quadRoute2` (through `routeL a (b+c) d`) on the
`φ`-side and `alignedRoute4` (through `routeR a (b+c) d`) on the
`φ'`-side. -/
theorem edgeT24_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (alignedRoute4 a b c d).toAlgEquiv w * edgeT24 a b c d
        = ((sgn (j * pentagonParity (K := K) a (b + c) d) : ℤˣ) : ℤ) •
          (edgeT24 a b c d * (quadRoute2 a b c d).toAlgEquiv w) := by
  intro j w hw
  -- step 1: the signed-diagonal transport of the triple intertwiner
  -- to the f-matrix layer
  have h1 := intertwines_mapMatrix
    ((((stdTower (K := K) a).gtensor (stdTower (b + c))).gtensor
      (stdTower d)).grading)
    (sumParity (fuseSize b c).1 (fuseSize b c).2)
    (routeL a (b + c) d).toAlgEquiv.toAlgHom
    (routeR a (b + c) d).toAlgEquiv.toAlgHom
    (pentagonT_intertwines a (b + c) d)
  -- step 2: push along the shared tail
  have h2 := intertwines_map
    ((((((stdTower (K := K) a).gtensor (stdTower (b + c))).gtensor
      (stdTower d)).matrixSuper (fuseSize b c).1
      (fuseSize b c).2)).grading)
    (routeL a (b + c) d).toAlgEquiv.toAlgHom.mapMatrix
    (routeR a (b + c) d).toAlgEquiv.toAlgHom.mapMatrix
    (clusterSharedTail a b c d).toAlgEquiv.toAlgHom
    h1
  -- step 3: precompose with the matrix-frame change and the cluster
  -- prefix
  have h3 := intertwines_precomp
    ((((stdTower (K := K) a).gtensor
      ((stdTower (b + c)).matrixSuper (fuseSize b c).1
        (fuseSize b c).2)).gtensor (stdTower d)).grading)
    ((((((stdTower (K := K) a).gtensor (stdTower (b + c))).gtensor
      (stdTower d)).matrixSuper (fuseSize b c).1
      (fuseSize b c).2)).grading)
    (((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).grading)
    ((clusterSharedTail a b c d).toAlgEquiv.toAlgHom.comp
      (routeL a (b + c) d).toAlgEquiv.toAlgHom.mapMatrix)
    ((clusterSharedTail a b c d).toAlgEquiv.toAlgHom.comp
      (routeR a (b + c) d).toAlgEquiv.toAlgHom.mapMatrix)
    (clusterFrame a b c d).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _ (clusterFrame a b c d).map_grading)
    h2
  have h4 := intertwines_precomp
    (((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).grading)
    ((((stdTower (K := K) a).gtensor
      ((stdTower (b + c)).matrixSuper (fuseSize b c).1
        (fuseSize b c).2)).gtensor (stdTower d)).grading)
    (((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).grading)
    (((clusterSharedTail a b c d).toAlgEquiv.toAlgHom.comp
        (routeL a (b + c) d).toAlgEquiv.toAlgHom.mapMatrix).comp
      (clusterFrame a b c d).toAlgEquiv.toAlgHom)
    (((clusterSharedTail a b c d).toAlgEquiv.toAlgHom.comp
        (routeR a (b + c) d).toAlgEquiv.toAlgHom.mapMatrix).comp
      (clusterFrame a b c d).toAlgEquiv.toAlgHom)
    (clusterPrefix a b c d).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _
      (clusterPrefix a b c d).map_grading)
    h3
  -- step 4: identify the composites with the factored vertex routes
  rw [show (alignedRoute4 a b c d).toAlgEquiv w
      = (clusterSharedTail a b c d).toAlgEquiv
          (((routeR a (b + c) d).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((clusterFrame a b c d).toAlgEquiv
              ((clusterPrefix a b c d).toAlgEquiv w))) from
      (alignedRoute4_factor a b c d w).trans
        (clusterTail4_factor_shared a b c d _),
    show (quadRoute2 a b c d).toAlgEquiv w
      = (clusterSharedTail a b c d).toAlgEquiv
          (((routeL a (b + c) d).matrixSuper (fuseSize b c).1
              (fuseSize b c).2).toAlgEquiv
            ((clusterFrame a b c d).toAlgEquiv
              ((clusterPrefix a b c d).toAlgEquiv w))) from
      (quadRoute2_factor a b c d w).trans
        (clusterTail2_factor_shared a b c d _)]
  exact h4 hw

end Edge24

end Superfusion

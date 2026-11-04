/-
Superfusion / Super / PentagonEdge13

Milestone M7d-5b-4-iii(c), part 2: **the (ab)-cluster edge e13**.
The triple intertwiner `pentagonT (a+b) c d` is amplified to the
`σ`-matrix layer (`σ := fuseSize a b`) by the signed diagonal
(`sdiagAmp`, M7d-5b-4-ii) and pushed through the shared tail of the
two cluster factorizations of `PentagonFactor13.lean`:

- `cluster13Tail1 = Ξ ≫ (routeL (a+b) c d).matrixSuper σ ≫ Θ`,
- `cluster13Tail3 = Ξ ≫ (routeR (a+b) c d).matrixSuper σ ≫ Θ`,

with the SAME shared tail `Θ = cluster13SharedTail` **by
construction** — both tails live in the left-associated frame, so
unlike the middle edge e24 no bridge coherence (`theta_gen`) is
needed here.

The edge `edgeT13 := Θ (sdiagAmp (sumParity σ) p(a+b, c, d)
(pentagonT (a+b) c d))` is homogeneous of parity `p(a+b, c, d)`,
invertible, and intertwines `(quadRoute1, quadRoute3)` — the
`routeL`-based vertex on the `φ`-side and the `routeR`-based vertex
on the `φ'`-side, matching the orientation of
`pentagonT_intertwines`.
-/
import Superfusion.Super.PentagonFactor13

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

section Edge13

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- **The (ab)-cluster edge intertwiner** of the pentagon: the triple
intertwiner of `(a+b, c, d)`, amplified to the `σ`-matrix layer by
the signed diagonal and pushed through the shared cluster tail. -/
noncomputable def edgeT13 (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  (cluster13SharedTail a b c d).toAlgEquiv
    (sdiagAmp (sumParity (fuseSize a b).1 (fuseSize a b).2)
      (pentagonParity (K := K) (a + b) c d)
      (pentagonT (a + b) c d))

theorem edgeT13_mem (a b c d : ZMod 8) :
    edgeT13 (K := K) a b c d
      ∈ ((stdTower (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) (a + b) c d) := by
  rw [edgeT13, ← (cluster13SharedTail a b c d).map_grading]
  exact Submodule.mem_map_of_mem
    (sdiagAmp_mem _ _ (pentagonT_mem (a + b) c d))

theorem edgeT13_isUnit (a b c d : ZMod 8) :
    IsUnit (edgeT13 (K := K) a b c d) := by
  rw [edgeT13]
  exact IsUnit.map _
    (sdiagAmp_isUnit _ (pentagonT_isUnit (a + b) c d))

/-- **The (ab)-cluster edge intertwines vertices 1 and 3**, with
parity `p(a+b, c, d)`: `quadRoute3` (through `routeR (a+b) c d`) on
the `φ'`-side and `quadRoute1` (through `routeL (a+b) c d`) on the
`φ`-side. -/
theorem edgeT13_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (quadRoute3 a b c d).toAlgEquiv w * edgeT13 a b c d
        = ((sgn (j * pentagonParity (K := K) (a + b) c d) : ℤˣ) : ℤ) •
          (edgeT13 a b c d * (quadRoute1 a b c d).toAlgEquiv w) := by
  intro j w hw
  -- step 1: the signed-diagonal transport of the triple intertwiner
  -- to the σ-matrix layer
  have h1 := intertwines_mapMatrix
    ((((stdTower (K := K) (a + b)).gtensor (stdTower c)).gtensor
      (stdTower d)).grading)
    (sumParity (fuseSize a b).1 (fuseSize a b).2)
    (routeL (a + b) c d).toAlgEquiv.toAlgHom
    (routeR (a + b) c d).toAlgEquiv.toAlgHom
    (pentagonT_intertwines (a + b) c d)
  -- step 2: push along the shared tail
  have h2 := intertwines_map
    ((((((stdTower (K := K) (a + b)).gtensor (stdTower c)).gtensor
      (stdTower d)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2)).grading)
    (routeL (a + b) c d).toAlgEquiv.toAlgHom.mapMatrix
    (routeR (a + b) c d).toAlgEquiv.toAlgHom.mapMatrix
    (cluster13SharedTail a b c d).toAlgEquiv.toAlgHom
    h1
  -- step 3: precompose with the matrix-frame change and the cluster
  -- prefix
  have h3 := intertwines_precomp
    ((((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).gtensor (stdTower c)).gtensor
      (stdTower d)).grading
    ((((((stdTower (K := K) (a + b)).gtensor (stdTower c)).gtensor
      (stdTower d)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2)).grading)
    (((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).grading)
    ((cluster13SharedTail a b c d).toAlgEquiv.toAlgHom.comp
      (routeL (a + b) c d).toAlgEquiv.toAlgHom.mapMatrix)
    ((cluster13SharedTail a b c d).toAlgEquiv.toAlgHom.comp
      (routeR (a + b) c d).toAlgEquiv.toAlgHom.mapMatrix)
    (cluster13Frame a b c d).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _
      (cluster13Frame a b c d).map_grading)
    h2
  have h4 := intertwines_precomp
    (((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).grading)
    ((((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).gtensor (stdTower c)).gtensor
      (stdTower d)).grading
    (((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).grading)
    (((cluster13SharedTail a b c d).toAlgEquiv.toAlgHom.comp
        (routeL (a + b) c d).toAlgEquiv.toAlgHom.mapMatrix).comp
      (cluster13Frame a b c d).toAlgEquiv.toAlgHom)
    (((cluster13SharedTail a b c d).toAlgEquiv.toAlgHom.comp
        (routeR (a + b) c d).toAlgEquiv.toAlgHom.mapMatrix).comp
      (cluster13Frame a b c d).toAlgEquiv.toAlgHom)
    (cluster13Prefix a b c d).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _
      (cluster13Prefix a b c d).map_grading)
    h3
  -- step 4: identify the composites with the factored vertex routes
  -- (both tails factor through the shared tail BY CONSTRUCTION)
  rw [show (quadRoute3 a b c d).toAlgEquiv w
      = (cluster13SharedTail a b c d).toAlgEquiv
          (((routeR (a + b) c d).matrixSuper (fuseSize a b).1
              (fuseSize a b).2).toAlgEquiv
            ((cluster13Frame a b c d).toAlgEquiv
              ((cluster13Prefix a b c d).toAlgEquiv w))) from
      quadRoute3_factor a b c d w,
    show (quadRoute1 a b c d).toAlgEquiv w
      = (cluster13SharedTail a b c d).toAlgEquiv
          (((routeL (a + b) c d).matrixSuper (fuseSize a b).1
              (fuseSize a b).2).toAlgEquiv
            ((cluster13Frame a b c d).toAlgEquiv
              ((cluster13Prefix a b c d).toAlgEquiv w))) from
      quadRoute1_factor a b c d w]
  exact h4 hw

end Edge13

end Superfusion

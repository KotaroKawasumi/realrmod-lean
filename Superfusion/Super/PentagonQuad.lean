/-
Superfusion / Super / PentagonQuad

Milestone M7d-5b-4-iii(b), part 1: **the quadruple layer, first
edge**.  The tail-extension functor

  `extendRoute R d : P ᵍ⊗ T_d ≅ M_{extSize}(T_{s+d})`
  (for `R : P ≅ M_σ(T_s)`)

produces the first two vertex routes of the K₅ pentagon
(`quadRoute1 = ext(routeL)`, `quadRoute2 = ext(routeR)`, sharing a
target), and the transport kit carries the triple intertwiner
across the tail: `edgeT12 := extTail (pentagonT a b c ᵍ⊗ 1)`
intertwines `(quadRoute1, quadRoute2)` with parity `p(a,b,c)`, is
homogeneous of that parity, and is invertible.
-/
import Superfusion.Super.PentagonCompose

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section Quad

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The size of the tail-extended stabilization. -/
def extSize (σ : ℕ × ℕ) (s d : ZMod 8) : ℕ × ℕ :=
  (σ.1 * (fuseSize s d).1 + σ.2 * (fuseSize s d).2,
   σ.1 * (fuseSize s d).2 + σ.2 * (fuseSize s d).1)

/-- The tail of the extension: everything after the congruence. -/
noncomputable def extTail (s : ZMod 8) (σ : ℕ × ℕ) (d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) s).matrixSuper σ.1 σ.2).gtensor (stdTower d))
      ((stdTower (s + d)).matrixSuper (extSize σ s d).1
        (extSize σ s d).2) :=
  (matrixSuperGtensor (stdTower s) (stdTower d) σ.1 σ.2).trans
    (((stdFuse s d).matrixSuper σ.1 σ.2).trans
      (matrixSuperComp (stdTower (s + d)) σ.1 σ.2
        (fuseSize s d).1 (fuseSize s d).2))

/-- **The tail extension of a stabilized route** by a further
fusion. -/
noncomputable def extendRoute {P : SuperAlgebra K} {s : ZMod 8}
    {σ : ℕ × ℕ}
    (R : SuperAlgEquiv P ((stdTower s).matrixSuper σ.1 σ.2))
    (d : ZMod 8) :
    SuperAlgEquiv (P.gtensor (stdTower d))
      ((stdTower (s + d)).matrixSuper (extSize σ s d).1
        (extSize σ s d).2) :=
  (R.gtensorCongr (SuperAlgEquiv.refl (stdTower d))).trans
    (extTail s σ d)

/-- Vertex 1 of the pentagon: `((ab)c)d`. -/
noncomputable def quadRoute1 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  extendRoute (routeL a b c) d

/-- Vertex 2 of the pentagon: `(a(bc))d`, sharing vertex 1's
target. -/
noncomputable def quadRoute2 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  extendRoute (routeR a b c) d

/-- **The first edge intertwiner** of the pentagon: the triple
intertwiner, tensored with `1` and pushed through the tail. -/
noncomputable def edgeT12 (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  (extTail (a + b + c) (sizeL a b c) d).toAlgEquiv
    ((pentagonT a b c ᵍ⊗ₜ[K] (1 : (stdTower d).carrier)) :
      ((stdTower (a + b + c)).matrixSuper (sizeL a b c).1
        (sizeL a b c).2).grading ᵍ⊗[K] (stdTower d).grading)

theorem edgeT12_mem (a b c d : ZMod 8) :
    edgeT12 (K := K) a b c d
      ∈ ((stdTower (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) a b c) := by
  rw [edgeT12, ← (extTail (a + b + c) (sizeL a b c) d).map_grading]
  refine Submodule.mem_map_of_mem ?_
  have h := tmul_mem_tensorGrading
    ((stdTower (K := K) (a + b + c)).matrixSuper (sizeL a b c).1
      (sizeL a b c).2).grading (stdTower d).grading
    (pentagonT_mem a b c)
    (SetLike.one_mem_graded (stdTower (K := K) d).grading)
  rwa [add_zero] at h

theorem edgeT12_isUnit (a b c d : ZMod 8) :
    IsUnit (edgeT12 (K := K) a b c d) := by
  rw [edgeT12]
  refine IsUnit.map _ ?_
  rw [show ((pentagonT (K := K) a b c ᵍ⊗ₜ[K]
        (1 : (stdTower d).carrier)) :
      ((stdTower (a + b + c)).matrixSuper (sizeL a b c).1
        (sizeL a b c).2).grading ᵍ⊗[K] (stdTower d).grading)
      = includeLeft ((stdTower (a + b + c)).matrixSuper
          (sizeL a b c).1 (sizeL a b c).2).grading
        (stdTower d).grading (pentagonT a b c) from rfl]
  exact IsUnit.map _ (pentagonT_isUnit a b c)

/-- **The first edge intertwines the first two vertex routes**, with
parity `p(a,b,c)`. -/
theorem edgeT12_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (quadRoute2 a b c d).toAlgEquiv w * edgeT12 a b c d
        = ((sgn (j * pentagonParity (K := K) a b c) : ℤˣ) : ℤ) •
          (edgeT12 a b c d * (quadRoute1 a b c d).toAlgEquiv w) := by
  intro j w hw
  -- step 1: the gmap-level relation from the transport kit
  have h1 := intertwines_gtensor_one
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).grading)
    (((stdTower (a + b + c)).matrixSuper (sizeL a b c).1
      (sizeL a b c).2).grading)
    ((stdTower (K := K) d).grading)
    (routeL a b c).toAlgEquiv.toAlgHom (routeR a b c).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _ (routeL a b c).map_grading)
    (isHomogeneousHom_of_map_grading _ (routeR a b c).map_grading)
    (pentagonT_mem a b c) (pentagonT_intertwines a b c) hw
  -- step 2: push along the tail equivalence
  have h2 := intertwines_map
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading
    (gmap _ _ _ _ (routeL a b c).toAlgEquiv.toAlgHom (AlgHom.id K _)
      (isHomogeneousHom_of_map_grading _ (routeL a b c).map_grading)
      (id_isHomogeneous _))
    (gmap _ _ _ _ (routeR a b c).toAlgEquiv.toAlgHom (AlgHom.id K _)
      (isHomogeneousHom_of_map_grading _ (routeR a b c).map_grading)
      (id_isHomogeneous _))
    (extTail (a + b + c) (sizeL a b c) d).toAlgEquiv.toAlgHom
    (fun _ _ hx =>
      intertwines_gtensor_one _ _ _
        (routeL a b c).toAlgEquiv.toAlgHom (routeR a b c).toAlgEquiv.toAlgHom
        (isHomogeneousHom_of_map_grading _ (routeL a b c).map_grading)
        (isHomogeneousHom_of_map_grading _ (routeR a b c).map_grading)
        (pentagonT_mem a b c) (pentagonT_intertwines a b c) hx) hw
  -- step 3: identify the composites with the quadruple routes
  exact h2

end Quad

end Superfusion

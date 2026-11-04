/-
Superfusion / Super / PentagonQuadRight

Milestone M7d-5b-4-iii(b), part 2: **the right-nested vertices and
their edge** — the mirror of part 1.  The head-extension functor

  `prependRoute R c : T_c ᵍ⊗ P ≅ M_{preSize}(T_{c+s})`
  (for `R : P ≅ M_σ(T_s)`)

applied to the triple routes of `(b,c,d)` produces the pentagon
vertices `a((bc)d)` and `a(b(cd))` with a common target, and the
transported `1 ᵍ⊗ T_{b,c,d}` intertwines them with parity
`p(b,c,d)`, homogeneous and invertible.
-/
import Superfusion.Super.PentagonQuad

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section QuadRight

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The size of the head-extended stabilization. -/
def preSize (σ : ℕ × ℕ) (c s : ZMod 8) : ℕ × ℕ :=
  (σ.1 * (fuseSize c s).1 + σ.2 * (fuseSize c s).2,
   σ.1 * (fuseSize c s).2 + σ.2 * (fuseSize c s).1)

/-- The tail of the head extension: everything after the
congruence. -/
noncomputable def preTail (c : ZMod 8) (s : ZMod 8) (σ : ℕ × ℕ) :
    SuperAlgEquiv
      ((stdTower (K := K) c).gtensor
        ((stdTower s).matrixSuper σ.1 σ.2))
      ((stdTower (c + s)).matrixSuper (preSize σ c s).1
        (preSize σ c s).2) :=
  (matrixSuperGtensorRight (stdTower c) (stdTower s) σ.1 σ.2).trans
    (((stdFuse c s).matrixSuper σ.1 σ.2).trans
      (matrixSuperComp (stdTower (c + s)) σ.1 σ.2
        (fuseSize c s).1 (fuseSize c s).2))

/-- **The head extension of a stabilized route** by a further
fusion on the left. -/
noncomputable def prependRoute {P : SuperAlgebra K} {s : ZMod 8}
    {σ : ℕ × ℕ}
    (R : SuperAlgEquiv P ((stdTower s).matrixSuper σ.1 σ.2))
    (c : ZMod 8) :
    SuperAlgEquiv ((stdTower c).gtensor P)
      ((stdTower (c + s)).matrixSuper (preSize σ c s).1
        (preSize σ c s).2) :=
  ((SuperAlgEquiv.refl (stdTower c)).gtensorCongr R).trans
    (preTail c s σ)

/-- Vertex 4 of the pentagon: `a((bc)d)`, on the
`T_a ᵍ⊗ ((T_b ᵍ⊗ T_c) ᵍ⊗ T_d)` source. -/
noncomputable def quadRoute4 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((stdTower (K := K) a).gtensor
        (((stdTower b).gtensor (stdTower c)).gtensor (stdTower d)))
      ((stdTower (a + (b + c + d))).matrixSuper
        (preSize (sizeL b c d) a (b + c + d)).1
        (preSize (sizeL b c d) a (b + c + d)).2) :=
  prependRoute (routeL b c d) a

/-- Vertex 5 of the pentagon: `a(b(cd))`, sharing vertex 4's source
and target. -/
noncomputable def quadRoute5 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((stdTower (K := K) a).gtensor
        (((stdTower b).gtensor (stdTower c)).gtensor (stdTower d)))
      ((stdTower (a + (b + c + d))).matrixSuper
        (preSize (sizeL b c d) a (b + c + d)).1
        (preSize (sizeL b c d) a (b + c + d)).2) :=
  prependRoute (routeR b c d) a

/-- **The right edge intertwiner** of the pentagon: the triple
intertwiner of `(b,c,d)`, tensored with `1` on the left and pushed
through the head tail. -/
noncomputable def edgeT45 (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + (b + c + d))).matrixSuper
      (preSize (sizeL b c d) a (b + c + d)).1
      (preSize (sizeL b c d) a (b + c + d)).2).carrier :=
  (preTail a (b + c + d) (sizeL b c d)).toAlgEquiv
    (((1 : (stdTower a).carrier) ᵍ⊗ₜ[K] pentagonT b c d) :
      (stdTower (K := K) a).grading ᵍ⊗[K]
        ((stdTower (b + c + d)).matrixSuper (sizeL b c d).1
          (sizeL b c d).2).grading)

theorem edgeT45_mem (a b c d : ZMod 8) :
    edgeT45 (K := K) a b c d
      ∈ ((stdTower (a + (b + c + d))).matrixSuper
          (preSize (sizeL b c d) a (b + c + d)).1
          (preSize (sizeL b c d) a (b + c + d)).2).grading
        (pentagonParity (K := K) b c d) := by
  rw [edgeT45, ← (preTail a (b + c + d) (sizeL b c d)).map_grading]
  refine Submodule.mem_map_of_mem ?_
  have h := tmul_mem_tensorGrading
    (stdTower (K := K) a).grading
    ((stdTower (K := K) (b + c + d)).matrixSuper (sizeL b c d).1
      (sizeL b c d).2).grading
    (SetLike.one_mem_graded (stdTower (K := K) a).grading)
    (pentagonT_mem b c d)
  rwa [zero_add] at h

theorem edgeT45_isUnit (a b c d : ZMod 8) :
    IsUnit (edgeT45 (K := K) a b c d) := by
  rw [edgeT45]
  refine IsUnit.map _ ?_
  rw [show (((1 : (stdTower a).carrier) ᵍ⊗ₜ[K]
        pentagonT (K := K) b c d) :
      (stdTower (K := K) a).grading ᵍ⊗[K]
        ((stdTower (b + c + d)).matrixSuper (sizeL b c d).1
          (sizeL b c d).2).grading)
      = includeRight (stdTower (K := K) a).grading
        ((stdTower (b + c + d)).matrixSuper (sizeL b c d).1
          (sizeL b c d).2).grading (pentagonT b c d) from rfl]
  exact IsUnit.map _ (pentagonT_isUnit b c d)

/-- **The right edge intertwines the right-nested vertex routes**,
with parity `p(b,c,d)`. -/
theorem edgeT45_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((stdTower (K := K) a).gtensor
        (((stdTower b).gtensor (stdTower c)).gtensor
          (stdTower d))).carrier⦄,
      w ∈ ((stdTower a).gtensor
        (((stdTower b).gtensor (stdTower c)).gtensor
          (stdTower d))).grading j →
      (quadRoute5 a b c d).toAlgEquiv w * edgeT45 a b c d
        = ((sgn (j * pentagonParity (K := K) b c d) : ℤˣ) : ℤ) •
          (edgeT45 a b c d * (quadRoute4 a b c d).toAlgEquiv w) := by
  intro j w hw
  have h2 := intertwines_map
    ((stdTower (K := K) a).gtensor
      (((stdTower b).gtensor (stdTower c)).gtensor
        (stdTower d))).grading
    (gmap _ _ _ _ (AlgHom.id K _) (routeL b c d).toAlgEquiv.toAlgHom
      (id_isHomogeneous _)
      (isHomogeneousHom_of_map_grading _ (routeL b c d).map_grading))
    (gmap _ _ _ _ (AlgHom.id K _) (routeR b c d).toAlgEquiv.toAlgHom
      (id_isHomogeneous _)
      (isHomogeneousHom_of_map_grading _ (routeR b c d).map_grading))
    (preTail a (b + c + d) (sizeL b c d)).toAlgEquiv.toAlgHom
    (fun _ _ hx =>
      intertwines_one_gtensor _ _ _
        (routeL b c d).toAlgEquiv.toAlgHom
        (routeR b c d).toAlgEquiv.toAlgHom
        (isHomogeneousHom_of_map_grading _ (routeL b c d).map_grading)
        (isHomogeneousHom_of_map_grading _ (routeR b c d).map_grading)
        (pentagonT_mem b c d) (pentagonT_intertwines b c d) hx) hw
  exact h2

end QuadRight

end Superfusion

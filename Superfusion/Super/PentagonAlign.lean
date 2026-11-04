/-
Superfusion / Super / PentagonAlign

Milestone M7d-5b-4-iii(b), part 3: **aligning the right-nested
vertices into the left frame**.  The right-nested vertex routes
(`quadRoute4/5`, source `T_a ᵍ⊗ ((T_b ᵍ⊗ T_c) ᵍ⊗ T_d)`, target
index `a+(b+c+d)`) are carried to the common frame of the
left-nested vertices (`quadRoute1/2`) by

- the reassociation prefix (two associators),
- the index cast `a+(b+c+d) = a+b+c+d` and the size identity
  `extSize (sizeL a b c) (a+b+c) d = preSize (sizeL b c d) a
  (b+c+d)` (the wrap count is bracketing-independent — a 4096-case
  kernel `decide`),
- `intertwines_precomp` (intertwining is stable under
  precomposition with a homogeneous map).

After this, four of the five pentagon vertices and both non-cluster
edges live in one frame.
-/
import Superfusion.Super.PentagonQuadRight

namespace Superfusion

open Module

section Align

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- Intertwining is stable under precomposition with a homogeneous
algebra map. -/
theorem intertwines_precomp {A₀ A B : Type*} [Ring A₀] [Algebra K A₀]
    [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (𝒜₀ : ZMod 2 → Submodule K A₀) (𝒜 : ZMod 2 → Submodule K A)
    (_ℬ : ZMod 2 → Submodule K B)
    (φ φ' : A →ₐ[K] B) (R : A₀ →ₐ[K] A)
    (hR : IsHomogeneousHom 𝒜₀ 𝒜 R) {p : ZMod 2} {t : B}
    (hint : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ' x * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ x)) :
    ∀ ⦃j : ZMod 2⦄ ⦃w : A₀⦄, w ∈ 𝒜₀ j →
      (φ'.comp R) w * t
        = ((sgn (j * p) : ℤˣ) : ℤ) • (t * (φ.comp R) w) :=
  fun j w hw => hint (hR j w hw)

/-- The reassociation prefix
`((T_a ᵍ⊗ T_b) ᵍ⊗ T_c) ᵍ⊗ T_d ≅ T_a ᵍ⊗ ((T_b ᵍ⊗ T_c) ᵍ⊗ T_d)`. -/
noncomputable def quadReassoc (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      ((stdTower a).gtensor
        (((stdTower b).gtensor (stdTower c)).gtensor (stdTower d))) :=
  ((gtensorAssoc (stdTower a) (stdTower b)
      (stdTower c)).gtensorCongr (SuperAlgEquiv.refl (stdTower d))).trans
    (gtensorAssoc (stdTower a)
      ((stdTower b).gtensor (stdTower c)) (stdTower d))

/-- The composed sizes agree across the two bracketings: the wrap
count is bracketing-independent. -/
theorem quadSize_eq : ∀ a b c d : ZMod 8,
    extSize (sizeL a b c) (a + b + c) d
      = preSize (sizeL b c d) a (b + c + d) := by
  decide

/-- Vertex 4 in the left frame. -/
noncomputable def alignedRoute4 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (quadReassoc a b c d).trans
    ((quadRoute4 a b c d).trans
      (stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
        (quadSize_eq a b c d).symm))

/-- Vertex 5 in the left frame. -/
noncomputable def alignedRoute5 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (quadReassoc a b c d).trans
    ((quadRoute5 a b c d).trans
      (stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
        (quadSize_eq a b c d).symm))

/-- The right edge in the left frame. -/
noncomputable def alignedEdgeT45 (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  (stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
    (quadSize_eq a b c d).symm).toAlgEquiv (edgeT45 a b c d)

theorem alignedEdgeT45_mem (a b c d : ZMod 8) :
    alignedEdgeT45 (K := K) a b c d
      ∈ ((stdTower (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) b c d) := by
  rw [alignedEdgeT45,
    ← (stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
      (quadSize_eq a b c d).symm).map_grading]
  exact Submodule.mem_map_of_mem (edgeT45_mem a b c d)

theorem alignedEdgeT45_isUnit (a b c d : ZMod 8) :
    IsUnit (alignedEdgeT45 (K := K) a b c d) := by
  rw [alignedEdgeT45]
  exact IsUnit.map _ (edgeT45_isUnit a b c d)

/-- **The aligned right edge intertwines the aligned vertex
routes**, with parity `p(b,c,d)`. -/
theorem alignedEdgeT45_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (alignedRoute5 a b c d).toAlgEquiv w * alignedEdgeT45 a b c d
        = ((sgn (j * pentagonParity (K := K) b c d) : ℤˣ) : ℤ) •
          (alignedEdgeT45 a b c d
            * (alignedRoute4 a b c d).toAlgEquiv w) := by
  intro j w hw
  -- push the edge relation along the cast, then precompose with the
  -- reassociation prefix
  have h2 := intertwines_precomp
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).grading
    ((stdTower a).gtensor
      (((stdTower b).gtensor (stdTower c)).gtensor
        (stdTower d))).grading
    ((stdTower (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).grading
    ((stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
        (quadSize_eq a b c d).symm).toAlgEquiv.toAlgHom.comp
      (quadRoute4 a b c d).toAlgEquiv.toAlgHom)
    ((stdMatrixCast (show a + (b + c + d) = a + b + c + d by ring)
        (quadSize_eq a b c d).symm).toAlgEquiv.toAlgHom.comp
      (quadRoute5 a b c d).toAlgEquiv.toAlgHom)
    (quadReassoc a b c d).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _ (quadReassoc a b c d).map_grading)
    (intertwines_map _ _ _ _ (edgeT45_intertwines a b c d)) hw
  exact h2

end Align

end Superfusion

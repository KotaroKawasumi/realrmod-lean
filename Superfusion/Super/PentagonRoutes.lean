/-
Superfusion / Super / PentagonRoutes

Milestone M7d-5b-3-i: **the two fusion routes on triples** — the
composite graded isomorphisms

  `routeL, routeR : (T_a ᵍ⊗ T_b) ᵍ⊗ T_c ≅ M_{σ(a,b,c)}(T_{a+b+c})`

through the left- and right-associated standard fusions, landing in
a COMMON matrix superalgebra: the composed matrix sizes agree on
the two routes because the number of mod-8 wraparounds is
route-independent (a 512-case kernel `decide`).  The route
comparison intertwiner `T_{a,b,c}` (super Skolem–Noether, M7d-5a)
and the parity `p(a,b,c)` are extracted in M7d-5b-3-ii.
-/
import Superfusion.Super.TowerStd

namespace Superfusion

section Routes

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The composed matrix size of the left route (outer `fuseSize a b`
applied to inner `fuseSize (a+b) c`, in `matrixSuperComp`'s
convention). -/
def sizeL (a b c : ZMod 8) : ℕ × ℕ :=
  ((fuseSize a b).1 * (fuseSize (a + b) c).1
      + (fuseSize a b).2 * (fuseSize (a + b) c).2,
    (fuseSize a b).1 * (fuseSize (a + b) c).2
      + (fuseSize a b).2 * (fuseSize (a + b) c).1)

/-- The composed matrix size of the right route. -/
def sizeR (a b c : ZMod 8) : ℕ × ℕ :=
  ((fuseSize b c).1 * (fuseSize a (b + c)).1
      + (fuseSize b c).2 * (fuseSize a (b + c)).2,
    (fuseSize b c).1 * (fuseSize a (b + c)).2
      + (fuseSize b c).2 * (fuseSize a (b + c)).1)

/-- The two routes wrap around mod 8 the same number of times, so
their composed sizes agree. -/
theorem sizeL_eq_sizeR : ∀ a b c : ZMod 8, sizeL a b c = sizeR a b c := by
  decide

/-- The sizes are nonzero (needed for BW statements downstream). -/
theorem sizeL_ne_zero : ∀ a b c : ZMod 8,
    (sizeL a b c).1 + (sizeL a b c).2 ≠ 0 := by
  decide

/-- Cast of a stabilized standard tower along index and size
equalities. -/
noncomputable def stdMatrixCast {x y : ZMod 8} (h : x = y)
    {s t : ℕ × ℕ} (hs : s = t) :
    SuperAlgEquiv ((stdTower (K := K) x).matrixSuper s.1 s.2)
      ((stdTower y).matrixSuper t.1 t.2) := by
  subst h
  subst hs
  exact SuperAlgEquiv.refl _

/-- **The left fusion route** (M7d-5b-3):
`(T_a ᵍ⊗ T_b) ᵍ⊗ T_c ≅ M_{σ}(T_{a+b+c})` through `(ab)c`. -/
noncomputable def routeL (a b c : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c))
      ((stdTower (a + b + c)).matrixSuper (sizeL a b c).1
        (sizeL a b c).2) :=
  ((stdFuse a b).gtensorCongr (SuperAlgEquiv.refl (stdTower c))).trans
    ((matrixSuperGtensor (stdTower (a + b)) (stdTower c)
        (fuseSize a b).1 (fuseSize a b).2).trans
      (((stdFuse (a + b) c).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).trans
        (matrixSuperComp (stdTower (a + b + c))
          (fuseSize a b).1 (fuseSize a b).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2)))

/-- **The right fusion route**:
`(T_a ᵍ⊗ T_b) ᵍ⊗ T_c ≅ M_{σ}(T_{a+b+c})` through `a(bc)`, cast onto
the left route's target. -/
noncomputable def routeR (a b c : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c))
      ((stdTower (a + b + c)).matrixSuper (sizeL a b c).1
        (sizeL a b c).2) :=
  (gtensorAssoc (stdTower a) (stdTower b) (stdTower c)).trans
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
              (sizeL_eq_sizeR a b c).symm)))))

end Routes

end Superfusion

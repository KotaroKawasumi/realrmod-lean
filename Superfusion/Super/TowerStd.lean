/-
Superfusion / Super / TowerStd

Milestone M7d-5b-2: **the ZMod 8 layer of the pentagon data** — the
standard tower representatives `stdTower a` (a : ℤ/8) and the
standard fusion

  `stdFuse a b : T_a ᵍ⊗ T_b ≅ M_{s(a,b)}(T_{a+b})`,

with sizes `s(a,b) = 1|0` below the Bott floor and `8|8` across the
mod-8 wraparound (the Bott certificate).  These are the table
isomorphisms of the paper's Section 4 in the tower gauge; the
route-comparison intertwiners `T_{a,b,c}` (M7d-5b-3) will be
extracted from them by super Skolem–Noether (M7d-5a).
-/
import Superfusion.Super.TowerFusion

namespace Superfusion

section Std

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The tower representative of a Brauer–Wall class. -/
noncomputable def stdTower (a : ZMod 8) : SuperAlgebra K :=
  divisionTower (1 : K) a.val

instance (a : ZMod 8) :
    FiniteDimensional K (stdTower (K := K) a).carrier :=
  inferInstanceAs
    (FiniteDimensional K (divisionTower (1 : K) a.val).carrier)

instance (a : ZMod 8) : Nontrivial (stdTower (K := K) a).carrier :=
  inferInstanceAs (Nontrivial (divisionTower (1 : K) a.val).carrier)

theorem stdTower_isSuperAzumaya (a : ZMod 8) :
    IsSuperAzumaya (stdTower (K := K) a).grading :=
  divisionTower_isSuperAzumaya one_ne_zero a.val

theorem stdTower_isGradedSimple (a : ZMod 8) :
    IsGradedSimple (stdTower (K := K) a).grading :=
  divisionTower_isGradedSimple one_ne_zero a.val

/-- Index cast along an equality of floors. -/
noncomputable def towerCast (ε : K) {m n : ℕ} (h : m = n) :
    SuperAlgEquiv (divisionTower ε m) (divisionTower ε n) :=
  h ▸ SuperAlgEquiv.refl (divisionTower ε m)

/-- Matrix sizes of the standard fusion: trivial below the Bott
floor, `8|8` across the wraparound. -/
def fuseSize (a b : ZMod 8) : ℕ × ℕ :=
  if a.val + b.val < 8 then (1, 0) else (8, 8)

/-- The no-wraparound branch of the standard fusion. -/
noncomputable def stdFuseLow (a b : ZMod 8)
    (h : a.val + b.val < 8) :
    SuperAlgEquiv ((stdTower (K := K) a).gtensor (stdTower b))
      ((stdTower (a + b)).matrixSuper 1 0) :=
  (towerFuse (1 : K) a.val b.val).trans
    ((towerCast (1 : K) (show a.val + b.val = (a + b).val by
        have h1 : (a + b).val = (a.val + b.val) % 8 := ZMod.val_add a b
        omega)).trans
      (matrixSuperOne (stdTower (a + b))).symm)

/-- The wraparound branch: peel off eight floors with the Bott
certificate. -/
noncomputable def stdFuseHigh (a b : ZMod 8)
    (h : ¬ a.val + b.val < 8) :
    SuperAlgEquiv ((stdTower (K := K) a).gtensor (stdTower b))
      ((stdTower (a + b)).matrixSuper 8 8) :=
  (towerFuse (1 : K) a.val b.val).trans
    ((towerCast (1 : K) (show a.val + b.val = (a + b).val + 8 by
        have h1 : (a + b).val = (a.val + b.val) % 8 := ZMod.val_add a b
        have h2 : a.val < 8 := ZMod.val_lt a
        have h3 : b.val < 8 := ZMod.val_lt b
        omega)).trans
      (towerMatrixEquiv K (a + b).val))

/-- **The standard fusion** (M7d-5b-2): the table isomorphism of the
tower representatives, `T_a ᵍ⊗ T_b ≅ M_{s(a,b)}(T_{a+b})`. -/
noncomputable def stdFuse (a b : ZMod 8) :
    SuperAlgEquiv ((stdTower (K := K) a).gtensor (stdTower b))
      ((stdTower (a + b)).matrixSuper (fuseSize a b).1
        (fuseSize a b).2) :=
  if h : a.val + b.val < 8 then by
    rw [show fuseSize a b = (1, 0) from if_pos h]
    exact stdFuseLow a b h
  else by
    rw [show fuseSize a b = (8, 8) from if_neg h]
    exact stdFuseHigh a b h

/-- The standard fusion realizes the Brauer–Wall product on the
standard representatives. -/
theorem isBWEquivalent_stdFuse (a b : ZMod 8) :
    IsBWEquivalent ((stdTower (K := K) a).gtensor (stdTower b))
      (stdTower (a + b)) := by
  refine IsBWEquivalent.of_matrixSuper ?_
    (stdFuse (K := K) a b)
  unfold fuseSize
  split <;> omega

end Std

end Superfusion

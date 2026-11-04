/-
Superfusion / Super / TowerFusion

Milestone M7d-5b-1: **the fusion equivalences of the division
tower** — for tower representatives the table isomorphisms of the
paper's Section 4 need no matrix ampliation below the Bott floor:

  `towerFuse a b : T_a ᵍ⊗ T_b ≅ T_{a+b}`   (a, b : ℕ)

built by induction on `b` from the unitor (`b = 0`), the one-step
decomposition `T_{n+1} ≅ T_n ᵍ⊗ T_1` (M7f-4d-2), the associator
(M7f-1c) and functoriality (M7f-1b).  Matrix sizes enter the
pentagon data only through the mod-8 wraparound (Bott certificate),
handled at the `ZMod 8` layer in M7d-5b-2.
-/
import Superfusion.Super.BWGenerator

namespace Superfusion

section Fuse

universe u

variable {K : Type u} [Field K]

/-- **The fusion equivalence of the division tower** (M7d-5b-1):
`T_a ᵍ⊗ T_b ≅ T_{a+b}`, with no matrix ampliation. -/
noncomputable def towerFuse (ε : K) (a : ℕ) :
    ∀ b : ℕ,
      SuperAlgEquiv
        ((divisionTower ε a).gtensor (divisionTower ε b))
        (divisionTower ε (a + b))
  | 0 => gtensorUnitorRight (divisionTower ε a)
  | b + 1 =>
      (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
          (towerSuccEquiv ε b)).trans
        ((gtensorAssoc (divisionTower ε a) (divisionTower ε b)
            (divisionTower ε 1)).symm.trans
          (((towerFuse ε a b).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).trans
            (towerSuccEquiv ε (a + b)).symm)))

/-- The fusion equivalence realizes the Brauer–Wall product on
tower classes. -/
theorem isBWEquivalent_towerFuse (ε : K) (a b : ℕ) :
    IsBWEquivalent
      ((divisionTower ε a).gtensor (divisionTower ε b))
      (divisionTower ε (a + b)) :=
  IsBWEquivalent.of_superAlgEquiv (towerFuse ε a b)

end Fuse

end Superfusion

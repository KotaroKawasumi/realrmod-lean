/-
Superfusion / Gauge / RealFuse1

Milestone M9-4b-ii-1: **the first slice of the 64 fusion isomorphisms**
for the eight real super division representatives `realRep : ZMod 8 →
SuperAlgebra ℝ` (`Superfusion.Gauge.RealReps`), matching Table 2 of the
paper (`docs/paper-tables-extract.md`).  Each isomorphism has the shape

  `realFuse a b : SuperAlgEquiv ((realRep a).gtensor (realRep b))
    ((realRep (a + b)).matrixSuper p q)`

with `(p, q)` Table 2's entry for the pair `(a, b)`.  This slice covers
the two "easy" groups, both landing on `M_{1|0}` (no genuine matrix
ampliation):

* **Group A** (fifteen pairs, `a = 0` or `b = 0`): `realRep 0` is
  `SuperAlgebra.base ℝ`, so the `M7f-4a` graded-tensor unitors
  (`gtensorUnitorLeft`/`gtensorUnitorRight`,
  `Superfusion.Super.TensorGradingUnitor`) compose with the `M_{1|0}`
  bridge `matrixSuperOne` (already present in
  `Superfusion.Super.BWTransitivity`, reverse direction via `.symm`) —
  `realFuse_zero_left`, `realFuse_zero_right`.
* **Group B** (six pairs, in-range same-sign Clifford pairs): three on
  each side of the division tower — `ε = -1` floors `(1,1), (1,2),
  (2,1)` and `ε = 1` floors `(7,7), (6,7), (7,6)` (paper indices `5, 6,
  7` are tower floors `3, 2, 1` respectively, per `realRepAux`) — via
  `towerFuse` (`Superfusion.Super.TowerFusion`), which is **already
  `ε`-generic** (no generalization needed: it is stated for an
  arbitrary field element `ε : K`), composed with `matrixSuperOne`.

Design note (totality, for the final slice): `realGauge.fuse` needs a
*total* function of `(a, b) : ZMod 8 × ZMod 8`.  The eventual assembly
plan is a case split on `a.val` and `b.val` (as in `realRep_isSuperDivision`
and friends: `interval_cases` after `ZMod.val_lt`), routing each of the
64 pairs to one of: this slice's unitor/tower lemmas, the remaining
same-sign Clifford pairs with matrix ampliation (`p|q ≠ 1|0`), the
mixed-sign pairs (new constructions per the paper's `φ_{a,b}` solver
data), and the `quatEvenSuper` row/column (`a = 4` or `b = 4`).
-/
import Superfusion.Gauge.RealReps

namespace Superfusion

/-! ### Group A: the fifteen unitor pairs (`a = 0` or `b = 0`) -/

/-- **Group A, left**: `realRep 0 ᵍ⊗ realRep b ≅ realRep b ≅ M_{1|0}(realRep b)`
(Table 2, row `0`: every entry is `1|0`). -/
noncomputable def realFuse_zero_left (b : ZMod 8) :
    SuperAlgEquiv ((realRep 0).gtensor (realRep b))
      ((realRep (0 + b)).matrixSuper 1 0) := by
  rw [zero_add]
  exact (gtensorUnitorLeft (realRep b)).trans (matrixSuperOne (realRep b)).symm

/-- **Group A, right**: `realRep a ᵍ⊗ realRep 0 ≅ realRep a ≅ M_{1|0}(realRep a)`
(Table 2, column `0`: every entry is `1|0`). -/
noncomputable def realFuse_zero_right (a : ZMod 8) :
    SuperAlgEquiv ((realRep a).gtensor (realRep 0))
      ((realRep (a + 0)).matrixSuper 1 0) := by
  rw [add_zero]
  exact (gtensorUnitorRight (realRep a)).trans (matrixSuperOne (realRep a)).symm

/-! ### Group B: the six in-range same-sign Clifford pairs

`towerFuse (ε : K) (a b : ℕ) : SuperAlgEquiv ((divisionTower ε a).gtensor
(divisionTower ε b)) (divisionTower ε (a + b))` is already `ε`-generic
in `Superfusion.Super.TowerFusion`, so no generalization was needed —
these six lemmas simply instantiate it at `ε = -1` (paper floors `1,
2, 3`) and `ε = 1` (paper indices `5, 6, 7` = floors `3, 2, 1`) and
compose with `matrixSuperOne`. -/

/-- `(1, 1) ↦ 2`: `Cl_{0,1} ᵍ⊗ Cl_{0,1} ≅ Cl_{0,2}` (Table 2 entry `1|0`). -/
noncomputable def realFuse_one_one :
    SuperAlgEquiv ((realRep 1).gtensor (realRep 1))
      ((realRep (1 + 1)).matrixSuper 1 0) :=
  (towerFuse (-1 : ℝ) 1 1).trans (matrixSuperOne (divisionTower (-1 : ℝ) 2)).symm

/-- `(1, 2) ↦ 3`: `Cl_{0,1} ᵍ⊗ Cl_{0,2} ≅ Cl_{0,3}` (Table 2 entry `1|0`). -/
noncomputable def realFuse_one_two :
    SuperAlgEquiv ((realRep 1).gtensor (realRep 2))
      ((realRep (1 + 2)).matrixSuper 1 0) :=
  (towerFuse (-1 : ℝ) 1 2).trans (matrixSuperOne (divisionTower (-1 : ℝ) 3)).symm

/-- `(2, 1) ↦ 3`: `Cl_{0,2} ᵍ⊗ Cl_{0,1} ≅ Cl_{0,3}` (Table 2 entry `1|0`). -/
noncomputable def realFuse_two_one :
    SuperAlgEquiv ((realRep 2).gtensor (realRep 1))
      ((realRep (2 + 1)).matrixSuper 1 0) :=
  (towerFuse (-1 : ℝ) 2 1).trans (matrixSuperOne (divisionTower (-1 : ℝ) 3)).symm

/-- `(7, 7) ↦ 6`: `Cl_{1,0} ᵍ⊗ Cl_{1,0} ≅ Cl_{2,0}` (Table 2 entry `1|0`). -/
noncomputable def realFuse_seven_seven :
    SuperAlgEquiv ((realRep 7).gtensor (realRep 7))
      ((realRep (7 + 7)).matrixSuper 1 0) :=
  (towerFuse (1 : ℝ) 1 1).trans (matrixSuperOne (divisionTower (1 : ℝ) 2)).symm

/-- `(6, 7) ↦ 5`: `Cl_{2,0} ᵍ⊗ Cl_{1,0} ≅ Cl_{3,0}` (Table 2 entry `1|0`). -/
noncomputable def realFuse_six_seven :
    SuperAlgEquiv ((realRep 6).gtensor (realRep 7))
      ((realRep (6 + 7)).matrixSuper 1 0) :=
  (towerFuse (1 : ℝ) 2 1).trans (matrixSuperOne (divisionTower (1 : ℝ) 3)).symm

/-- `(7, 6) ↦ 5`: `Cl_{1,0} ᵍ⊗ Cl_{2,0} ≅ Cl_{3,0}` (Table 2 entry `1|0`). -/
noncomputable def realFuse_seven_six :
    SuperAlgEquiv ((realRep 7).gtensor (realRep 6))
      ((realRep (7 + 6)).matrixSuper 1 0) :=
  (towerFuse (1 : ℝ) 1 2).trans (matrixSuperOne (divisionTower (1 : ℝ) 3)).symm

end Superfusion

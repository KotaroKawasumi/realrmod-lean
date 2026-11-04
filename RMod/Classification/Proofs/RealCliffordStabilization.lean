import Superfusion.Gauge.RealCanonical
import Superfusion.Super.TowerClifford

/-!
# Negative Clifford towers and the eight real representatives

Repeated fusion with the negative one-generator algebra gives an actual
graded matrix stabilization at every floor. This reuses the verified
binary fusion table and its matrix tensor identities. The induction also
proves that the stabilizing index is nonempty at each step.
-/

set_option autoImplicit false

namespace RMod.Classification

open Superfusion

theorem negativeTower_realRep_stabilization (n : ℕ) :
    ∃ p q : ℕ, p + q ≠ 0 ∧ Nonempty (SuperAlgEquiv (divisionTower (-1 : ℝ) n)
      ((realRep (n : ZMod 8)).matrixSuper p q)) := by
  induction n with
  | zero =>
    exact ⟨1, 0, one_ne_zero, ⟨(matrixSuperOne (realRep 0)).symm⟩⟩
  | succ n ih =>
    obtain ⟨p, q, hpq, ⟨e⟩⟩ := ih
    let r := (realSize (n : ZMod 8) 1).1
    let s := (realSize (n : ZMod 8) 1).2
    have hrs : r + s ≠ 0 := realGauge.size_pos (n : ZMod 8) 1
    refine ⟨p * r + q * s, p * s + q * r, ?_, ⟨?_⟩⟩
    · have hsum : (p * r + q * s) + (p * s + q * r) = (p + q) * (r + s) := by ring
      rw [hsum]
      exact mul_ne_zero hpq hrs
    · have ef : SuperAlgEquiv (divisionTower (-1 : ℝ) (n + 1))
          ((realRep ((n : ZMod 8) + 1)).matrixSuper
            (p * r + q * s) (p * s + q * r)) :=
        (towerFuse (-1 : ℝ) n 1).symm.trans <|
          (e.gtensorCongr (SuperAlgEquiv.refl (realRep 1))).trans <|
            (matrixSuperGtensor (realRep (n : ZMod 8)) (realRep 1) p q).trans <|
              ((realFuse (n : ZMod 8) 1).matrixSuper p q).trans
                (matrixSuperComp (realRep ((n : ZMod 8) + 1)) p q r s)
      simpa only [Nat.cast_add, Nat.cast_one] using ef

theorem negativeTower_isBWEquivalent_realRep (n : ℕ) :
    IsBWEquivalent (divisionTower (-1 : ℝ) n) (realRep (n : ZMod 8)) := by
  obtain ⟨p, q, hpq, ⟨e⟩⟩ := negativeTower_realRep_stabilization n
  exact IsBWEquivalent.of_matrixSuper hpq e

/-- Distinct listed division algebras have different graded Morita classes.
This is the existing order-eight calculation, transported from BW units. -/
theorem realRep_label_eq_of_isBWEquivalent {a b : ZMod 8}
    (h : IsBWEquivalent (realRep a) (realRep b)) : a = b := by
  letI := realRep_finiteDimensional a
  letI := realRep_finiteDimensional b
  letI := realRep_nontrivial a
  letI := realRep_nontrivial b
  apply realGauge_bwClass_injective
  apply Units.ext
  change BWMonoid.mk (realRep a) = BWMonoid.mk (realRep b)
  exact BWMonoid.mk_eq_mk_iff.mpr h

/-- The negative Clifford test cannot assign two different mod-eight labels. -/
theorem negativeTower_label_eq {a b : ZMod 8}
    (h : IsBWEquivalent (divisionTower (-1 : ℝ) a.val) (divisionTower (-1 : ℝ) b.val)) :
    a = b := by
  apply realRep_label_eq_of_isBWEquivalent
  have ha := negativeTower_isBWEquivalent_realRep a.val
  have hb := negativeTower_isBWEquivalent_realRep b.val
  rw [ZMod.natCast_zmod_val] at ha hb
  exact ha.symm.trans (h.trans hb)

end RMod.Classification

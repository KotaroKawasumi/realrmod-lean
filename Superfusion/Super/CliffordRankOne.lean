/-
Superfusion / Super / CliffordRankOne

Milestone M7b: the bridge between the explicit model `AdjoinOdd ε` (M7a)
and mathlib's Clifford algebra of the rank-one quadratic form
`x ↦ ε x²` on `K`.

* `AdjoinOdd.equivClifford : AdjoinOdd ε ≃ₐ[K] CliffordAlgebra (rankOneForm ε)`
  (over any commutative ring), matching `e ↔ ι 1`;
* `AdjoinOdd.map_grading` — the equivalence carries the explicit grading
  onto mathlib's `evenOdd` grading;
* consequences mathlib itself does not know: rank-one Clifford algebras
  are finite (`Module.Finite`), nontrivial (no `Invertible 2` needed),
  and of `finrank = 2`;
* transport of M7a through `GradedTransfer`: for a field with `2`
  invertible and `ε ≠ 0`, **mathlib's Clifford algebra
  `CliffordAlgebra (rankOneForm ε)` with its `evenOdd` grading is a
  central simple superalgebra**, hence super-Azumaya.

For `K = ℝ`, `ε = ∓1` these are the Clifford algebras `Cl(∓x²)`
(ungraded, `Cl(-x²) ≅ ℂ` is `CliffordAlgebraComplex.equiv`), i.e. the
standard super division algebras `D_{∓1}` in their native Clifford
guise.
-/
import Superfusion.Super.AdjoinOdd
import Superfusion.Super.GradedTransfer
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

namespace Superfusion

namespace AdjoinOdd

section CommRingBase

variable {K : Type*} [CommRing K] (ε : K)

/-- The rank-one quadratic form `x ↦ ε x²` on `K`. -/
def rankOneForm : QuadraticForm K K := ε • QuadraticMap.sq

@[simp] theorem rankOneForm_apply (x : K) : rankOneForm ε x = ε * (x * x) := by
  rw [rankOneForm, QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul]

/-- Clifford → `AdjoinOdd`, by the universal property (`ι 1 ↦ e`). -/
def ofClifford : CliffordAlgebra (rankOneForm ε) →ₐ[K] AdjoinOdd ε :=
  CliffordAlgebra.lift (rankOneForm ε)
    ⟨LinearMap.toSpanSingleton K (AdjoinOdd ε) (e ε), fun c => by
      rw [LinearMap.toSpanSingleton_apply, smul_mul_smul_comm, e_mul_e,
        Algebra.smul_def, ← map_mul]
      congr 1
      rw [rankOneForm_apply]
      ring⟩

@[simp] theorem ofClifford_ι (c : K) :
    ofClifford ε (CliffordAlgebra.ι (rankOneForm ε) c) = c • e ε := by
  rw [ofClifford, CliffordAlgebra.lift_ι_apply, LinearMap.toSpanSingleton_apply]

/-- The linear skeleton of `toClifford`: `a + b e ↦ a + b ι(1)`. -/
def toCliffordLin : AdjoinOdd ε →ₗ[K] CliffordAlgebra (rankOneForm ε) :=
  (Algebra.linearMap K (CliffordAlgebra (rankOneForm ε))).comp (ev ε)
    + (LinearMap.toSpanSingleton K (CliffordAlgebra (rankOneForm ε))
        (CliffordAlgebra.ι (rankOneForm ε) 1)).comp (od ε)

theorem toCliffordLin_mk (a b : K) :
    toCliffordLin ε (mk ε a b) =
      algebraMap K (CliffordAlgebra (rankOneForm ε)) a
        + b • CliffordAlgebra.ι (rankOneForm ε) 1 := by
  rw [toCliffordLin, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, ev_mk, od_mk, Algebra.linearMap_apply,
    LinearMap.toSpanSingleton_apply]

/-- The square of `ι 1`, in `•`-form. -/
private theorem ι_one_sq :
    CliffordAlgebra.ι (rankOneForm ε) 1 * CliffordAlgebra.ι (rankOneForm ε) 1
      = ε • (1 : CliffordAlgebra (rankOneForm ε)) := by
  rw [CliffordAlgebra.ι_sq_scalar, rankOneForm_apply, mul_one, mul_one,
    Algebra.algebraMap_eq_smul_one]

/-- Multiplication of `a + b ι(1)` normal forms in the Clifford algebra. -/
private theorem clifford_mul (a b c d : K) :
    (algebraMap K (CliffordAlgebra (rankOneForm ε)) a
        + b • CliffordAlgebra.ι (rankOneForm ε) 1)
      * (algebraMap K (CliffordAlgebra (rankOneForm ε)) c
        + d • CliffordAlgebra.ι (rankOneForm ε) 1)
    = algebraMap K (CliffordAlgebra (rankOneForm ε)) (a * c + ε * (b * d))
        + (a * d + b * c) • CliffordAlgebra.ι (rankOneForm ε) 1 := by
  simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul,
    smul_mul_smul_comm, ι_one_sq, one_mul, mul_one, smul_smul]
  module

/-- `AdjoinOdd` → Clifford, `a + b e ↦ a + b ι(1)`. -/
def toClifford : AdjoinOdd ε →ₐ[K] CliffordAlgebra (rankOneForm ε) :=
  AlgHom.ofLinearMap (toCliffordLin ε)
    (by
      rw [show (1 : AdjoinOdd ε) = mk ε 1 0 from rfl, toCliffordLin_mk,
        map_one, zero_smul, add_zero])
    (fun x y => by
      rw [← mk_ev_od ε x, ← mk_ev_od ε y, mk_mul_mk, toCliffordLin_mk,
        toCliffordLin_mk, toCliffordLin_mk, clifford_mul])

@[simp] theorem toClifford_mk (a b : K) :
    toClifford ε (mk ε a b) =
      algebraMap K (CliffordAlgebra (rankOneForm ε)) a
        + b • CliffordAlgebra.ι (rankOneForm ε) 1 :=
  toCliffordLin_mk ε a b

/-- **M7b**: the explicit rank-one Clifford superalgebra `AdjoinOdd ε` is
mathlib's Clifford algebra of the form `ε x²`, over any commutative
ring. -/
def equivClifford : AdjoinOdd ε ≃ₐ[K] CliffordAlgebra (rankOneForm ε) :=
  AlgEquiv.ofAlgHom (toClifford ε) (ofClifford ε)
    (by
      apply CliffordAlgebra.hom_ext
      apply LinearMap.ext
      intro c
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, AlgHom.coe_id, id_eq]
      rw [ofClifford_ι, map_smul, show e ε = mk ε 0 1 from rfl, toClifford_mk,
        map_zero, zero_add, one_smul, ← map_smul, smul_eq_mul, mul_one])
    (by
      apply AlgHom.ext
      intro p
      rw [AlgHom.comp_apply, ← mk_ev_od ε p, toClifford_mk, map_add,
        AlgHom.commutes, map_smul, ofClifford_ι, one_smul]
      exact ext ε (by simp) (by simp))

theorem equivClifford_apply (p : AdjoinOdd ε) :
    equivClifford ε p = toClifford ε p := rfl

theorem equivClifford_mk (a b : K) :
    equivClifford ε (mk ε a b) =
      algebraMap K (CliffordAlgebra (rankOneForm ε)) a
        + b • CliffordAlgebra.ι (rankOneForm ε) 1 :=
  toClifford_mk ε a b

/-- The equivalence matches the explicit grading with mathlib's `evenOdd`
grading. -/
theorem map_grading (i : ZMod 2) :
    (grading ε i).map (equivClifford ε).toLinearMap =
      CliffordAlgebra.evenOdd (rankOneForm ε) i := by
  have hmk0 : ∀ a : K, equivClifford ε (mk ε a 0) ∈
      CliffordAlgebra.evenOdd (rankOneForm ε) 0 := fun a => by
    rw [equivClifford_mk, zero_smul, add_zero]
    exact SetLike.algebraMap_mem_graded _ _
  have hmk1 : ∀ b : K, equivClifford ε (mk ε 0 b) ∈
      CliffordAlgebra.evenOdd (rankOneForm ε) 1 := fun b => by
    rw [equivClifford_mk, map_zero, zero_add]
    exact Submodule.smul_mem _ _ (CliffordAlgebra.ι_mem_evenOdd_one _ _)
  refine le_antisymm ?_ ?_
  · rintro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [AlgEquiv.toLinearMap_apply]
    rcases zmod2_cases i with hi | hi <;> subst hi
    · rw [mem_grading_zero] at hy
      have hymk : y = mk ε (ev ε y) 0 := by
        conv_lhs => rw [← mk_ev_od ε y, hy]
      rw [hymk]
      exact hmk0 _
    · rw [mem_grading_one] at hy
      have hymk : y = mk ε 0 (od ε y) := by
        conv_lhs => rw [← mk_ev_od ε y, hy]
      rw [hymk]
      exact hmk1 _
  · intro x hx
    have hsplit : (equivClifford ε).symm x =
        mk ε (ev ε ((equivClifford ε).symm x)) 0
          + mk ε 0 (od ε ((equivClifford ε).symm x)) :=
      ext ε (by simp) (by simp)
    have hx' : x = equivClifford ε (mk ε (ev ε ((equivClifford ε).symm x)) 0)
        + equivClifford ε (mk ε 0 (od ε ((equivClifford ε).symm x))) := by
      rw [← map_add, ← hsplit, AlgEquiv.apply_symm_apply]
    rcases zmod2_cases i with hi | hi <;> subst hi
    · have hodd : equivClifford ε
          (mk ε 0 (od ε ((equivClifford ε).symm x))) = 0 := by
        have hde := DirectSum.decompose_of_mem_ne
          (CliffordAlgebra.evenOdd (rankOneForm ε)) hx
          (by decide : (0 : ZMod 2) ≠ 1)
        calc equivClifford ε (mk ε 0 (od ε ((equivClifford ε).symm x)))
            = ((DirectSum.decompose (CliffordAlgebra.evenOdd (rankOneForm ε))
                x 1 : _) : CliffordAlgebra (rankOneForm ε)) := by
              conv_rhs => rw [hx']
              rw [DirectSum.decompose_add, DirectSum.add_apply,
                Submodule.coe_add,
                DirectSum.decompose_of_mem_ne _ (hmk0 _)
                  (by decide : (0 : ZMod 2) ≠ 1),
                DirectSum.decompose_of_mem_same _ (hmk1 _), zero_add]
          _ = 0 := hde
      rw [hx', hodd, add_zero, ← AlgEquiv.toLinearMap_apply]
      exact Submodule.mem_map_of_mem (mk_mem_grading_zero ε _)
    · have heven : equivClifford ε
          (mk ε (ev ε ((equivClifford ε).symm x)) 0) = 0 := by
        have hde := DirectSum.decompose_of_mem_ne
          (CliffordAlgebra.evenOdd (rankOneForm ε)) hx
          (by decide : (1 : ZMod 2) ≠ 0)
        calc equivClifford ε (mk ε (ev ε ((equivClifford ε).symm x)) 0)
            = ((DirectSum.decompose (CliffordAlgebra.evenOdd (rankOneForm ε))
                x 0 : _) : CliffordAlgebra (rankOneForm ε)) := by
              conv_rhs => rw [hx']
              rw [DirectSum.decompose_add, DirectSum.add_apply,
                Submodule.coe_add,
                DirectSum.decompose_of_mem_same _ (hmk0 _),
                DirectSum.decompose_of_mem_ne _ (hmk1 _)
                  (by decide : (1 : ZMod 2) ≠ 0),
                add_zero]
          _ = 0 := hde
      rw [hx', heven, zero_add, ← AlgEquiv.toLinearMap_apply]
      exact Submodule.mem_map_of_mem (mk_mem_grading_one ε _)

/-- Rank-one Clifford algebras are module-finite — a statement mathlib
itself does not yet have. -/
instance : Module.Finite K (CliffordAlgebra (rankOneForm ε)) :=
  Module.Finite.equiv (equivClifford ε).toLinearEquiv

/-- Rank-one Clifford algebras are nontrivial, with no `Invertible 2`
hypothesis (mathlib's route via `equivExterior` needs one). -/
instance [Nontrivial K] : Nontrivial (CliffordAlgebra (rankOneForm ε)) :=
  Equiv.nontrivial (equivClifford ε).symm.toEquiv

theorem finrank_adjoinOdd [Nontrivial K] :
    Module.finrank K (AdjoinOdd ε) = 2 := by
  rw [← (ofPair ε).finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- Rank-one Clifford algebras have dimension `2`. -/
theorem finrank_clifford_rankOne [Nontrivial K] :
    Module.finrank K (CliffordAlgebra (rankOneForm ε)) = 2 := by
  rw [← (equivClifford ε).toLinearEquiv.finrank_eq]
  exact finrank_adjoinOdd ε

end CommRingBase

/-! ### Central simplicity of mathlib's rank-one Clifford algebras -/

section Field

variable {K : Type*} [Field K] (ε : K)

/-- Mathlib's rank-one Clifford algebra, with its own `evenOdd` grading,
is supercentral (field base, `2` invertible, `ε ≠ 0`). -/
theorem isSuperCentral_evenOdd [Invertible (2 : K)] (hε : ε ≠ 0) :
    IsSuperCentral (CliffordAlgebra.evenOdd (rankOneForm ε)) := by
  haveI := AdjoinOdd.isSuperCentral ε hε
  exact isSuperCentral_of_equiv (grading ε) _ (equivClifford ε)
    (map_grading ε)

/-- Mathlib's rank-one Clifford algebra, with its own `evenOdd` grading,
is graded-simple (field base, `ε ≠ 0`). -/
theorem isGradedSimple_evenOdd (hε : ε ≠ 0) :
    IsGradedSimple (CliffordAlgebra.evenOdd (rankOneForm ε)) := by
  haveI := AdjoinOdd.isGradedSimple ε hε
  exact isGradedSimple_of_equiv (grading ε) _ (equivClifford ε)
    (map_grading ε)

/-- **Rank-one Clifford algebras are super-Azumaya** (field base, `2`
invertible, `ε ≠ 0`): Wall's criterion for mathlib's own
`CliffordAlgebra` with the `evenOdd` grading.  Over `ℝ` with
`ε = ±1` these are the standard super division algebras `D_{±1}`. -/
theorem isSuperAzumaya_evenOdd [Invertible (2 : K)] (hε : ε ≠ 0) :
    IsSuperAzumaya (CliffordAlgebra.evenOdd (rankOneForm ε)) := by
  haveI := isSuperCentral_evenOdd ε hε
  haveI := isGradedSimple_evenOdd ε hε
  exact isSuperAzumaya_of_central_simple _

end Field

end AdjoinOdd

end Superfusion

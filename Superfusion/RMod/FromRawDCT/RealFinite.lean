import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Superfusion.RMod.FromRawDCT.Finite
import Superfusion.RMod.FromRawDCT.RealCandidate

/-!
# Finiteness of the shifted real coordinate candidate

This concrete proof layer supplies canonical finite biproducts and a
proof-only finite basis for every Hom space.  The basis is chosen only inside
the law witness; no choice enters `realCandidateData` or any executable map.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT
open RModCoordinate
open CandidateData

private abbrev realShiftedDData : DData :=
  realDData

instance realShiftedDLawsFact : Fact (DLaws realShiftedDData) :=
  ⟨realDLaws⟩

/-- The shift does not alter `D`, but this instance records the law witness at
the exact reducible expression used by the concrete candidate. -/
instance realComputableShiftedDLawsFact :
    Fact (DLaws realComputableShiftedRawDCT.data.D) :=
  ⟨realComputableShiftedRawDCT.laws.D⟩

/-! ## Finite-dimensional atomic and matrix Hom spaces -/

/-- Evaluation at the common endpoint is a linear map from an atomic Hom
quotient into its finite coordinate algebra. -/
def realAtomHomCoeffMap {X Y : Atom}
    (hXY : Atom.label X = Atom.label Y) :
    AtomHom realShiftedDData X Y →ₗ[ℝ]
      Coeff (Atom.label X) where
  toFun f := f.coeff hXY
  map_add' f g := by
    change (AtomHom.add f g).coeff hXY = _
    rw [AtomHom.coeff_add]
    rfl
  map_smul' r f := by
    change (AtomHom.smul r f).coeff hXY = _
    rw [AtomHom.coeff_smul]
    rfl

theorem realAtomHomCoeffMap_injective {X Y : Atom}
    (hXY : Atom.label X = Atom.label Y) :
    Function.Injective (realAtomHomCoeffMap hXY) := by
  intro f g hfg
  apply AtomHom.ext
  intro h
  change f.coeff hXY = g.coeff hXY at hfg
  simpa only [Subsingleton.elim h hXY] using hfg

/-- Every atomic quotient is finite-dimensional.  At unequal labels it is
a singleton; at equal labels evaluation embeds it in the stored coordinate
algebra. -/
noncomputable instance realAtomHomFiniteDimensional (X Y : Atom) :
    FiniteDimensional ℝ (AtomHom realShiftedDData X Y) := by
  by_cases hXY : Atom.label X = Atom.label Y
  · exact FiniteDimensional.of_injective (realAtomHomCoeffMap hXY)
      (realAtomHomCoeffMap_injective hXY)
  · letI : Subsingleton (AtomHom realShiftedDData X Y) :=
      ⟨AtomHom.eq_of_label_ne hXY⟩
    exact FiniteDimensional.of_injective
      (0 : AtomHom realShiftedDData X Y →ₗ[ℝ] ℝ)
      (Function.injective_of_subsingleton _)

noncomputable instance realHomFiniteDimensional (X Y : Obj) :
    FiniteDimensional ℝ (Hom realShiftedDData X Y) :=
  inferInstance

/-- The same finite-dimensional instance at the exact shifted-data
expression occurring in `realCandidateData`. -/
noncomputable instance realComputableShiftedAtomHomFiniteDimensional
    (X Y : Atom) :
    FiniteDimensional ℝ
      (AtomHom realComputableShiftedRawDCT.data.D X Y) := by
  change FiniteDimensional ℝ (AtomHom realShiftedDData X Y)
  infer_instance

noncomputable instance realComputableShiftedHomFiniteDimensional
    (X Y : Obj) :
    FiniteDimensional ℝ
      (Hom realComputableShiftedRawDCT.data.D X Y) :=
  inferInstance

/-! ## Candidate-law witnesses -/

/-- A proof-only finite basis witness for one concrete Hom space. -/
noncomputable def realFiniteBasisWitness (X Y : Obj) :
    realCandidateData.FiniteBasisWitness X Y := by
  let b := Module.finBasis ℝ
    (Hom realComputableShiftedRawDCT.data.D X Y)
  exact
    { dimension := Module.finrank ℝ
        (Hom realComputableShiftedRawDCT.data.D X Y)
      basis := b
      coordinates := fun f i => b.equivFun f i
      reconstruct := fun f => by
        change (Candidate.data realComputableShiftedRawDCT.data
          realUnitRowsData).finSum _ _ = f
        rw [Finite.candidateFinSum_eq_sum]
        exact b.sum_equivFun f
      coordinates_unique := fun f c h => by
        change (Candidate.data realComputableShiftedRawDCT.data
          realUnitRowsData).finSum _ _ = f at h
        rw [Finite.candidateFinSum_eq_sum] at h
        apply b.equivFun.symm.injective
        rw [Module.Basis.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
        exact h }

theorem real_finiteDimensional_hom (X Y : Obj) :
    Nonempty (realCandidateData.FiniteBasisWitness X Y) :=
  ⟨realFiniteBasisWitness X Y⟩

theorem real_has_finite_biproducts {n : ℕ} (S : Fin n → Obj) :
    Nonempty (realCandidateData.BiproductWitness S) := by
  exact Finite.has_finite_biproducts
    realComputableShiftedRawDCT.data realUnitRowsData
    realComputableShiftedRawDCT.laws.D S

end Superfusion.RMod.FromRawDCT

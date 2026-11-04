import Superfusion.RMod.FromRawDCT.RealSemisimple

/-!
# The tensor unit of the shifted real candidate

The tensor unit is the unshifted singleton at label zero.  Its coordinate
algebra has one real basis vector, so its endomorphisms are exactly scalar
multiples of the identity.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT
open RModCoordinate
open CandidateData

namespace RealUnitEnd

private abbrev realShiftedD : DData := realDData

/-! ## Simplicity of the tensor unit -/

theorem simple_unit :
    realCandidateData.IsSimple realCandidateData.tensorUnit := by
  simpa [realCandidateData, Candidate.data, Unitor.canonicalData,
    Unitor.unit] using RealSemisimple.singleton_simple ((0, 0) : Atom)

/-! ## Scalar endomorphisms -/

/-- Distinct real scalars induce distinct endomorphisms of the unit. -/
theorem scalar_injective (r s : ℝ) :
    realCandidateData.smul r
        (realCandidateData.id realCandidateData.tensorUnit) =
      realCandidateData.smul s
        (realCandidateData.id realCandidateData.tensorUnit) →
      r = s := by
  intro h
  change Hom.smul r (Hom.id realShiftedD Unitor.unit) =
    Hom.smul s (Hom.id realShiftedD Unitor.unit) at h
  have hentry := congrFun
    (congrFun h (Finite.singletonIndex (0, 0)))
      (Finite.singletonIndex (0, 0))
  have hcoeff := congrArg (fun q => q.coeff rfl) hentry
  have hcoord := congrFun hcoeff (0 : Fin 1)
  simpa [Hom.smul, Hom.id, Unitor.unit, Obj.singleton, Obj.atom,
    Finite.singletonIndex, realShiftedD, realDData,
    coordinateSuperAlgebraData, AtomHom.id, Coeff.smul, Coeff.one,
    Atom.label] using hcoord

/-- Every unit endomorphism is a real scalar multiple of the identity. -/
theorem scalar_surjective
    (f : realCandidateData.Hom realCandidateData.tensorUnit
      realCandidateData.tensorUnit) :
    ∃ r : ℝ,
      realCandidateData.smul r
          (realCandidateData.id realCandidateData.tensorUnit) = f := by
  change Hom realShiftedD Unitor.unit Unitor.unit at f
  let u : Fin Unitor.unit.size := Finite.singletonIndex (0, 0)
  let r : ℝ := (f u u).coeff rfl (0 : Fin 1)
  refine ⟨r, ?_⟩
  change Hom.smul r (Hom.id realShiftedD Unitor.unit) = f
  apply Hom.ext
  intro i j
  have hi : i = u := Finite.eq_singletonIndex (0, 0) i
  have hj : j = u := Finite.eq_singletonIndex (0, 0) j
  subst i
  subst j
  apply AtomHom.ext
  intro hlabel
  change (AtomHom.smul r (Hom.id realShiftedD Unitor.unit u u)).coeff hlabel =
    (f u u).coeff hlabel
  rw [AtomHom.coeff_smul]
  have hlabel' : hlabel = rfl := Subsingleton.elim _ _
  rw [hlabel']
  rw [Hom.id, dif_pos rfl, AtomHom.coeff_id]
  funext k
  fin_cases k
  simp [r, u, Unitor.unit, Obj.singleton, Obj.atom,
    Finite.singletonIndex, realShiftedD, realDData,
    coordinateSuperAlgebraData, Coeff.smul, Coeff.one, Atom.label]
  congr

end RealUnitEnd

end Superfusion.RMod.FromRawDCT

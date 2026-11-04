import Superfusion.RMod.FromRawDCT.CandidateInvariantAdapter
import Superfusion.RMod.FromRawDCT.RealCandidateWithAssociator
import Superfusion.RMod.FromRawDCT.RealFinite
import Superfusion.RMod.FromRawDCT.RealUnitEnd

/-!
# Associator-independent laws for the endpoint real candidate

The endpoint-normalized candidate changes only its two associator maps.
This concrete proof layer reuses the already proved finite, semisimple,
graded-Schur, and unit-endomorphism facts by explicitly re-bundling their
nested witnesses over `realEndpointCandidateData`.

No associator, unitor, pairing, or coherence law is asserted here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace RealCandidateInvariantLaws

/-! ## Finite biproducts and Hom spaces -/

theorem hasFiniteBiproducts {n : ℕ} (S : Fin n → Obj) :
    Nonempty (realEndpointCandidateData.BiproductWitness S) := by
  obtain ⟨w⟩ := real_has_finite_biproducts S
  exact ⟨CandidateInvariantAdapter.biproductWitness
    realComputableShiftedRawDCT.data
    realComputableShiftedRawDCT.laws.D realUnitRowsData
    realAssociatorData w⟩

theorem finiteDimensionalHom (X Y : Obj) :
    Nonempty (realEndpointCandidateData.FiniteBasisWitness X Y) := by
  obtain ⟨w⟩ := real_finiteDimensional_hom X Y
  exact ⟨CandidateInvariantAdapter.finiteBasisWitness
    realComputableShiftedRawDCT.data
    realComputableShiftedRawDCT.laws.D realUnitRowsData
    realAssociatorData w⟩

/-! ## Semisimplicity and graded Schur -/

theorem semisimple (X : Obj) :
    ∃ (n : ℕ) (S : Fin n → Obj),
      (∀ i, realEndpointCandidateData.IsSimple (S i)) ∧
        Nonempty (realEndpointCandidateData.DecompositionWitness X S) := by
  obtain ⟨n, S, hsimple, ⟨w⟩⟩ := RealSemisimple.real_semisimple X
  refine ⟨n, S, ?_, ⟨CandidateInvariantAdapter.decompositionWitness
    realComputableShiftedRawDCT.data
    realComputableShiftedRawDCT.laws.D realUnitRowsData
    realAssociatorData w⟩⟩
  intro i
  exact (CandidateInvariantAdapter.isSimple_iff
    realComputableShiftedRawDCT.data realUnitRowsData
    realAssociatorData (S i)).2 (hsimple i)

theorem gradedSchur :
    ∀ {X Y : Obj}, realEndpointCandidateData.IsSimple X →
      realEndpointCandidateData.IsSimple Y →
      ∀ {d : ZMod 2} (f : realEndpointCandidateData.Hom X Y),
        realEndpointCandidateData.IsHomogeneous d f →
          f ≠ realEndpointCandidateData.zero →
            realEndpointCandidateData.IsIso f := by
  intro X Y hX hY d f hf hf0
  apply (CandidateInvariantAdapter.isIso_iff
    realComputableShiftedRawDCT.data realUnitRowsData
    realAssociatorData).2
  exact RealSemisimple.graded_schur
    ((CandidateInvariantAdapter.isSimple_iff
      realComputableShiftedRawDCT.data realUnitRowsData
      realAssociatorData X).1 hX)
    ((CandidateInvariantAdapter.isSimple_iff
      realComputableShiftedRawDCT.data realUnitRowsData
      realAssociatorData Y).1 hY)
    f
    ((CandidateInvariantAdapter.isHomogeneous_iff
      realComputableShiftedRawDCT.data realUnitRowsData
      realAssociatorData).1 hf) hf0

/-! ## Finite simple representatives -/

theorem finiteSimpleRepresentatives :
    ∃ (n : ℕ) (S : Fin n → Obj),
      (∀ i, realEndpointCandidateData.IsSimple (S i)) ∧
        ∀ X : Obj, realEndpointCandidateData.IsSimple X →
          ∃ (i : Fin n) (d : ZMod 2),
            Nonempty (realEndpointCandidateData.HomogeneousIso d X (S i)) := by
  obtain ⟨n, S, hsimple, hrepresent⟩ :=
    RealSemisimple.finite_simple_representatives
  refine ⟨n, S, ?_, ?_⟩
  · intro i
    exact (CandidateInvariantAdapter.isSimple_iff
      realComputableShiftedRawDCT.data realUnitRowsData
      realAssociatorData (S i)).2 (hsimple i)
  · intro X hX
    obtain ⟨i, d, ⟨e⟩⟩ := hrepresent X
      ((CandidateInvariantAdapter.isSimple_iff
        realComputableShiftedRawDCT.data realUnitRowsData
        realAssociatorData X).1 hX)
    exact ⟨i, d, ⟨CandidateInvariantAdapter.homogeneousIso
      realComputableShiftedRawDCT.data realUnitRowsData
      realAssociatorData e⟩⟩

/-! ## Tensor unit endomorphisms -/

theorem simpleUnit :
    realEndpointCandidateData.IsSimple
      realEndpointCandidateData.tensorUnit := by
  apply (CandidateInvariantAdapter.isSimple_iff
    realComputableShiftedRawDCT.data realUnitRowsData
    realAssociatorData realEndpointCandidateData.tensorUnit).2
  exact RealUnitEnd.simple_unit

theorem unitEndScalarInjective (r s : ℝ) :
    realEndpointCandidateData.smul r
        (realEndpointCandidateData.id realEndpointCandidateData.tensorUnit) =
      realEndpointCandidateData.smul s
        (realEndpointCandidateData.id realEndpointCandidateData.tensorUnit) →
      r = s :=
  RealUnitEnd.scalar_injective r s

theorem unitEndScalarSurjective
    (f : realEndpointCandidateData.Hom
      realEndpointCandidateData.tensorUnit
      realEndpointCandidateData.tensorUnit) :
    ∃ r : ℝ,
      realEndpointCandidateData.smul r
          (realEndpointCandidateData.id realEndpointCandidateData.tensorUnit) =
        f :=
  RealUnitEnd.scalar_surjective f

end RealCandidateInvariantLaws

end Superfusion.RMod.FromRawDCT

import Superfusion.RMod.FromRawDCT.Finite
import Superfusion.RMod.FromRawDCT.PairingAdapterWithAssociator

/-!
# Associator-independent candidate witnesses

Nested witness structures such as finite biproducts and finite bases retain
their entire `CandidateData` parameter.  Therefore a witness for
`Candidate.data x rows` does not elaborate directly as a witness for
`Candidate.dataWithAssociator x rows associator`, even though every field it
uses is unchanged.

This abstract proof adapter re-bundles exactly those unchanged coordinates.
It contains no concrete real instance and performs no finite-table
calculation.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace CandidateInvariantAdapter

/-! ## Associator-independent predicates -/

/-- Homogeneity uses only the common graded Hom data. -/
theorem isHomogeneous_iff (x : RawDCTData)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    {X Y : Obj} {a : ZMod 2} {f : Hom x.D X Y} :
    (Candidate.dataWithAssociator x rows associator).IsHomogeneous a f ↔
      (Candidate.data x rows).IsHomogeneous a f :=
  Iff.rfl

/-- Raw invertibility uses only composition and identities. -/
theorem isIso_iff (x : RawDCTData)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    {X Y : Obj} {f : Hom x.D X Y} :
    (Candidate.dataWithAssociator x rows associator).IsIso f ↔
      (Candidate.data x rows).IsIso f :=
  Iff.rfl

/-- Simplicity uses only the common even category. -/
theorem isSimple_iff (x : RawDCTData)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (X : Obj) :
    (Candidate.dataWithAssociator x rows associator).IsSimple X ↔
      (Candidate.data x rows).IsSimple X :=
  Iff.rfl

/-! ## Homogeneous isomorphisms -/

/-- Re-bundle a homogeneous isomorphism over the supplied-associator
candidate. -/
def homogeneousIso (x : RawDCTData)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    {a : ZMod 2} {X Y : Obj}
    (e : (Candidate.data x rows).HomogeneousIso a X Y) :
    (Candidate.dataWithAssociator x rows associator).HomogeneousIso a X Y where
  hom := e.hom
  inv := e.inv
  hom_inv := e.hom_inv
  inv_hom := e.inv_hom
  hom_mem := e.hom_mem
  inv_mem := e.inv_mem

/-! ## Finite biproduct and decomposition witnesses -/

/-- Re-bundle a finite biproduct witness.  The only proof transport is the
fixed-order sum, and both recursive sums equal the same ordinary sum. -/
def biproductWitness (x : RawDCTData) (hD : DLaws x.D)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    {n : ℕ} {S : Fin n → Obj}
    (w : (Candidate.data x rows).BiproductWitness S) :
    (Candidate.dataWithAssociator x rows associator).BiproductWitness S := by
  letI : Fact (DLaws x.D) := ⟨hD⟩
  exact
    { object := w.object
      inclusion := w.inclusion
      projection := w.projection
      inclusion_even := w.inclusion_even
      projection_even := w.projection_even
      inclusion_projection_self := w.inclusion_projection_self
      inclusion_projection_ne := w.inclusion_projection_ne
      projection_inclusion_total := by
        have htotal := w.projection_inclusion_total
        rw [PairingAdapterWithAssociator.candidateFinSum_eq_sum]
        rw [Finite.candidateFinSum_eq_sum] at htotal
        exact htotal }

/-- Re-bundle a decomposition witness over the same listed coordinates. -/
def decompositionWitness (x : RawDCTData) (hD : DLaws x.D)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    {X : Obj} {n : ℕ} {S : Fin n → Obj}
    (w : (Candidate.data x rows).DecompositionWitness X S) :
    (Candidate.dataWithAssociator x rows associator).DecompositionWitness X S := by
  letI : Fact (DLaws x.D) := ⟨hD⟩
  exact
    { inclusion := w.inclusion
      projection := w.projection
      inclusion_even := w.inclusion_even
      projection_even := w.projection_even
      inclusion_projection_self := w.inclusion_projection_self
      inclusion_projection_ne := w.inclusion_projection_ne
      projection_inclusion_total := by
        have htotal := w.projection_inclusion_total
        rw [PairingAdapterWithAssociator.candidateFinSum_eq_sum]
        rw [Finite.candidateFinSum_eq_sum] at htotal
        exact htotal }

/-! ## Finite Hom bases -/

/-- Re-bundle a finite basis witness.  Its basis and coordinate maps are
unchanged; reconstruction is transported through the common ordinary sum. -/
def finiteBasisWitness (x : RawDCTData) (hD : DLaws x.D)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    {X Y : Obj} (w : (Candidate.data x rows).FiniteBasisWitness X Y) :
    (Candidate.dataWithAssociator x rows associator).FiniteBasisWitness X Y := by
  letI : Fact (DLaws x.D) := ⟨hD⟩
  exact
    { dimension := w.dimension
      basis := w.basis
      coordinates := w.coordinates
      reconstruct := fun f => by
        have hreconstruct := w.reconstruct f
        rw [PairingAdapterWithAssociator.candidateFinSum_eq_sum]
        rw [Finite.candidateFinSum_eq_sum] at hreconstruct
        exact hreconstruct
      coordinates_unique := fun f c h => by
        apply w.coordinates_unique f c
        rw [Finite.candidateFinSum_eq_sum]
        rw [PairingAdapterWithAssociator.candidateFinSum_eq_sum] at h
        exact h }

end CandidateInvariantAdapter

end Superfusion.RMod.FromRawDCT

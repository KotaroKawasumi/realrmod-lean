import Superfusion.RMod.FromRawDCT.CandidateWithAssociator
import Superfusion.RMod.FromRawDCT.PairingAdapter

/-!
# Exact-pairing adapters for a supplied raw associator

This abstract proof layer is the associator-parametric counterpart of
`PairingAdapter`.  It completes exactly the supplied `AssociatorData`, then
forgets Mathlib category packaging back to `Candidate.dataWithAssociator`.
The coefficient algebra, tensor, unit rows, and unitors remain the canonical
ones extracted from the same raw DCT.

No concrete real table or instance is constructed in this file.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open CategoryTheory MonoidalCategory
open RawDCT

namespace PairingAdapterWithAssociator

/-! ## Completed proof-layer structures -/

/-- The completed coefficient-algebra family; it is independent of the
associator choice. -/
abbrev completedD (x : RawDCTData) (hx : RawDCTLaws x) : D :=
  PairingAdapter.completedD x hx

/-- The completed binary kernel; it is independent of the associator
choice. -/
abbrev completedC (x : RawDCTData) (hx : RawDCTLaws x) : C (completedD x hx) :=
  PairingAdapter.completedC x hx

/-- The completed canonical tensor extracted from the stored binary kernel. -/
abbrev completedTensor (x : RawDCTData) (hx : RawDCTLaws x) :
    Tensor (completedD x hx) :=
  PairingAdapter.completedTensor x hx

/-- Bundle the supplied executable associator with laws for exactly that
data. -/
def completedAssociator (x : RawDCTData) (hx : RawDCTLaws x)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws associator) :
    Associator (completedD x hx) (completedTensor x hx) where
  data := associator
  laws := hAssociator

/-- Bundle the canonical unitors over the supplied completed associator. -/
def completedUnitor (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws associator)
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx associator hAssociator).data
      (completedAssociator x hx associator hAssociator).laws
      (Unitor.canonicalData x rows)) :
    Unitor (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator) where
  data := Unitor.canonicalData x rows
  laws := hUnitor

/-! ## Category-level witness types -/

/-- Exact pairing in the Mathlib category view determined by the supplied
associator and its compatible unitors. -/
abbrev CategoryExactPairing (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws associator)
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx associator hAssociator).data
      (completedAssociator x hx associator hAssociator).laws
      (Unitor.canonicalData x rows))
    (X Y : Obj) :=
  @Superfusion.Category.SuperExactPairing ℝ inferInstance Obj
    (MathlibAdapter.category (completedD x hx))
    (MathlibAdapter.preadditive (completedD x hx))
    (MathlibAdapter.linear (completedD x hx))
    (MathlibAdapter.monoidalCategoryStruct
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor))
    (MathlibAdapter.supercategory (completedD x hx))
    (MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor)) X Y

/-- Homogeneous isomorphisms do not mention monoidal structure, so this is
definitionally the existing proof-layer type. -/
abbrev CategoryHomogeneousIso (x : RawDCTData) (hx : RawDCTLaws x)
    (a : ZMod 2) (X Y : Obj) :=
  PairingAdapter.CategoryHomogeneousIso x hx a X Y

/-- Supermultiplicity depends on the additive graded category and finite
biproducts, but not on the associator. -/
abbrev CategorySuperMultiplicity (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C) (A X : Obj) (p q : ℕ) :=
  PairingAdapter.CategorySuperMultiplicity x hx rows A X p q

/-- Weak-invertibility data in the monoidal category view selected by the
supplied associator. -/
abbrev CategoryWeakInvertibilityWitness
    (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws associator)
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx associator hAssociator).data
      (completedAssociator x hx associator hAssociator).laws
      (Unitor.canonicalData x rows))
    (X : Obj) :=
  @Superfusion.Category.WeakInvertibilityWitness ℝ inferInstance Obj
    (MathlibAdapter.category (completedD x hx))
    (MathlibAdapter.preadditive (completedD x hx))
    (MathlibAdapter.linear (completedD x hx))
    (MathlibAdapter.supercategory (completedD x hx))
    (MathlibAdapter.evenHasFiniteBiproducts x hx.D rows)
    (MathlibAdapter.monoidalCategoryStruct
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor))
    (MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor)) X

/-- Weak-invertibility proposition in the same supplied-associator view. -/
abbrev CategoryIsWeaklyInvertible
    (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws associator)
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx associator hAssociator).data
      (completedAssociator x hx associator hAssociator).laws
      (Unitor.canonicalData x rows))
    (X : Obj) :=
  @Superfusion.Category.IsWeaklyInvertible ℝ inferInstance Obj
    (MathlibAdapter.category (completedD x hx))
    (MathlibAdapter.preadditive (completedD x hx))
    (MathlibAdapter.linear (completedD x hx))
    (MathlibAdapter.supercategory (completedD x hx))
    (MathlibAdapter.evenHasFiniteBiproducts x hx.D rows)
    (MathlibAdapter.monoidalCategoryStruct
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor))
    (MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor)) X

/-! ## Fixed-order sums for the associator-parametric candidate -/

/-- The recursive candidate sum uses only zero and addition, hence is the
ordinary pointwise sum independently of the supplied associator. -/
theorem candidateFinSum_eq_sum (x : RawDCTData)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    [Fact (DLaws x.D)] {X Y : Obj} (n : ℕ)
    (f : Fin n → Hom x.D X Y) :
    (Candidate.dataWithAssociator x rows associator).finSum n f =
      ∑ i, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [CandidateData.finSum, ih, Fin.sum_univ_castSucc]
      rfl

/-- The candidate's even/odd fixed-order sum is the ordinary sum over the
disjoint union, again independently of associator data. -/
theorem candidateSuperFinSum_eq_sum (x : RawDCTData)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    [Fact (DLaws x.D)] {X Y : Obj} {p q : ℕ}
    (f : Fin p ⊕ Fin q → Hom x.D X Y) :
    (Candidate.dataWithAssociator x rows associator).superFinSum f =
      ∑ i, f i := by
  rw [CandidateData.superFinSum,
    candidateFinSum_eq_sum x rows associator,
    candidateFinSum_eq_sum x rows associator]
  exact (Fintype.sum_sum_type f).symm

section Conversion

variable (x : RawDCTData) (hx : RawDCTLaws x)
variable (rows : UnitRowsData x.D x.C)
variable (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
variable (hAssociator : AssociatorLaws
  (completedD x hx).data (completedD x hx).laws
  (completedTensor x hx).data (completedTensor x hx).laws associator)
variable (hUnitor : UnitorLaws
  (completedD x hx).data (completedD x hx).laws
  (completedTensor x hx).data (completedTensor x hx).laws
  (completedAssociator x hx associator hAssociator).data
  (completedAssociator x hx associator hAssociator).laws
  (Unitor.canonicalData x rows))

/-! ## Associator-independent conversions -/

/-- Regard a raw homogeneous isomorphism as the same isomorphism in the
Mathlib category view.  The nested witness remembers its full candidate
parameter, so its unchanged coordinate fields are repackaged explicitly. -/
def homogeneousIso {a : ZMod 2} {X Y : Obj}
    (e : (Candidate.dataWithAssociator x rows associator).HomogeneousIso a X Y) :
    CategoryHomogeneousIso x hx a X Y := by
  letI : Category Obj := MathlibAdapter.category (completedD x hx)
  letI : Preadditive Obj := MathlibAdapter.preadditive (completedD x hx)
  letI : Linear ℝ Obj := MathlibAdapter.linear (completedD x hx)
  letI : Superfusion.Category.Supercategory ℝ Obj :=
    MathlibAdapter.supercategory (completedD x hx)
  exact
    { iso :=
        { hom := e.hom
          inv := e.inv
          hom_inv_id := e.hom_inv
          inv_hom_id := e.inv_hom }
      hom_mem := e.hom_mem
      inv_mem := e.inv_mem }

/-- Forget the Mathlib biproduct packaging of a supermultiplicity witness.
Its coordinates are associator-independent; only the nested candidate
parameter is repackaged. -/
noncomputable def superMultiplicityWitness {A X : Obj} {p q : ℕ}
    (m : CategorySuperMultiplicity x hx rows A X p q) :
    (Candidate.dataWithAssociator x rows associator).SuperMultiplicityWitness
      A X p q := by
  letI : Category Obj := MathlibAdapter.category (completedD x hx)
  letI : Preadditive Obj := MathlibAdapter.preadditive (completedD x hx)
  letI : Linear ℝ Obj := MathlibAdapter.linear (completedD x hx)
  letI : Superfusion.Category.Supercategory ℝ Obj :=
    MathlibAdapter.supercategory (completedD x hx)
  letI : CategoryTheory.Limits.HasFiniteBiproducts
      (Superfusion.Category.EvenSubcategory ℝ Obj) :=
    MathlibAdapter.evenHasFiniteBiproducts x hx.D rows
  letI : Fact (DLaws x.D) := ⟨hx.D⟩
  exact
    { inclusion := m.inclusion
      projection := m.projection
      inclusion_mem := m.inclusion_mem
      projection_mem := m.projection_mem
      inclusion_projection_self := m.inclusion_projection_self
      inclusion_projection_ne := fun i j hij =>
        m.inclusion_projection_ne hij
      projection_inclusion_total := by
        rw [candidateSuperFinSum_eq_sum x rows associator]
        exact m.projection_inclusion_total }

/-! ## Exact pairings -/

/-- Forget the Mathlib pairing interface while retaining the exact maps and
snake identities for the supplied associator. -/
def exactPairingWitness {X Y : Obj}
    (p : CategoryExactPairing
      x hx rows associator hAssociator hUnitor X Y) :
    (Candidate.dataWithAssociator x rows associator).ExactPairingWitness X Y := by
  letI : Category Obj := MathlibAdapter.category (completedD x hx)
  letI : Preadditive Obj := MathlibAdapter.preadditive (completedD x hx)
  letI : Linear ℝ Obj := MathlibAdapter.linear (completedD x hx)
  letI : Superfusion.Category.Supercategory ℝ Obj :=
    MathlibAdapter.supercategory (completedD x hx)
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor)
  exact
    { coeval := p.coeval
      eval := p.eval
      coeval_even := p.coeval_mem
      eval_even := p.eval_mem
      coevaluation_evaluation := by
        change
          ((Y ◁ p.coeval) ≫ (α_ Y X Y).inv) ≫ (p.eval ▷ Y) =
            (ρ_ Y).hom ≫ (λ_ Y).inv
        simpa only [Category.assoc] using p.coevaluation_evaluation
      evaluation_coevaluation := by
        change
          ((p.coeval ▷ X) ≫ (α_ X Y X).hom) ≫ (X ◁ p.eval) =
            (λ_ X).hom ≫ (ρ_ X).inv
        simpa only [Category.assoc] using p.evaluation_coevaluation }

/-! ## Weak invertibility -/

/-- Forget the category packaging of weak invertibility, preserving the
chosen dual, supplied-associator pairing, and positive supermultiplicity. -/
noncomputable def weakInvertibilityWitness {X : Obj}
    (w : CategoryWeakInvertibilityWitness
      x hx rows associator hAssociator hUnitor X) :
    (Candidate.dataWithAssociator x rows associator).WeakInvertibilityWitness X := by
  letI : Category Obj := MathlibAdapter.category (completedD x hx)
  letI : Preadditive Obj := MathlibAdapter.preadditive (completedD x hx)
  letI : Linear ℝ Obj := MathlibAdapter.linear (completedD x hx)
  letI : Superfusion.Category.Supercategory ℝ Obj :=
    MathlibAdapter.supercategory (completedD x hx)
  letI : CategoryTheory.Limits.HasFiniteBiproducts
      (Superfusion.Category.EvenSubcategory ℝ Obj) :=
    MathlibAdapter.evenHasFiniteBiproducts x hx.D rows
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx associator hAssociator)
      (completedUnitor x hx rows associator hAssociator hUnitor)
  exact
    { dual := w.dual
      pairing := exactPairingWitness (x := x) (hx := hx) rows associator
        hAssociator hUnitor w.pairing
      evenMultiplicity := w.evenMultiplicity
      oddMultiplicity := w.oddMultiplicity
      multiplicity_pos := w.multiplicity_pos
      multiplicity := superMultiplicityWitness (x := x) (hx := hx) rows
        associator w.multiplicity }

/-- Category weak invertibility implies the raw predicate for the candidate
carrying the same supplied associator. -/
theorem isWeaklyInvertible {X : Obj}
    (hX : CategoryIsWeaklyInvertible
      x hx rows associator hAssociator hUnitor X) :
    (Candidate.dataWithAssociator x rows associator).IsWeaklyInvertible X := by
  rcases hX with ⟨w⟩
  exact ⟨weakInvertibilityWitness (x := x) (hx := hx) rows associator
    hAssociator hUnitor w⟩

end Conversion

end PairingAdapterWithAssociator

end Superfusion.RMod.FromRawDCT

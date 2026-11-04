import Superfusion.Category.WeaklyPointed
import Superfusion.RMod.FromRawDCT.MathlibAdapter

/-!
# Exact-pairing witnesses at the raw candidate boundary

This abstract proof layer converts exact pairings and supermultiplicity
witnesses proved through the Mathlib category interface back to the raw
`CandidateData` predicates.  Both interfaces use the same canonical
coefficient matrices, tensor, associator, and unitors; the conversion adds no
executable operation and performs no finite table calculation.

No concrete real instance is constructed in this file.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open CategoryTheory MonoidalCategory
open RawDCT

namespace PairingAdapter

/-! ## Completed canonical proof-layer structures -/

/-- The completed coefficient-algebra family of a raw DCT. -/
def completedD (x : RawDCTData) (hx : RawDCTLaws x) : D where
  data := x.D
  laws := hx.D

/-- The completed binary kernel of a raw DCT. -/
def completedC (x : RawDCTData) (hx : RawDCTLaws x) : C (completedD x hx) where
  data := x.C
  laws := hx.C

/-- The completed canonical tensor extracted from the stored binary kernel. -/
def completedTensor (x : RawDCTData) (hx : RawDCTLaws x) :
    Tensor (completedD x hx) :=
  Tensor.canonical (completedD x hx) (completedC x hx)

/-- Bundle proved laws for the canonical associator data. -/
def completedAssociator (x : RawDCTData) (hx : RawDCTLaws x)
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (Associator.canonicalData x)) :
    Associator (completedD x hx) (completedTensor x hx) where
  data := Associator.canonicalData x
  laws := hAssociator

/-- Bundle proved laws for the canonical unitors. -/
def completedUnitor (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (Associator.canonicalData x))
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx hAssociator).data
      (completedAssociator x hx hAssociator).laws
      (Unitor.canonicalData x rows)) :
    Unitor (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator) where
  data := Unitor.canonicalData x rows
  laws := hUnitor

/-! The following aliases display every proof-layer instance explicitly.
This keeps the conversion functions parametric in a raw DCT without
installing ambiguous global instances on the fixed object type `Obj`. -/

/-- Exact pairing for the canonical proof-layer view of `x`. -/
abbrev CategoryExactPairing (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (Associator.canonicalData x))
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx hAssociator).data
      (completedAssociator x hx hAssociator).laws
      (Unitor.canonicalData x rows))
    (X Y : Obj) :=
  @Superfusion.Category.SuperExactPairing ℝ inferInstance Obj
    (MathlibAdapter.category (completedD x hx))
    (MathlibAdapter.preadditive (completedD x hx))
    (MathlibAdapter.linear (completedD x hx))
    (MathlibAdapter.monoidalCategoryStruct
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor))
    (MathlibAdapter.supercategory (completedD x hx))
    (MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor)) X Y

/-- Homogeneous isomorphism for the canonical proof-layer view of `x`. -/
abbrev CategoryHomogeneousIso (x : RawDCTData) (hx : RawDCTLaws x)
    (a : ZMod 2) (X Y : Obj) :=
  @Superfusion.Category.HomogeneousIso ℝ inferInstance Obj
    (MathlibAdapter.category (completedD x hx))
    (MathlibAdapter.preadditive (completedD x hx))
    (MathlibAdapter.linear (completedD x hx))
    (MathlibAdapter.supercategory (completedD x hx)) a X Y

/-- Supermultiplicity for the canonical proof-layer view of `x`. -/
abbrev CategorySuperMultiplicity (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C) (A X : Obj) (p q : ℕ) :=
  @Superfusion.Category.SuperMultiplicityWitness ℝ inferInstance Obj
    (MathlibAdapter.category (completedD x hx))
    (MathlibAdapter.preadditive (completedD x hx))
    (MathlibAdapter.linear (completedD x hx))
    (MathlibAdapter.supercategory (completedD x hx))
    (MathlibAdapter.evenHasFiniteBiproducts x hx.D rows) A X p q

/-- Weak-invertibility data for the canonical proof-layer view of `x`. -/
abbrev CategoryWeakInvertibilityWitness
    (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (Associator.canonicalData x))
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx hAssociator).data
      (completedAssociator x hx hAssociator).laws
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
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor))
    (MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor)) X

/-- Weak-invertibility proposition for the canonical proof-layer view. -/
abbrev CategoryIsWeaklyInvertible
    (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (hAssociator : AssociatorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (Associator.canonicalData x))
    (hUnitor : UnitorLaws
      (completedD x hx).data (completedD x hx).laws
      (completedTensor x hx).data (completedTensor x hx).laws
      (completedAssociator x hx hAssociator).data
      (completedAssociator x hx hAssociator).laws
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
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor))
    (MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor)) X

section Conversion

variable (x : RawDCTData) (hx : RawDCTLaws x)
variable (rows : UnitRowsData x.D x.C)
variable (hAssociator : AssociatorLaws
  (completedD x hx).data (completedD x hx).laws
  (completedTensor x hx).data (completedTensor x hx).laws
  (Associator.canonicalData x))
variable (hUnitor : UnitorLaws
  (completedD x hx).data (completedD x hx).laws
  (completedTensor x hx).data (completedTensor x hx).laws
  (completedAssociator x hx hAssociator).data
  (completedAssociator x hx hAssociator).laws
  (Unitor.canonicalData x rows))

/-! ## Exact pairings -/

/-- Regard a raw homogeneous isomorphism as the same isomorphism in the
canonical Mathlib category view. -/
def homogeneousIso {a : ZMod 2} {X Y : Obj}
    (e : (Candidate.data x rows).HomogeneousIso a X Y) :
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

/-- Forget the Mathlib proof-layer interface of an exact pairing while
retaining its exact raw coordinate maps and snake identities. -/
def exactPairingWitness {X Y : Obj}
    (p : CategoryExactPairing x hx rows hAssociator hUnitor X Y) :
    (Candidate.data x rows).ExactPairingWitness X Y := by
  letI : Category Obj := MathlibAdapter.category (completedD x hx)
  letI : Preadditive Obj := MathlibAdapter.preadditive (completedD x hx)
  letI : Linear ℝ Obj := MathlibAdapter.linear (completedD x hx)
  letI : Superfusion.Category.Supercategory ℝ Obj :=
    MathlibAdapter.supercategory (completedD x hx)
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor)
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

/-! ## Supermultiplicity -/

/-- Forget the Mathlib biproduct packaging of a supermultiplicity witness.
The raw total-resolution law follows from the same finite sum, using the
candidate's proved fixed-order-sum comparison. -/
noncomputable def superMultiplicityWitness {A X : Obj} {p q : ℕ}
    (m : CategorySuperMultiplicity x hx rows A X p q) :
    (Candidate.data x rows).SuperMultiplicityWitness A X p q := by
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
        rw [Finite.candidateSuperFinSum_eq_sum x rows]
        exact m.projection_inclusion_total }

/-! ## Weak invertibility -/

/-- Forget the proof-layer packaging of weak invertibility, preserving the
chosen dual, exact pairing, positive multiplicity, and all its coordinates. -/
noncomputable def weakInvertibilityWitness {X : Obj}
    (w : CategoryWeakInvertibilityWitness
      x hx rows hAssociator hUnitor X) :
    (Candidate.data x rows).WeakInvertibilityWitness X := by
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
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory
      (completedD x hx) (completedTensor x hx)
      (completedAssociator x hx hAssociator)
      (completedUnitor x hx rows hAssociator hUnitor)
  exact
    { dual := w.dual
      pairing := exactPairingWitness (x := x) (hx := hx) rows
        hAssociator hUnitor w.pairing
      evenMultiplicity := w.evenMultiplicity
      oddMultiplicity := w.oddMultiplicity
      multiplicity_pos := w.multiplicity_pos
      multiplicity := superMultiplicityWitness (x := x) (hx := hx) rows
        w.multiplicity }

/-- Weak invertibility proved through the category interface implies the
raw candidate predicate for the same coordinate object. -/
theorem isWeaklyInvertible {X : Obj}
    (hX : CategoryIsWeaklyInvertible x hx rows hAssociator hUnitor X) :
    (Candidate.data x rows).IsWeaklyInvertible X := by
  rcases hX with ⟨w⟩
  exact ⟨weakInvertibilityWitness (x := x) (hx := hx) rows
    hAssociator hUnitor w⟩

end Conversion

end PairingAdapter

end Superfusion.RMod.FromRawDCT

import Superfusion.RMod.FromRawDCT.PairingAdapterWithAssociator
import Superfusion.RMod.FromRawDCT.RealCandidateWithAssociator
import Superfusion.RMod.FromRawDCT.RealPairing

/-!
# Exact pairings for the endpoint-normalized real associator

This concrete proof layer reuses all coordinate, dual-atom, multiplicity,
and finite-biproduct constructions from `RealPairing`.  Only the monoidal
completion is replaced: it bundles the fixed executable
`realAssociatorData`, then forgets category witnesses to
`realEndpointCandidateData` through `PairingAdapterWithAssociator`.

Associator and unitor laws remain explicit parameters.  Thus this file does
not assume that the still-separate concrete coherence proofs are complete.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open RawDCT

namespace RealPairingWithAssociator

open RealPairing

/-! ## Reused completed binary category -/

/-- The completed real coefficient algebra used by the coordinate pairing
construction. -/
abbrev realD : D := RealPairing.realD

/-- The completed shifted real fusion kernel. -/
abbrev realC : C realD := RealPairing.realC

/-- The canonical tensor remains unchanged by endpoint normalization. -/
abbrev realTensor : Tensor realD := RealPairing.realTensor

local instance realCategory : Category Obj :=
  MathlibAdapter.category realD

local instance realPreadditive : Preadditive Obj :=
  MathlibAdapter.preadditive realD

local instance realLinear : Linear ℝ Obj :=
  MathlibAdapter.linear realD

local instance realSupercategory : Superfusion.Category.Supercategory ℝ Obj :=
  MathlibAdapter.supercategory realD

local instance realDLawsFact : Fact (DLaws realD.data) :=
  ⟨realD.laws⟩

noncomputable local instance realEvenBiproducts :
    HasFiniteBiproducts (Superfusion.Category.EvenSubcategory ℝ Obj) :=
  MathlibAdapter.evenHasFiniteBiproducts
    realComputableShiftedRawDCT.data realD.laws realUnitRowsData

/-! ## Endpoint-normalized monoidal completion -/

/-- Bundle laws for the fixed endpoint-normalized real associator data. -/
def realAssociator
    (hAssociator : AssociatorLaws
      realD.data realD.laws realTensor.data realTensor.laws
      realAssociatorData) :
    Associator realD realTensor where
  data := realAssociatorData
  laws := hAssociator

/-- Bundle canonical real unitors whose triangle law refers to the fixed
endpoint-normalized associator. -/
def realUnitor
    (hAssociator : AssociatorLaws
      realD.data realD.laws realTensor.data realTensor.laws
      realAssociatorData)
    (hUnitor : UnitorLaws
      realD.data realD.laws realTensor.data realTensor.laws
      (realAssociator hAssociator).data
      (realAssociator hAssociator).laws
      (Unitor.canonicalData realComputableShiftedRawDCT.data
        realUnitRowsData)) :
    Unitor realD realTensor (realAssociator hAssociator) where
  data := Unitor.canonicalData realComputableShiftedRawDCT.data
    realUnitRowsData
  laws := hUnitor

section MonoidalPairing

variable (hAssociator : AssociatorLaws
  realD.data realD.laws realTensor.data realTensor.laws
  realAssociatorData)

variable (hUnitor : UnitorLaws
  realD.data realD.laws realTensor.data realTensor.laws
  (realAssociator hAssociator).data
  (realAssociator hAssociator).laws
  (Unitor.canonicalData realComputableShiftedRawDCT.data realUnitRowsData))

/-! ## Atomic right pairings -/

/-- Every shifted real singleton has an exact pairing with the already
constructed inverse-label atom, now in the endpoint-normalized monoidal
view.  The old coordinate and supermultiplicity witnesses are reused. -/
theorem singletonRightPairing_nonempty (A : Atom) :
    Nonempty
      (PairingAdapterWithAssociator.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        realAssociatorData hAssociator hUnitor
        (Obj.singleton A) (Obj.singleton (rightDualAtom A))) := by
  classical
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  let X := Obj.singleton A
  let Y := Obj.singleton (rightDualAtom A)
  let η : 𝟙_ Obj ⟶ X ⊗ Y := rightCoevaluation A
  let π : X ⊗ Y ⟶ 𝟙_ Obj := rightCoevaluationProjection A
  have hη : η ∈ Superfusion.Category.homGrade ℝ (𝟙_ Obj) (X ⊗ Y) 0 := by
    change Hom.MemGrade 0 (rightCoevaluation A)
    exact rightCoevaluation_even A
  have hsplit : η ≫ π = 𝟙 (𝟙_ Obj) := by
    change Hom.comp (rightCoevaluation A) (rightCoevaluationProjection A) =
      Hom.id realD.data (Obj.singleton (0, 0))
    exact rightCoevaluation_split A
  let m : Superfusion.Category.SuperMultiplicityWitness ℝ Obj
      (Y ⊗ X) (𝟙_ Obj)
      (reverseTensorSort A).evenMultiplicity
      (reverseTensorSort A).oddMultiplicity :=
    reverseTensorMultiplicity A
  have hX : 𝟙 X ≠ 0 := by
    change Hom.id realD.data (Obj.singleton A) ≠
      Hom.zero realD.data (Obj.singleton A) (Obj.singleton A)
    exact RealSemisimple.singleton_id_ne_zero A
  obtain ⟨i, hi⟩ :=
    Superfusion.Category.exists_normalizedXSnake_projection_ne_zero
      η π hη hsplit m hX
  let ε := m.projection i
  have hε : ε ∈ Superfusion.Category.homGrade ℝ
      (Y ⊗ X) (𝟙_ Obj)
      (Superfusion.Category.superIndexParity i) :=
    m.projection_mem i
  let r := Superfusion.Category.normalizedXSnake η ε
  have hr : r ∈ Superfusion.Category.homGrade ℝ X X
      (Superfusion.Category.superIndexParity i) := by
    simpa only [zero_add] using
      Superfusion.Category.normalizedXSnake_mem η ε hη hε
  letI : IsIso r :=
    singleton_isIso_of_homogeneous_of_ne_zero A A
      (Superfusion.Category.superIndexParity i) r hr hi
  let ε₀ := Superfusion.Category.normalizeEvaluationByXSnake η ε
  have hε₀ : ε₀ ∈ Superfusion.Category.homGrade ℝ
      (Y ⊗ X) (𝟙_ Obj) 0 :=
    Superfusion.Category.normalizeEvaluationByXSnake_mem_even
      η ε hη hε
  have hsnake :
      Superfusion.Category.normalizedXSnake η ε₀ = 𝟙 X :=
    Superfusion.Category.normalizedXSnake_normalizeEvaluationByXSnake
      η ε hη hε
  let p : Superfusion.Category.SuperExactPairing ℝ X Y :=
    Superfusion.Category.SuperExactPairing.ofNormalizedXSnakeOfEvenSchur
      η ε₀ hη hε₀ hsnake hX (by
        intro g hg hg0
        exact singleton_isIso_of_homogeneous_of_ne_zero
          (rightDualAtom A) (rightDualAtom A) 0 g hg hg0)
  exact ⟨p⟩

/-- Category-level weak-invertibility data for one singleton in the same
endpoint-normalized monoidal view. -/
noncomputable def singletonRightWeakInvertibilityWitness (A : Atom) :
    PairingAdapterWithAssociator.CategoryWeakInvertibilityWitness
      realComputableShiftedRawDCT.data
      realComputableShiftedRawDCT.laws realUnitRowsData
      realAssociatorData hAssociator hUnitor (Obj.singleton A) := by
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  let w : Superfusion.Category.WeakInvertibilityWitness ℝ Obj
      (Obj.singleton A) :=
    { dual := Obj.singleton (rightDualAtom A)
      pairing := Classical.choice
        (singletonRightPairing_nonempty hAssociator hUnitor A)
      evenMultiplicity := (forwardTensorSort A).evenMultiplicity
      oddMultiplicity := (forwardTensorSort A).oddMultiplicity
      multiplicity_pos := forwardTensorMultiplicity_pos A
      multiplicity := forwardTensorMultiplicity A }
  exact w

/-- The singleton witness at the endpoint-normalized raw candidate
boundary. -/
noncomputable def rawSingletonRightWeakInvertibilityWitness (A : Atom) :
    realEndpointCandidateData.WeakInvertibilityWitness (Obj.singleton A) :=
  PairingAdapterWithAssociator.weakInvertibilityWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData realAssociatorData hAssociator hUnitor
    (singletonRightWeakInvertibilityWitness hAssociator hUnitor A)

/-! ## Atomic left pairings -/

/-- The inverse-label involution turns the right pairing of the left dual
into a left pairing for the original atom. -/
theorem singletonLeftPairing_nonempty (A : Atom) :
    Nonempty
      (PairingAdapterWithAssociator.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        realAssociatorData hAssociator hUnitor
        (Obj.singleton (leftDualAtom A)) (Obj.singleton A)) := by
  simpa only [rightDual_leftDual] using
    singletonRightPairing_nonempty hAssociator hUnitor (leftDualAtom A)

/-! ## Pairings for arbitrary finite coordinate tuples -/

/-- Componentwise right pairings extend through the existing canonical atom
decomposition of every coordinate tuple. -/
theorem objectRightPairing_nonempty (X : Obj) :
    Nonempty
      (PairingAdapterWithAssociator.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        realAssociatorData hAssociator hUnitor X (rightDualObject X)) := by
  classical
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : HasFiniteBiproducts
      (Superfusion.Category.EvenSubcategory ℝ Obj) :=
    MathlibAdapter.evenHasFiniteBiproducts
      realComputableShiftedRawDCT.data realD.laws realUnitRowsData
  let e := Superfusion.Category.evenIsoOfEvenSubcategoryIso
    (atomDecompositionIso X)
  let atomPairing (i : Fin X.size) :
      Superfusion.Category.SuperExactPairing ℝ
        (Obj.singleton (X.atom i))
        (Obj.singleton (rightDualAtom (X.atom i))) :=
    Classical.choice
      (singletonRightPairing_nonempty hAssociator hUnitor (X.atom i))
  let p := Superfusion.Category.SuperExactPairing.biproduct atomPairing
  let q : Superfusion.Category.SuperExactPairing ℝ
      X (rightDualObject X) :=
    Superfusion.Category.SuperExactPairing.congrLeft e p
  exact ⟨q⟩

/-- Componentwise left pairings extend through the same atom
decomposition. -/
theorem objectLeftPairing_nonempty (X : Obj) :
    Nonempty
      (PairingAdapterWithAssociator.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        realAssociatorData hAssociator hUnitor (leftDualObject X) X) := by
  classical
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : HasFiniteBiproducts
      (Superfusion.Category.EvenSubcategory ℝ Obj) :=
    MathlibAdapter.evenHasFiniteBiproducts
      realComputableShiftedRawDCT.data realD.laws realUnitRowsData
  let e := Superfusion.Category.evenIsoOfEvenSubcategoryIso
    (atomDecompositionIso X)
  let atomPairing (i : Fin X.size) :
      Superfusion.Category.SuperExactPairing ℝ
        (Obj.singleton (leftDualAtom (X.atom i)))
        (Obj.singleton (X.atom i)) :=
    Classical.choice
      (singletonLeftPairing_nonempty hAssociator hUnitor (X.atom i))
  let p := Superfusion.Category.SuperExactPairing.biproduct atomPairing
  let q : Superfusion.Category.SuperExactPairing ℝ
      (leftDualObject X) X :=
    Superfusion.Category.SuperExactPairing.congrRight e p
  exact ⟨q⟩

/-! ## Endpoint-normalized raw candidate boundary -/

include hAssociator hUnitor

/-- Every endpoint-normalized raw coordinate object has a right exact
pairing witness. -/
theorem raw_has_right_dual (X : Obj) :
    ∃ Y : Obj,
      Nonempty (realEndpointCandidateData.ExactPairingWitness X Y) := by
  refine ⟨rightDualObject X, ?_⟩
  obtain ⟨p⟩ := objectRightPairing_nonempty hAssociator hUnitor X
  exact ⟨PairingAdapterWithAssociator.exactPairingWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData realAssociatorData hAssociator hUnitor p⟩

/-- Every endpoint-normalized raw coordinate object has a left exact
pairing witness. -/
theorem raw_has_left_dual (X : Obj) :
    ∃ Y : Obj,
      Nonempty (realEndpointCandidateData.ExactPairingWitness Y X) := by
  refine ⟨leftDualObject X, ?_⟩
  obtain ⟨p⟩ := objectLeftPairing_nonempty hAssociator hUnitor X
  exact ⟨PairingAdapterWithAssociator.exactPairingWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData realAssociatorData hAssociator hUnitor p⟩

/-- Every simple endpoint-normalized coordinate object is weakly
invertible.  Simplicity is transported to the canonical presentation only
to reuse its atom-classification theorem; the resulting isomorphism is then
repackaged for the endpoint candidate. -/
theorem raw_weaklyPointed (X : Obj)
    (hX : realEndpointCandidateData.IsSimple X) :
    realEndpointCandidateData.IsWeaklyInvertible X := by
  classical
  have hXCanonical : realCandidateData.IsSimple X := by
    unfold CandidateData.IsSimple CandidateData.IsEvenMono
      CandidateData.IsEvenIso CandidateData.IsHomogeneous at hX ⊢
    unfold realEndpointCandidateData Candidate.dataWithAssociator at hX
    unfold realCandidateData Candidate.data
    exact hX
  obtain ⟨i, ⟨e⟩⟩ := RealSemisimple.simple_iso_atom hXCanonical
  let eEndpoint : realEndpointCandidateData.HomogeneousIso 0 X
      (Obj.singleton (X.atom i)) :=
    { hom := e.hom
      inv := e.inv
      hom_inv := e.hom_inv
      inv_hom := e.inv_hom
      hom_mem := e.hom_mem
      inv_mem := e.inv_mem }
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  let e' := PairingAdapterWithAssociator.homogeneousIso
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData realAssociatorData eEndpoint
  let w : Superfusion.Category.WeakInvertibilityWitness ℝ Obj X :=
    Superfusion.Category.WeakInvertibilityWitness.congrLeft e'
      (singletonRightWeakInvertibilityWitness
        hAssociator hUnitor (X.atom i))
  exact ⟨PairingAdapterWithAssociator.weakInvertibilityWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData realAssociatorData hAssociator hUnitor w⟩

end MonoidalPairing

/-! ## Closed nontrivial dual evaluations -/

example : rightDualAtom (1, 0) = (7, 1) := rfl

example : leftDualAtom (3, 1) = (5, 0) := rfl

end RealPairingWithAssociator

end Superfusion.RMod.FromRawDCT

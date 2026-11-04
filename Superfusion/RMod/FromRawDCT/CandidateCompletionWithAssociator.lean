import Superfusion.RMod.FromRawDCT.CandidateCompletion
import Superfusion.RMod.FromRawDCT.CandidateWithAssociator

/-!
# Completing raw-DCT candidate laws with supplied associator data

This abstract proof layer is the associator-parametric counterpart of
`Candidate.completionLaws`.  It keeps the finite coordinate category,
tensor, unit, and unitors fixed while accepting any executable associator
data together with laws for exactly that data.

No concrete real table or instance is constructed here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace Candidate

/-! ## Completed proof-layer structures -/

/-- Bundle supplied associator data with laws for that same data. -/
def completedAssociatorWithData (x : RawDCTData) (hx : RawDCTLaws x)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (PairingAdapter.completedD x hx).data
      (PairingAdapter.completedD x hx).laws
      (PairingAdapter.completedTensor x hx).data
      (PairingAdapter.completedTensor x hx).laws associator) :
    Associator (PairingAdapter.completedD x hx)
      (PairingAdapter.completedTensor x hx) where
  data := associator
  laws := hAssociator

/-- Bundle the canonical unitors over the supplied completed associator. -/
def completedUnitorWithAssociator (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (PairingAdapter.completedD x hx).data
      (PairingAdapter.completedD x hx).laws
      (PairingAdapter.completedTensor x hx).data
      (PairingAdapter.completedTensor x hx).laws associator)
    (hUnitor : UnitorLaws
      (PairingAdapter.completedD x hx).data
      (PairingAdapter.completedD x hx).laws
      (PairingAdapter.completedTensor x hx).data
      (PairingAdapter.completedTensor x hx).laws
      (completedAssociatorWithData x hx associator hAssociator).data
      (completedAssociatorWithData x hx associator hAssociator).laws
      (Unitor.canonicalData x rows)) :
    Unitor (PairingAdapter.completedD x hx)
      (PairingAdapter.completedTensor x hx)
      (completedAssociatorWithData x hx associator hAssociator) where
  data := Unitor.canonicalData x rows
  laws := hUnitor

/-! ## Candidate-law assembly -/

set_option maxHeartbeats 800000 in
/-- Assemble all candidate laws for a raw DCT and the supplied associator.

Every proof argument refers to `dataWithAssociator x rows associator`, so
the final laws cannot accidentally be attached to different executable
data. -/
def completionLawsWithAssociator (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C))
    (hAssociator : AssociatorLaws
      (PairingAdapter.completedD x hx).data
      (PairingAdapter.completedD x hx).laws
      (PairingAdapter.completedTensor x hx).data
      (PairingAdapter.completedTensor x hx).laws associator)
    (hUnitor : UnitorLaws
      (PairingAdapter.completedD x hx).data
      (PairingAdapter.completedD x hx).laws
      (PairingAdapter.completedTensor x hx).data
      (PairingAdapter.completedTensor x hx).laws
      (completedAssociatorWithData x hx associator hAssociator).data
      (completedAssociatorWithData x hx associator hAssociator).laws
      (Unitor.canonicalData x rows))
    (hasFiniteBiproducts : ∀ {n : ℕ} (S : Fin n → Obj),
      Nonempty ((dataWithAssociator x rows associator).BiproductWitness S))
    (semisimple : ∀ X : Obj,
      ∃ (n : ℕ) (S : Fin n → Obj),
        (∀ i, (dataWithAssociator x rows associator).IsSimple (S i)) ∧
          Nonempty ((dataWithAssociator x rows associator).DecompositionWitness X S))
    (gradedSchur : ∀ {X Y : Obj},
      (dataWithAssociator x rows associator).IsSimple X →
        (dataWithAssociator x rows associator).IsSimple Y →
        ∀ {a : ZMod 2}
          (f : (dataWithAssociator x rows associator).Hom X Y),
          (dataWithAssociator x rows associator).IsHomogeneous a f →
            f ≠ (dataWithAssociator x rows associator).zero →
              (dataWithAssociator x rows associator).IsIso f)
    (finiteDimensionalHom : ∀ X Y : Obj,
      Nonempty ((dataWithAssociator x rows associator).FiniteBasisWitness X Y))
    (finiteSimpleRepresentatives :
      ∃ (n : ℕ) (S : Fin n → Obj),
        (∀ i, (dataWithAssociator x rows associator).IsSimple (S i)) ∧
          ∀ X : Obj, (dataWithAssociator x rows associator).IsSimple X →
            ∃ (i : Fin n) (a : ZMod 2),
              Nonempty
                ((dataWithAssociator x rows associator).HomogeneousIso a X (S i)))
    (simpleUnit :
      (dataWithAssociator x rows associator).IsSimple
        (dataWithAssociator x rows associator).tensorUnit)
    (unitEndScalarInjective : ∀ r s : ℝ,
      (dataWithAssociator x rows associator).smul r
          ((dataWithAssociator x rows associator).id
            (dataWithAssociator x rows associator).tensorUnit) =
        (dataWithAssociator x rows associator).smul s
          ((dataWithAssociator x rows associator).id
            (dataWithAssociator x rows associator).tensorUnit) → r = s)
    (unitEndScalarSurjective : ∀ f :
      (dataWithAssociator x rows associator).Hom
        (dataWithAssociator x rows associator).tensorUnit
        (dataWithAssociator x rows associator).tensorUnit,
        ∃ r : ℝ,
          (dataWithAssociator x rows associator).smul r
              ((dataWithAssociator x rows associator).id
                (dataWithAssociator x rows associator).tensorUnit) = f)
    (hasRightDual : ∀ X : Obj,
      ∃ Y : Obj, Nonempty
        ((dataWithAssociator x rows associator).ExactPairingWitness X Y))
    (hasLeftDual : ∀ X : Obj,
      ∃ Y : Obj, Nonempty
        ((dataWithAssociator x rows associator).ExactPairingWitness Y X))
    (weaklyPointed : ∀ X : Obj,
      (dataWithAssociator x rows associator).IsSimple X →
        (dataWithAssociator x rows associator).IsWeaklyInvertible X) :
    Superfusion.CandidateLaws (dataWithAssociator x rows associator) where
  comp_id := Hom.comp_id hx.D
  id_comp := Hom.id_comp hx.D
  comp_assoc := Hom.comp_assoc hx.D
  add_assoc := Hom.add_assoc hx.D
  zero_add := Hom.zero_add hx.D
  add_zero := Hom.add_zero hx.D
  add_comm := Hom.add_comm hx.D
  neg_add := Hom.neg_add hx.D
  one_smul := Hom.one_smul hx.D
  mul_smul := Hom.mul_smul hx.D
  add_smul := Hom.add_smul hx.D
  smul_add := Hom.smul_add hx.D
  zero_smul := Hom.zero_smul hx.D
  smul_zero := Hom.smul_zero hx.D
  add_comp := Hom.add_comp hx.D
  comp_add := Hom.comp_add hx.D
  smul_comp := Hom.smul_comp hx.D
  comp_smul := Hom.comp_smul hx.D
  grade_zero := fun _ _ a => Hom.zero_memGrade hx.D a
  grade_add := fun f g hf hg => Hom.add_memGrade hx.D f g hf hg
  grade_neg := fun f hf => Hom.neg_memGrade hx.D f hf
  grade_smul := fun r f hf => Hom.smul_memGrade hx.D r f hf
  grade_decomposition := Hom.grade_decomposition hx.D
  grade_disjoint := by
    intro X Y f hf₀ hf₁
    change Hom.MemGrade 0 f at hf₀
    change Hom.MemGrade 1 f at hf₁
    change f = Hom.zero x.D X Y
    exact Hom.grade_disjoint hx.D 0 f hf₀ (by simpa using hf₁)
  id_even := Hom.id_even hx.D
  comp_grade := fun f g hf hg => Hom.comp_memGrade hx.D f g hf hg
  tensor_grade := (PairingAdapter.completedTensor x hx).laws.tensor_grade
  tensor_id := (PairingAdapter.completedTensor x hx).laws.tensor_id
  tensor_add_left :=
    (PairingAdapter.completedTensor x hx).laws.tensor_add_left
  tensor_add_right :=
    (PairingAdapter.completedTensor x hx).laws.tensor_add_right
  tensor_smul_left :=
    (PairingAdapter.completedTensor x hx).laws.tensor_smul_left
  tensor_smul_right :=
    (PairingAdapter.completedTensor x hx).laws.tensor_smul_right
  super_interchange :=
    (PairingAdapter.completedTensor x hx).laws.super_interchange
  associator_hom_inv := hAssociator.associator_hom_inv
  associator_inv_hom := hAssociator.associator_inv_hom
  associator_hom_even := hAssociator.associator_hom_even
  associator_inv_even := hAssociator.associator_inv_even
  associator_naturality := hAssociator.associator_naturality
  leftUnitor_hom_inv := hUnitor.leftUnitor_hom_inv
  leftUnitor_inv_hom := hUnitor.leftUnitor_inv_hom
  leftUnitor_hom_even := hUnitor.leftUnitor_hom_even
  leftUnitor_inv_even := hUnitor.leftUnitor_inv_even
  leftUnitor_naturality := hUnitor.leftUnitor_naturality
  rightUnitor_hom_inv := hUnitor.rightUnitor_hom_inv
  rightUnitor_inv_hom := hUnitor.rightUnitor_inv_hom
  rightUnitor_hom_even := hUnitor.rightUnitor_hom_even
  rightUnitor_inv_even := hUnitor.rightUnitor_inv_even
  rightUnitor_naturality := hUnitor.rightUnitor_naturality
  pentagon := hAssociator.pentagon
  triangle := hUnitor.triangle
  has_finite_biproducts := hasFiniteBiproducts
  semisimple := semisimple
  graded_schur := gradedSchur
  finiteDimensional_hom := finiteDimensionalHom
  finite_simple_representatives := finiteSimpleRepresentatives
  simple_unit := simpleUnit
  unitEnd_scalar_injective := unitEndScalarInjective
  unitEnd_scalar_surjective := unitEndScalarSurjective
  has_right_dual := hasRightDual
  has_left_dual := hasLeftDual
  weaklyPointed := weaklyPointed

end Candidate

end Superfusion.RMod.FromRawDCT

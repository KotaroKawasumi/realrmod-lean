import Superfusion.RMod.FromRawDCT.PairingAdapter

/-!
# Completing raw-DCT candidate laws

This abstract proof layer bundles already proved category, tensor,
associator, and unitor laws with separately supplied superfusion and
weak-pointedness proofs.  It adds no executable data and constructs no
concrete instance.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace Candidate

set_option maxHeartbeats 800000 in
/-- Assemble all laws for the exact candidate extracted from `x`.

The lower algebraic and monoidal fields are projections of laws about the
same canonical data.  The final arguments are precisely the genuinely
global finiteness, rigidity, and weak-pointedness properties. -/
def completionLaws (x : RawDCTData) (hx : RawDCTLaws x)
    (rows : UnitRowsData x.D x.C)
    (hAssociator : AssociatorLaws
      (PairingAdapter.completedD x hx).data
      (PairingAdapter.completedD x hx).laws
      (PairingAdapter.completedTensor x hx).data
      (PairingAdapter.completedTensor x hx).laws
      (Associator.canonicalData x))
    (hUnitor : UnitorLaws
      (PairingAdapter.completedD x hx).data
      (PairingAdapter.completedD x hx).laws
      (PairingAdapter.completedTensor x hx).data
      (PairingAdapter.completedTensor x hx).laws
      (PairingAdapter.completedAssociator x hx hAssociator).data
      (PairingAdapter.completedAssociator x hx hAssociator).laws
      (Unitor.canonicalData x rows))
    (hasFiniteBiproducts : ∀ {n : ℕ} (S : Fin n → Obj),
      Nonempty ((data x rows).BiproductWitness S))
    (semisimple : ∀ X : Obj,
      ∃ (n : ℕ) (S : Fin n → Obj),
        (∀ i, (data x rows).IsSimple (S i)) ∧
          Nonempty ((data x rows).DecompositionWitness X S))
    (gradedSchur : ∀ {X Y : Obj},
      (data x rows).IsSimple X → (data x rows).IsSimple Y →
        ∀ {a : ZMod 2} (f : (data x rows).Hom X Y),
          (data x rows).IsHomogeneous a f →
            f ≠ (data x rows).zero → (data x rows).IsIso f)
    (finiteDimensionalHom : ∀ X Y : Obj,
      Nonempty ((data x rows).FiniteBasisWitness X Y))
    (finiteSimpleRepresentatives :
      ∃ (n : ℕ) (S : Fin n → Obj),
        (∀ i, (data x rows).IsSimple (S i)) ∧
          ∀ X : Obj, (data x rows).IsSimple X →
            ∃ (i : Fin n) (a : ZMod 2),
              Nonempty ((data x rows).HomogeneousIso a X (S i)))
    (simpleUnit : (data x rows).IsSimple (data x rows).tensorUnit)
    (unitEndScalarInjective : ∀ r s : ℝ,
      (data x rows).smul r ((data x rows).id (data x rows).tensorUnit) =
        (data x rows).smul s ((data x rows).id (data x rows).tensorUnit) →
          r = s)
    (unitEndScalarSurjective : ∀ f :
      (data x rows).Hom (data x rows).tensorUnit (data x rows).tensorUnit,
        ∃ r : ℝ,
          (data x rows).smul r
              ((data x rows).id (data x rows).tensorUnit) = f)
    (hasRightDual : ∀ X : Obj,
      ∃ Y : Obj, Nonempty ((data x rows).ExactPairingWitness X Y))
    (hasLeftDual : ∀ X : Obj,
      ∃ Y : Obj, Nonempty ((data x rows).ExactPairingWitness Y X))
    (weaklyPointed : ∀ X : Obj,
      (data x rows).IsSimple X → (data x rows).IsWeaklyInvertible X) :
    Superfusion.CandidateLaws (data x rows) where
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
  pentagon := by
    intro W X Y Z
    exact hAssociator.pentagon W X Y Z
  triangle := by
    intro X Y
    exact hUnitor.triangle X Y
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

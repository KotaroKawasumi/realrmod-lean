import RMod.Definitions.RealRModData
import RMod.Definitions.WeaklyPointedSuperfusion
import Superfusion.RMod.FromRawDCT.RealComputableRMod

/-!
# The real regular-module superfusion category

The legacy construction proves all laws on exact finite coordinates. This
module transports those proofs into the public, mathematically named API.
Only proposition-valued existence witnesses require repackaging; the
executable data is unchanged.
-/

set_option autoImplicit false

namespace RMod.Theorems.Internal

private abbrev legacyData : Superfusion.CandidateData :=
  Superfusion.RMod.FromRawDCT.realComputableRModData

private theorem legacyLaws : Superfusion.CandidateLaws legacyData :=
  Superfusion.RMod.FromRawDCT.realComputableRModLaws

/-! ## Compatibility of derived finite sums -/

private theorem finSum_eq_legacy {X Y : realRModData.Obj} :
    ∀ (n : ℕ) (f : Fin n → realRModData.Hom X Y),
      realRModData.finSum n f = legacyData.finSum n f
  | 0, _ => rfl
  | n + 1, f => by
      simp only [WeaklyPointedSuperfusionData.finSum,
        Superfusion.CandidateData.finSum]
      rw [finSum_eq_legacy n]
      rfl

private theorem superFinSum_eq_legacy
    {X Y : realRModData.Obj} {p q : ℕ}
    (f : Fin p ⊕ Fin q → realRModData.Hom X Y) :
    realRModData.superFinSum f = legacyData.superFinSum f := by
  simp only [WeaklyPointedSuperfusionData.superFinSum,
    Superfusion.CandidateData.superFinSum]
  rw [finSum_eq_legacy, finSum_eq_legacy]
  rfl

/-! ## Repackaging of noncomputational witnesses -/

private theorem hasFiniteBiproduct_of_legacy {n : ℕ}
    (S : Fin n → realRModData.Obj)
    (w : legacyData.BiproductWitness S) :
    realRModData.HasFiniteBiproduct S := by
  refine ⟨w.object, w.inclusion, w.projection, ?_, ?_, ?_, ?_, ?_⟩
  · exact w.inclusion_even
  · exact w.projection_even
  · exact w.inclusion_projection_self
  · exact w.inclusion_projection_ne
  · rw [finSum_eq_legacy]
    exact w.projection_inclusion_total

private theorem hasDecomposition_of_legacy
    (X : realRModData.Obj) {n : ℕ} (S : Fin n → realRModData.Obj)
    (w : legacyData.DecompositionWitness X S) :
    realRModData.HasDecomposition X S := by
  refine ⟨w.inclusion, w.projection, ?_, ?_, ?_, ?_, ?_⟩
  · exact w.inclusion_even
  · exact w.projection_even
  · exact w.inclusion_projection_self
  · exact w.inclusion_projection_ne
  · rw [finSum_eq_legacy]
    exact w.projection_inclusion_total

private theorem hasFiniteBasis_of_legacy
    (X Y : realRModData.Obj)
    (w : legacyData.FiniteBasisWitness X Y) :
    realRModData.HasFiniteBasis X Y := by
  refine ⟨w.dimension, w.basis, w.coordinates, ?_, ?_⟩
  · intro f
    rw [finSum_eq_legacy]
    exact w.reconstruct f
  · intro f c h
    apply w.coordinates_unique f c
    rw [← finSum_eq_legacy]
    exact h

private theorem hasHomogeneousIso_of_legacy
    (a : ZMod 2) (X Y : realRModData.Obj)
    (w : legacyData.HomogeneousIso a X Y) :
    realRModData.HasHomogeneousIso a X Y :=
  ⟨w.hom, w.inv, w.hom_inv, w.inv_hom, w.hom_mem, w.inv_mem⟩

private theorem hasExactPairing_of_legacy
    (X Y : realRModData.Obj)
    (w : legacyData.ExactPairingWitness X Y) :
    realRModData.HasExactPairing X Y := by
  refine ⟨w.coeval, w.eval, w.coeval_even, w.eval_even, ?_, ?_⟩
  · simpa only [WeaklyPointedSuperfusionData.whiskerLeft,
      WeaklyPointedSuperfusionData.whiskerRight,
      Superfusion.CandidateData.whiskerLeft,
      Superfusion.CandidateData.whiskerRight, realRModData, legacyData,
      Superfusion.RMod.FromRawDCT.realComputableRModData] using
      w.coevaluation_evaluation
  · simpa only [WeaklyPointedSuperfusionData.whiskerLeft,
      WeaklyPointedSuperfusionData.whiskerRight,
      Superfusion.CandidateData.whiskerLeft,
      Superfusion.CandidateData.whiskerRight, realRModData, legacyData,
      Superfusion.RMod.FromRawDCT.realComputableRModData] using
      w.evaluation_coevaluation

private theorem hasSuperMultiplicity_of_legacy
    (A X : realRModData.Obj) (p q : ℕ)
    (w : legacyData.SuperMultiplicityWitness A X p q) :
    realRModData.HasSuperMultiplicity A X p q := by
  refine ⟨w.inclusion, w.projection, ?_, ?_, ?_, ?_, ?_⟩
  · exact w.inclusion_mem
  · exact w.projection_mem
  · exact w.inclusion_projection_self
  · exact w.inclusion_projection_ne
  · rw [superFinSum_eq_legacy]
    exact w.projection_inclusion_total

private theorem isWeaklyInvertible_of_legacy
    (X : realRModData.Obj)
    (w : legacyData.WeakInvertibilityWitness X) :
    realRModData.IsWeaklyInvertible X := by
  refine ⟨w.dual, hasExactPairing_of_legacy X w.dual w.pairing,
    w.evenMultiplicity, w.oddMultiplicity, w.multiplicity_pos, ?_⟩
  exact hasSuperMultiplicity_of_legacy
    (realRModData.tensorObj X w.dual) realRModData.tensorUnit
    w.evenMultiplicity w.oddMultiplicity w.multiplicity

/-! ## Laws and final structure -/

set_option maxHeartbeats 1600000 in
/-- All weakly pointed superfusion laws for `realRModData`. -/
theorem realRModLaws : WeaklyPointedSuperfusionLaws realRModData := by
  refine {
    comp_id := ?_
    id_comp := ?_
    comp_assoc := ?_
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    add_comm := ?_
    neg_add := ?_
    one_smul := ?_
    mul_smul := ?_
    add_smul := ?_
    smul_add := ?_
    zero_smul := ?_
    smul_zero := ?_
    add_comp := ?_
    comp_add := ?_
    smul_comp := ?_
    comp_smul := ?_
    grade_zero := ?_
    grade_add := ?_
    grade_neg := ?_
    grade_smul := ?_
    grade_decomposition := ?_
    grade_disjoint := ?_
    id_even := ?_
    comp_grade := ?_
    tensor_grade := ?_
    tensor_id := ?_
    tensor_add_left := ?_
    tensor_add_right := ?_
    tensor_smul_left := ?_
    tensor_smul_right := ?_
    super_interchange := ?_
    associator_hom_inv := ?_
    associator_inv_hom := ?_
    associator_hom_even := ?_
    associator_inv_even := ?_
    associator_naturality := ?_
    left_unitor_hom_inv := ?_
    left_unitor_inv_hom := ?_
    left_unitor_hom_even := ?_
    left_unitor_inv_even := ?_
    left_unitor_naturality := ?_
    right_unitor_hom_inv := ?_
    right_unitor_inv_hom := ?_
    right_unitor_hom_even := ?_
    right_unitor_inv_even := ?_
    right_unitor_naturality := ?_
    pentagon := ?_
    triangle := ?_
    has_finite_biproducts := ?_
    semisimple := ?_
    graded_schur := ?_
    finite_dimensional_hom := ?_
    finite_simple_representatives := ?_
    simple_unit := ?_
    unit_end_scalar_injective := ?_
    unit_end_scalar_surjective := ?_
    has_right_dual := ?_
    has_left_dual := ?_
    weakly_pointed := ?_ }
  · exact legacyLaws.comp_id
  · exact legacyLaws.id_comp
  · exact legacyLaws.comp_assoc
  · exact legacyLaws.add_assoc
  · exact legacyLaws.zero_add
  · exact legacyLaws.add_zero
  · exact legacyLaws.add_comm
  · exact legacyLaws.neg_add
  · exact legacyLaws.one_smul
  · exact legacyLaws.mul_smul
  · exact legacyLaws.add_smul
  · exact legacyLaws.smul_add
  · exact legacyLaws.zero_smul
  · exact legacyLaws.smul_zero
  · exact legacyLaws.add_comp
  · exact legacyLaws.comp_add
  · exact legacyLaws.smul_comp
  · exact legacyLaws.comp_smul
  · exact legacyLaws.grade_zero
  · exact legacyLaws.grade_add
  · exact legacyLaws.grade_neg
  · exact legacyLaws.grade_smul
  · exact legacyLaws.grade_decomposition
  · exact legacyLaws.grade_disjoint
  · exact legacyLaws.id_even
  · exact legacyLaws.comp_grade
  · exact legacyLaws.tensor_grade
  · exact legacyLaws.tensor_id
  · exact legacyLaws.tensor_add_left
  · exact legacyLaws.tensor_add_right
  · exact legacyLaws.tensor_smul_left
  · exact legacyLaws.tensor_smul_right
  · exact legacyLaws.super_interchange
  · exact legacyLaws.associator_hom_inv
  · exact legacyLaws.associator_inv_hom
  · exact legacyLaws.associator_hom_even
  · exact legacyLaws.associator_inv_even
  · exact legacyLaws.associator_naturality
  · exact legacyLaws.leftUnitor_hom_inv
  · exact legacyLaws.leftUnitor_inv_hom
  · exact legacyLaws.leftUnitor_hom_even
  · exact legacyLaws.leftUnitor_inv_even
  · exact legacyLaws.leftUnitor_naturality
  · exact legacyLaws.rightUnitor_hom_inv
  · exact legacyLaws.rightUnitor_inv_hom
  · exact legacyLaws.rightUnitor_hom_even
  · exact legacyLaws.rightUnitor_inv_even
  · exact legacyLaws.rightUnitor_naturality
  · simpa only [WeaklyPointedSuperfusionData.whiskerLeft,
      WeaklyPointedSuperfusionData.whiskerRight,
      Superfusion.CandidateData.whiskerLeft,
      Superfusion.CandidateData.whiskerRight, realRModData, legacyData,
      Superfusion.RMod.FromRawDCT.realComputableRModData] using
      legacyLaws.pentagon
  · simpa only [WeaklyPointedSuperfusionData.whiskerLeft,
      WeaklyPointedSuperfusionData.whiskerRight,
      Superfusion.CandidateData.whiskerLeft,
      Superfusion.CandidateData.whiskerRight, realRModData, legacyData,
      Superfusion.RMod.FromRawDCT.realComputableRModData] using
      legacyLaws.triangle
  · intro n S
    rcases legacyLaws.has_finite_biproducts S with ⟨w⟩
    exact hasFiniteBiproduct_of_legacy S w
  · intro X
    rcases legacyLaws.semisimple X with ⟨n, S, hSimple, ⟨w⟩⟩
    exact ⟨n, S, hSimple, hasDecomposition_of_legacy X S w⟩
  · exact legacyLaws.graded_schur
  · intro X Y
    rcases legacyLaws.finiteDimensional_hom X Y with ⟨w⟩
    exact hasFiniteBasis_of_legacy X Y w
  · rcases legacyLaws.finite_simple_representatives with
      ⟨n, S, hSimple, hRepresentative⟩
    refine ⟨n, S, hSimple, ?_⟩
    intro X hX
    rcases hRepresentative X hX with ⟨i, a, ⟨w⟩⟩
    exact ⟨i, a, hasHomogeneousIso_of_legacy a X (S i) w⟩
  · exact legacyLaws.simple_unit
  · exact legacyLaws.unitEnd_scalar_injective
  · exact legacyLaws.unitEnd_scalar_surjective
  · intro X
    rcases legacyLaws.has_right_dual X with ⟨Y, ⟨w⟩⟩
    exact ⟨Y, hasExactPairing_of_legacy X Y w⟩
  · intro X
    rcases legacyLaws.has_left_dual X with ⟨Y, ⟨w⟩⟩
    exact ⟨Y, hasExactPairing_of_legacy Y X w⟩
  · intro X hX
    rcases legacyLaws.weaklyPointed X hX with ⟨w⟩
    exact isWeaklyInvertible_of_legacy X w

end RMod.Theorems.Internal

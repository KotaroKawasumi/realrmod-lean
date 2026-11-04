import RMod.Classification.Instances.ScalarReplacement
import RMod.Classification.Proofs.ConvolutionScalarUnit
import RMod.Classification.Proofs.ConvolutionScalarAssociativity

/-!
# A scalar cochain change gives an actual monoidal superequivalence

The cochain identity supplies the proved associativity diagram on all
families. Normalized scalar comparisons are identities on unit
convolutions. Both underlying superfunctors and all inverse comparisons
are the specified componentwise identities, with their laws verified.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (omega : t.data.group → t.data.group → t.data.group → ℝˣ)
  (h : TwistLaws (omegaReplacementData t.data omega))
  (beta : t.data.group → t.data.group → ℝˣ)
  (hbetaL : ∀ g, beta 1 g = 1) (hbetaR : ∀ g, beta g 1 = 1)
  (hw : ∀ g h k, (beta g h * beta (g * h) k) * t.data.omega g h k =
    omega g h k * (beta h k * beta g (h * k)))

include hbetaL hbetaR hw

theorem scalarReplacementMonoidalLaws :
    MonoidalSuperfunctorLaws (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData
      (scalarReplacementMonoidalData C hC t omega h beta) where
  toSuperfunctorLaws := omegaReplacementForwardLaws C hC t omega h
  tensor_hom_even X Y := fun k => (convolutionScalar_evenIso C hC t.data beta X Y k).hom_even
  tensor_inv_even X Y := fun k => (convolutionScalar_evenIso C hC t.data beta X Y k).inv_even
  tensor_hom_inv X Y := funext fun k => (convolutionScalar_evenIso C hC t.data beta X Y k).hom_inv
  tensor_inv_hom X Y := funext fun k => (convolutionScalar_evenIso C hC t.data beta X Y k).inv_hom
  unit_hom_even := fun k => hC.id_even (pullbackUnitObj C hC t.data k).val
  unit_inv_even := fun k => hC.id_even (pullbackUnitObj C hC t.data k).val
  unit_hom_inv := funext fun k => hC.id_comp (C.id (pullbackUnitObj C hC t.data k).val)
  unit_inv_hom := funext fun k => hC.id_comp (C.id (pullbackUnitObj C hC t.data k).val)
  tensor_naturality f g := funext fun k => convolutionScalar_naturality C hC t.data beta f g k
  associativity X Y Z := by
    funext k
    exact (congrFun (convolutionScalar_associativity C hC t.data t.laws.normalizer_parity
      omega beta hw X Y Z) k).trans (hC.comp_assoc _ _ _).symm
  left_unit X := by
    funext k
    change C.comp (C.comp (convolutionHom C hC t.data
      (fun j => C.id (pullbackUnitObj C hC t.data j).val) (fun j => C.id (X j).val) k)
      (convolutionScalarData C hC t.data beta (pullbackUnitObj C hC t.data) X k).hom)
      (convolutionLeftUnitorData C hC t.data t.laws X k).hom =
      (convolutionLeftUnitorData C hC t.data t.laws X k).hom
    rw [convolutionHom_id, hC.id_comp, convolutionScalar_unit_left C hC t.data beta hbetaL, hC.id_comp]
  right_unit X := by
    funext k
    change C.comp (C.comp (convolutionHom C hC t.data
      (fun j => C.id (X j).val) (fun j => C.id (pullbackUnitObj C hC t.data j).val) k)
      (convolutionScalarData C hC t.data beta X (pullbackUnitObj C hC t.data) k).hom)
      (convolutionRightUnitorData C hC t.data t.laws X k).hom =
      (convolutionRightUnitorData C hC t.data t.laws X k).hom
    rw [convolutionHom_id, hC.id_comp, convolutionScalar_unit_right C hC t.data beta hbetaR, hC.id_comp]

theorem scalarReplacementEquivalenceLaws :
    MonoidalSuperequivalenceLaws (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData
      (scalarReplacementEquivalenceData C hC t omega h beta) where
  forward := scalarReplacementMonoidalLaws C hC t omega h beta hbetaL hbetaR hw
  backward := omegaReplacementBackwardLaws C hC t omega h
  unit_hom_even X k := hC.id_even (X k).val
  unit_inv_even X k := hC.id_even (X k).val
  unit_hom_inv X := funext fun k => hC.id_comp (C.id (X k).val)
  unit_inv_hom X := funext fun k => hC.id_comp (C.id (X k).val)
  counit_hom_even Y k := hC.id_even (Y k).val
  counit_inv_even Y k := hC.id_even (Y k).val
  counit_hom_inv Y := funext fun k => hC.id_comp (C.id (Y k).val)
  counit_inv_hom Y := funext fun k => hC.id_comp (C.id (Y k).val)
  unit_naturality f := funext fun k => (hC.comp_id (f k)).trans (hC.id_comp (f k)).symm
  counit_naturality f := funext fun k => (hC.comp_id (f k)).trans (hC.id_comp (f k)).symm

theorem scalarReplacement_equivalent :
    Equivalent (twistedPullback C hC t) (twistedPullback C hC (omegaReplacement t omega h)) :=
  ⟨⟨scalarReplacementEquivalenceData C hC t omega h beta,
    scalarReplacementEquivalenceLaws C hC t omega h beta hbetaL hbetaR hw⟩⟩

end RMod.Classification

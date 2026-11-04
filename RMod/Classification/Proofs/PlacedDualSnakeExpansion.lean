import RMod.Classification.Instances.PlacedDualSnakeBlock
import RMod.Classification.Proofs.PlacedDualInsertions
import RMod.Classification.Proofs.ConvolutionInversePairBlock
import RMod.Classification.Instances.ConvolutionPairings

/-!
# Expanding the actual normalized first snake at its support

The inverse left unitor enters the unit summand, tensoring coevaluation
enters the inverse-pair triple, and the associator crosses to the right
triple. Evaluation and the right unitor leave through their matching
summands. These exact insertion equations give the surviving raw block.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily
  convolutionEvenFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

theorem placedNormalizedSnake_at :
    normalizedXSnake (D := ConvolutionCategory C hC t ht)
      (placedTwistedCoevaluation C hC t g hX q) (placedTwistedEvaluation C hC t ht g hX q) g =
        placedFirstSnakeBlock C hC t ht g hX q := by
  let A := placedObj C hC t g X hX
  let B := placedRightDualObj C hC t g hX q
  let η := placedTwistedCoevaluation C hC t g hX q
  let ε := placedTwistedEvaluation C hC t ht g hX q
  let iA : PullbackHom C t A A := fun k => C.id (A k).val
  change C.comp (convolutionLeftUnitorData C hC t ht A g).inv
    (C.comp (convolutionHom C hC t η iA g)
      (C.comp (convolutionAssociatorData C hC t ht A B A g).hom
        (C.comp (convolutionHom C hC t iA ε g) (convolutionRightUnitorData C hC t ht A g).hom))) = _
  rw [convolutionLeftUnitor_inverse_inclusion, hC.comp_assoc]
  rw [← hC.comp_assoc (convolutionInclusion C hC t (pullbackUnitObj C hC t) A g 1)
    (convolutionHom C hC t η iA g), placedTwistedCoevaluation_tensor_inclusion]
  simp only [hC.comp_assoc]
  rw [← hC.comp_assoc (convolutionLeftInsertionEven C hC t A B A g 1 g).hom
    (convolutionAssociatorData C hC t ht A B A g).hom, convolutionAssociator_inverse_pair_inclusion]
  simp only [hC.comp_assoc]
  rw [← hC.comp_assoc (convolutionRightInsertionEven C hC t A B A g g g⁻¹).hom
    (convolutionHom C hC t iA ε g), convolutionRightInsertion_outer_map]
  simp only [hC.comp_assoc]
  rw [convolutionRightUnitor_inclusion]
  rfl

end RMod.Classification

import RMod.Classification.Proofs.PlacedDualSnakeExpansion
import RMod.Classification.Proofs.PlacedDualSnakeBlock
import RMod.Classification.Proofs.PlacedDualCompletion
import RMod.Classification.Proofs.DualSchur

/-!
# Both snake identities for the specified placed pairing

The first normalized snake is determined by the support coordinate,
where its expansion is the local weighted snake. The even Schur property
of the opposite dual then supplies the second snake for these same maps.
In particular every placed simple has the specified right dual.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

theorem placedNormalizedSnake_eq_id :
    normalizedXSnake (D := ConvolutionCategory C hC t ht)
      (placedTwistedCoevaluation C hC t g hX q) (placedTwistedEvaluation C hC t ht g hX q) =
        @CategoryStruct.id (ConvolutionCategory C hC t ht) _ (placedObj C hC t g X hX) := by
  apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws
  · intro k hk
    rw [placedObj_away C hC t g X hX k hk]
    exact pullbackZero_id C hC t k
  · exact (placedNormalizedSnake_at C hC t ht g hX q).trans
      (placedFirstSnakeBlock_eq_id C hC t ht g hX q)

theorem placedTwistedPairingLaws
    (hXne : C.id X ≠ C.zero)
    (hY : ∀ f : C.Hom Y Y, C.IsHomogeneous 0 f → f ≠ C.zero → C.IsEvenIso f) :
    DualPairingLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (placedTwistedPairingData C hC t ht g hX q) :=
  placedTwistedPairingLaws_of_first C hC t ht g hX q hXne hY
    (placedNormalizedSnake_eq_id C hC t ht g hX q)

theorem placedSimpleTwistedPairingLaws (hs : C.IsSimple X) :
    DualPairingLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (placedTwistedPairingData C hC t ht g hX q) :=
  placedTwistedPairingLaws C hC t ht g hX q
    (simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hs) (q.right_even_schur hs)

end RMod.Classification

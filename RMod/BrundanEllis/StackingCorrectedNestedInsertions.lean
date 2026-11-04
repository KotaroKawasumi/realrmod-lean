import RMod.BrundanEllis.StackingCorrectedNestedBinary
import RMod.BrundanEllis.StackingReferenceWeightedBinaryNaturality
import RMod.BrundanEllis.StackingCorrectedTripleInsertions
import RMod.Classification.Proofs.TensorWhiskerCalculus
import RMod.Classification.Proofs.ConvolutionProductTripleExt

/-! Coherence of the corrected exterior tensor comparison and normalization of its unit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data
local notation "hR" => referenceProperty
attribute [local irreducible] correctedExteriorBinaryData

/-- Moving the pair of inner convolution inclusions through the left outer
comparison retains precisely the specified weighted local binary map. -/
theorem correctedExteriorLeftOuter_inclusion (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :
    let XX := convolutionObj R hR (oldTwist s).data X X'
    let YY := convolutionObj R hR (oldTwist t).data Y Y'
    let iS := convolutionProductInclusion R hR (oldTwist s).data X X' g g'
    let iT := convolutionProductInclusion R hR (oldTwist t).data Y Y' h h'
    let jL := (referenceBinaryBlockData (s.rho (g * g')).toAdd (t.rho h'').toAdd
      (twistSummand R (oldTwist t).data Y Y' h h')
      (twistSummand R (oldTwist s).data X X' g g')
      (Y'' h'').val (X'' g'').val
      (twistSummand_inComponent R hR (oldTwist s).data X X' g g')
      (Y'' h'').property (s.nu (g * g') g'') (t.nu (h * h') h'')).scale
        (R).toWeaklyPointedSuperfusionData
        (realSign (exteriorComparisonExponent s t (g * g') g'' (h * h') h''))
    (R).comp
      ((R).tensorHom
        ((R).tensorHom ((R).tensorHom iT iS)
          ((R).id ((R).tensorObj (Y'' h'').val (X'' g'').val)))
        ((R).id ((R).pi.factor ((exteriorTwist s t).val.nu (g * g', h * h') (g'', h'')))))
      (correctedExteriorBinaryData s t XX X'' YY Y'' (g * g') g'' (h * h') h'').hom =
    (R).comp jL.hom
      ((R).tensorHom
        ((R).tensorHom ((R).tensorHom iT ((R).id (Y'' h'').val))
          ((R).id ((R).pi.factor (t.nu (h * h') h''))))
        ((R).tensorHom ((R).tensorHom iS ((R).id (X'' g'').val))
          ((R).id ((R).pi.factor (s.nu (g * g') g''))))) := by
  dsimp only
  rw [correctedExteriorBinary_hom]
  have hn := referenceWeightedBinary_even_naturality
    (s.rho (g * g')).toAdd (t.rho h'').toAdd
    (twistSummand R (oldTwist t).data Y Y' h h')
    (convolutionObj R hR (oldTwist t).data Y Y' (h * h')).val
    (twistSummand R (oldTwist s).data X X' g g')
    (convolutionObj R hR (oldTwist s).data X X' (g * g')).val
    (Y'' h'').val (Y'' h'').val (X'' g'').val (X'' g'').val
    (twistSummand_inComponent R hR (oldTwist s).data X X' g g')
    (convolutionObj R hR (oldTwist s).data X X' (g * g')).property
    (Y'' h'').property (Y'' h'').property
    (convolutionProductInclusion R hR (oldTwist t).data Y Y' h h')
    (convolutionProductInclusion R hR (oldTwist s).data X X' g g')
    ((R).id (Y'' h'').val) ((R).id (X'' g'').val)
    (s.nu (g * g') g'') (t.nu (h * h') h'')
    (realSign (exteriorComparisonExponent s t (g * g') g'' (h * h') h''))
    (convolutionProductInclusion_grade R hR (oldTwist t).data Y Y' h h')
    (convolutionProductInclusion_grade R hR (oldTwist s).data X X' g g')
    ((hR).id_even _) ((hR).id_even _)
  simp only [(hR).tensor_id] at hn
  with_unfolding_all exact hn

/-- The same naturality transports the inner inclusions of the right route. -/
theorem correctedExteriorRightOuter_inclusion (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :
    let XX := convolutionObj R hR (oldTwist s).data X' X''
    let YY := convolutionObj R hR (oldTwist t).data Y' Y''
    let iS := convolutionProductInclusion R hR (oldTwist s).data X' X'' g' g''
    let iT := convolutionProductInclusion R hR (oldTwist t).data Y' Y'' h' h''
    let jR := (referenceBinaryBlockData (s.rho g).toAdd (t.rho (h' * h'')).toAdd
      (Y h).val (X g).val
      (twistSummand R (oldTwist t).data Y' Y'' h' h'')
      (twistSummand R (oldTwist s).data X' X'' g' g'')
      (X g).property
      (twistSummand_inComponent R hR (oldTwist t).data Y' Y'' h' h'')
      (s.nu g (g' * g'')) (t.nu h (h' * h''))).scale (R).toWeaklyPointedSuperfusionData
        (realSign (exteriorComparisonExponent s t g (g' * g'') h (h' * h'')))
    (R).comp
      ((R).tensorHom
        ((R).tensorHom ((R).id ((R).tensorObj (Y h).val (X g).val)) ((R).tensorHom iT iS))
        ((R).id ((R).pi.factor ((exteriorTwist s t).val.nu (g, h) (g' * g'', h' * h'')))))
      (correctedExteriorBinaryData s t X XX Y YY g (g' * g'') h (h' * h'')).hom =
    (R).comp jR.hom
      ((R).tensorHom
        ((R).tensorHom ((R).tensorHom ((R).id (Y h).val) iT)
          ((R).id ((R).pi.factor (t.nu h (h' * h'')))))
        ((R).tensorHom ((R).tensorHom ((R).id (X g).val) iS)
          ((R).id ((R).pi.factor (s.nu g (g' * g'')))))) := by
  dsimp only
  rw [correctedExteriorBinary_hom]
  have hn := referenceWeightedBinary_even_naturality
    (s.rho g).toAdd (t.rho (h' * h'')).toAdd
    (Y h).val (Y h).val (X g).val (X g).val
    (twistSummand R (oldTwist t).data Y' Y'' h' h'')
    (convolutionObj R hR (oldTwist t).data Y' Y'' (h' * h'')).val
    (twistSummand R (oldTwist s).data X' X'' g' g'')
    (convolutionObj R hR (oldTwist s).data X' X'' (g' * g'')).val
    (X g).property (X g).property
    (twistSummand_inComponent R hR (oldTwist t).data Y' Y'' h' h'')
    (convolutionObj R hR (oldTwist t).data Y' Y'' (h' * h'')).property
    ((R).id (Y h).val) ((R).id (X g).val)
    (convolutionProductInclusion R hR (oldTwist t).data Y' Y'' h' h'')
    (convolutionProductInclusion R hR (oldTwist s).data X' X'' g' g'')
    (s.nu g (g' * g'')) (t.nu h (h' * h''))
    (realSign (exteriorComparisonExponent s t g (g' * g'') h (h' * h'')))
    ((hR).id_even _) ((hR).id_even _)
    (convolutionProductInclusion_grade R hR (oldTwist t).data Y' Y'' h' h'')
    (convolutionProductInclusion_grade R hR (oldTwist s).data X' X'' g' g'')
  simp only [(hR).tensor_id] at hn
  with_unfolding_all exact hn

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data
local notation "hR" => referenceProperty
attribute [local irreducible] correctedExteriorTensoratorData correctedExteriorBinaryData

theorem correctedExteriorNestedLeft_inclusions (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :
    let u := (oldTwist (exteriorTwist s t).val).data
    let F := reversedExteriorPairing s t
    let XX := convolutionObj R hR (oldTwist s).data X X'
    let YY := convolutionObj R hR (oldTwist t).data Y Y'
    (R).comp
      ((R).comp
        ((R).tensorHom
          ((R).tensorHom
            ((R).comp (correctedExteriorBinaryData s t X X' Y Y' g g' h h').hom
              ((R).tensorHom
                (convolutionProductInclusion R hR (oldTwist t).data Y Y' h h')
                (convolutionProductInclusion R hR (oldTwist s).data X X' g g')))
            ((R).id (F.obj (X'', Y'') (g'', h'')).val))
          ((R).id ((R).pi.factor (u.nu (g * g', h * h') (g'', h'')))))
        (correctedExteriorBinaryData s t XX X'' YY Y'' (g * g') g'' (h * h') h'').hom)
      ((R).tensorHom
        (convolutionProductInclusion R hR (oldTwist t).data YY Y'' (h * h') h'')
        (convolutionProductInclusion R hR (oldTwist s).data XX X'' (g * g') g'')) =
    (R).comp (correctedExteriorLeftBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
      ((R).tensorHom
        (convolutionProductLeftInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
        (convolutionProductLeftInsertion R hR (oldTwist s).data X X' X'' g g' g'')) := by
  dsimp only
  rw [tensor_right_right_comp (hR).toWeaklyPointedSuperfusionLaws]
  dsimp only [correctedExteriorLeftBinaryData, IsoData.trans, IsoData.tensor, IsoData.refl]
  simp only [(hR).comp_assoc]
  with_unfolding_all apply congrArg ((R).comp _)
  rw [← (hR).comp_assoc]
  with_unfolding_all
    refine (congrArg (fun m => (R).comp m ((R).tensorHom
        (convolutionProductInclusion R hR (oldTwist t).data
          (convolutionObj R hR (oldTwist t).data Y Y') Y'' (h * h') h'')
        (convolutionProductInclusion R hR (oldTwist s).data
          (convolutionObj R hR (oldTwist s).data X X') X'' (g * g') g'')))
      (correctedExteriorLeftOuter_inclusion s t X X' X'' Y Y' Y'' g g' g'' h h' h'')).trans ?_
  rw [(hR).comp_assoc]
  with_unfolding_all apply congrArg ((R).comp _)
  rw [interchange_second_even (hR).toWeaklyPointedSuperfusionLaws _ _ _ _
    (convolutionProductInclusion_grade R hR (oldTwist s).data (convolutionObj R hR (oldTwist s).data X X') X'' (g * g') g'')]
  rfl

theorem correctedExteriorNestedRight_inclusions (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :
    let u := (oldTwist (exteriorTwist s t).val).data
    let F := reversedExteriorPairing s t
    let XX := convolutionObj R hR (oldTwist s).data X' X''
    let YY := convolutionObj R hR (oldTwist t).data Y' Y''
    (R).comp
      ((R).comp
        ((R).tensorHom
          ((R).tensorHom ((R).id (F.obj (X, Y) (g, h)).val)
            ((R).comp (correctedExteriorBinaryData s t X' X'' Y' Y'' g' g'' h' h'').hom
              ((R).tensorHom
                (convolutionProductInclusion R hR (oldTwist t).data Y' Y'' h' h'')
                (convolutionProductInclusion R hR (oldTwist s).data X' X'' g' g''))))
          ((R).id ((R).pi.factor (u.nu (g, h) (g' * g'', h' * h'')))))
        (correctedExteriorBinaryData s t X XX Y YY g (g' * g'') h (h' * h'')).hom)
      ((R).tensorHom
        (convolutionProductInclusion R hR (oldTwist t).data Y YY h (h' * h''))
        (convolutionProductInclusion R hR (oldTwist s).data X XX g (g' * g''))) =
    (R).comp (correctedExteriorRightBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
      ((R).tensorHom
        (convolutionProductRightInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
        (convolutionProductRightInsertion R hR (oldTwist s).data X X' X'' g g' g'')) := by
  dsimp only
  rw [tensor_left_right_comp (hR).toWeaklyPointedSuperfusionLaws]
  dsimp only [correctedExteriorRightBinaryData, IsoData.trans, IsoData.tensor, IsoData.refl]
  simp only [(hR).comp_assoc]
  with_unfolding_all apply congrArg ((R).comp _)
  rw [← (hR).comp_assoc]
  with_unfolding_all
    refine (congrArg (fun m => (R).comp m ((R).tensorHom
        (convolutionProductInclusion R hR (oldTwist t).data Y
          (convolutionObj R hR (oldTwist t).data Y' Y'') h (h' * h''))
        (convolutionProductInclusion R hR (oldTwist s).data X
          (convolutionObj R hR (oldTwist s).data X' X'') g (g' * g''))))
      (correctedExteriorRightOuter_inclusion s t X X' X'' Y Y' Y'' g g' g'' h h' h'')).trans ?_
  rw [(hR).comp_assoc]
  with_unfolding_all apply congrArg ((R).comp _)
  rw [interchange_second_even (hR).toWeaklyPointedSuperfusionLaws _ _ _ _
    (convolutionProductInclusion_grade R hR (oldTwist s).data X (convolutionObj R hR (oldTwist s).data X' X'') g (g' * g''))]
  rfl

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data
local notation "hR" => referenceProperty
attribute [local irreducible] correctedExteriorTensoratorData correctedExteriorBinaryData

theorem correctedExteriorProductLeft_tensorators (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :
    let u := (oldTwist (exteriorTwist s t).val).data
    let F := reversedExteriorPairing s t
    let XX := convolutionObj R hR (oldTwist s).data X X'
    let YY := convolutionObj R hR (oldTwist t).data Y Y'
    (R).comp
      ((R).comp (convolutionProductLeftInsertion R hR u
        (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) (g, h) (g', h') (g'', h''))
        (convolutionHom R hR u
          (fun ab => (correctedExteriorTensoratorData s t X X' Y Y' ab.1 ab.2).hom)
          (fun ab => (R).id (F.obj (X'', Y'') ab).val) ((g * g') * g'', (h * h') * h'')))
      (correctedExteriorTensoratorData s t XX X'' YY Y'' ((g * g') * g'') ((h * h') * h'')).hom =
    (R).comp (correctedExteriorLeftBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
      ((R).tensorHom
        (convolutionProductLeftInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
        (convolutionProductLeftInsertion R hR (oldTwist s).data X X' X'' g g' g'')) := by
  exact (correctedExteriorTensorator_leftInsertion s t X X' X'' Y Y' Y'' g g' g'' h h' h'').trans
    (correctedExteriorNestedLeft_inclusions s t X X' X'' Y Y' Y'' g g' g'' h h' h'')

theorem correctedExteriorProductRight_tensorators (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :
    let u := (oldTwist (exteriorTwist s t).val).data
    let F := reversedExteriorPairing s t
    let XX := convolutionObj R hR (oldTwist s).data X' X''
    let YY := convolutionObj R hR (oldTwist t).data Y' Y''
    (R).comp
      ((R).comp (convolutionProductRightInsertion R hR u
        (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) (g, h) (g', h') (g'', h''))
        (convolutionHom R hR u
          (fun ab => (R).id (F.obj (X, Y) ab).val)
          (fun ab => (correctedExteriorTensoratorData s t X' X'' Y' Y'' ab.1 ab.2).hom)
          (g * (g' * g''), h * (h' * h''))))
      (correctedExteriorTensoratorData s t X XX Y YY (g * (g' * g'')) (h * (h' * h''))).hom =
    (R).comp (correctedExteriorRightBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
      ((R).tensorHom
        (convolutionProductRightInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
        (convolutionProductRightInsertion R hR (oldTwist s).data X X' X'' g g' g'')) := by
  exact (correctedExteriorTensorator_rightInsertion s t X X' X'' Y Y' Y'' g g' g'' h h' h'').trans
    (correctedExteriorNestedRight_inclusions s t X X' X'' Y Y' Y'' g g' g'' h h' h'')

end RMod.BrundanEllis.Stacking

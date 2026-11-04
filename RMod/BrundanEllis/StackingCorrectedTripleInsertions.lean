import RMod.BrundanEllis.StackingCorrectedProductInclusion
import RMod.Classification.Proofs.ConvolutionProductPartialMaps

/-! Coordinate and summand formulas for the actual corrected exterior tensor comparison. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
attribute [local irreducible] correctedExteriorTensoratorData correctedExteriorBinaryData
local notation "R" => reference.data
local notation "hR" => referenceProperty

/-- On a left-associated triple summand, the assembled tensorators reduce
exactly to their inner and outer binary comparisons and the retained inclusions. -/
theorem correctedExteriorTensorator_leftInsertion (s t : Twist)
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
        (convolutionProductInclusion R hR (oldTwist s).data XX X'' (g * g') g'')) := by
  dsimp only
  let u := (oldTwist (exteriorTwist s t).val).data
  let F := reversedExteriorPairing s t
  let XX := convolutionObj R hR (oldTwist s).data X X'
  let YY := convolutionObj R hR (oldTwist t).data Y Y'
  let f : PullbackHom R u (convolutionObj R hR u (F.obj (X, Y)) (F.obj (X', Y')))
      (F.obj (XX, YY)) := fun ab => (correctedExteriorTensoratorData s t X X' Y Y' ab.1 ab.2).hom
  let z : PullbackHom R u (F.obj (X'', Y'')) (F.obj (X'', Y'')) := fun ab => (R).id _
  let outer := (correctedExteriorTensoratorData s t XX X'' YY Y'' ((g * g') * g'') ((h * h') * h'')).hom
  let j := (correctedExteriorBinaryData s t XX X'' YY Y'' (g * g') g'' (h * h') h'').hom
  let inc := (R).tensorHom
    (convolutionProductInclusion R hR (oldTwist t).data YY Y'' (h * h') h'')
    (convolutionProductInclusion R hR (oldTwist s).data XX X'' (g * g') g'')
  let W := fun m : (R).Hom (twistSummand R u (F.obj (X, Y)) (F.obj (X', Y')) (g, h) (g', h'))
      (F.obj (XX, YY) (g * g', h * h')).val =>
    (R).tensorHom ((R).tensorHom m ((R).id (F.obj (X'', Y'') (g'', h'')).val))
      ((R).id ((R).pi.factor (u.nu (g * g', h * h') (g'', h''))))
  have hm := convolutionProductLeftInsertion_outer_map R hR u f z (g, h) (g', h') (g'', h'')
  have hi := correctedExteriorTensorator_productInclusion s t X X' Y Y' g g' h h'
  have ho := correctedExteriorTensorator_productInclusion s t XX X'' YY Y'' (g * g') g'' (h * h') h''
  exact (congrArg (fun m => (R).comp m outer) hm).trans
    (((hR).comp_assoc _ _ _).trans
      ((congrArg ((R).comp (W ((R).comp
        (convolutionProductInclusion R hR u (F.obj (X, Y)) (F.obj (X', Y')) (g, h) (g', h'))
        (f (g * g', h * h'))))) ho).trans
        ((congrArg (fun m => (R).comp (W m) ((R).comp j inc)) hi).trans
          ((hR).comp_assoc _ _ _).symm)))

/-- The right-associated route has the analogous exact binary reduction. -/
theorem correctedExteriorTensorator_rightInsertion (s t : Twist)
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
        (convolutionProductInclusion R hR (oldTwist s).data X XX g (g' * g''))) := by
  dsimp only
  let u := (oldTwist (exteriorTwist s t).val).data
  let F := reversedExteriorPairing s t
  let XX := convolutionObj R hR (oldTwist s).data X' X''
  let YY := convolutionObj R hR (oldTwist t).data Y' Y''
  let x : PullbackHom R u (F.obj (X, Y)) (F.obj (X, Y)) := fun ab => (R).id _
  let f : PullbackHom R u (convolutionObj R hR u (F.obj (X', Y')) (F.obj (X'', Y'')))
      (F.obj (XX, YY)) := fun ab => (correctedExteriorTensoratorData s t X' X'' Y' Y'' ab.1 ab.2).hom
  let outer := (correctedExteriorTensoratorData s t X XX Y YY (g * (g' * g'')) (h * (h' * h''))).hom
  let j := (correctedExteriorBinaryData s t X XX Y YY g (g' * g'') h (h' * h'')).hom
  let inc := (R).tensorHom
    (convolutionProductInclusion R hR (oldTwist t).data Y YY h (h' * h''))
    (convolutionProductInclusion R hR (oldTwist s).data X XX g (g' * g''))
  let W := fun m : (R).Hom (twistSummand R u (F.obj (X', Y')) (F.obj (X'', Y'')) (g', h') (g'', h''))
      (F.obj (XX, YY) (g' * g'', h' * h'')).val =>
    (R).tensorHom ((R).tensorHom ((R).id (F.obj (X, Y) (g, h)).val) m)
      ((R).id ((R).pi.factor (u.nu (g, h) (g' * g'', h' * h''))))
  have hm := convolutionProductRightInsertion_outer_map R hR u x f (g, h) (g', h') (g'', h'')
  have hi := correctedExteriorTensorator_productInclusion s t X' X'' Y' Y'' g' g'' h' h''
  have ho := correctedExteriorTensorator_productInclusion s t X XX Y YY g (g' * g'') h (h' * h'')
  exact (congrArg (fun m => (R).comp m outer) hm).trans
    (((hR).comp_assoc _ _ _).trans
      ((congrArg ((R).comp (W ((R).comp
        (convolutionProductInclusion R hR u (F.obj (X', Y')) (F.obj (X'', Y'')) (g', h') (g'', h''))
        (f (g' * g'', h' * h''))))) ho).trans
        ((congrArg (fun m => (R).comp (W m) ((R).comp j inc)) hi).trans
          ((hR).comp_assoc _ _ _).symm)))

end RMod.BrundanEllis.Stacking

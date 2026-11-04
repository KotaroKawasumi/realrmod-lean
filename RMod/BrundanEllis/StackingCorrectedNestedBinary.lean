import RMod.BrundanEllis.StackingCorrectedExteriorTensorator
import RMod.BrundanEllis.StackingExternalBinaryNaturality
import RMod.Classification.Proofs.ConvolutionComponents

/-! Coordinate and summand formulas for the actual corrected exterior tensor comparison. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData

/-- The actual gauge-corrected summand comparison has the specified
weighted reference map, including its original parity convention. -/
theorem correctedExteriorBinary_hom (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g g' : s.group) (h h' : t.group) :
    (correctedExteriorBinaryData s t X X' Y Y' g g' h h').hom =
    ((referenceBinaryBlockData (s.rho g).toAdd (t.rho h').toAdd
      (Y h).val (X g).val (Y' h').val (X' g').val (X g).property (Y' h').property
      (s.nu g g') (t.nu h h')).scale R
        (realSign (exteriorComparisonExponent s t g g' h h'))).hom := by
  dsimp only [correctedExteriorBinaryData, IsoData.scale]
  rw [exteriorBinaryBlock_hom]

/-- Retain the two actual weighted binary comparisons on a left-associated
triple, before composing the original associators or inserting in sums. -/
def correctedExteriorLeftBinaryData (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :=
  let j₁₂ := correctedExteriorBinaryData s t X X' Y Y' g g' h h'
  let jL := (referenceBinaryBlockData (s.rho (g * g')).toAdd (t.rho h'').toAdd
    (twistSummand reference.data (oldTwist t).data Y Y' h h')
    (twistSummand reference.data (oldTwist s).data X X' g g')
    (Y'' h'').val (X'' g'').val
    (twistSummand_inComponent reference.data referenceProperty (oldTwist s).data X X' g g')
    (Y'' h'').property (s.nu (g * g') g'') (t.nu (h * h') h'')).scale R
      (realSign (exteriorComparisonExponent s t (g * g') g'' (h * h') h''))
  ((j₁₂.tensor R (IsoData.refl R ((R).tensorObj (Y'' h'').val (X'' g'').val))).tensor R
    (IsoData.refl R (reference.data.pi.factor
      ((exteriorTwist s t).val.nu (g * g', h * h') (g'', h''))))).trans R jL

/-- The corresponding retained binary route for the right-associated triple. -/
def correctedExteriorRightBinaryData (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :=
  let j₂₃ := correctedExteriorBinaryData s t X' X'' Y' Y'' g' g'' h' h''
  let jR := (referenceBinaryBlockData (s.rho g).toAdd (t.rho (h' * h'')).toAdd
    (Y h).val (X g).val
    (twistSummand reference.data (oldTwist t).data Y' Y'' h' h'')
    (twistSummand reference.data (oldTwist s).data X' X'' g' g'')
    (X g).property
    (twistSummand_inComponent reference.data referenceProperty (oldTwist t).data Y' Y'' h' h'')
    (s.nu g (g' * g'')) (t.nu h (h' * h''))).scale R
      (realSign (exteriorComparisonExponent s t g (g' * g'') h (h' * h'')))
  (((IsoData.refl R ((R).tensorObj (Y h).val (X g).val)).tensor R j₂₃).tensor R
    (IsoData.refl R (reference.data.pi.factor
      ((exteriorTwist s t).val.nu (g, h) (g' * g'', h' * h''))))).trans R jR

end RMod.BrundanEllis.Stacking

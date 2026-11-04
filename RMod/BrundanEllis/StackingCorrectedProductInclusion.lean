import RMod.BrundanEllis.StackingCorrectedExteriorNaturality
import RMod.Classification.Proofs.ConvolutionProductInsertions

/-! Coordinate and summand formulas for the actual corrected exterior tensor comparison. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
attribute [local irreducible] correctedExteriorTensoratorData correctedExteriorBinaryData reversedExteriorPairing

/-- Equality comparisons commute with the raw tensor. -/
theorem tensor_equality_comparison (C : WeaklyPointedSuperfusion.{0, 0})
    {A A' B B' : C.data.Obj} (eA : A = A') (eB : B = B')
    (e : C.data.tensorObj A B = C.data.tensorObj A' B') :
    (IsoData.ofEq C.data e).hom =
      C.data.tensorHom (IsoData.ofEq C.data eA).hom (IsoData.ofEq C.data eB).hom := by
  subst A'
  subst B'
  exact (C.laws.tensor_id A B).symm

/-- Product-indexed input degrees give the same prescribed binary comparison. -/
theorem correctedExteriorTensorator_productInclusion (s t : Twist)
    (X X' : pullback s) (Y Y' : pullback t)
    (g g' : s.group) (h h' : t.group) :
    reference.data.comp
      (convolutionProductInclusion reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
        ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y'))
        (g, h) (g', h'))
      (correctedExteriorTensoratorData s t X X' Y Y' (g * g') (h * h')).hom =
    reference.data.comp (correctedExteriorBinaryData s t X X' Y Y' g g' h h').hom
      (reference.data.tensorHom
        (convolutionProductInclusion reference.data referenceProperty (oldTwist t).data Y Y' h h')
        (convolutionProductInclusion reference.data referenceProperty (oldTwist s).data X X' g g')) := by
  let C : WeaklyPointedSuperfusion :=
    ⟨reference.data.toWeaklyPointedSuperfusionData, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
  let P := fun gh : s.group × t.group =>
    twistSummand reference.data (oldTwist (exteriorTwist s t).val).data
      ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h) gh
  let Q := fun gh : s.group × t.group => reference.data.tensorObj
    (twistSummand reference.data (oldTwist t).data Y Y' h gh.2)
    (twistSummand reference.data (oldTwist s).data X X' g gh.1)
  let e : (g', h') = (g⁻¹ * (g * g'), h⁻¹ * (h * h')) :=
    Prod.ext (inv_mul_cancel_left g g').symm (inv_mul_cancel_left h h').symm
  have hn := indexed_morphism_eq_naturality C P Q
    (fun gh => (correctedExteriorBinaryData s t X X' Y Y' g gh.1 h gh.2).hom)
    e (congrArg P e) (congrArg Q e)
  change reference.data.comp (reference.data.comp _ _) _ = _
  rw [referenceProperty.comp_assoc]
  erw [correctedExteriorTensorator_inclusion s t X X' Y Y' (g * g') g (h * h') h]
  rw [← referenceProperty.comp_assoc]
  erw [← hn]
  rw [referenceProperty.comp_assoc]
  congr 1
  rw [tensor_equality_comparison C
    (congrArg (twistSummand reference.data (oldTwist t).data Y Y' h) (inv_mul_cancel_left h h').symm)
    (congrArg (twistSummand reference.data (oldTwist s).data X X' g) (inv_mul_cancel_left g g').symm)]
  rw [interchange_first_even referenceProperty.toWeaklyPointedSuperfusionLaws _ _ _ _
    (EvenIsoLaws.ofEq referenceProperty.toWeaklyPointedSuperfusionLaws _).hom_even]
  rfl

end RMod.BrundanEllis.Stacking

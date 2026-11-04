import RMod.Classification.Proofs.ConvolutionScalarMap
import RMod.Classification.Proofs.ConvolutionProductPartialMaps

/-!
# Binary scalar comparisons on the two triple routes

The inner comparison multiplies a triple summand by its binary scalar;
the outer comparison contributes the second scalar. These formulas use
the original product-indexed insertions and hold on every summand of
the full convolution, before imposing an associator equation.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (beta : t.group → t.group → ℝˣ)

theorem convolutionScalar_productInclusion (X Y : PullbackObj C t) (g h : t.group) :
    C.comp (convolutionProductInclusion C hC t X Y g h)
      (convolutionScalarData C hC t beta X Y (g * h)).hom =
    C.smul (beta g h).val (convolutionProductInclusion C hC t X Y g h) := by
  unfold convolutionProductInclusion
  rw [hC.comp_assoc, convolutionScalar_inclusion, hC.comp_smul]
  exact congrArg (fun a => C.smul (beta g a).val
    (convolutionProductInclusion C hC t X Y g h)) (inv_mul_cancel_left g h)

theorem convolutionScalar_left_route (X Y Z : PullbackObj C t) (g h k : t.group) :
    C.comp (convolutionProductLeftInsertion C hC t X Y Z g h k)
      (C.comp (convolutionHom C hC t
        (fun q => (convolutionScalarData C hC t beta X Y q).hom)
        (fun q => C.id (Z q).val) ((g * h) * k))
        (convolutionScalarData C hC t beta (convolutionObj C hC t X Y) Z ((g * h) * k)).hom) =
    C.smul ((beta g h * beta (g * h) k).val)
      (convolutionProductLeftInsertion C hC t X Y Z g h k) := by
  rw [← hC.comp_assoc, convolutionProductLeftInsertion_outer_map,
    convolutionScalar_productInclusion, hC.tensor_smul_left, hC.tensor_smul_left,
    hC.smul_comp, hC.smul_comp, hC.comp_assoc, convolutionScalar_productInclusion, hC.comp_smul,
    ← hC.mul_smul, Units.val_mul]
  rfl

theorem convolutionScalar_right_route (X Y Z : PullbackObj C t) (g h k : t.group) :
    C.comp (convolutionProductRightInsertion C hC t X Y Z g h k)
      (C.comp (convolutionHom C hC t
        (fun q => C.id (X q).val)
        (fun q => (convolutionScalarData C hC t beta Y Z q).hom) (g * (h * k)))
        (convolutionScalarData C hC t beta X (convolutionObj C hC t Y Z) (g * (h * k))).hom) =
    C.smul ((beta h k * beta g (h * k)).val)
      (convolutionProductRightInsertion C hC t X Y Z g h k) := by
  rw [← hC.comp_assoc, convolutionProductRightInsertion_outer_map,
    convolutionScalar_productInclusion, hC.tensor_smul_right, hC.tensor_smul_left,
    hC.smul_comp, hC.smul_comp, hC.comp_assoc, convolutionScalar_productInclusion, hC.comp_smul,
    ← hC.mul_smul, Units.val_mul]
  rfl

end RMod.Classification

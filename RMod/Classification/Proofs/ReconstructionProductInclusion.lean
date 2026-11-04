import RMod.Classification.Instances.ConvolutionProductInsertions
import RMod.Classification.Proofs.ReconstructionTensoratorProductInclusion

/-!
# The global tensorator on the inclusion of an actual pair of degrees

The equality comparison in the product-indexed inclusion cancels the
source comparison in the binary summand equation. The result uses just
the retained binary tensorator and mapped source component inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstructionProductInclusion_tensorator (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.comp
      (convolutionProductInclusion C.data hC (reconstructionTwistData A C hC)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) g h)
      (reconstructionTensoratorData A C hC X Y (g * h)).hom =
    C.data.comp
      ((reconstructionTensorComparison A C hC g h).data.app
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)).hom
      (reconstructionMappedTensorSpanInclusion A C hC X Y g h) := by
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  let e : twistSummand C.data t (F.obj X) (F.obj Y) g (g⁻¹ * (g * h)) =
      twistSummand C.data t (F.obj X) (F.obj Y) g h :=
    congrArg (twistSummand C.data t (F.obj X) (F.obj Y) g) (inv_mul_cancel_left g h)
  change C.data.comp
    (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data e.symm).hom
      (convolutionInclusion C.data hC t (F.obj X) (F.obj Y) (g * h) g)) _ = _
  exact (C.laws.comp_assoc _ _ _).trans
    ((congrArg (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data e.symm).hom)
      (reconstructionTensorator_inclusion_product A C hC X Y g h e)).trans
      ((isoData_ofEq_hom_comp_assoc C.toWeaklyPointedSuperfusion e.symm e _).trans
        (C.laws.id_comp _)))

end RMod.Classification

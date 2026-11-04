import RMod.Classification.Proofs.ReconstructionTensorInclusionIndex
import RMod.Classification.Proofs.ReconstructionTensoratorInsertions
import RMod.Classification.Proofs.IndexedMorphismEquality

/-!
# Binary reconstruction on a summand with its actual product degree

The only output transport is moved past the mapped source inclusion.
At degree `g*h` it cancels, so the global tensorator restricts to the
selected binary comparison followed by the actual mapped inclusion.
The source equality below records the convolution convention `g^-1*k`.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y : LinearCategory A.toWeaklyPointedSuperfusion)

theorem reconstructionTensorator_inclusion_product_index
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.comp (convolutionInclusion C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) k g)
      (reconstructionTensoratorData A C hC X Y k).hom =
    C.data.comp
      ((reconstructionTensorComparison A C hC g (g⁻¹ * k)).data.app
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y (g⁻¹ * k))).hom
      (C.data.comp (reconstructionMappedTensorSpanInclusion A C hC X Y g (g⁻¹ * k))
        (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (congrArg (fun j => (((reconstructionUnderlyingEquivalence A C hC).functor.obj
            (A.data.tensorObj X Y)) j).val) (mul_inv_cancel_left g k))).hom) := by
  exact (reconstructionTensorator_inclusion A C hC X Y k g).trans
    ((congrArg (fun m => C.data.comp m ((reconstructionMappedTensorBicone A C hC X Y k).ι g))
      (reconstructionConvolutionBlock_hom A C hC X Y k g)).trans
      ((C.laws.comp_assoc _ _ _).trans
        (congrArg (C.data.comp
          ((reconstructionTensorComparison A C hC g (g⁻¹ * k)).data.app
            ((reconstructionSourceEquivalence A).inverse.obj X g)
            ((reconstructionSourceEquivalence A).inverse.obj Y (g⁻¹ * k))).hom)
          (reconstructionMappedTensorInclusion_index A C hC X Y k g))))

theorem reconstructionTensorator_inclusion_product
    (g h : SimpleOrbit A.toWeaklyPointedSuperfusion)
    (hs : twistSummand C.data (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) g (g⁻¹ * (g * h)) =
      twistSummand C.data (reconstructionTwistData A C hC)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) g h) :
    C.data.comp (convolutionInclusion C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) (g * h) g)
      (reconstructionTensoratorData A C hC X Y (g * h)).hom =
    C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hs).hom
      (C.data.comp
        ((reconstructionTensorComparison A C hC g h).data.app
          ((reconstructionSourceEquivalence A).inverse.obj X g)
          ((reconstructionSourceEquivalence A).inverse.obj Y h)).hom
        (reconstructionMappedTensorSpanInclusion A C hC X Y g h)) := by
  apply (reconstructionTensorator_inclusion_product_index A C hC X Y (g * h) g).trans
  exact (C.laws.comp_assoc _ _ _).symm.trans
    (indexed_morphism_eq_naturality C.toWeaklyPointedSuperfusion
      (I := SimpleOrbit A.toWeaklyPointedSuperfusion)
      (twistSummand C.data (reconstructionTwistData A C hC)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) g)
      (fun q => (((reconstructionUnderlyingEquivalence A C hC).functor.obj
        (A.data.tensorObj X Y)) (g * q)).val)
      (fun q => C.data.comp
        ((reconstructionTensorComparison A C hC g q).data.app
          ((reconstructionSourceEquivalence A).inverse.obj X g)
          ((reconstructionSourceEquivalence A).inverse.obj Y q)).hom
        (reconstructionMappedTensorSpanInclusion A C hC X Y g q))
      (inv_mul_cancel_left g h) hs _)

end RMod.Classification

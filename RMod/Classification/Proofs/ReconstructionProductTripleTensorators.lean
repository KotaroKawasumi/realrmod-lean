import RMod.Classification.Proofs.ReconstructionProductInclusion
import RMod.Classification.Proofs.ReconstructionNestedTensorators
import RMod.Classification.Proofs.ConvolutionProductPartialMaps

/-!
# The two global tensorator routes on each product-indexed triple summand

Outer convolution naturality and the binary summand formula reduce the
global routes to the selected component triple tensorators. Both routes
retain the actual triple source inclusions and their product degrees.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionProductLeftInsertion_tensorators :
    let F := (reconstructionUnderlyingEquivalence A C hC).functor
    let t := reconstructionTwistData A C hC
    C.data.comp
      (C.data.comp (convolutionProductLeftInsertion C.data hC t (F.obj X) (F.obj Y) (F.obj Z) g h k)
        (convolutionHom C.data hC t (fun q => (reconstructionTensoratorData A C hC X Y q).hom)
          (fun q => C.data.id (F.obj Z q).val) ((g * h) * k)))
      (reconstructionTensoratorData A C hC (A.data.tensorObj X Y) Z ((g * h) * k)).hom =
    C.data.comp
      (componentTripleLeftTensorator
        (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        (reconstructionComponentSystem A C hC)
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion)
        (reconstruction_target_product A C hC) (reconstructionNu A C hC)
        (normalizedReconstructionComparison A C hC) g h k
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
      (reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k) := by
  dsimp only
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  let f : PullbackHom C.data t (convolutionObj C.data hC t (F.obj X) (F.obj Y))
      (F.obj (A.data.tensorObj X Y)) := fun q => (reconstructionTensoratorData A C hC X Y q).hom
  let z : PullbackHom C.data t (F.obj Z) (F.obj Z) := fun q => C.data.id (F.obj Z q).val
  let u := (reconstructionTensoratorData A C hC (A.data.tensorObj X Y) Z ((g * h) * k)).hom
  let b := ((reconstructionTensorComparison A C hC (g * h) k).data.app
    ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y) (g * h))
    ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
  let j := reconstructionMappedTensorSpanInclusion A C hC (A.data.tensorObj X Y) Z (g * h) k
  let W := fun m : C.data.Hom (twistSummand C.data t (F.obj X) (F.obj Y) g h)
      (F.obj (A.data.tensorObj X Y) (g * h)).val =>
    C.data.tensorHom (C.data.tensorHom m (C.data.id (F.obj Z k).val))
      (C.data.id (C.data.pi.factor (reconstructionNu A C hC (g * h) k)))
  have hm := convolutionProductLeftInsertion_outer_map C.data hC t f z g h k
  have hi := reconstructionProductInclusion_tensorator A C hC X Y g h
  have ho := reconstructionProductInclusion_tensorator A C hC (A.data.tensorObj X Y) Z (g * h) k
  exact (congrArg (fun m => C.data.comp m u) hm).trans
    ((C.laws.comp_assoc _ _ _).trans
      ((congrArg (C.data.comp (W (C.data.comp
        (convolutionProductInclusion C.data hC t (F.obj X) (F.obj Y) g h) (f (g * h))))) ho).trans
        ((C.laws.comp_assoc _ _ _).symm.trans
          ((congrArg (fun m => C.data.comp (C.data.comp (W m) b) j) hi).trans
            (reconstructionNestedTensorator_left A C hC X Y Z g h k)))))

theorem reconstructionProductRightInsertion_tensorators :
    let F := (reconstructionUnderlyingEquivalence A C hC).functor
    let t := reconstructionTwistData A C hC
    C.data.comp
      (C.data.comp (convolutionProductRightInsertion C.data hC t (F.obj X) (F.obj Y) (F.obj Z) g h k)
        (convolutionHom C.data hC t (fun q => C.data.id (F.obj X q).val)
          (fun q => (reconstructionTensoratorData A C hC Y Z q).hom) (g * (h * k))))
      (reconstructionTensoratorData A C hC X (A.data.tensorObj Y Z) (g * (h * k))).hom =
    C.data.comp
      (componentTripleRightTensorator
        (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        (reconstructionComponentSystem A C hC)
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion)
        (reconstruction_target_product A C hC) (reconstructionNu A C hC)
        (normalizedReconstructionComparison A C hC) g h k
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
      (reconstructionMappedTripleRightInclusion A C hC X Y Z g h k) := by
  dsimp only
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  let x : PullbackHom C.data t (F.obj X) (F.obj X) := fun q => C.data.id (F.obj X q).val
  let f : PullbackHom C.data t (convolutionObj C.data hC t (F.obj Y) (F.obj Z))
      (F.obj (A.data.tensorObj Y Z)) := fun q => (reconstructionTensoratorData A C hC Y Z q).hom
  let u := (reconstructionTensoratorData A C hC X (A.data.tensorObj Y Z) (g * (h * k))).hom
  let b := ((reconstructionTensorComparison A C hC g (h * k)).data.app
    ((reconstructionSourceEquivalence A).inverse.obj X g)
    ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj Y Z) (h * k))).hom
  let j := reconstructionMappedTensorSpanInclusion A C hC X (A.data.tensorObj Y Z) g (h * k)
  let W := fun m : C.data.Hom (twistSummand C.data t (F.obj Y) (F.obj Z) h k)
      (F.obj (A.data.tensorObj Y Z) (h * k)).val =>
    C.data.tensorHom (C.data.tensorHom (C.data.id (F.obj X g).val) m)
      (C.data.id (C.data.pi.factor (reconstructionNu A C hC g (h * k))))
  have hm := convolutionProductRightInsertion_outer_map C.data hC t x f g h k
  have hi := reconstructionProductInclusion_tensorator A C hC Y Z h k
  have ho := reconstructionProductInclusion_tensorator A C hC X (A.data.tensorObj Y Z) g (h * k)
  exact (congrArg (fun m => C.data.comp m u) hm).trans
    ((C.laws.comp_assoc _ _ _).trans
      ((congrArg (C.data.comp (W (C.data.comp
        (convolutionProductInclusion C.data hC t (F.obj Y) (F.obj Z) h k) (f (h * k))))) ho).trans
        ((C.laws.comp_assoc _ _ _).symm.trans
          ((congrArg (fun m => C.data.comp (C.data.comp (W m) b) j) hi).trans
            (reconstructionNestedTensorator_right A C hC X Y Z g h k)))))

end RMod.Classification

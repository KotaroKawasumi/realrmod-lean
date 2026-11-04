import RMod.Classification.Instances.ReconstructionOmega
import RMod.Classification.Proofs.NormalizedReconstructionComparison
import RMod.Classification.Proofs.ParityTensorComparisonTransport

/-!
# Reconstruction's actual tensorators at the unit degree

The extracted cochain has unit values zero by proof. Transport exactly
that right-factor equality and use the equality of the chosen comparison
data with the canonical unit comparisons. These equations apply on all
objects of the two homogeneous spans.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionTensorComparison_unit_left
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion)
    (X : HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object)
    (Y : HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object) :
    C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
      (congrArg (fun q => C.data.tensorObj
        (C.data.tensorObj ((reconstructionComponentEquivalence A C hC 1).forwardFunctor.data.obj X).obj
          ((reconstructionComponentEquivalence A C hC g).forwardFunctor.data.obj Y).obj)
        (C.data.pi.factor q)) (reconstructionNu_one_left A C hC g))).inv
      ((reconstructionTensorComparison A C hC 1 g).data.app X Y).hom =
      ((parityTensorComparison (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        ((reconstructionComponentSystem A C hC).leftUnitComparison g
          (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 g)
          (reconstruction_target_product A C hC 1 g))).data.app X Y).hom :=
  parityTensorComparison_hom_of_data_eq (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (normalizedReconstructionComparison A C hC 1 g) _
    (reconstructionNu_one_left A C hC g) (normalizedReconstructionComparison_one_left A C hC g) X Y

theorem reconstructionTensorComparison_unit_right
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion)
    (X : HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object)
    (Y : HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object) :
    C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
      (congrArg (fun q => C.data.tensorObj
        (C.data.tensorObj ((reconstructionComponentEquivalence A C hC g).forwardFunctor.data.obj X).obj
          ((reconstructionComponentEquivalence A C hC 1).forwardFunctor.data.obj Y).obj)
        (C.data.pi.factor q)) (reconstructionNu_one_right A C hC g))).inv
      ((reconstructionTensorComparison A C hC g 1).data.app X Y).hom =
      ((parityTensorComparison (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        ((reconstructionComponentSystem A C hC).rightUnitComparison g
          (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1)
          (reconstruction_target_product A C hC g 1))).data.app X Y).hom :=
  parityTensorComparison_hom_of_data_eq (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (normalizedReconstructionComparison A C hC g 1) _
    (reconstructionNu_one_right A C hC g) (normalizedReconstructionComparison_one_right A C hC g) X Y

end RMod.Classification

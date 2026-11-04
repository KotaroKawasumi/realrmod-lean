import RMod.Classification.Instances.ReconstructionTensorator
import RMod.Classification.Proofs.EvenNormalizers

/-!
# The raw binary map and output equality in each convolution block

The even-category comparison has exactly the retained parity tensorator
as its first map. Its second map is the equality from the product degree
to the fixed output degree.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
  (k g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionConvolutionBlock_hom :
    (reconstructionConvolutionBlockIso A C hC X Y k g).hom.hom =
      C.data.comp
        ((reconstructionTensorComparison A C hC g (g⁻¹ * k)).data.app
          ((reconstructionSourceEquivalence A).inverse.obj X g)
          ((reconstructionSourceEquivalence A).inverse.obj Y (g⁻¹ * k))).hom
        (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (reconstructionTensorOutputRealization_obj A C hC X Y k g).symm).hom := by
  exact congrArg (C.data.comp
      ((reconstructionTensorComparison A C hC g (g⁻¹ * k)).data.app
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y (g⁻¹ * k))).hom)
    (even_eqToIso_hom C.toWeaklyPointedSuperfusion _)

end RMod.Classification

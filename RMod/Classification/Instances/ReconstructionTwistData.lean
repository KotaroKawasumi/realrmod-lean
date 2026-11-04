import RMod.Classification.Instances.ReconstructionOmega
import RMod.Classification.Abstract.Parameters

/-!
# The extracted group and cochains as reconstruction data

The group and type homomorphism are intrinsic. The two cochains use the
chosen component comparisons and their actual normalized associator
routes. This is only the data layer; its normalization and coherence
laws must be established separately for these exact fields.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def reconstructionTwistData (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data) :
    TwistData where
  group := simpleOrbitFiniteGroup A.toWeaklyPointedSuperfusion
  rho := intrinsicRho A
  nu := reconstructionNu A C hC
  omega := reconstructionOmega A C hC

end RMod.Classification

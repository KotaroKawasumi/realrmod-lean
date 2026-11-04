import RMod.Classification.Instances.ReconstructionUnitSpanMaps

/-!
# Unit summands in the convolution indexing convention

At the surviving left index 1, the other index 1^-1*g equals g. At the
surviving right index g, the unit index g^-1*g equals 1. These are actual
equalities of the fixed-output span objects.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0}) (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionLeftUnitOutput_eq :
    reconstructionTensorOutputSpan A A.data.tensorUnit X g 1 = reconstructionLeftUnitSpan A X g := by
  apply ObjectProperty.FullSubcategory.ext
  exact congrArg (fun k => A.data.tensorObj
    ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
    ((reconstructionSourceEquivalence A).inverse.obj X k).obj) (by rw [inv_one, one_mul])

theorem reconstructionRightUnitOutput_eq :
    reconstructionTensorOutputSpan A X A.data.tensorUnit g g = reconstructionRightUnitSpan A X g := by
  apply ObjectProperty.FullSubcategory.ext
  exact congrArg (fun k => A.data.tensorObj
    ((reconstructionSourceEquivalence A).inverse.obj X g).obj
    ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit k).obj) (inv_mul_cancel g)

end RMod.Classification

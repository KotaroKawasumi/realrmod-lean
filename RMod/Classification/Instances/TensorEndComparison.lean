import RMod.Classification.Instances.TensorEndEquivalence
import Superfusion.Super.TensorCoherence

/-!
# Comparing tensor-product endomorphism algebras

Use the actual tensor-endomorphism equivalence on each side and apply
the two given graded algebra maps factorwise in between. This is the
endomorphism action prescribed by a pair of component superfunctors.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category

noncomputable def tensorEndComparison (C D : WeaklyPointedSuperfusion.{0, 0})
    (S T : LinearCategory C) (X Y : LinearCategory D)
    (hT : C.data.IsSimple T) (hY : D.data.IsSimple Y)
    (a : SuperAlgEquiv (endSuperAlgebra (K := ℝ) S) (endSuperAlgebra (K := ℝ) X))
    (b : SuperAlgEquiv (endSuperAlgebra (K := ℝ) T) (endSuperAlgebra (K := ℝ) Y)) :
    SuperAlgEquiv
      (endSuperAlgebra (K := ℝ) (C := LinearCategory C) (C.data.tensorObj S T))
      (endSuperAlgebra (K := ℝ) (C := LinearCategory D) (D.data.tensorObj X Y)) :=
  (tensorEndSuperEquiv C S T hT).symm.trans
    ((a.gtensorCongr b).trans (tensorEndSuperEquiv D X Y hY))

end RMod.Classification

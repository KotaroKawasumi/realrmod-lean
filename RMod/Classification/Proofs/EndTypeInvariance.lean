import RMod.Classification.Proofs.BrauerWallTypes

/-!
# Graded endomorphism algebra isomorphisms preserve intrinsic labels

Each supplied intrinsic Clifford type determines the Brauer–Wall class
of the endomorphism algebra. Transporting through the specified graded
algebra isomorphism and using Clifford-label uniqueness identifies the
two labels without choosing categorical equivalences.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

theorem HasBWType.label_eq_of_endEquiv (C D : WeaklyPointedSuperfusion.{0, 0})
    {X : C.data.Obj} {Y : D.data.Obj} {r s : ZMod 8}
    (hr : HasBWType C.data X r) (hs : HasBWType D.data Y s)
    (e : SuperAlgEquiv
      (Category.endSuperAlgebra (K := ℝ) (C := LinearCategory C) X)
      (Category.endSuperAlgebra (K := ℝ) (C := LinearCategory D) Y)) : r = s :=
  negativeTower_label_eq ((hr.isBWEquivalent C).symm.trans
    ((IsBWEquivalent.of_superAlgEquiv e).trans (hs.isBWEquivalent D)))

end RMod.Classification

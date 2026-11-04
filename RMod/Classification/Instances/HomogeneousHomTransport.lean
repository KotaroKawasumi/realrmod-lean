import RMod.Classification.Instances.HomogeneousHomMatrix

/-!
# Transporting actual Hom spaces through an endomorphism algebra equivalence

The source and target presentations have matching matrix dimensions.
Taking source coordinates, applying the algebra equivalence entrywise,
and reconstructing with the target maps gives a linear equivalence of
the full Hom spaces. Its inverse is retained by Mathlib's LinearEquiv.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S X Y : LinearCategory C} {T X' Y' : LinearCategory D} {n m : ℕ}
  (a : End S ≃ₐ[ℝ] End T)
  (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data S Y m)
  (d' : HomogeneousSum D.data T X' n) (e' : HomogeneousSum D.data T Y' m)

def transportHom : (X ⟶ Y) ≃ₗ[ℝ] (X' ⟶ Y') :=
  (homMatrixLinearEquiv d e).trans
    (a.toLinearEquiv.mapMatrix.trans (homMatrixLinearEquiv d' e').symm)

theorem transportHom_apply (f : X ⟶ Y) :
    transportHom a d e d' e' f = fromHomMatrix d' e' ((toHomMatrix d e f).map a) := rfl

theorem toHomMatrix_transportHom (f : X ⟶ Y) :
    toHomMatrix d' e' (transportHom a d e d' e' f) = (toHomMatrix d e f).map a :=
  toHomMatrix_fromHomMatrix d' e' _

end RMod.Classification.HomogeneousSum

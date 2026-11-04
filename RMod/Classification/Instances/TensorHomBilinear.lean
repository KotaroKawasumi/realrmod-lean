import RMod.Classification.Instances.LinearCategory

/-!
# The bilinear tensor map on arbitrary Hom spaces

Mathlib linear maps package the given tensor operation and its existing
additivity and scalar laws. This generalizes the endomorphism-only view
to the inclusions and projections in homogeneous sum presentations.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

def tensorHomBilinear (C : WeaklyPointedSuperfusion.{u, v}) (X X' Y Y' : LinearCategory C) :
    (X ⟶ X') →ₗ[ℝ] (Y ⟶ Y') →ₗ[ℝ]
      (@Quiver.Hom (LinearCategory C) _ (C.data.tensorObj X Y) (C.data.tensorObj X' Y')) where
  toFun f :=
    { toFun := C.data.tensorHom f
      map_add' := C.laws.tensor_add_right f
      map_smul' r g := C.laws.tensor_smul_right r f g }
  map_add' f g := by
    ext h
    exact C.laws.tensor_add_left f g h
  map_smul' r f := by
    ext g
    exact C.laws.tensor_smul_left r f g

end RMod.Classification

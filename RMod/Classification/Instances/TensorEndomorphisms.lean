import RMod.Classification.Instances.EndGrading
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The linear tensor-endomorphism map

The underlying map sends a pure tensor of endomorphisms to their given
categorical tensor. Bilinearity comes directly from the supplied laws.
Its graded algebra structure and bijectivity are separate proof obligations.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{u, v}) (X Y : C.data.Obj)

def tensorEndBilinear : End (C := LinearCategory C) X →ₗ[ℝ]
    End (C := LinearCategory C) Y →ₗ[ℝ] End (C := LinearCategory C) (C.data.tensorObj X Y) where
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

def tensorEndLinear : TensorProduct ℝ (End (C := LinearCategory C) X)
    (End (C := LinearCategory C) Y) →ₗ[ℝ] End (C := LinearCategory C) (C.data.tensorObj X Y) :=
  TensorProduct.lift (tensorEndBilinear C X Y)

@[simp]
theorem tensorEndLinear_tmul (f : End (C := LinearCategory C) X)
    (g : End (C := LinearCategory C) Y) :
    tensorEndLinear C X Y (TensorProduct.tmul ℝ f g) = C.data.tensorHom f g := rfl

end RMod.Classification

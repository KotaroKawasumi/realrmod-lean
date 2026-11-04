import RMod.Classification.Instances.Functors
import RMod.Classification.Instances.LinearMonoidal
import RMod.Classification.Proofs.TensorCalculus

/-!
# Tensoring by a fixed object as a superfunctor

Although the tensor on all morphisms has signed interchange, tensoring by
an identity on one side is an ordinary real-linear, grading-preserving
functor. The crossing identity is even. These functors let duality be
expressed by Mathlib adjunctions on the full Hom spaces.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

def tensorLeftData (C : WeaklyPointedSuperfusionData.{u, v}) (X : C.Obj) :
    SuperfunctorData C C where
  obj Y := C.tensorObj X Y
  map f := C.whiskerLeft X f

def tensorRightData (C : WeaklyPointedSuperfusionData.{u, v}) (X : C.Obj) :
    SuperfunctorData C C where
  obj Y := C.tensorObj Y X
  map f := C.whiskerRight f X

variable (C : WeaklyPointedSuperfusion.{u, v}) (X : C.data.Obj)

theorem tensorLeftLaws : SuperfunctorLaws C.data C.data (tensorLeftData C.data X) where
  map_id Y := C.laws.tensor_id X Y
  map_comp f g := by
    change C.data.tensorHom (C.data.id X) (C.data.comp f g) =
      C.data.comp (C.data.tensorHom (C.data.id X) f) (C.data.tensorHom (C.data.id X) g)
    rw [interchange_first_even C.laws _ _ _ _ (C.laws.id_even X), C.laws.comp_id]
  map_zero Y Z := tensor_zero_right C.laws _
  map_add f g := C.laws.tensor_add_right _ f g
  map_smul r f := C.laws.tensor_smul_right r _ f
  map_grade f hf := by
    have h := C.laws.tensor_grade _ _ (C.laws.id_even X) hf
    rw [zero_add] at h
    exact h

theorem tensorRightLaws : SuperfunctorLaws C.data C.data (tensorRightData C.data X) where
  map_id Y := C.laws.tensor_id Y X
  map_comp f g := by
    change C.data.tensorHom (C.data.comp f g) (C.data.id X) =
      C.data.comp (C.data.tensorHom f (C.data.id X)) (C.data.tensorHom g (C.data.id X))
    rw [interchange_second_even C.laws _ _ _ _ (C.laws.id_even X), C.laws.comp_id]
  map_zero Y Z := tensor_zero_left C.laws _
  map_add f g := C.laws.tensor_add_left f g _
  map_smul r f := C.laws.tensor_smul_left r f _
  map_grade f hf := by
    have h := C.laws.tensor_grade _ _ hf (C.laws.id_even X)
    rw [add_zero] at h
    exact h

def tensorLeftSuperfunctor : Superfunctor C C := ⟨tensorLeftData C.data X, tensorLeftLaws C X⟩

def tensorRightSuperfunctor : Superfunctor C C := ⟨tensorRightData C.data X, tensorRightLaws C X⟩

end RMod.Classification

import RMod.Classification.Instances.TensorFunctors

/-!
# Natural tensor comparisons on the full category

The unitors and associator give ordinary natural isomorphisms between the
fixed-object tensor functors on all morphisms. An even map of fixed objects
also gives a natural transformation. The evenness assumption is exactly
what removes the crossing sign, including for inhomogeneous test maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{u, v})

abbrev tensorLeftFunctor (X : C.data.Obj) := (tensorLeftSuperfunctor C X).toFunctor
abbrev tensorRightFunctor (X : C.data.Obj) := (tensorRightSuperfunctor C X).toFunctor

attribute [local implicit_reducible] tensorLeftData tensorRightData
  tensorLeftSuperfunctor tensorRightSuperfunctor Superfunctor.toFunctor

def tensorLeftUnitIso : tensorLeftFunctor C C.data.tensorUnit ≅ 𝟭 (LinearCategory C) :=
  NatIso.ofComponents
    (fun X =>
      { hom := C.data.leftUnitorHom X
        inv := C.data.leftUnitorInv X
        hom_inv_id := C.laws.left_unitor_hom_inv X
        inv_hom_id := C.laws.left_unitor_inv_hom X })
    (fun f => C.laws.left_unitor_naturality f)

def tensorRightUnitIso : tensorRightFunctor C C.data.tensorUnit ≅ 𝟭 (LinearCategory C) :=
  NatIso.ofComponents
    (fun X =>
      { hom := C.data.rightUnitorHom X
        inv := C.data.rightUnitorInv X
        hom_inv_id := C.laws.right_unitor_hom_inv X
        inv_hom_id := C.laws.right_unitor_inv_hom X })
    (fun f => C.laws.right_unitor_naturality f)

def tensorLeftAssocIso (X Y : C.data.Obj) :
    tensorLeftFunctor C (C.data.tensorObj X Y) ≅ tensorLeftFunctor C Y ⋙ tensorLeftFunctor C X :=
  NatIso.ofComponents
    (fun Z =>
      { hom := C.data.associatorHom X Y Z
        inv := C.data.associatorInv X Y Z
        hom_inv_id := C.laws.associator_hom_inv X Y Z
        inv_hom_id := C.laws.associator_inv_hom X Y Z })
    (fun f => by
      have h := C.laws.associator_naturality (C.data.id X) (C.data.id Y) f
      rw [C.laws.tensor_id] at h
      exact h)

def tensorRightAssocIso (X Y : C.data.Obj) :
    tensorRightFunctor C X ⋙ tensorRightFunctor C Y ≅ tensorRightFunctor C (C.data.tensorObj X Y) :=
  NatIso.ofComponents
    (fun Z =>
      { hom := C.data.associatorHom Z X Y
        inv := C.data.associatorInv Z X Y
        hom_inv_id := C.laws.associator_hom_inv Z X Y
        inv_hom_id := C.laws.associator_inv_hom Z X Y })
    (fun f => by
      have h := C.laws.associator_naturality f (C.data.id X) (C.data.id Y)
      rw [C.laws.tensor_id] at h
      exact h)

def tensorLeftMap {X Y : C.data.Obj} (f : C.data.Hom X Y) (hf : C.data.IsHomogeneous 0 f) :
    tensorLeftFunctor C X ⟶ tensorLeftFunctor C Y where
  app Z := C.data.tensorHom f (C.data.id Z)
  naturality {U V} g := by
    change C.data.comp (C.data.tensorHom (C.data.id X) g) (C.data.tensorHom f (C.data.id V)) =
      C.data.comp (C.data.tensorHom f (C.data.id U)) (C.data.tensorHom (C.data.id Y) g)
    rw [interchange_second_even C.laws _ _ _ _ (C.laws.id_even V),
      interchange_first_even C.laws _ _ _ _ hf,
      C.laws.id_comp, C.laws.comp_id, C.laws.id_comp, C.laws.comp_id]

def tensorRightMap {X Y : C.data.Obj} (f : C.data.Hom X Y) (hf : C.data.IsHomogeneous 0 f) :
    tensorRightFunctor C X ⟶ tensorRightFunctor C Y where
  app Z := C.data.tensorHom (C.data.id Z) f
  naturality {U V} g := by
    change C.data.comp (C.data.tensorHom g (C.data.id X)) (C.data.tensorHom (C.data.id V) f) =
      C.data.comp (C.data.tensorHom (C.data.id U) f) (C.data.tensorHom g (C.data.id Y))
    rw [interchange_second_even C.laws _ _ _ _ hf,
      interchange_first_even C.laws _ _ _ _ (C.laws.id_even U),
      C.laws.comp_id, C.laws.id_comp, C.laws.comp_id, C.laws.id_comp]

end RMod.Classification

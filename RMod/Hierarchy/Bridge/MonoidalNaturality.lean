import RMod.Hierarchy.Bridge.TensorComponents

/-!
# Total naturality of the retained coherence maps

Expanding the two parity components reduces each equation to the old
naturality equations and bilinearity. The odd-odd correction is applied
on both sides of the associativity diagram.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem ofOld_associator_naturality {X X' Y Y' Z Z' : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X X')
    (g : THom (ofOldSupercategoryData C) Y Y')
    (h : THom (ofOldSupercategoryData C) Z Z') :
    tComp (ofOldSupercategoryData C)
      (tTensor (ofOldMonoidalStructureData C) (tTensor (ofOldMonoidalStructureData C) f g) h)
      (evenPoint ((ofOldMonoidalStructureData C).associatorHom X' Y' Z')) =
    tComp (ofOldSupercategoryData C)
      (evenPoint ((ofOldMonoidalStructureData C).associatorHom X Y Z))
      (tTensor (ofOldMonoidalStructureData C) f (tTensor (ofOldMonoidalStructureData C) g h)) := by
  apply (totalHomEquiv C _ _).injective
  rw [totalHomEquiv_comp, totalHomEquiv_comp, totalHomEquiv_even, totalHomEquiv_even]
  have he (X Y Z : C.data.Obj) :
      (evenPoint ((ofOldMonoidalStructureData C).associatorHom X Y Z) 0).val =
        C.data.associatorHom X Y Z := by
    dsimp only [ofOldMonoidalStructureData, evenPoint]
    rw [homogeneousPoint_map_same]
  rw [he, he, totalHomEquiv_tTensor, totalHomEquiv_tTensor]
  simp only [ofOld_tTensor_zero, ofOld_tTensor_one, C.laws.tensor_add_left,
    C.laws.tensor_add_right, C.laws.tensor_smul_left, C.laws.tensor_smul_right,
    C.laws.smul_add, C.laws.add_comp, C.laws.comp_add, C.laws.smul_comp,
    C.laws.comp_smul, C.laws.associator_naturality]
  letI (A B : C.data.Obj) : Std.Associative (@C.data.add A B) := ⟨C.laws.add_assoc⟩
  letI (A B : C.data.Obj) : Std.Commutative (@C.data.add A B) := ⟨C.laws.add_comm⟩
  ac_rfl

theorem ofOld_left_naturality {X Y : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X Y) :
    tComp (ofOldSupercategoryData C)
      (tTensor (ofOldMonoidalStructureData C) (evenPoint ((ofOldSupercategoryData C).id C.data.tensorUnit)) f)
      (evenPoint ((ofOldMonoidalStructureData C).leftHom Y)) =
    tComp (ofOldSupercategoryData C) (evenPoint ((ofOldMonoidalStructureData C).leftHom X)) f := by
  apply (totalHomEquiv C _ _).injective
  rw [totalHomEquiv_comp, totalHomEquiv_comp, totalHomEquiv_even, totalHomEquiv_even,
    totalHomEquiv_tTensor_even_left]
  have he (X : C.data.Obj) :
      (evenPoint ((ofOldMonoidalStructureData C).leftHom X) 0).val =
        C.data.leftUnitorHom X := by
    dsimp only [ofOldMonoidalStructureData, evenPoint]
    rw [homogeneousPoint_map_same]
  have hi : (evenPoint ((ofOldSupercategoryData C).id C.data.tensorUnit) 0).val =
      C.data.id C.data.tensorUnit := oldEnrichedId_zero C C.data.tensorUnit
  rw [he, he, hi]
  exact C.laws.left_unitor_naturality _

theorem ofOld_right_naturality {X Y : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X Y) :
    tComp (ofOldSupercategoryData C)
      (tTensor (ofOldMonoidalStructureData C) f (evenPoint ((ofOldSupercategoryData C).id C.data.tensorUnit)))
      (evenPoint ((ofOldMonoidalStructureData C).rightHom Y)) =
    tComp (ofOldSupercategoryData C) (evenPoint ((ofOldMonoidalStructureData C).rightHom X)) f := by
  apply (totalHomEquiv C _ _).injective
  rw [totalHomEquiv_comp, totalHomEquiv_comp, totalHomEquiv_even, totalHomEquiv_even,
    totalHomEquiv_tTensor_even_right]
  have he (X : C.data.Obj) :
      (evenPoint ((ofOldMonoidalStructureData C).rightHom X) 0).val =
        C.data.rightUnitorHom X := by
    dsimp only [ofOldMonoidalStructureData, evenPoint]
    rw [homogeneousPoint_map_same]
  have hi : (evenPoint ((ofOldSupercategoryData C).id C.data.tensorUnit) 0).val =
      C.data.id C.data.tensorUnit := oldEnrichedId_zero C C.data.tensorUnit
  rw [he, he, hi]
  exact C.laws.right_unitor_naturality _

end RMod.Legacy.Hierarchy

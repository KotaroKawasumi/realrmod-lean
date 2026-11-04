import RMod.Classification.Instances.UnitGeneratorMaps

/-! # The transported generator unit maps are even isomorphisms -/

set_option autoImplicit false

namespace RMod.Classification

variable (A : WeaklyPointedSuperfusion.{0, 0}) (S : SimpleObject A) (hS : S = unitSimple A)

theorem leftUnitGeneratorMap_even (Y : A.data.Obj) :
    EvenIsoLaws A.data (leftUnitGeneratorMap A S hS Y) := by
  subst S
  exact EvenIsoLaws.leftUnit A.laws Y

theorem rightUnitGeneratorMap_even (Y : A.data.Obj) :
    EvenIsoLaws A.data (rightUnitGeneratorMap A S hS Y) := by
  subst S
  exact EvenIsoLaws.rightUnit A.laws Y

/-! The transported maps have the expected formula in terms of the
generator equality followed by the original unitor. -/

theorem leftUnitGeneratorMap_hom (Y : A.data.Obj) :
    A.data.comp (A.data.tensorHom
      (IsoData.ofEq A.data (congrArg (fun S => S.data.object) hS)).hom (A.data.id Y))
      (A.data.leftUnitorHom Y) = (leftUnitGeneratorMap A S hS Y).hom := by
  subst S
  change A.data.comp (A.data.tensorHom (A.data.id A.data.tensorUnit) (A.data.id Y))
    (A.data.leftUnitorHom Y) = A.data.leftUnitorHom Y
  rw [A.laws.tensor_id, A.laws.id_comp]

theorem rightUnitGeneratorMap_hom (Y : A.data.Obj) :
    A.data.comp (A.data.tensorHom (A.data.id Y)
      (IsoData.ofEq A.data (congrArg (fun S => S.data.object) hS)).hom)
      (A.data.rightUnitorHom Y) = (rightUnitGeneratorMap A S hS Y).hom := by
  subst S
  change A.data.comp (A.data.tensorHom (A.data.id Y) (A.data.id A.data.tensorUnit))
    (A.data.rightUnitorHom Y) = A.data.rightUnitorHom Y
  rw [A.laws.tensor_id, A.laws.id_comp]

end RMod.Classification

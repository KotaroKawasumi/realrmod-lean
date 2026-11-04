import RMod.Classification.Instances.TensorIsoBeforeCoherence

/-!
# Inverse comparison maps before target coherence

The counit identifies every target object with an image. Tensor these
identifications and use the specified forward tensorator; full faithfulness
then supplies its unique preimage. This constructs inverse tensor and unit
maps without presupposing a monoidal category on the target.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategoryStruct C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategoryStruct D]

noncomputable def inverseMonoidalComparisonData (e : C ≌ D)
    (hD : TensorStructuralLaws D) (d : MonoidalComparisonData e.functor) :
    MonoidalComparisonData e.inverse where
  tensor X Y := e.functor.preimageIso
    ((d.tensor (e.inverse.obj X) (e.inverse.obj Y)).symm ≪≫
      tensorIsoBeforeCoherence hD (e.counitIso.app X) (e.counitIso.app Y) ≪≫
      (e.counitIso.app (X ⊗ Y)).symm)
  unit := e.functor.preimageIso
    (d.unit.symm ≪≫ (e.counitIso.app (𝟙_ D)).symm)

end RMod.Classification

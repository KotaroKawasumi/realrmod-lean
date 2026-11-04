import RMod.Hierarchy.Abstract.Superfunctor
import RMod.Hierarchy.Bridge.TotalHom
import RMod.Hierarchy.Instances.HomogeneousLine
import RMod.Classification.Instances.Functors

/-!
# Enriched superfunctors from the old linear maps

Restricting a grading-preserving linear functor to each homogeneous Hom
component gives its enriched map. The old identity and composition laws
then prove the enriched functor laws on generators.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.Legacy.Hierarchy
variable {C D : WeaklyPointedSuperfusion.{0, 0}} (F : Classification.Superfunctor C D)

def ofOldSuperfunctorData : SuperfunctorData (ofOldSupercategoryData C) (ofOldSupercategoryData D) where
  obj := F.data.obj
  map _ _ _ := ModuleCat.ofHom {
    toFun f := ⟨F.data.map f.val, F.laws.map_grade f.val f.property⟩
    map_add' f g := Subtype.ext (F.laws.map_add f.val g.val)
    map_smul' r f := Subtype.ext (F.laws.map_smul r f.val) }

theorem ofOldSuperfunctorLaws : SuperfunctorLaws (ofOldSuperfunctorData F) where
  map_id X := by
    apply (homogeneousHomEquiv _ 0).injective
    apply Subtype.ext
    change F.data.map (evenPoint ((ofOldSupercategoryData C).id X) 0).val =
      (evenPoint ((ofOldSupercategoryData D).id (F.data.obj X)) 0).val
    have hC : (evenPoint ((ofOldSupercategoryData C).id X) 0).val = C.data.id X :=
      oldEnrichedId_zero C X
    have hD : (evenPoint ((ofOldSupercategoryData D).id (F.data.obj X)) 0).val =
        D.data.id (F.data.obj X) := oldEnrichedId_zero D (F.data.obj X)
    rw [hC, hD]
    exact F.laws.map_id X
  map_comp X Y Z := by
    funext a
    apply tensorObj_ext
    intro i j hij
    change ιTensorObj (oldEnrichedHom C X Y) (oldEnrichedHom C Y Z) i j a hij ≫
        (oldEnrichedComp C X Y Z a ≫ (ofOldSuperfunctorData F).map X Z a) =
      ιTensorObj (oldEnrichedHom C X Y) (oldEnrichedHom C Y Z) i j a hij ≫
        (GradedObject.Monoidal.tensorHom ((ofOldSuperfunctorData F).map X Y)
          ((ofOldSuperfunctorData F).map Y Z) a ≫
            oldEnrichedComp D (F.data.obj X) (F.data.obj Y) (F.data.obj Z) a)
    erw [ι_tensorHom_assoc]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    apply Subtype.ext
    change F.data.map (oldEnrichedComp C X Y Z a
      (ιTensorObj (oldEnrichedHom C X Y) (oldEnrichedHom C Y Z) i j a hij (f ⊗ₜ[ℝ] g))).val =
      (oldEnrichedComp D (F.data.obj X) (F.data.obj Y) (F.data.obj Z) a
        (ιTensorObj (oldEnrichedHom D (F.data.obj X) (F.data.obj Y))
          (oldEnrichedHom D (F.data.obj Y) (F.data.obj Z)) i j a hij
          ((ofOldSuperfunctorData F).map X Y i f ⊗ₜ[ℝ] (ofOldSuperfunctorData F).map Y Z j g))).val
    rw [oldEnrichedComp_tmul, oldEnrichedComp_tmul]
    exact F.laws.map_comp f.val g.val

def ofOldSuperfunctor : Superfunctor (ofOldSupercategory C) (ofOldSupercategory D) :=
  ⟨ofOldSuperfunctorData F, ofOldSuperfunctorLaws F⟩

theorem totalHomEquiv_map {X Y : C.data.Obj} (f : THom (ofOldSupercategoryData C) X Y) :
    totalHomEquiv D (F.data.obj X) (F.data.obj Y) (tMap (ofOldSuperfunctorData F) f) =
      F.data.map (totalHomEquiv C X Y f) := by
  simp only [totalHomEquiv_apply]
  exact (F.laws.map_add (f 0).val (f 1).val).symm

end RMod.Legacy.Hierarchy

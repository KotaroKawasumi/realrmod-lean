import RMod.Hierarchy.Bridge.LegacyCategories
import RMod.Hierarchy.Instances.HomogeneousEmbedding

/-!
# Enriched maps for the new-old-new comparison

Forward maps include a homogeneous vector into the total Hom space.
Backward maps evaluate a supported total vector in its degree. Their
composition laws are the single-summand convolution identities.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.Legacy.Hierarchy
variable (A : WeaklyPointedFusionPiSupercategory)

abbrev originalSuper := A.toMonoidalPiSupercategory.monoidal.super

def roundtripForwardData : SuperfunctorData (originalSuper A).data (ofOldSupercategoryData (legacyCategory A)) where
  obj X := X
  map X Y a := ModuleCat.ofHom {
    toFun f := ⟨homogeneousEmbedding (originalSuper A) X Y a f,
      homogeneousEmbedding_mem (originalSuper A) X Y a f⟩
    map_add' f g := Subtype.ext ((homogeneousEmbedding (originalSuper A) X Y a).map_add f g)
    map_smul' r f := Subtype.ext ((homogeneousEmbedding (originalSuper A) X Y a).map_smul r f) }

def roundtripBackwardData : SuperfunctorData (ofOldSupercategoryData (legacyCategory A)) (originalSuper A).data where
  obj X := X
  map _ _ a := ModuleCat.ofHom {
    toFun f := f.val a
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

theorem roundtripForwardLaws : SuperfunctorLaws (roundtripForwardData A) where
  map_id X := by
    apply (homogeneousHomEquiv _ 0).injective
    apply Subtype.ext
    change homogeneousEmbedding (originalSuper A) X X 0 (evenPoint ((originalSuper A).data.id X) 0) =
      (evenPoint ((ofOldSupercategoryData (legacyCategory A)).id X) 0).val
    have hid : (evenPoint ((ofOldSupercategoryData (legacyCategory A)).id X) 0).val =
      (legacyCategory A).data.id X := oldEnrichedId_zero (legacyCategory A) X
    rw [hid]
    exact homogeneousEmbedding_evaluation (originalSuper A) 0 _
      (evenPoint_mem_grade (originalSuper A) _)
  map_comp X Y Z := by
    funext a
    apply tensorObj_ext
    intro i j hij
    erw [ι_tensorHom_assoc]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    apply Subtype.ext
    change homogeneousEmbedding (originalSuper A) X Z a
      ((originalSuper A).data.comp X Y Z a
        (ιTensorObj ((originalSuper A).data.Hom X Y) ((originalSuper A).data.Hom Y Z) i j a hij (f ⊗ₜ[ℝ] g))) =
      (oldEnrichedComp (legacyCategory A) X Y Z a
        (ιTensorObj (oldEnrichedHom (legacyCategory A) X Y) (oldEnrichedHom (legacyCategory A) Y Z) i j a hij
          ((roundtripForwardData A).map X Y i f ⊗ₜ[ℝ] (roundtripForwardData A).map Y Z j g))).val
    rw [oldEnrichedComp_tmul]
    exact (homogeneousEmbedding_comp (originalSuper A) i j a hij f g).symm

theorem roundtripBackwardLaws : SuperfunctorLaws (roundtripBackwardData A) where
  map_id X := by
    apply (homogeneousHomEquiv _ 0).injective
    change (evenPoint ((ofOldSupercategoryData (legacyCategory A)).id X) 0).val 0 =
      evenPoint ((originalSuper A).data.id X) 0
    have hid : (evenPoint ((ofOldSupercategoryData (legacyCategory A)).id X) 0).val =
      (legacyCategory A).data.id X := oldEnrichedId_zero (legacyCategory A) X
    rw [hid]
    rfl
  map_comp X Y Z := by
    funext a
    apply tensorObj_ext
    intro i j hij
    erw [ι_tensorHom_assoc]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (oldEnrichedComp (legacyCategory A) X Y Z a
      (ιTensorObj (oldEnrichedHom (legacyCategory A) X Y) (oldEnrichedHom (legacyCategory A) Y Z) i j a hij (f ⊗ₜ[ℝ] g))).val a =
      (originalSuper A).data.comp X Y Z a
        (ιTensorObj ((originalSuper A).data.Hom X Y) ((originalSuper A).data.Hom Y Z) i j a hij (f.val i ⊗ₜ[ℝ] g.val j))
    rw [oldEnrichedComp_tmul]
    exact tComp_homogeneous_at (originalSuper A) i j a hij f.val g.val f.property

def roundtripForward : Superfunctor (originalSuper A) (ofOldSupercategory (legacyCategory A)) :=
  ⟨roundtripForwardData A, roundtripForwardLaws A⟩
def roundtripBackward : Superfunctor (ofOldSupercategory (legacyCategory A)) (originalSuper A) :=
  ⟨roundtripBackwardData A, roundtripBackwardLaws A⟩

end RMod.Legacy.Hierarchy

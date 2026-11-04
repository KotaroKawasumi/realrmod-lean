import RMod.Hierarchy.Abstract.Supercategory
import RMod.Classification.Instances.LinearCategory

/-!
# Enriched operations from the old proved category

The homogeneous Hom spaces are the existing grading submodules. Enriched
composition is the tensor-linear extension of the old composition, and the
identity is the old identity in degree zero. No categorical operation is
replaced by an existential choice.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy

variable (C : WeaklyPointedSuperfusion.{0, 0})

def oldEnrichedHom (X Y : C.data.Obj) : SuperVec :=
  fun a => ModuleCat.of ℝ (Classification.LinearCategory.grade C X Y a)

def oldEnrichedId (X : C.data.Obj) : 𝟙_ SuperVec ⟶ oldEnrichedHom C X X := fun a =>
  if h : a = 0 then
    (GradedObject.singleObjApplyIsoOfEq (0 : ZMod 2) (ModuleCat.of ℝ ℝ) a h).hom ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _
        (⟨C.data.id X, by
          change C.data.id X ∈ C.data.grade X X a
          rw [h]
          exact C.laws.id_even X⟩ :
          Classification.LinearCategory.grade C X X a))
  else (GradedObject.isInitialSingleObjApply (0 : ZMod 2) (ModuleCat.of ℝ ℝ) a h).to _

def oldGradedComp (X Y Z : C.data.Obj) (i j a : ZMod 2) (h : i + j = a) :
    Classification.LinearCategory.grade C X Y i →ₗ[ℝ]
      Classification.LinearCategory.grade C Y Z j →ₗ[ℝ]
        Classification.LinearCategory.grade C X Z a where
  toFun f :=
    { toFun g := ⟨C.data.comp f.val g.val,
        by
          change C.data.comp f.val g.val ∈ C.data.grade X Z a
          rw [← h]
          exact C.laws.comp_grade f.val g.val f.property g.property⟩
      map_add' g k := Subtype.ext (C.laws.comp_add f.val g.val k.val)
      map_smul' r g := Subtype.ext (C.laws.comp_smul r f.val g.val) }
  map_add' f g := LinearMap.ext fun k => Subtype.ext (C.laws.add_comp f.val g.val k.val)
  map_smul' r f := LinearMap.ext fun g => Subtype.ext (C.laws.smul_comp r f.val g.val)

def oldEnrichedComp (X Y Z : C.data.Obj) :
    oldEnrichedHom C X Y ⊗ oldEnrichedHom C Y Z ⟶ oldEnrichedHom C X Z := fun a =>
  GradedObject.Monoidal.tensorObjDesc fun i j h =>
    ModuleCat.ofHom (TensorProduct.lift (oldGradedComp C X Y Z i j a h))

def ofOldSupercategoryData : SupercategoryData where
  Obj := C.data.Obj
  Hom := oldEnrichedHom C
  id := oldEnrichedId C
  comp := oldEnrichedComp C

open scoped TensorProduct in
/-- On every homogeneous tensor generator, the enriched operation is the old composition. -/
theorem oldEnrichedComp_tmul (X Y Z : C.data.Obj) (i j a : ZMod 2) (h : i + j = a)
    (f : Classification.LinearCategory.grade C X Y i)
    (g : Classification.LinearCategory.grade C Y Z j) :
    (oldEnrichedComp C X Y Z a
      (GradedObject.Monoidal.ιTensorObj (oldEnrichedHom C X Y) (oldEnrichedHom C Y Z)
        i j a h (f ⊗ₜ[ℝ] g))).val = C.data.comp f.val g.val := by
  have he := GradedObject.Monoidal.ι_tensorObjDesc
    (X₁ := oldEnrichedHom C X Y) (X₂ := oldEnrichedHom C Y Z)
    (fun i j h => ModuleCat.ofHom (TensorProduct.lift (oldGradedComp C X Y Z i j a h))) i j h
  exact congrArg (fun q => (q (f ⊗ₜ[ℝ] g)).val) he

end RMod.Legacy.Hierarchy

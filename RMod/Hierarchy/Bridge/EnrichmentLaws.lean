import RMod.Hierarchy.Bridge.EnrichmentData

/-!
# Enriched laws inherited from the old category

The unit diagrams reduce to the old identity laws. The associativity diagram
is tested on homogeneous pure tensors, where it is the old associativity law.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem oldEnrichedId_zero (X : C.data.Obj) :
    (oldEnrichedId C X 0 ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1)).val = C.data.id X := by
  let e := tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)
  change ((e.inv ≫ e.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _
    (⟨C.data.id X, C.laws.id_even X⟩ : Classification.LinearCategory.grade C X X 0))) 1).val = _
  rw [Iso.inv_hom_id_assoc]
  exact C.laws.one_smul _

theorem oldEnriched_id_comp (X Y : C.data.Obj) :
    (λ_ (oldEnrichedHom C X Y)).inv ≫
      oldEnrichedId C X ▷ _ ≫ oldEnrichedComp C X X Y = 𝟙 _ := by
  funext a
  change (GradedObject.Monoidal.leftUnitor (oldEnrichedHom C X Y)).inv a ≫
    GradedObject.Monoidal.tensorHom (oldEnrichedId C X) (𝟙 (oldEnrichedHom C X Y)) a ≫
    oldEnrichedComp C X X Y a = 𝟙 _
  erw [GradedObject.Monoidal.leftUnitor_inv_apply, assoc, assoc, ι_tensorHom_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change ((oldEnrichedComp C X X Y a)
    (ιTensorObj (oldEnrichedHom C X X) (oldEnrichedHom C X Y) 0 a a (zero_add a)
      (oldEnrichedId C X 0 ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1) ⊗ₜ[ℝ] f))).val = f.val
  rw [oldEnrichedComp_tmul, oldEnrichedId_zero]
  exact C.laws.id_comp _

theorem oldEnriched_comp_id (X Y : C.data.Obj) :
    (ρ_ (oldEnrichedHom C X Y)).inv ≫
      _ ◁ oldEnrichedId C Y ≫ oldEnrichedComp C X Y Y = 𝟙 _ := by
  funext a
  change (GradedObject.Monoidal.rightUnitor (oldEnrichedHom C X Y)).inv a ≫
    GradedObject.Monoidal.tensorHom (𝟙 (oldEnrichedHom C X Y)) (oldEnrichedId C Y) a ≫
    oldEnrichedComp C X Y Y a = 𝟙 _
  erw [GradedObject.Monoidal.rightUnitor_inv_apply, assoc, assoc, ι_tensorHom_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change ((oldEnrichedComp C X Y Y a)
    (ιTensorObj (oldEnrichedHom C X Y) (oldEnrichedHom C Y Y) a 0 a (add_zero a)
      (f ⊗ₜ[ℝ] oldEnrichedId C Y 0 ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1)))).val = f.val
  rw [oldEnrichedComp_tmul, oldEnrichedId_zero]
  exact C.laws.comp_id _

theorem oldEnriched_assoc (W X Y Z : C.data.Obj) :
    (α_ (oldEnrichedHom C W X) (oldEnrichedHom C X Y) (oldEnrichedHom C Y Z)).inv ≫
      oldEnrichedComp C W X Y ▷ _ ≫ oldEnrichedComp C W Y Z =
    _ ◁ oldEnrichedComp C X Y Z ≫ oldEnrichedComp C W X Z := by
  funext a
  apply tensorObj₃_ext
  intro i j k h
  change ιTensorObj₃ _ _ _ i j k a h ≫
    ((GradedObject.Monoidal.associator _ _ _).inv a ≫
      GradedObject.Monoidal.tensorHom (oldEnrichedComp C W X Y) (𝟙 _) a ≫
      oldEnrichedComp C W Y Z a) =
    ιTensorObj₃ _ _ _ i j k a h ≫
      (GradedObject.Monoidal.tensorHom (𝟙 _) (oldEnrichedComp C X Y Z) a ≫
        oldEnrichedComp C W X Z a)
  erw [ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq _ _ _ i j k a h _ rfl, assoc, assoc, ι_tensorHom_assoc,
    ι_tensorHom_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f gq
  refine TensorProduct.induction_on gq ?_ ?_ ?_
  · simp
  · intro g q
    apply Subtype.ext
    change (oldEnrichedComp C W Y Z a
      (ιTensorObj (oldEnrichedHom C W Y) (oldEnrichedHom C Y Z) (i + j) k a h
        (oldEnrichedComp C W X Y (i + j)
          (ιTensorObj (oldEnrichedHom C W X) (oldEnrichedHom C X Y) i j (i + j) rfl (f ⊗ₜ[ℝ] g)) ⊗ₜ[ℝ] q))).val =
      (oldEnrichedComp C W X Z a
        (ιTensorObj (oldEnrichedHom C W X) (oldEnrichedHom C X Z) i (j + k) a (by rw [← add_assoc, h])
          (f ⊗ₜ[ℝ] oldEnrichedComp C X Y Z (j + k)
            (ιTensorObj (oldEnrichedHom C X Y) (oldEnrichedHom C Y Z) j k (j + k) rfl (g ⊗ₜ[ℝ] q))))).val
    rw [oldEnrichedComp_tmul, oldEnrichedComp_tmul,
      oldEnrichedComp_tmul, oldEnrichedComp_tmul]
    exact C.laws.comp_assoc _ _ _
  · intro x y hx hy
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

theorem ofOldSupercategoryLaws : SupercategoryLaws (ofOldSupercategoryData C) where
  id_comp := oldEnriched_id_comp C
  comp_id := oldEnriched_comp_id C
  assoc := oldEnriched_assoc C

def ofOldSupercategory : Supercategory :=
  ⟨ofOldSupercategoryData C, ofOldSupercategoryLaws C⟩

end RMod.Legacy.Hierarchy

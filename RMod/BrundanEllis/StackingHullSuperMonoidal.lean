import RMod.BrundanEllis.StackingHullMonoidal

/-! The restricted tensor keeps the ambient homogeneous Hom maps. In
particular, the monoidal inclusion is compatible with both even and odd
morphisms; ordinary monoidality alone would not specify this condition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)
  [ObjectProperty.IsMonoidal (AddPiHull C Z)]

/-- Restrict the existing enriched tensor, using the proved closure on objects. -/
def hullTensor : SuperFunctor (SuperTensorProduct (HullCategory C Z) (HullCategory C Z))
    (HullCategory C Z) where
  obj X := ⟨(MonoidalSuperCategory.tensor (C := C)).obj (X.1.obj, X.2.obj), by
    change AddPiHull C Z
      (evenObj C ((MonoidalSuperCategory.tensor (C := C)).obj (X.1.obj, X.2.obj)))
    rw [MonoidalSuperCategory.tensor_objects]
    exact ObjectProperty.prop_tensor X.1.property X.2.property⟩
  map X Y := (MonoidalSuperCategory.tensor (C := C)).map (X.1.obj, X.2.obj) (Y.1.obj, Y.2.obj)
  map_id X := (MonoidalSuperCategory.tensor (C := C)).map_id (X.1.obj, X.2.obj)
  map_comp X Y W := (MonoidalSuperCategory.tensor (C := C)).map_comp
    (X.1.obj, X.2.obj) (Y.1.obj, Y.2.obj) (W.1.obj, W.2.obj)

theorem hullTensor_objects : TensorObjectsAgree (hullTensor C Z) := by
  intro X Y
  apply ObjectProperty.FullSubcategory.ext
  exact MonoidalSuperCategory.tensor_objects X.obj Y.obj

/-- The aligned homogeneous tensor map is precisely the original map. -/
theorem hullTensor_map (X X' Y Y' : Even (HullCategory C Z)) :
    enrichedTensorMap (hullTensor C Z) (hullTensor_objects C Z) X X' Y Y' =
      enrichedTensorMap (MonoidalSuperCategory.tensor (C := C))
        MonoidalSuperCategory.tensor_objects X.obj X'.obj Y.obj Y'.obj := rfl

instance hullSuperMonoidal : MonoidalSuperCategory (HullCategory C Z) where
  tensor := hullTensor C Z
  tensor_objects := hullTensor_objects C Z
  tensor_even f g := by
    rw [hullTensor_map]
    exact MonoidalSuperCategory.tensor_even (C := C) f g
  associator_naturality f g h := by
    with_unfolding_all
      exact MonoidalSuperCategory.associator_naturality (C := C) f g h
  left_naturality f := by
    with_unfolding_all
      exact MonoidalSuperCategory.left_naturality (C := C) f
  right_naturality f := by
    with_unfolding_all
      exact MonoidalSuperCategory.right_naturality (C := C) f

/-- The monoidal inclusion has the all-degree tensor compatibility required
by the stack contract, with identity comparison maps. -/
theorem hullInclusion_tensor_natural
    {X X' Y Y' : Even (HullCategory C Z)}
    (f : THom (HullCategory C Z) X X') (g : THom (HullCategory C Z) Y Y') :
    tComp C
      (tTensor (MonoidalSuperCategory.tensor (C := C)) MonoidalSuperCategory.tensor_objects
        (tMap (hullInclusion C Z) f) (tMap (hullInclusion C Z) g))
      (evenPoint ((hullInclusionMonoidal C Z).μIso X' Y').hom) =
    tComp C (evenPoint ((hullInclusionMonoidal C Z).μIso X Y).hom)
      (tMap (hullInclusion C Z)
        (tTensor (MonoidalSuperCategory.tensor (C := HullCategory C Z))
          MonoidalSuperCategory.tensor_objects f g)) := by
  letI : RMod.SuperCategory C := C.superCategory
  with_unfolding_all
    exact (RMod.EnrichedSupport.tComp_id_right C _).trans
      (RMod.EnrichedSupport.tComp_id_left C _).symm

end RMod.BrundanEllis

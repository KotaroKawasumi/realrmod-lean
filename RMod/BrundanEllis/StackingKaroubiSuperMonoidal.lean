import RMod.BrundanEllis.StackingKaroubiNaturality

/-! The enriched idempotent completion inherits the ambient monoidal
supercategory structure. All coherence is proved on the full graded Hom
objects, so this construction retains the odd morphisms and their signs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]

theorem completedTensor_aligned (P P' Q Q' : Even (Karoubi (Even C))) :
    RMod.enrichedTensorMap SuperVec (completedTensor C) (completedTensor_objects C) P P' Q Q' =
      completedTensorMap P P' Q Q' := by
  simp only [RMod.enrichedTensorMap, eqToHom_refl, Category.id_comp, completedTensorMap]
  rfl

instance completedEnrichedMonoidal : RMod.MonoidalEnrichedCategory SuperVec (Karoubi (Even C)) where
  tensor := completedTensor C
  tensor_objects := completedTensor_objects C
  tensor_even f g := by
    rw [completedTensor_aligned]
    exact completedTensor_even C f g
  associator_isGradedNatural := by
    apply (RMod.associator_isGradedNatural_iff SuperVec (completedTensor C) (completedTensor_objects C)).2
    intros P P' Q Q' R R'
    simp only [completedTensor_aligned]
    exact completed_associator_naturality P P' Q Q' R R'
  leftUnitor_isGradedNatural := by
    apply (RMod.leftUnitor_isGradedNatural_iff SuperVec (completedTensor C) (completedTensor_objects C)).2
    intros P Q
    simp only [completedTensor_aligned]
    exact completed_left_naturality P Q
  rightUnitor_isGradedNatural := by
    apply (RMod.rightUnitor_isGradedNatural_iff SuperVec (completedTensor C) (completedTensor_objects C)).2
    intros P Q
    simp only [completedTensor_aligned]
    exact completed_right_naturality P Q

instance completedSuperMonoidal : MonoidalSuperCategory (Karoubi (Even C)) :=
  Bridge.fromEnriched (Karoubi (Even C))

end RMod.BrundanEllis.Stacking.KaroubiSuper

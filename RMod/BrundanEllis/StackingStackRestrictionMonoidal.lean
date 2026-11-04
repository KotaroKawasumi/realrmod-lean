import RMod.BrundanEllis.StackingSupportedCompositeMonoidal
import RMod.BrundanEllis.StackingStackExteriorMonoidal
import RMod.BrundanEllis.StackingReindexEnrichedTensor
import RMod.BrundanEllis.StackingDiagonalGeneration

/-! The actual stack restriction carries the composite monoidal structure.
Its binary inverse uses the proved diagonal support, and its unit is
normalized using the proved ordinary equivalence. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- Separate first-variable naturality for the ordinary binary comparison. -/
theorem pullbackReindexTensorMap_natural_left (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    {X Y : Even (pullback s)} (u : X ⟶ Y) (Z : Even (pullback s)) :
    (pullbackReindex s f).forget.map u ▷ (pullbackReindex s f).forget.obj Z ≫
      pullbackReindexTensorMap s f Y Z =
    pullbackReindexTensorMap s f X Z ≫ (pullbackReindex s f).forget.map (u ▷ Z) := by
  have hn := pullbackReindexTensorMap_naturality s f u (𝟙 Z)
  rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at hn
  exact hn

/-- Separate second-variable naturality for the same binary comparison. -/
theorem pullbackReindexTensorMap_natural_right (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    {X Y : Even (pullback s)} (Z : Even (pullback s)) (u : X ⟶ Y) :
    (pullbackReindex s f).forget.obj Z ◁ (pullbackReindex s f).forget.map u ≫
      pullbackReindexTensorMap s f Z Y =
    pullbackReindexTensorMap s f Z X ≫ (pullbackReindex s f).forget.map (Z ◁ u) := by
  have hn := pullbackReindexTensorMap_naturality s f (𝟙 Z) u
  rw [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at hn
  exact hn

attribute [local irreducible] stack stackInclusion stackExteriorFunctor stackRestriction

/-- The second binary comparison is invertible on every actual stack image. -/
def stackRestrictionTensorIso (s t : Twist) (h : s.group = t.group) (X Y : Even (stack s t h)) :
    (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h)).forget.obj
        ((stackExteriorFunctor s t h).forget.obj X) ⊗
      (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h)).forget.obj
        ((stackExteriorFunctor s t h).forget.obj Y) ≅
    (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h)).forget.obj
      ((stackExteriorFunctor s t h).forget.obj X ⊗ (stackExteriorFunctor s t h).forget.obj Y) :=
  pullbackReindexTensorIso (exteriorTwist s t).val (diagonalLabelMap s t h)
    (diagonalLabelMap_injective s t h) _ _
    (stackExteriorFunctor_support s t h (ForgetEnrichment.to SuperVec X))

theorem stackRestrictionTensorIso_hom (s t : Twist) (h : s.group = t.group)
    (X Y : Even (stack s t h)) :
    (stackRestrictionTensorIso s t h X Y).hom =
      pullbackReindexTensorMap (exteriorTwist s t).val (diagonalLabelMap s t h)
        ((stackExteriorFunctor s t h).forget.obj X) ((stackExteriorFunctor s t h).forget.obj Y) :=
  pullbackReindexTensorIso_hom (exteriorTwist s t).val (diagonalLabelMap s t h)
    (diagonalLabelMap_injective s t h) _ _
    (stackExteriorFunctor_support s t h (ForgetEnrichment.to SuperVec X))

variable (s t : Twist) (h : s.group = t.group)
  (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
  (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d)

include hl hr in
/-- The same comparison already known to be an equivalence is now strong monoidal. -/
def stackRestrictionMonoidal : (stackRestriction s t h).forget.CoreMonoidal := by
  letI : ((stackExteriorFunctor s t h).comp SuperVec
      (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h))).forget.IsEquivalence := by
    simpa only [stackRestriction] using stackRestriction_isEquivalence s t h
  unfold stackRestriction
  exact supportedCompositeCoreMonoidal (stackExteriorFunctor s t h)
    (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h))
    (stackExteriorMonoidal s t hl hr h)
    (pullbackReindexTensorMap (exteriorTwist s t).val (diagonalLabelMap s t h))
    (pullbackReindexTensorMap_natural_left (exteriorTwist s t).val (diagonalLabelMap s t h))
    (pullbackReindexTensorMap_natural_right (exteriorTwist s t).val (diagonalLabelMap s t h))
    (pullbackReindexTensorMap_associativity (exteriorTwist s t).val (diagonalLabelMap s t h))
    (stackRestrictionTensorIso s t h) (stackRestrictionTensorIso_hom s t h)

attribute [local irreducible] stackRestrictionMonoidal stackExteriorMonoidal
  stackRestrictionTensorIso pullbackReindex supportedCompositeCoreMonoidal

set_option maxHeartbeats 400000 in
/-- All homogeneous degrees respect the assembled stack tensor comparison. -/
theorem stackRestrictionMonoidal_enriched (X X' Y Y' : Even (stack s t h)) :
    let F := stackRestriction s t h
    let M := stackRestrictionMonoidal s t h hl hr
    (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) := by
  letI : ((stackExteriorFunctor s t h).comp SuperVec
      (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h))).forget.IsEquivalence := by
    simpa only [stackRestriction] using stackRestriction_isEquivalence s t h
  unfold stackRestrictionMonoidal stackRestriction
  exact supportedCompositeCoreMonoidal_enriched (stackExteriorFunctor s t h)
    (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h))
    (stackExteriorMonoidal s t hl hr h)
    (pullbackReindexTensorMap (exteriorTwist s t).val (diagonalLabelMap s t h))
    (pullbackReindexTensorMap_natural_left (exteriorTwist s t).val (diagonalLabelMap s t h))
    (pullbackReindexTensorMap_natural_right (exteriorTwist s t).val (diagonalLabelMap s t h))
    (pullbackReindexTensorMap_associativity (exteriorTwist s t).val (diagonalLabelMap s t h))
    (stackRestrictionTensorIso s t h) (stackRestrictionTensorIso_hom s t h)
    (stackExteriorMonoidal_enriched s t hl hr h)
    (pullbackReindexTensorMap_enriched_naturality (exteriorTwist s t).val (diagonalLabelMap s t h))
    X X' Y Y'

end RMod.BrundanEllis.Stacking

import RMod.BrundanEllis.StackingEnrichedUnit

/-! A fully faithful enriched comparison with even representatives gives
an actual strong monoidal superequivalence once its tensor comparison is
specified. Inverse functors and their full graded unit/counit naturality
are constructed here, not added to the comparison's hypotheses. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MonoidalSuperCategory C] [MonoidalSuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
  (R : D → C) (e : ∀ X : D, F.forget.obj (evenObj C (R X)) ≅ evenObj D X)
  (M : F.forget.CoreMonoidal)
  (hM : ∀ {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y'),
    tComp D (tTensor (C := D) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
      (tMap F f) (tMap F g)) (evenPoint (M.μIso X' Y').hom) =
    tComp D (evenPoint (M.μIso X Y).hom)
      (tMap F (tTensor (C := C) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects f g)))

/-- Construct the inverse and both graded naturality witnesses from the
forward comparison and its even object representatives. -/
def monoidalSuperequivalenceOfComparison : MonoidalSuperequivalence C D where
  forward := F
  backward := enrichedInverse F hF R e
  monoidal := M
  unit := enrichedInverseUnit F hF R e
  counit := enrichedInverseCounit F hF R e
  unit_natural f := enrichedInverseUnit_total F hF R e f
  counit_natural f := enrichedInverseCounit_total F hF R e f
  tensor_natural f g := hM f g

end RMod.BrundanEllis.Stacking

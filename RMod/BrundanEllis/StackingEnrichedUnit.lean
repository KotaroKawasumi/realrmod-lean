import RMod.BrundanEllis.StackingEnrichedCounit
import RMod.BrundanEllis.StackingGradedFaithful
import RMod.BrundanEllis.StackingOrbitTransport
import RMod.Enriched.TotalNaturality

/-! The counit of the chosen enriched inverse determines its unit by full
faithfulness. Both comparison maps are natural on all homogeneous degrees,
so the ordinary equivalence lifts without additional naturality assumptions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
  (R : D → C) (e : ∀ X : D, F.forget.obj (evenObj C (R X)) ≅ evenObj D X)

/-- The unit is the inverse counit lifted through the faithful even functor. -/
def enrichedInverseUnit :
    𝟭 (Even C) ≅ F.forget ⋙ (enrichedInverse F hF R e).forget :=
  NatIso.ofComponents
    (fun X => (forgetFullyFaithful F hF).preimageIso
      (e (F.obj (ForgetEnrichment.to SuperVec X))).symm) (by
    intro X Y f
    apply (forgetFullyFaithful F hF).map_injective
    simp only [CategoryTheory.Functor.map_comp, Functor.FullyFaithful.preimageIso,
      Functor.FullyFaithful.map_preimage]
    change F.forget.map f ≫ (e (F.obj (ForgetEnrichment.to SuperVec Y))).inv =
      (e (F.obj (ForgetEnrichment.to SuperVec X))).inv ≫
        F.forget.map ((enrichedInverse F hF R e).forget.map (F.forget.map f))
    rw [inverse_forget_map_image F hF R e
      (X := F.obj (ForgetEnrichment.to SuperVec X))
      (Y := F.obj (ForgetEnrichment.to SuperVec Y)) (F.forget.map f)]
    simp only [Iso.inv_hom_id_assoc])

/-- The image of the chosen unit is precisely the inverse counit. -/
theorem enrichedInverseUnit_map (X : C) :
    F.forget.map ((enrichedInverseUnit F hF R e).hom.app (evenObj C X)) =
      (e (F.obj X)).inv :=
  (forgetFullyFaithful F hF).map_preimage _

/-- Even points are mapped by the same graded Hom map as arbitrary vectors. -/
theorem map_even_point {X Y : Even C} (f : X ⟶ Y) :
    tMap F (evenPoint (ForgetEnrichment.homTo SuperVec f)) =
      evenPoint (ForgetEnrichment.homTo SuperVec (F.forget.map f)) :=
  map_homogeneousPoint F 0 _

/-- The same image identity holds in the total category. -/
theorem enrichedInverseUnit_point (X : C) :
    tMap F (evenPoint ((enrichedInverseUnit F hF R e).hom.app (evenObj C X))) =
      evenPoint (e (F.obj X)).inv := by
  exact (map_even_point F ((enrichedInverseUnit F hF R e).hom.app (evenObj C X))).trans
    (congrArg (fun f => evenPoint (ForgetEnrichment.homTo SuperVec f))
      (enrichedInverseUnit_map F hF R e X))

/-- The enriched counit is natural on arbitrary total morphisms. -/
theorem enrichedInverseCounit_total {X Y : D} (f : THom D X Y) :
    tComp D (tMap F (tMap (enrichedInverse F hF R e) f)) (evenPoint (e Y).hom) =
      tComp D (evenPoint (e X).hom) f := by
  with_unfolding_all
    exact RMod.Regression.hom_equation_total (D := D)
      (A := F.forget.obj (evenObj C (R X))) (B := F.forget.obj (evenObj C (R Y)))
      (A' := evenObj D X) (B' := evenObj D Y)
      (inverseHom F hF R e X Y ≫ F.map (R X) (R Y)) (𝟙 (SHom D X Y))
      (e X).hom (e Y).hom
      (by
        rw [Category.assoc, Category.id_comp]
        exact inverseHom_counit F hF R e X Y) f

/-- The lifted unit inherits full graded naturality by faithful cancellation. -/
theorem enrichedInverseUnit_total {X Y : C} (f : THom C X Y) :
    tComp C f (evenPoint ((enrichedInverseUnit F hF R e).hom.app (evenObj C Y))) =
      tComp C (evenPoint ((enrichedInverseUnit F hF R e).hom.app (evenObj C X)))
        (tMap (enrichedInverse F hF R e) (tMap F f)) := by
  apply (totalFullyFaithful F hF).map_injective
  change (totalSuperFunctor F).map (_ ≫ _) = (totalSuperFunctor F).map (_ ≫ _)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  change tComp D (tMap F f)
      (tMap F (evenPoint ((enrichedInverseUnit F hF R e).hom.app (evenObj C Y)))) =
    tComp D (tMap F (evenPoint ((enrichedInverseUnit F hF R e).hom.app (evenObj C X))))
      (tMap F (tMap (enrichedInverse F hF R e) (tMap F f)))
  rw [enrichedInverseUnit_point, enrichedInverseUnit_point]
  let ex := (superEvenToTotal D).mapIso (e (F.obj X))
  let ey := (superEvenToTotal D).mapIso (e (F.obj Y))
  change tMap F f ≫ ey.inv = ex.inv ≫ tMap F (tMap (enrichedInverse F hF R e) (tMap F f))
  apply (cancel_mono ey.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
  have h := enrichedInverseCounit_total F hF R e (tMap F f)
  change tMap F (tMap (enrichedInverse F hF R e) (tMap F f)) ≫ ey.hom =
    ex.hom ≫ tMap F f at h
  rw [h, Iso.inv_hom_id_assoc]

end RMod.BrundanEllis.Stacking

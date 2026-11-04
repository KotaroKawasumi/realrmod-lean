import RMod.BrundanEllis.StackingEnrichedInverse

/-! The chosen object comparisons form an actual counit for the enriched
inverse. Naturality follows from the defining conjugation of the full Hom
maps, rather than a separate assumption on the even arrows. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
  (R : D → C) (e : ∀ X : D, F.forget.obj (evenObj C (R X)) ≅ evenObj D X)

/-- The forward image of the inverse Hom map is conjugation by the counit. -/
theorem inverse_forget_map_image {X Y : D} (f : evenObj D X ⟶ evenObj D Y) :
    F.forget.map ((enrichedInverse F hF R e).forget.map f) =
      (e X).hom ≫ f ≫ (e Y).inv := by
  change (ForgetEnrichment.homTo SuperVec f ≫ inverseHom F hF R e X Y) ≫ F.map _ _ = _
  rw [Category.assoc, inverseHom_map]
  change eHomEquiv SuperVec f ≫ (Iso.eHomCongr SuperVec (e X) (e Y)).inv =
    eHomEquiv SuperVec ((e X).hom ≫ f ≫ (e Y).inv)
  simp only [Iso.eHomCongr, ← Category.assoc]
  rw [even_pre, even_post]

/-- The counit square commutes on the entire enriched Hom object. -/
@[reassoc] theorem inverseHom_counit (X Y : D) :
    inverseHom F hF R e X Y ≫ F.map (R X) (R Y) ≫
      eHomWhiskerLeft SuperVec (F.forget.obj (evenObj C (R X))) (e Y).hom =
        eHomWhiskerRight SuperVec (e X).hom (evenObj D Y) := by
  rw [inverseHom_map_assoc]
  simp only [Iso.eHomCongr, Category.assoc, ← eHomWhiskerLeft_comp,
    Iso.inv_hom_id, eHomWhiskerLeft_id, Category.comp_id]

/-- The object comparisons are natural for the actual inverse functor. -/
def enrichedInverseCounit :
    (enrichedInverse F hF R e).forget ⋙ F.forget ≅ 𝟭 (Even D) :=
  NatIso.ofComponents (fun X => e (ForgetEnrichment.to SuperVec X)) (by
    intro X Y f
    change F.forget.map ((enrichedInverse F hF R e).forget.map f) ≫ (e (ForgetEnrichment.to SuperVec Y)).hom =
      (e (ForgetEnrichment.to SuperVec X)).hom ≫ f
    rw [inverse_forget_map_image F hF R e
      (X := ForgetEnrichment.to SuperVec X) (Y := ForgetEnrichment.to SuperVec Y) f]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end RMod.BrundanEllis.Stacking

import RMod.BrundanEllis.StackingOrbitTransport
import RMod.BrundanEllis.ParityBridge
import RMod.Enriched.GradedSchur

/-! Degree-zero total isomorphisms lift to the even category, while the
specified parity comparison is odd. These constructions work before any
fusion or weakly pointed conditions are known. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking.GradedIso
variable (C : Type) [SuperCategory C]

def even {X Y : Even C} (e : totalObj C X ≅ totalObj C Y)
    (hf : e.hom ∈ grade C X Y 0) (hg : e.inv ∈ grade C Y X 0) : X ≅ Y := by
  let L := RMod.StatementLegacy.toLegacySupercategory (Bridge.bundled C)
  let F := RMod.Legacy.evenToTotal L
  let f := RMod.EnrichedSupport.liftEven L e.hom hf
  let g := RMod.EnrichedSupport.liftEven L e.inv hg
  refine { hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }
  · with_unfolding_all
      apply F.map_injective
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        RMod.EnrichedSupport.liftEven_map, RMod.EnrichedSupport.liftEven_map]
      exact e.hom_inv_id
  · with_unfolding_all
      apply F.map_injective
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        RMod.EnrichedSupport.liftEven_map, RMod.EnrichedSupport.liftEven_map]
      exact e.inv_hom_id

variable [MonoidalCategory (Even C)] [MonoidalSuperCategory C] [MonoidalPiSuperCategory C]

def parity (X : C) : totalObj C ((piFunctor C).obj X) ≅ totalObj C X where
  hom := homogeneousPoint 1 (ParityConstruction.zeta C X)
  inv := homogeneousPoint 1 (ParityConstruction.zetaInv C X)
  hom_inv_id := ParityConstruction.zeta_hom_inv C X
  inv_hom_id := ParityConstruction.zeta_inv_hom C X

theorem parity_hom_grade (X : C) :
    (parity C X).hom ∈ grade C ((piFunctor C).obj X) X 1 := by
  intro b hb
  change b ≠ 1 at hb
  change homogeneousPoint 1 (ParityConstruction.zeta C X) b = 0
  simp only [homogeneousPoint, dif_neg hb]

theorem parity_inv_grade (X : C) :
    (parity C X).inv ∈ grade C X ((piFunctor C).obj X) 1 := by
  intro b hb
  change b ≠ 1 at hb
  change homogeneousPoint 1 (ParityConstruction.zetaInv C X) b = 0
  simp only [homogeneousPoint, dif_neg hb]

def parityTwice (X : Even C) : (piFunctor C).forget.obj ((piFunctor C).forget.obj X) ≅ X := by
  let e := parity C ((piFunctor C).obj X) ≪≫ parity C X
  exact even C e (homogeneous_comp_grade C (parity_hom_grade C _) (parity_hom_grade C _))
    (homogeneous_comp_grade C (parity_inv_grade C _) (parity_inv_grade C _))

end RMod.BrundanEllis.Stacking.GradedIso

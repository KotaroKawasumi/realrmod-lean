import RMod.BrundanEllis.StackingHullTensor
import RMod.Enriched.GradedSchur

/-! Even cancellation of two parity shifts, built from the specified odd
isomorphisms. This proves closure of the completion under its parity functor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (C : WeaklyPointedFusionPiSuperCat)

/-- Degree-zero inverse pairs lift uniquely to the existing even category. -/
def evenIsoOfTotal {X Y : Even C} (f : THom C X Y) (g : THom C Y X)
    (hf : f ∈ grade C X Y 0) (hg : g ∈ grade C Y X 0)
    (hfg : tComp C f g = evenPoint (eId SuperVec X))
    (hgf : tComp C g f = evenPoint (eId SuperVec Y)) : X ≅ Y := by
  let L := (ParityConstruction.monoidal C).super
  let F := RMod.Legacy.evenToTotal L
  let f' := RMod.EnrichedSupport.liftEven L f hf
  let g' := RMod.EnrichedSupport.liftEven L g hg
  refine { hom := f', inv := g', hom_inv_id := ?_, inv_hom_id := ?_ }
  · with_unfolding_all
      apply F.map_injective
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        RMod.EnrichedSupport.liftEven_map, RMod.EnrichedSupport.liftEven_map]
      exact hfg
  · with_unfolding_all
      apply F.map_injective
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        RMod.EnrichedSupport.liftEven_map, RMod.EnrichedSupport.liftEven_map]
      exact hgf

/-- The existing odd comparison, as an isomorphism of the total category. -/
def totalPiIso (X : C) :
    RMod.Legacy.totalObj (ParityConstruction.monoidal C).super ((piFunctor C).obj X) ≅
      RMod.Legacy.totalObj (ParityConstruction.monoidal C).super X where
  hom := homogeneousPoint 1 (ParityConstruction.zeta C X)
  inv := homogeneousPoint 1 (ParityConstruction.zetaInv C X)
  hom_inv_id := ParityConstruction.zeta_hom_inv C X
  inv_hom_id := ParityConstruction.zeta_inv_hom C X

theorem totalPiIso_hom_odd (X : C) :
    (totalPiIso C X).hom ∈ RMod.Legacy.grade (ParityConstruction.monoidal C).super
      ((piFunctor C).obj X) X 1 := by
  change homogeneousPoint 1 (ParityConstruction.zeta C X) ∈ _
  rw [ParityConstruction.point_zeta]
  exact RMod.Legacy.BrundanEllisParity.z_hom_odd
    (ParityConstruction.monoidal C) (ParityConstruction.parity C) X

theorem totalPiIso_inv_odd (X : C) :
    (totalPiIso C X).inv ∈ RMod.Legacy.grade (ParityConstruction.monoidal C).super
      X ((piFunctor C).obj X) 1 := by
  change homogeneousPoint 1 (ParityConstruction.zetaInv C X) ∈ _
  rw [ParityConstruction.point_zetaInv]
  exact RMod.Legacy.BrundanEllisParity.z_inv_odd
    (ParityConstruction.monoidal C) (ParityConstruction.parity C) X

/-- Two odd comparisons compose to an even isomorphism, with their actual inverses. -/
def piTwiceIso (X : Even C) :
    evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗
      (evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ X) ≅ X := by
  let e := (totalPiIso C ((piFunctor C).obj X)) ≪≫ totalPiIso C X
  refine evenIsoOfTotal C e.hom e.inv ?_ ?_ e.hom_inv_id e.inv_hom_id
  · exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal C).super _ _
      (totalPiIso_hom_odd C _) (totalPiIso_hom_odd C _)
  · exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal C).super _ _
      (totalPiIso_inv_odd C _) (totalPiIso_inv_odd C _)

end Stacking
namespace AddPiHull
variable {C : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

/-- Closing under generators, finite sums and even retracts already closes under Π. -/
theorem parity {X : Even C} (h : AddPiHull C Z X) :
    AddPiHull C Z (evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ X) := by
  let P := evenObj C (MonoidalPiSuperCategory.pi (C := C))
  letI := leftTensorAdditive P
  apply map (tensorLeft P) (fun i p => ?_) h
  cases p
  · exact parityGenerator i
  · exact (iso_iff (Stacking.piTwiceIso C (Z i))).mpr (generator i)

end AddPiHull
end RMod.BrundanEllis

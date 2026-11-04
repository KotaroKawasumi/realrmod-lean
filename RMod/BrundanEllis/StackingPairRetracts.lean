import RMod.BrundanEllis.StackingPairSums
import RMod.BrundanEllis.StackingBilinear

/-! Parity shifts of exterior images can be absorbed in the left factor.
Consequently every object in the additive parity completion is an even
retract of a single paired object, not merely of a sum of such objects. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B D : WeaklyPointedFusionPiSuperCat}

/-- An enriched functor carries the odd parity comparison to an even
comparison with the target parity functor. No monoidal constraint is used. -/
def mapParityIso (F : SuperFunctor A D) (X : Even A) :
    F.forget.obj ((piFunctor A).obj X) ≅ (piFunctor D).obj (F.forget.obj X) := by
  let z : totalObj A ((piFunctor A).obj X) ≅ totalObj A X := {
    hom := (totalPiIso A X).hom
    inv := (totalPiIso A X).inv
    hom_inv_id := (totalPiIso A X).hom_inv_id
    inv_hom_id := (totalPiIso A X).inv_hom_id }
  let w : totalObj D ((piFunctor D).obj (F.forget.obj X)) ≅ totalObj D (F.obj X) := {
    hom := (totalPiIso D (F.obj X)).hom
    inv := (totalPiIso D (F.obj X)).inv
    hom_inv_id := (totalPiIso D (F.obj X)).hom_inv_id
    inv_hom_id := (totalPiIso D (F.obj X)).inv_hom_id }
  let e := (totalFunctor F).mapIso z ≪≫ w.symm
  refine evenIsoOfTotal D e.hom e.inv ?_ ?_ e.hom_inv_id e.inv_hom_id
  · exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal D).super _ _
      (tMap_grade F (totalPiIso_hom_odd A X)) (totalPiIso_inv_odd D (F.obj X))
  · exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal D).super _ _
      (totalPiIso_hom_odd D (F.obj X)) (tMap_grade F (totalPiIso_inv_odd A X))

/-- Absorb every parity bit before taking the rectangular pair of sums. -/
theorem pairHull_retract (F : SuperFunctor (SuperTensorProduct A B) D)
    {W : Even D}
    (h : AddPiHull D (fun Z => evenObj D (F.obj Z)) W) :
    ∃ (X : Even A) (Y : Even B), Nonempty (Retract W ((evenPair F).obj (X, Y))) := by
  classical
  obtain ⟨n, Z, p, ⟨r⟩⟩ := h
  let X : Fin n → Even A := fun i =>
    if p i then (piFunctor A).obj (Z i).1 else evenObj A (Z i).1
  let Y : Fin n → Even B := fun i => evenObj B (Z i).2
  let e (i : Fin n) :
      (if p i then evenObj D (MonoidalPiSuperCategory.pi (C := D)) ⊗
        evenObj D (F.obj (Z i)) else evenObj D (F.obj (Z i))) ≅
      (evenPair F).obj (X i, Y i) := by
    dsimp [X, Y]
    cases hp : p i
    · exact Iso.refl _
    · exact (mapParityIso (pairRight F (Z i).2) (evenObj A (Z i).1)).symm
  exact ⟨⨁ X, ⨁ Y, ⟨r.trans ((Retract.ofIso (biproduct.mapIso e)).trans
    (pairSumRetract F X Y))⟩⟩

end RMod.BrundanEllis.Stacking

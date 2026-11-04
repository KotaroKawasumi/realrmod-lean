import RMod.BrundanEllis.MonoidalBridge
import RMod.Hierarchy.Instances.TotalFunctor

/-! Any enriched functor preserves homogeneous inverse pairs. Applied to
the odd identification of pi with the unit, this supplies the pi data on
strictly unit-preserving constructions such as products and completions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]

/-- The total functor is available without fusion or monoidal hypotheses. -/
def totalSuperFunctor (F : SuperFunctor C D) : TotalCategory C ⥤ TotalCategory D where
  obj X := F.obj X
  map := tMap F
  map_id X := by
    with_unfolding_all
      exact RMod.Legacy.tMap_id
        (RMod.StatementLegacy.StatementBridge.toFunctor
          (C := Bridge.bundled C) (D := Bridge.bundled D) F) X
  map_comp f g := by
    with_unfolding_all
      exact RMod.Legacy.tMap_comp
        (RMod.StatementLegacy.StatementBridge.toFunctor
          (C := Bridge.bundled C) (D := Bridge.bundled D) F) f g

theorem map_homogeneousPoint (F : SuperFunctor C D) {X Y : C} (p : ZMod 2)
    (f : (GradedObject.single p).obj (ModuleCat.of ℝ ℝ) ⟶ SHom C X Y) :
    tMap F (homogeneousPoint p f) = homogeneousPoint p (f ≫ F.map X Y) := by
  funext a
  by_cases h : a = p
  · subst a
    simp only [tMap, homogeneousPoint, dif_pos rfl]
    rfl
  · simp only [tMap, homogeneousPoint, h, dite_false, map_zero]

variable [MonoidalCategory (Even C)] [MonoidalPiSuperCategory C]

theorem mapped_pi_hom_inv (F : SuperFunctor C D) :
    tComp D
      (homogeneousPoint 1 (MonoidalPiSuperCategory.hom (C := C) ≫
        F.map MonoidalPiSuperCategory.pi (ForgetEnrichment.to SuperVec (𝟙_ (Even C)))))
      (homogeneousPoint 1 (MonoidalPiSuperCategory.inv (C := C) ≫
        F.map (ForgetEnrichment.to SuperVec (𝟙_ (Even C))) MonoidalPiSuperCategory.pi)) =
      evenPoint (eId SuperVec (F.obj (MonoidalPiSuperCategory.pi (C := C)))) := by
  let X : C := MonoidalPiSuperCategory.pi (C := C)
  let Y : C := ForgetEnrichment.to SuperVec (𝟙_ (Even C))
  let f : THom C X Y := homogeneousPoint 1 (MonoidalPiSuperCategory.hom (C := C))
  let g : THom C Y X := homogeneousPoint 1 (MonoidalPiSuperCategory.inv (C := C))
  calc
    _ = tComp D (tMap F f) (tMap F g) :=
      congrArg₂ (fun (u : THom D (F.obj X) (F.obj Y))
        (v : THom D (F.obj Y) (F.obj X)) => tComp D u v)
        (map_homogeneousPoint F 1 _).symm (map_homogeneousPoint F 1 _).symm
    _ = tMap F (tComp C f g) := ((totalSuperFunctor F).map_comp f g).symm
    _ = tMap F (evenPoint (eId SuperVec X)) :=
      congrArg (fun u : THom C X X => tMap F u) (MonoidalPiSuperCategory.hom_inv (C := C))
    _ = _ := (totalSuperFunctor F).map_id X

theorem mapped_pi_inv_hom (F : SuperFunctor C D) :
    tComp D
      (homogeneousPoint 1 (MonoidalPiSuperCategory.inv (C := C) ≫
        F.map (ForgetEnrichment.to SuperVec (𝟙_ (Even C))) MonoidalPiSuperCategory.pi))
      (homogeneousPoint 1 (MonoidalPiSuperCategory.hom (C := C) ≫
        F.map MonoidalPiSuperCategory.pi (ForgetEnrichment.to SuperVec (𝟙_ (Even C))))) =
      evenPoint (eId SuperVec (F.obj (ForgetEnrichment.to SuperVec (𝟙_ (Even C))))) := by
  let X : C := MonoidalPiSuperCategory.pi (C := C)
  let Y : C := ForgetEnrichment.to SuperVec (𝟙_ (Even C))
  let f : THom C X Y := homogeneousPoint 1 (MonoidalPiSuperCategory.hom (C := C))
  let g : THom C Y X := homogeneousPoint 1 (MonoidalPiSuperCategory.inv (C := C))
  calc
    _ = tComp D (tMap F g) (tMap F f) :=
      congrArg₂ (fun (u : THom D (F.obj Y) (F.obj X))
        (v : THom D (F.obj X) (F.obj Y)) => tComp D u v)
        (map_homogeneousPoint F 1 _).symm (map_homogeneousPoint F 1 _).symm
    _ = tMap F (tComp C g f) := ((totalSuperFunctor F).map_comp g f).symm
    _ = tMap F (evenPoint (eId SuperVec Y)) :=
      congrArg (fun u : THom C Y Y => tMap F u) (MonoidalPiSuperCategory.inv_hom (C := C))
    _ = _ := (totalSuperFunctor F).map_id Y

end RMod.BrundanEllis.Stacking

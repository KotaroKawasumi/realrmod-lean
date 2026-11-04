import RMod.BrundanEllis.StackingHullOrbits
import RMod.Hierarchy.Instances.TotalFunctor

/-! Parity orbits are functorial under enriched functors. Consequently tensor
closure of a completion can be checked on the unshifted generating objects;
the four parity choices require no additional closure assumptions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : WeaklyPointedFusionPiSuperCat}

/-- The given homogeneous maps act on the total category degree by degree. -/
def totalFunctor (F : SuperFunctor C D) : TotalCategory C ⥤ TotalCategory D where
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

theorem tMap_grade (F : SuperFunctor C D) {X Y : C} {a : ZMod 2}
    {f : THom C X Y} (hf : f ∈ grade C X Y a) :
    tMap F f ∈ grade D (F.obj X) (F.obj Y) a := by
  intro b hb
  change F.map X Y b (f b) = 0
  rw [show f b = 0 from hf b hb, map_zero]

theorem map_orbit (F : SuperFunctor C D) {X Y : C}
    (h : SameParityOrbit C X Y) : SameParityOrbit D (F.obj X) (F.obj Y) := by
  obtain ⟨a, e, hf, hg⟩ := h
  exact ⟨a, (totalFunctor F).mapIso e, tMap_grade F hf, tMap_grade F hg⟩

theorem orbit_refl (X : C) : SameParityOrbit C X X := by
  refine ⟨0, Iso.refl _, ?_, ?_⟩
  all_goals
    exact RMod.Legacy.evenPoint_mem_grade (ParityConstruction.monoidal C).super
      (eId SuperVec X)

theorem orbit_symm {X Y : C} (h : SameParityOrbit C X Y) : SameParityOrbit C Y X := by
  obtain ⟨a, e, hf, hg⟩ := h
  exact ⟨a, e.symm, hg, hf⟩

theorem orbit_trans {X Y W : C} (h : SameParityOrbit C X Y)
    (k : SameParityOrbit C Y W) : SameParityOrbit C X W := by
  obtain ⟨a, e, hf, hg⟩ := h
  obtain ⟨b, d, hu, hv⟩ := k
  refine ⟨a + b, e ≪≫ d, ?_, ?_⟩
  · exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal C).super _ _ hf hu
  · rw [add_comm a b]
    exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal C).super _ _ hv hg

theorem parity_orbit (X : C) :
    SameParityOrbit C ((piFunctor C).obj X) X := by
  let e : totalObj C ((piFunctor C).obj X) ≅ totalObj C X := {
    hom := (totalPiIso C X).hom
    inv := (totalPiIso C X).inv
    hom_inv_id := (totalPiIso C X).hom_inv_id
    inv_hom_id := (totalPiIso C X).inv_hom_id }
  exact ⟨1, e, totalPiIso_hom_odd C X, totalPiIso_inv_odd C X⟩

/-- Tensoring one variable is enriched, hence preserves homogeneous isomorphisms. -/
def tensorLeftSuper (X : C) : SuperFunctor C C :=
  (RMod.insertLeft SuperVec X).comp SuperVec
    (RMod.alignedTensor SuperVec MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects)
def tensorRightSuper (Y : C) : SuperFunctor C C :=
  (RMod.insertRight SuperVec Y).comp SuperVec
    (RMod.alignedTensor SuperVec MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects)

end Stacking
namespace AddPiHull
variable {C : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

/-- It suffices to check the ordinary generating pairs. Parity shifts follow
by enriched functoriality and the established orbit closure. -/
theorem tensor_of_unshifted_generators
    (h : ∀ i j, AddPiHull C Z (Z i ⊗ Z j))
    {X Y : Even C} (hX : AddPiHull C Z X) (hY : AddPiHull C Z Y) :
    AddPiHull C Z (X ⊗ Y) := by
  apply tensor_of_generators (fun i j p q => ?_) hX hY
  let A := if p then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z i else Z i
  let B := if q then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z j else Z j
  have hA : SameParityOrbit C A (Z i) := by
    cases p
    · exact Stacking.orbit_refl _
    · exact Stacking.parity_orbit _
  have hB : SameParityOrbit C B (Z j) := by
    cases q
    · exact Stacking.orbit_refl _
    · exact Stacking.parity_orbit _
  have h₁ := Stacking.map_orbit (Stacking.tensorRightSuper (C := C) B) hA
  have h₂ := Stacking.map_orbit (Stacking.tensorLeftSuper (C := C) (Z i)) hB
  exact of_orbit (Stacking.orbit_symm (Stacking.orbit_trans h₁ h₂)) (h i j)

end AddPiHull
end RMod.BrundanEllis

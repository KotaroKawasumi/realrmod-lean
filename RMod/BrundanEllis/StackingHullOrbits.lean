import RMod.BrundanEllis.StackingHullSemisimple
import RMod.BrundanEllis.StackingParity

/-! The completion is closed under the full parity orbit of each member.
A homogeneous odd isomorphism becomes even after one parity shift; this is
what allows the finite ambient list of simple parity orbits to restrict. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
namespace Stacking
variable (C : WeaklyPointedFusionPiSuperCat)

/-- An orbit comparison is either even, or even after a single parity shift. -/
theorem even_or_parity_iso {X Y : Even C} (h : SameParityOrbit C X Y) :
    Nonempty (X ≅ Y) ∨ Nonempty
      ((evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ X) ≅ Y) := by
  obtain ⟨a, e, hf, hg⟩ := h
  fin_cases a
  · exact Or.inl ⟨evenIsoOfTotal C e.hom e.inv hf hg e.hom_inv_id e.inv_hom_id⟩
  · let z : totalObj C ((piFunctor C).obj X) ≅ totalObj C X := {
      hom := (totalPiIso C X).hom
      inv := (totalPiIso C X).inv
      hom_inv_id := (totalPiIso C X).hom_inv_id
      inv_hom_id := (totalPiIso C X).inv_hom_id }
    let u := z ≪≫ e
    apply Or.inr
    refine ⟨evenIsoOfTotal C u.hom u.inv ?_ ?_ u.hom_inv_id u.inv_hom_id⟩
    · exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal C).super _ _
        (totalPiIso_hom_odd C X) hf
    · exact RMod.Legacy.tComp_mem_grade (ParityConstruction.monoidal C).super _ _
        hg (totalPiIso_inv_odd C X)

end Stacking
namespace AddPiHull
variable {C : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

/-- Membership depends only on the parity orbit, not its chosen representative. -/
theorem of_orbit {X Y : Even C} (h : SameParityOrbit C X Y) (hX : AddPiHull C Z X) :
    AddPiHull C Z Y := by
  rcases Stacking.even_or_parity_iso C h with h | h
  · obtain ⟨e⟩ := h
    exact (iso_iff e).mp hX
  · obtain ⟨e⟩ := h
    exact (iso_iff e).mp (parity hX)

end AddPiHull
variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)

/-- Subobject closure also makes a simple object of the hull ambiently simple. -/
theorem hull_simple_ambient (X : Even (HullCategory C Z)) [Simple X] : Simple X.obj := by
  let F := (hullInclusion C Z).forget
  refine ⟨fun {Y} f _ => ?_⟩
  let Y' : Even (HullCategory C Z) := evenObj _
    ⟨Y, ObjectProperty.prop_of_mono (AddPiHull C Z) f X.property⟩
  let f' : Y' ⟶ X := f
  have hf : F.map f' = f := by simp [F, hullInclusion, EnrichedFunctor.forget]; rfl
  haveI : Mono f' := F.mono_of_mono_map (by rw [hf]; infer_instance)
  rw [← hf]
  exact (isIso_iff_of_reflects_iso f' F).trans
    ((Simple.mono_isIso_iff_nonzero f').trans (not_congr (Functor.map_eq_zero_iff F)).symm)

/-- Retaining precisely the ambient representatives belonging to the hull
provides its finite list of simple parity orbits. -/
theorem hull_finite_simples :
    ∃ (n : ℕ) (S : Fin n → Even (HullCategory C Z)),
      (∀ i, Simple (S i)) ∧ ∀ X : Even (HullCategory C Z), Simple X →
        ∃ i, SameParityOrbit (HullCategory C Z) X (S i) := by
  classical
  obtain ⟨n, S, hS, hcover⟩ := FusionPiSuperCategory.finite_simples (C := C)
  let J := {i : Fin n // AddPiHull C Z (S i)}
  let e := (Fintype.equivFin J).symm
  let T : J → Even (HullCategory C Z) := fun i => evenObj _ ⟨S i.val, i.property⟩
  refine ⟨Fintype.card J, T ∘ e, fun i => hull_simple_of_ambient C Z (T (e i)) (hS _), ?_⟩
  intro X hX
  letI := hX
  have hs : Simple X.obj := hull_simple_ambient C Z X
  obtain ⟨i, a, u, hu, hv⟩ := hcover X.obj hs
  have hi : AddPiHull C Z (S i) := AddPiHull.of_orbit ⟨a, u, hu, hv⟩ X.property
  let j : J := ⟨i, hi⟩
  refine ⟨e.symm j, ?_⟩
  change SameParityOrbit (HullCategory C Z) X (T (e (e.symm j)))
  rw [e.apply_symm_apply]
  let v : totalObj (HullCategory C Z) X ≅ totalObj (HullCategory C Z) (T j) := {
    hom := u.hom
    inv := u.inv
    hom_inv_id := u.hom_inv_id
    inv_hom_id := u.inv_hom_id }
  exact ⟨a, v, hu, hv⟩

end RMod.BrundanEllis

import RMod.Hierarchy.Bridge.LegacyData
import RMod.Hierarchy.Instances.EvenTotal

/-!
# The legacy even predicates on extracted data

The degree-zero Hom equivalence identifies the raw cancellation and
invertibility predicates with Mathlib's monomorphisms and isomorphisms.
Consequently the two definitions of a simple object agree.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : MonoidalSupercategory)

private def liftEven {X Y : Even C.super} (f : THom C.super.data X Y)
    (hf : f ∈ grade C.super X Y 0) : X ⟶ Y :=
  (evenHomGradeEquiv C.super X Y).symm ⟨f, hf⟩

private theorem liftEven_map {X Y : Even C.super} (f : THom C.super.data X Y)
    (hf : f ∈ grade C.super X Y 0) : evenPoint (liftEven C f hf) = f :=
  congrArg Subtype.val ((evenHomGradeEquiv C.super X Y).apply_symm_apply ⟨f, hf⟩)

theorem legacyEvenMono_iff {X Y : Even C.super} (f : X ⟶ Y) :
    (toOldData C).IsEvenMono (evenPoint f) ↔ Mono f := by
  constructor
  · rintro ⟨_, h⟩
    refine ⟨fun {Z} g k e => ?_⟩
    apply evenPoint_injective (C.data.Hom Z X)
    apply h Z (evenPoint g) (evenPoint k)
      (evenPoint_mem_grade C.super g) (evenPoint_mem_grade C.super k)
    have he := congrArg ((evenToTotal C.super).map) e
    simp only [CategoryTheory.Functor.map_comp] at he
    exact he
  · intro h
    letI := h
    refine ⟨evenPoint_mem_grade C.super f, fun Z g k hg hk he => ?_⟩
    let g' : evenObj C.super Z ⟶ X := liftEven C g hg
    let k' : evenObj C.super Z ⟶ X := liftEven C k hk
    have h' : g' ≫ f = k' ≫ f := by
      apply (evenToTotal C.super).map_injective
      rw [Functor.map_comp, Functor.map_comp]
      change tComp C.super.data (evenPoint g') (evenPoint f) =
        tComp C.super.data (evenPoint k') (evenPoint f)
      rw [liftEven_map C g hg, liftEven_map C k hk]
      exact he
    have hk' := (cancel_mono f).mp h'
    have hm := congrArg ((evenToTotal C.super).map) hk'
    exact (liftEven_map C g hg).symm.trans (hm.trans (liftEven_map C k hk))

theorem legacyEvenIso_iff {X Y : Even C.super} (f : X ⟶ Y) :
    (toOldData C).IsEvenIso (evenPoint f) ↔ IsIso f := by
  constructor
  · rintro ⟨_, g, hg, hfg, hgf⟩
    let g' : Y ⟶ X := liftEven C g hg
    refine ⟨⟨g', ?_, ?_⟩⟩
    · apply (evenToTotal C.super).map_injective
      rw [Functor.map_comp, CategoryTheory.Functor.map_id]
      change tComp C.super.data (evenPoint f) (evenPoint g') = _
      rw [liftEven_map C g hg]
      exact hfg
    · apply (evenToTotal C.super).map_injective
      rw [Functor.map_comp, CategoryTheory.Functor.map_id]
      change tComp C.super.data (evenPoint g') (evenPoint f) = _
      rw [liftEven_map C g hg]
      exact hgf
  · intro h
    letI := h
    refine ⟨evenPoint_mem_grade C.super f, evenPoint (inv (C := Even C.super) f),
      evenPoint_mem_grade C.super (inv (C := Even C.super) f), ?_, ?_⟩
    · have he := congrArg ((evenToTotal C.super).map) (IsIso.hom_inv_id f)
      simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      exact he
    · have he := congrArg ((evenToTotal C.super).map) (IsIso.inv_hom_id f)
      simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      exact he

theorem legacySimple_iff (X : Even C.super) :
    (toOldData C).IsSimple X ↔ Simple X := by
  constructor
  · intro h
    refine ⟨fun {Y} f _ => ?_⟩
    have he := h Y (evenPoint f) ((legacyEvenMono_iff C f).mpr inferInstance)
    exact (legacyEvenIso_iff C f).symm.trans
      (he.trans (not_congr (Functor.map_eq_zero_iff (evenToTotal C.super))))
  · intro h
    letI := h
    intro Y f hf
    let f' : evenObj C.super Y ⟶ X := liftEven C f hf.1
    have hm : evenPoint f' = f := liftEven_map C f hf.1
    haveI : Mono f' := (legacyEvenMono_iff C f').mp (hm.symm ▸ hf)
    rw [← hm, legacyEvenIso_iff C f', Simple.mono_isIso_iff_nonzero]
    exact not_congr (Functor.map_eq_zero_iff (evenToTotal C.super)).symm

end RMod.Legacy.Hierarchy

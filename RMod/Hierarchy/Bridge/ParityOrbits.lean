import RMod.Hierarchy.Bridge.Grading
import RMod.Hierarchy.Bridge.SimpleObjects
import RMod.Classification.Abstract.Reference

/-!
# Simple parity orbits and the graded Schur property

The total equivalence preserves both parities and reflects invertibility.
Consequently the old finite representatives and homogeneous Schur lemma
supply the corresponding intrinsic properties of the enriched category.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem oldParityOrbit_iff (X Y : C.data.Obj) :
    Classification.SameParityOrbit C.data X Y ↔ SameParityOrbit (ofOldSupercategory C) X Y := by
  constructor
  · rintro ⟨a, f, g, hfg, hgf, hf, hg⟩
    let e : (totalForget C).obj X ≅ (totalForget C).obj Y := ⟨f, g, hfg, hgf⟩
    let e' := (totalForget C).preimageIso e
    refine ⟨a, e', (totalHomEquiv_grade C X Y e'.hom a).mpr ?_,
      (totalHomEquiv_grade C Y X e'.inv a).mpr ?_⟩
    · change (totalForget C).map ((totalForget C).preimage e.hom) ∈ _
      rw [Functor.map_preimage]
      exact hf
    · change (totalForget C).map ((totalForget C).preimage e.inv) ∈ _
      rw [Functor.map_preimage]
      exact hg
  · rintro ⟨a, e, hf, hg⟩
    let e' := (totalForget C).mapIso e
    exact ⟨a, e'.hom, e'.inv, e'.hom_inv_id, e'.inv_hom_id,
      (totalHomEquiv_grade C X Y e.hom a).mp hf,
      (totalHomEquiv_grade C Y X e.inv a).mp hg⟩

theorem ofOldFiniteSimples :
    ∃ (n : ℕ) (S : Fin n → Even (ofOldSupercategory C)),
      (∀ i, Simple (S i)) ∧ ∀ X : Even (ofOldSupercategory C), Simple X →
        ∃ i, SameParityOrbit (ofOldSupercategory C) X (S i) := by
  obtain ⟨n, S, hS, h⟩ := C.laws.finite_simple_representatives
  refine ⟨n, fun i => evenObj (ofOldSupercategory C) (S i),
    fun i => (oldSimple_iff C (S i)).mp (hS i), ?_⟩
  intro X hX
  obtain ⟨i, a, hi⟩ := h X ((oldSimple_iff C X).mpr hX)
  exact ⟨i, (oldParityOrbit_iff C X (S i)).mp ⟨a, hi⟩⟩

theorem ofOldGradedSchur (X Y : Even (ofOldSupercategory C))
    (hX : Simple X) (hY : Simple Y) (a : ZMod 2)
    (f : THom (ofOldSupercategoryData C) X Y)
    (hf : f ∈ grade (ofOldSupercategory C) X Y a) (hne : f ≠ 0) :
    @IsIso (TotalCategory (ofOldSupercategory C)) _ X Y f := by
  have hg := (totalHomEquiv_grade C X Y f a).mp hf
  have hn : totalHomEquiv C X Y f ≠ 0 := by
    intro h
    apply hne
    exact (totalHomEquiv C X Y).injective (h.trans (map_zero _).symm)
  obtain ⟨g, hfg, hgf⟩ := C.laws.graded_schur
    ((oldSimple_iff C X).mpr hX) ((oldSimple_iff C Y).mpr hY) _ hg hn
  haveI : IsIso ((totalForget C).map f) := ⟨⟨g, hfg, hgf⟩⟩
  exact isIso_of_reflects_iso f (totalForget C)

end RMod.Legacy.Hierarchy

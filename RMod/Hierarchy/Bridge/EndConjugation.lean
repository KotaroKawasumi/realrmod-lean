import RMod.Hierarchy.Bridge.EvenCategory

/-!
# Endomorphism algebra transport along even isomorphisms

Mathlib's conjugation equivalence is real linear. In the old grading its
two comparison maps are even, so conjugation preserves every degree.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy

variable {A : Type*} [Category A] [Preadditive A] [Linear ℝ A]

def endConjAlgEquiv {X Y : A} (e : X ≅ Y) : End X ≃ₐ[ℝ] End Y where
  toEquiv := e.conj.toEquiv
  map_mul' := e.conj.map_mul
  map_add' f g := by
    change e.inv ≫ (f + g) ≫ e.hom = _
    erw [Preadditive.add_comp, Preadditive.comp_add]
    rfl
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change e.inv ≫ (r • 𝟙 X) ≫ e.hom = r • 𝟙 Y
    erw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]

variable (C : WeaklyPointedSuperfusion.{0, 0})

def oldEvenTotalIso {X Y : Classification.LinearCategory C} (e : oldEvenObj C X ≅ oldEvenObj C Y) :
    X ≅ Y :=
  (wideSubcategoryInclusion (Superfusion.Category.evenMorphismProperty ℝ
    (Classification.LinearCategory C))).mapIso e

theorem oldEven_conj_grade {X Y : Classification.LinearCategory C} (e : oldEvenObj C X ≅ oldEvenObj C Y)
    (a : ZMod 2) (f : End (X : Classification.LinearCategory C))
    (hf : f ∈ Classification.LinearCategory.grade C X X a) :
    endConjAlgEquiv (oldEvenTotalIso C e) f ∈ Classification.LinearCategory.grade C Y Y a := by
  have h := C.laws.comp_grade e.inv.hom (C.data.comp f e.hom.hom) e.inv.property
    (C.laws.comp_grade f e.hom.hom hf e.hom.property)
  simp only [zero_add, add_zero] at h
  exact h

theorem oldEven_conj_grade_iff {X Y : Classification.LinearCategory C} (e : oldEvenObj C X ≅ oldEvenObj C Y)
    (a : ZMod 2) (f : End (X : Classification.LinearCategory C)) :
    endConjAlgEquiv (oldEvenTotalIso C e) f ∈ Classification.LinearCategory.grade C Y Y a ↔
      f ∈ Classification.LinearCategory.grade C X X a := by
  refine ⟨fun h => ?_, oldEven_conj_grade C e a f⟩
  have h' := oldEven_conj_grade C e.symm a _ h
  change (oldEvenTotalIso C e).symm.conj ((oldEvenTotalIso C e).conj f) ∈ _ at h'
  simpa only [Iso.symm_self_conj] using h'

end RMod.Legacy.Hierarchy

import RMod.Hierarchy.Bridge.SimpleObjects

/-!
# Raw decompositions and Mathlib biproduct isomorphisms

The old matrix equations are exactly the bicone identities. The even
linear equivalence transports their universal object, including the
chosen biproduct objects used in the new statements.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem oldDecomposition_of_evenIso (X : C.data.Obj) {n : ℕ} (S : Fin n → C.data.Obj)
    (e : oldEvenObj C X ≅ ⨁ (fun i => oldEvenObj C (S i))) : C.data.HasDecomposition X S := by
  let i (j : Fin n) := biproduct.ι (fun j => oldEvenObj C (S j)) j ≫ e.inv
  let r (j : Fin n) := e.hom ≫ biproduct.π (fun j => oldEvenObj C (S j)) j
  refine ⟨fun j => (i j).hom, fun j => (r j).hom,
    fun j => (i j).property, fun j => (r j).property, ?_, ?_, ?_⟩
  · intro j
    exact congrArg (fun f : oldEvenObj C (S j) ⟶ oldEvenObj C (S j) => f.hom)
      (show i j ≫ r j = 𝟙 _ by simp [i, r, Category.assoc])
  · intro j k hjk
    exact congrArg (fun f : oldEvenObj C (S j) ⟶ oldEvenObj C (S k) => f.hom)
      (show i j ≫ r k = 0 by simp [i, r, Category.assoc, hjk])
  · have ht : ∑ j, r j ≫ i j = 𝟙 (oldEvenObj C X) := by
      calc
        _ = e.hom ≫ (∑ j, biproduct.π (fun j => oldEvenObj C (S j)) j ≫
            biproduct.ι (fun j => oldEvenObj C (S j)) j) ≫ e.inv := by
          simp only [i, r, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = _ := by rw [biproduct.total, Category.id_comp, Iso.hom_inv_id]
    rw [Classification.LinearCategory.finSum_eq_sum C]
    let F := wideSubcategoryInclusion (Superfusion.Category.evenMorphismProperty ℝ
      (Classification.LinearCategory C))
    change (∑ j, F.map (r j ≫ i j)) = F.map (𝟙 (oldEvenObj C X))
    rw [← F.map_sum, ht]

theorem oldDecomposition_iff_evenIso (X : C.data.Obj) {n : ℕ} (S : Fin n → C.data.Obj) :
    C.data.HasDecomposition X S ↔
      Nonempty (evenObj (ofOldSupercategory C) X ≅
        ⨁ (fun j => evenObj (ofOldSupercategory C) (S j))) := by
  let S' := fun j => evenObj (ofOldSupercategory C) (S j)
  constructor
  · intro h
    obtain ⟨d⟩ := (Classification.hasDecomposition_iff C X S).mp h
    let e := biproduct.uniqueUpToIso _ d.evenIsBilimit
    exact ⟨(evenForget C).preimageIso (e ≪≫ ((evenForget C).mapBiproduct S').symm)⟩
  · rintro ⟨e⟩
    exact oldDecomposition_of_evenIso C X S
      ((evenForget C).mapIso e ≪≫ (evenForget C).mapBiproduct S')

end RMod.Legacy.Hierarchy

import RMod.Classification.Instances.HomogeneousHom

/-!
# Super-multiplicity as a homogeneous sum

The frozen weak-pointedness predicate uses separate even and odd finite
indices. Mathlib's finite-sum equivalence puts these same maps into one
homogeneous sum presentation. The parity is retained in the data and the
completeness equation is just reindexing of a finite sum.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem exists_homogeneousSum_of_superMultiplicity
    (C : WeaklyPointedSuperfusion.{0, 0}) {A X : LinearCategory C} {p q : ℕ}
    (h : C.data.HasSuperMultiplicity A X p q) :
    Nonempty (HomogeneousSum C.data X A (p + q)) := by
  obtain ⟨i, r, hi, hr, hd, ho, ht⟩ := h
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  let d : HomogeneousSumData C.data X A (p + q) :=
    { parity := fun k => WeaklyPointedSuperfusionData.superIndexParity (e k)
      inclusion := fun k => i (e k)
      projection := fun k => r (e k) }
  refine ⟨⟨d, ?_⟩⟩
  refine
    { inclusion_grade := fun k => hi (e k)
      projection_grade := fun k => hr (e k)
      diagonal := fun k => hd (e k)
      off_diagonal := fun k l hkl => ho (e k) (e l) (fun h => hkl (e.injective h))
      total := ?_ }
  change C.data.finSum (p + q) (fun k => C.data.comp (r (e k)) (i (e k))) = C.data.id A
  rw [LinearCategory.finSum_eq_sum C (X := A) (Y := A)]
  change (∑ k, r (e k) ≫ i (e k)) = 𝟙 A
  have he : (∑ k, r (e k) ≫ i (e k) : A ⟶ A) = ∑ j, r j ≫ i j :=
    e.sum_comp (fun j => (r j ≫ i j : A ⟶ A))
  rw [he, Fintype.sum_sum_type]
  dsimp only [WeaklyPointedSuperfusionData.superFinSum] at ht
  simp only [LinearCategory.finSum_eq_sum C (X := A) (Y := A)] at ht
  exact ht

end RMod.Classification

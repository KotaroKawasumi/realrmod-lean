import RMod.Classification.Proofs.ReconstructionSourceBicone

/-!
# The selected component projector acts as identity on its span

For a map from one simple-orbit component, every other component entry
vanishes by orthogonality. The total identity of the component bicone
therefore reduces to the single entry in that component. The dual
statement holds for maps into the component.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable (A : PiSuperfusion.{0, 0}) {X Z : LinearCategory A.toWeaklyPointedSuperfusion}
  (k : SimpleOrbit A.toWeaklyPointedSuperfusion)
  (hZ : InHomogeneousSpan A.toWeaklyPointedSuperfusion
    (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).data.object Z)

include hZ

theorem reconstructionComponentProjection_incoming (f : Z ⟶ X) :
    f ≫ (reconstructionSourceBicone A X).π k ≫ (reconstructionSourceBicone A X).ι k = f := by
  classical
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  let b := reconstructionSourceBicone A X
  let p : ∀ j, @Quiver.Hom (LinearCategory A.toWeaklyPointedSuperfusion) _ X
    ((reconstructionSourceEquivalence A).inverse.obj X j).obj := b.π
  let inc : ∀ j, @Quiver.Hom (LinearCategory A.toWeaklyPointedSuperfusion) _
    ((reconstructionSourceEquivalence A).inverse.obj X j).obj X := b.ι
  have ht : (∑ j, p j ≫ inc j) = 𝟙 X := IsBilimit.total (reconstructionSourceBicone_isBilimit A X)
  have hz (j : SimpleOrbit A.toWeaklyPointedSuperfusion) (hj : j ≠ k) : f ≫ p j = 0 :=
    hom_zero_of_distinct_spans A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).laws.simple
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion j).laws.simple
      (simpleOrbitRepresentatives_separate A.toWeaklyPointedSuperfusion k j hj.symm)
      hZ ((reconstructionSourceEquivalence A).inverse.obj X j).property (f ≫ p j)
  change f ≫ p k ≫ inc k = f
  calc
    _ = f ≫ ∑ j, p j ≫ inc j := by
      rw [comp_sum]
      symm
      apply Finset.sum_eq_single k
      · intro j _ hj
        rw [← Category.assoc, hz j hj, Limits.zero_comp]
      · intro hk
        exact False.elim (hk (Finset.mem_univ k))
    _ = f := by rw [ht, Category.comp_id]

theorem reconstructionComponentProjection_outgoing (f : X ⟶ Z) :
    (reconstructionSourceBicone A X).π k ≫ (reconstructionSourceBicone A X).ι k ≫ f = f := by
  classical
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  let b := reconstructionSourceBicone A X
  let p : ∀ j, @Quiver.Hom (LinearCategory A.toWeaklyPointedSuperfusion) _ X
    ((reconstructionSourceEquivalence A).inverse.obj X j).obj := b.π
  let inc : ∀ j, @Quiver.Hom (LinearCategory A.toWeaklyPointedSuperfusion) _
    ((reconstructionSourceEquivalence A).inverse.obj X j).obj X := b.ι
  have ht : (∑ j, p j ≫ inc j) = 𝟙 X := IsBilimit.total (reconstructionSourceBicone_isBilimit A X)
  have hz (j : SimpleOrbit A.toWeaklyPointedSuperfusion) (hj : j ≠ k) : inc j ≫ f = 0 :=
    hom_zero_of_distinct_spans A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion j).laws.simple
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).laws.simple
      (simpleOrbitRepresentatives_separate A.toWeaklyPointedSuperfusion j k hj)
      ((reconstructionSourceEquivalence A).inverse.obj X j).property hZ (inc j ≫ f)
  change p k ≫ inc k ≫ f = f
  calc
    _ = (∑ j, p j ≫ inc j) ≫ f := by
      rw [sum_comp]
      simp only [Category.assoc]
      symm
      apply Finset.sum_eq_single k
      · intro j _ hj
        rw [hz j hj, Limits.comp_zero]
      · intro hk
        exact False.elim (hk (Finset.mem_univ k))
    _ = f := by rw [ht, Category.id_comp]

end RMod.Classification

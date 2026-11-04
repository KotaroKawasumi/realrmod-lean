import RMod.Classification.Instances.ReconstructionSourceComponentIso
import RMod.Classification.Proofs.ReconstructionComponentProjection

/-!
# A supported object has exactly its selected component

Orthogonality kills every other selected summand. On the supported
summand, the actual inclusion and projection are inverse even maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A : PiSuperfusion.{0, 0}) (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionSourceComponentIso_even
    (hX : InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).data.object X) :
    EvenIsoLaws A.toWeaklyPointedSuperfusion.data (reconstructionSourceComponentIsoData A X k) where
  hom_inv := bicone_ι_π_self (reconstructionSourceBicone A X) k
  inv_hom := by
    have h := reconstructionComponentProjection_incoming A k hX (𝟙 X)
    rw [Category.id_comp] at h
    exact h
  hom_even := reconstructionSourceBicone_inclusion_even A X k
  inv_even := reconstructionSourceBicone_projection_even A X k

theorem reconstructionSourceComponent_id_zero
    (j : SimpleOrbit A.toWeaklyPointedSuperfusion)
    (hX : InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion j).data.object X)
    (hkj : k ≠ j) :
    A.data.id ((reconstructionSourceEquivalence A).inverse.obj X k).obj = A.data.zero := by
  have hi : (reconstructionSourceBicone A X).ι k = 0 :=
    hom_zero_of_distinct_spans A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).laws.simple
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion j).laws.simple
      (simpleOrbitRepresentatives_separate A.toWeaklyPointedSuperfusion k j hkj)
      ((reconstructionSourceEquivalence A).inverse.obj X k).property hX _
  have h := bicone_ι_π_self (reconstructionSourceBicone A X) k
  rw [hi, zero_comp] at h
  exact h.symm

theorem reconstructionUnitSource_mem :
    InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object A.data.tensorUnit := by
  have he : (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object = A.data.tensorUnit :=
    congrArg (fun S => S.data.object) (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion)
  rw [← he]
  exact (spanGenerator A.toWeaklyPointedSuperfusion _).property

end RMod.Classification

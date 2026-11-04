import RMod.Classification.Instances.ReconstructionSourceBicone
import RMod.Classification.Proofs.ReconstructionSourceEquivalence
import RMod.Classification.Proofs.BiconeTransportPoint

/-!
# The component presentation is universal and even

Its bilimit structure uses the proved full-Hom universality of the
even sum. Both directions of the selected counit are even, so the
transported component inclusions and projections are also even.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A : PiSuperfusion.{0, 0}) (X : LinearCategory A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionSourceBicone_isBilimit : (reconstructionSourceBicone A X).IsBilimit := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact biconeTransportPoint_isBilimit _ (evenBiproductFullIsBilimit _ _)
    ((reconstructionSourceEquivalence A).counitIso.app X)

theorem reconstructionSourceBicone_inclusion_even (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionSourceBicone A X).ι g) := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  have h := A.laws.comp_grade _ _
    (biproduct.ι (spanFamilyEvenObjects A.toWeaklyPointedSuperfusion _
      ((reconstructionSourceEquivalence A).inverse.obj X)) g).property
    (reconstructionSource_counit_hom_even A X)
  rw [zero_add] at h
  exact h

theorem reconstructionSourceBicone_projection_even (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionSourceBicone A X).π g) := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  have h := A.laws.comp_grade _ _ (reconstructionSource_counit_inv_even A X)
    (biproduct.π (spanFamilyEvenObjects A.toWeaklyPointedSuperfusion _
      ((reconstructionSourceEquivalence A).inverse.obj X)) g).property
  rw [zero_add] at h
  exact h

end RMod.Classification

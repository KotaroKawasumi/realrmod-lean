import RMod.Classification.Instances.ReconstructionTensorComponentBicone
import RMod.Classification.Proofs.BiconeSelectGraph
import RMod.Classification.Proofs.ReconstructionTensorBicone

/-!
# The selected tensor-component presentation is an even bilimit

Graph selection removes precisely the entries that vanish by orbit
orthogonality. Full-subcategory inclusion reflects its total identity.
All retained inclusions and projections are composites of even maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A : PiSuperfusion.{0, 0}) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
  (k : SimpleOrbit A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionTensorComponentBiconeRaw_isBilimit :
    (reconstructionTensorComponentBiconeRaw A X Y k).IsBilimit := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact biconeSelectGraph_isBilimit _ (reconstructionTensorBicone_isBilimit A X Y) _ _ _
    (reconstructionTensorProjection_graph A X Y k) (reconstructionTensorProjection_zero A X Y k)
    (bicone_ι_π_self (reconstructionSourceBicone A (A.data.tensorObj X Y)) k)

noncomputable def reconstructionTensorComponentBicone_isBilimit :
    (reconstructionTensorComponentBicone A X Y k).IsBilimit := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  apply isBilimitOfTotal
  apply ObjectProperty.hom_ext
  let F := (InHomogeneousSpan A.toWeaklyPointedSuperfusion
    (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).data.object).ι
  have hm := F.map_sum (fun g => (reconstructionTensorComponentBicone A X Y k).π g ≫
    (reconstructionTensorComponentBicone A X Y k).ι g) Finset.univ
  exact hm.trans (IsBilimit.total (reconstructionTensorComponentBiconeRaw_isBilimit A X Y k))

theorem reconstructionTensorComponentBicone_inclusion_even
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionTensorComponentBicone A X Y k).ι g).hom :=
  comp_even A.laws.toWeaklyPointedSuperfusionLaws
    (reconstructionTensorBicone_inclusion_even A X Y g (g⁻¹ * k))
    (reconstructionSourceBicone_projection_even A (A.data.tensorObj X Y) k)

theorem reconstructionTensorComponentBicone_projection_even
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionTensorComponentBicone A X Y k).π g).hom :=
  comp_even A.laws.toWeaklyPointedSuperfusionLaws
    (reconstructionSourceBicone_inclusion_even A (A.data.tensorObj X Y) k)
    (reconstructionTensorBicone_projection_even A X Y g (g⁻¹ * k))

end RMod.Classification

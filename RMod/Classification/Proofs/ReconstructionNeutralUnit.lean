import RMod.Classification.Instances.ReconstructionNeutralUnit
import RMod.Classification.Proofs.ReconstructionSourceComponentIso
import RMod.Classification.Instances.ReconstructionMappedTensorBicone

/-!
# The unit comparison is even and has no other support

The neutral maps are inverse even maps by functoriality. At any other
coordinate the selected source component is zero, and the component
equivalence preserves its zero identity.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionNeutralUnit_even :
    EvenIsoLaws C.toWeaklyPointedSuperfusion.data (reconstructionNeutralUnitData A C hC) :=
  (reconstructionUnitComparisonLaws A C hC).trans C.laws.toWeaklyPointedSuperfusionLaws
    ((reconstructionComponentEquivalence A C hC 1).forwardFunctor.mapEvenIsoLaws
      (X := spanGenerator A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object)
      (Y := (reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1)
      ((EvenIsoLaws.ofEq A.laws.toWeaklyPointedSuperfusionLaws
        (reconstructionComponentSystem A C hC).laws.source_unit).trans
        A.laws.toWeaklyPointedSuperfusionLaws
        (reconstructionSourceComponentIso_even A A.data.tensorUnit 1
          (reconstructionUnitSource_mem A)).symm))

theorem reconstructionUnitImage_id_zero (k : SimpleOrbit A.toWeaklyPointedSuperfusion)
    (hk : k ≠ 1) :
    C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj A.data.tensorUnit) k).val =
      C.data.zero := by
  let F := reconstructionComponentRealization A C hC k
  let X := (reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit k
  have hz : 𝟙 X = 0 := ObjectProperty.hom_ext _
    (reconstructionSourceComponent_id_zero A A.data.tensorUnit k 1
      (reconstructionUnitSource_mem A) hk)
  have h := congrArg F.map hz
  rw [F.map_id, F.map_zero] at h
  exact h

end RMod.Classification

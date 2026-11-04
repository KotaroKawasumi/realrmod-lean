import RMod.Classification.Instances.ReconstructionUnitSourceIso
import RMod.Classification.Proofs.ReconstructionSourceComponentIso
import RMod.Classification.Proofs.ReconstructionNeutralUnit

/-!
# The selected source-unit comparison and the retained neutral map

Its inclusion cancels the selected component projection. The global
neutral unit comparison is precisely the original component unit map
followed by the image of this same source isomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : PiSuperfusion.{0, 0})

theorem reconstructionUnitSourceIso_even :
    EvenIsoLaws A.toWeaklyPointedSuperfusion.data (reconstructionUnitSourceIsoData A) :=
  (EvenIsoLaws.ofEq A.laws.toWeaklyPointedSuperfusionLaws _).trans
    A.laws.toWeaklyPointedSuperfusionLaws
    (reconstructionSourceComponentIso_even A A.data.tensorUnit 1 (reconstructionUnitSource_mem A)).symm

theorem reconstructionUnitSourceIso_inclusion :
    A.data.comp (reconstructionUnitSourceIsoData A).hom
      ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) =
      (IsoData.ofEq A.toWeaklyPointedSuperfusion.data
        (congrArg (fun S => S.data.object)
          (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion))).hom := by
  have hc : A.data.comp ((reconstructionSourceBicone A A.data.tensorUnit).π 1)
      ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) = A.data.id A.data.tensorUnit :=
    (reconstructionSourceComponentIso_even A A.data.tensorUnit 1 (reconstructionUnitSource_mem A)).inv_hom
  change A.data.comp (A.data.comp _ ((reconstructionSourceBicone A A.data.tensorUnit).π 1))
    ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) = _
  rw [A.laws.comp_assoc, hc]
  exact A.laws.comp_id _

theorem reconstructionNeutralUnit_sourceIso (C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data) :
    reconstructionNeutralUnitData A C hC =
      (reconstructionUnitComparisonData A C hC).trans C.toWeaklyPointedSuperfusion.data
        (SpanSuperfunctor.mapIsoData (reconstructionComponentEquivalence A C hC 1).forwardFunctor.data
          (X := spanGenerator A.toWeaklyPointedSuperfusion
            (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object)
          (Y := (reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1)
          (reconstructionUnitSourceIsoData A)) := rfl

end RMod.Classification

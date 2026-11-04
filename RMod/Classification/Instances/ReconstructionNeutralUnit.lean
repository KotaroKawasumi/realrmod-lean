import RMod.Classification.Instances.ReconstructionSourceComponentIso
import RMod.Classification.Instances.ReconstructionUnderlyingEquivalence
import RMod.Classification.Instances.SpanMapIso

/-!
# The neutral coordinate of the global unit comparison

Start with the retained unit comparison of the neutral component
equivalence. Map the equality with the source unit and then its actual
component projection. This lands in the component selected by the
global reconstruction functor, including its specified inverse.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionNeutralUnitData :
    IsoData C.toWeaklyPointedSuperfusion.data C.data.tensorUnit
      (((reconstructionUnderlyingEquivalence A C hC).functor.obj A.data.tensorUnit) 1).val :=
  (reconstructionUnitComparisonData A C hC).trans C.toWeaklyPointedSuperfusion.data
    (SpanSuperfunctor.mapIsoData (reconstructionComponentEquivalence A C hC 1).forwardFunctor.data
      (X := spanGenerator A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object)
      (Y := (reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1)
      ((IsoData.ofEq A.toWeaklyPointedSuperfusion.data
        (reconstructionComponentSystem A C hC).laws.source_unit).trans
        A.toWeaklyPointedSuperfusion.data
        ((reconstructionSourceComponentIsoData A A.data.tensorUnit 1).symm
          A.toWeaklyPointedSuperfusion.data)))

end RMod.Classification

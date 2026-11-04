import RMod.Classification.Instances.ReconstructionNeutralUnit
import RMod.Classification.Proofs.PullbackObjects

/-!
# The actual global unit comparison

At the identity, use the retained neutral comparison. Every other
coordinate has the zero map in each direction. These choices define
the data before the inverse and grading laws are verified.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionUnitData (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    IsoData C.toWeaklyPointedSuperfusion.data
      (pullbackUnitObj C.data hC (reconstructionTwistData A C hC) k).val
      (((reconstructionUnderlyingEquivalence A C hC).functor.obj A.data.tensorUnit) k).val := by
  classical
  by_cases hk : k = 1
  · subst k
    exact (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
      (supportedObj_one C.data hC (reconstructionTwistData A C hC) _ _)).trans
      C.toWeaklyPointedSuperfusion.data (reconstructionNeutralUnitData A C hC)
  · exact ⟨C.data.zero, C.data.zero⟩

end RMod.Classification

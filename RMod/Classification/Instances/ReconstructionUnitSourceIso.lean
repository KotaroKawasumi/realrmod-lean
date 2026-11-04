import RMod.Classification.Instances.ReconstructionSourceComponentIso

/-!
# The actual generator-to-selected-component comparison for the source unit

Identify the normalized generator with the source unit, then project to
the component chosen by reconstruction. The inverse uses its retained
inclusion followed by the reverse equality map.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def reconstructionUnitSourceIsoData (A : PiSuperfusion.{0, 0}) :
    IsoData A.toWeaklyPointedSuperfusion.data
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object
      ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj :=
  (IsoData.ofEq A.toWeaklyPointedSuperfusion.data
    (congrArg (fun S => S.data.object)
      (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion))).trans
    A.toWeaklyPointedSuperfusion.data
    ((reconstructionSourceComponentIsoData A A.data.tensorUnit 1).symm A.toWeaklyPointedSuperfusion.data)

end RMod.Classification

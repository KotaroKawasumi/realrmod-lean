import RMod.Definitions.WeaklyPointedSuperfusionData
import Superfusion.RMod.FromRawDCT.RealCandidateWithAssociator

/-!
# Computational data of the real regular-module example

This file contains the concrete instance data only. It copies the executable
operations from the endpoint-normalized finite-coordinate construction in
Superfusion into the public `WeaklyPointedSuperfusionData` interface; no law
or proof is bundled here.
-/

set_option autoImplicit false

namespace RMod

/-- Executable finite-coordinate data of the real regular-module
superfusion category. -/
def realRModData : WeaklyPointedSuperfusionData :=
  let D := Superfusion.RMod.FromRawDCT.realEndpointCandidateData
  { Obj := D.Obj
    Hom := D.Hom
    id := D.id
    comp := D.comp
    zero := D.zero
    add := D.add
    neg := D.neg
    smul := D.smul
    grade := D.grade
    tensorObj := D.tensorObj
    tensorHom := D.tensorHom
    tensorUnit := D.tensorUnit
    associatorHom := D.associatorHom
    associatorInv := D.associatorInv
    leftUnitorHom := D.leftUnitorHom
    leftUnitorInv := D.leftUnitorInv
    rightUnitorHom := D.rightUnitorHom
    rightUnitorInv := D.rightUnitorInv }

end RMod

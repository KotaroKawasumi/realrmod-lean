import RMod.Classification.Instances.ReconstructionModelData
import RMod.Classification.Instances.ReconstructionTensorator
import RMod.Classification.Instances.ReconstructionUnit

/-!
# The specified reconstruction superequivalence data

Keep the already constructed forward and inverse functors, their actual
unit and counit, and the global tensor and unit comparisons. Coherence
and linearity are proved separately for these exact maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionMonoidalFunctorData :
    MonoidalSuperfunctorData A.data.toWeaklyPointedSuperfusionData
      (reconstructionModelData A C hC).toWeaklyPointedSuperfusionData where
  obj := (reconstructionUnderlyingEquivalence A C hC).functor.obj
  map := (reconstructionUnderlyingEquivalence A C hC).functor.map
  tensorHom X Y := fun q => (reconstructionTensoratorData A C hC X Y q).hom
  tensorInv X Y := fun q => (reconstructionTensoratorData A C hC X Y q).inv
  unitHom := fun q => (reconstructionUnitData A C hC q).hom
  unitInv := fun q => (reconstructionUnitData A C hC q).inv

noncomputable def reconstructionSuperequivalenceData :
    MonoidalSuperequivalenceData A.data.toWeaklyPointedSuperfusionData
      (reconstructionModelData A C hC).toWeaklyPointedSuperfusionData where
  forward := reconstructionMonoidalFunctorData A C hC
  backward :=
    { obj := (reconstructionUnderlyingEquivalence A C hC).inverse.obj
      map := (reconstructionUnderlyingEquivalence A C hC).inverse.map }
  unitHom := (reconstructionUnderlyingEquivalence A C hC).unitIso.hom.app
  unitInv := (reconstructionUnderlyingEquivalence A C hC).unitIso.inv.app
  counitHom := (reconstructionUnderlyingEquivalence A C hC).counitIso.hom.app
  counitInv := (reconstructionUnderlyingEquivalence A C hC).counitIso.inv.app

end RMod.Classification

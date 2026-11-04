import RMod.Classification.Instances.OmegaReplacement
import RMod.Classification.Instances.ConvolutionScalarMap

/-!
# Monoidal comparison data for a scalar change of associator

Use the identity on underlying components and maps, with the prescribed
binary scalar on each convolution summand. The unit comparison, inverse
functor, unit, and counit are componentwise identities. The cochain
identity and normalization are laws to be proved for these actual data.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (omega : t.data.group → t.data.group → t.data.group → ℝˣ)
  (h : TwistLaws (omegaReplacementData t.data omega))
  (beta : t.data.group → t.data.group → ℝˣ)

noncomputable def scalarReplacementMonoidalData :
    MonoidalSuperfunctorData (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData where
  toPrefunctor := omegaReplacementForwardData C hC t omega h
  tensorHom X Y k := (convolutionScalarData C hC t.data beta X Y k).hom
  tensorInv X Y k := (convolutionScalarData C hC t.data beta X Y k).inv
  unitHom k := C.id (pullbackUnitObj C hC t.data k).val
  unitInv k := C.id (pullbackUnitObj C hC t.data k).val

noncomputable def scalarReplacementEquivalenceData :
    MonoidalSuperequivalenceData (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData where
  forward := scalarReplacementMonoidalData C hC t omega h beta
  backward := omegaReplacementBackwardData C hC t omega h
  unitHom X k := C.id (X k).val
  unitInv X k := C.id (X k).val
  counitHom Y k := C.id (Y k).val
  counitInv Y k := C.id (Y k).val

end RMod.Classification

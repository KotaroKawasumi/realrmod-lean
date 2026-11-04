import RMod.Classification.Abstract.SimpleRetract
import RMod.Classification.Instances.SimpleTensorRepresentative

/-!
# Retaining the simple retract used for a product component

The selected tensor-product constituent already has an even inclusion
and projection in its chosen simple decomposition. Retain those maps,
and their inverse identity, with the same simple representative used
for the intrinsic group multiplication.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (S T : SimpleObject C)

noncomputable def tensorSimpleRetractData :
    SimpleRetractData C.data (C.data.tensorObj S.data.object T.data.object) where
  toSimpleObjectData := simpleTensorRepresentativeData C S T
  inclusion := (simpleDecomposition C _).data.decomposition.inclusion (tensorSimpleIndex C S T)
  projection := (simpleDecomposition C _).data.decomposition.projection (tensorSimpleIndex C S T)

theorem tensorSimpleRetractLaws : SimpleRetractLaws (tensorSimpleRetractData C S T) where
  toSimpleObjectLaws := simpleTensorRepresentativeLaws C S T
  inclusion_projection := (simpleDecomposition C _).laws.decomposition.diagonal (tensorSimpleIndex C S T)
  inclusion_even := (simpleDecomposition C _).laws.decomposition.inclusion_even (tensorSimpleIndex C S T)
  projection_even := (simpleDecomposition C _).laws.decomposition.projection_even (tensorSimpleIndex C S T)

noncomputable def tensorSimpleRetract :
    SimpleRetract C (C.data.tensorObj S.data.object T.data.object) :=
  ⟨tensorSimpleRetractData C S T, tensorSimpleRetractLaws C S T⟩

end RMod.Classification

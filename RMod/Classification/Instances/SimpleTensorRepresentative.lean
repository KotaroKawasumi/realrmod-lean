import RMod.Classification.Abstract.SimpleObjects
import RMod.Classification.Proofs.SimpleDecomposition
import RMod.Classification.Proofs.TensorNonvanishing

/-!
# Selecting a simple constituent of the tensor product

The tensor product of two simples is nonzero. Its chosen simple
decomposition therefore has a first summand. This specified object is
the representative used to define multiplication of intrinsic orbits;
independence from representatives is a separate theorem.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : SimpleObject C)

def tensorSimpleIndex :
    Fin (simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)).data.size :=
  ⟨0, (simpleDecomposition C _).size_pos
    (tensor_id_ne_zero (C := C) (simple_id_ne_zero C.laws X.laws.simple)
      (simple_id_ne_zero C.laws Y.laws.simple))⟩

noncomputable def simpleTensorRepresentativeData : SimpleObjectData C.data :=
  ⟨(simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)).data.summand
    (tensorSimpleIndex C X Y)⟩

theorem simpleTensorRepresentativeLaws : SimpleObjectLaws C.data (simpleTensorRepresentativeData C X Y) :=
  ⟨(simpleDecomposition C _).laws.simple (tensorSimpleIndex C X Y)⟩

noncomputable def simpleTensorRepresentative : SimpleObject C :=
  ⟨simpleTensorRepresentativeData C X Y, simpleTensorRepresentativeLaws C X Y⟩

end RMod.Classification

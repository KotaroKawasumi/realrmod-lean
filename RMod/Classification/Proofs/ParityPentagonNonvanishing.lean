import RMod.Classification.Proofs.ParityFactorIso
import RMod.Classification.Proofs.TensorNonvanishing

/-!
# Nonvanishing of the source of the parity pentagon

A tensor product of nonzero objects is nonzero, and adjoining a parity
factor is a homogeneous isomorphism. Iterating these two proved facts
provides the scalar-faithfulness hypothesis for reconstruction generators.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

theorem parityPentagon_source_id_ne_zero (W X Y Z : C.data.Obj) (a b t : ZMod 2)
    (hW : C.data.id W ≠ C.data.zero) (hX : C.data.id X ≠ C.data.zero)
    (hY : C.data.id Y ≠ C.data.zero) (hZ : C.data.id Z ≠ C.data.zero) :
    C.data.id (C.data.tensorObj (C.data.tensorObj
      (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj W X) (p.factor a)) Y)
        (p.factor b)) Z) (p.factor t)) ≠ C.data.zero :=
  right_factor_id_ne_zero C p hp _ t (tensor_id_ne_zero
    (right_factor_id_ne_zero C p hp _ b (tensor_id_ne_zero
      (right_factor_id_ne_zero C p hp _ a (tensor_id_ne_zero hW hX)) hY)) hZ)

end RMod.Classification

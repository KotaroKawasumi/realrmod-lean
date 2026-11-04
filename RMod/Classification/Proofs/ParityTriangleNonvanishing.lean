import RMod.Classification.Proofs.WeightedTriangleNecessity
import RMod.Classification.Proofs.ParityFactorIso
import RMod.Classification.Proofs.TensorNonvanishing

/-!
# The unweighted triangle route is nonzero

Its second route is a tensor product of unit isomorphisms and identities.
Tensor nonvanishing and invertibility of parity factors make its source
nonzero whenever the two component objects are nonzero.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

theorem parityTriangle_right_ne_zero (X Y : C.data.Obj) (a : ZMod 2)
    (hX : C.data.id X ≠ C.data.zero) (hY : C.data.id Y ≠ C.data.zero) :
    C.data.tensorHom
      (C.data.tensorHom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit))
          (C.data.rightUnitorHom X)) (C.data.id Y)) (C.data.id (p.factor a)) ≠ C.data.zero := by
  have hu := simple_id_ne_zero C.laws C.laws.simple_unit
  have hi := (((EvenIsoLaws.rightUnit C.laws (C.data.tensorObj X C.data.tensorUnit)).trans C.laws
    (EvenIsoLaws.rightUnit C.laws X)).tensor C.laws (EvenIsoLaws.refl C.laws Y)).tensor C.laws
      (EvenIsoLaws.refl C.laws (p.factor a))
  exact iso_hom_ne_zero C hi.toIsoLaws
    (right_factor_id_ne_zero C p hp _ a (tensor_id_ne_zero
      (tensor_id_ne_zero (tensor_id_ne_zero hX hu) hu) hY))

end RMod.Classification

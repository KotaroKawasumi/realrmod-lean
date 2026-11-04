import RMod.Classification.Instances.DualAdjunctions
import RMod.Classification.Proofs.AdjunctionGrading

/-!
# Even units and counits of the dual adjunctions

Their formulas involve only the even coevaluation, evaluation, identities
and coherence maps. The full Hom equivalences consequently preserve and
reflect parity, including the odd component.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.DualPairing

variable {C : WeaklyPointedSuperfusion.{u, v}} {X Y : C.data.Obj} (p : DualPairing C X Y)

theorem rightAdjunction_unit_even (Z : LinearCategory C) :
    C.data.IsHomogeneous 0 (p.rightAdjunction.unit.app Z) :=
  comp_even C.laws (C.laws.right_unitor_inv_even Z)
    (comp_even C.laws (tensor_even C.laws (C.laws.id_even Z) p.laws.coeval_even)
      (C.laws.associator_inv_even Z X Y))

theorem rightAdjunction_counit_even (Z : LinearCategory C) :
    C.data.IsHomogeneous 0 (p.rightAdjunction.counit.app Z) :=
  comp_even C.laws (C.laws.associator_hom_even Z Y X)
    (comp_even C.laws (tensor_even C.laws (C.laws.id_even Z) p.laws.eval_even)
      (C.laws.right_unitor_hom_even Z))

theorem leftAdjunction_unit_even (Z : LinearCategory C) :
    C.data.IsHomogeneous 0 (p.leftAdjunction.unit.app Z) :=
  comp_even C.laws (C.laws.left_unitor_inv_even Z)
    (comp_even C.laws (tensor_even C.laws p.laws.coeval_even (C.laws.id_even Z))
      (C.laws.associator_hom_even X Y Z))

theorem leftAdjunction_counit_even (Z : LinearCategory C) :
    C.data.IsHomogeneous 0 (p.leftAdjunction.counit.app Z) :=
  comp_even C.laws (C.laws.associator_inv_even Y X Z)
    (comp_even C.laws (tensor_even C.laws p.laws.eval_even (C.laws.id_even Z))
      (C.laws.left_unitor_hom_even Z))

end RMod.Classification.DualPairing

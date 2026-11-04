import RMod.Classification.Proofs.WeightedDualSnake

/-!
# Closing the local first snake with the actual unit comparisons

The outer right-unit factor is retained by convolution. Naturality of
that unitor removes it from the proved weighted snake, and the remaining
left and right unit inverse laws give the identity of X.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

theorem normalizedLocal_first_snake {X Y : C.data.Obj} (q : DualPairing C X Y) (a : ZMod 2) (ω : ℝˣ) :
    C.data.comp
      (C.data.comp (C.data.leftUnitorInv X) (C.data.rightUnitorInv (C.data.tensorObj C.data.tensorUnit X)))
      (C.data.comp
        (C.data.comp
          (C.data.comp
            (C.data.tensorHom (C.data.tensorHom (p.twistedCoevaluation q.data a) (C.data.id X))
              (C.data.id C.data.tensorUnit))
            (p.localAssociator X (C.data.tensorObj Y (p.factor a)) X a 0 a 0 rfl ω).hom)
          (C.data.tensorHom (C.data.tensorHom (C.data.id X) (p.twistedEvaluation q.data a ω))
            (C.data.id C.data.tensorUnit)))
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit)) (C.data.rightUnitorHom X))) =
      C.data.id X := by
  rw [localAssociator_weighted_first_snake C p hp q a ω]
  let f := C.data.comp (C.data.leftUnitorHom X) (C.data.rightUnitorInv X)
  have hn := C.laws.right_unitor_naturality f
  change C.data.comp (C.data.comp (C.data.leftUnitorInv X)
      (C.data.rightUnitorInv (C.data.tensorObj C.data.tensorUnit X)))
    (C.data.comp (C.data.tensorHom f (C.data.id C.data.tensorUnit))
      (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit))
        (C.data.rightUnitorHom X))) = _
  simp only [C.laws.comp_assoc]
  rw [← C.laws.comp_assoc (C.data.tensorHom f (C.data.id C.data.tensorUnit))
    (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit)), hn]
  simp only [C.laws.comp_assoc]
  rw [← C.laws.comp_assoc (C.data.rightUnitorInv (C.data.tensorObj C.data.tensorUnit X))
    (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit X)),
    C.laws.right_unitor_inv_hom, C.laws.id_comp]
  dsimp only [f]
  rw [C.laws.comp_assoc, C.laws.right_unitor_inv_hom, C.laws.comp_id, C.laws.left_unitor_inv_hom]

end RMod.Classification

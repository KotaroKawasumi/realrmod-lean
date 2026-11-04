import RMod.Classification.Proofs.DualMateCancellation
import RMod.Classification.Instances.Duals

/-!
# Nonvanishing of both members of an exact pairing

The mate of the identity is the identity of the dual. Mate cancellation
therefore transfers nonvanishing in either direction, without a separate
simplicity assumption on the chosen dual object.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.DualPairing

open CategoryTheory Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{u, v}} {X Y : C.data.Obj} (q : DualPairing C X Y)

include q

theorem left_id_ne_zero (hY : C.data.id Y ≠ C.data.zero) : C.data.id X ≠ C.data.zero := by
  let X' := evenObj ℝ (LinearCategory C) X
  let Y' := evenObj ℝ (LinearCategory C) Y
  letI : HasLeftDual Y' := { leftDual := X', exact := q.toEvenPairing }
  have hY' : 𝟙 Y' ≠ 0 := fun he => hY (congrArg (fun f => f.hom) he)
  have h := DualMate.left_mate_ne_zero hY'
  intro hz
  apply h
  rw [leftAdjointMate_id]
  exact WideSubcategory.hom_ext _ hz

theorem right_id_ne_zero (hX : C.data.id X ≠ C.data.zero) : C.data.id Y ≠ C.data.zero := by
  let X' := evenObj ℝ (LinearCategory C) X
  let Y' := evenObj ℝ (LinearCategory C) Y
  letI : HasRightDual X' := { rightDual := Y', exact := q.toEvenPairing }
  have hX' : 𝟙 X' ≠ 0 := fun he => hX (congrArg (fun f => f.hom) he)
  have h := DualMate.right_mate_ne_zero hX'
  intro hz
  apply h
  rw [rightAdjointMate_id]
  exact WideSubcategory.hom_ext _ hz

end RMod.Classification.DualPairing

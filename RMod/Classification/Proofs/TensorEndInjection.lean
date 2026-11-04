import RMod.Classification.Proofs.EndSlices
import RMod.Classification.Proofs.TensorSlices

/-!
# Injectivity of tensoring endomorphisms

Choose a left dual of X. The perfect split-unit pairing realizes each real
functional on End(X) as a cap, and the slice formula detects its coefficient
in every pure tensor. Mathlib's tensor basis argument then kills the whole
kernel. Neither P nor the weak-pointed dimension calculation is used here.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem tensorEndLinear_injective (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : C.data.Obj) :
    Function.Injective (tensorEndLinear C X Y) := by
  apply tensor_lift_injective_of_slices (tensorEndBilinear C X Y)
  intro φ
  let p := (dualChoices C).leftPairing X
  exact ⟨p.endSlice Y φ, p.endSlice_tensor Y φ⟩

end RMod.Classification

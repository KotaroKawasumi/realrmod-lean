import RMod.Classification.Proofs.ReconstructionOmegaNormalization

/-!
# The completed reconstructed classification parameter

Bundle the previously constructed data with normalization, the parity
cocycle, and the signed scalar pentagon proved for those exact data.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionTwistLaws : TwistLaws (reconstructionTwistData A C hC) where
  nu_one_left := reconstructionNu_one_left A C hC
  nu_one_right := reconstructionNu_one_right A C hC
  omega_one₁ := reconstructionOmega_one_left A C hC
  omega_one₂ := reconstructionOmega_one_middle A C hC
  omega_one₃ := reconstructionOmega_one_right A C hC
  cocycle := reconstructionNu_cocycle A C hC
  pentagon := reconstructionOmega_pentagon A C hC

noncomputable def reconstructionTwist : Twist where
  data := reconstructionTwistData A C hC
  laws := reconstructionTwistLaws A C hC

end RMod.Classification

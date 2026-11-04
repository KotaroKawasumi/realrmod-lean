import RMod.Classification.Proofs.ConvolutionPentagonReflection
import RMod.Classification.Proofs.ConvolutionBlockPentagonNecessity
import RMod.Classification.Proofs.PullbackNonzeroFamily

/-!
# The convolution pentagon implies its fermionic parameter equation

Test the actual pentagon on a family nonzero in every degree. Restriction
to the summand of four specified degrees yields its local weighted
pentagon. Scalar faithfulness recovers exactly the signed equation.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem convolution_pentagon_forces_scalar (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : TwistData)
    (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
    (hp : ∀ (W X Y Z : PullbackObj C t) (K : t.group),
      convolutionPentagonThreeOfParity C hC t hν W X Y Z K =
        convolutionPentagonTwoOfParity C hC t hν W X Y Z K)
    (g h k l : t.group) :
    t.omega h k l * t.omega g (h * k) l * t.omega g h k =
      realSign (t.nu g h * t.nu k l) *
        (t.omega (g * h) k l * t.omega g h (k * l)) := by
  obtain ⟨V, hV⟩ := pullback_exists_nonzero_family C hC t
  have hb := convolutionBlockPentagon_heq_of_eq C hC t hν V V V V (g * (h * (k * l))) g h k
    (hp V V V V _)
  have hs := convolutionBlockPentagon_scalar_of_heq C hC t hν V V V V (g * (h * (k * l))) g h k
    (hV g) (hV h) (hV k) (hV _) hb
  simpa only [inv_mul_cancel_left] using hs

end RMod.Classification

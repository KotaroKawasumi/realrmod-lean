import RMod.Classification.Proofs.ReconstructionModelCoherence
import RMod.Classification.Proofs.ConvolutionPentagonNecessity

/-!
# The extracted reconstruction scalar satisfies the signed pentagon

Coherence of the specified reconstruction model was transported from the
original category without scalar hypotheses. Applying the converse for
convolution now proves the fermionic equation for the extracted omega.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstructionOmega_pentagon (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (g h k l : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    let t := reconstructionTwistData A C hC
    t.omega h k l * t.omega g (h * k) l * t.omega g h k =
      realSign (t.nu g h * t.nu k l) *
        (t.omega (g * h) k l * t.omega g h (k * l)) :=
  convolution_pentagon_forces_scalar C.data hC (reconstructionTwistData A C hC)
    (reconstruction_normalizer_parity A C hC)
    (fun W X Y Z K => congrFun (reconstructionModel_pentagon A C hC W X Y Z) K) g h k l

end RMod.Classification

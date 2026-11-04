import RMod.Classification.Proofs.ReconstructionOmegaPentagon
import RMod.Classification.Proofs.ConvolutionTriangleNecessity
import RMod.Classification.Proofs.TwistNormalizationFromMiddle

/-!
# Normalization of the extracted associator scalar

The actual transported triangle, tested on nonzero component objects,
forces the middle normalization. The other two normalizations follow
from this case and the already proved signed pentagon.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionOmega_one_middle (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionTwistData A C hC).omega g 1 h = 1 := by
  let t := reconstructionTwistData A C hC
  let K : SimpleOrbit A.toWeaklyPointedSuperfusion := g * h
  let a : SimpleOrbit A.toWeaklyPointedSuperfusion := g * 1
  obtain ⟨V, hV⟩ := pullback_exists_nonzero_family C.data hC t
  have he := congrFun (reconstructionModel_triangle A C hC V V) (g * h)
  have hs := convolutionTriangle_scalar_of_summand_eq C.data hC t
    (reconstruction_normalizer_parity A C hC)
    (reconstructionNu_one_left A C hC) (reconstructionNu_one_right A C hC)
    V V (g * h) g (hV g) (hV _)
    (congrArg (C.data.comp
      (convolutionLeftInsertionEven C.data hC t V (pullbackUnitObj C.data hC t) V
        K a g).hom) he)
  change (reconstructionTwistData A C hC).omega g 1 (g⁻¹ * (g * h)) = 1 at hs
  simpa only [inv_mul_cancel_left] using hs

theorem reconstructionOmega_one_left (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionTwistData A C hC).omega 1 g h = 1 :=
  omega_one_left_of_middle_pentagon (reconstructionTwistData A C hC)
    (reconstructionNu_one_left A C hC 1) (reconstructionOmega_one_middle A C hC)
    (reconstructionOmega_pentagon A C hC) g h

theorem reconstructionOmega_one_right (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionTwistData A C hC).omega g h 1 = 1 :=
  omega_one_right_of_middle_pentagon (reconstructionTwistData A C hC)
    (reconstructionNu_one_left A C hC 1) (reconstructionOmega_one_middle A C hC)
    (reconstructionOmega_pentagon A C hC) g h

end RMod.Classification

import RMod.Classification.Instances.GaugeProductTriple
import RMod.Classification.Proofs.ConvolutionIndexedProducts

/-!
# Source gauge insertions are the transported original product insertions

Their output degrees are the inverse images of target products. The
group isomorphism supplies precisely the equalities needed by the
indexed product interface, without changing any convolution object.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data)

theorem gaugeProductBaseInclusion_eq_indexed (X Y : PullbackObj C s.data) (g h : t.data.group) :
    gaugeProductBaseInclusion C hC s t d X Y g h =
      convolutionIndexedProductInclusion C hC s.data X Y
        (d.phi.symm g) (d.phi.symm h) (d.phi.symm (g * h)) (map_mul d.phi.symm g h).symm :=
  (convolutionIndexedProductInclusion_eq C hC s.data X Y
    (d.phi.symm g) (d.phi.symm h) (d.phi.symm (g * h)) (map_mul d.phi.symm g h).symm
    (gaugeProductComplement d g h)).symm

theorem gaugeProductLeftSourceInsertion_eq_indexed (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    gaugeProductLeftSourceInsertion C hC s t d X Y Z g h k =
      C.tensorHom (convolutionIndexedLeftInsertion C hC s.data X Y Z
        (d.phi.symm g) (d.phi.symm h) (d.phi.symm k) (d.phi.symm (g * h)) (d.phi.symm ((g * h) * k))
        (map_mul d.phi.symm g h).symm (map_mul d.phi.symm (g * h) k).symm)
        (C.id (C.pi.factor (d.lam (d.phi.symm ((g * h) * k))))) := by
  simp only [gaugeProductLeftSourceInsertion, gaugeProductBaseInclusion_eq_indexed,
    convolutionIndexedLeftInsertion]

theorem gaugeProductRightSourceInsertion_eq_indexed (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    gaugeProductRightSourceInsertion C hC s t d X Y Z g h k =
      C.tensorHom (convolutionIndexedRightInsertion C hC s.data X Y Z
        (d.phi.symm g) (d.phi.symm h) (d.phi.symm k) (d.phi.symm (h * k)) (d.phi.symm (g * (h * k)))
        (map_mul d.phi.symm h k).symm (map_mul d.phi.symm g (h * k)).symm)
        (C.id (C.pi.factor (d.lam (d.phi.symm (g * (h * k)))))) := by
  simp only [gaugeProductRightSourceInsertion, gaugeProductBaseInclusion_eq_indexed,
    convolutionIndexedRightInsertion]

end RMod.Classification

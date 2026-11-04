import RMod.Classification.Abstract.Pullback
import RMod.Classification.Proofs.TensorTypes
import RMod.Classification.Proofs.UnitComponent

/-!
# Components of the actual twisted convolution summands

Both parity factors lie in the neutral component. Tensor closure and the
given group homomorphism therefore place each right-parity-normalized
summand in component rho(g h). No multiplication table for the concrete
reference category is used in the construction.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem InComponent.parity_factor {C : PiSuperfusionData.{0, 0}}
    (hC : ReferenceProperty C) (a : ZMod 2) :
    InComponent C.toWeaklyPointedSuperfusionData 0 (C.pi.factor a) := by
  unfold PiData.factor
  split_ifs
  · exact InComponent.tensor_unit hC
  · exact InComponent.parity_object hC

theorem twistSummand_inComponent (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)
    (t : TwistData) (X Y : PullbackObj C t) (g h : t.group) :
    InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho (g * h)))
      (twistSummand C t X Y g h) := by
  have hh := InComponent.tensor hC (InComponent.tensor hC (X g).property (Y h).property)
    (InComponent.parity_factor hC (t.nu g h))
  simpa only [twistSummand, map_mul, toAdd_mul, add_zero] using hh

end RMod.Classification

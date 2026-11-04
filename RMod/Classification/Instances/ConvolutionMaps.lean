import RMod.Classification.Instances.ConvolutionObjects
import RMod.Classification.Proofs.BiproductMap

/-!
# Convolution on morphisms

In each output degree, tensor the two input component maps with the
identity of the specified right parity factor, then take the map of the
chosen finite sums. The formula uses only C's maps and finite sums.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionSum (X Y : PullbackObj C t) (k : t.group) :
    Biproduct C (convolutionFamily C t X Y k) :=
  ⟨(finiteSumsData C hC.toWeaklyPointedSuperfusionLaws).sum (convolutionFamily C t X Y k),
    (finiteSumsLaws C hC.toWeaklyPointedSuperfusionLaws).sum (convolutionFamily C t X Y k)⟩

noncomputable def convolutionHom {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') :
    PullbackHom C t (convolutionObj C hC t X Y) (convolutionObj C hC t X' Y') := fun k =>
  (convolutionSum C hC t X Y k).data.mapHom (convolutionSum C hC t X' Y' k).data
    (fun i => twistSummandHom C t f g (groupEnumeration t i) ((groupEnumeration t i)⁻¹ * k))

end RMod.Classification

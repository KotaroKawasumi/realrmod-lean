import RMod.Classification.Instances.ConvolutionTripleInsertions

/-!
# Maps of the uncontracted triple summands

These are the two parenthesizations of three arbitrary component maps,
with identities on the prescribed parity factors. No parity assumption
on the component maps is needed to define either expression.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  {X X' Y Y' Z Z' : PullbackObj C t}

def convolutionLeftBlockHom (f : PullbackHom C t X X') (g : PullbackHom C t Y Y')
    (h : PullbackHom C t Z Z') (k a b : t.group) :
    C.Hom (convolutionLeftFamily C hC t X Y Z k a b).obj
      (convolutionLeftFamily C hC t X' Y' Z' k a b).obj :=
  C.tensorHom (C.tensorHom (twistSummandHom C t f g b (b⁻¹ * a)) (h (a⁻¹ * k)))
    (C.id (C.pi.factor (t.nu a (a⁻¹ * k))))

def convolutionRightBlockHom (f : PullbackHom C t X X') (g : PullbackHom C t Y Y')
    (h : PullbackHom C t Z Z') (k a b : t.group) :
    C.Hom (convolutionRightFamily C hC t X Y Z k a b).obj
      (convolutionRightFamily C hC t X' Y' Z' k a b).obj :=
  C.tensorHom (C.tensorHom (f a) (twistSummandHom C t g h b (b⁻¹ * (a⁻¹ * k))))
    (C.id (C.pi.factor (t.nu a (a⁻¹ * k))))

end RMod.Classification

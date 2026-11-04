import RMod.Classification.Instances.ConvolutionProductInsertions

/-!
# Product insertions with an explicitly identified output degree

The original product inclusion is followed by its output equality map.
Nested inclusions permit an intermediate product degree to be supplied
with its equality witness. No sum or structural morphism is reselected.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionIndexedProductInclusion (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u) :
    C.Hom (twistSummand C t X Y g h) (convolutionObj C hC t X Y u).val :=
  C.comp (convolutionProductInclusion C hC t X Y g h)
    (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (congrArg (fun j => (convolutionObj C hC t X Y j).val) e)).hom

noncomputable def convolutionIndexedLeftInsertion (X Y Z : PullbackObj C t)
    (g h k u w : t.group) (eu : g * h = u) (ew : u * k = w) :
    C.Hom (C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z k).val)
      (C.pi.factor (t.nu u k)))
      (convolutionObj C hC t (convolutionObj C hC t X Y) Z w).val :=
  C.comp (C.tensorHom (C.tensorHom (convolutionIndexedProductInclusion C hC t X Y g h u eu)
    (C.id (Z k).val)) (C.id (C.pi.factor (t.nu u k))))
    (convolutionIndexedProductInclusion C hC t (convolutionObj C hC t X Y) Z u k w ew)

noncomputable def convolutionIndexedRightInsertion (X Y Z : PullbackObj C t)
    (g h k v w : t.group) (ev : h * k = v) (ew : g * v = w) :
    C.Hom (C.tensorObj (C.tensorObj (X g).val (twistSummand C t Y Z h k))
      (C.pi.factor (t.nu g v)))
      (convolutionObj C hC t X (convolutionObj C hC t Y Z) w).val :=
  C.comp (C.tensorHom (C.tensorHom (C.id (X g).val)
    (convolutionIndexedProductInclusion C hC t Y Z h k v ev)) (C.id (C.pi.factor (t.nu g v))))
    (convolutionIndexedProductInclusion C hC t X (convolutionObj C hC t Y Z) g v w ew)

end RMod.Classification

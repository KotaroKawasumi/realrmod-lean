import RMod.Classification.Instances.ConvolutionIndexedProducts
import RMod.Classification.Proofs.ConvolutionProductAssociator

/-!
# Associator comparison on insertions with transported product degrees

Equality elimination reduces the intermediate and final output degrees
to the original product-indexed insertion theorem. The arbitrary
normalizer parity proof and output transport proof are retained; proof
irrelevance identifies them with the supplied cocycle and associativity.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionIndexedProductInclusion_eq (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u) (ec : h = g⁻¹ * u) :
    convolutionIndexedProductInclusion C hC t X Y g h u e =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg (twistSummand C t X Y g) ec)).hom (convolutionInclusion C hC t X Y u g) := by
  cases e
  change C.comp (convolutionProductInclusion C hC t X Y g h) (C.id _) = _
  rw [hC.comp_id]
  rfl

theorem convolutionIndexedInsertion_associator
    (hnu : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
    (X Y Z : PullbackObj C t) (g h k u v w w' : t.group)
    (eu : g * h = u) (ev : h * k = v) (ew : u * k = w) (ew' : g * v = w')
    (eo : w = w') (ep : t.nu g h + t.nu u k = t.nu h k + t.nu g v) :
    C.comp (C.comp (convolutionIndexedLeftInsertion C hC t X Y Z g h k u w eu ew)
      (convolutionAssociatorDataOfParity C hC t hnu X Y Z w).hom)
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg (fun j => (convolutionObj C hC t X (convolutionObj C hC t Y Z) j).val) eo)).hom =
      C.comp (C.pi.localAssociator (X g).val (Y h).val (Z k).val
        (t.nu g h) (t.nu u k) (t.nu h k) (t.nu g v) ep (t.omega g h k)).hom
        (convolutionIndexedRightInsertion C hC t X Y Z g h k v w' ev ew') := by
  cases eu
  cases ev
  cases ew
  cases ew'
  simp only [convolutionIndexedLeftInsertion, convolutionIndexedRightInsertion,
    convolutionIndexedProductInclusion, IsoData.ofEq, IsoData.refl, hC.comp_id]
  exact convolutionProductInsertion_associator C hC t hnu X Y Z g h k

end RMod.Classification

import RMod.Classification.Proofs.ConvolutionIndexedComparisons

/-!
# Supported triple inclusions can be cancelled

Both binary summand inclusions are even isomorphisms when the first two
inputs have their indicated supports. Their explicit tensor and composite
inverses therefore cancel the actual left triple insertion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

theorem convolutionIndexedLeftInsertion_cancel
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
    (X Y Z : PullbackObj C t) (g h k u w : t.group) (eu : g * h = u) (ew : u * k = w)
    (hX : ∀ l, l ≠ g → C.id (X l).val = C.zero)
    (hY : ∀ l, l ≠ h → C.id (Y l).val = C.zero)
    {V : C.Obj} {f q : C.Hom (convolutionObj C hC t (convolutionObj C hC t X Y) Z w).val V}
    (he : C.comp (convolutionIndexedLeftInsertion C hC t X Y Z g h k u w eu ew) f =
      C.comp (convolutionIndexedLeftInsertion C hC t X Y Z g h k u w eu ew) q) : f = q := by
  have hXY : ∀ l, l ≠ u → C.id (convolutionObj C hC t X Y l).val = C.zero :=
    fun l hl => convolution_support C hC t g h hX hY l (fun e => hl (e.trans eu))
  let i := (((convolutionIndexedInclusionData C hC t X Y g h u eu).tensor
    C.toWeaklyPointedSuperfusionData (IsoData.refl C.toWeaklyPointedSuperfusionData (Z k).val)).tensor
      C.toWeaklyPointedSuperfusionData (IsoData.refl C.toWeaklyPointedSuperfusionData
        (C.pi.factor (t.nu u k)))).trans C.toWeaklyPointedSuperfusionData
          (convolutionIndexedInclusionData C hC t (convolutionObj C hC t X Y) Z u k w ew)
  have hi : EvenIsoLaws C.toWeaklyPointedSuperfusionData i :=
    (((convolutionIndexedInclusion_evenIso C hC t X Y g h u eu hX).tensor
      hC.toWeaklyPointedSuperfusionLaws (EvenIsoLaws.refl hC.toWeaklyPointedSuperfusionLaws (Z k).val)).tensor
        hC.toWeaklyPointedSuperfusionLaws
        (EvenIsoLaws.refl hC.toWeaklyPointedSuperfusionLaws (C.pi.factor (t.nu u k)))).trans
          hC.toWeaklyPointedSuperfusionLaws
          (convolutionIndexedInclusion_evenIso C hC t (convolutionObj C hC t X Y) Z u k w ew hXY)
  have hh : i.hom = convolutionIndexedLeftInsertion C hC t X Y Z g h k u w eu ew := by
    simp only [i, IsoData.trans, IsoData.tensor, IsoData.refl,
      convolutionIndexedInclusionData_hom, convolutionIndexedLeftInsertion]
  rw [← hh] at he
  have hc := congrArg (fun z => C.comp i.inv z) he
  simpa only [← hC.comp_assoc, hi.inv_hom, hC.id_comp] using hc

end RMod.Classification

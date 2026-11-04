import RMod.Classification.Proofs.ConvolutionIndexedTripleComparisons
import RMod.Classification.Proofs.ConvolutionIndexedCancellation

/-!
# The raw triple scalar of the actual convolution associator

On supported families, insert the actual triple summand and use the
specified associator block. The binary comparisons reduce to outer-first
parity deletion; cancellation of the even inclusion gives the complete
evaluation identity. Its coefficient includes both deletion-order signs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

theorem convolutionIndexedComparison_associator
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
    (hnu : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
    (X Y Z : PullbackObj C t) (g h k u v w w' : t.group)
    (eu : g * h = u) (ev : h * k = v) (ew : u * k = w) (ew' : g * v = w')
    (eo : w = w') (ep : t.nu g h + t.nu u k = t.nu h k + t.nu g v)
    (hX : ∀ l, l ≠ g → C.id (X l).val = C.zero)
    (hY : ∀ l, l ≠ h → C.id (Y l).val = C.zero) :
    C.comp (C.comp (convolutionAssociatorDataOfParity C hC t hnu X Y Z w).hom
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg (fun j => (convolutionObj C hC t X (convolutionObj C hC t Y Z) j).val) eo)).hom)
      (convolutionIndexedRightComparisonData C hC t X Y Z g h k v w' ev ew').hom =
      C.smul ((t.omega g h k).val * (-1 : ℝ) ^
        (t.nu g h * t.nu u k + t.nu h k * t.nu g v).val)
        (convolutionIndexedLeftComparisonData C hC t X Y Z g h k u w eu ew).hom := by
  apply convolutionIndexedLeftInsertion_cancel C hC t X Y Z g h k u w eu ew hX hY
  have ha := convolutionIndexedInsertion_associator C hC t hnu X Y Z g h k u v w w'
    eu ev ew ew' eo ep
  have hd := hC.pi.localAssociator_outerDeletion hC.toWeaklyPointedSuperfusionLaws
    (X g).val (Y h).val (Z k).val (t.nu g h) (t.nu u k) (t.nu h k) (t.nu g v) ep (t.omega g h k)
  rw [← hC.comp_assoc, ← hC.comp_assoc, ha, hC.comp_assoc,
    convolutionIndexedRightComparison_inclusion, ← hC.comp_assoc _ _
      (C.associatorInv (X g).val (Y h).val (Z k).val), ← hC.comp_assoc]
  refine (congrArg (fun z => C.comp z
    (C.associatorInv (X g).val (Y h).val (Z k).val)) hd).trans ?_
  rw [hC.smul_comp, hC.comp_assoc, hC.comp_assoc, hC.associator_hom_inv, hC.comp_id,
    hC.comp_smul, convolutionIndexedLeftComparison_inclusion]
  rfl

end RMod.Classification

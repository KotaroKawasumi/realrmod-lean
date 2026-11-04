import RMod.Classification.Instances.ConvolutionAssociatorOfParity
import RMod.Classification.Proofs.ConvolutionExpansion
import Batteries.Tactic.GeneralizeProofs

/-!
# The actual associator on an individual threefold summand

The reindexing of the middle biproduct takes `(g*h,g)` to `(g,h)`.
Its block is precisely the selected local associator. Cancelling the
expansion comparisons then gives the corresponding equation on the
original convolution objects.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] convolutionEvenFamily convolutionLeftFamily
  convolutionRightFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h l : t.group, t.nu g h + t.nu (g * h) l = t.nu h l + t.nu g (h * l))

theorem convolutionAssocIndex_apply (a g : t.group) :
    convolutionAssocIndex t ⟨a, g⟩ = ⟨g, g⁻¹ * a⟩ := rfl

theorem convolutionBlocksIsoOfParity_inclusion (X Y Z : PullbackObj C t) (k g h : t.group) :
    biproduct.ι (fun i : (_ : t.group) × t.group => convolutionLeftFamily C hC t X Y Z k i.1 i.2)
        ⟨g * h, g⟩ ≫ (convolutionBlocksIsoOfParity C hC t hν X Y Z k).hom =
      (convolutionBlockIsoOfParity C hC t hν X Y Z k g h).hom ≫
        biproduct.ι (fun i : (_ : t.group) × t.group => convolutionRightFamily C hC t X Y Z k i.1 i.2)
          ⟨g, h⟩ := by
  simp only [convolutionBlocksIsoOfParity, biproduct.whiskerEquiv_hom, biproduct.ι_desc,
    convolutionAssocIndex_apply]
  generalize_proofs hC₀ hm hb hcast
  revert hcast
  rw [inv_mul_cancel_left]
  intro hcast
  rfl

theorem convolutionAssociator_inclusionOfParity (X Y Z : PullbackObj C t) (k g h : t.group) :
    convolutionLeftInsertionEven C hC t X Y Z k (g * h) g ≫
      (convolutionAssociatorEvenIsoOfParity C hC t hν X Y Z k).hom =
        (convolutionBlockIsoOfParity C hC t hν X Y Z k g h).hom ≫
          convolutionRightInsertionEven C hC t X Y Z k g h := by
  apply (cancel_mono (convolutionRightExpand C hC t X Y Z k).hom).1
  simp only [convolutionAssociatorEvenIsoOfParity, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, convolutionLeftInsertion_expand, convolutionBlocksIsoOfParity_inclusion C hC t hν,
    convolutionRightInsertion_expand]

theorem convolutionAssociatorOfParity_inclusion_hom (X Y Z : PullbackObj C t) (k a b : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t X Y Z k (a * b) a).hom
      (convolutionAssociatorDataOfParity C hC t hν X Y Z k).hom =
        C.comp (convolutionBlockIsoOfParity C hC t hν X Y Z k a b).hom.hom
          (convolutionRightInsertionEven C hC t X Y Z k a b).hom :=
  congrArg (fun f => f.hom) (convolutionAssociator_inclusionOfParity C hC t hν X Y Z k a b)

end RMod.Classification

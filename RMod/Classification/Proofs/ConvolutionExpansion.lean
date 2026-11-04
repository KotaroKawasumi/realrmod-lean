import RMod.Classification.Instances.ConvolutionTripleInsertions
import RMod.Classification.Proofs.IteratedBiproducts
import RMod.Classification.Proofs.TensorBiproducts

/-!
# The expansion maps on every threefold summand

The chosen sum comparison cancels against the inclusions transported
from Mathlib. The two tensor distributors then carry these maps to the
nested biproduct inclusions. Finally the iterated biproduct comparison
identifies the label pair, giving the exact block equations needed for
naturality and coherence of the actual convolution associator.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local implicit_reducible] convolutionEvenFamily convolutionLeftFamily
  convolutionRightFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionLeftInsertion_expand (X Y Z : PullbackObj C t) (k a g : t.group) :
    convolutionLeftInsertionEven C hC t X Y Z k a g ≫ (convolutionLeftExpand C hC t X Y Z k).hom =
      biproduct.ι (fun i : (_ : t.group) × t.group => convolutionLeftFamily C hC t X Y Z k i.1 i.2)
        ⟨a, g⟩ := by
  simp only [convolutionLeftInsertionEven, convolutionLeftExpand, convolutionInclusionEven,
    Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc, biproduct.mapIso_hom,
    biproduct.ι_map_assoc, tensorIso_hom, Iso.refl_hom, tensorHom_id]
  have he := rightTensorExpansion_inclusion (convolutionEvenFamily C hC t X Y a)
    (convolutionEvenIso C hC t X Y a) (referenceEvenObj C hC (Z (a⁻¹ * k)).val)
    (referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))) g
  have hh := congrArg (fun m => m ≫
    biproduct.ι (fun a => ⨁ (convolutionLeftFamily C hC t X Y Z k a)) a ≫
      (biproductBiproductIso (fun _ : t.group => t.group) (convolutionLeftFamily C hC t X Y Z k)).hom) he
  simp only [Category.assoc] at hh
  exact hh.trans (iteratedBiproduct_inclusion (convolutionLeftFamily C hC t X Y Z k) a g)

theorem convolutionRightInsertion_expand (X Y Z : PullbackObj C t) (k g h : t.group) :
    convolutionRightInsertionEven C hC t X Y Z k g h ≫ (convolutionRightExpand C hC t X Y Z k).hom =
      biproduct.ι (fun i : (_ : t.group) × t.group => convolutionRightFamily C hC t X Y Z k i.1 i.2)
        ⟨g, h⟩ := by
  simp only [convolutionRightInsertionEven, convolutionRightExpand, convolutionInclusionEven,
    Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc, biproduct.mapIso_hom,
    biproduct.ι_map_assoc, tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom]
  have he := leftTensorExpansion_inclusion (convolutionEvenFamily C hC t Y Z (g⁻¹ * k))
    (convolutionEvenIso C hC t Y Z (g⁻¹ * k)) (referenceEvenObj C hC (X g).val)
    (referenceEvenObj C hC (C.pi.factor (t.nu g (g⁻¹ * k)))) h
  have hh := congrArg (fun m => m ≫
    biproduct.ι (fun g => ⨁ (convolutionRightFamily C hC t X Y Z k g)) g ≫
      (biproductBiproductIso (fun _ : t.group => t.group) (convolutionRightFamily C hC t X Y Z k)).hom) he
  simp only [Category.assoc] at hh
  exact hh.trans (iteratedBiproduct_inclusion (convolutionRightFamily C hC t X Y Z k) g h)

end RMod.Classification

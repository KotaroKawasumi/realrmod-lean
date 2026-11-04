import RMod.Classification.Instances.ConvolutionBiproduct
import RMod.Classification.Proofs.EvenBiproducts

/-!
# The actual convolution comparison preserves its summand maps

The finite enumeration is only an implementation choice. Its biproduct
comparison takes the supplied inclusion of each enumerated summand to
the group-indexed inclusion. The inverse equation recovers the supplied
inclusion, fixing the connection between raw convolution maps and the
Mathlib distributors used to construct associativity.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

attribute [local implicit_reducible] Decomposition.toEvenBicone convolutionDecomposition
  convolutionEvenFamily convolutionFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionEvenIso_inclusion (X Y : PullbackObj C t) (k : t.group)
    (i : Fin (Nat.card t.group)) :
    (convolutionDecomposition C hC t X Y k).toEvenBicone.ι i ≫
      (convolutionEvenIso C hC t X Y k).hom =
        biproduct.ι (convolutionEvenFamily C hC t X Y k) (groupEnumeration t i) := by
  rw [convolutionEvenIso, Iso.trans_hom, ← Category.assoc, Decomposition.inclusion_comparison]
  simp only [biproduct.whiskerEquiv_hom, biproduct.ι_desc, Iso.refl_inv]
  exact Category.id_comp _

theorem convolutionEvenIso_inclusion_inv (X Y : PullbackObj C t) (k : t.group)
    (i : Fin (Nat.card t.group)) :
    biproduct.ι (convolutionEvenFamily C hC t X Y k) (groupEnumeration t i) ≫
      (convolutionEvenIso C hC t X Y k).inv =
        (convolutionDecomposition C hC t X Y k).toEvenBicone.ι i := by
  apply (cancel_mono (convolutionEvenIso C hC t X Y k).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, convolutionEvenIso_inclusion]

theorem convolutionEvenIso_inv_projection (X Y : PullbackObj C t) (k : t.group)
    (i : Fin (Nat.card t.group)) :
    (convolutionEvenIso C hC t X Y k).inv ≫
      (convolutionDecomposition C hC t X Y k).toEvenBicone.π i =
        biproduct.π (convolutionEvenFamily C hC t X Y k) (groupEnumeration t i) := by
  rw [convolutionEvenIso, Iso.trans_inv, Category.assoc, Decomposition.comparison_inv_projection,
    biproduct.whiskerEquiv_inv_eq_lift, biproduct.lift_π]
  simp only [Iso.refl_hom, Category.comp_id]

end RMod.Classification

import RMod.Classification.Instances.ConvolutionMaps
import RMod.Classification.Instances.EvenBiproducts
import RMod.Classification.Instances.EvenIsos

/-!
# The chosen convolution sum and Mathlib's indexed biproduct

The comparison first uses the actual inclusions and projections of C's
chosen finite sum, then reindexes by the finite-group enumeration. Thus
all subsequent Mathlib distributivity maps refer to the original
convolution object through an explicit even isomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

abbrev ReferenceEvenCategory :=
  EvenSubcategory ℝ (LinearCategory ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩)

abbrev referenceEvenObj (X : C.Obj) : ReferenceEvenCategory C hC := ⟨X⟩

def convolutionEvenFamily (X Y : PullbackObj C t) (k : t.group) :
    t.group → ReferenceEvenCategory C hC := fun g =>
  referenceEvenObj C hC (twistSummand C t X Y g (g⁻¹ * k))

noncomputable def convolutionDecomposition (X Y : PullbackObj C t) (k : t.group) :
    Decomposition ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (convolutionObj C hC t X Y k).val (convolutionFamily C t X Y k) :=
  let b := convolutionSum C hC t X Y k
  ⟨⟨b.data.inclusion, b.data.projection⟩,
    ⟨b.laws.inclusion_even, b.laws.projection_even, b.laws.diagonal,
      b.laws.off_diagonal, b.laws.total⟩⟩

noncomputable def convolutionEvenIso (X Y : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t X Y k).val ≅
      ⨁ (convolutionEvenFamily C hC t X Y k) :=
  (biproduct.uniqueUpToIso _ (convolutionDecomposition C hC t X Y k).evenIsBilimit) ≪≫
    biproduct.whiskerEquiv
      (f := fun i => referenceEvenObj C hC (convolutionFamily C t X Y k i))
      (g := convolutionEvenFamily C hC t X Y k)
      (groupEnumeration t) (fun _ => CategoryTheory.Iso.refl _)

end RMod.Classification

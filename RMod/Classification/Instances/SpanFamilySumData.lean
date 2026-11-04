import RMod.Classification.Abstract.SpanFamily
import RMod.Classification.Instances.EvenBiproducts

/-!
# Actual finite sums of component families

Choose the sum in the even category, retaining its even inclusions and
projections. Arbitrary homogeneous or inhomogeneous maps are sent to
the diagonal matrix in the full linear category. Thus the sum uses
Mathlib's biproduct objects without restricting the input morphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I] (S : I → C.data.Obj)

noncomputable def spanFamilyEvenObjects (X : SpanFamilyCategory C S) : I → EvenSubcategory ℝ (LinearCategory C) :=
  fun i => evenObj ℝ (LinearCategory C) (X i).obj

noncomputable def spanFamilySumObj (X : SpanFamilyCategory C S) : LinearCategory C :=
  (⨁ spanFamilyEvenObjects C S X).obj

noncomputable def spanFamilySumData : Prefunctor (SpanFamilyCategory C S) (LinearCategory C) where
  obj := spanFamilySumObj C S
  map {X Y} f := ∑ i, (show @Quiver.Hom (LinearCategory C) _
    (spanFamilySumObj C S X) (spanFamilySumObj C S Y) from
      C.data.comp (C.data.comp (biproduct.π (spanFamilyEvenObjects C S X) i).hom (f i).hom)
        (biproduct.ι (spanFamilyEvenObjects C S Y) i).hom)

end RMod.Classification

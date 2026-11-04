import RMod.Classification.Instances.SpanFamilySum

/-!
# Explicit diagonal entries of a map between the chosen sums

Project to each source and target component using the retained even
matrix coordinates. This supplies actual preimage data for fullness;
no inverse operation is hidden in a mere surjectivity assertion.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I] (S : I → C.data.Obj)

noncomputable def spanFamilySumPreimage {X Y : SpanFamilyCategory C S}
    (f : (spanFamilySum C S).obj X ⟶ (spanFamilySum C S).obj Y) : X ⟶ Y := fun i =>
  ObjectProperty.homMk (C.data.comp
    (C.data.comp ((evenBiproductFullBicone C (spanFamilyEvenObjects C S X)).ι i) f)
    ((evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).π i))

end RMod.Classification

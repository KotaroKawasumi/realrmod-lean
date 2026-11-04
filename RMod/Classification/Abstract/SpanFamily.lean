import RMod.Classification.Abstract.HomogeneousSpan
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Families of objects in specified homogeneous spans

Mathlib's product category keeps all morphisms coordinatewise. No
monoidal structure or comparison of distinct component labels is built
into this carrier.
-/

set_option autoImplicit false

namespace RMod.Classification

abbrev SpanFamilyCategory (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} (S : I → C.data.Obj) :=
  (i : I) → HomogeneousSpanCategory C (S i)

end RMod.Classification

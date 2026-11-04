import RMod.Classification.Abstract.HomogeneousSpan

/-!
# Choosing coordinates on an object of the homogeneous span

The size and actual homogeneous sum are selected from membership in the
span. The completed sum retains its explicit Data and the Laws on those
Data, so subsequent map constructions can use all matrix coordinates.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj}

noncomputable def spanSize (X : HomogeneousSpanCategory C S) : ℕ := X.property.choose

noncomputable def spanPresentation (X : HomogeneousSpanCategory C S) :
    HomogeneousSum C.data S X.obj (spanSize X) := Classical.choice X.property.choose_spec

end RMod.Classification

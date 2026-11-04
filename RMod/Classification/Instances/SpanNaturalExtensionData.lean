import RMod.Classification.Abstract.SpanIntertwiner
import RMod.Classification.Instances.HomogeneousSpanPresentation

/-!
# Extending a generator comparison by homogeneous matrix coordinates

Each summand contributes the transported generator comparison with the
sign required to cross its parity. Only the chosen inclusions, projections
and the supplied comparison morphism enter these component data.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

noncomputable def spanNaturalExtensionData (F G : SpanSuperfunctorData C D S T) (a : ZMod 2)
    (t : SpanIntertwinerData F G) : SpanHomogeneousNatData F G where
  app X := ∑ i, ((-1 : ℝ) ^ (a * (spanPresentation X).data.parity i).val) •
    (F.map (ObjectProperty.homMk ((spanPresentation X).data.projection i) : X ⟶ spanGenerator C S) ≫
      t.hom ≫ G.map (ObjectProperty.homMk ((spanPresentation X).data.inclusion i) : spanGenerator C S ⟶ X))

end RMod.Classification

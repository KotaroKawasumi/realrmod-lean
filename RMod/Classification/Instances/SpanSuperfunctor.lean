import RMod.Classification.Abstract.SpanSuperfunctor
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Mathlib functors underlying span superfunctors

The functor uses exactly the supplied object and morphism data. Their
separated laws install ordinary functoriality and real linearity.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperfunctor

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

def toFunctor (F : SpanSuperfunctor C D S T) :
    HomogeneousSpanCategory C S ⥤ HomogeneousSpanCategory D T where
  obj := F.data.obj
  map := F.data.map
  map_id := F.laws.map_id
  map_comp := F.laws.map_comp

instance additive (F : SpanSuperfunctor C D S T) : F.toFunctor.Additive where
  map_add := F.laws.map_add _ _

instance linear (F : SpanSuperfunctor C D S T) : F.toFunctor.Linear ℝ where
  map_smul f r := F.laws.map_smul r f

end RMod.Classification.SpanSuperfunctor

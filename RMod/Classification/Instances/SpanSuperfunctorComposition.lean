import RMod.Classification.Instances.SpanSuperfunctor

/-!
# Composition of component superfunctors

Compose the specified object and morphism maps. The functor, linearity
and degree laws follow successively from the two completed functors.
No new choices of maps or inverse maps are made by this operation.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperfunctor

variable {C D E : WeaklyPointedSuperfusion.{0, 0}}
  {S : C.data.Obj} {T : D.data.Obj} {U : E.data.Obj}

def compData (F : SpanSuperfunctorData C D S T) (G : SpanSuperfunctorData D E T U) :
    SpanSuperfunctorData C E S U where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

theorem compLaws (F : SpanSuperfunctor C D S T) (G : SpanSuperfunctor D E T U) :
    SpanSuperfunctorLaws C E S U (compData F.data G.data) where
  map_id X := (congrArg G.data.map (F.laws.map_id X)).trans (G.laws.map_id _)
  map_comp f g := (congrArg G.data.map (F.laws.map_comp f g)).trans (G.laws.map_comp _ _)
  map_zero X Y := (congrArg G.data.map (F.laws.map_zero X Y)).trans (G.laws.map_zero _ _)
  map_add f g := (congrArg G.data.map (F.laws.map_add f g)).trans (G.laws.map_add _ _)
  map_smul r f := (congrArg G.data.map (F.laws.map_smul r f)).trans (G.laws.map_smul _ _)
  map_grade f hf := G.laws.map_grade _ (F.laws.map_grade f hf)

def comp (F : SpanSuperfunctor C D S T) (G : SpanSuperfunctor D E T U) :
    SpanSuperfunctor C E S U := ⟨compData F.data G.data, compLaws F G⟩

end RMod.Classification.SpanSuperfunctor

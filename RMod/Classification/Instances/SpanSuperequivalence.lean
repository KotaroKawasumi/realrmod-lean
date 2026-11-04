import RMod.Classification.Abstract.SpanSuperequivalence
import RMod.Classification.Instances.SpanSuperfunctor

/-!
# The two superfunctors of a component equivalence

The forward and inverse maps retain precisely the data in the underlying
Mathlib equivalence. Their linearity and grading proofs are the separate
laws already carried by the completed super-equivalence.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperequivalence

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

def forwardFunctor (E : SpanSuperequivalence C D S T) : SpanSuperfunctor C D S T :=
  ⟨E.data.functor.toPrefunctor, E.laws.forward⟩

def backwardFunctor (E : SpanSuperequivalence C D S T) : SpanSuperfunctor D C T S :=
  ⟨E.data.inverse.toPrefunctor, E.laws.backward⟩

end RMod.Classification.SpanSuperequivalence

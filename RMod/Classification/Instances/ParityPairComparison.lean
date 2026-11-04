import RMod.Classification.Proofs.ParityCenterFunctor
import RMod.Classification.Instances.MonoidalWordComparisons

/-!
# The parity specialization of the canonical pair comparison

This abbreviation retains the supplied parity-sum equality and the
actual center multiplication maps. It only shortens the subsequent
comparison statements; it introduces no new operation or law.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory

noncomputable abbrev parityPairCompare (C : WeaklyPointedSuperfusion.{u, v})
    (p : PiData C.data) (hp : PiLaws C.data p)
    (a b c d : ZMod 2) (he : a + b = c + d) :
    factorCenter C p hp a ⊗ factorCenter C p hp b ≅
      factorCenter C p hp c ⊗ factorCenter C p hp d :=
  MonoidalWord.pairCompare (parityCenterFunctor C p hp)
    (.ofAdd a) (.ofAdd b) (.ofAdd c) (.ofAdd d) (congrArg Multiplicative.ofAdd he)

end RMod.Classification

import RMod.BrundanEllis.StackingGradedFaithful
import RMod.BrundanEllis.StackingOrbitTransport
import RMod.Hierarchy.Bridge.EndConjugation

/-! A graded fully faithful functor preserves the full real endomorphism
algebra. An even object comparison can then identify this algebra with that
of a chosen target object, including the split real tensor unit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))

def totalEndEquivalence (X : C) :
    End (totalObj C X) ≃ₐ[ℝ] End (totalObj D (F.obj X)) where
  toEquiv := (totalFullyFaithful F hF).homEquiv
  map_mul' f g := (totalSuperFunctor F).map_comp g f
  map_add' f g := by
    funext a
    exact map_add (F.map X X a).hom (f a) (g a)
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change tMap F (r • evenPoint (eId SuperVec X)) =
      r • evenPoint (eId SuperVec (F.obj X))
    funext a
    change F.map X X a (r • evenPoint (eId SuperVec X) a) = _
    rw [map_smul]
    exact congrArg (fun f : THom D (F.obj X) (F.obj X) => r • f a)
      ((totalSuperFunctor F).map_id X)

/-- Include an even comparison with the target object in the algebra transport. -/
def endEquivalenceOfIso (X : Even C) (Y : Even D) (e : F.forget.obj X ≅ Y) :
    End (totalObj C X) ≃ₐ[ℝ] End (totalObj D Y) :=
  (totalEndEquivalence F hF (ForgetEnrichment.to SuperVec X)).trans
    (RMod.Legacy.Hierarchy.endConjAlgEquiv ((superEvenToTotal D).mapIso e))

end RMod.BrundanEllis.Stacking

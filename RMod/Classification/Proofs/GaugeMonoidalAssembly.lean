import RMod.Classification.Instances.GaugeMonoidalData
import RMod.Classification.Proofs.GaugeUnitCoherence
import RMod.Classification.Proofs.GaugeRightUnitCoherence
import RMod.Classification.Proofs.GaugeUnit

/-!
# All gauge functor laws except the associativity comparison

Real superlinearity comes from the completed underlying functor. The
specified tensorator and unit have checked even inverse pairs, and their
naturality and unit diagrams hold on the chosen convolution objects.
Only the associativity equation is an input to this assembly lemma;
the omega gauge equation must establish it for the final construction.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
  (hlam : d.lam 1 = 0)

theorem gaugeMonoidalFunctorLaws_of_associativity
    (hβL : ∀ g, d.beta 1 g = 1) (hβR : ∀ g, d.beta g 1 = 1)
    (hassoc :
      let A := (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      let B := (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      let F := gaugeMonoidalFunctorData C hC s t d hρ hν hlam
      ∀ X Y Z,
        B.comp (B.comp (B.tensorHom (F.tensorHom X Y) (B.id (F.obj Z)))
          (F.tensorHom (A.tensorObj X Y) Z)) (F.map (A.associatorHom X Y Z)) =
        B.comp (B.comp (B.associatorHom (F.obj X) (F.obj Y) (F.obj Z))
          (B.tensorHom (B.id (F.obj X)) (F.tensorHom Y Z)))
          (F.tensorHom X (A.tensorObj Y Z))) :
    MonoidalSuperfunctorLaws (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (gaugeMonoidalFunctorData C hC s t d hρ hν hlam) where
  toSuperfunctorLaws := (gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).laws
  tensor_hom_even X Y := fun k => (gaugeTensorator_evenIso C hC s t d hρ hν X Y k).hom_even
  tensor_inv_even X Y := fun k => (gaugeTensorator_evenIso C hC s t d hρ hν X Y k).inv_even
  tensor_hom_inv X Y := funext fun k => (gaugeTensorator_evenIso C hC s t d hρ hν X Y k).hom_inv
  tensor_inv_hom X Y := funext fun k => (gaugeTensorator_evenIso C hC s t d hρ hν X Y k).inv_hom
  unit_hom_even := fun k => (gaugeUnitComponent_evenIso C hC s t d hρ hlam k).hom_even
  unit_inv_even := fun k => (gaugeUnitComponent_evenIso C hC s t d hρ hlam k).inv_even
  unit_hom_inv := funext fun k => (gaugeUnitComponent_evenIso C hC s t d hρ hlam k).hom_inv
  unit_inv_hom := funext fun k => (gaugeUnitComponent_evenIso C hC s t d hρ hlam k).inv_hom
  tensor_naturality f g := funext fun k => gaugeTensorator_naturality C hC s t d hρ hν f g k
  associativity := hassoc
  left_unit X := funext fun k => gaugeTensorator_left_unit C hC s t d hρ hν hlam hβL X k
  right_unit X := funext fun k => gaugeTensorator_right_unit C hC s t d hρ hν hlam hβR X k

end RMod.Classification

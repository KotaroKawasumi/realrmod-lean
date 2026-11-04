import RMod.BrundanEllis.StackingPullbackEvenCalculus
import RMod.BrundanEllis.StackingExternalReversedPure
import RMod.BrundanEllis.StackingProductWhisker
import RMod.BrundanEllis.StackingEnrichedUnit

/-! Coordinate and summand formulas for the actual corrected exterior tensor comparison. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- On pure pairs of even maps the exterior functor is the reversed tensor
of the actual coordinate maps, with no remaining Koszul scalar. -/
theorem reversedExteriorPairing_evenPair (s t : Twist)
    {X X' : Even (pullback s)} {Y Y' : Even (pullback t)}
    (f : X ⟶ X') (q : Y ⟶ Y') (g : s.group) (h : t.group) :
    pullbackEvenValue (exteriorTwist s t).val
      ((reversedExteriorPairing s t).forget.map
        ((productPair (pullback s) (pullback t)).map (X := (X, Y)) (Y := (X', Y')) (f, q))) (g, h) =
    reference.data.tensorHom (pullbackEvenValue t q h) (pullbackEvenValue s f g) := by
  let pq := (productPair (pullback s) (pullback t)).map (X := (X, Y)) (Y := (X', Y')) (f, q)
  have hp : RMod.evenPoint (ForgetEnrichment.homTo SuperVec pq) 0 =
      RMod.Legacy.gradedTmul (SHom (pullback s) X X') (SHom (pullback t) Y Y')
        0 0 0 rfl (RMod.evenPoint (ForgetEnrichment.homTo SuperVec f) 0)
          (RMod.evenPoint (ForgetEnrichment.homTo SuperVec q) 0) := by
    change ((λ_ (𝟙_ SuperVec)).inv ≫
      (ForgetEnrichment.homTo SuperVec f ⊗ₘ ForgetEnrichment.homTo SuperVec q)) 0
        ((GradedObject.Monoidal.tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1) = _
    have hu := GradedObject.Monoidal.leftUnitor_inv_apply (𝟙_ SuperVec) 0
    change (GradedObject.Monoidal.leftUnitor (𝟙_ SuperVec)).inv 0 = _ at hu
    change GradedObject.Monoidal.tensorHom (ForgetEnrichment.homTo SuperVec f)
      (ForgetEnrichment.homTo SuperVec q) 0
      ((GradedObject.Monoidal.leftUnitor (𝟙_ SuperVec)).inv 0
        ((GradedObject.Monoidal.tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1)) = _
    rw [hu]
    have he := congrArg (fun z => z
      (((GradedObject.Monoidal.tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1) ⊗ₜ[ℝ]
       ((GradedObject.Monoidal.tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1)))
      (GradedObject.Monoidal.ι_tensorHom (ForgetEnrichment.homTo SuperVec f)
        (ForgetEnrichment.homTo SuperVec q) 0 0 0 (zero_add 0))
    exact he
  have hm := congrArg (fun z => z.val (g, h))
    (congrFun (map_even_point (reversedExteriorPairing s t) pq) 0)
  change ((reversedExteriorPairing s t).map (X, Y) (X', Y') 0
    (RMod.evenPoint (ForgetEnrichment.homTo SuperVec pq) 0)).val (g, h) =
      pullbackEvenValue (exteriorTwist s t).val
        ((reversedExteriorPairing s t).forget.map pq) (g, h) at hm
  rw [hp, reversedExteriorPairing_tmul] at hm
  exact hm.symm

/-- The actual product associator is mapped to the tensor of the two
original convolution associators in the same reversed order. -/
theorem reversedExteriorPairing_associator (s t : Twist)
    (X Y Z : Even (SuperTensorProduct (pullback s) (pullback t)))
    (g : s.group) (h : t.group) :
    pullbackEvenValue (exteriorTwist s t).val
      ((reversedExteriorPairing s t).forget.map (α_ X Y Z).hom) (g, h) =
    reference.data.tensorHom
      (convolutionAssociatorData reference.data referenceProperty (oldTwist t).data
        (oldTwist t).laws X.2 Y.2 Z.2 h).hom
      (convolutionAssociatorData reference.data referenceProperty (oldTwist s).data
        (oldTwist s).laws X.1 Y.1 Z.1 g).hom := by
  exact (reversedExteriorPairing_evenPair s t
    (X := ((X.1 : Even (pullback s)) ⊗ Y.1) ⊗ Z.1) (X' := (X.1 : Even (pullback s)) ⊗ ((Y.1 : Even (pullback s)) ⊗ Z.1))
    (Y := ((X.2 : Even (pullback t)) ⊗ Y.2) ⊗ Z.2) (Y' := (X.2 : Even (pullback t)) ⊗ ((Y.2 : Even (pullback t)) ⊗ Z.2))
    (CategoryTheory.MonoidalCategory.associator (C := Even (pullback s)) X.1 Y.1 Z.1).hom
    (CategoryTheory.MonoidalCategory.associator (C := Even (pullback t)) X.2 Y.2 Z.2).hom g h).trans
    (congrArg₂ reference.data.tensorHom
      (pullbackEvenValue_associator t X.2 Y.2 Z.2 h)
      (pullbackEvenValue_associator s X.1 Y.1 Z.1 g))

/-- The original left unitors are mapped coordinatewise in reversed order. -/
theorem reversedExteriorPairing_leftUnitor (s t : Twist)
    (X : Even (SuperTensorProduct (pullback s) (pullback t)))
    (g : s.group) (h : t.group) :
    pullbackEvenValue (exteriorTwist s t).val
      ((reversedExteriorPairing s t).forget.map (λ_ X).hom) (g, h) =
    reference.data.tensorHom
      (convolutionLeftUnitorData reference.data referenceProperty (oldTwist t).data
        (oldTwist t).laws X.2 h).hom
      (convolutionLeftUnitorData reference.data referenceProperty (oldTwist s).data
        (oldTwist s).laws X.1 g).hom := by
  exact (reversedExteriorPairing_evenPair s t
    (X := (𝟙_ (Even (pullback s))) ⊗ X.1) (X' := X.1)
    (Y := (𝟙_ (Even (pullback t))) ⊗ X.2) (Y' := X.2)
    (CategoryTheory.MonoidalCategory.leftUnitor (C := Even (pullback s)) X.1).hom (CategoryTheory.MonoidalCategory.leftUnitor (C := Even (pullback t)) X.2).hom g h).trans
    (congrArg₂ reference.data.tensorHom
      (pullbackEvenValue_leftUnitor t X.2 h) (pullbackEvenValue_leftUnitor s X.1 g))

/-- The original right unitors have the corresponding coordinate formula. -/
theorem reversedExteriorPairing_rightUnitor (s t : Twist)
    (X : Even (SuperTensorProduct (pullback s) (pullback t)))
    (g : s.group) (h : t.group) :
    pullbackEvenValue (exteriorTwist s t).val
      ((reversedExteriorPairing s t).forget.map (ρ_ X).hom) (g, h) =
    reference.data.tensorHom
      (convolutionRightUnitorData reference.data referenceProperty (oldTwist t).data
        (oldTwist t).laws X.2 h).hom
      (convolutionRightUnitorData reference.data referenceProperty (oldTwist s).data
        (oldTwist s).laws X.1 g).hom := by
  exact (reversedExteriorPairing_evenPair s t
    (X := (X.1 : Even (pullback s)) ⊗ (𝟙_ (Even (pullback s)))) (X' := X.1)
    (Y := (X.2 : Even (pullback t)) ⊗ (𝟙_ (Even (pullback t)))) (Y' := X.2)
    (CategoryTheory.MonoidalCategory.rightUnitor (C := Even (pullback s)) X.1).hom (CategoryTheory.MonoidalCategory.rightUnitor (C := Even (pullback t)) X.2).hom g h).trans
    (congrArg₂ reference.data.tensorHom
      (pullbackEvenValue_rightUnitor t X.2 h) (pullbackEvenValue_rightUnitor s X.1 g))

end RMod.BrundanEllis.Stacking

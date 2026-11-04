import RMod.BrundanEllis.StackingExternalReversed
import RMod.BrundanEllis.StackingExternalFaithful
import RMod.BrundanEllis.StackingTensorFaithful

/-! The reversed exterior pairing retains full faithfulness in every degree.
Both support reversal and the enriched swap have explicit inverse maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace RMod.BrundanEllis.Stacking

/-- Support reversal is bijective on each homogeneous Hom space. -/
theorem reverseExterior_bijective (s t : Twist) (X Y : exteriorModel t s) (a : ZMod 2) :
    Function.Bijective ((reverseExterior s t).map X Y a) := by
  constructor
  · intro f g h
    apply Subtype.ext
    funext gh
    exact congrArg (fun q => q.val (gh.2, gh.1)) h
  · intro f
    refine ⟨⟨fun hg => f.val (hg.2, hg.1), fun hg => f.property (hg.2, hg.1)⟩, ?_⟩
    apply Subtype.ext
    funext gh
    rfl

/-- Swapping enriched input factors retains the actual Koszul Hom isomorphism. -/
theorem enrichedSwap_bijective (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t)) (a : ZMod 2) :
    Function.Bijective ((enrichedSwap SuperVec (pullback s) (pullback t)).map X Y a) :=
  iso_component_bijective (β_ (SHom (pullback s) X.1 Y.1) (SHom (pullback t) X.2 Y.2)) a

/-- The specified reversed exterior functor is fully faithful in all parities. -/
theorem reversedExteriorPairing_bijective (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t)) (a : ZMod 2) :
    Function.Bijective ((reversedExteriorPairing s t).map X Y a) :=
  comp_functors_bijective _ _
    (comp_functors_bijective _ _ (enrichedSwap_bijective s t) (exteriorPairing_bijective t s))
    (reverseExterior_bijective s t) X Y a

end RMod.BrundanEllis.Stacking

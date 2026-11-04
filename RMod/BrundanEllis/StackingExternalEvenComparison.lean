import RMod.BrundanEllis.StackingExternalTensorator
import RMod.BrundanEllis.StackingPullbackCoordinateIso
import RMod.BrundanEllis.StackingPullbackHomPoints
import RMod.BrundanEllis.StackingProductMonoidal

/-! The previously specified finite-sum comparisons assemble into an actual
isomorphism in the even pullback category. Coherence is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- The exterior tensor comparison as an isomorphism of whole pullback objects. -/
def reversedExteriorTensorIso (s t : Twist)
    (X Y : Even (SuperTensorProduct (pullback s) (pullback t))) :
    (reversedExteriorPairing s t).forget.obj X ⊗ (reversedExteriorPairing s t).forget.obj Y ≅
      (reversedExteriorPairing s t).forget.obj (X ⊗ Y) :=
  pullbackCoordinateIso (exteriorTwist s t).val _ _
    (fun gh => exteriorTensoratorEvenIso s t X.1 Y.1 X.2 Y.2 gh.1 gh.2)

/-- The assembled comparison has exactly the previously specified coordinate map. -/
theorem reversedExteriorTensorIso_hom (s t : Twist)
    (X Y : Even (SuperTensorProduct (pullback s) (pullback t)))
    (g : s.group) (h : t.group) :
    pullbackEvenValue (exteriorTwist s t).val (reversedExteriorTensorIso s t X Y).hom (g, h) =
      (exteriorTensoratorData s t X.1 Y.1 X.2 Y.2 g h).hom := by
  unfold pullbackEvenValue reversedExteriorTensorIso
  rw [pullbackCoordinateIso_hom]
  rfl

end RMod.BrundanEllis.Stacking

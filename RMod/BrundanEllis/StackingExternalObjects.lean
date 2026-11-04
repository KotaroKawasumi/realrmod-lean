import RMod.BrundanEllis.StackingBaseChange
import RMod.BrundanEllis.StackingModelBridge
import RMod.Classification.Instances.PullbackEvaluation
import RMod.Hierarchy.Bridge.Superfunctors

/-! The external cochain model has actual reference-category tensor products
at pairs of labels. Evaluation of each input coordinate is an enriched
functor. These constructions provide the object and component maps needed
for the exterior pairing; monoidal comparison is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory
namespace RMod.BrundanEllis.Stacking

/-- Retain the precise reference presentation used by the public pullbacks. -/
abbrev referenceCategory : WeaklyPointedFusionPiSuperCat := fromOld reference

/-- Evaluation preserves the actual linear maps in each homogeneous degree. -/
def evaluate (s : Twist) (g : s.group) : SuperFunctor (pullback s) referenceCategory := by
  with_unfolding_all
    exact RMod.StatementLegacy.StatementBridge.fromFunctor
      (RMod.Legacy.Hierarchy.ofOldSuperfunctor
        (RMod.Classification.pullbackEvaluation reference.data referenceProperty (oldTwist s) g))

def exteriorTwist (s t : Twist) : TwistOn (FiniteGrp.of (s.group × t.group)) :=
  externalTwist ⟨s, rfl⟩ ⟨t, rfl⟩

/-- This model already has the explicitly specified external cochains. -/
def exteriorModel (s t : Twist) : WeaklyPointedFusionPiSuperCat :=
  pullback (exteriorTwist s t).val

/-- The object at (g,h) is the reference tensor of the two input objects.
Its intrinsic Brauer--Wall type is the sum, exactly the external degree. -/
def exteriorObject (s t : Twist) (X : pullback s) (Y : pullback t) : exteriorModel s t :=
  fun gh => ⟨reference.data.tensorObj (X gh.1).val (Y gh.2).val, by
    change RMod.Classification.InComponent reference.data.toWeaklyPointedSuperfusionData
      ((s.rho gh.1).toAdd + (t.rho gh.2).toAdd) _
    exact RMod.Classification.InComponent.tensor referenceProperty (X gh.1).property (Y gh.2).property⟩

/-- The component formula is fixed before any comparison of monoidal data. -/
theorem exteriorObject_data (s t : Twist) (X : pullback s) (Y : pullback t)
    (g : s.group) (h : t.group) :
    (exteriorObject s t X Y (g, h)).val = reference.data.tensorObj (X g).val (Y h).val := rfl

end RMod.BrundanEllis.Stacking

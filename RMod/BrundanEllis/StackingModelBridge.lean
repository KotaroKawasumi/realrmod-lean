import RMod.BrundanEllis.Classification
import RMod.Classification.Proofs.PullbackUnitLabel
import RMod.Classification.Proofs.PullbackOrbitType

/-! Retain the actual pullback objects through the three established interface
conversions.  Simplicity, parity orbits and Brauer--Wall types are transported
by the existing comparison theorems. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
namespace Stacking
open RMod.Legacy.Hierarchy

/-- The proved old model, expressed in the current public interface. -/
def fromOld (P : RMod.Classification.PiSuperfusion.{0, 0}) :
    WeaklyPointedFusionPiSuperCat :=
  Bridge.fromStage (RMod.EnrichedBridge.fromWeak
    (RMod.StatementLegacy.StatementBridge.fromWeak (ofOldWeaklyPointedFusionPiSupercategory P)))

theorem fromOld_simple (P : RMod.Classification.PiSuperfusion.{0, 0}) (X : P.data.Obj) :
    P.data.IsSimple X ↔ Simple (evenObj (fromOld P) X) := by
  exact oldSimple_iff P.toWeaklyPointedSuperfusion X

theorem fromOld_orbit (P : RMod.Classification.PiSuperfusion.{0, 0}) (X Y : P.data.Obj) :
    RMod.Classification.SameParityOrbit P.data.toWeaklyPointedSuperfusionData X Y ↔
      SameParityOrbit (fromOld P) X Y := by
  with_unfolding_all
    exact (oldParityOrbit_iff P.toWeaklyPointedSuperfusion X Y).trans
      (RMod.StatementLegacy.StatementBridge.orbit_fromSuper
        (ofOldSupercategory P.toWeaklyPointedSuperfusion) X Y).symm

theorem fromOld_type (P : RMod.Classification.PiSuperfusion.{0, 0})
    (X : P.data.Obj) (r : ZMod 8) :
    RMod.Classification.HasBWType P.data.toWeaklyPointedSuperfusionData X r ↔
      HasBrauerWallType (fromOld P) (evenObj (fromOld P) X) r := by
  exact (oldBrauerWallType_iff P X r).trans
    (RMod.StatementLegacy.StatementBridge.hasType_fromFusion _ _ _).symm

/-- The reference already used by the public pullback, before its interface conversions. -/
def legacyReference : RMod.Legacy.WeaklyPointedFusionPiSupercategory :=
  RMod.StatementLegacy.StatementBridge.toWeak
    (RMod.EnrichedBridge.toWeak (Bridge.toStage realRMod))

def legacyReferenceProperty : RMod.Legacy.IsBrauerWallReference legacyReference :=
  RMod.StatementLegacy.StatementBridge.toReference _
    (RMod.EnrichedBridge.toReference _ (Bridge.toReference realRMod real_isBrauerWallReference))

def reference : RMod.Classification.PiSuperfusion.{0, 0} :=
  toOldPiSuperfusion legacyReference

def referenceProperty : RMod.Classification.ReferenceProperty reference.data :=
  toOldReference legacyReference legacyReferenceProperty

/-- The earlier normalized twist has exactly the same cochains and group. -/
def oldTwist (s : Twist) : RMod.Classification.Twist :=
  (RMod.EnrichedBridge.toTwist (Bridge.toTwist s)).toOld

def oldPullback (s : Twist) : RMod.Classification.PiSuperfusion.{0, 0} :=
  RMod.Classification.twistedPullback reference.data referenceProperty (oldTwist s)

end Stacking

abbrev pullback (s : Twist) := twistedPullback realRMod real_isBrauerWallReference s

def pullbackSimple (s : Twist) : s.group → Even (pullback s) := fun g =>
  evenObj (pullback s) (RMod.Classification.pullbackDegreeSimple
    Stacking.reference.data Stacking.referenceProperty (Stacking.oldTwist s) g).data.object

namespace Stacking

theorem pullback_fromOld (s : Twist) : fromOld (oldPullback s) = pullback s := by
  with_unfolding_all rfl

theorem pullbackSimple_simple (s : Twist) (g : s.group) : Simple (pullbackSimple s g) := by
  exact (fromOld_simple (oldPullback s) _).mp
    (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) g).laws.simple

theorem pullbackSimple_one (s : Twist) : pullbackSimple s 1 = (𝟙_ (Even (pullback s))) := by
  exact RMod.Classification.pullbackDegreeSimple_one_object reference.data referenceProperty (oldTwist s)

/-- Every simple has the support label of its existing old-model representative. -/
theorem pullbackSimple_cover (s : Twist) (X : Even (pullback s)) (hX : Simple X) :
    ∃ g, SameParityOrbit (pullback s) X (pullbackSimple s g) := by
  let P := oldPullback s
  let S : RMod.Classification.SimpleObject P.toWeaklyPointedSuperfusion :=
    ⟨⟨X⟩, ⟨(fromOld_simple P X).mpr hX⟩⟩
  let g := RMod.Classification.pullbackSimpleDegree reference.data referenceProperty (oldTwist s) S
  refine ⟨g, (fromOld_orbit P _ _).mp ?_⟩
  apply (RMod.Classification.pullbackSimpleDegree_eq_iff reference.data referenceProperty (oldTwist s) S
    (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) g)).mp
  exact (RMod.Classification.pullbackSimpleDegree_placed reference.data referenceProperty (oldTwist s) g).symm

/-- Distinct group labels give distinct simple parity orbits. -/
theorem pullbackSimple_orbit (s : Twist) (g h : s.group) :
    SameParityOrbit (pullback s) (pullbackSimple s g) (pullbackSimple s h) ↔ g = h := by
  have hi := RMod.Classification.pullbackSimpleDegree_eq_iff reference.data referenceProperty
    (oldTwist s)
    (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) g)
    (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) h)
  rw [RMod.Classification.pullbackSimpleDegree_placed,
    RMod.Classification.pullbackSimpleDegree_placed] at hi
  exact (fromOld_orbit (oldPullback s) _ _).symm.trans hi.symm

/-- The old support theorem identifies the representative's Brauer--Wall type. -/
theorem pullbackSimple_type (s : Twist) (g : s.group) :
    HasBrauerWallType (pullback s) (pullbackSimple s g) (s.rho g).toAdd := by
  apply (fromOld_type (oldPullback s) _ _).mp
  have h := RMod.Classification.simpleType_spec (oldPullback s)
    (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) g)
  dsimp only [oldPullback] at h
  rw [RMod.Classification.pullbackSimple_type, RMod.Classification.pullbackSimpleDegree_placed] at h
  exact h

/-- A simple retract of the convolution tensor has the product support. -/
theorem pullbackSimple_tensor (s : Twist) (g h : s.group) (X : Even (pullback s))
    (hX : Simple X) (hr : Nonempty (Retract X (pullbackSimple s g ⊗ pullbackSimple s h))) :
    SameParityOrbit (pullback s) X (pullbackSimple s (g * h)) := by
  let P := oldPullback s
  let D := P.toWeaklyPointedSuperfusion
  let S : RMod.Classification.SimpleObject D := ⟨⟨X⟩, ⟨(fromOld_simple P X).mpr hX⟩⟩
  let k := RMod.Classification.pullbackSimpleDegree reference.data referenceProperty (oldTwist s) S
  have hk : k = g * h := by
    by_contra he
    have hg := RMod.Classification.pullbackSimpleDegree_supported reference.data referenceProperty
      (oldTwist s) (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) g)
    have hh := RMod.Classification.pullbackSimpleDegree_supported reference.data referenceProperty
      (oldTwist s) (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) h)
    rw [RMod.Classification.pullbackSimpleDegree_placed] at hg hh
    have hz := RMod.Classification.convolution_support reference.data referenceProperty
      (oldTwist s).data g h hg hh k he
    obtain ⟨r⟩ := hr
    let F := RMod.Legacy.Hierarchy.evenForget D
    let r' := r.map F
    have hj := RMod.Classification.hom_eq_zero_of_target
      referenceProperty.toWeaklyPointedSuperfusionLaws hz (r'.i.hom k)
    have hd : reference.data.comp (r'.i.hom k) (r'.r.hom k) =
        reference.data.id (S.data.object k).val := by
      exact congrFun (congrArg (fun f => f.hom) r'.retract) k
    rw [hj] at hd
    exact RMod.Classification.simple_id_ne_zero referenceProperty.toWeaklyPointedSuperfusionLaws
      (RMod.Classification.pullbackSimpleDegree_simple reference.data referenceProperty (oldTwist s) S)
      (hd.symm.trans (RMod.Classification.raw_zero_comp referenceProperty.toWeaklyPointedSuperfusionLaws _))
  apply (fromOld_orbit P _ _).mp
  apply (RMod.Classification.pullbackSimpleDegree_eq_iff reference.data referenceProperty (oldTwist s) S
    (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) (g * h))).mp
  exact hk.trans (RMod.Classification.pullbackSimpleDegree_placed reference.data referenceProperty
    (oldTwist s) (g * h)).symm

end Stacking
/-- The chosen labels retain all six normalization and classification properties. -/
theorem pullbackSimple_data (s : Twist) :
    (∀ g, Simple (pullbackSimple s g)) ∧
    (∀ X : Even (pullback s), Simple X →
      ∃ g, SameParityOrbit (pullback s) X (pullbackSimple s g)) ∧
    (∀ g h, SameParityOrbit (pullback s) (pullbackSimple s g) (pullbackSimple s h) ↔ g = h) ∧
    pullbackSimple s 1 = (𝟙_ (Even (pullback s))) ∧
    (∀ g h X, Simple X → Nonempty (Retract X (pullbackSimple s g ⊗ pullbackSimple s h)) →
      SameParityOrbit (pullback s) X (pullbackSimple s (g * h))) ∧
    (∀ g, HasBrauerWallType (pullback s) (pullbackSimple s g) (s.rho g).toAdd) :=
  ⟨Stacking.pullbackSimple_simple s, Stacking.pullbackSimple_cover s,
    Stacking.pullbackSimple_orbit s, Stacking.pullbackSimple_one s,
    Stacking.pullbackSimple_tensor s, Stacking.pullbackSimple_type s⟩

end RMod.BrundanEllis

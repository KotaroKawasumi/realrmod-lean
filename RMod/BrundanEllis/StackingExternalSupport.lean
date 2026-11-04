import RMod.BrundanEllis.StackingExternalPairing
import RMod.BrundanEllis.StackingHullDualClosure

/-! Exterior products of the chosen simple objects have exactly their pair
of support labels. A nonzero simple retract therefore has that same label.
This connects the concrete exterior pairing with generation of its target. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.Limits
namespace RMod.BrundanEllis.Stacking
open RMod.Legacy.Hierarchy

/-- The images of the two labelled simple representatives. -/
def exteriorGenerator (s t : Twist) (g : s.group) (h : t.group) : Even (exteriorModel s t) :=
  evenObj _ (exteriorObject s t (pullbackSimple s g) (pullbackSimple t h))

/-- Outside the pair of labels, one tensor factor is zero. -/
theorem exteriorGenerator_support (s t : Twist) (g : s.group) (h : t.group)
    (k : s.group × t.group) (hk : k ≠ (g, h)) :
    reference.data.id ((exteriorGenerator s t g h) k).val = reference.data.zero := by
  classical
  have hs := RMod.Classification.pullbackSimpleDegree_supported reference.data referenceProperty
    (oldTwist s) (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) g)
  have ht := RMod.Classification.pullbackSimpleDegree_supported reference.data referenceProperty
    (oldTwist t) (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist t) h)
  rw [RMod.Classification.pullbackSimpleDegree_placed] at hs ht
  by_cases hg : k.1 = g
  · have hh : k.2 ≠ h := fun e => hk (Prod.ext hg e)
    exact RMod.Classification.tensor_id_zero_right referenceProperty.toWeaklyPointedSuperfusionLaws
      _ (ht k.2 hh)
  · exact RMod.Classification.tensor_id_zero_left referenceProperty.toWeaklyPointedSuperfusionLaws
      (hs k.1 hg) _

/-- The distinguished component is nonzero because both factors are simple. -/
theorem exteriorGenerator_coordinate_ne_zero (s t : Twist) (g : s.group) (h : t.group) :
    reference.data.id ((exteriorGenerator s t g h) (g, h)).val ≠ reference.data.zero := by
  exact RMod.Classification.tensor_id_ne_zero (C := reference.toWeaklyPointedSuperfusion)
    (RMod.Classification.simple_id_ne_zero referenceProperty.toWeaklyPointedSuperfusionLaws
      (RMod.Classification.pullbackDegreeSimple_coordinate reference.data referenceProperty (oldTwist s) g))
    (RMod.Classification.simple_id_ne_zero referenceProperty.toWeaklyPointedSuperfusionLaws
      (RMod.Classification.pullbackDegreeSimple_coordinate reference.data referenceProperty (oldTwist t) h))

/-- Nonzero in one coordinate is nonzero in the even category. -/
theorem exteriorGenerator_id_ne_zero (s t : Twist) (g : s.group) (h : t.group) :
    𝟙 (exteriorGenerator s t g h) ≠ 0 := by
  intro he
  let P := oldPullback (exteriorTwist s t).val
  let F := evenForget P.toWeaklyPointedSuperfusion
  have he' := congrArg (fun f => (F.map f).hom (g, h)) he
  rw [F.map_id, F.map_zero] at he'
  exact exteriorGenerator_coordinate_ne_zero s t g h he'

/-- A simple retract of an object supported at k has label k. -/
theorem simple_retract_supported (s : Twist) (k : s.group) (W X : Even (pullback s))
    (hX : Simple X) (r : Retract X W)
    (hW : ∀ j, j ≠ k → reference.data.id (W j).val = reference.data.zero) :
    SameParityOrbit (pullback s) X (pullbackSimple s k) := by
  let P := oldPullback s
  let S : RMod.Classification.SimpleObject P.toWeaklyPointedSuperfusion :=
    ⟨⟨X⟩, ⟨(fromOld_simple P X).mpr hX⟩⟩
  let j := RMod.Classification.pullbackSimpleDegree reference.data referenceProperty (oldTwist s) S
  have hj : j = k := by
    by_contra hj
    let F := evenForget P.toWeaklyPointedSuperfusion
    let q := r.map F
    have hz := RMod.Classification.hom_eq_zero_of_target
      referenceProperty.toWeaklyPointedSuperfusionLaws (hW j hj) (q.i.hom j)
    have he : reference.data.comp (q.i.hom j) (q.r.hom j) = reference.data.id (X j).val :=
      congrFun (congrArg (fun f => f.hom) q.retract) j
    rw [hz] at he
    exact RMod.Classification.simple_id_ne_zero referenceProperty.toWeaklyPointedSuperfusionLaws
      (RMod.Classification.pullbackSimpleDegree_simple reference.data referenceProperty (oldTwist s) S)
      (he.symm.trans (RMod.Classification.raw_zero_comp referenceProperty.toWeaklyPointedSuperfusionLaws _))
  apply (fromOld_orbit P _ _).mp
  apply (RMod.Classification.pullbackSimpleDegree_eq_iff reference.data referenceProperty
    (oldTwist s) S (RMod.Classification.pullbackDegreeSimple reference.data referenceProperty (oldTwist s) k)).mp
  exact hj.trans (RMod.Classification.pullbackSimpleDegree_placed reference.data referenceProperty (oldTwist s) k).symm

/-- Semisimplicity supplies an actual simple even retract of every nonzero object. -/
theorem exists_simple_retract (C : WeaklyPointedFusionPiSuperCat) (X : Even C)
    (hX : 𝟙 X ≠ 0) : ∃ S : Even C, Simple S ∧ Nonempty (Retract S X) := by
  classical
  obtain ⟨n, S, hS, ⟨e⟩⟩ := FusionPiSuperCategory.semisimple (C := C) X
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hz : 𝟙 (⨁ S) = 0 := by
      apply biproduct.hom_ext
      intro j
      exact Fin.elim0 j
    apply hX
    calc
      𝟙 X = e.hom ≫ 𝟙 (⨁ S) ≫ e.inv := by simp
      _ = 0 := by rw [hz]; simp
  let i : Fin n := ⟨0, hn⟩
  exact ⟨S i, hS i, ⟨{
    i := biproduct.ι S i ≫ e.inv
    r := e.hom ≫ biproduct.π S i
    retract := by simp [Category.assoc] }⟩⟩

end RMod.BrundanEllis.Stacking

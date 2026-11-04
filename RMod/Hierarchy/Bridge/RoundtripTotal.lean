import RMod.Hierarchy.Bridge.RoundtripSuperfunctors
import RMod.Hierarchy.Bridge.TensorComponents
import RMod.Hierarchy.Instances.TotalFunctor

/-!
# Total-coordinate identities for the round trip

The old total Hom equivalence is precisely the backward coordinate map.
The forward coordinate map is its inverse, so no morphism information is
lost in recovering and re-enriching a category.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (A : WeaklyPointedFusionPiSupercategory)

theorem roundtripForward_total {X Y : A.data.Obj} (f : THom (originalSuper A).data X Y) :
    totalHomEquiv (legacyCategory A) X Y (tMap (roundtripForwardData A) f) = f := by
  funext a
  change Pi.single (M := fun b => A.data.Hom X Y b) 0 (f 0) a +
    Pi.single (M := fun b => A.data.Hom X Y b) 1 (f 1) a = f a
  rcases Classification.parity_cases a with rfl | rfl <;> simp

theorem roundtripBackward_total {X Y : A.data.Obj}
    (f : THom (ofOldSupercategoryData (legacyCategory A)) X Y) :
    tMap (roundtripBackwardData A) f = totalHomEquiv (legacyCategory A) X Y f := by
  funext a
  rcases Classification.parity_cases a with rfl | rfl
  · change (f 0).val 0 = (f 0).val 0 + (f 1).val 0
    have h : (f 1).val 0 = 0 := (f 1).property 0 zero_ne_one
    rw [h, add_zero]
  · change (f 1).val 1 = (f 0).val 1 + (f 1).val 1
    have h : (f 0).val 1 = 0 := (f 0).property 1 one_ne_zero
    rw [h, zero_add]

theorem roundtrip_unit_map {X Y : A.data.Obj} (f : THom (originalSuper A).data X Y) :
    tMap (roundtripBackwardData A) (tMap (roundtripForwardData A) f) = f := by
  rw [roundtripBackward_total, roundtripForward_total]

theorem roundtrip_counit_map {X Y : A.data.Obj}
    (f : THom (ofOldSupercategoryData (legacyCategory A)) X Y) :
    tMap (roundtripForwardData A) (tMap (roundtripBackwardData A) f) = f := by
  apply (totalHomEquiv (legacyCategory A) X Y).injective
  rw [roundtripForward_total, roundtripBackward_total]

theorem roundtripForward_even {X Y : Even (originalSuper A)} (f : X ⟶ Y) :
    (evenHomEquiv (legacyCategory A) X Y
      ((Superfunctor.enriched (roundtripForward A)).forget.map f)).hom = evenPoint f := by
  change (evenPoint ((Superfunctor.enriched (roundtripForward A)).forget.map f) 0).val = _
  rw [← totalHomEquiv_even]
  change totalHomEquiv (legacyCategory A) X Y
    (evenPoint (f ≫ (roundtripForwardData A).map X Y)) = _
  have h := tMap_evenPoint (roundtripForward A) f
  exact (congrArg (totalHomEquiv (legacyCategory A) X Y) h.symm).trans
    (roundtripForward_total A (evenPoint f))

end RMod.Legacy.Hierarchy

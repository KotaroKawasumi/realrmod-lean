import RMod.BrundanEllis.StackingIntrinsicOrbits
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.GroupTheory.OrderOfElement

/-! A tensor-closed completion determines a subgroup of the intrinsic finite
group of simple parity orbits. Finiteness supplies inverse closure from
multiplicative closure; no separate marking or inverse-closure assumption
is attached to the category. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification
variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)
  [ObjectProperty.IsMonoidal (AddPiHull C Z)]

/-- A selected simple constituent of a tensor in the hull remains in the hull. -/
theorem tensor_representative_mem
    (X Y : SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion)
    (hX : AddPiHull C Z (evenObj C X.data.object))
    (hY : AddPiHull C Z (evenObj C Y.data.object)) :
    AddPiHull C Z (evenObj C
      (simpleTensorRepresentative (intrinsicOld C).toWeaklyPointedSuperfusion X Y).data.object) := by
  let A := (intrinsicOld C).toWeaklyPointedSuperfusion
  let d := simpleDecomposition A (A.data.tensorObj X.data.object Y.data.object)
  obtain ⟨e⟩ := (intrinsic_decomposition C _ d.data.summand).mp d.hasDecomposition
  let j := tensorSimpleIndex A X Y
  apply AddPiHull.of_retract (Y := evenObj C (A.data.tensorObj X.data.object Y.data.object))
  · exact {
      i := biproduct.ι (fun i => evenObj C (d.data.summand i)) j ≫ e.inv
      r := e.hom ≫ biproduct.π (fun i => evenObj C (d.data.summand i)) j
      retract := by simp [Category.assoc]; rfl }
  · exact ObjectProperty.prop_tensor hX hY

/-- Membership records an actual simple object in the completion. -/
def hullSupportMonoid : Submonoid (intrinsicOrbitGroup C) where
  carrier a := ∃ S : SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion,
    simpleOrbitMk _ S = a ∧ AddPiHull C Z (evenObj C S.data.object)
  one_mem' := ⟨unitSimple _, rfl, ObjectProperty.prop_unit (AddPiHull C Z)⟩
  mul_mem' := by
    rintro a b ⟨X, rfl, hX⟩ ⟨Y, rfl, hY⟩
    exact ⟨simpleTensorRepresentative _ X Y, rfl, tensor_representative_mem C Z X Y hX hY⟩

theorem hullSupport_mk_iff (X : SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion) :
    simpleOrbitMk _ X ∈ hullSupportMonoid C Z ↔ AddPiHull C Z (evenObj C X.data.object) := by
  constructor
  · rintro ⟨Y, he, hY⟩
    have h := Quotient.exact he
    exact AddPiHull.of_orbit ((intrinsic_orbit C _ _).mp h) hY
  · intro h
    exact ⟨X, rfl, h⟩

/-- In a finite group an inverse is a nonnegative power, so no new objects
need to be postulated for inverse parity classes. -/
def hullSupportGroup : Subgroup (intrinsicOrbitGroup C) :=
  { hullSupportMonoid C Z with
    inv_mem' := by
      intro a ha
      change a⁻¹ ∈ hullSupportMonoid C Z
      rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a, ← pow_sub a (orderOf_pos a)]
      exact (hullSupportMonoid C Z).pow_mem ha (orderOf a - 1) }

/-- An actual dual pairing makes the two simple parity classes inverse. -/
theorem simple_pairing_mul_eq_one
    (X Y : SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion)
    (p : DualPairing (intrinsicOld C).toWeaklyPointedSuperfusion X.data.object Y.data.object) :
    (simpleOrbitMk _ X : intrinsicOrbitGroup C) * simpleOrbitMk _ Y = 1 := by
  let A := (intrinsicOld C).toWeaklyPointedSuperfusion
  apply Quotient.sound
  exact RMod.Classification.SameParityOrbit.symm
    (simple_orbit_of_map_to_tensor A X Y A.laws.simple_unit p.data.coeval p.laws.coeval_even
      (p.coeval_ne_zero (simple_id_ne_zero A.laws X.laws.simple)))

/-- The right dual of a simple member lies in the same completed family. -/
theorem simple_pairing_right_mem
    (X Y : SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion)
    (p : DualPairing (intrinsicOld C).toWeaklyPointedSuperfusion X.data.object Y.data.object)
    (hX : AddPiHull C Z (evenObj C X.data.object)) :
    AddPiHull C Z (evenObj C Y.data.object) := by
  apply (hullSupport_mk_iff C Z Y).mp
  change (simpleOrbitMk _ Y : intrinsicOrbitGroup C) ∈ hullSupportGroup C Z
  rw [eq_inv_of_mul_eq_one_right (simple_pairing_mul_eq_one C X Y p)]
  exact (hullSupportGroup C Z).inv_mem ((hullSupport_mk_iff C Z X).mpr hX)

/-- The same argument applies to the left member of an actual dual pairing. -/
theorem simple_pairing_left_mem
    (X Y : SimpleObject (intrinsicOld C).toWeaklyPointedSuperfusion)
    (p : DualPairing (intrinsicOld C).toWeaklyPointedSuperfusion X.data.object Y.data.object)
    (hY : AddPiHull C Z (evenObj C Y.data.object)) :
    AddPiHull C Z (evenObj C X.data.object) := by
  apply (hullSupport_mk_iff C Z X).mp
  change (simpleOrbitMk _ X : intrinsicOrbitGroup C) ∈ hullSupportGroup C Z
  rw [eq_inv_of_mul_eq_one_left (simple_pairing_mul_eq_one C X Y p)]
  exact (hullSupportGroup C Z).inv_mem ((hullSupport_mk_iff C Z Y).mpr hY)

end RMod.BrundanEllis.Stacking

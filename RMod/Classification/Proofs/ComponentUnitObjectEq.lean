import RMod.Classification.Instances.ComponentSystemUnit
import RMod.Classification.Instances.UnitGeneratorMaps
import Batteries.Tactic.GeneralizeProofs

/-!
# The unit product index identifies the actual component images

The product component at 1*g (or g*1) is the component at g. The
underlying object comparison retains this equality even though the two
full-subcategory presentations have different membership proofs.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))

theorem componentLeftUnitObject_eq (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object
      (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object
      (T (1 * g)).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object) :
    ((componentProductEquivalence d 1 g hS hT).forwardFunctor.data.obj
      (spanTensorObj A (S 1) (S g) (spanGenerator A (S 1).data.object) Y)).obj =
      ((d.component g).forwardFunctor.data.obj
        (leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y)).obj := by
  change ((d.component (1 * g)).forwardFunctor.data.obj
    ⟨A.data.tensorObj (S 1).data.object Y.obj, _⟩).obj = _
  generalize_proofs hmem
  revert hmem
  rw [one_mul]
  intro hmem
  rfl

theorem componentRightUnitObject_eq (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object
      (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object
      (T (g * 1)).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object) :
    ((componentProductEquivalence d g 1 hS hT).forwardFunctor.data.obj
      (spanTensorObj A (S g) (S 1) Y (spanGenerator A (S 1).data.object))).obj =
      ((d.component g).forwardFunctor.data.obj
        (rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y)).obj := by
  change ((d.component (g * 1)).forwardFunctor.data.obj
    ⟨A.data.tensorObj Y.obj (S 1).data.object, _⟩).obj = _
  generalize_proofs hmem
  revert hmem
  rw [mul_one]
  intro hmem
  rfl

/-- The product-index equality also holds for an arbitrary neutral-component object. -/
theorem componentLeftUnitObject_eq_at (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object
      (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object
      (T (1 * g)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (hXY : InHomogeneousSpan A (S g).data.object (A.data.tensorObj X.obj Y.obj)) :
    ((componentProductEquivalence d 1 g hS hT).forwardFunctor.data.obj
      (spanTensorObj A (S 1) (S g) X Y)).obj =
      ((d.component g).forwardFunctor.data.obj ⟨A.data.tensorObj X.obj Y.obj, hXY⟩).obj := by
  change ((d.component (1 * g)).forwardFunctor.data.obj ⟨A.data.tensorObj X.obj Y.obj, _⟩).obj = _
  generalize_proofs hmem
  revert hmem
  rw [one_mul]
  intro hmem
  rfl

/-- The product-index equality also holds for an arbitrary neutral-component object. -/
theorem componentRightUnitObject_eq_at (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object
      (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object
      (T (g * 1)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (hXY : InHomogeneousSpan A (S g).data.object (A.data.tensorObj Y.obj X.obj)) :
    ((componentProductEquivalence d g 1 hS hT).forwardFunctor.data.obj
      (spanTensorObj A (S g) (S 1) Y X)).obj =
      ((d.component g).forwardFunctor.data.obj ⟨A.data.tensorObj Y.obj X.obj, hXY⟩).obj := by
  change ((d.component (g * 1)).forwardFunctor.data.obj ⟨A.data.tensorObj Y.obj X.obj, _⟩).obj = _
  generalize_proofs hmem
  revert hmem
  rw [mul_one]
  intro hmem
  rfl

end RMod.Classification

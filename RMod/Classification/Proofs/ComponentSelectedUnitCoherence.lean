import RMod.Classification.Proofs.ComponentUnitIsoCoherence
import RMod.Classification.Proofs.ComponentUnitIsoMap

/-!
# The unit diagram for arbitrary selected neutral-component data

The mapped source equation identifies the inverse transport in the
generator diagram with the actual chosen source unitor. Only the even
isomorphism to the unit generator and that source equation are used.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C} (p : Pi C.data)
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))

theorem componentLeftSelectedUnit_coherence (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object (T (1 * g)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (hXY : InHomogeneousSpan A (S g).data.object (A.data.tensorObj X.obj Y.obj))
    (e : IsoData A.data (S 1).data.object X.obj) (he : EvenIsoLaws A.data e)
    (f : A.data.Hom (A.data.tensorObj X.obj Y.obj) Y.obj)
    (hf : A.data.comp (A.data.tensorHom e.inv (A.data.id Y.obj)) (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom = f) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.comp d.data.unitIso.hom ((d.component 1).forwardFunctor.data.map (ObjectProperty.homMk e.hom : spanGenerator A (S 1).data.object ⟶ X)).hom) (C.data.id ((d.component g).forwardFunctor.data.obj Y).obj)) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (d.leftUnitComparison g hS hT)).data.app X Y).hom)
      (C.data.comp (IsoData.ofEq C.data (componentLeftUnitObject_eq_at d g hS hT X Y hXY)).hom
        ((d.component g).forwardFunctor.data.map
          (ObjectProperty.homMk f : ⟨A.data.tensorObj X.obj Y.obj, hXY⟩ ⟶ Y)).hom) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit ((d.component g).forwardFunctor.data.obj Y).obj))
        (C.data.leftUnitorHom ((d.component g).forwardFunctor.data.obj Y).obj) := by
  rw [← componentLeftUnitIso_map d g hS hT X Y hXY e f hf]
  exact componentLeftUnitIso_coherence p d g hS hT X Y e he

theorem componentRightSelectedUnit_coherence (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object (T (g * 1)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (hXY : InHomogeneousSpan A (S g).data.object (A.data.tensorObj Y.obj X.obj))
    (e : IsoData A.data (S 1).data.object X.obj) (he : EvenIsoLaws A.data e)
    (f : A.data.Hom (A.data.tensorObj Y.obj X.obj) Y.obj)
    (hf : A.data.comp (A.data.tensorHom (A.data.id Y.obj) e.inv) (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom = f) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id ((d.component g).forwardFunctor.data.obj Y).obj) (C.data.comp d.data.unitIso.hom ((d.component 1).forwardFunctor.data.map (ObjectProperty.homMk e.hom : spanGenerator A (S 1).data.object ⟶ X)).hom)) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (d.rightUnitComparison g hS hT)).data.app Y X).hom)
      (C.data.comp (IsoData.ofEq C.data (componentRightUnitObject_eq_at d g hS hT X Y hXY)).hom
        ((d.component g).forwardFunctor.data.map
          (ObjectProperty.homMk f : ⟨A.data.tensorObj Y.obj X.obj, hXY⟩ ⟶ Y)).hom) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj ((d.component g).forwardFunctor.data.obj Y).obj C.data.tensorUnit))
        (C.data.rightUnitorHom ((d.component g).forwardFunctor.data.obj Y).obj) := by
  rw [← componentRightUnitIso_map d g hS hT X Y hXY e f hf]
  exact componentRightUnitIso_coherence p d g hS hT X Y e he

end RMod.Classification

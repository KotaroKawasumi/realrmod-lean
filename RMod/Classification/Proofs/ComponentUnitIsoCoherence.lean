import RMod.Classification.Proofs.ComponentUnitGeneratorCoherence
import RMod.Classification.Proofs.ParityTensorComparisonUnitTransport

/-!
# Unit coherence on a chosen object in the neutral component

An even isomorphism from the normalized generator supplies the actual
unit comparison. Tensorator naturality transports the established unit
diagram to this object; the inverse is retained in the source diagram.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C} (p : Pi C.data)
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))

theorem componentLeftUnitIso_coherence (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object
      (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object
      (T (1 * g)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (e : IsoData A.data (S 1).data.object X.obj) (he : EvenIsoLaws A.data e) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.comp d.data.unitIso.hom ((d.component 1).forwardFunctor.data.map (ObjectProperty.homMk e.hom : spanGenerator A (S 1).data.object ⟶ X)).hom) (C.data.id ((d.component g).forwardFunctor.data.obj Y).obj)) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (d.leftUnitComparison g hS hT)).data.app X Y).hom)
      (C.data.comp
        ((componentProductEquivalence d 1 g hS hT).forwardFunctor.data.map (spanTensorHom A (S 1) (S g) (ObjectProperty.homMk e.inv : X ⟶ spanGenerator A (S 1).data.object) (𝟙 Y))).hom
        (C.data.comp (IsoData.ofEq C.data (componentLeftUnitObject_eq d g hS hT Y)).hom
          ((d.component g).forwardFunctor.data.map
            (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom :
              leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom)) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit ((d.component g).forwardFunctor.data.obj Y).obj))
        (C.data.leftUnitorHom ((d.component g).forwardFunctor.data.obj Y).obj) := by
  exact ((parityTensorComparison p (d.leftUnitComparison g hS hT)).inserted_iso_transport_left
    Y e he d.data.unitIso.hom _).trans (componentLeftUnitGenerator_coherence p d g hS hT Y)

theorem componentRightUnitIso_coherence (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object
      (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object
      (T (g * 1)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (e : IsoData A.data (S 1).data.object X.obj) (he : EvenIsoLaws A.data e) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id ((d.component g).forwardFunctor.data.obj Y).obj) (C.data.comp d.data.unitIso.hom ((d.component 1).forwardFunctor.data.map (ObjectProperty.homMk e.hom : spanGenerator A (S 1).data.object ⟶ X)).hom)) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (d.rightUnitComparison g hS hT)).data.app Y X).hom)
      (C.data.comp
        ((componentProductEquivalence d g 1 hS hT).forwardFunctor.data.map (spanTensorHom A (S g) (S 1) (𝟙 Y) (ObjectProperty.homMk e.inv : X ⟶ spanGenerator A (S 1).data.object))).hom
        (C.data.comp (IsoData.ofEq C.data (componentRightUnitObject_eq d g hS hT Y)).hom
          ((d.component g).forwardFunctor.data.map
            (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom :
              rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom)) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj ((d.component g).forwardFunctor.data.obj Y).obj C.data.tensorUnit))
        (C.data.rightUnitorHom ((d.component g).forwardFunctor.data.obj Y).obj) := by
  exact ((parityTensorComparison p (d.rightUnitComparison g hS hT)).inserted_iso_transport_right
    Y e he d.data.unitIso.hom _).trans (componentRightUnitGenerator_coherence p d g hS hT Y)

end RMod.Classification

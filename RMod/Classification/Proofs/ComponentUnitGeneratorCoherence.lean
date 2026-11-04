import RMod.Classification.Proofs.ComponentUnitObjectEq
import RMod.Classification.Proofs.ParityUnitGeneratorCoherence

/-!
# Unit diagrams with the actual product-component equality maps

The binary comparison lands in the product-indexed component. Retain
the equality map to the unit-reduced component before mapping the
source unitor. This is the comparison used by the global tensorator.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C} (p : Pi C.data)
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))

theorem componentLeftUnitGenerator_coherence (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object
      (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object
      (T (1 * g)).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom d.data.unitIso.hom
        (C.data.id ((d.component g).forwardFunctor.data.obj Y).obj)) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (d.leftUnitComparison g hS hT)).data.app
        (spanGenerator A (S 1).data.object) Y).hom)
      (C.data.comp (IsoData.ofEq C.data (componentLeftUnitObject_eq d g hS hT Y)).hom
        ((d.component g).forwardFunctor.data.map
          (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom :
            leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom) =
      C.data.comp (C.data.rightUnitorHom
        (C.data.tensorObj C.data.tensorUnit ((d.component g).forwardFunctor.data.obj Y).obj))
        (C.data.leftUnitorHom ((d.component g).forwardFunctor.data.obj Y).obj) := by
  unfold ComponentSystem.leftUnitComparison componentProductEquivalence
  generalize_proofs hfun hunit hsource hobj
  revert hS hT hfun hobj
  rw [one_mul]
  intro hS hT hfun hobj
  have hm : C.data.comp (IsoData.ofEq C.data hobj).hom
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) hsource Y.obj).hom :
          leftUnitGeneratorSpan A (S 1) (S g) hsource Y ⟶ Y)).hom =
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) hsource Y.obj).hom :
          leftUnitGeneratorSpan A (S 1) (S g) hsource Y ⟶ Y)).hom := C.laws.id_comp _
  rw [hm]
  exact parityLeftUnitGenerator_coherence p (S 1) (S g) (T 1) (T g)
    (d.component 1) (d.component g) hunit hsource hS hT Y

theorem componentRightUnitGenerator_coherence (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object
      (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object
      (T (g * 1)).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id ((d.component g).forwardFunctor.data.obj Y).obj)
        d.data.unitIso.hom) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (d.rightUnitComparison g hS hT)).data.app
        Y (spanGenerator A (S 1).data.object)).hom)
      (C.data.comp (IsoData.ofEq C.data (componentRightUnitObject_eq d g hS hT Y)).hom
        ((d.component g).forwardFunctor.data.map
          (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom :
            rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom) =
      C.data.comp (C.data.rightUnitorHom
        (C.data.tensorObj ((d.component g).forwardFunctor.data.obj Y).obj C.data.tensorUnit))
        (C.data.rightUnitorHom ((d.component g).forwardFunctor.data.obj Y).obj) := by
  unfold ComponentSystem.rightUnitComparison componentProductEquivalence
  generalize_proofs hfun hunit hsource hobj
  revert hS hT hfun hobj
  rw [mul_one]
  intro hS hT hfun hobj
  have hm : C.data.comp (IsoData.ofEq C.data hobj).hom
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) hsource Y.obj).hom :
          rightUnitGeneratorSpan A (S 1) (S g) hsource Y ⟶ Y)).hom =
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) hsource Y.obj).hom :
          rightUnitGeneratorSpan A (S 1) (S g) hsource Y ⟶ Y)).hom := C.laws.id_comp _
  rw [hm]
  exact parityRightUnitGenerator_coherence p (S 1) (S g) (T 1) (T g)
    (d.component 1) (d.component g) hunit hsource hS hT Y

end RMod.Classification

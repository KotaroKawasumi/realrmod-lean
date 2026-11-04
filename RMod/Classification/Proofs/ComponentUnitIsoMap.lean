import RMod.Classification.Proofs.ComponentUnitObjectEq
import RMod.Classification.Instances.SpanTensorFunctors

/-!
# Mapping the selected source-unit diagram through the product component

A source equation can be mapped before or after identifying the product
index with the fixed degree. The two specified equality maps make these
routes agree, including when the chosen neutral object is not the generator.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))

theorem componentLeftUnitIso_map (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object (T (1 * g)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (hXY : InHomogeneousSpan A (S g).data.object (A.data.tensorObj X.obj Y.obj))
    (e : IsoData A.data (S 1).data.object X.obj) (f : A.data.Hom (A.data.tensorObj X.obj Y.obj) Y.obj)
    (hf : A.data.comp (A.data.tensorHom e.inv (A.data.id Y.obj)) (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom = f) :
    C.data.comp
      ((componentProductEquivalence d 1 g hS hT).forwardFunctor.data.map (spanTensorHom A (S 1) (S g) (ObjectProperty.homMk e.inv : X ⟶ spanGenerator A (S 1).data.object) (𝟙 Y))).hom
      (C.data.comp (IsoData.ofEq C.data (componentLeftUnitObject_eq d g hS hT Y)).hom
        ((d.component g).forwardFunctor.data.map (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom) =
    C.data.comp (IsoData.ofEq C.data (componentLeftUnitObject_eq_at d g hS hT X Y hXY)).hom
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk f : ⟨A.data.tensorObj X.obj Y.obj, hXY⟩ ⟶ Y)).hom := by
  unfold componentProductEquivalence
  generalize_proofs hsource hOld hNew
  revert hS hT hOld hNew
  rw [one_mul]
  intro hS hT hOld hNew
  have hiOld : C.data.comp (IsoData.ofEq C.data hOld).hom
      ((d.component g).forwardFunctor.data.map (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom =
      ((d.component g).forwardFunctor.data.map (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom := C.laws.id_comp _
  have hiNew : C.data.comp (IsoData.ofEq C.data hNew).hom
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk f : ⟨A.data.tensorObj X.obj Y.obj, hXY⟩ ⟶ Y)).hom =
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk f : ⟨A.data.tensorObj X.obj Y.obj, hXY⟩ ⟶ Y)).hom := C.laws.id_comp _
  rw [hiOld, hiNew]
  have hm := congrArg (fun m => m.hom) ((d.component g).forwardFunctor.laws.map_comp
    (ObjectProperty.homMk (A.data.tensorHom e.inv (A.data.id Y.obj)) : ⟨A.data.tensorObj X.obj Y.obj, hXY⟩ ⟶ leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y)
    (ObjectProperty.homMk (leftUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : leftUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y))
  exact hm.symm.trans (congrArg (fun m => ((d.component g).forwardFunctor.data.map m).hom)
    (ObjectProperty.hom_ext _ hf))

theorem componentRightUnitIso_map (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object (T (g * 1)).data.object)
    (X : HomogeneousSpanCategory A (S 1).data.object)
    (Y : HomogeneousSpanCategory A (S g).data.object)
    (hXY : InHomogeneousSpan A (S g).data.object (A.data.tensorObj Y.obj X.obj))
    (e : IsoData A.data (S 1).data.object X.obj) (f : A.data.Hom (A.data.tensorObj Y.obj X.obj) Y.obj)
    (hf : A.data.comp (A.data.tensorHom (A.data.id Y.obj) e.inv) (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom = f) :
    C.data.comp
      ((componentProductEquivalence d g 1 hS hT).forwardFunctor.data.map (spanTensorHom A (S g) (S 1) (𝟙 Y) (ObjectProperty.homMk e.inv : X ⟶ spanGenerator A (S 1).data.object))).hom
      (C.data.comp (IsoData.ofEq C.data (componentRightUnitObject_eq d g hS hT Y)).hom
        ((d.component g).forwardFunctor.data.map (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom) =
    C.data.comp (IsoData.ofEq C.data (componentRightUnitObject_eq_at d g hS hT X Y hXY)).hom
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk f : ⟨A.data.tensorObj Y.obj X.obj, hXY⟩ ⟶ Y)).hom := by
  unfold componentProductEquivalence
  generalize_proofs hsource hOld hNew
  revert hS hT hOld hNew
  rw [mul_one]
  intro hS hT hOld hNew
  have hiOld : C.data.comp (IsoData.ofEq C.data hOld).hom
      ((d.component g).forwardFunctor.data.map (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom =
      ((d.component g).forwardFunctor.data.map (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y)).hom := C.laws.id_comp _
  have hiNew : C.data.comp (IsoData.ofEq C.data hNew).hom
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk f : ⟨A.data.tensorObj Y.obj X.obj, hXY⟩ ⟶ Y)).hom =
      ((d.component g).forwardFunctor.data.map
        (ObjectProperty.homMk f : ⟨A.data.tensorObj Y.obj X.obj, hXY⟩ ⟶ Y)).hom := C.laws.id_comp _
  rw [hiOld, hiNew]
  have hm := congrArg (fun m => m.hom) ((d.component g).forwardFunctor.laws.map_comp
    (ObjectProperty.homMk (A.data.tensorHom (A.data.id Y.obj) e.inv) : ⟨A.data.tensorObj Y.obj X.obj, hXY⟩ ⟶ rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y)
    (ObjectProperty.homMk (rightUnitGeneratorMap A (S 1) (SimpleObject.ext d.laws.source_unit) Y.obj).hom : rightUnitGeneratorSpan A (S 1) (S g) (SimpleObject.ext d.laws.source_unit) Y ⟶ Y))
  exact hm.symm.trans (congrArg (fun m => ((d.component g).forwardFunctor.data.map m).hom)
    (ObjectProperty.hom_ext _ hf))

end RMod.Classification

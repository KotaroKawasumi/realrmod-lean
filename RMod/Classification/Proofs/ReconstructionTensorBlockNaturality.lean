import RMod.Classification.Instances.ReconstructionTensorator
import RMod.Classification.Instances.ReconstructionTensorComponentMaps
import RMod.Classification.Proofs.ParityTensorComparisonNaturality
import RMod.Classification.Proofs.IndexedFullSubcategoryFunctor
import RMod.Classification.Proofs.EvenEqualityMaps

/-!
# Naturality of the actual tensorator blocks on full Hom spaces

The binary comparison supplies naturality before changing the output
degree. Equality of the product degree with the selected degree gives a
natural equality comparison of the same component functor. Composing
these two squares proves naturality for the exact convolution block.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  {X X' Y Y' : LinearCategory A.toWeaklyPointedSuperfusion}

theorem reconstructionTensorBlock_naturality (f : X ⟶ X') (h : Y ⟶ Y')
    (g k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.comp (twistSummandHom C.data (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map f)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map h) g k)
      (reconstructionTensorBlock A C hC X' Y' g k).hom.hom =
    C.data.comp (reconstructionTensorBlock A C hC X Y g k).hom.hom
      ((reconstructionComponentRealization A C hC (g * k)).map (reconstructionTensorSpanMap A f h g k)) :=
  (reconstructionTensorComparison A C hC g k).naturality_all
    ((reconstructionSourceEquivalence A).inverse.map f g)
    ((reconstructionSourceEquivalence A).inverse.map h k)

theorem reconstructionTensorOutputIndex_naturality (f : X ⟶ X') (h : Y ⟶ Y')
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionComponentRealization A C hC (g * (g⁻¹ * k))).map
        (reconstructionTensorSpanMap A f h g (g⁻¹ * k)) ≫
        eqToHom (reconstructionTensorOutputRealization_obj A C hC X' Y' k g).symm =
      eqToHom (reconstructionTensorOutputRealization_obj A C hC X Y k g).symm ≫
        (reconstructionComponentRealization A C hC k).map (reconstructionTensorOutputSpanMap A f h k g) :=
  indexedFullSubcategoryFunctor_eq_naturality
    (fun q => InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion q).data.object)
    (reconstructionComponentRealization A C hC) (mul_inv_cancel_left g k)
    (reconstructionTensorSpanObject A X Y g (g⁻¹ * k)).property
    (reconstructionTensorSpanObject A X' Y' g (g⁻¹ * k)).property
    (reconstructionTensorOutputSpan A X Y k g).property
    (reconstructionTensorOutputSpan A X' Y' k g).property
    (A.data.tensorHom ((reconstructionSourceEquivalence A).inverse.map f g).hom
      ((reconstructionSourceEquivalence A).inverse.map h (g⁻¹ * k)).hom) _ _

theorem reconstructionConvolutionBlockIso_naturality (f : X ⟶ X') (h : Y ⟶ Y')
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.comp (twistSummandHom C.data (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map f)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map h) g (g⁻¹ * k))
      (reconstructionConvolutionBlockIso A C hC X' Y' k g).hom.hom =
    C.data.comp (reconstructionConvolutionBlockIso A C hC X Y k g).hom.hom
      ((reconstructionComponentRealization A C hC k).map (reconstructionTensorOutputSpanMap A f h k g)) := by
  let sx : C.data.Obj := twistSummand C.data (reconstructionTwistData A C hC)
    ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
    ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) g (g⁻¹ * k)
  let sy : C.data.Obj := twistSummand C.data (reconstructionTwistData A C hC)
    ((reconstructionUnderlyingEquivalence A C hC).functor.obj X')
    ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y') g (g⁻¹ * k)
  let px : C.data.Obj := (reconstructionComponentRealization A C hC (g * (g⁻¹ * k))).obj
    (reconstructionTensorSpanObject A X Y g (g⁻¹ * k))
  let py : C.data.Obj := (reconstructionComponentRealization A C hC (g * (g⁻¹ * k))).obj
    (reconstructionTensorSpanObject A X' Y' g (g⁻¹ * k))
  let qx : C.data.Obj := (reconstructionComponentRealization A C hC k).obj (reconstructionTensorOutputSpan A X Y k g)
  let qy : C.data.Obj := (reconstructionComponentRealization A C hC k).obj (reconstructionTensorOutputSpan A X' Y' k g)
  let ex : px = qx := (reconstructionTensorOutputRealization_obj A C hC X Y k g).symm
  let ey : py = qy := (reconstructionTensorOutputRealization_obj A C hC X' Y' k g).symm
  let eqx : C.data.Hom px qx := (eqToHom ex : @Quiver.Hom (LinearCategory C.toWeaklyPointedSuperfusion) _ px qx)
  let eqy : C.data.Hom py qy := (eqToHom ey : @Quiver.Hom (LinearCategory C.toWeaklyPointedSuperfusion) _ py qy)
  let eqxe : referenceEvenObj C.data hC px ⟶ referenceEvenObj C.data hC qx :=
    eqToHom (congrArg (referenceEvenObj C.data hC) ex)
  let eqye : referenceEvenObj C.data hC py ⟶ referenceEvenObj C.data hC qy :=
    eqToHom (congrArg (referenceEvenObj C.data hC) ey)
  have hex : eqxe.hom = eqx := even_eqToHom_hom C.toWeaklyPointedSuperfusion ex
  have hey : eqye.hom = eqy := even_eqToHom_hom C.toWeaklyPointedSuperfusion ey
  let u : C.data.Hom sx px := (reconstructionTensorBlock A C hC X Y g (g⁻¹ * k)).hom.hom
  let v : C.data.Hom sy py := (reconstructionTensorBlock A C hC X' Y' g (g⁻¹ * k)).hom.hom
  let s : C.data.Hom sx sy := twistSummandHom C.data (reconstructionTwistData A C hC)
    ((reconstructionUnderlyingEquivalence A C hC).functor.map f)
    ((reconstructionUnderlyingEquivalence A C hC).functor.map h) g (g⁻¹ * k)
  let m : C.data.Hom px py := (reconstructionComponentRealization A C hC (g * (g⁻¹ * k))).map
    (reconstructionTensorSpanMap A f h g (g⁻¹ * k))
  let n : C.data.Hom qx qy := (reconstructionComponentRealization A C hC k).map
    (reconstructionTensorOutputSpanMap A f h k g)
  have hbase : C.data.comp s v = C.data.comp u m := reconstructionTensorBlock_naturality A C hC f h g (g⁻¹ * k)
  have hi : C.data.comp m eqy = C.data.comp eqx n := reconstructionTensorOutputIndex_naturality A C hC f h k g
  change C.data.comp s (C.data.comp v eqye.hom) = C.data.comp (C.data.comp u eqxe.hom) n
  rw [hex, hey]
  calc
    _ = C.data.comp (C.data.comp s v) eqy := (C.laws.comp_assoc _ _ _).symm
    _ = C.data.comp (C.data.comp u m) eqy := congrArg (fun z => C.data.comp z eqy) hbase
    _ = C.data.comp u (C.data.comp m eqy) := C.laws.comp_assoc _ _ _
    _ = C.data.comp u (C.data.comp eqx n) := congrArg (C.data.comp u) hi
    _ = _ := (C.laws.comp_assoc _ _ _).symm

end RMod.Classification

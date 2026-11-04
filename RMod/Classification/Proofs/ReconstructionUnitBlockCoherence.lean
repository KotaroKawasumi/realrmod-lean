import RMod.Classification.Proofs.ReconstructionUnitSummandCoherence
import RMod.Classification.Proofs.ReconstructionTensorBlockFormula
import RMod.Classification.Proofs.ReconstructionUnitOutputIndex
import RMod.Classification.Proofs.ConvolutionUnitBlockFormula
import RMod.Classification.Proofs.IsoEqualityMaps

/-!
# The reconstruction unit diagram on the surviving convolution block

Combine the binary unit equation with the actual fixed-degree equality
maps. The source is exactly the surviving summand in the convolution
with the supported unit family.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionLeftUnitBlock_coherence :
    C.data.comp
      (twistSummandHom C.data (reconstructionTwistData A C hC) (fun j => (reconstructionUnitData A C hC j).hom) (fun j => C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) j).val) 1 ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g))
      (C.data.comp (reconstructionConvolutionBlockIso A C hC A.data.tensorUnit X g 1).hom.hom
        (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
            (congrArg (reconstructionComponentRealization A C hC g).obj
              (reconstructionLeftUnitOutput_eq A X g))).hom
          ((reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g)))) =
      (convolutionLeftUnitBlockOfParity C.data hC (reconstructionTwistData A C hC)
        (reconstructionNu_one_left A C hC) ((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).hom.hom := by
  let I := SimpleOrbit A.toWeaklyPointedSuperfusion
  let F : I → C.data.Obj := fun h => (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) h).val
  let U : I → C.data.Obj := fun h => (pullbackUnitObj C.data hC (reconstructionTwistData A C hC) h).val
  let V : I → C.data.Obj := fun h => (((reconstructionUnderlyingEquivalence A C hC).functor.obj A.data.tensorUnit) h).val
  let u : ∀ h, C.data.Hom (U h) (V h) := fun h => (reconstructionUnitData A C hC h).hom
  let n : I → ZMod 2 := fun h => reconstructionNu A C hC 1 h
  let L : I → C.data.Obj := fun h => C.data.tensorObj (C.data.tensorObj (U 1) (F h)) (C.data.pi.factor (n h))
  let M : I → C.data.Obj := fun h => C.data.tensorObj (C.data.tensorObj (V 1) (F h)) (C.data.pi.factor (n h))
  let P : I → C.data.Obj := fun h => (reconstructionComponentRealization A C hC (1 * h)).obj
    (reconstructionTensorSpanObject A A.data.tensorUnit X 1 h)
  let Q : C.data.Obj := (reconstructionComponentRealization A C hC g).obj
    (reconstructionLeftUnitSpan A X g)
  let a : ∀ h, C.data.Hom (L h) (M h) := fun h =>
    C.data.tensorHom (C.data.tensorHom (u 1) (C.data.id (F h))) (C.data.id (C.data.pi.factor (n h)))
  let m : ∀ h, C.data.Hom (M h) (P h) := fun h =>
    ((reconstructionTensorComparison A C hC 1 h).data.app ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X h)).hom
  let q : C.data.Hom Q (F g) :=
    (reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g)
  let r : C.data.Hom (C.data.tensorObj (C.data.tensorObj C.data.tensorUnit (F g)) C.data.tensorUnit) (F g) :=
    C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit (F g))) (C.data.leftUnitorHom (F g))
  have hu : U 1 = C.data.tensorUnit := supportedObj_one C.data hC (reconstructionTwistData A C hC) _ _
  have hs : L ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g) = C.data.tensorObj (C.data.tensorObj C.data.tensorUnit (F g)) C.data.tensorUnit := by
    dsimp only [L, n]
    rw [inv_one, one_mul, reconstructionNu_one_left, hu]
    rfl
  have hb := convolutionLeftUnitBlockOfParity_hom C.data hC (reconstructionTwistData A C hC)
    (reconstructionNu_one_left A C hC) ((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g hs
  apply Eq.trans ?_ hb.symm
  rw [reconstructionConvolutionBlock_hom]
  let e := (reconstructionTensorOutputRealization_obj A C hC A.data.tensorUnit X g 1).symm
  let f := congrArg (reconstructionComponentRealization A C hC g).obj
    (reconstructionLeftUnitOutput_eq A X g)
  change C.data.comp (a ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g))
    (C.data.comp (C.data.comp (m ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g)) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data e).hom)
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data f).hom q)) =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hs).hom r
  apply (isoData_ofEq_two_comparisons C.toWeaklyPointedSuperfusion (a ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g)) (m ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g)) e f q).trans
  clear hb
  generalize_proofs hcast
  revert hs
  revert hcast
  change ∀ (hcast : P ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g) = Q)
    (hs : L ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g) = C.data.tensorObj (C.data.tensorObj C.data.tensorUnit (F g)) C.data.tensorUnit),
    C.data.comp (C.data.comp (a ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g)) (m ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g)))
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hcast).hom q) =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hs).hom r
  generalize he : ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g) = h
  have hh : h = g := by rw [← he, inv_one, one_mul]
  clear he
  subst h
  intro hcast hs
  exact reconstructionLeftUnitSummand_coherence A C hC X g hs

theorem reconstructionRightUnitBlock_coherence :
    C.data.comp
      (twistSummandHom C.data (reconstructionTwistData A C hC) (fun j => C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) j).val) (fun j => (reconstructionUnitData A C hC j).hom) g (g⁻¹ * g))
      (C.data.comp (reconstructionConvolutionBlockIso A C hC X A.data.tensorUnit g g).hom.hom
        (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
            (congrArg (reconstructionComponentRealization A C hC g).obj
              (reconstructionRightUnitOutput_eq A X g))).hom
          ((reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g)))) =
      (convolutionRightUnitBlockOfParity C.data hC (reconstructionTwistData A C hC)
        (reconstructionNu_one_right A C hC) ((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).hom.hom := by
  let I := SimpleOrbit A.toWeaklyPointedSuperfusion
  let F : I → C.data.Obj := fun h => (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) h).val
  let U : I → C.data.Obj := fun h => (pullbackUnitObj C.data hC (reconstructionTwistData A C hC) h).val
  let V : I → C.data.Obj := fun h => (((reconstructionUnderlyingEquivalence A C hC).functor.obj A.data.tensorUnit) h).val
  let u : ∀ h, C.data.Hom (U h) (V h) := fun h => (reconstructionUnitData A C hC h).hom
  let n : I → ZMod 2 := fun h => reconstructionNu A C hC g h
  let L : I → C.data.Obj := fun h => C.data.tensorObj (C.data.tensorObj (F g) (U h)) (C.data.pi.factor (n h))
  let M : I → C.data.Obj := fun h => C.data.tensorObj (C.data.tensorObj (F g) (V h)) (C.data.pi.factor (n h))
  let P : I → C.data.Obj := fun h => (reconstructionComponentRealization A C hC (g * h)).obj
    (reconstructionTensorSpanObject A X A.data.tensorUnit g h)
  let Q : C.data.Obj := (reconstructionComponentRealization A C hC g).obj
    (reconstructionRightUnitSpan A X g)
  let a : ∀ h, C.data.Hom (L h) (M h) := fun h =>
    C.data.tensorHom (C.data.tensorHom (C.data.id (F g)) (u h)) (C.data.id (C.data.pi.factor (n h)))
  let m : ∀ h, C.data.Hom (M h) (P h) := fun h =>
    ((reconstructionTensorComparison A C hC g h).data.app ((reconstructionSourceEquivalence A).inverse.obj X g) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit h)).hom
  let q : C.data.Hom Q (F g) :=
    (reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g)
  let r : C.data.Hom (C.data.tensorObj (C.data.tensorObj (F g) C.data.tensorUnit) C.data.tensorUnit) (F g) :=
    C.data.comp (C.data.rightUnitorHom (C.data.tensorObj (F g) C.data.tensorUnit)) (C.data.rightUnitorHom (F g))
  have hu : U 1 = C.data.tensorUnit := supportedObj_one C.data hC (reconstructionTwistData A C hC) _ _
  have hs : L (g⁻¹ * g) = C.data.tensorObj (C.data.tensorObj (F g) C.data.tensorUnit) C.data.tensorUnit := by
    dsimp only [L, n]
    rw [inv_mul_cancel, reconstructionNu_one_right, hu]
    rfl
  have hb := convolutionRightUnitBlockOfParity_hom C.data hC (reconstructionTwistData A C hC)
    (reconstructionNu_one_right A C hC) ((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g hs
  apply Eq.trans ?_ hb.symm
  rw [reconstructionConvolutionBlock_hom]
  let e := (reconstructionTensorOutputRealization_obj A C hC X A.data.tensorUnit g g).symm
  let f := congrArg (reconstructionComponentRealization A C hC g).obj
    (reconstructionRightUnitOutput_eq A X g)
  change C.data.comp (a (g⁻¹ * g))
    (C.data.comp (C.data.comp (m (g⁻¹ * g)) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data e).hom)
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data f).hom q)) =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hs).hom r
  apply (isoData_ofEq_two_comparisons C.toWeaklyPointedSuperfusion (a (g⁻¹ * g)) (m (g⁻¹ * g)) e f q).trans
  clear hb
  generalize_proofs hcast
  revert hs
  revert hcast
  change ∀ (hcast : P (g⁻¹ * g) = Q)
    (hs : L (g⁻¹ * g) = C.data.tensorObj (C.data.tensorObj (F g) C.data.tensorUnit) C.data.tensorUnit),
    C.data.comp (C.data.comp (a (g⁻¹ * g)) (m (g⁻¹ * g)))
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hcast).hom q) =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hs).hom r
  generalize he : (g⁻¹ * g) = h
  have hh : h = 1 := by rw [← he, inv_mul_cancel]
  clear he
  subst h
  intro hcast hs
  exact reconstructionRightUnitSummand_coherence A C hC X g hs

end RMod.Classification

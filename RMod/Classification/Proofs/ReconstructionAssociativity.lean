import RMod.Classification.Proofs.ReconstructionProductAssociativity
import RMod.Classification.Proofs.ConvolutionProductTripleExt

/-!
# Global monoidal associativity of the reconstruction tensorator

The product-indexed triple inclusions detect equality of the actual map
families. On every triple of degrees the preceding component comparison
identifies the two routes. No normalization or pentagon law for the
extracted scalar is used in this global functor associativity diagram.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstructionTensorator_associativity (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
    (K : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    let F := (reconstructionUnderlyingEquivalence A C hC).functor
    let t := reconstructionTwistData A C hC
    C.data.comp (C.data.comp
      (convolutionHom C.data hC t (fun q => (reconstructionTensoratorData A C hC X Y q).hom)
        (fun q => C.data.id (F.obj Z q).val) K)
      (reconstructionTensoratorData A C hC (A.data.tensorObj X Y) Z K).hom)
      (F.map (A.data.associatorHom X Y Z) K) =
    C.data.comp (reconstructionAssociatorData A C hC (F.obj X) (F.obj Y) (F.obj Z) K).hom
      (C.data.comp (convolutionHom C.data hC t (fun q => C.data.id (F.obj X q).val)
        (fun q => (reconstructionTensoratorData A C hC Y Z q).hom) K)
        (reconstructionTensoratorData A C hC X (A.data.tensorObj Y Z) K).hom) := by
  dsimp only
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  have he := hom_ext_of_convolutionProductLeftInsertions C.data hC t (F.obj X) (F.obj Y) (F.obj Z)
    (fun q => (F.obj (A.data.tensorObj X (A.data.tensorObj Y Z)) q).val)
    (fun q => C.data.comp (C.data.comp
      (convolutionHom C.data hC t (fun r => (reconstructionTensoratorData A C hC X Y r).hom)
        (fun r => C.data.id (F.obj Z r).val) q)
      (reconstructionTensoratorData A C hC (A.data.tensorObj X Y) Z q).hom)
      (F.map (A.data.associatorHom X Y Z) q))
    (fun q => C.data.comp (reconstructionAssociatorData A C hC (F.obj X) (F.obj Y) (F.obj Z) q).hom
      (C.data.comp (convolutionHom C.data hC t (fun r => C.data.id (F.obj X r).val)
        (fun r => (reconstructionTensoratorData A C hC Y Z r).hom) q)
        (reconstructionTensoratorData A C hC X (A.data.tensorObj Y Z) q).hom))
    (fun g h k => reconstructionProductInsertion_associativity A C hC X Y Z g h k)
  exact congrFun he K

end RMod.Classification

import RMod.Classification.Proofs.ReconstructionMappedTripleAssociator
import RMod.Classification.Proofs.ReconstructionTripleIndexNaturality

/-!
# The mapped ambient associator on a threefold component

The left triple inclusion followed by the image of the ambient
associator agrees with the component associator followed by the right
triple inclusion. The final equality comparison is retained explicitly:
the two inclusions originally use the indices `(g*h)*k` and `g*(h*k)`.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionMappedTripleInclusion_associator :
    C.data.comp
      (C.data.comp (reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k)
        ((reconstructionUnderlyingEquivalence A C hC).functor.map
          (A.data.associatorHom X Y Z) ((g * h) * k)))
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (congrArg (fun j => (((reconstructionUnderlyingEquivalence A C hC).functor.obj
          (A.data.tensorObj X (A.data.tensorObj Y Z))) j).val) (mul_assoc g h k))).hom =
    C.data.comp
      (componentMappedTripleAssociator (reconstructionComponentSystem A C hC)
        (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion)
        (reconstruction_target_product A C hC) g h k
        ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
      (reconstructionMappedTripleRightInclusion A C hC X Y Z g h k) := by
  let L : C.data.Obj := (reconstructionComponentRealization A C hC ((g * h) * k)).obj
    (reconstructionTripleLeftSpan A X Y Z g h k)
  let R : C.data.Obj := (reconstructionComponentRealization A C hC ((g * h) * k)).obj
    (reconstructionTripleRightSpanAtLeft A X Y Z g h k)
  let R' : C.data.Obj := (reconstructionComponentRealization A C hC (g * (h * k))).obj
    (reconstructionTripleRightSpan A X Y Z g h k)
  let T : C.data.Obj := (((reconstructionUnderlyingEquivalence A C hC).functor.obj
    (A.data.tensorObj X (A.data.tensorObj Y Z))) ((g * h) * k)).val
  let T' : C.data.Obj := (((reconstructionUnderlyingEquivalence A C hC).functor.obj
    (A.data.tensorObj X (A.data.tensorObj Y Z))) (g * (h * k))).val
  let a : C.data.Hom L R := (reconstructionComponentRealization A C hC ((g * h) * k)).map
    (reconstructionTripleAssociatorAtLeft A X Y Z g h k)
  let q : C.data.Hom R T := (reconstructionComponentRealization A C hC ((g * h) * k)).map
    (reconstructionTripleRightInclusionAtLeft A X Y Z g h k)
  let e : C.data.Hom R R' := (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
    (reconstructionTripleRightRealization_index A C hC X Y Z g h k)).hom
  let u : C.data.Hom T T' := (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
    (congrArg (fun j => (((reconstructionUnderlyingEquivalence A C hC).functor.obj
      (A.data.tensorObj X (A.data.tensorObj Y Z))) j).val) (mul_assoc g h k))).hom
  let j : C.data.Hom R' T' := reconstructionMappedTripleRightInclusion A C hC X Y Z g h k
  have hi : C.data.comp q u = C.data.comp e j :=
    reconstructionMappedTripleRightInclusion_index A C hC X Y Z g h k
  exact (congrArg (fun m => C.data.comp m u)
      (reconstructionMappedTripleInclusion_associator_at_left A C hC X Y Z g h k)).trans
    ((C.laws.comp_assoc a q u).trans
      ((congrArg (C.data.comp a) hi).trans
        ((C.laws.comp_assoc a e j).symm.trans
          (congrArg (fun m => C.data.comp m j)
            (reconstructionComponentAssociator_index A C hC X Y Z g h k)))))

end RMod.Classification

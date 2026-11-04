import RMod.Classification.Instances.ParityTripleRightData
import RMod.Classification.Proofs.NormalizerNaturality

/-!
# Naturality of the right normalized triple route

Source reassociation is mapped by the complete component functor. Both
inverse tensorators and the target normalizer are even, so the four
squares compose without any additional Koszul scalar.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {p : Pi C.data} {a b : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object}
  (η : ParityTensorComparison T R V W p H K F a)
  (θ : ParityTensorComparison S (simpleTensorRepresentative A T R) U
    (simpleTensorRepresentative C V W) p E F N b)

theorem parityTripleRightTensorator_evenIso
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    EvenIsoLaws C.data (parityTripleRightTensorator S T R U V W η.data θ.data X Y Z) :=
  (((EvenIsoLaws.refl C.laws (E.data.obj X).obj).tensor C.laws (η.laws.iso Y Z)).tensor C.laws
    (EvenIsoLaws.refl C.laws (p.data.factor b))).trans C.laws (θ.laws.iso X (spanTensorObj A T R Y Z))

theorem parityTripleRightLaws :
    ParityTripleComparisonLaws S T R U V W (parityTripleRightData S T R U V W η.data θ.data) where
  iso X Y Z := (((N.mapEvenIsoLaws
      (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
      (EvenIsoLaws.assoc A.laws X.obj Y.obj Z.obj)).trans C.laws
        (θ.laws.iso X (spanTensorObj A T R Y Z)).symm).trans C.laws
          (((EvenIsoLaws.refl C.laws (E.data.obj X).obj).tensor C.laws (η.laws.iso Y Z).symm).tensor C.laws
            (EvenIsoLaws.refl C.laws (p.data.factor b)))).trans C.laws
              (p.laws.normalRight_evenIso C.laws (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj a b)
  naturality := by
    intro X X' Y Y' Z Z' c d e f g h hf hg hh
    have hsource := N.mapIso_naturality
      (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
      (X' := tripleSpanObjInRight A S T R X' Y' Z') (Y' := rightTripleSpanObj A S T R X' Y' Z')
      (i := IsoData.assoc A.data X.obj Y.obj Z.obj) (j := IsoData.assoc A.data X'.obj Y'.obj Z'.obj)
      (ObjectProperty.homMk (A.data.tensorHom (A.data.tensorHom f.hom g.hom) h.hom))
      (ObjectProperty.homMk (A.data.tensorHom f.hom (A.data.tensorHom g.hom h.hom)))
      (A.laws.associator_naturality f.hom g.hom h.hom)
    have houter := iso_naturality_symm C.laws (θ.laws.iso _ _).toIsoLaws (θ.laws.iso _ _).toIsoLaws
      (θ.laws.naturality f (spanTensorHom A T R g h) hf (A.laws.tensor_grade _ _ hg hh))
    have hinner := iso_naturality_symm C.laws (η.laws.iso Y Z).toIsoLaws (η.laws.iso Y' Z').toIsoLaws
      (η.laws.naturality g h hg hh)
    have hi := iso_naturality_tensor C.laws (EvenIsoLaws.refl C.laws (E.data.obj X).obj)
      (η.laws.iso Y' Z').symm (iso_naturality_refl C.laws (E.data.map f).hom) hinner
    have hw := iso_naturality_whiskerRight C.laws
      ((EvenIsoLaws.refl C.laws (E.data.obj X).obj).tensor C.laws (η.laws.iso Y Z).symm) hi (p.data.factor b)
    exact iso_naturality_trans C.laws
      (iso_naturality_trans C.laws (iso_naturality_trans C.laws hsource houter) hw)
        (p.laws.normalRight_naturality C.laws (E.data.map f).hom (H.data.map g).hom (K.data.map h).hom a b)

end RMod.Classification

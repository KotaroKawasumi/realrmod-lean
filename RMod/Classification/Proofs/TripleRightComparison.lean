import RMod.Classification.Instances.TripleRightComparisonData
import RMod.Classification.Proofs.HomogeneousIsoCalculus
import RMod.Classification.Proofs.ComparisonHomogeneousIso
import RMod.Classification.Proofs.HomogeneousTensorNaturality
import RMod.Classification.Proofs.IsoNaturality

/-!
# The right-associated route is a homogeneous natural comparison

The mapped source associator and inverse target associator are even.
Between them, the two binary comparisons contribute their summed degree.
Whiskering the inner comparison supplies the crossing sign from the
first input map, giving signed naturality on the sum of all three degrees.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object} {a b : ZMod 2}
  (η : TensorComparison T R V W H K F a)
  (θ : TensorComparison S (simpleTensorRepresentative A T R) U (simpleTensorRepresentative C V W) E F N b)

theorem tripleRightComparisonLaws :
    TripleComparisonLaws S T R U V W (a + b) (tripleRightComparisonData S T R U V W η.data θ.data) where
  iso X Y Z := by
    have h := (((N.mapEvenIsoLaws
      (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
      (EvenIsoLaws.assoc A.laws X.obj Y.obj Z.obj)).homogeneous.trans C.laws
        (θ.homogeneousIsoLaws X (spanTensorObj A T R Y Z))).trans C.laws
          ((η.homogeneousIsoLaws Y Z).whiskerLeft C.laws (E.data.obj X).obj)).trans C.laws
            (EvenIsoLaws.assoc C.laws (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj).symm.homogeneous
    simp only [zero_add, add_zero, add_comm b a] at h
    exact h
  naturality := by
    intro X X' Y Y' Z Z' p q r f g h hf hg hh
    have hsource := N.mapIso_naturality
      (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
      (X' := tripleSpanObjInRight A S T R X' Y' Z') (Y' := rightTripleSpanObj A S T R X' Y' Z')
      (i := IsoData.assoc A.data X.obj Y.obj Z.obj) (j := IsoData.assoc A.data X'.obj Y'.obj Z'.obj)
      (ObjectProperty.homMk (A.data.tensorHom (A.data.tensorHom f.hom g.hom) h.hom))
      (ObjectProperty.homMk (A.data.tensorHom f.hom (A.data.tensorHom g.hom h.hom)))
      (A.laws.associator_naturality f.hom g.hom h.hom)
    have houter := θ.laws.naturality f (spanTensorHom A T R g h) hf (A.laws.tensor_grade _ _ hg hh)
    have hinner := signed_naturality_whiskerLeft C.laws (η.data.app Y Z).hom (η.data.app Y' Z').hom
      (E.data.map f).hom (F.data.map (spanTensorHom A T R g h)).hom
      (C.data.tensorHom (H.data.map g).hom (K.data.map h).hom)
      (η.laws.hom_grade Y' Z') (E.laws.map_grade f hf) (η.laws.naturality g h hg hh)
    have htarget := iso_naturality_symm C.laws
      (EvenIsoLaws.assoc C.laws (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj).toIsoLaws
      (EvenIsoLaws.assoc C.laws (E.data.obj X').obj (H.data.obj Y').obj (K.data.obj Z').obj).toIsoLaws
      (C.laws.associator_naturality (E.data.map f).hom (H.data.map g).hom (K.data.map h).hom)
    have ht₁ := signed_naturality_trans C.laws (hsource.trans (C.laws.one_smul _).symm) houter
    have ht₂ := signed_naturality_trans C.laws ht₁ hinner
    have ht₃ := signed_naturality_trans C.laws ht₂ (htarget.trans (C.laws.one_smul _).symm)
    simp only [one_mul, mul_one] at ht₃
    rw [← parity_power_add, ← add_mul, add_comm b a] at ht₃
    rw [← add_assoc p q r] at ht₃
    exact ht₃

end RMod.Classification

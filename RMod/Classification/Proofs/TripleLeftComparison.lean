import RMod.Classification.Instances.TripleLeftComparisonData
import RMod.Classification.Proofs.HomogeneousIsoCalculus
import RMod.Classification.Proofs.ComparisonHomogeneousIso
import RMod.Classification.Proofs.HomogeneousTensorNaturality

/-!
# Laws for the actual left-associated triple route

The two comparison degrees add. Whiskering the inner comparison includes
the crossing sign from the third input map. Composing this signed square
with the outer binary square therefore gives the sign of the sum of the
two comparison degrees against all three input degrees.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a b : ZMod 2}
  (η : TensorComparison S T U V E H F a)
  (θ : TensorComparison (simpleTensorRepresentative A S T) R (simpleTensorRepresentative C U V) W F K N b)

theorem tripleLeftComparisonLaws :
    TripleComparisonLaws S T R U V W (a + b) (tripleLeftComparisonData S T R U V W η.data θ.data) where
  iso X Y Z := by
    have h := (θ.homogeneousIsoLaws (spanTensorObj A S T X Y) Z).trans C.laws
      ((η.homogeneousIsoLaws X Y).whiskerRight C.laws (K.data.obj Z).obj)
    rw [add_comm b a] at h
    exact h
  naturality f g h hf hg hh := by
    have houter := θ.laws.naturality (spanTensorHom A S T f g) h (A.laws.tensor_grade _ _ hf hg) hh
    have hinner := signed_naturality_whiskerRight C.laws (η.data.app _ _).hom (η.data.app _ _).hom
      (F.data.map (spanTensorHom A S T f g)).hom
      (C.data.tensorHom (E.data.map f).hom (H.data.map g).hom) (K.data.map h).hom
      (η.laws.hom_grade _ _) (K.laws.map_grade h hh) (η.laws.naturality f g hf hg)
    have ht := signed_naturality_trans C.laws houter hinner
    rw [← parity_power_add, ← add_mul, add_comm b a] at ht
    exact ht

end RMod.Classification

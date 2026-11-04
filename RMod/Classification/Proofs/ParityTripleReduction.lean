import RMod.Classification.Instances.ParityTripleReductionData
import RMod.Classification.Proofs.RightFactorDeletion
import RMod.Classification.Proofs.HomogeneousTensorNaturality
import RMod.Classification.Proofs.IsoNaturality

/-!
# Reduction preserves homogeneous triple naturality

The even comparison and reassociation add no sign. The only crossing
is deletion of the common parity factor against the three input maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a : ZMod 2}
  (η : ParityTripleComparison S T R U V W p E H K N a)

theorem parityTripleReductionLaws : TripleComparisonLaws S T R U V W a
    (parityTripleReductionData p.data a η.data) where
  iso X Y Z := by
    have h := (((η.laws.iso X Y Z).homogeneous.trans C.laws
      (p.laws.rightFactorDeletion_homogeneousIso C.laws
        (C.data.tensorObj (E.data.obj X).obj (C.data.tensorObj (H.data.obj Y).obj (K.data.obj Z).obj)) a)).trans C.laws
          (EvenIsoLaws.assoc C.laws (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj).symm.homogeneous)
    rw [zero_add, add_zero] at h
    exact h
  naturality := by
    intro X X' Y Y' Z Z' b c e f g h hf hg hh
    have hdel := p.laws.rightFactorDeletion_naturality C.laws a
      (C.data.tensorHom (E.data.map f).hom (C.data.tensorHom (H.data.map g).hom (K.data.map h).hom))
      (C.laws.tensor_grade _ _ (E.laws.map_grade f hf)
        (C.laws.tensor_grade _ _ (H.laws.map_grade g hg) (K.laws.map_grade h hh)))
    have hassoc := iso_naturality_symm C.laws
      (EvenIsoLaws.assoc C.laws (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj).toIsoLaws
      (EvenIsoLaws.assoc C.laws (E.data.obj X').obj (H.data.obj Y').obj (K.data.obj Z').obj).toIsoLaws
      (C.laws.associator_naturality (E.data.map f).hom (H.data.map g).hom (K.data.map h).hom)
    have h₁ := signed_naturality_trans C.laws
      ((η.laws.naturality f g h hf hg hh).trans (C.laws.one_smul _).symm) hdel
    have h₂ := signed_naturality_trans C.laws h₁ (hassoc.trans (C.laws.one_smul _).symm)
    rw [one_mul, mul_one, ← add_assoc b c e] at h₂
    exact h₂

end RMod.Classification

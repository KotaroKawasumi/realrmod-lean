import RMod.Classification.Instances.ParityTensorComparisonData
import RMod.Classification.Proofs.RightFactorDeletion
import RMod.Classification.Proofs.SignedNaturalityInverse
import RMod.Classification.Proofs.HomogeneousTensorNaturality
import RMod.Classification.Proofs.ComparisonHomogeneousIso

/-!
# The parity-corrected comparison is even and natural

Deletion and the inverse comparison contribute the same Koszul sign.
Their product is one, leaving the ordinary naturality square required
of a strong monoidal superfunctor's tensorator.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object} {a : ZMod 2}
  (p : Pi C.data) (η : TensorComparison S T U V E H N a)

theorem parityTensorComparisonLaws :
    ParityTensorComparisonLaws S T U V (parityTensorComparisonData p.data a η.data) where
  iso X Y := by
    have hi := (p.laws.rightFactorDeletion_homogeneousIso C.laws
      (C.data.tensorObj (E.data.obj X).obj (H.data.obj Y).obj) a).trans C.laws
      (η.homogeneousIsoLaws X Y).symm
    rw [CharTwo.add_self_eq_zero] at hi
    exact ⟨hi.toIsoLaws, hi.hom_grade, hi.inv_grade⟩
  naturality f g hf hg := by
    have hdel := p.laws.rightFactorDeletion_naturality C.laws a
      (C.data.tensorHom (E.data.map f).hom (H.data.map g).hom)
      (C.laws.tensor_grade _ _ (E.laws.map_grade f hf) (H.laws.map_grade g hg))
    have hinv := signed_naturality_symm C.laws (η.laws.iso _ _) (η.laws.iso _ _)
      (parity_power_mul_self (a * (_ + _))) (η.laws.naturality f g hf hg)
    have hh := signed_naturality_trans C.laws hdel hinv
    rw [parity_power_mul_self, C.laws.one_smul] at hh
    exact hh

end RMod.Classification

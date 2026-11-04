import RMod.Classification.Proofs.SpanComparisonSurjective
import RMod.Classification.Proofs.SpanInverse

/-!
# The completed equivalence of homogeneous spans

The comparison functor, its explicit Hom preimages and its even object
preimages construct an actual inverse equivalence. Grading reflection
proves the inverse superfunctor laws and evenness of the unit and counit.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C D : PiSuperfusion.{0, 0}) (S : C.data.Obj) (T : D.data.Obj)
  (a : @End (LinearCategory C.toWeaklyPointedSuperfusion) _ S ≃ₐ[ℝ]
    @End (LinearCategory D.toWeaklyPointedSuperfusion) _ T)
  (ha : ∀ b f, D.data.IsHomogeneous b (a f) ↔ C.data.IsHomogeneous b f)

noncomputable def spanComparisonEquivalenceData :
    SpanSuperequivalenceData C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion S T :=
  let F := spanComparison D T a (fun b f hf => (ha b f).mpr hf)
  let p := spanPreimages F (spanComparison_even_essSurj C D S T a (fun b f hf => (ha b f).mpr hf))
  p.underlyingEquivalence (spanComparisonFullyFaithful D T a (fun b f hf => (ha b f).mpr hf))

theorem spanComparisonEquivalenceLaws :
    SpanSuperequivalenceLaws C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion S T
      (spanComparisonEquivalenceData C D S T a ha) :=
  let F := spanComparison D T a (fun b f hf => (ha b f).mpr hf)
  let p := spanPreimages F (spanComparison_even_essSurj C D S T a (fun b f hf => (ha b f).mpr hf))
  p.underlyingEquivalenceLaws
    (spanComparisonFullyFaithful D T a (fun b f hf => (ha b f).mpr hf))
    (spanComparison_grade_iff D T a ha)

noncomputable def spanComparisonSuperequivalence :
    SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion S T :=
  ⟨spanComparisonEquivalenceData C D S T a ha, spanComparisonEquivalenceLaws C D S T a ha⟩

end RMod.Classification

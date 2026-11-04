import RMod.Classification.Instances.SpanComparison

/-!
# Even essential surjectivity of the component comparison

Realize the target object's parity list in the source. The functor may
choose different coordinates on that realization. Rectangular transport
of its identity changes between these two presentations, and the two
orders of composition are identity maps. Both maps are even.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C D : PiSuperfusion.{0, 0}) (S : C.data.Obj) (T : D.data.Obj)
  (a : @End (LinearCategory C.toWeaklyPointedSuperfusion) _ S ≃ₐ[ℝ]
    @End (LinearCategory D.toWeaklyPointedSuperfusion) _ T)
  (ha : ∀ b f, C.data.IsHomogeneous b f → D.data.IsHomogeneous b (a f))

theorem spanComparison_even_essSurj (Y : HomogeneousSpanCategory D.toWeaklyPointedSuperfusion T) :
    ∃ X : HomogeneousSpanCategory C.toWeaklyPointedSuperfusion S,
      D.data.HasHomogeneousIso 0 ((spanComparison D T a ha).data.obj X).obj Y.obj := by
  let r := homogeneousRealization C S (spanPresentation Y).data.parity
  let X : HomogeneousSpanCategory C.toWeaklyPointedSuperfusion S :=
    ⟨r.data.object, spanSize Y, ⟨r.toHomogeneousSum⟩⟩
  let d := spanPresentation X
  let e := r.toHomogeneousSum
  let d' := (spanImageRealization D T X).toHomogeneousSum
  let e' := spanPresentation Y
  let f := HomogeneousSum.transportHom a d e d' e' (𝟙 (X.obj : LinearCategory C.toWeaklyPointedSuperfusion))
  let g := HomogeneousSum.transportHom a e d e' d' (𝟙 (X.obj : LinearCategory C.toWeaklyPointedSuperfusion))
  refine ⟨X, f, g, ?_, ?_, ?_, ?_⟩
  · have h := (HomogeneousSum.transportHom_comp a d e d d' e' d'
      (𝟙 (X.obj : LinearCategory C.toWeaklyPointedSuperfusion)) (𝟙 X.obj)).symm
    rw [Category.id_comp, HomogeneousSum.transportHom_id] at h
    exact h
  · have h := (HomogeneousSum.transportHom_comp a e d e e' d' e'
      (𝟙 (X.obj : LinearCategory C.toWeaklyPointedSuperfusion)) (𝟙 X.obj)).symm
    rw [Category.id_comp, HomogeneousSum.transportHom_id] at h
    exact h
  · exact HomogeneousSum.transportHom_grade a d e d' e' ha
      (spanImageRealization D T X).laws.parity r.laws.parity.symm (C.laws.id_even X.obj)
  · exact HomogeneousSum.transportHom_grade a e d e' d' ha
      r.laws.parity.symm (spanImageRealization D T X).laws.parity (C.laws.id_even X.obj)

end RMod.Classification

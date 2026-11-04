import RMod.Classification.Instances.SpanComparisonObjectData

/-!
# The object comparison preserves the prescribed endomorphism action

Transport of compositions proves both inverse identities. Equality of
the two parity lists makes the maps even. Transport of f followed by an
identity, and of an identity followed by f, proves the intertwining
equation for every source endomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} (D : PiSuperfusion.{0, 0})
  {S : C.data.Obj} (T : D.data.Obj)
  (a : @End (LinearCategory C) _ S ≃ₐ[ℝ] @End (LinearCategory D.toWeaklyPointedSuperfusion) _ T)
  (X : HomogeneousSpanCategory C S) {Y : D.data.Obj}
  (B : HomogeneousSum D.data.toWeaklyPointedSuperfusionData T Y (spanSize X))
  (ha : ∀ b f, C.data.IsHomogeneous b f → D.data.IsHomogeneous b (a f))
  (hB : B.data.parity = (spanPresentation X).data.parity)

include ha hB in
theorem spanComparisonObjectIsoLaws :
    EvenIsoLaws D.data.toWeaklyPointedSuperfusionData (spanComparisonObjectIsoData D T a X B) where
  hom_inv := by
    have h := (HomogeneousSum.transportHom_comp a (spanPresentation X) (spanPresentation X)
      (spanPresentation X) (spanImageRealization D T X).toHomogeneousSum B
      (spanImageRealization D T X).toHomogeneousSum
      (𝟙 (X.obj : LinearCategory C)) (𝟙 (X.obj : LinearCategory C))).symm
    rw [Category.id_comp, HomogeneousSum.transportHom_id] at h
    exact h
  inv_hom := by
    have h := (HomogeneousSum.transportHom_comp a (spanPresentation X) (spanPresentation X)
      (spanPresentation X) B (spanImageRealization D T X).toHomogeneousSum B
      (𝟙 (X.obj : LinearCategory C)) (𝟙 (X.obj : LinearCategory C))).symm
    rw [Category.id_comp, HomogeneousSum.transportHom_id] at h
    exact h
  hom_even := HomogeneousSum.transportHom_grade a (spanPresentation X) (spanPresentation X)
    (spanImageRealization D T X).toHomogeneousSum B ha (spanImageRealization D T X).laws.parity hB
    (C.laws.id_even X.obj)
  inv_even := HomogeneousSum.transportHom_grade a (spanPresentation X) (spanPresentation X)
    B (spanImageRealization D T X).toHomogeneousSum ha hB (spanImageRealization D T X).laws.parity
    (C.laws.id_even X.obj)

theorem spanComparisonObject_intertwines (f : @End (LinearCategory C) _ X.obj) :
    D.data.comp ((spanComparison D T a ha).data.map (ObjectProperty.homMk f : X ⟶ X)).hom
        (spanComparisonObjectIsoData D T a X B).hom =
      D.data.comp (spanComparisonObjectIsoData D T a X B).hom
        (HomogeneousSum.transportHom a (spanPresentation X) (spanPresentation X) B B f) := by
  let A := spanPresentation X
  let A' := (spanImageRealization D T X).toHomogeneousSum
  change HomogeneousSum.transportHom a A A A' A' f ≫
      HomogeneousSum.transportHom a A A A' B (𝟙 (X.obj : LinearCategory C)) =
    HomogeneousSum.transportHom a A A A' B (𝟙 (X.obj : LinearCategory C)) ≫
      HomogeneousSum.transportHom a A A B B f
  rw [← HomogeneousSum.transportHom_comp, ← HomogeneousSum.transportHom_comp,
    Category.comp_id, Category.id_comp]

end RMod.Classification

import RMod.Classification.Instances.ReconstructionPullbackSpans
import RMod.Classification.Instances.SpanFamilyLinearCategory
import RMod.Classification.Proofs.EquivalenceComponents

/-!
# Superlinear laws on the product of component equivalences

The identity description change preserves every map. The product
equivalence applies a chosen superlinear component equivalence in each
coordinate, so its linearity and grading follow coordinate by coordinate.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

instance reconstructionPullbackSpanFunctor_additive :
    (reconstructionPullbackSpanFunctor A C hC).Additive where
  map_add := rfl

instance reconstructionPullbackSpanFunctor_linear :
    (reconstructionPullbackSpanFunctor A C hC).Linear ℝ where
  map_smul _ _ := rfl

instance reconstructionSpanPullbackFunctor_additive :
    (reconstructionSpanPullbackFunctor A C hC).Additive where
  map_add := rfl

instance reconstructionSpanPullbackFunctor_linear :
    (reconstructionSpanPullbackFunctor A C hC).Linear ℝ where
  map_smul _ _ := rfl

instance reconstructionComponentFamily_forward_additive :
    (reconstructionComponentFamilyEquivalence A C hC).functor.Additive where
  map_add {_ _ f g} := funext fun i =>
    ((reconstructionComponentSystem A C hC).component i).laws.forward.map_add (f i) (g i)

instance reconstructionComponentFamily_forward_linear :
    (reconstructionComponentFamilyEquivalence A C hC).functor.Linear ℝ where
  map_smul f r := funext fun i =>
    ((reconstructionComponentSystem A C hC).component i).laws.forward.map_smul r (f i)

instance reconstructionComponentFamily_backward_additive :
    (reconstructionComponentFamilyEquivalence A C hC).inverse.Additive :=
  Equivalence.inverse_additive _

instance reconstructionComponentFamily_backward_linear :
    (reconstructionComponentFamilyEquivalence A C hC).inverse.Linear ℝ :=
  Equivalence.inverseLinear ℝ _

instance reconstructionPullbackFamily_forward_additive :
    (reconstructionPullbackFamilyEquivalence A C hC).functor.Additive := by
  change ((reconstructionPullbackSpanFunctor A C hC) ⋙
    (reconstructionComponentFamilyEquivalence A C hC).inverse).Additive
  infer_instance

instance reconstructionPullbackFamily_forward_linear :
    (reconstructionPullbackFamilyEquivalence A C hC).functor.Linear ℝ := by
  change ((reconstructionPullbackSpanFunctor A C hC) ⋙
    (reconstructionComponentFamilyEquivalence A C hC).inverse).Linear ℝ
  infer_instance

instance reconstructionPullbackFamily_backward_additive :
    (reconstructionPullbackFamilyEquivalence A C hC).inverse.Additive :=
  Equivalence.inverse_additive _

instance reconstructionPullbackFamily_backward_linear :
    (reconstructionPullbackFamilyEquivalence A C hC).inverse.Linear ℝ :=
  Equivalence.inverseLinear ℝ _

theorem reconstructionPullbackFamily_forward_grade
    {X Y : PullbackCategory C.data hC (reconstructionTwistData A C hC)}
    {a : ZMod 2} (f : X ⟶ Y) (hf : ∀ g, C.data.IsHomogeneous a (f g))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous a ((reconstructionPullbackFamilyEquivalence A C hC).functor.map f g).hom :=
  ((reconstructionComponentSystem A C hC).component g).laws.backward.map_grade _ (hf g)

theorem reconstructionPullbackFamily_backward_grade
    {X Y : SpanFamilyCategory A.toWeaklyPointedSuperfusion
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object)}
    {a : ZMod 2} (f : X ⟶ Y) (hf : ∀ g, A.data.IsHomogeneous a (f g).hom)
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous a ((reconstructionPullbackFamilyEquivalence A C hC).inverse.map f g) :=
  ((reconstructionComponentSystem A C hC).component g).laws.forward.map_grade _ (hf g)

/-! The composite equivalence retains the chosen even component unit and
counit; the description-change equivalence contributes only identities. -/

theorem reconstructionPullbackFamily_unit_hom_even
    (X : PullbackCategory C.data hC (reconstructionTwistData A C hC))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous 0 ((reconstructionPullbackFamilyEquivalence A C hC).unitIso.hom.app X g) := by
  have h := C.laws.comp_grade _ _ (C.laws.id_even (X g).val)
    (((reconstructionComponentSystem A C hC).component g).laws.counit_inv_even
      ((reconstructionPullbackSpanFunctor A C hC).obj X g))
  rw [zero_add] at h
  have he := congrArg (fun f : X ⟶ _ => f g)
    (equivalence_trans_unit_hom (reconstructionPullbackSpanEquivalence A C hC)
      (reconstructionComponentFamilyEquivalence A C hC).symm X)
  exact he.symm ▸ h

theorem reconstructionPullbackFamily_unit_inv_even
    (X : PullbackCategory C.data hC (reconstructionTwistData A C hC))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous 0 ((reconstructionPullbackFamilyEquivalence A C hC).unitIso.inv.app X g) := by
  have h := C.laws.comp_grade _ _
    (((reconstructionComponentSystem A C hC).component g).laws.counit_hom_even
      ((reconstructionPullbackSpanFunctor A C hC).obj X g)) (C.laws.id_even (X g).val)
  rw [zero_add] at h
  have he := congrArg (fun f : _ ⟶ X => f g)
    (equivalence_trans_unit_inv (reconstructionPullbackSpanEquivalence A C hC)
      (reconstructionComponentFamilyEquivalence A C hC).symm X)
  exact he.symm ▸ h

theorem reconstructionPullbackFamily_counit_hom_even
    (X : SpanFamilyCategory A.toWeaklyPointedSuperfusion
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionPullbackFamilyEquivalence A C hC).counitIso.hom.app X g).hom := by
  let E := (reconstructionComponentSystem A C hC).component g
  have h := A.laws.comp_grade _ _
    (E.laws.backward.map_grade (𝟙 (E.data.functor.obj (X g)))
      (C.laws.id_even (E.data.functor.obj (X g)).obj)) (E.laws.unit_inv_even (X g))
  rw [zero_add] at h
  have he := congrArg (fun f : _ ⟶ X => (f g).hom)
    (equivalence_trans_counit_hom (reconstructionPullbackSpanEquivalence A C hC)
      (reconstructionComponentFamilyEquivalence A C hC).symm X)
  exact he.symm ▸ h

theorem reconstructionPullbackFamily_counit_inv_even
    (X : SpanFamilyCategory A.toWeaklyPointedSuperfusion
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionPullbackFamilyEquivalence A C hC).counitIso.inv.app X g).hom := by
  let E := (reconstructionComponentSystem A C hC).component g
  have h := A.laws.comp_grade _ _ (E.laws.unit_hom_even (X g))
    (E.laws.backward.map_grade (𝟙 (E.data.functor.obj (X g)))
      (C.laws.id_even (E.data.functor.obj (X g)).obj))
  rw [zero_add] at h
  have he := congrArg (fun f : X ⟶ _ => (f g).hom)
    (equivalence_trans_counit_inv (reconstructionPullbackSpanEquivalence A C hC)
      (reconstructionComponentFamilyEquivalence A C hC).symm X)
  exact he.symm ▸ h

end RMod.Classification

import RMod.Classification.Instances.ReconstructionUnderlyingEquivalence
import RMod.Classification.Proofs.ReconstructionSourceEquivalence
import RMod.Classification.Proofs.ReconstructionPullbackSpans

/-!
# Superlinear laws of the actual global reconstruction equivalence

Both functors preserve all real-linear operations and homogeneous
degrees. Their specified unit and counit have even maps and even
inverses. These laws concern the already constructed ordinary
equivalence and do not assume any coherence law for omega.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

instance reconstructionUnderlying_forward_additive :
    (reconstructionUnderlyingEquivalence A C hC).functor.Additive := by
  change ((reconstructionSourceEquivalence A).inverse ⋙
    (reconstructionPullbackFamilyEquivalence A C hC).inverse).Additive
  infer_instance

instance reconstructionUnderlying_forward_linear :
    (reconstructionUnderlyingEquivalence A C hC).functor.Linear ℝ := by
  change ((reconstructionSourceEquivalence A).inverse ⋙
    (reconstructionPullbackFamilyEquivalence A C hC).inverse).Linear ℝ
  infer_instance

instance reconstructionUnderlying_backward_additive :
    (reconstructionUnderlyingEquivalence A C hC).inverse.Additive :=
  Equivalence.inverse_additive _

instance reconstructionUnderlying_backward_linear :
    (reconstructionUnderlyingEquivalence A C hC).inverse.Linear ℝ :=
  Equivalence.inverseLinear ℝ _

theorem reconstructionUnderlying_forward_grade
    {X Y : LinearCategory A.toWeaklyPointedSuperfusion} {a : ZMod 2}
    (f : X ⟶ Y) (hf : A.data.IsHomogeneous a f)
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous a ((reconstructionUnderlyingEquivalence A C hC).functor.map f g) :=
  reconstructionPullbackFamily_backward_grade A C hC _ (reconstructionSource_backward_grade A f hf) g

theorem reconstructionUnderlying_backward_grade
    {X Y : PullbackCategory C.data hC (reconstructionTwistData A C hC)} {a : ZMod 2}
    (f : X ⟶ Y) (hf : ∀ g, C.data.IsHomogeneous a (f g)) :
    A.data.IsHomogeneous a ((reconstructionUnderlyingEquivalence A C hC).inverse.map f) :=
  reconstructionSource_forward_grade A _ (reconstructionPullbackFamily_forward_grade A C hC f hf)

/-! The formulas for the unit and counit of Mathlib's composite reduce
their evenness to evenness of the selected component comparisons. -/

theorem reconstructionUnderlying_unit_hom_even (X : LinearCategory A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionUnderlyingEquivalence A C hC).unitIso.hom.app X) := by
  have h := A.laws.comp_grade _ _ (reconstructionSource_counit_inv_even A X)
    (reconstructionSource_forward_grade A _
      (reconstructionPullbackFamily_counit_inv_even A C hC _))
  rw [zero_add] at h
  have he := equivalence_trans_unit_hom (reconstructionSourceEquivalence A).symm
    (reconstructionPullbackFamilyEquivalence A C hC).symm X
  exact he.symm ▸ h

theorem reconstructionUnderlying_unit_inv_even (X : LinearCategory A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionUnderlyingEquivalence A C hC).unitIso.inv.app X) := by
  have h := A.laws.comp_grade _ _
    (reconstructionSource_forward_grade A _
      (reconstructionPullbackFamily_counit_hom_even A C hC _))
    (reconstructionSource_counit_hom_even A X)
  rw [zero_add] at h
  have he := equivalence_trans_unit_inv (reconstructionSourceEquivalence A).symm
    (reconstructionPullbackFamilyEquivalence A C hC).symm X
  exact he.symm ▸ h

theorem reconstructionUnderlying_counit_hom_even
    (X : PullbackCategory C.data hC (reconstructionTwistData A C hC))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous 0 ((reconstructionUnderlyingEquivalence A C hC).counitIso.hom.app X g) := by
  have h := C.laws.comp_grade _ _
    (reconstructionPullbackFamily_backward_grade A C hC _ (reconstructionSource_unit_inv_even A _) g)
    (reconstructionPullbackFamily_unit_inv_even A C hC X g)
  rw [zero_add] at h
  have he := congrArg (fun f : _ ⟶ X => f g)
    (equivalence_trans_counit_hom (reconstructionSourceEquivalence A).symm
      (reconstructionPullbackFamilyEquivalence A C hC).symm X)
  exact he.symm ▸ h

theorem reconstructionUnderlying_counit_inv_even
    (X : PullbackCategory C.data hC (reconstructionTwistData A C hC))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.IsHomogeneous 0 ((reconstructionUnderlyingEquivalence A C hC).counitIso.inv.app X g) := by
  have h := C.laws.comp_grade _ _ (reconstructionPullbackFamily_unit_hom_even A C hC X g)
    (reconstructionPullbackFamily_backward_grade A C hC _ (reconstructionSource_unit_hom_even A _) g)
  rw [zero_add] at h
  have he := congrArg (fun f : X ⟶ _ => f g)
    (equivalence_trans_counit_inv (reconstructionSourceEquivalence A).symm
      (reconstructionPullbackFamilyEquivalence A C hC).symm X)
  exact he.symm ▸ h

end RMod.Classification

import RMod.Classification.Instances.TwistedPullback
import RMod.Classification.Instances.EndGrading
import RMod.Classification.Proofs.SingleComponentHom

/-!
# The endomorphism algebra of an object supported at one degree

Evaluation at the support and extension by zero are specified inverse
maps. The algebra operations are the actual coordinatewise operations,
and evaluation preserves each homogeneous subspace.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (X : PullbackObj C t.data) (g : t.data.group)
  (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero)

noncomputable def pullbackSupportedEndAlgEquiv :
    End (C := LinearCategory (twistedPullback C hC t).toWeaklyPointedSuperfusion) X ≃ₐ[ℝ]
      End (C := LinearCategory ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩)
        (X g).val where
  toFun f := f g
  invFun f := singleComponentHom C t.data g f
  left_inv f := hom_ext_of_supported_source C t.data g hC.toWeaklyPointedSuperfusionLaws hX _ _
    (singleComponentHom_at C t.data g (f g))
  right_inv f := singleComponentHom_at C t.data g f
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

noncomputable def pullbackSupportedEndEquiv :
    SuperAlgEquiv
      (Category.endSuperAlgebra (K := ℝ)
        (C := LinearCategory (twistedPullback C hC t).toWeaklyPointedSuperfusion) X)
      (Category.endSuperAlgebra (K := ℝ)
        (C := LinearCategory ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩)
        (X g).val) := by
  let e := pullbackSupportedEndAlgEquiv C hC t X g hX
  refine ⟨e, ?_⟩
  intro a
  apply Submodule.ext
  intro f
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu g
  · intro hf
    refine ⟨singleComponentHom C t.data g f, ?_, singleComponentHom_at C t.data g f⟩
    exact singleComponentHom_grade C t.data g hC.toWeaklyPointedSuperfusionLaws f hf

end RMod.Classification

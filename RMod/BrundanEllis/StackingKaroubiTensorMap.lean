import RMod.BrundanEllis.StackingKaroubiSuperTensor
import RMod.BrundanEllis.StackingKaroubiWhisker
import RMod.BrundanEllis.StackingKaroubiEvenMaps

/-! After aligning tensor objects, the completed Hom tensor is still the
restriction of the ambient operation. In particular it agrees on even arrows
with the transported ordinary tensor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]

@[reassoc] theorem completedTensor_aligned_inclusion
    (P P' Q Q' : Even (Karoubi (Even C))) :
    enrichedTensorMap (completedTensor C) (completedTensor_objects C) P P' Q Q' ≫
      inclusion (ForgetEnrichment.to SuperVec (P ⊗ Q))
        (ForgetEnrichment.to SuperVec (P' ⊗ Q')) =
    (inclusion (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec P') ⊗ₘ
      inclusion (ForgetEnrichment.to SuperVec Q) (ForgetEnrichment.to SuperVec Q')) ≫
      enrichedTensorMap MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        (ForgetEnrichment.to SuperVec P).X (ForgetEnrichment.to SuperVec P').X
        (ForgetEnrichment.to SuperVec Q).X (ForgetEnrichment.to SuperVec Q').X := by
  let p : Karoubi (Even C) := ForgetEnrichment.to SuperVec P
  let p' : Karoubi (Even C) := ForgetEnrichment.to SuperVec P'
  let q : Karoubi (Even C) := ForgetEnrichment.to SuperVec Q
  let q' : Karoubi (Even C) := ForgetEnrichment.to SuperVec Q'
  change ((completedTensor C).map (p, q) (p', q') ≫
    eqToHom (congrArg₂ homObject (completedTensor_object C p q) (completedTensor_object C p' q'))) ≫
      inclusion (KaroubiTensor.objectTensor p q) (KaroubiTensor.objectTensor p' q') = _
  rw [assoc, inclusion_transport (completedTensor_object C p q) (completedTensor_object C p' q')]
  simp only [eqToHom_refl, Category.comp_id]
  exact completedTensor_map_inclusion C p p' q q'

theorem completedTensor_even {P P' Q Q' : Even (Karoubi (Even C))}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (λ_ (𝟙_ SuperVec)).inv ≫
      (ForgetEnrichment.homTo SuperVec f ⊗ₘ ForgetEnrichment.homTo SuperVec g) ≫
        enrichedTensorMap (completedTensor C) (completedTensor_objects C) P P' Q Q' =
      ForgetEnrichment.homTo SuperVec (f ⊗ₘ g) := by
  apply (cancel_mono (inclusion (ForgetEnrichment.to SuperVec (P ⊗ Q))
    (ForgetEnrichment.to SuperVec (P' ⊗ Q')))).1
  rw [assoc, assoc, completedTensor_aligned_inclusion]
  simp only [tensorHom_comp_tensorHom_assoc, even_hom_inclusion]
  have h := MonoidalSuperCategory.tensor_even (C := C)
    ((evenEquivalence (C := C)).functor.map f).f ((evenEquivalence (C := C)).functor.map g).f
  have hfg := congrArg Karoubi.Hom.f (even_tensor_map f g)
  exact h.trans (congrArg (eHomEquiv SuperVec) hfg.symm)

end RMod.BrundanEllis.Stacking.KaroubiSuper

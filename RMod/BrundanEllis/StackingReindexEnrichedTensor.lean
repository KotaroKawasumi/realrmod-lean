import RMod.BrundanEllis.StackingReindexEvenTensor
import RMod.BrundanEllis.StackingExternalTensorHomPoints
import RMod.BrundanEllis.StackingKaroubiNaturality

/-! The coordinate comparison is natural on the whole enriched Hom object.
The chronological tensor sign occurs equally on both sides of the square. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.Classification
/-- Scalar compatibility is discharged abstractly before instantiating the reference model. -/
theorem coordinateRestrictionTensorHom_scaled_naturality
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (f : t.data.group →* s.data.group) (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
    (hν : ∀ g h, t.data.nu g h = s.data.nu (f g) (f h))
    {X X' Y Y' : PullbackObj C s.data}
    (u : PullbackHom C s.data X X') (v : PullbackHom C s.data Y Y') (k : t.data.group) (r : ℝ) :
    C.comp (C.smul r (convolutionHom C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).map u)
      ((coordinateRestrictionData C hC s t f hρ).map v) k))
      (coordinateRestrictionTensorHom C hC s t f hρ hν X' Y' k) =
    C.comp (coordinateRestrictionTensorHom C hC s t f hρ hν X Y k)
      (C.smul r (convolutionHom C hC s.data u v (f k))) := by
  rw [hC.smul_comp, hC.comp_smul]
  exact congrArg (C.smul r)
    (coordinateRestrictionTensorHom_naturality C hC s t f hρ hν u v k)
end RMod.Classification

namespace RMod.BrundanEllis.Stacking
open RMod.Classification RMod.Legacy

/-- Homogeneous maps are restricted by the same coordinate function. -/
theorem pullbackReindex_hom_value (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    (X Y : Even (pullback s)) (a : ZMod 2) (u : SHom (pullback s) X Y a) :
    ((pullbackReindex s f).map X Y a u).val = fun k => u.val (f k) := rfl

attribute [local irreducible] pullbackReindex pullbackReindexTensorMap

/-- Naturality holds for the enriched tensor, in both homogeneous degrees. -/
theorem pullbackReindexTensorMap_enriched_naturality (s : Twist) {H : FiniteGrp.{0}}
    (f : H →* s.group) (X X' Y Y' : Even (pullback s)) :
    let F := pullbackReindex s f
    (F.map X X' ⊗ₘ F.map Y Y') ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X')
        (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y)
        (pullbackReindexTensorMap s f X' Y') =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      F.map (X ⊗ Y : Even (pullback s)) (X' ⊗ Y' : Even (pullback s)) ≫
      eHomWhiskerRight SuperVec (pullbackReindexTensorMap s f X Y)
        (F.forget.obj (X' ⊗ Y')) := by
  dsimp only
  funext a
  apply tensorObj_ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro u v
  apply Subtype.ext
  funext k
  change (eHomWhiskerLeft SuperVec _ (pullbackReindexTensorMap s f X' Y') a
    (enrichedTensorMap (C := pullback (reindexTwist s f).val) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects _ _ _ _ a
      (((pullbackReindex s f).map X X' ⊗ₘ (pullbackReindex s f).map Y Y') a
        (gradedTmul _ _ i j a hij u v)))).val k =
    (eHomWhiskerRight SuperVec (pullbackReindexTensorMap s f X Y) _ a
      ((pullbackReindex s f).map (X ⊗ Y : Even (pullback s)) (X' ⊗ Y' : Even (pullback s)) a
        (enrichedTensorMap (C := pullback s) MonoidalSuperCategory.tensor
          MonoidalSuperCategory.tensor_objects _ _ _ _ a (gradedTmul _ _ i j a hij u v)))).val k
  erw [tensorHom_gradedTmul]
  erw [pullback_post_apply (reindexTwist s f).val]
  erw [pullback_pre_apply (reindexTwist s f).val
    (X := (pullbackReindex s f).forget.obj X ⊗ (pullbackReindex s f).forget.obj Y)
    (Y := (pullbackReindex s f).forget.obj (X ⊗ Y))
    (Z := (pullbackReindex s f).forget.obj (X' ⊗ Y')) a
    (pullbackReindexTensorMap s f X Y) _ k]
  erw [pullbackTensor_tmul (reindexTwist s f).val]
  erw [pullbackReindex_hom_value s f X X' i u,
    pullbackReindex_hom_value s f Y Y' j v,
    pullbackReindex_hom_value s f (X ⊗ Y) (X' ⊗ Y') a]
  dsimp only
  erw [pullbackTensor_tmul s X X' Y Y' i j a hij u v (f k)]
  rw [pullbackReindexTensorMap_value s f X' Y', pullbackReindexTensorMap_value s f X Y]
  with_unfolding_all
    exact coordinateRestrictionTensorHom_scaled_naturality reference.data referenceProperty
      (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl) (fun _ _ => rfl)
      u.val v.val k ((-1 : ℝ) ^ (i * j).val)

end RMod.BrundanEllis.Stacking

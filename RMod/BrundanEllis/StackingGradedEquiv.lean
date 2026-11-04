import RMod.BrundanEllis.StackingGradedTensor
import RMod.BrundanEllis.StackingTensorSign

/-! A degree-preserving isomorphism of total tensor spaces yields an
isomorphism on every enriched Hom component. The chronological sign is
retained explicitly, so the criterion applies to the actual exterior map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory CategoryTheory.MonoidalCategory GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking.Graded
open Superfusion.Bimod
variable {V W U : Type}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]
  (v : ZMod 2 → Submodule ℝ V) (w : ZMod 2 → Submodule ℝ W) (u : ZMod 2 → Submodule ℝ U)
  [DirectSum.Decomposition v] [DirectSum.Decomposition w] [DirectSum.Decomposition u]
  (e : V ⊗[ℝ] W ≃ₗ[ℝ] U)
  (he : ∀ {a z}, z ∈ tensorGrading v w a → e z ∈ u a)

/-- Both directions of the total isomorphism preserve the homogeneous layers. -/
def restrictEquiv (a : ZMod 2) : tensorGrading v w a ≃ₗ[ℝ] u a :=
  LinearEquiv.ofBijective
    ((e.toLinearMap.domRestrict _).codRestrict _ (fun z => he z.property)) (by
      constructor
      · intro x y h
        exact Subtype.ext (e.injective (congrArg Subtype.val h))
      · intro y
        refine ⟨⟨e.symm y.val, gradedLinearEquiv_symm_mem (tensorGrading v w) u e he y.property⟩, ?_⟩
        exact Subtype.ext (e.apply_symm_apply y.val))

theorem restrictEquiv_val (a : ZMod 2) (x : tensorGrading v w a) :
    (restrictEquiv v w u e he a x).val = e x.val := rfl

/-- Realize the chronological map on the graded tensor component. -/
def signedTensorEquiv (a : ZMod 2) : (object v ⊗ object w) a ≃ₗ[ℝ] u a :=
  (tensorSignEquiv (object v) (object w) a).trans
    ((includeTensorEquiv v w a).trans (restrictEquiv v w u e he a))

theorem signedTensorEquiv_tmul (i j a : ZMod 2) (h : i + j = a) (x : v i) (y : w j) :
    (signedTensorEquiv v w u e he a
      (ιTensorObj (object v) (object w) i j a h (x ⊗ₜ[ℝ] y))).val =
        ((-1 : ℝ) ^ (i * j).val) • e (x.val ⊗ₜ[ℝ] y.val) := by
  change e (includeTensor v w a (tensorSign (object v) (object w) a
    (ιTensorObj (object v) (object w) i j a h (x ⊗ₜ[ℝ] y)))) = _
  rw [tensorSign_tmul]
  change e ((includeTensor v w a).hom (_ • _)) = _
  rw [map_smul, includeTensor_tmul, map_smul]

include he in
/-- Equality on homogeneous pure tensors proves bijectivity of the given map. -/
theorem bijective_of_signed_tmul (a : ZMod 2)
    (F : (object v ⊗ object w) a ⟶ ModuleCat.of ℝ (u a))
    (hF : ∀ i j (h : i + j = a) (x : v i) (y : w j),
      (F (ιTensorObj (object v) (object w) i j a h (x ⊗ₜ[ℝ] y))).val =
        ((-1 : ℝ) ^ (i * j).val) • e (x.val ⊗ₜ[ℝ] y.val)) : Function.Bijective F := by
  have hmap : F = ModuleCat.ofHom (signedTensorEquiv v w u e he a).toLinearMap := by
    apply tensorObj_ext
    intro i j h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    apply Subtype.ext
    exact (hF i j h x y).trans (signedTensorEquiv_tmul v w u e he i j a h x y).symm
  rw [hmap]
  exact (signedTensorEquiv v w u e he a).bijective

end RMod.BrundanEllis.Stacking.Graded

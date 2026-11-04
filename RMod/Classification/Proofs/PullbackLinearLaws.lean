import RMod.Classification.Instances.PullbackLinearCategory
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finite-dimensional graded Hom spaces of the pullback

Mathlib's finite basis of the dependent-product Hom module supplies both
spanning and unique coordinates in the frozen statement's finite-sum
format. The original two-grade decomposition is selected coordinatewise;
disjointness is checked in every component.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_hasFiniteBasis (X Y : PullbackCategory C hC t) :
    (twistedPullbackData C hC t ht).HasFiniteBasis X Y := by
  let b := Module.finBasis ℝ (X ⟶ Y)
  refine ⟨_, b, b.equivFun, ?_, ?_⟩
  · intro f
    rw [PullbackCategory.finSum_eq_sum C hC t ht]
    exact b.sum_equivFun f
  · intro f c he
    rw [PullbackCategory.finSum_eq_sum C hC t ht] at he
    apply b.equivFun.symm.injective
    rw [b.equivFun.symm_apply_apply, b.equivFun_symm_apply]
    exact he

theorem twistedPullback_grade_decomposition {X Y : PullbackObj C t} (f : PullbackHom C t X Y) :
    ∃ f₀ f₁ : PullbackHom C t X Y,
      (twistedPullbackData C hC t ht).IsHomogeneous 0 f₀ ∧
      (twistedPullbackData C hC t ht).IsHomogeneous 1 f₁ ∧
      (twistedPullbackData C hC t ht).add f₀ f₁ = f := by
  choose f₀ f₁ h₀ h₁ he using fun g => hC.grade_decomposition (f g)
  exact ⟨f₀, f₁, h₀, h₁, funext he⟩

theorem twistedPullback_grade_disjoint {X Y : PullbackObj C t} (f : PullbackHom C t X Y)
    (h₀ : (twistedPullbackData C hC t ht).IsHomogeneous 0 f)
    (h₁ : (twistedPullbackData C hC t ht).IsHomogeneous 1 f) :
    f = (twistedPullbackData C hC t ht).zero := by
  exact funext (fun g => hC.grade_disjoint (f g) (h₀ g) (h₁ g))

end RMod.Classification

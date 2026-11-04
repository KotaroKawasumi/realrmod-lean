import RMod.Hierarchy.Bridge.RoundtripTotal
import RMod.Hierarchy.Bridge.LegacyTensor

/-!
# Tensor compatibility of the round trip

The two convention corrections cancel. The comparison on total morphisms
therefore preserves the enriched tensor product exactly.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (A : WeaklyPointedFusionPiSupercategory)

theorem homogeneousEmbedding_sum {X Y : A.data.Obj} (f : THom (originalSuper A).data X Y) :
    homogeneousEmbedding (originalSuper A) X Y 0 (f 0) +
      homogeneousEmbedding (originalSuper A) X Y 1 (f 1) = f := by
  funext a
  rcases Classification.parity_cases a with rfl | rfl <;>
    simp [homogeneousEmbedding]

theorem roundtripForward_tensor {X X' Y Y' : A.data.Obj}
    (f : THom (originalSuper A).data X X') (g : THom (originalSuper A).data Y Y') :
    totalHomEquiv (legacyCategory A) _ _
      (tTensor (ofOldMonoidalStructureData (legacyCategory A))
        (tMap (roundtripForwardData A) f) (tMap (roundtripForwardData A) g)) =
      tTensor A.data.monoidal f g := by
  rw [totalHomEquiv_tTensor]
  let C := A.toMonoidalPiSupercategory.monoidal
  let f₀ := homogeneousEmbedding (originalSuper A) X X' 0 (f 0)
  let f₁ := homogeneousEmbedding (originalSuper A) X X' 1 (f 1)
  let g₀ := homogeneousEmbedding (originalSuper A) Y Y' 0 (g 0)
  let g₁ := homogeneousEmbedding (originalSuper A) Y Y' 1 (g 1)
  have hf₀ := homogeneousEmbedding_mem (originalSuper A) X X' 0 (f 0)
  have hf₁ := homogeneousEmbedding_mem (originalSuper A) X X' 1 (f 1)
  have hg₀ := homogeneousEmbedding_mem (originalSuper A) Y Y' 0 (g 0)
  have hg₁ := homogeneousEmbedding_mem (originalSuper A) Y Y' 1 (g 1)
  change (legacyTensor C f₀ g₀ + (-1 : ℝ) • legacyTensor C f₁ g₁) +
    (legacyTensor C f₀ g₁ + legacyTensor C f₁ g₀) = _
  rw [legacyTensor_even_left C f₀ g₀ hf₀,
    legacyTensor_homogeneous C 1 1 f₁ g₁ hf₁ hg₁,
    legacyTensor_even_left C f₀ g₁ hf₀,
    legacyTensor_even_right C f₁ g₀ hg₀]
  change (tTensor A.data.monoidal f₀ g₀ + (-1 : ℝ) •
    ((-1 : ℝ) ^ ((1 : ZMod 2) * 1).val • tTensor A.data.monoidal f₁ g₁)) +
    (tTensor A.data.monoidal f₀ g₁ + tTensor A.data.monoidal f₁ g₀) = _
  simp only [mul_one, ZMod.val_one, pow_one, neg_one_smul, neg_neg]
  have h := congrArg₂ (tTensor A.data.monoidal)
    (homogeneousEmbedding_sum A f) (homogeneousEmbedding_sum A g)
  simp only [tTensor_add_left, tTensor_add_right] at h
  change (tTensor A.data.monoidal f₀ g₀ + tTensor A.data.monoidal f₁ g₀) +
    (tTensor A.data.monoidal f₀ g₁ + tTensor A.data.monoidal f₁ g₁) = _ at h
  rw [← h]
  change (tTensor A.data.monoidal f₀ g₀ + tTensor A.data.monoidal f₁ g₁) +
    (tTensor A.data.monoidal f₀ g₁ + tTensor A.data.monoidal f₁ g₀) = _
  abel

end RMod.Legacy.Hierarchy

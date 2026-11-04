import RMod.BrundanEllis.StackingExternalPure
import RMod.BrundanEllis.StackingProductSuperMonoidal
import RMod.Hierarchy.Instances.TensorInterchangePoints

/-! Generator formulas for the actual tensor Hom maps. The product tensor
crosses the two middle morphisms, while each pullback tensor retains the
chronological sign of the old-model adapter. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking
open RMod.Legacy RMod.Legacy.Hierarchy RMod.Classification

/-- The enriched pullback tensor is the specified convolution on coordinates. -/
theorem pullbackTensor_tmul (s : Twist) (X X' Y Y' : Even (pullback s))
    (i j a : ZMod 2) (hij : i + j = a)
    (f : SHom (pullback s) X X' i) (q : SHom (pullback s) Y Y' j) (g : s.group) :
    (enrichedTensorMap (C := pullback s) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects X X' Y Y' a
        (gradedTmul (SHom (pullback s) X X') (SHom (pullback s) Y Y')
          i j a hij f q)).val g =
      reference.data.smul ((-1 : ℝ) ^ (i * j).val)
        (convolutionHom reference.data referenceProperty (oldTwist s).data f.val q.val g) := by
  with_unfolding_all
    exact congrFun
      (oldTensorMap_tmul (oldPullback s).toWeaklyPointedSuperfusion X X' Y Y' i j a hij f q) g

section
variable {A B : Type} [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

/-- Four homogeneous generators expose precisely the middle Koszul crossing. -/
theorem productTensor_tmul (X X' Y Y' : Even (SuperTensorProduct A B))
    (i j k l a : ZMod 2) (h : i + j + k + l = a)
    (f : SHom A X.1 X'.1 i) (q : SHom B X.2 X'.2 j)
    (f' : SHom A Y.1 Y'.1 k) (q' : SHom B Y.2 Y'.2 l) :
    (productTensor A B).map (X, Y) (X', Y') a
      (gradedTmul (SHom (SuperTensorProduct A B) X X') (SHom (SuperTensorProduct A B) Y Y')
        (i + j) (k + l) a (by rw [← add_assoc, h])
        (gradedTmul (SHom A X.1 X'.1) (SHom B X.2 X'.2) i j (i + j) rfl f q)
        (gradedTmul (SHom A Y.1 Y'.1) (SHom B Y.2 Y'.2) k l (k + l) rfl f' q')) =
      (-1 : ℝ) ^ (j * k).val •
        gradedTmul (SHom A (X.1 ⊗ Y.1 : Even A) (X'.1 ⊗ Y'.1 : Even A))
          (SHom B (X.2 ⊗ Y.2 : Even B) (X'.2 ⊗ Y'.2 : Even B))
          (i + k) (j + l) a (by linear_combination h)
          (enrichedTensorMap (C := A) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
            X.1 X'.1 Y.1 Y'.1 (i + k) (gradedTmul _ _ i k (i + k) rfl f f'))
          (enrichedTensorMap (C := B) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
            X.2 X'.2 Y.2 Y'.2 (j + l) (gradedTmul _ _ j l (j + l) rfl q q')) := by
  rw [productTensor_map]
  change ((enrichedTensorMap (C := A) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
      X.1 X'.1 Y.1 Y'.1 ⊗ₘ
    enrichedTensorMap (C := B) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
      X.2 X'.2 Y.2 Y'.2) a
      (tensorμ (SHom A X.1 X'.1) (SHom B X.2 X'.2)
        (SHom A Y.1 Y'.1) (SHom B Y.2 Y'.2) a _)) = _
  erw [tensorμ_gradedTmul _ _ _ _ i j k l a h, map_smul, tensorHom_gradedTmul]

end
end RMod.BrundanEllis.Stacking

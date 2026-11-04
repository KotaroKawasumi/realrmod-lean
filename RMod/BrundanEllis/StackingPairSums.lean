import RMod.BrundanEllis.StackingPairing

/-! A finite direct sum of paired objects is a retract of the pair of the
two direct sums. The diagonal inclusions and projections have identity
matrix on the selected diagonal summands and zero off that diagonal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
local instance : Preadditive SuperVec := RMod.Legacy.superVecPreadditive
local instance : MonoidalPreadditive SuperVec := RMod.Legacy.superVecMonoidalPreadditive
variable {A B D : WeaklyPointedFusionPiSuperCat}
  (F : SuperFunctor (SuperTensorProduct A B) D)

theorem evenPair_zero_left {X X' : Even A} {Y Y' : Even B} (g : Y ⟶ Y') :
    (evenPair F).map (X := (X, Y)) (Y := (X', Y')) (0, g) = 0 := by
  apply_fun ForgetEnrichment.homTo SuperVec
  · change (λ_ (𝟙_ SuperVec)).inv ≫
      ((0 : 𝟙_ SuperVec ⟶ SHom A X X') ⊗ₘ ForgetEnrichment.homTo SuperVec g) ≫
        F.map (X, Y) (X', Y') = 0
    simp only [MonoidalPreadditive.zero_tensor, comp_zero, zero_comp]
  · intro f g h
    exact congrArg (ForgetEnrichment.homOf SuperVec) h

/-- The finite diagonal of a rectangular pair of sums is an even retract. -/
def pairSumRetract {n : ℕ} (X : Fin n → Even A) (Y : Fin n → Even B) :
    Retract (⨁ fun i => (evenPair F).obj (X i, Y i))
      ((evenPair F).obj (⨁ X, ⨁ Y)) where
  i := biproduct.desc fun i => (evenPair F).map (biproduct.ι X i, biproduct.ι Y i)
  r := biproduct.lift fun i => (evenPair F).map (biproduct.π X i, biproduct.π Y i)
  retract := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [assoc, biproduct.ι_desc_assoc, biproduct.lift_π,
      ← CategoryTheory.Functor.map_comp, Category.comp_id]
    by_cases h : i = j
    · subst j
      simp only [CategoryTheory.prod_comp, biproduct.ι_π_self]
      exact (evenPair F).map_id (X i, Y i)
    · simp only [CategoryTheory.prod_comp, biproduct.ι_π_ne _ h]
      exact evenPair_zero_left F 0

end RMod.BrundanEllis.Stacking

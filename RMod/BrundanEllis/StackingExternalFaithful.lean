import RMod.BrundanEllis.StackingExternalTotal
import RMod.BrundanEllis.StackingExternalPure
import RMod.BrundanEllis.StackingGradedEquiv

/-! Full faithfulness is proved for the previously constructed exterior
pairing itself. Finite coordinate distribution gives the total isomorphism;
its degree restriction and chronological sign give the enriched isomorphism. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Every homogeneous Hom map of the exterior pairing is bijective. -/
theorem exteriorPairing_bijective (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t)) (a : ZMod 2) :
    Function.Bijective ((exteriorPairing s t).map X Y a) := by
  let v := LinearCategory.grade (oldPullback s).toWeaklyPointedSuperfusion X.1 Y.1
  let w := LinearCategory.grade (oldPullback t).toWeaklyPointedSuperfusion X.2 Y.2
  let u := LinearCategory.grade (oldPullback (exteriorTwist s t).val).toWeaklyPointedSuperfusion
    (exteriorObject s t X.1 X.2) (exteriorObject s t Y.1 Y.2)
  letI : DirectSum.Decomposition v :=
    (LinearCategory.grade_isInternal (oldPullback s).toWeaklyPointedSuperfusion X.1 Y.1).chooseDecomposition
  letI : DirectSum.Decomposition w :=
    (LinearCategory.grade_isInternal (oldPullback t).toWeaklyPointedSuperfusion X.2 Y.2).chooseDecomposition
  letI : DirectSum.Decomposition u :=
    (LinearCategory.grade_isInternal (oldPullback (exteriorTwist s t).val).toWeaklyPointedSuperfusion
      (exteriorObject s t X.1 X.2) (exteriorObject s t Y.1 Y.2)).chooseDecomposition
  let e := exteriorTotalEquiv s t X.1 Y.1 X.2 Y.2
  have he : ∀ {a z}, z ∈ Superfusion.Bimod.tensorGrading v w a → e z ∈ u a :=
    fun {_ _} hz => exteriorTotalEquiv_grade s t X.1 Y.1 X.2 Y.2 hz
  apply Graded.bijective_of_signed_tmul v w u e he a ((exteriorPairing s t).map X Y a)
  intro i j hij f q
  funext gh
  change ((exteriorPairing s t).map X Y a
    (ιTensorObj (SHom (pullback s) X.1 Y.1) (SHom (pullback t) X.2 Y.2)
      i j a hij (f ⊗ₜ[ℝ] q))).val gh =
    reference.data.smul ((-1 : ℝ) ^ (i * j).val)
      (exteriorTotalEquiv s t X.1 Y.1 X.2 Y.2 (f.val ⊗ₜ[ℝ] q.val) gh)
  rw [exteriorPairing_tmul, exteriorTotalEquiv_tmul]

end RMod.BrundanEllis.Stacking

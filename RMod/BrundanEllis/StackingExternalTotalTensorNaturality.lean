import RMod.BrundanEllis.StackingExternalEnrichedTensorNaturality
import RMod.BrundanEllis.StackingHomEquationTotal

/-! Evaluate the enriched comparison on total morphisms. This is the tensor
naturality equation used by the public monoidal superequivalence contract. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
attribute [local irreducible] reversedExteriorPairing reversedExteriorTensorIso

/-- The exterior comparison is natural on arbitrary, possibly inhomogeneous maps. -/
theorem reversedExteriorTensorIso_total_naturality (s t : Twist)
    {X X' Y Y' : Even (SuperTensorProduct (pullback s) (pullback t))}
    (f : THom (SuperTensorProduct (pullback s) (pullback t)) X X')
    (g : THom (SuperTensorProduct (pullback s) (pullback t)) Y Y') :
    let F := reversedExteriorPairing s t
    tComp (exteriorModel s t)
      (tTensor (C := exteriorModel s t) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        (tMap F f) (tMap F g))
      (evenPoint (reversedExteriorTensorIso s t X' Y').hom) =
    tComp (exteriorModel s t) (evenPoint (reversedExteriorTensorIso s t X Y).hom)
      (tMap F (tTensor (C := SuperTensorProduct (pullback s) (pullback t))
        MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects f g)) := by
  let F := reversedExteriorPairing s t
  let L := (F.map X X' ⊗ₘ F.map Y Y') ≫
    enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y')
  let R := (productTensor (pullback s) (pullback t)).map (X, Y) (X', Y') ≫
    F.map (X ⊗ Y : Even (SuperTensorProduct (pullback s) (pullback t)))
      (X' ⊗ Y' : Even (SuperTensorProduct (pullback s) (pullback t)))
  have hn := homEquation_total (D := exteriorModel s t)
    (A := F.forget.obj X ⊗ F.forget.obj Y) (B := F.forget.obj X' ⊗ F.forget.obj Y')
    (A' := F.forget.obj (X ⊗ Y)) (B' := F.forget.obj (X' ⊗ Y')) L R
    (reversedExteriorTensorIso s t X Y).hom (reversedExteriorTensorIso s t X' Y').hom
    (by simpa only [L, R, F, Category.assoc] using
      reversedExteriorTensorIso_enriched_naturality s t X X' Y Y')
    (RMod.Regression.tensorPoint f g)
  have hl : (fun a => L a (RMod.Regression.tensorPoint f g a)) =
      tTensor (C := exteriorModel s t) MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects (tMap F f) (tMap F g) := by
    funext a
    change enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects _ _ _ _ a
      ((F.map X X' ⊗ₘ F.map Y Y') a (RMod.Regression.tensorPoint f g a)) = _
    rw [congrFun (RMod.Regression.tensorPoint_map (F.map X X') (F.map Y Y') f g) a]
    rfl
  erw [hl] at hn
  exact hn

end RMod.BrundanEllis.Stacking

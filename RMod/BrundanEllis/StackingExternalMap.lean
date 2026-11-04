import RMod.BrundanEllis.StackingExternalObjects

/-! Coordinatewise tensoring of the two enriched evaluation functors gives
an actual graded linear exterior map. The evaluations jointly detect maps
into a pullback Hom object, so its functor laws can be checked componentwise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- The enriched tensor in the reference category applied to two evaluations. -/
def exteriorComponent (s t : Twist) (g : s.group) (h : t.group) :
    SuperFunctor (SuperTensorProduct (pullback s) (pullback t)) referenceCategory :=
  (RMod.tensorEnrichedFunctors SuperVec (evaluate s g) (evaluate t h)).comp SuperVec
    (RMod.alignedTensor SuperVec (MonoidalSuperCategory.tensor (C := referenceCategory))
      MonoidalSuperCategory.tensor_objects)

/-- A graded map into a pullback is determined by all of its coordinates. -/
theorem evaluate_hom_ext (s : Twist) {X Y : pullback s} {V : SuperVec}
    {f g : V ⟶ SHom (pullback s) X Y}
    (h : ∀ k, f ≫ (evaluate s k).map X Y = g ≫ (evaluate s k).map X Y) : f = g := by
  apply funext
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext k
  exact congrArg (fun q => (q a v).val) (h k)

/-- The external map assembles the genuine tensor maps in the reference. -/
def exteriorMap (s t : Twist) (X Y : SuperTensorProduct (pullback s) (pullback t)) :
    SHom (SuperTensorProduct (pullback s) (pullback t)) X Y ⟶
      SHom (exteriorModel s t) (exteriorObject s t X.1 X.2) (exteriorObject s t Y.1 Y.2) :=
  fun a => ModuleCat.ofHom {
    toFun := fun f => ⟨fun gh => ((exteriorComponent s t gh.1 gh.2).map X Y a f).val,
      fun gh => ((exteriorComponent s t gh.1 gh.2).map X Y a f).property⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext gh
      exact congrArg Subtype.val (map_add ((exteriorComponent s t gh.1 gh.2).map X Y a).hom f g)
    map_smul' := by
      intro r f
      apply Subtype.ext
      funext gh
      exact congrArg Subtype.val (map_smul ((exteriorComponent s t gh.1 gh.2).map X Y a).hom r f) }

/-- Projection of the assembled map recovers the given component tensor. -/
theorem exteriorMap_evaluate (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t)) (g : s.group) (h : t.group) :
    exteriorMap s t X Y ≫
      (evaluate (exteriorTwist s t).val (g, h)).map
        (exteriorObject s t X.1 X.2) (exteriorObject s t Y.1 Y.2) =
      (exteriorComponent s t g h).map X Y := by
  apply funext
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rfl

end RMod.BrundanEllis.Stacking

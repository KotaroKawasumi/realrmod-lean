import RMod.BrundanEllis.StackingExternalPairing
import RMod.BrundanEllis.StackingEnrichedSwap

/-! Reverse the reference tensor order for the specified cochain convention.
The cross term in nu is bit(s_g) bit(t_h'), so the comparison exchanges the
middle factors in (Y_h tensor X_g) tensor (Y_h' tensor X_g').  Reindexing below
is an enriched functor only; its monoidal structure is not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- Swap the two support coordinates, retaining every reference object. -/
def reverseExteriorObject (s t : Twist) (Z : exteriorModel t s) : exteriorModel s t :=
  fun gh => ⟨(Z (gh.2, gh.1)).val, by
    have h := (Z (gh.2, gh.1)).property
    change RMod.Classification.InComponent reference.data.toWeaklyPointedSuperfusionData
      ((s.rho gh.1).toAdd + (t.rho gh.2).toAdd) _
    change RMod.Classification.InComponent reference.data.toWeaklyPointedSuperfusionData
      ((t.rho gh.2).toAdd + (s.rho gh.1).toAdd) _ at h
    simpa only [add_comm] using h⟩

/-- Support reversal is a linear map in each parity, before any tensor comparison. -/
def reverseExteriorMap (s t : Twist) (X Y : exteriorModel t s) :
    SHom (exteriorModel t s) X Y ⟶
      SHom (exteriorModel s t) (reverseExteriorObject s t X) (reverseExteriorObject s t Y) :=
  fun a => ModuleCat.ofHom {
    toFun := fun f => ⟨fun gh => f.val (gh.2, gh.1), fun gh => f.property (gh.2, gh.1)⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Evaluation of the reindexed map is the original evaluation at the swapped coordinate. -/
theorem reverseExteriorMap_evaluate (s t : Twist) (X Y : exteriorModel t s)
    (g : s.group) (h : t.group) :
    reverseExteriorMap s t X Y ≫
      (evaluate (exteriorTwist s t).val (g, h)).map
        (reverseExteriorObject s t X) (reverseExteriorObject s t Y) =
    (evaluate (exteriorTwist t s).val (h, g)).map X Y := by
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rfl

/-- Enriched reindexing between the two external models. -/
def reverseExterior (s t : Twist) : SuperFunctor (exteriorModel t s) (exteriorModel s t) where
  obj := reverseExteriorObject s t
  map := reverseExteriorMap s t
  map_id X := by
    apply evaluate_hom_ext (exteriorTwist s t).val
    rintro ⟨g, h⟩
    rw [Category.assoc, reverseExteriorMap_evaluate]
    rw [(evaluate (exteriorTwist t s).val (h, g)).map_id,
      (evaluate (exteriorTwist s t).val (g, h)).map_id]
    rfl
  map_comp X Y Z := by
    apply evaluate_hom_ext (exteriorTwist s t).val
    rintro ⟨g, h⟩
    rw [Category.assoc, reverseExteriorMap_evaluate]
    rw [Category.assoc, (evaluate (exteriorTwist s t).val (g, h)).map_comp]
    rw [← Category.assoc, tensorHom_comp_tensorHom, reverseExteriorMap_evaluate,
      reverseExteriorMap_evaluate]
    exact (evaluate (exteriorTwist t s).val (h, g)).map_comp X Y Z

/-- The exterior pairing in the order matching the prescribed cross term. -/
def reversedExteriorPairing (s t : Twist) :
    SuperFunctor (SuperTensorProduct (pullback s) (pullback t)) (exteriorModel s t) :=
  ((enrichedSwap SuperVec (pullback s) (pullback t)).comp SuperVec (exteriorPairing t s)).comp
    SuperVec (reverseExterior s t)

theorem reversedExteriorPairing_object (s t : Twist) (X : pullback s) (Y : pullback t)
    (g : s.group) (h : t.group) :
    ((reversedExteriorPairing s t).obj (X, Y) (g, h)).val =
      reference.data.tensorObj (Y h).val (X g).val := rfl

/-- Reversing the coordinates twice retains the original object exactly. -/
theorem reverseExteriorObject_twice (s t : Twist) (X : exteriorModel s t) :
    reverseExteriorObject s t (reverseExteriorObject t s X) = X := by
  funext gh
  apply Subtype.ext
  rfl

end RMod.BrundanEllis.Stacking

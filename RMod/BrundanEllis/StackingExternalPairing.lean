import RMod.BrundanEllis.StackingExternalMap

/-! The external pairing uses the reference tensor on objects and on every
graded Hom component. Functoriality is verified after all coordinate
evaluations, whose maps jointly detect equality. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- The genuine exterior superfunctor into the explicit cochain model. -/
def exteriorPairing (s t : Twist) :
    SuperFunctor (SuperTensorProduct (pullback s) (pullback t)) (exteriorModel s t) where
  obj X := exteriorObject s t X.1 X.2
  map := exteriorMap s t
  map_id X := by
    apply evaluate_hom_ext (exteriorTwist s t).val
    rintro ⟨g, h⟩
    rw [Category.assoc, exteriorMap_evaluate]
    rw [(exteriorComponent s t g h).map_id,
      (evaluate (exteriorTwist s t).val (g, h)).map_id]
    rfl
  map_comp X Y Z := by
    apply evaluate_hom_ext (exteriorTwist s t).val
    rintro ⟨g, h⟩
    rw [Category.assoc, exteriorMap_evaluate]
    rw [Category.assoc, (evaluate (exteriorTwist s t).val (g, h)).map_comp]
    rw [← Category.assoc, tensorHom_comp_tensorHom, exteriorMap_evaluate, exteriorMap_evaluate]
    exact (exteriorComponent s t g h).map_comp X Y Z

/-- The coordinate map is fixed, including its graded tensor convention. -/
theorem exteriorPairing_coordinate (s t : Twist)
    (X Y : SuperTensorProduct (pullback s) (pullback t)) (g : s.group) (h : t.group) :
    (exteriorPairing s t).map X Y ≫
      (evaluate (exteriorTwist s t).val (g, h)).map
        ((exteriorPairing s t).obj X) ((exteriorPairing s t).obj Y) =
      (exteriorComponent s t g h).map X Y := exteriorMap_evaluate s t X Y g h

end RMod.BrundanEllis.Stacking

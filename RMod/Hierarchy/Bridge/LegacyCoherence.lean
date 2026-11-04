import RMod.Hierarchy.Bridge.LegacyTensor
import RMod.Hierarchy.Instances.EvenTotal

/-!
# Even coherence maps in the legacy presentation

The tensor convention correction is trivial on even morphisms. Hence all
structural isomorphisms, the pentagon, the triangle, and the exact-pairing
identities are obtained by evaluating the same even-category equations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy
variable (C : MonoidalSupercategory)

theorem legacyTensor_even_maps {X X' Y Y' : Even C.super} (f : X ⟶ X') (g : Y ⟶ Y') :
    legacyTensor C (evenPoint f) (evenPoint g) = evenPoint (f ⊗ₘ g) := by
  rw [legacyTensor_even_left C _ _ (evenPoint_mem_grade C.super f)]
  exact (evenPoint_tensor C.data.monoidal f g).symm

theorem legacyTensor_id (X Y : C.data.Obj) :
    (toOldData C).tensorHom ((toOldData C).id X) ((toOldData C).id Y) =
      (toOldData C).id ((toOldData C).tensorObj X Y) := by
  change legacyTensor C (evenPoint (C.data.id X)) (evenPoint (C.data.id Y)) = _
  rw [legacyTensor_even_left C _ _ (evenPoint_mem_grade C.super (C.data.id X)),
    ← evenPoint_tensor]
  exact congrArg evenPoint (eTensor_id (C := C.super) C.data.monoidal C.laws.monoidal X Y)

theorem legacyPentagon (W X Y Z : C.data.Obj) :
    (toOldData C).comp
      ((toOldData C).comp
        ((toOldData C).whiskerRight ((toOldData C).associatorHom W X Y) Z)
        ((toOldData C).associatorHom W ((toOldData C).tensorObj X Y) Z))
      ((toOldData C).whiskerLeft W ((toOldData C).associatorHom X Y Z)) =
    (toOldData C).comp
      ((toOldData C).associatorHom ((toOldData C).tensorObj W X) Y Z)
      ((toOldData C).associatorHom W X ((toOldData C).tensorObj Y Z)) := by
  have h := congrArg evenPoint (C.laws.monoidal.pentagon W X Y Z)
  simp only [evenPoint_comp, evenPoint_tensor] at h
  change tComp C.super.data
    (tComp C.super.data (legacyTensor C (evenPoint (C.data.monoidal.associatorHom W X Y))
      (evenPoint (C.data.id Z))) (evenPoint (C.data.monoidal.associatorHom W _ Z)))
    (legacyTensor C (evenPoint (C.data.id W)) (evenPoint (C.data.monoidal.associatorHom X Y Z))) = _
  rw [legacyTensor_even_left C _ _ (evenPoint_mem_grade C.super _),
    legacyTensor_even_left C _ _ (evenPoint_mem_grade C.super _)]
  exact h

theorem legacyTriangle (X Y : C.data.Obj) :
    (toOldData C).comp ((toOldData C).associatorHom X (toOldData C).tensorUnit Y)
      ((toOldData C).whiskerLeft X ((toOldData C).leftUnitorHom Y)) =
    (toOldData C).whiskerRight ((toOldData C).rightUnitorHom X) Y := by
  have h := congrArg evenPoint (C.laws.monoidal.triangle X Y)
  simp only [evenPoint_comp, evenPoint_tensor] at h
  change tComp C.super.data (evenPoint (C.data.monoidal.associatorHom X _ Y))
    (legacyTensor C (evenPoint (C.data.id X)) (evenPoint (C.data.monoidal.leftHom Y))) =
      legacyTensor C (evenPoint (C.data.monoidal.rightHom X)) (evenPoint (C.data.id Y))
  rw [legacyTensor_even_left C _ _ (evenPoint_mem_grade C.super _),
    legacyTensor_even_left C _ _ (evenPoint_mem_grade C.super _)]
  exact h

theorem legacyExactPairing (X Y : Even C.super) [ExactPairing X Y] :
    (toOldData C).HasExactPairing X Y := by
  let F := evenToTotal C.super
  refine ⟨evenPoint (η_ X Y), evenPoint (ε_ X Y),
    evenPoint_mem_grade C.super _, evenPoint_mem_grade C.super _, ?_, ?_⟩
  · have h := congrArg F.map (ExactPairing.coevaluation_evaluation (X := X) (Y := Y))
    simp only [Functor.map_comp] at h
    change tComp C.super.data
      (tComp C.super.data (legacyTensor C (evenPoint (C.data.id Y)) (evenPoint (η_ X Y)))
        (evenPoint (C.data.monoidal.associatorInv Y X Y)))
      (legacyTensor C (evenPoint (ε_ X Y)) (evenPoint (C.data.id Y))) = _
    erw [legacyTensor_even_maps C (𝟙 Y) (η_ X Y), legacyTensor_even_maps C (ε_ X Y) (𝟙 Y)]
    rw [tComp_assoc C.super]
    exact h
  · have h := congrArg F.map (ExactPairing.evaluation_coevaluation (X := X) (Y := Y))
    simp only [Functor.map_comp] at h
    change tComp C.super.data
      (tComp C.super.data (legacyTensor C (evenPoint (η_ X Y)) (evenPoint (C.data.id X)))
        (evenPoint (C.data.monoidal.associatorHom X Y X)))
      (legacyTensor C (evenPoint (C.data.id X)) (evenPoint (ε_ X Y))) = _
    erw [legacyTensor_even_maps C (η_ X Y) (𝟙 X), legacyTensor_even_maps C (𝟙 X) (ε_ X Y)]
    rw [tComp_assoc C.super]
    exact h

end RMod.Legacy.Hierarchy

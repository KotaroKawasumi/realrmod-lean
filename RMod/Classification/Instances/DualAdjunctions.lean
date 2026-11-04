import RMod.Classification.Instances.Duals
import RMod.Classification.Instances.TensorNaturality
import RMod.Classification.Instances.AdjunctionFromEven

/-!
# Dual adjunctions on all morphisms

Even coevaluation and evaluation give full natural unit and counit maps by
the tensor comparisons. Mathlib's even rigid-category adjunction supplies
the two triangle identities. Lifting it therefore gives adjunctions on
the complete real Hom spaces, including their odd parts.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.DualPairing

open CategoryTheory Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{u, v}} {X Y : C.data.Obj} (p : DualPairing C X Y)

def rightAdjunctionUnit : 𝟭 (LinearCategory C) ⟶ tensorRightFunctor C X ⋙ tensorRightFunctor C Y :=
  (tensorRightUnitIso C).inv ≫ tensorRightMap C p.data.coeval p.laws.coeval_even ≫
    (tensorRightAssocIso C X Y).inv

def rightAdjunctionCounit : tensorRightFunctor C Y ⋙ tensorRightFunctor C X ⟶
    𝟭 (LinearCategory C) :=
  (tensorRightAssocIso C Y X).hom ≫ tensorRightMap C p.data.eval p.laws.eval_even ≫
    (tensorRightUnitIso C).hom

def leftAdjunctionUnit : 𝟭 (LinearCategory C) ⟶ tensorLeftFunctor C Y ⋙ tensorLeftFunctor C X :=
  (tensorLeftUnitIso C).inv ≫ tensorLeftMap C p.data.coeval p.laws.coeval_even ≫
    (tensorLeftAssocIso C X Y).hom

def leftAdjunctionCounit : tensorLeftFunctor C X ⋙ tensorLeftFunctor C Y ⟶
    𝟭 (LinearCategory C) :=
  (tensorLeftAssocIso C Y X).inv ≫ tensorLeftMap C p.data.eval p.laws.eval_even ≫
    (tensorLeftUnitIso C).hom

noncomputable def evenRightAdjunction :
    (tensorRightSuperfunctor C X).toEvenFunctor ⊣ (tensorRightSuperfunctor C Y).toEvenFunctor := by
  letI := p.toEvenPairing
  exact CategoryTheory.tensorRightAdjunction (evenObj ℝ (LinearCategory C) X)
    (evenObj ℝ (LinearCategory C) Y)

noncomputable def evenLeftAdjunction :
    (tensorLeftSuperfunctor C Y).toEvenFunctor ⊣ (tensorLeftSuperfunctor C X).toEvenFunctor := by
  letI := p.toEvenPairing
  exact CategoryTheory.tensorLeftAdjunction (evenObj ℝ (LinearCategory C) X)
    (evenObj ℝ (LinearCategory C) Y)

/-- Tensoring on the right by X is left adjoint to tensoring on the right by Y. -/
def rightAdjunction : tensorRightFunctor C X ⊣ tensorRightFunctor C Y := by
  refine
    { unit := p.rightAdjunctionUnit
      counit := p.rightAdjunctionCounit
      left_triangle_components := ?_
      right_triangle_components := ?_ }
  all_goals
    let adj : tensorRightFunctor C X ⊣ tensorRightFunctor C Y :=
      (tensorRightSuperfunctor C X).adjunctionOfEven (tensorRightSuperfunctor C Y)
        p.evenRightAdjunction p.rightAdjunctionUnit p.rightAdjunctionCounit
        (fun Z => by
          change C.data.comp (C.data.rightUnitorInv Z)
            (C.data.comp (C.data.tensorHom (C.data.id Z) p.data.coeval) (C.data.associatorInv Z X Y)) =
            C.data.comp (C.data.rightUnitorInv Z)
              (C.data.comp (C.data.tensorHom (C.data.id Z) p.data.coeval)
                (C.data.comp (C.data.associatorInv Z X Y)
                  (C.data.tensorHom (C.data.id (C.data.tensorObj Z X)) (C.data.id Y))))
          rw [C.laws.tensor_id, C.laws.comp_id])
        (fun Z => by
          change C.data.comp (C.data.associatorHom Z Y X)
            (C.data.comp (C.data.tensorHom (C.data.id Z) p.data.eval) (C.data.rightUnitorHom Z)) =
            C.data.comp (C.data.tensorHom (C.data.id (C.data.tensorObj Z Y)) (C.data.id X))
              (C.data.comp (C.data.associatorHom Z Y X)
                (C.data.comp (C.data.tensorHom (C.data.id Z) p.data.eval) (C.data.rightUnitorHom Z)))
          rw [C.laws.tensor_id, C.laws.id_comp])
    first | exact adj.left_triangle_components | exact adj.right_triangle_components

/-- Tensoring on the left by Y is left adjoint to tensoring on the left by X. -/
def leftAdjunction : tensorLeftFunctor C Y ⊣ tensorLeftFunctor C X := by
  refine
    { unit := p.leftAdjunctionUnit
      counit := p.leftAdjunctionCounit
      left_triangle_components := ?_
      right_triangle_components := ?_ }
  all_goals
    let adj : tensorLeftFunctor C Y ⊣ tensorLeftFunctor C X :=
      (tensorLeftSuperfunctor C Y).adjunctionOfEven (tensorLeftSuperfunctor C X)
        p.evenLeftAdjunction p.leftAdjunctionUnit p.leftAdjunctionCounit
        (fun Z => by
          change C.data.comp (C.data.leftUnitorInv Z)
            (C.data.comp (C.data.tensorHom p.data.coeval (C.data.id Z)) (C.data.associatorHom X Y Z)) =
            C.data.comp (C.data.leftUnitorInv Z)
              (C.data.comp (C.data.tensorHom p.data.coeval (C.data.id Z))
                (C.data.comp (C.data.associatorHom X Y Z)
                  (C.data.tensorHom (C.data.id X) (C.data.id (C.data.tensorObj Y Z)))))
          rw [C.laws.tensor_id, C.laws.comp_id])
        (fun Z => by
          change C.data.comp (C.data.associatorInv Y X Z)
            (C.data.comp (C.data.tensorHom p.data.eval (C.data.id Z)) (C.data.leftUnitorHom Z)) =
            C.data.comp (C.data.tensorHom (C.data.id Y) (C.data.id (C.data.tensorObj X Z)))
              (C.data.comp (C.data.associatorInv Y X Z)
                (C.data.comp (C.data.tensorHom p.data.eval (C.data.id Z)) (C.data.leftUnitorHom Z)))
          rw [C.laws.tensor_id, C.laws.id_comp])
    first | exact adj.left_triangle_components | exact adj.right_triangle_components

end RMod.Classification.DualPairing

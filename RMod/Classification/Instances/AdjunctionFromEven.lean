import RMod.Classification.Instances.Functors
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Lifting an even adjunction with full naturality

Suppose the even restrictions of two superfunctors are adjoint, and their
unit and counit extend to natural transformations on all morphisms. The
triangle identities are equations of even maps, so forgetting their degree
witnesses proves the full adjunction. Naturality on odd maps is an explicit
input to this construction, not inferred from the even restriction.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.Superfunctor

open CategoryTheory Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}

def adjunctionOfEven (F : Superfunctor C D) (G : Superfunctor D C)
    (e : F.toEvenFunctor ⊣ G.toEvenFunctor)
    (η : 𝟭 (LinearCategory C) ⟶ F.toFunctor ⋙ G.toFunctor)
    (ε : G.toFunctor ⋙ F.toFunctor ⟶ 𝟭 (LinearCategory D))
    (hη : ∀ X : LinearCategory C, η.app X = (e.unit.app (evenObj ℝ (LinearCategory C) X)).hom)
    (hε : ∀ Y : LinearCategory D, ε.app Y = (e.counit.app (evenObj ℝ (LinearCategory D) Y)).hom) :
    F.toFunctor ⊣ G.toFunctor where
  unit := η
  counit := ε
  left_triangle_components X := by
    rw [hη, hε]
    exact congrArg (fun f => f.hom) (e.left_triangle_components (evenObj ℝ (LinearCategory C) X))
  right_triangle_components Y := by
    rw [hη, hε]
    exact congrArg (fun f => f.hom) (e.right_triangle_components (evenObj ℝ (LinearCategory D) Y))

end RMod.Classification.Superfunctor

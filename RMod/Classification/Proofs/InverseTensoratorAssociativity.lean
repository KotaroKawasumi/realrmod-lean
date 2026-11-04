import RMod.Classification.Instances.MonoidalFunctors

/-!
# Associativity for the actual inverse tensorators

Restrict the completed monoidal superfunctor to its even subcategory and
reuse Mathlib's oplax monoidal associativity. Forgetting only the evenness
certificates gives the equation for the original specified raw maps.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.MonoidalSuperfunctor

open CategoryTheory Superfusion.Category

theorem inverseTensorator_associativity
    {A : WeaklyPointedSuperfusion.{u₁, v₁}} {B : WeaklyPointedSuperfusion.{u₂, v₂}}
    (F : MonoidalSuperfunctor A B) (X Y Z : A.data.Obj) :
    B.data.comp (F.data.tensorInv (A.data.tensorObj X Y) Z)
      (B.data.comp (B.data.tensorHom (F.data.tensorInv X Y) (B.data.id (F.data.obj Z)))
        (B.data.associatorHom (F.data.obj X) (F.data.obj Y) (F.data.obj Z))) =
      B.data.comp (F.data.map (A.data.associatorHom X Y Z))
        (B.data.comp (F.data.tensorInv X (A.data.tensorObj Y Z))
          (B.data.tensorHom (B.data.id (F.data.obj X)) (F.data.tensorInv Y Z))) := by
  have h := congrArg (fun f => f.hom)
    (Functor.OplaxMonoidal.associativity F.toSuperfunctor.toEvenFunctor
      (evenObj ℝ (LinearCategory A) X) (evenObj ℝ (LinearCategory A) Y)
      (evenObj ℝ (LinearCategory A) Z))
  exact h

end RMod.Classification.MonoidalSuperfunctor

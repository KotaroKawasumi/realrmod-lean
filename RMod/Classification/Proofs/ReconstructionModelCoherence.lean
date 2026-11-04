import RMod.Classification.Instances.ReconstructionEvenMonoidal
import RMod.Classification.Instances.ReconstructionModelData

/-!
# Pentagon and triangle for the actual reconstruction maps

Forget the even-subcategory wrappers in the transported coherence laws.
The resulting equations concern the original specified raw model data,
so they can be restricted to simple components to recover omega's laws.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionModel_pentagon
    (W X Y Z : (reconstructionModelData A C hC).Obj) :
    let D := reconstructionModelData A C hC
    D.comp (D.comp (D.whiskerRight (D.associatorHom W X Y) Z)
      (D.associatorHom W (D.tensorObj X Y) Z))
      (D.whiskerLeft W (D.associatorHom X Y Z)) =
    D.comp (D.associatorHom (D.tensorObj W X) Y Z) (D.associatorHom W X (D.tensorObj Y Z)) := by
  letI := reconstructionEvenMonoidalStruct A C hC
  letI := reconstructionEvenMonoidalCategory A C hC
  have he := congrArg (fun f => f.hom)
    (MonoidalCategory.pentagon
      (evenObj ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC)) W)
      (evenObj ℝ _ X) (evenObj ℝ _ Y) (evenObj ℝ _ Z))
  funext q
  exact (C.laws.comp_assoc _ _ _).trans (congrFun he q)

theorem reconstructionModel_triangle (X Y : (reconstructionModelData A C hC).Obj) :
    let D := reconstructionModelData A C hC
    D.comp (D.associatorHom X D.tensorUnit Y) (D.whiskerLeft X (D.leftUnitorHom Y)) =
      D.whiskerRight (D.rightUnitorHom X) Y := by
  letI := reconstructionEvenMonoidalStruct A C hC
  letI := reconstructionEvenMonoidalCategory A C hC
  exact congrArg (fun f => f.hom)
    (MonoidalCategory.triangle
      (evenObj ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC)) X)
      (evenObj ℝ _ Y))

theorem reconstructionModelData_eq (ht : TwistLaws (reconstructionTwistData A C hC)) :
    reconstructionModelData A C hC =
      twistedPullbackData C.data hC (reconstructionTwistData A C hC) ht := rfl

end RMod.Classification

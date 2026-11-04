import RMod.Classification.Instances.LinearMonoidal
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Ordinary coherence restricted to even structural maps

Mathlib supplies coherence in the existing even monoidal category.
Forgetting its Hom subtype yields the corresponding raw identities;
this does not impose sign-free interchange on odd morphisms.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem unitors_hom_equal : C.leftUnitorHom C.tensorUnit = C.rightUnitorHom C.tensorUnit := by
  have h := MonoidalCategory.unitors_equal
    (C := EvenSubcategory ℝ (LinearCategory ⟨C, hC⟩))
  exact congrArg (fun f => f.hom) h

theorem leftUnitor_tensor (X Y : C.Obj) :
    C.comp (C.associatorHom C.tensorUnit X Y) (C.leftUnitorHom (C.tensorObj X Y)) =
      C.tensorHom (C.leftUnitorHom X) (C.id Y) := by
  have h := MonoidalCategory.leftUnitor_tensor_hom''
    (evenObj ℝ (LinearCategory ⟨C, hC⟩) X) (evenObj ℝ (LinearCategory ⟨C, hC⟩) Y)
  exact congrArg (fun f => f.hom) h

theorem rightUnitor_tensor (X Y : C.Obj) :
    C.rightUnitorHom (C.tensorObj X Y) =
      C.comp (C.associatorHom X Y C.tensorUnit) (C.tensorHom (C.id X) (C.rightUnitorHom Y)) := by
  have h := MonoidalCategory.rightUnitor_tensor_hom
    (evenObj ℝ (LinearCategory ⟨C, hC⟩) X) (evenObj ℝ (LinearCategory ⟨C, hC⟩) Y)
  exact congrArg (fun f => f.hom) h

end RMod.Classification

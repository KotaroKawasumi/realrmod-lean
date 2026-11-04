import RMod.BrundanEllis.StackingKaroubiOrdinary
import RMod.BrundanEllis.StackingKaroubiMonoidal
import Mathlib.CategoryTheory.Monoidal.Transport

/-! Transport the ordinary Karoubi tensor to the even category of its enriched
completion. Tensor objects retain their concrete tensor idempotents. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)]

instance evenMonoidal : MonoidalCategory (Even (Karoubi (Even C))) :=
  Monoidal.transport (evenEquivalence (C := C)).symm

@[simp] theorem evenTensor_object (P Q : Even (Karoubi (Even C))) :
    ForgetEnrichment.to SuperVec (P ⊗ Q) =
      KaroubiTensor.objectTensor (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec Q) := rfl

@[simp] theorem evenUnit_object :
    ForgetEnrichment.to SuperVec (𝟙_ (Even (Karoubi (Even C)))) =
      ((𝟙_ (Even C) : Even C) : Karoubi (Even C)) := rfl

/-- The comparison to ordinary Karoubi objects is monoidal for the transported tensor. -/
instance evenComparisonMonoidal : (evenEquivalence (C := C)).functor.Monoidal := by
  change (Monoidal.equivalenceTransported (evenEquivalence (C := C)).symm).inverse.Monoidal
  infer_instance

end RMod.BrundanEllis.Stacking.KaroubiSuper

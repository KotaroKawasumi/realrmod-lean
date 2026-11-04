import RMod.BrundanEllis.StackingKaroubiEvenMonoidal
import RMod.BrundanEllis.StackingKaroubiLeftDual
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! The canonical monoidal comparison transports the concrete corner
duals to the even category of the enriched completion. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [RigidCategory (Even C)]

instance evenRigid : RigidCategory (Even (Karoubi (Even C))) :=
  rigidCategoryOfEquivalence (evenEquivalence (C := C)).toAdjunction

end RMod.BrundanEllis.Stacking.KaroubiSuper

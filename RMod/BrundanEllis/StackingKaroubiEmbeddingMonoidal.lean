import RMod.BrundanEllis.StackingKaroubiEmbedding
import RMod.BrundanEllis.StackingKaroubiEvenMaps
import RMod.BrundanEllis.StackingKaroubiInclusion

/-! The enriched embedding has the ordinary strong monoidal inclusion as
its even part, under the canonical comparison with ordinary Karoubi. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)]

theorem embedding_forget : (embedding C).forget =
    toKaroubi (Even C) ⋙ (evenEquivalence (C := C)).inverse := rfl

instance inverseComparisonMonoidal : (evenEquivalence (C := C)).inverse.Monoidal := by
  change (Monoidal.equivalenceTransported (evenEquivalence (C := C)).symm).functor.Monoidal
  infer_instance

def embeddingMonoidal : (embedding C).forget.CoreMonoidal := by
  letI := (KaroubiTensor.inclusionMonoidal (Even C)).toMonoidal
  rw [embedding_forget]
  exact Functor.CoreMonoidal.ofLaxMonoidal _

end RMod.BrundanEllis.Stacking.KaroubiSuper

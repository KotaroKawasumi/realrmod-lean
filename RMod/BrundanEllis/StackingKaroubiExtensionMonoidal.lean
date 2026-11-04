import RMod.BrundanEllis.StackingKaroubiFunctorMonoidal
import RMod.BrundanEllis.StackingKaroubiExtension
import RMod.BrundanEllis.StackingEnrichedCounit
import RMod.BrundanEllis.StackingEnrichedInverseMonoidal
import RMod.BrundanEllis.StackingCompositeMonoidal

/-! Splitting corners in an idempotent-complete target is monoidal for the
existing tensor on that target. Composing this splitting with the corner
functor extends a monoidal functor to the source completion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
attribute [local irreducible] embedding retraction enrichedInverse
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [IsIdempotentComplete (Even D)]

/-- The fixed enriched splitting is monoidal, via its concrete counit. -/
def retractionMonoidal : (retraction D).forget.CoreMonoidal := by
  unfold retraction
  exact enrichedInverseCoreMonoidal (embedding D) (embedding_bijective D)
    (retractObject D) (retractComparison D) (embeddingMonoidal D)

/-- Ordinary monoidal coherence of the actual enriched extension. -/
def extensionMonoidal (F : SuperFunctor C D) (M : F.forget.CoreMonoidal) :
    (extension F).forget.CoreMonoidal := by
  unfold extension
  exact compositeCoreMonoidal (functor F) (retraction D)
    (functorMonoidal F M) (retractionMonoidal (D := D))

end RMod.BrundanEllis.Stacking.KaroubiSuper

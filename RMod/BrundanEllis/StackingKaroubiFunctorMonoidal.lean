import RMod.BrundanEllis.StackingKaroubiMapMonoidal
import RMod.BrundanEllis.StackingKaroubiFunctor
import RMod.BrundanEllis.StackingKaroubiEmbeddingMonoidal

/-! The enriched corner functor has the same even arrows as the ordinary
Karoubi functor. This comparison transfers the already proved monoidal
structure without changing any of its enriched Hom maps. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]

/-- The ordinary map of corners expressed in the enriched even categories. -/
def mappedEvenFunctor (F : SuperFunctor C D) :
    Even (Karoubi (Even C)) ⥤ Even (Karoubi (Even D)) :=
  (evenEquivalence (C := C)).functor ⋙ KaroubiTensor.mapFunctor F.forget ⋙
    (evenEquivalence (C := D)).inverse

theorem functor_forget_eq (F : SuperFunctor C D) :
    (functor F).forget = mappedEvenFunctor F := by
  rfl

variable [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]

/-- Ordinary coherence for the same enriched corner functor. -/
def functorMonoidal (F : SuperFunctor C D) (M : F.forget.CoreMonoidal) :
    (functor F).forget.CoreMonoidal := by
  letI := M.toMonoidal
  letI := (KaroubiTensor.mapMonoidal F.forget).toMonoidal
  change (mappedEvenFunctor F).CoreMonoidal
  unfold mappedEvenFunctor
  exact Functor.CoreMonoidal.ofLaxMonoidal _

end RMod.BrundanEllis.Stacking.KaroubiSuper

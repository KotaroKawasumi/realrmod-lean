import RMod.BrundanEllis.StackingEnrichedInverse
import RMod.BrundanEllis.StackingKaroubiEmbedding

/-! For an idempotent-complete even category the standard embedding into
even corners has an actual enriched inverse. The chosen ordinary splitting
is lifted by conjugation on full graded Hom objects. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable (C : Type) [SuperCategory C] [IsIdempotentComplete (Even C)]

instance embeddingEquivalence : (embedding C).forget.IsEquivalence := by
  change (toKaroubi (Even C) ⋙ (evenEquivalence (C := C)).inverse).IsEquivalence
  infer_instance

/-- The ordinary splitting object supplies the enriched quasi-inverse object. -/
def retractObject (P : Karoubi (Even C)) : C :=
  ForgetEnrichment.to SuperVec ((embedding C).forget.objPreimage (evenObj _ P))

def retractComparison (P : Karoubi (Even C)) :
    (embedding C).forget.obj (evenObj C (retractObject C P)) ≅ evenObj _ P :=
  (embedding C).forget.objObjPreimageIso (evenObj _ P)

def retraction : SuperFunctor (Karoubi (Even C)) C :=
  enrichedInverse (embedding C) (embedding_bijective C) (retractObject C) (retractComparison C)

theorem retraction_bijective (P Q : Karoubi (Even C)) (a : ZMod 2) :
    Function.Bijective ((retraction C).map P Q a) :=
  enrichedInverse_bijective (embedding C) (embedding_bijective C)
    (retractObject C) (retractComparison C) P Q a

/-- Splitting a trivial corner returns the original object up to an even isomorphism. -/
def retractionEmbeddingIso (X : Even C) :
    (retraction C).forget.obj ((embedding C).forget.obj X) ≅ X :=
  (embedding C).forget.preimageIso
    (retractComparison C ((embedding C).obj (ForgetEnrichment.to SuperVec X)))

end RMod.BrundanEllis.Stacking.KaroubiSuper

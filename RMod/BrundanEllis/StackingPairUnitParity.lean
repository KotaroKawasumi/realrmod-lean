import RMod.BrundanEllis.StackingPairSpan
import RMod.BrundanEllis.StackingFunctorParity
import RMod.BrundanEllis.StackingWeakRetracts
import RMod.BrundanEllis.StackingPiStructures
import RMod.BrundanEllis.StackingKaroubiSuperMonoidal

/-! Pairing the unit and parity objects gives only the unit and parity
again. The two odd factors cancel through the canonical even isomorphism
from the parity square to the unit; no exterior-model monoidal comparison
is used in this calculation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking

def mapParityObject {C D : Type} [SuperCategory C] [SuperCategory D]
    [MonoidalCategory (Even C)] [MonoidalSuperCategory C] [MonoidalPiSuperCategory C]
    [MonoidalCategory (Even D)] [MonoidalSuperCategory D] [MonoidalPiSuperCategory D]
    (F : SuperFunctor C D) :
    F.forget.obj (evenObj C (MonoidalPiSuperCategory.pi (C := C))) ≅
      (piFunctor D).forget.obj (F.forget.obj (𝟙_ (Even C))) :=
  F.forget.mapIso (ρ_ (evenObj C (MonoidalPiSuperCategory.pi (C := C)))).symm ≪≫
    GradedIso.parityComparison F (𝟙_ (Even C))

variable (A B : WeaklyPointedFusionPiSuperCat)
variable [HasFiniteBiproducts (Even (Karoubi (Even (SuperTensorProduct A B))))]

/-- Four unit/parity pairs lie in the two-generator target span. -/
theorem pair_unit_parity_span (a b : Bool) :
    FiniteSpan (unitParityFamily (Karoubi (Even (SuperTensorProduct A B))))
      ((evenPairFunctor (KaroubiSuper.embedding (SuperTensorProduct A B))).obj
        (unitParityFamily A a, unitParityFamily B b)) := by
  let F := KaroubiSuper.embedding (SuperTensorProduct A B)
  cases a <;> cases b
  · exact FiniteSpan.generator false
  · let L := (insertLeft SuperVec (ForgetEnrichment.to SuperVec (𝟙_ (Even A)))).comp SuperVec F
    apply FiniteSpan.of_iso (mapParityObject L ≪≫
      ρ_ (evenObj (Karoubi (Even (SuperTensorProduct A B))) (MonoidalPiSuperCategory.pi (C := (Karoubi (Even (SuperTensorProduct A B)))))))
    exact FiniteSpan.generator true
  · exact FiniteSpan.generator true
  · let L := (insertLeft SuperVec (MonoidalPiSuperCategory.pi (C := A))).comp SuperVec F
    apply FiniteSpan.of_iso (mapParityObject L ≪≫ GradedIso.paritySquare (Karoubi (Even (SuperTensorProduct A B))))
    exact FiniteSpan.generator false

end RMod.BrundanEllis.Stacking

import RMod.BrundanEllis.StackingPairUnitParity
import RMod.BrundanEllis.StackingKaroubiEmbeddingDual
import RMod.BrundanEllis.StackingProductRigid
import RMod.BrundanEllis.StackingPairSimpleRetract

/-! A pair of weakly invertible objects remains weakly invertible after
completion. Its self-dual tensor is the paired self-dual tensors of the
factors, whose unit/parity spans combine into the same target span. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
namespace RMod.BrundanEllis.Stacking

/-- The usual two multiplicities are equivalently membership in a finite span. -/
theorem weak_inverse_span (C : WeaklyPointedFusionPiSuperCat) (X : Even C)
    (hX : IsWeaklyInvertible C X) : FiniteSpan (unitParityFamily C) (X ⊗ Xᘁ) := by
  obtain ⟨p, q, ⟨e⟩⟩ := hX
  exact FiniteSpan.of_iso e (FiniteSpan.binary_biproduct
    (FiniteSpan.of_finite_family (Z := unitParityFamily C) (fun _ : Fin p => false))
    (FiniteSpan.of_finite_family (Z := unitParityFamily C) (fun _ : Fin q => true)))

variable (A B : WeaklyPointedFusionPiSuperCat)
variable [Abelian (Even (Karoubi (Even (SuperTensorProduct A B))))] [FusionPiSuperCategory (Karoubi (Even (SuperTensorProduct A B)))]

theorem paired_weaklyInvertible (X : Even A) (Y : Even B)
    (hX : IsWeaklyInvertible A X) (hY : IsWeaklyInvertible B Y) :
    IsWeaklyInvertible (Karoubi (Even (SuperTensorProduct A B)))
      ((evenPairFunctor (KaroubiSuper.embedding (SuperTensorProduct A B))).obj (X, Y)) := by
  let F := KaroubiSuper.embedding (SuperTensorProduct A B)
  have h := pair_span F (unitParityFamily A) (unitParityFamily B) (unitParityFamily (Karoubi (Even (SuperTensorProduct A B))))
    (pair_unit_parity_span A B) (weak_inverse_span A X hX) (weak_inverse_span B Y hY)
  have e := KaroubiSuper.embeddingSelfDualIso (SuperTensorProduct A B) ((productPair A B).obj (X, Y))
  have h' := FiniteSpan.of_iso e h
  exact binary_multiplicities (𝟙_ (Even (Karoubi (Even (SuperTensorProduct A B)))))
    (evenObj (Karoubi (Even (SuperTensorProduct A B))) (MonoidalPiSuperCategory.pi (C := (Karoubi (Even (SuperTensorProduct A B)))))) h'

/-- Weak pointedness follows from the paired-simple retract description. -/
theorem completed_weaklyPointed : IsWeaklyPointed (Karoubi (Even (SuperTensorProduct A B))) := by
  intro X hX
  letI := hX
  obtain ⟨S, T, hS, hT, ⟨r⟩⟩ := completed_simple_retract_pair A B
    (FusionPiSuperCategory.semisimple (C := (Karoubi (Even (SuperTensorProduct A B))))) X
  exact weaklyInvertible_of_retract (Karoubi (Even (SuperTensorProduct A B))) r (paired_weaklyInvertible A B S T
    (WeaklyPointedFusionPiSuperCategory.weaklyPointed (C := A) S hS)
    (WeaklyPointedFusionPiSuperCategory.weaklyPointed (C := B) T hT))

end RMod.BrundanEllis.Stacking

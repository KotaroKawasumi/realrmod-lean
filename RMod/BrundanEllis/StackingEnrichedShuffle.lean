import RMod.BrundanEllis.StackingEnrichedSwap
import RMod.BrundanEllis.StackingEnrichedReassociation

/-! Reorder four enriched factors by the middle interchange. On Hom objects
this is precisely Mathlib's tensorMu, including the ambient symmetry. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
universe u₁ u₂ u₃ u₄ v w
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [SymmetricCategory V]
  (A : Type u₁) (B : Type u₂) (C : Type u₃) (D : Type u₄)
  [EnrichedCategory V A] [EnrichedCategory V B] [EnrichedCategory V C] [EnrichedCategory V D]

def enrichedShuffle : EnrichedFunctor V
    (EnrichedTensorProduct V (EnrichedTensorProduct V A B) (EnrichedTensorProduct V C D))
    (EnrichedTensorProduct V (EnrichedTensorProduct V A C) (EnrichedTensorProduct V B D)) :=
  ((((RMod.reassociate V A B (EnrichedTensorProduct V C D)).comp V
    (RMod.tensorEnrichedFunctors V (EnrichedFunctor.id V A) (enrichedReassociateInv V B C D))).comp V
      (RMod.tensorEnrichedFunctors V (EnrichedFunctor.id V A)
        (RMod.tensorEnrichedFunctors V (enrichedSwap V B C) (EnrichedFunctor.id V D)))).comp V
          (RMod.tensorEnrichedFunctors V (EnrichedFunctor.id V A) (RMod.reassociate V C B D))).comp V
            (enrichedReassociateInv V A C (EnrichedTensorProduct V B D))

theorem enrichedShuffle_map
    (X Y : EnrichedTensorProduct V (EnrichedTensorProduct V A B) (EnrichedTensorProduct V C D)) :
    (enrichedShuffle V A B C D).map X Y =
      tensorμ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
        (X.2.1 ⟶[V] Y.2.1) (X.2.2 ⟶[V] Y.2.2) := by
  simp only [enrichedShuffle, EnrichedFunctor.comp, RMod.reassociate,
    enrichedReassociateInv, RMod.tensorEnrichedFunctors, enrichedSwap, EnrichedFunctor.id,
    EnrichedTensorProduct.of, id_tensorHom, tensorHom_id, Category.assoc, tensorμ]
  rfl

end RMod.BrundanEllis.Stacking

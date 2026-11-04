import RMod.BrundanEllis.StackingPairSpan
import RMod.BrundanEllis.StackingSimpleSpan
import RMod.BrundanEllis.StackingKaroubiEmbedding

/-! Every completed simple object is a retract of a pair of simple objects.
The proof first retracts to the underlying pair, decomposes both factors,
and then uses semisimplicity to select one paired summand. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking

/-- The inclusion of the underlying object contains each corner as a retract. -/
def completedRetract {C : Type} [SuperCategory C] (X : Even (Karoubi (Even C))) :
    Retract X ((KaroubiSuper.embedding C).forget.obj
      (ForgetEnrichment.to SuperVec X).X) :=
  (Karoubi.retract (ForgetEnrichment.to SuperVec X)).map
    (KaroubiSuper.evenEquivalence (C := C)).inverse

/-- Actual simple objects, including both parity choices, suffice as factor generators. -/
theorem simple_span (C : WeaklyPointedFusionPiSuperCat) (X : Even C) :
    FiniteSpan (fun S : {S : Even C // Simple S} => S.val) X := by
  obtain ⟨n, S, hS, e⟩ := FusionPiSuperCategory.semisimple (C := C) X
  exact ⟨n, fun i => ⟨S i, hS i⟩, e⟩

variable (A B : WeaklyPointedFusionPiSuperCat)
variable [Abelian (Even (Karoubi (Even (SuperTensorProduct A B))))] [HasFiniteBiproducts (Even (Karoubi (Even (SuperTensorProduct A B))))]

theorem completed_simple_retract_pair
    (hsemi : ∀ X : Even (Karoubi (Even (SuperTensorProduct A B))), ∃ (n : ℕ) (S : Fin n → Even (Karoubi (Even (SuperTensorProduct A B)))),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S))
    (X : Even (Karoubi (Even (SuperTensorProduct A B)))) [Simple X] :
    ∃ (S : Even A) (T : Even B), Simple S ∧ Simple T ∧
      Nonempty (Retract X ((evenPairFunctor (KaroubiSuper.embedding
        (SuperTensorProduct A B))).obj (S, T))) := by
  let F := KaroubiSuper.embedding (SuperTensorProduct A B)
  let Z (i : {S : Even A // Simple S} × {T : Even B // Simple T}) :=
    (evenPairFunctor F).obj (i.1.val, i.2.val)
  let Y := (ForgetEnrichment.to SuperVec X).X
  have h : FiniteSpan Z (F.forget.obj Y) :=
    pair_span F (fun S : {S : Even A // Simple S} => S.val)
      (fun T : {T : Even B // Simple T} => T.val) Z
      (fun S T => FiniteSpan.generator (S, T))
      (simple_span A (evenObj A (ForgetEnrichment.to SuperVec Y).1))
      (simple_span B (evenObj B (ForgetEnrichment.to SuperVec Y).2))
  obtain ⟨⟨S, T⟩, r⟩ := FiniteSpan.simple_retract_generator hsemi (completedRetract X) h
  exact ⟨S.val, T.val, S.property, T.property, r⟩

end RMod.BrundanEllis.Stacking

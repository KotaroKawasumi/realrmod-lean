import RMod.Classification.Proofs.HomogeneousSums
import RMod.Classification.Proofs.UnitComponent
import Mathlib.Logic.Equiv.Sum

/-!
# Separating the even and odd copies of a homogeneous sum

Mathlib's equivalence for a predicate and its complement partitions the
existing finite index by parity. Reindexing retains every matrix map and
turns its total equation into the frozen super-multiplicity predicate.
The neutral intrinsic component consequently consists of super-multiples
of the tensor unit, with positive total multiplicity for nonzero objects.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem homogeneousSum_superMultiplicity (C : WeaklyPointedSuperfusion.{0, 0})
    {X A : C.data.Obj} {n : ℕ} (d : HomogeneousSum C.data X A n) :
    ∃ p q, p + q = n ∧ C.data.HasSuperMultiplicity A X p q := by
  classical
  letI : AddCommGroup (C.data.Hom A A) := (LinearCategory.preadditive C).homGroup A A
  let E := { j : Fin n // d.data.parity j = 0 }
  let O := { j : Fin n // ¬ d.data.parity j = 0 }
  let e₀ : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let e₁ : Fin (Fintype.card O) ≃ O := (Fintype.equivFin O).symm
  let e : Fin (Fintype.card E) ⊕ Fin (Fintype.card O) ≃ Fin n :=
    (e₀.sumCongr e₁).trans (Equiv.sumCompl (fun j => d.data.parity j = 0))
  have he (j : Fin (Fintype.card E) ⊕ Fin (Fintype.card O)) :
      d.data.parity (e j) = WeaklyPointedSuperfusionData.superIndexParity j := by
    cases j with
    | inl j => exact (e₀ j).property
    | inr j => exact (parity_cases (d.data.parity (e₁ j).val)).resolve_left (e₁ j).property
  refine ⟨Fintype.card E, Fintype.card O, ?_,
    fun j => d.data.inclusion (e j), fun j => d.data.projection (e j), ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  · intro j
    rw [← he j]
    exact d.laws.inclusion_grade (e j)
  · intro j
    rw [← he j]
    exact d.laws.projection_grade (e j)
  · exact fun j => d.laws.diagonal (e j)
  · exact fun j k hjk => d.laws.off_diagonal (e j) (e k) (e.injective.ne hjk)
  · dsimp only [WeaklyPointedSuperfusionData.superFinSum]
    simp only [LinearCategory.finSum_eq_sum C]
    change (∑ j, C.data.comp (d.data.projection (e (Sum.inl j))) (d.data.inclusion (e (Sum.inl j)))) +
      (∑ j, C.data.comp (d.data.projection (e (Sum.inr j))) (d.data.inclusion (e (Sum.inr j)))) = C.data.id A
    rw [← Fintype.sum_sum_type (fun j => C.data.comp (d.data.projection (e j)) (d.data.inclusion (e j))),
      e.sum_comp (fun j => C.data.comp (d.data.projection j) (d.data.inclusion j))]
    rw [← LinearCategory.finSum_eq_sum C]
    exact d.laws.total

theorem InComponent.neutral_superMultiplicity {C : PiSuperfusionData.{0, 0}}
    (hC : ReferenceProperty C) {A : C.Obj}
    (hA : InComponent C.toWeaklyPointedSuperfusionData 0 A) :
    ∃ p q, C.HasSuperMultiplicity A C.tensorUnit p q := by
  let C₀ : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  obtain ⟨n, S, hs, hd⟩ := hA
  have ho (j : Fin n) : SameParityOrbit C.toWeaklyPointedSuperfusionData C.tensorUnit (S j) :=
    (hC.type_detects_orbit C.tensorUnit (S j) 0 hC.simple_unit (hs j).1 (hasBWType_unit C₀)).mp (hs j).2
  obtain ⟨d, hd⟩ := exists_homogeneousSum C₀.laws ho hd
  obtain ⟨p, q, _, hm⟩ := homogeneousSum_superMultiplicity C₀ ⟨d, hd⟩
  exact ⟨p, q, hm⟩

end RMod.Classification

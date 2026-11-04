import RMod.Classification.Proofs.PullbackSimples
import RMod.Classification.Proofs.PlacedMaps
import RMod.Classification.Instances.PullbackLinearCategory

/-!
# Semisimplicity of the abstract pullback

The component certificate of each coordinate already gives a finite
decomposition into simples of the required intrinsic type. Place those
simples in their group degrees and enumerate the finite dependent sum of
their indices using Mathlib. The matrix equations follow coordinatewise;
the total sum has contributions only from the coordinate being evaluated.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_semisimple (A : PullbackObj C t) :
    ∃ n S, (∀ j : Fin n, (twistedPullbackData C hC t ht).IsSimple (S j)) ∧
      (twistedPullbackData C hC t ht).HasDecomposition A S := by
  classical
  choose n S hs i p hi hp hd ho hh using fun g => (A g).property
  let hc (g : t.group) (j : Fin (n g)) :=
    InComponent.of_simple hC (hs g j).1 (hs g j).2
  letI := Fintype.ofFinite t.group
  let J := (g : t.group) × Fin (n g)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let T (a : J) : PullbackObj C t := placedObj C hC t a.1 (S a.1 a.2) (hc a.1 a.2)
  let incl (a : J) : PullbackHom C t (T a) A := placedTo C hC t a.1 (hc a.1 a.2) (i a.1 a.2)
  let proj (a : J) : PullbackHom C t A (T a) := placedFrom C hC t a.1 (hc a.1 a.2) (p a.1 a.2)
  refine ⟨Fintype.card J, fun j => T (e j), ?_, fun j => incl (e j), fun j => proj (e j),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact twistedPullback_placed_simple C hC t ht (e j).1 _ _ (hs (e j).1 (e j).2).1
  · intro j
    exact placedTo_grade C hC t _ _ _ (hi (e j).1 (e j).2)
  · intro j
    exact placedFrom_grade C hC t _ _ _ (hp (e j).1 (e j).2)
  · intro j
    exact funext (placedTo_From_diagonal C hC t _ _ _ _ (hd (e j).1 (e j).2))
  · intro j l hjl
    have hne : e j ≠ e l := e.injective.ne hjl
    change (fun k => C.comp (incl (e j) k) (proj (e l) k)) = (fun _ => C.zero)
    generalize e j = a, e l = b at hne ⊢
    obtain ⟨g, a⟩ := a
    obtain ⟨h, b⟩ := b
    by_cases hgh : g = h
    · subst h
      have hab : a ≠ b := fun he => hne (by cases he; rfl)
      exact funext (placedTo_From_zero C hC t g _ _ _ _ (ho g a b hab))
    · exact funext (placedTo_From_disjoint C hC t g _ h hgh _ _ _)
  · funext k
    rw [PullbackCategory.finSum_apply C hC t ht]
    letI : AddCommGroup (C.Hom (A k).val (A k).val) :=
      (LinearCategory.preadditive ⟨C.toWeaklyPointedSuperfusionData,
        hC.toWeaklyPointedSuperfusionLaws⟩).homGroup _ _
    rw [LinearCategory.finSum_eq_sum ⟨C.toWeaklyPointedSuperfusionData,
      hC.toWeaklyPointedSuperfusionLaws⟩]
    change (∑ j, C.comp (proj (e j) k) (incl (e j) k)) = C.id (A k).val
    rw [e.sum_comp (fun a => C.comp (proj a k) (incl a k)), Fintype.sum_sigma]
    rw [Finset.sum_eq_single k]
    · change (∑ a : Fin (n k), C.comp (placedFrom C hC t k (hc k a) (p k a) k)
        (placedTo C hC t k (hc k a) (i k a) k)) = C.id (A k).val
      simp only [placedFrom_To_at]
      rw [← LinearCategory.finSum_eq_sum ⟨C.toWeaklyPointedSuperfusionData,
        hC.toWeaklyPointedSuperfusionLaws⟩]
      exact hh k
    · intro g _ hg
      apply Finset.sum_eq_zero
      intro a _
      exact placedFrom_To_away C hC t g (hc g a) (p g a) (i g a) k (Ne.symm hg)
    · simp

end RMod.Classification

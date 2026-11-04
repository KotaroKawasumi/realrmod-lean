import RMod.Classification.Proofs.HomogeneousSuperMultiplicity
import RMod.Classification.Proofs.PullbackUnitLaws
import RMod.Classification.Instances.ConvolutionPairings
import Superfusion.Category.ExactPairingNonvanishing

/-!
# Super-multiples of the unit in the identity-supported convolution sector

The original neutral-component matrix maps extend by zero at every other
group degree. Supported extensionality and coordinatewise finite sums
prove their full super-multiplicity laws. Exact pairing excludes an empty
multiple when its first member is nonzero.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_supported_superMultiplicity (A : PullbackObj C t)
    (hA : ∀ k, k ≠ 1 → C.id (A k).val = C.zero) :
    ∃ p q, (twistedPullbackData C hC t ht).HasSuperMultiplicity A
      (twistedPullbackData C hC t ht).tensorUnit p q := by
  have hA₁ : InComponent C.toWeaklyPointedSuperfusionData 0 (A 1).val := by
    simpa only [map_one, toAdd_one] using (A 1).property
  obtain ⟨p, q, hm⟩ := hA₁.neutral_superMultiplicity hC
  have hm' : C.HasSuperMultiplicity (A 1).val (pullbackUnitObj C hC t 1).val p q := by
    rw [pullbackUnitObj, supportedObj_one]
    exact hm
  obtain ⟨i, r, hi, hr, hd, ho, hh⟩ := hm'
  let d := twistedPullbackData C hC t ht
  let i' (j : Fin p ⊕ Fin q) : PullbackHom C t (pullbackUnitObj C hC t) A := singleComponentHom C t 1 (i j)
  let r' (j : Fin p ⊕ Fin q) : PullbackHom C t A (pullbackUnitObj C hC t) := singleComponentHom C t 1 (r j)
  refine ⟨p, q, i', r', ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => singleComponentHom_grade C t 1 hC.toWeaklyPointedSuperfusionLaws (i j) (hi j)
  · exact fun j => singleComponentHom_grade C t 1 hC.toWeaklyPointedSuperfusionLaws (r j) (hr j)
  · intro j
    apply hom_ext_of_supported_source C t 1 hC.toWeaklyPointedSuperfusionLaws (pullbackUnit_supported C hC t)
    change C.comp (singleComponentHom C t 1 (i j) 1) (singleComponentHom C t 1 (r j) 1) = _
    rw [singleComponentHom_at, singleComponentHom_at]
    exact hd j
  · intro j k hjk
    apply hom_ext_of_supported_source C t 1 hC.toWeaklyPointedSuperfusionLaws (pullbackUnit_supported C hC t)
    change C.comp (singleComponentHom C t 1 (i j) 1) (singleComponentHom C t 1 (r k) 1) = C.zero
    rw [singleComponentHom_at, singleComponentHom_at]
    exact ho j k hjk
  · apply hom_ext_of_supported_source C t 1 hC.toWeaklyPointedSuperfusionLaws hA
    change C.add (d.finSum p (fun j => d.comp (r' (Sum.inl j)) (i' (Sum.inl j))) 1)
      (d.finSum q (fun j => d.comp (r' (Sum.inr j)) (i' (Sum.inr j))) 1) = C.id (A 1).val
    rw [PullbackCategory.finSum_apply C hC t ht, PullbackCategory.finSum_apply C hC t ht]
    change C.add
      (C.finSum p (fun j => C.comp (singleComponentHom C t 1 (r (Sum.inl j)) 1)
        (singleComponentHom C t 1 (i (Sum.inl j)) 1)))
      (C.finSum q (fun j => C.comp (singleComponentHom C t 1 (r (Sum.inr j)) 1)
        (singleComponentHom C t 1 (i (Sum.inr j)) 1))) = C.id (A 1).val
    simp only [singleComponentHom_at]
    exact hh

theorem twistedPullback_superMultiplicity_positive {A X : PullbackObj C t} {p q : ℕ}
    (hA : (twistedPullbackData C hC t ht).id A ≠ (twistedPullbackData C hC t ht).zero)
    (hm : (twistedPullbackData C hC t ht).HasSuperMultiplicity A X p q) : 0 < p + q := by
  by_contra hn
  obtain ⟨hp, hq⟩ := Nat.add_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hn)
  subst p
  subst q
  obtain ⟨_, _, _, _, _, _, hh⟩ := hm
  apply hA
  funext k
  have he := congrFun hh k
  change C.add C.zero C.zero = C.id (A k).val at he
  exact he.symm.trans (hC.zero_add C.zero)

theorem twistedPullback_pairing_tensor_nonzero {A B : ConvolutionCategory C hC t ht}
    (p : SuperExactPairing ℝ A B) (hA : 𝟙 A ≠ 0) :
    (twistedPullbackData C hC t ht).id ((twistedPullbackData C hC t ht).tensorObj A B) ≠
      (twistedPullbackData C hC t ht).zero := by
  intro hz
  apply p.not_evenTensor_isZero_of_id_ne_zero hA
  apply (IsZero.iff_id_eq_zero _).mpr
  exact WideSubcategory.hom_ext _ hz

end RMod.Classification

import RMod.Classification.Proofs.PullbackSimples
import RMod.Classification.Proofs.PlacedMaps
import RMod.Classification.Proofs.SimpleIso

/-!
# Every simple in the pullback is supported in one component

Choose a nonzero coordinate of its identity and a simple summand of that
coordinate. Its placed inclusion has an explicit even retraction and is
nonzero, hence simplicity makes it an even isomorphism. This identifies
the simple objects before proving any monoidal laws of the pullback.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_evenMono_of_retraction {X Y : PullbackObj C t}
    (f : PullbackHom C t X Y) (p : PullbackHom C t Y X)
    (hf : ∀ k, C.IsHomogeneous 0 (f k))
    (hfp : ∀ k, C.comp (f k) (p k) = C.id (X k).val) :
    (twistedPullbackData C hC t ht).IsEvenMono f := by
  refine ⟨hf, ?_⟩
  intro Z a b _ _ he
  funext k
  have hk := congrArg (fun q => C.comp (q k) (p k)) he
  change C.comp (C.comp (a k) (f k)) (p k) = C.comp (C.comp (b k) (f k)) (p k) at hk
  simpa only [hC.comp_assoc, hfp k, hC.comp_id] using hk

theorem twistedPullback_simple_id_ne_zero {A : PullbackObj C t}
    (hA : (twistedPullbackData C hC t ht).IsSimple A) :
    (fun k => C.id (A k).val) ≠ (fun _ => C.zero) := by
  let d := twistedPullbackData C hC t ht
  have hm : d.IsEvenMono (d.id A) := twistedPullback_evenMono_of_retraction C hC t ht
    (d.id A) (d.id A) (fun k => hC.id_even (A k).val) (fun k => hC.id_comp _)
  exact (hA A (d.id A) hm).mp ⟨(fun k => hC.id_even (A k).val), d.id A,
    (fun k => hC.id_even (A k).val), funext (fun _ => hC.id_comp _), funext (fun _ => hC.id_comp _)⟩

theorem twistedPullback_simple_iso_placed (A : PullbackObj C t)
    (hA : (twistedPullbackData C hC t ht).IsSimple A) :
    ∃ (g : t.group) (S : C.Obj)
      (hS : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) S),
      C.IsSimple S ∧ (twistedPullbackData C hC t ht).HasHomogeneousIso 0
        (placedObj C hC t g S hS) A := by
  classical
  have hex : ∃ g, C.id (A g).val ≠ C.zero := by
    by_contra h
    apply twistedPullback_simple_id_ne_zero C hC t ht hA
    funext g
    by_contra hg
    exact h ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hex
  obtain ⟨n, S, hs, i, p, hi, hp, hd, ho, hh⟩ := (A g).property
  have hn : n ≠ 0 := by
    intro he
    subst n
    exact hg hh.symm
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let hc := InComponent.of_simple hC (hs j).1 (hs j).2
  let B := placedObj C hC t g (S j) hc
  let f : PullbackHom C t B A := placedTo C hC t g hc (i j)
  let q : PullbackHom C t A B := placedFrom C hC t g hc (p j)
  have hfg : ∀ k, C.IsHomogeneous 0 (f k) := placedTo_grade C hC t g hc _ (hi j)
  have hfq : ∀ k, C.comp (f k) (q k) = C.id (B k).val :=
    placedTo_From_diagonal C hC t g hc _ _ (hd j)
  have hm := twistedPullback_evenMono_of_retraction C hC t ht f q hfg hfq
  have hne : f ≠ (twistedPullbackData C hC t ht).zero := by
    intro he
    have hz := hfq g
    have hzero : f g = C.zero := congrFun he g
    rw [hzero, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws] at hz
    have hbs : C.IsSimple (B g).val := by
      change C.IsSimple (placedObj C hC t g (S j) hc g).val
      rw [placedObj_at]
      exact (hs j).1
    exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hbs hz.symm
  obtain ⟨hf, f', hf', hff', hf'f⟩ := (hA B f hm).mpr hne
  exact ⟨g, S j, hc, (hs j).1, f, f', hff', hf'f, hf, hf'⟩

theorem twistedPullback_simple_support (A : PullbackObj C t)
    (hA : (twistedPullbackData C hC t ht).IsSimple A) :
    ∃ g : t.group, (∀ k, k ≠ g → C.id (A k).val = C.zero) ∧ C.IsSimple (A g).val := by
  obtain ⟨g, S, hc, hs, i, p, hip, hpi, hi, hp⟩ :=
    twistedPullback_simple_iso_placed C hC t ht A hA
  refine ⟨g, ?_, ?_⟩
  · intro k hk
    have hz : C.id (placedObj C hC t g S hc k).val = C.zero := by
      rw [placedObj_away C hC t g S hc k hk]
      exact pullbackZero_id C hC t k
    have he : C.comp (p k) (i k) = C.id (A k).val := congrFun hpi k
    rw [hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz (i k),
      raw_comp_zero hC.toWeaklyPointedSuperfusionLaws] at he
    exact he.symm
  · have hb : C.IsSimple (placedObj C hC t g S hc g).val := by
      rw [placedObj_at]
      exact hs
    exact simple_of_evenIso ⟨C.toWeaklyPointedSuperfusionData,
      hC.toWeaklyPointedSuperfusionLaws⟩ ⟨i g, p g⟩
      ⟨⟨congrFun hip g, congrFun hpi g⟩, hi g, hp g⟩ hb

theorem twistedPullback_graded_schur {X Y : PullbackObj C t}
    (hX : (twistedPullbackData C hC t ht).IsSimple X)
    (hY : (twistedPullbackData C hC t ht).IsSimple Y)
    {a : ZMod 2} (f : PullbackHom C t X Y) (hf : ∀ k, C.IsHomogeneous a (f k))
    (hne : f ≠ (twistedPullbackData C hC t ht).zero) :
    (twistedPullbackData C hC t ht).IsIso f := by
  obtain ⟨g, hx, hsx⟩ := twistedPullback_simple_support C hC t ht X hX
  obtain ⟨h, hy, hsy⟩ := twistedPullback_simple_support C hC t ht Y hY
  have hfg : f g ≠ C.zero := by
    intro he
    exact hne (hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hx f
      (fun _ => C.zero) he)
  have hgh : g = h := by
    by_contra he
    exact hfg (hom_eq_zero_of_target hC.toWeaklyPointedSuperfusionLaws (hy g he) (f g))
  subst h
  obtain ⟨s, hfs, hsf⟩ := hC.graded_schur hsx hsy (f g) (hf g) hfg
  refine ⟨singleComponentHom C t g s, ?_, ?_⟩
  · apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hx
    change C.comp (f g) (singleComponentHom C t g s g) = C.id (X g).val
    rw [singleComponentHom_at, hfs]
  · apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hy
    change C.comp (singleComponentHom C t g s g) (f g) = C.id (Y g).val
    rw [singleComponentHom_at, hsf]

end RMod.Classification

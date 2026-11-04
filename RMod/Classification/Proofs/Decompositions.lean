import RMod.Classification.Proofs.Grading

/-!
# Detection of morphisms by finite decompositions

The completeness equation for inclusions and projections determines every
morphism. All proofs use the existing finite-sum operations; distribution
of composition over sums comes from Mathlib preadditivity. These lemmas are
the matrix-coordinate tests needed for the convolution construction.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {D : WeaklyPointedSuperfusionData.{u, v}}
  (hD : WeaklyPointedSuperfusionLaws D)

include hD

theorem decomposition_singleton (X : D.Obj) :
    D.HasDecomposition X (fun _ : Fin 1 => X) := by
  refine ⟨fun _ => D.id X, fun _ => D.id X,
    fun _ => hD.id_even X, fun _ => hD.id_even X,
    fun _ => hD.comp_id _, ?_, ?_⟩
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · simp only [WeaklyPointedSuperfusionData.finSum, hD.comp_id, hD.zero_add]

omit hD in
theorem decomposition_empty_iff (X : D.Obj) :
    D.HasDecomposition X (Fin.elim0 : Fin 0 → D.Obj) ↔ D.id X = D.zero := by
  constructor
  · rintro ⟨_, _, _, _, _, _, ht⟩
    exact ht.symm
  · intro h
    exact ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), h.symm⟩

/-- Agreement after every summand inclusion implies equality. -/
theorem hom_ext_of_inclusions {X Y : D.Obj} {n : ℕ} {S : Fin n → D.Obj}
    (i : (k : Fin n) → D.Hom (S k) X) (p : (k : Fin n) → D.Hom X (S k))
    (ht : D.finSum n (fun k => D.comp (p k) (i k)) = D.id X)
    (f g : D.Hom X Y) (h : ∀ k, D.comp (i k) f = D.comp (i k) g) : f = g := by
  calc
    f = D.comp (D.id X) f := (hD.id_comp f).symm
    _ = D.comp (D.finSum n (fun k => D.comp (p k) (i k))) f := by rw [ht]
    _ = D.finSum n (fun k => D.comp (p k) (D.comp (i k) f)) := by
      rw [raw_finSum_comp hD]
      simp only [hD.comp_assoc]
    _ = D.finSum n (fun k => D.comp (p k) (D.comp (i k) g)) := by simp only [h]
    _ = D.comp (D.finSum n (fun k => D.comp (p k) (i k))) g := by
      rw [raw_finSum_comp hD]
      simp only [hD.comp_assoc]
    _ = g := by rw [ht, hD.id_comp]

/-- Agreement after every summand projection implies equality. -/
theorem hom_ext_of_projections {X Y : D.Obj} {n : ℕ} {S : Fin n → D.Obj}
    (i : (k : Fin n) → D.Hom (S k) Y) (p : (k : Fin n) → D.Hom Y (S k))
    (ht : D.finSum n (fun k => D.comp (p k) (i k)) = D.id Y)
    (f g : D.Hom X Y) (h : ∀ k, D.comp f (p k) = D.comp g (p k)) : f = g := by
  calc
    f = D.comp f (D.id Y) := (hD.comp_id f).symm
    _ = D.comp f (D.finSum n (fun k => D.comp (p k) (i k))) := by rw [ht]
    _ = D.finSum n (fun k => D.comp (D.comp f (p k)) (i k)) := by
      rw [raw_comp_finSum hD]
      simp only [hD.comp_assoc]
    _ = D.finSum n (fun k => D.comp (D.comp g (p k)) (i k)) := by simp only [h]
    _ = D.comp g (D.finSum n (fun k => D.comp (p k) (i k))) := by
      rw [raw_comp_finSum hD]
      simp only [hD.comp_assoc]
    _ = g := by rw [ht, hD.comp_id]

/-- If all morphisms between summands vanish, every morphism between the
two decomposed objects vanishes, including inhomogeneous morphisms. -/
theorem hom_zero_of_decompositions {X Y : D.Obj} {n m : ℕ}
    {S : Fin n → D.Obj} {T : Fin m → D.Obj}
    (hX : D.HasDecomposition X S) (hY : D.HasDecomposition Y T)
    (h : ∀ i j, ∀ f : D.Hom (S i) (T j), f = D.zero) (f : D.Hom X Y) :
    f = D.zero := by
  obtain ⟨i, p, _, _, _, _, ht⟩ := hX
  obtain ⟨j, q, _, _, _, _, hu⟩ := hY
  apply hom_ext_of_inclusions hD i p ht
  intro a
  apply hom_ext_of_projections hD j q hu
  intro b
  rw [h a b (D.comp (D.comp (i a) f) (q b)), raw_comp_zero hD, raw_zero_comp hD]

/-- Transport a decomposition along a specified even isomorphism. Both
inclusions and projections are transported, preserving all matrix laws. -/
theorem decomposition_of_evenIso {X Y : D.Obj} {n : ℕ} {S : Fin n → D.Obj}
    (hX : D.HasDecomposition X S) (e : D.HasHomogeneousIso 0 X Y) :
    D.HasDecomposition Y S := by
  obtain ⟨i, p, hi, hp, hd, ho, ht⟩ := hX
  obtain ⟨f, g, hfg, hgf, hf, hg⟩ := e
  refine ⟨fun k => D.comp (i k) f, fun k => D.comp g (p k), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, zero_add]
      using hD.comp_grade _ _ (hi k) hf
  · intro k
    simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, zero_add]
      using hD.comp_grade _ _ hg (hp k)
  · intro k
    rw [hD.comp_assoc, ← hD.comp_assoc f, hfg, hD.id_comp, hd]
  · intro k l hkl
    rw [hD.comp_assoc, ← hD.comp_assoc f, hfg, hD.id_comp, ho k l hkl]
  · calc
      _ = D.comp g (D.comp (D.finSum n (fun k => D.comp (p k) (i k))) f) := by
        rw [raw_finSum_comp hD, raw_comp_finSum hD]
        simp only [hD.comp_assoc]
      _ = D.id Y := by rw [ht, hD.id_comp, hgf]

end RMod.Classification

import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Proofs.Decompositions

/-!
# From parity-orbit decompositions to homogeneous matrix units

For each summand choose a homogeneous isomorphism from the fixed object.
Composing its two maps with the even biproduct maps gives matrix units of
the chosen parity. No choices are added to the public Clifford predicate.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {D : WeaklyPointedSuperfusionData.{0, 0}}
  (hD : WeaklyPointedSuperfusionLaws D)

include hD

theorem exists_homogeneousSum_of_degrees {X Y : D.Obj} {n : ℕ} {S : Fin n → D.Obj}
    (a : Fin n → ZMod 2) (hS : ∀ i, D.HasHomogeneousIso (a i) X (S i))
    (hY : D.HasDecomposition Y S) :
    ∃ d : HomogeneousSumData D X Y n, HomogeneousSumLaws d ∧ d.parity = a := by
  classical
  choose f g hfg hgf hf hg using hS
  obtain ⟨i, p, hi, hp, hd, ho, ht⟩ := hY
  refine ⟨⟨a, fun k => D.comp (f k) (i k), fun k => D.comp (p k) (g k)⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro k
    simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, add_zero]
      using hD.comp_grade _ _ (hf k) (hi k)
  · intro k
    simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, zero_add]
      using hD.comp_grade _ _ (hp k) (hg k)
  · intro k
    change D.comp (D.comp (f k) (i k)) (D.comp (p k) (g k)) = D.id X
    rw [hD.comp_assoc, ← hD.comp_assoc (i k), hd, hD.id_comp, hfg]
  · intro k l hkl
    change D.comp (D.comp (f k) (i k)) (D.comp (p l) (g l)) = D.zero
    rw [hD.comp_assoc, ← hD.comp_assoc (i k), ho k l hkl,
      raw_zero_comp hD, raw_comp_zero hD]
  · change D.finSum n (fun k =>
      D.comp (D.comp (p k) (g k)) (D.comp (f k) (i k))) = D.id Y
    simpa only [hD.comp_assoc, ← hD.comp_assoc (g _), hgf, hD.id_comp] using ht

theorem exists_homogeneousSum {X Y : D.Obj} {n : ℕ} {S : Fin n → D.Obj}
    (hS : ∀ i, SameParityOrbit D X (S i)) (hY : D.HasDecomposition Y S) :
    ∃ d : HomogeneousSumData D X Y n, HomogeneousSumLaws d := by
  classical
  choose a ha using hS
  obtain ⟨d, hd, _⟩ := exists_homogeneousSum_of_degrees hD a ha hY
  exact ⟨d, hd⟩

end RMod.Classification

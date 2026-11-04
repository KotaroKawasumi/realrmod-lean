import RMod.Classification.Instances.PlacedMaps
import RMod.Classification.Proofs.SingleComponentHom
import RMod.Classification.Proofs.IsoCalculus

/-!
# Matrix equations for placed inclusions and projections

At the common support the equality comparisons cancel, recovering the
original matrix coefficient. Disjoint supports give zero. These equations
assemble componentwise simple decompositions without any tensor coherence
assumption on the new category.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (hY : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) Y)

theorem placedComparison_evenIso :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (placedComparisonData C hC t g hX) :=
  EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _

theorem placedTo_grade {A : PullbackObj C t} {a : ZMod 2}
    (f : C.Hom X (A g).val) (hf : C.IsHomogeneous a f) :
    ∀ k, C.IsHomogeneous a (placedTo C hC t g hX f k) := by
  apply singleComponentHom_grade C t g hC.toWeaklyPointedSuperfusionLaws
  simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, zero_add] using hC.comp_grade _ _
    (placedComparison_evenIso C hC t g hX).hom_even hf

theorem placedFrom_grade {A : PullbackObj C t} {a : ZMod 2}
    (f : C.Hom (A g).val X) (hf : C.IsHomogeneous a f) :
    ∀ k, C.IsHomogeneous a (placedFrom C hC t g hX f k) := by
  apply singleComponentHom_grade C t g hC.toWeaklyPointedSuperfusionLaws
  simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, add_zero] using hC.comp_grade _ _ hf
    (placedComparison_evenIso C hC t g hX).inv_even

theorem placedTo_From_diagonal {A : PullbackObj C t}
    (i : C.Hom X (A g).val) (p : C.Hom (A g).val X) (hip : C.comp i p = C.id X) (k : t.group) :
    C.comp (placedTo C hC t g hX i k) (placedFrom C hC t g hX p k) =
      C.id (placedObj C hC t g X hX k).val := by
  by_cases hk : k = g
  · subst k
    simp only [placedTo, placedFrom, singleComponentHom_at]
    rw [hC.comp_assoc, ← hC.comp_assoc i, hip, hC.id_comp]
    exact (placedComparison_evenIso C hC t g hX).hom_inv
  · simp only [placedTo, placedFrom, singleComponentHom_away C t g _ k hk,
      raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]
    rw [placedObj_away C hC t g X hX k hk]
    exact (pullbackZero_id C hC t k).symm

theorem placedTo_From_zero {A : PullbackObj C t}
    (i : C.Hom X (A g).val) (p : C.Hom (A g).val Y) (hip : C.comp i p = C.zero) (k : t.group) :
    C.comp (placedTo C hC t g hX i k) (placedFrom C hC t g hY p k) = C.zero := by
  by_cases hk : k = g
  · subst k
    simp only [placedTo, placedFrom, singleComponentHom_at]
    rw [hC.comp_assoc, ← hC.comp_assoc i, hip,
      raw_zero_comp hC.toWeaklyPointedSuperfusionLaws, raw_comp_zero hC.toWeaklyPointedSuperfusionLaws]
  · simp only [placedTo, placedFrom, singleComponentHom_away C t g _ k hk,
      raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

theorem placedTo_From_disjoint {A : PullbackObj C t} (h : t.group) (hgh : g ≠ h)
    (hY' : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho h)) Y)
    (i : C.Hom X (A g).val) (p : C.Hom (A h).val Y) (k : t.group) :
    C.comp (placedTo C hC t g hX i k) (placedFrom C hC t h hY' p k) = C.zero := by
  by_cases hk : k = g
  · have hkh : k ≠ h := hk ▸ hgh
    rw [placedFrom, singleComponentHom_away C t h _ k hkh,
      raw_comp_zero hC.toWeaklyPointedSuperfusionLaws]
  · rw [placedTo, singleComponentHom_away C t g _ k hk,
      raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

theorem placedFrom_To_at {A : PullbackObj C t}
    (p : C.Hom (A g).val X) (i : C.Hom X (A g).val) :
    C.comp (placedFrom C hC t g hX p g) (placedTo C hC t g hX i g) = C.comp p i := by
  simp only [placedTo, placedFrom, singleComponentHom_at]
  rw [hC.comp_assoc, ← hC.comp_assoc _ _ i,
    (placedComparison_evenIso C hC t g hX).inv_hom, hC.id_comp]

theorem placedFrom_To_away {A : PullbackObj C t}
    (p : C.Hom (A g).val X) (i : C.Hom X (A g).val) (k : t.group) (hk : k ≠ g) :
    C.comp (placedFrom C hC t g hX p k) (placedTo C hC t g hX i k) = C.zero := by
  simp only [placedTo, placedFrom, singleComponentHom_away C t g _ k hk,
    raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

end RMod.Classification

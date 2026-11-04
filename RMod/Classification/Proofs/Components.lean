import RMod.Classification.Proofs.Decompositions

/-!
# Orthogonality of the intrinsic type components

The reference property assigns a unique Clifford type to each simple.
Graded Schur and invariance under homogeneous isomorphism imply that Hom
spaces between distinct types vanish. Finite decompositions extend this to
all objects in the components used by pullback. No concrete data of U is
used in these arguments.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C : PiSuperfusionData.{0, 0}} (hC : ReferenceProperty C)

include hC

namespace ReferenceProperty

theorem homogeneous_hom_zero_of_type_ne {X Y : C.Obj} {r s : ZMod 8}
    (hX : C.IsSimple X) (hY : C.IsSimple Y)
    (hr : HasBWType C.toWeaklyPointedSuperfusionData X r)
    (hs : HasBWType C.toWeaklyPointedSuperfusionData Y s) (hrs : r ≠ s)
    {a : ZMod 2} (f : C.Hom X Y) (hf : C.IsHomogeneous a f) : f = C.zero := by
  by_contra hne
  apply hrs
  have ho : SameParityOrbit C.toWeaklyPointedSuperfusionData X Y :=
    ⟨a, homogeneous_schur hC.toWeaklyPointedSuperfusionLaws hX hY f hf hne⟩
  have hyr := (SameParityOrbit.hasBWType_iff hC.toWeaklyPointedSuperfusionLaws ho r).mp hr
  exact (hC.simple_type Y hY).unique hyr hs

/-- Orthogonality concerns every morphism, not only the homogeneous ones. -/
theorem hom_zero_of_type_ne {X Y : C.Obj} {r s : ZMod 8}
    (hX : C.IsSimple X) (hY : C.IsSimple Y)
    (hr : HasBWType C.toWeaklyPointedSuperfusionData X r)
    (hs : HasBWType C.toWeaklyPointedSuperfusionData Y s) (hrs : r ≠ s)
    (f : C.Hom X Y) : f = C.zero := by
  obtain ⟨f₀, f₁, h₀, h₁, hsum⟩ := hC.grade_decomposition f
  rw [← hsum, hC.homogeneous_hom_zero_of_type_ne hX hY hr hs hrs f₀ h₀,
    hC.homogeneous_hom_zero_of_type_ne hX hY hr hs hrs f₁ h₁, hC.zero_add]

end ReferenceProperty

namespace InComponent

/-- A simple with the indicated type is already a one-summand component object. -/
theorem of_simple {X : C.Obj} {r : ZMod 8} (hX : C.IsSimple X)
    (hr : HasBWType C.toWeaklyPointedSuperfusionData X r) :
    InComponent C.toWeaklyPointedSuperfusionData r X :=
  ⟨1, fun _ => X, fun _ => ⟨hX, hr⟩,
    decomposition_singleton hC.toWeaklyPointedSuperfusionLaws X⟩

omit hC in
/-- A zero object lies in every type component through the empty decomposition. -/
theorem of_id_zero {X : C.Obj} (hX : C.id X = C.zero) (r : ZMod 8) :
    InComponent C.toWeaklyPointedSuperfusionData r X :=
  ⟨0, Fin.elim0, (fun i => Fin.elim0 i), (decomposition_empty_iff X).mpr hX⟩

theorem of_evenIso {X Y : C.Obj} {r : ZMod 8}
    (hX : InComponent C.toWeaklyPointedSuperfusionData r X)
    (e : C.HasHomogeneousIso 0 X Y) :
    InComponent C.toWeaklyPointedSuperfusionData r Y := by
  obtain ⟨n, S, hs, hd⟩ := hX
  exact ⟨n, S, hs, decomposition_of_evenIso hC.toWeaklyPointedSuperfusionLaws hd e⟩

/-- Distinct component labels give the zero Hom space. -/
theorem hom_zero {X Y : C.Obj} {r s : ZMod 8}
    (hX : InComponent C.toWeaklyPointedSuperfusionData r X)
    (hY : InComponent C.toWeaklyPointedSuperfusionData s Y)
    (hrs : r ≠ s) (f : C.Hom X Y) : f = C.zero := by
  obtain ⟨n, S, hs, hd⟩ := hX
  obtain ⟨m, T, ht, he⟩ := hY
  exact hom_zero_of_decompositions hC.toWeaklyPointedSuperfusionLaws hd he
    (fun i j => hC.hom_zero_of_type_ne (hs i).1 (ht j).1 (hs i).2 (ht j).2 hrs) f

/-- Orthogonality to the other simple types characterizes a component.
This avoids choosing or flattening new simple decompositions when proving
closure under finite sums. -/
theorem iff_orthogonal (X : C.Obj) (r : ZMod 8) :
    InComponent C.toWeaklyPointedSuperfusionData r X ↔
      ∀ (S : C.Obj) (s : ZMod 8), C.IsSimple S →
        HasBWType C.toWeaklyPointedSuperfusionData S s → s ≠ r →
          ∀ f : C.Hom S X, f = C.zero := by
  constructor
  · intro hX S s hS hs hsr f
    exact hom_zero hC (of_simple hC hS hs) hX hsr f
  · intro h
    obtain ⟨n, S, hs, i, p, hi, hp, hd, ho, ht⟩ := hC.semisimple X
    refine ⟨n, S, ?_, i, p, hi, hp, hd, ho, ht⟩
    intro k
    refine ⟨hs k, ?_⟩
    obtain ⟨s, hsk, _⟩ := hC.simple_type (S k) (hs k)
    have heq : s = r := by
      by_contra hne
      have hz := h (S k) s (hs k) hsk hne (i k)
      apply simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws (hs k)
      rw [← hd k, hz, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]
    exact heq ▸ hsk

/-- Component membership is preserved by any isomorphism. -/
theorem of_iso {X Y : C.Obj} {r : ZMod 8}
    (hX : InComponent C.toWeaklyPointedSuperfusionData r X)
    (f : C.Hom X Y) (hf : C.IsIso f) :
    InComponent C.toWeaklyPointedSuperfusionData r Y := by
  obtain ⟨g, _, hgf⟩ := hf
  apply (iff_orthogonal hC Y r).mpr
  intro S s hS hs hsr k
  have hz := hom_zero hC (of_simple hC hS hs) hX hsr (C.comp k g)
  calc
    k = C.comp (C.comp k g) f := by rw [hC.comp_assoc, hgf, hC.comp_id]
    _ = C.zero := by rw [hz, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

/-- Any finite sum of objects in the same component remains in it. -/
theorem of_decomposition {X : C.Obj} {n : ℕ} {S : Fin n → C.Obj} {r : ZMod 8}
    (hs : ∀ i, InComponent C.toWeaklyPointedSuperfusionData r (S i))
    (hX : C.HasDecomposition X S) :
    InComponent C.toWeaklyPointedSuperfusionData r X := by
  obtain ⟨i, p, _, _, _, _, ht⟩ := hX
  apply (iff_orthogonal hC X r).mpr
  intro T s hT htype hsr f
  apply hom_ext_of_projections hC.toWeaklyPointedSuperfusionLaws i p ht
  intro k
  rw [hom_zero hC (of_simple hC hT htype) (hs k) hsr (C.comp f (p k)),
    raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

/-- A nonzero object belongs to at most one type component. -/
theorem unique {X : C.Obj} {r s : ZMod 8}
    (hr : InComponent C.toWeaklyPointedSuperfusionData r X)
    (hs : InComponent C.toWeaklyPointedSuperfusionData s X)
    (hX : C.id X ≠ C.zero) : r = s := by
  by_contra hne
  exact hX (hom_zero hC hr hs hne (C.id X))

/-- On simple objects the decomposition-based component predicate is exactly
the Clifford-type predicate occurring in P. -/
theorem simple_iff {X : C.Obj} (hX : C.IsSimple X) (r : ZMod 8) :
    InComponent C.toWeaklyPointedSuperfusionData r X ↔
      HasBWType C.toWeaklyPointedSuperfusionData X r := by
  constructor
  · intro hr
    obtain ⟨s, hs, _⟩ := hC.simple_type X hX
    have heq := unique hC hr (of_simple hC hX hs)
      (simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hX)
    exact heq.symm ▸ hs
  · exact of_simple hC hX

end InComponent
end RMod.Classification

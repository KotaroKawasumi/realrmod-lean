import RMod.Classification.Instances.Functors
import RMod.Classification.Proofs.Decompositions

/-!
# Preservation of intrinsic linear and graded data

Superfunctors preserve homogeneous isomorphisms and finite decompositions.
An equivalence is fully faithful on all morphisms, and its even unit also
shows that a map has a given parity exactly when its image does. The same
argument applies to the inverse functor using the even counit.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}

namespace Superfunctor

variable (F : Superfunctor C D)

theorem map_finSum {X Y : C.data.Obj} (n : ℕ) (f : Fin n → C.data.Hom X Y) :
    F.data.map (C.data.finSum n f) = D.data.finSum n (fun i => F.data.map (f i)) := by
  induction n with
  | zero => exact F.laws.map_zero X Y
  | succ n ih =>
    rw [WeaklyPointedSuperfusionData.finSum, WeaklyPointedSuperfusionData.finSum,
      F.laws.map_add, ih]

theorem map_homogeneousIso {X Y : C.data.Obj} {a : ZMod 2}
    (h : C.data.HasHomogeneousIso a X Y) :
    D.data.HasHomogeneousIso a (F.data.obj X) (F.data.obj Y) := by
  obtain ⟨f, g, hfg, hgf, hf, hg⟩ := h
  refine ⟨F.data.map f, F.data.map g, ?_, ?_, F.laws.map_grade _ hf, F.laws.map_grade _ hg⟩
  · rw [← F.laws.map_comp, hfg, F.laws.map_id]
  · rw [← F.laws.map_comp, hgf, F.laws.map_id]

theorem map_decomposition {X : C.data.Obj} {n : ℕ} {S : Fin n → C.data.Obj}
    (h : C.data.HasDecomposition X S) :
    D.data.HasDecomposition (F.data.obj X) (fun i => F.data.obj (S i)) := by
  obtain ⟨i, p, hi, hp, hd, ho, ht⟩ := h
  refine ⟨fun k => F.data.map (i k), fun k => F.data.map (p k),
    fun k => F.laws.map_grade _ (hi k), fun k => F.laws.map_grade _ (hp k), ?_, ?_, ?_⟩
  · intro k
    rw [← F.laws.map_comp, hd, F.laws.map_id]
  · intro k l hkl
    rw [← F.laws.map_comp, ho k l hkl, F.laws.map_zero]
  · simp only [← F.laws.map_comp]
    rw [← F.map_finSum, ht, F.laws.map_id]

end Superfunctor

namespace MonoidalSuperequivalence

open CategoryTheory

variable (E : MonoidalSuperequivalence C D)

theorem map_bijective (X Y : C.data.Obj) :
    Function.Bijective (E.data.forward.map : C.data.Hom X Y → _) :=
  E.underlyingEquivalence.fullyFaithfulFunctor.map_bijective X Y

theorem backward_map_bijective (X Y : D.data.Obj) :
    Function.Bijective (E.data.backward.map : D.data.Hom X Y → _) :=
  E.underlyingEquivalence.symm.fullyFaithfulFunctor.map_bijective X Y

/-- Naturality of the even unit reflects each homogeneous component. -/
theorem map_grade_iff {X Y : C.data.Obj} {a : ZMod 2} (f : C.data.Hom X Y) :
    D.data.IsHomogeneous a (E.data.forward.map f) ↔ C.data.IsHomogeneous a f := by
  refine ⟨fun hf => ?_, E.laws.forward.map_grade f⟩
  have hb := E.laws.backward.map_grade _ hf
  have hu := C.laws.comp_grade _ _ (E.laws.unit_hom_even X) hb
  have h := C.laws.comp_grade _ _ hu (E.laws.unit_inv_even Y)
  rw [zero_add, add_zero] at h
  have he : C.data.comp
      (C.data.comp (E.data.unitHom X) (E.data.backward.map (E.data.forward.map f)))
      (E.data.unitInv Y) = f := by
    rw [← E.laws.unit_naturality, C.laws.comp_assoc, E.laws.unit_hom_inv, C.laws.comp_id]
  rw [he] at h
  exact h

theorem backward_map_grade_iff {X Y : D.data.Obj} {a : ZMod 2} (f : D.data.Hom X Y) :
    C.data.IsHomogeneous a (E.data.backward.map f) ↔ D.data.IsHomogeneous a f := by
  refine ⟨fun hf => ?_, E.laws.backward.map_grade f⟩
  have hb := E.laws.forward.map_grade _ hf
  have hu := D.laws.comp_grade _ _ (E.laws.counit_inv_even X) hb
  have h := D.laws.comp_grade _ _ hu (E.laws.counit_hom_even Y)
  rw [zero_add, add_zero] at h
  have he : D.data.comp
      (D.data.comp (E.data.counitInv X) (E.data.forward.map (E.data.backward.map f)))
      (E.data.counitHom Y) = f := by
    rw [D.laws.comp_assoc, E.laws.counit_naturality, ← D.laws.comp_assoc,
      E.laws.counit_inv_hom, D.laws.id_comp]
  rw [he] at h
  exact h

theorem homogeneousIso_map_iff {X Y : C.data.Obj} {a : ZMod 2} :
    D.data.HasHomogeneousIso a (E.data.forward.obj X) (E.data.forward.obj Y) ↔
      C.data.HasHomogeneousIso a X Y := by
  refine ⟨?_, E.forwardFunctor.map_homogeneousIso⟩
  rintro ⟨f, g, hfg, hgf, hf, hg⟩
  obtain ⟨f', rfl⟩ := (E.map_bijective X Y).surjective f
  obtain ⟨g', rfl⟩ := (E.map_bijective Y X).surjective g
  refine ⟨f', g', ?_, ?_, (E.map_grade_iff f').mp hf, (E.map_grade_iff g').mp hg⟩
  · apply (E.map_bijective X X).injective
    rw [E.laws.forward.map_comp, E.laws.forward.map_id, hfg]
  · apply (E.map_bijective Y Y).injective
    rw [E.laws.forward.map_comp, E.laws.forward.map_id, hgf]

theorem homogeneousIso_backward_map_iff {X Y : D.data.Obj} {a : ZMod 2} :
    C.data.HasHomogeneousIso a (E.data.backward.obj X) (E.data.backward.obj Y) ↔
      D.data.HasHomogeneousIso a X Y := by
  refine ⟨?_, E.backwardFunctor.map_homogeneousIso⟩
  rintro ⟨f, g, hfg, hgf, hf, hg⟩
  obtain ⟨f', rfl⟩ := (E.backward_map_bijective X Y).surjective f
  obtain ⟨g', rfl⟩ := (E.backward_map_bijective Y X).surjective g
  refine ⟨f', g', ?_, ?_, (E.backward_map_grade_iff f').mp hf,
    (E.backward_map_grade_iff g').mp hg⟩
  · apply (E.backward_map_bijective X X).injective
    rw [E.laws.backward.map_comp, E.laws.backward.map_id, hfg]
  · apply (E.backward_map_bijective Y Y).injective
    rw [E.laws.backward.map_comp, E.laws.backward.map_id, hgf]

end MonoidalSuperequivalence
end RMod.Classification

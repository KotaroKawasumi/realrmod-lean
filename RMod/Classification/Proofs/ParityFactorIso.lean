import RMod.Classification.Proofs.ParitySchur

/-!
# Homogeneous comparison with a right parity factor

The degree-zero comparison is the inverse right unitor, and the
degree-one comparison is the specified right odd isomorphism. These
comparisons preserve nonvanishing and supply the two simultaneous
homogeneous transports used to construct left duals.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

theorem right_factor_homogeneous_iso (X : C.data.Obj) (a : ZMod 2) :
    C.data.HasHomogeneousIso a X (C.data.tensorObj X (p.factor a)) := by
  rcases parity_cases a with rfl | rfl
  · exact ⟨C.data.rightUnitorInv X, C.data.rightUnitorHom X,
      C.laws.right_unitor_inv_hom X, C.laws.right_unitor_hom_inv X,
      C.laws.right_unitor_inv_even X, C.laws.right_unitor_hom_even X⟩
  · exact ⟨p.rightZInv X, p.rightZHom X, (hp.rightZ_iso C.laws X).inv_hom,
      (hp.rightZ_iso C.laws X).hom_inv, hp.rightZ_inv_odd C.laws X, hp.rightZ_hom_odd C.laws X⟩

theorem right_factor_id_ne_zero (X : C.data.Obj) (a : ZMod 2) (hX : C.data.id X ≠ C.data.zero) :
    C.data.id (C.data.tensorObj X (p.factor a)) ≠ C.data.zero := by
  obtain ⟨f, g, hfg, _, _, _⟩ := right_factor_homogeneous_iso C p hp X a
  intro hz
  have hf := C.laws.comp_id f
  rw [hz, raw_comp_zero C.laws] at hf
  apply hX
  rw [← hfg, ← hf, raw_zero_comp C.laws]

omit hp in
theorem simple_even_schur {X : C.data.Obj} (hX : C.data.IsSimple X)
    (f : C.data.Hom X X) (hf : C.data.IsHomogeneous 0 f) (hne : f ≠ C.data.zero) :
    C.data.IsEvenIso f := by
  obtain ⟨g, hfg, hgf⟩ := C.laws.graded_schur hX hX f hf hne
  exact ⟨hf, g, homogeneous_inverse C.laws f g hfg hgf hf, hfg, hgf⟩

end RMod.Classification

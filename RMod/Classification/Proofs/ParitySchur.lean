import RMod.Classification.Proofs.DualSchur
import RMod.Classification.Proofs.RightParityComparison

/-!
# Even Schur under a homogeneous change of object

Conjugation by an isomorphism of degree a takes even endomorphisms to
degree a+0+a=0. It reflects zero and invertibility. Consequently adding
the right parity factor preserves the even Schur property needed to
complete the constructed dual pairing.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{u, v})

theorem even_schur_of_homogeneous_iso {X Y : C.data.Obj} {a : ZMod 2}
    (hX : ∀ f : C.data.Hom X X, C.data.IsHomogeneous 0 f → f ≠ C.data.zero → C.data.IsEvenIso f)
    (hi : C.data.HasHomogeneousIso a X Y)
    (k : C.data.Hom Y Y) (hk : C.data.IsHomogeneous 0 k) (hne : k ≠ C.data.zero) :
    C.data.IsEvenIso k := by
  obtain ⟨f, g, hfg, hgf, hf, hg⟩ := hi
  let e : @CategoryTheory.Iso (LinearCategory C) _ X Y := ⟨f, g, hfg, hgf⟩
  let s : @Quiver.Hom (LinearCategory C) _ Y Y := k
  let j : @Quiver.Hom (LinearCategory C) _ X X := e.hom ≫ s ≫ e.inv
  have hj : C.data.IsHomogeneous 0 j := by
    have hh := C.laws.comp_grade f (C.data.comp k g) hf (C.laws.comp_grade k g hk hg)
    simp only [zero_add, CharTwo.add_self_eq_zero] at hh
    exact hh
  have hc : s = e.inv ≫ j ≫ e.hom := by simp [j]
  have hsne : s ≠ 0 := hne
  have hjne : j ≠ 0 := by
    intro hz
    apply hsne
    rw [hc, hz]
    simp
  obtain ⟨_, l, _, hjl, hlj⟩ := hX j hj hjne
  letI : IsIso j := ⟨⟨l, hjl, hlj⟩⟩
  haveI : IsIso s := by
    have h : IsIso (e.inv ≫ j ≫ e.hom) :=
      @IsIso.comp_isIso (LinearCategory C) _ _ _ _ e.inv (j ≫ e.hom)
        e.isIso_inv (@IsIso.comp_isIso (LinearCategory C) _ _ _ _ j e.hom inferInstance e.isIso_hom)
    exact hc.symm ▸ h
  have hki : C.data.comp k (inv s) = C.data.id Y := IsIso.hom_inv_id s
  have hik : C.data.comp (inv s) k = C.data.id Y := IsIso.inv_hom_id s
  exact ⟨hk, inv s, homogeneous_inverse C.laws k _ hki hik hk, hki, hik⟩

theorem right_factor_even_schur (p : PiData C.data) (hp : PiLaws C.data p) {X : C.data.Obj}
    (hX : ∀ f : C.data.Hom X X, C.data.IsHomogeneous 0 f → f ≠ C.data.zero → C.data.IsEvenIso f)
    (a : ZMod 2) (f : C.data.Hom (C.data.tensorObj X (p.factor a)) (C.data.tensorObj X (p.factor a)))
    (hf : C.data.IsHomogeneous 0 f) (hne : f ≠ C.data.zero) : C.data.IsEvenIso f := by
  rcases parity_cases a with rfl | rfl
  · exact even_schur_of_homogeneous_iso C hX
      ⟨C.data.rightUnitorInv X, C.data.rightUnitorHom X,
        C.laws.right_unitor_inv_hom X, C.laws.right_unitor_hom_inv X,
        C.laws.right_unitor_inv_even X, C.laws.right_unitor_hom_even X⟩ f hf hne
  · exact even_schur_of_homogeneous_iso C hX
      ⟨p.rightZInv X, p.rightZHom X, (hp.rightZ_iso C.laws X).inv_hom,
        (hp.rightZ_iso C.laws X).hom_inv, hp.rightZ_inv_odd C.laws X, hp.rightZ_hom_odd C.laws X⟩ f hf hne

end RMod.Classification

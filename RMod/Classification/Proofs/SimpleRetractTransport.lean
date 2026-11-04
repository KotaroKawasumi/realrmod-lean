import RMod.Classification.Proofs.SimpleCorners
import RMod.Classification.Proofs.SimpleRetractDetection

/-!
# Transporting a simple retract through an endomorphism algebra equivalence

The image of the source projector is an even nonzero idempotent. Detect
a simple retract below it using target semisimplicity. Pulling this
smaller projector back gives a nonzero even idempotent in the source
simple corner, hence the whole source projector. The detected target
retract therefore splits the exact transported projector.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

theorem exists_simpleRetract_transport (C D : WeaklyPointedSuperfusion.{0, 0})
    (X : LinearCategory C) (Y : LinearCategory D) (d : SimpleRetract C X)
    (φ : End X ≃ₐ[ℝ] End Y)
    (hφ : ∀ {a : ZMod 2} (f : End X),
      D.data.IsHomogeneous a (φ f) ↔ C.data.IsHomogeneous a f) :
    ∃ t : SimpleRetract D Y, SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data) := by
  let e : End X := SimpleRetract.projectorData d.data
  have he : C.data.IsHomogeneous 0 e := d.projector_even
  have hee : e ≫ e = e := d.projector_idempotent
  have hen : e ≠ 0 := d.projector_ne_zero
  have hfe : D.data.IsHomogeneous 0 (φ e) := (hφ e).mpr he
  have hfee : φ e ≫ φ e = φ e := (φ.map_mul e e).symm.trans (congrArg φ hee)
  have hfen : φ e ≠ 0 := fun hz => hen (φ.injective (hz.trans (map_zero φ).symm))
  obtain ⟨t, hif, hfp⟩ := exists_simpleRetract_under_idempotent D Y (φ e) hfe hfee hfen
  let q : End Y := SimpleRetract.projectorData t.data
  let q' : End X := φ.symm q
  have hq : D.data.IsHomogeneous 0 q := t.projector_even
  have hq' : C.data.IsHomogeneous 0 q' := by
    apply (hφ q').mp
    change D.data.IsHomogeneous 0 (φ (φ.symm q))
    rw [AlgEquiv.apply_symm_apply]
    exact hq
  have hqq' : q' ≫ q' = q' := by
    apply φ.injective
    change φ (q' * q') = φ q'
    rw [map_mul]
    change (φ (φ.symm q)) * (φ (φ.symm q)) = φ (φ.symm q)
    rw [AlgEquiv.apply_symm_apply]
    exact t.projector_idempotent
  have hqn' : q' ≠ 0 := by
    intro hz
    have hh : q = 0 := (φ.apply_symm_apply q).symm.trans ((congrArg φ hz).trans (map_zero φ))
    exact t.projector_ne_zero hh
  have hqe' : q' ≫ (d.data.projection ≫ d.data.inclusion) = q' := by
    apply φ.injective
    change φ (e * q') = φ q'
    rw [map_mul]
    change φ e * φ (φ.symm q) = φ (φ.symm q)
    rw [AlgEquiv.apply_symm_apply]
    change D.data.comp (D.data.comp t.data.projection t.data.inclusion) (φ e) = q
    rw [D.laws.comp_assoc, hif]
    rfl
  have heq' : (d.data.projection ≫ d.data.inclusion) ≫ q' = q' := by
    apply φ.injective
    change φ (q' * e) = φ q'
    rw [map_mul]
    change φ (φ.symm q) * φ e = φ (φ.symm q)
    rw [AlgEquiv.apply_symm_apply]
    change D.data.comp (φ e) (D.data.comp t.data.projection t.data.inclusion) = q
    rw [← D.laws.comp_assoc, hfp]
    rfl
  have hh : q' = e := simple_retract_idempotent_unique C d.laws.simple
    d.data.inclusion d.data.projection d.laws.inclusion_even d.laws.projection_even
    q' hq' hqq' hqn' hqe' heq'
  exact ⟨t, (φ.apply_symm_apply q).symm.trans (congrArg φ hh)⟩

end RMod.Classification

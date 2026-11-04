import RMod.Classification.Instances.SingleComponentHom
import RMod.Classification.Proofs.ZeroObjects

/-!
# Coordinate and grading laws for a single-component map

At its support the map is the original morphism; away from its support
it is zero. The grading is preserved, and maps with supported source or
target are determined by their single potentially nonzero coordinate.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (t : TwistData) {X Y : PullbackObj C t} (g : t.group)

theorem singleComponentHom_at (f : C.Hom (X g).val (Y g).val) : singleComponentHom C t g f g = f := by
  classical
  simp [singleComponentHom]

theorem singleComponentHom_away (f : C.Hom (X g).val (Y g).val) (k : t.group) (hk : k ≠ g) :
    singleComponentHom C t g f k = C.zero := by
  classical
  simp only [singleComponentHom, dif_neg hk]

variable (hC : WeaklyPointedSuperfusionLaws C.toWeaklyPointedSuperfusionData)

include hC

theorem singleComponentHom_grade {a : ZMod 2} (f : C.Hom (X g).val (Y g).val)
    (hf : C.IsHomogeneous a f) : ∀ k, C.IsHomogeneous a (singleComponentHom C t g f k) := by
  intro k
  by_cases hk : k = g
  · subst k
    rw [singleComponentHom_at]
    exact hf
  · rw [singleComponentHom_away C t g f k hk]
    exact hC.grade_zero _ _ _

theorem hom_ext_of_supported_source (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero)
    (f h : PullbackHom C t X Y) (he : f g = h g) : f = h := by
  funext k
  by_cases hk : k = g
  · exact hk ▸ he
  · exact (hom_eq_zero_of_source hC (hX k hk) (f k)).trans
      (hom_eq_zero_of_source hC (hX k hk) (h k)).symm

theorem hom_ext_of_supported_target (hY : ∀ k, k ≠ g → C.id (Y k).val = C.zero)
    (f h : PullbackHom C t X Y) (he : f g = h g) : f = h := by
  funext k
  by_cases hk : k = g
  · exact hk ▸ he
  · exact (hom_eq_zero_of_target hC (hY k hk) (f k)).trans
      (hom_eq_zero_of_target hC (hY k hk) (h k)).symm

end RMod.Classification

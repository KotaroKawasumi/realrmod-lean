import RMod.Classification.Abstract.Pullback
import RMod.Classification.Proofs.TensorCalculus

/-!
# Maps of the right-parity-factor summands

The parity factor is fixed at each pair of group degrees, so its identity
contributes no additional interchange sign. These formulas retain the
original super interchange sign of the two variable input maps.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

variable (C : PiSuperfusionData.{0, 0})
  (hC : WeaklyPointedSuperfusionLaws C.toWeaklyPointedSuperfusionData) (t : TwistData)

include hC

theorem twistSummandHom_id (X Y : PullbackObj C t) (a b : t.group) :
    twistSummandHom C t (fun g => C.id (X g).val) (fun g => C.id (Y g).val) a b =
      C.id (twistSummand C t X Y a b) := by
  simp only [twistSummandHom, twistSummand, hC.tensor_id]

theorem twistSummandHom_grade {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') (p q : ZMod 2)
    (hf : ∀ a, C.IsHomogeneous p (f a)) (hg : ∀ b, C.IsHomogeneous q (g b))
    (a b : t.group) : C.IsHomogeneous (p + q) (twistSummandHom C t f g a b) := by
  have h := hC.tensor_grade _ _ (hC.tensor_grade _ _ (hf a) (hg b))
    (hC.id_even (C.pi.factor (t.nu a b)))
  change C.IsHomogeneous ((p + q) + 0) (twistSummandHom C t f g a b) at h
  simpa only [add_zero] using h

theorem twistSummandHom_zero_left {X X' Y Y' : PullbackObj C t}
    (g : PullbackHom C t Y Y') (a b : t.group) :
    twistSummandHom C t (X := X) (X' := X') (fun _ => C.zero) g a b = C.zero := by
  simp only [twistSummandHom, tensor_zero_left hC]

theorem twistSummandHom_zero_right {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (a b : t.group) :
    twistSummandHom C t (Y := Y) (Y' := Y') f (fun _ => C.zero) a b = C.zero := by
  simp only [twistSummandHom, tensor_zero_right hC, tensor_zero_left hC]

theorem twistSummandHom_add_left {X X' Y Y' : PullbackObj C t}
    (f f' : PullbackHom C t X X') (g : PullbackHom C t Y Y') (a b : t.group) :
    twistSummandHom C t (fun k => C.add (f k) (f' k)) g a b =
      C.add (twistSummandHom C t f g a b) (twistSummandHom C t f' g a b) := by
  simp only [twistSummandHom, hC.tensor_add_left]

theorem twistSummandHom_add_right {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (g g' : PullbackHom C t Y Y') (a b : t.group) :
    twistSummandHom C t f (fun k => C.add (g k) (g' k)) a b =
      C.add (twistSummandHom C t f g a b) (twistSummandHom C t f g' a b) := by
  simp only [twistSummandHom, hC.tensor_add_right, hC.tensor_add_left]

theorem twistSummandHom_smul_left {X X' Y Y' : PullbackObj C t}
    (r : ℝ) (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') (a b : t.group) :
    twistSummandHom C t (fun k => C.smul r (f k)) g a b =
      C.smul r (twistSummandHom C t f g a b) := by
  simp only [twistSummandHom, hC.tensor_smul_left]

theorem twistSummandHom_smul_right {X X' Y Y' : PullbackObj C t}
    (r : ℝ) (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') (a b : t.group) :
    twistSummandHom C t f (fun k => C.smul r (g k)) a b =
      C.smul r (twistSummandHom C t f g a b) := by
  simp only [twistSummandHom, hC.tensor_smul_right, hC.tensor_smul_left]

theorem twistSummandHom_interchange {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : PullbackObj C t}
    (f : PullbackHom C t Y₁ Z₁) (g : PullbackHom C t Y₂ Z₂)
    (h : PullbackHom C t X₁ Y₁) (k : PullbackHom C t X₂ Y₂) (p q : ZMod 2)
    (hg : ∀ b, C.IsHomogeneous p (g b)) (hh : ∀ a, C.IsHomogeneous q (h a))
    (a b : t.group) :
    C.comp (twistSummandHom C t h k a b) (twistSummandHom C t f g a b) =
      C.smul ((-1 : ℝ) ^ (p * q).val)
        (twistSummandHom C t (fun d => C.comp (h d) (f d))
          (fun d => C.comp (k d) (g d)) a b) := by
  unfold twistSummandHom
  rw [interchange_second_even hC _ _ _ _ (hC.id_even _), hC.id_comp,
    hC.super_interchange _ _ _ _ (hg b) (hh a), hC.tensor_smul_left]

end RMod.Classification

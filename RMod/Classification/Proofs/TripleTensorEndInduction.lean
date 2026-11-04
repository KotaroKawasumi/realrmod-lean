import RMod.Classification.Proofs.TensorEndHomogeneousInduction

/-!
# Homogeneous endomorphisms of a triple are spanned by pure triples

Apply the proved binary graded span induction twice. The inner induction
is transported through tensoring with the third homogeneous factor by
bilinearity. This permits testing supercentrality on three independent
homogeneous endomorphisms without assuming the intermediate object simple.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

theorem tripleTensorEnd_homogeneous_induction (C : WeaklyPointedSuperfusion.{0, 0})
    (X Y Z : LinearCategory C) (hY : C.data.IsSimple Y) (hZ : C.data.IsSimple Z) {a : ZMod 2}
    {P : @End (LinearCategory C) _ (C.data.tensorObj (C.data.tensorObj X Y) Z) → Prop}
    (k : @End (LinearCategory C) _ (C.data.tensorObj (C.data.tensorObj X Y) Z)) (hk : C.data.IsHomogeneous a k)
    (htensor : ∀ (b c d : ZMod 2) (f : End X) (g : End Y) (h : End Z), (b + c) + d = a →
      C.data.IsHomogeneous b f → C.data.IsHomogeneous c g → C.data.IsHomogeneous d h →
        P (C.data.tensorHom (C.data.tensorHom f g) h))
    (hzero : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hsmul : ∀ (r : ℝ) f, P f → P (r • f)) : P k := by
  refine tensorEnd_homogeneous_induction C (C.data.tensorObj X Y) Z hZ k hk ?_ hzero hadd hsmul
  intro b c f g hbc hf hg
  refine tensorEnd_homogeneous_induction C X Y hY
    (P := fun f => P (C.data.tensorHom f g)) f hf ?_ ?_ ?_ ?_
  · intro d e u v hde hu hv
    exact htensor d e c u v g (hde ▸ hbc) hu hv hg
  · change P (C.data.tensorHom C.data.zero g)
    rw [tensor_zero_left C.laws]
    exact hzero
  · intro u v hu hv
    change P (C.data.tensorHom (C.data.add u v) g)
    rw [C.laws.tensor_add_left]
    exact hadd _ _ hu hv
  · intro r u hu
    change P (C.data.tensorHom (C.data.smul r u) g)
    rw [C.laws.tensor_smul_left]
    exact hsmul r _ hu

end RMod.Classification

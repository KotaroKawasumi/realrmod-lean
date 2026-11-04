import RMod.Classification.Proofs.ParityDualSnake

/-!
# The reciprocal omega normalization of the first snake

The associator contributes omega and the specified evaluation contributes
its inverse. Bilinearity extracts these scalars from the actual raw tensor
and composition maps, leaving the proved scalar-free parity snake.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

/-- Reciprocal scalars on two consecutive maps cancel by bilinearity. -/
theorem comp_reciprocal_scales {W X Y Z : C.data.Obj}
    (f : C.data.Hom W X) (g : C.data.Hom X Y) (h : C.data.Hom Y Z) (ω : ℝˣ) :
    C.data.comp (C.data.comp f (C.data.smul (ω : ℝ) g))
      (C.data.smul ((ω⁻¹ : ℝˣ) : ℝ) h) = C.data.comp (C.data.comp f g) h := by
  simp only [C.laws.comp_smul, C.laws.smul_comp, ← C.laws.mul_smul]
  have he : ((ω⁻¹ : ℝˣ) : ℝ) * (ω : ℝ) = 1 := congrArg Units.val (inv_mul_cancel ω)
  rw [he, C.laws.one_smul]

include hp

theorem localAssociator_weighted_first_snake {X Y : C.data.Obj}
    (q : DualPairing C X Y) (a : ZMod 2) (ω : ℝˣ) :
    C.data.comp
      (C.data.comp
        (C.data.tensorHom (C.data.tensorHom (p.twistedCoevaluation q.data a) (C.data.id X))
          (C.data.id C.data.tensorUnit))
        (p.localAssociator X (C.data.tensorObj Y (p.factor a)) X a 0 a 0 rfl ω).hom)
      (C.data.tensorHom (C.data.tensorHom (C.data.id X) (p.twistedEvaluation q.data a ω))
        (C.data.id C.data.tensorUnit)) =
      C.data.tensorHom (C.data.comp (C.data.leftUnitorHom X) (C.data.rightUnitorInv X))
        (C.data.id C.data.tensorUnit) := by
  have ha : (p.localAssociator X (C.data.tensorObj Y (p.factor a)) X a 0 a 0 rfl ω).hom =
      C.data.smul (ω : ℝ)
        (p.localAssociator X (C.data.tensorObj Y (p.factor a)) X a 0 a 0 rfl 1).hom := by
    simp only [PiData.localAssociator, IsoData.scale, Units.val_one, C.laws.one_smul]
  have he : C.data.tensorHom
      (C.data.tensorHom (C.data.id X) (p.twistedEvaluation q.data a ω)) (C.data.id C.data.tensorUnit) =
      C.data.smul ((ω⁻¹ : ℝˣ) : ℝ)
        (C.data.tensorHom (C.data.tensorHom (C.data.id X)
          (C.data.comp (p.dualNegativeNormalizer X Y a).hom q.data.eval)) (C.data.id C.data.tensorUnit)) := by
    simp only [PiData.twistedEvaluation, C.laws.tensor_smul_left, C.laws.tensor_smul_right]
  erw [ha, he]
  exact (comp_reciprocal_scales C _ _ _ ω).trans (localAssociator_first_snake C p hp q a)

end RMod.Classification

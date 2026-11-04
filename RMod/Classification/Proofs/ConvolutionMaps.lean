import RMod.Classification.Instances.ConvolutionMaps
import RMod.Classification.Proofs.TwistSummandMaps

/-!
# Linearity, parity and super interchange for convolution

The equations for maps of finite sums lift the corresponding equations
of each tensor summand. Every formula is proved in the abstract category
C; no regular-module model enters either the construction or its laws.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionObj convolutionFamily convolutionSum twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionHom_id (X Y : PullbackObj C t) :
    convolutionHom C hC t (fun g => C.id (X g).val) (fun g => C.id (Y g).val) =
      fun k => C.id (convolutionObj C hC t X Y k).val := by
  funext k
  simp only [convolutionHom, twistSummandHom_id C hC.toWeaklyPointedSuperfusionLaws]
  exact Biproduct.mapHom_id hC.toWeaklyPointedSuperfusionLaws (convolutionSum C hC t X Y k)

theorem convolutionHom_grade {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') (p q : ZMod 2)
    (hf : ∀ a, C.IsHomogeneous p (f a)) (hg : ∀ b, C.IsHomogeneous q (g b)) :
    ∀ k, C.IsHomogeneous (p + q) (convolutionHom C hC t f g k) := by
  intro k
  apply Biproduct.mapHom_grade hC.toWeaklyPointedSuperfusionLaws
  intro i
  exact twistSummandHom_grade C hC.toWeaklyPointedSuperfusionLaws t f g p q hf hg _ _

theorem convolutionHom_zero_left {X X' Y Y' : PullbackObj C t}
    (g : PullbackHom C t Y Y') :
    convolutionHom C hC t (X := X) (X' := X') (fun _ => C.zero) g = fun _ => C.zero := by
  funext k
  simp only [convolutionHom, twistSummandHom_zero_left C hC.toWeaklyPointedSuperfusionLaws,
    Biproduct.mapHom_zero hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X Y k) (convolutionSum C hC t X' Y' k)]

theorem convolutionHom_zero_right {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') :
    convolutionHom C hC t (Y := Y) (Y' := Y') f (fun _ => C.zero) = fun _ => C.zero := by
  funext k
  simp only [convolutionHom, twistSummandHom_zero_right C hC.toWeaklyPointedSuperfusionLaws,
    Biproduct.mapHom_zero hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X Y k) (convolutionSum C hC t X' Y' k)]

theorem convolutionHom_add_left {X X' Y Y' : PullbackObj C t}
    (f f' : PullbackHom C t X X') (g : PullbackHom C t Y Y') :
    convolutionHom C hC t (fun k => C.add (f k) (f' k)) g =
      fun k => C.add (convolutionHom C hC t f g k) (convolutionHom C hC t f' g k) := by
  funext k
  simp only [convolutionHom, twistSummandHom_add_left C hC.toWeaklyPointedSuperfusionLaws,
    Biproduct.mapHom_add hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X Y k) (convolutionSum C hC t X' Y' k)]

theorem convolutionHom_add_right {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (g g' : PullbackHom C t Y Y') :
    convolutionHom C hC t f (fun k => C.add (g k) (g' k)) =
      fun k => C.add (convolutionHom C hC t f g k) (convolutionHom C hC t f g' k) := by
  funext k
  simp only [convolutionHom, twistSummandHom_add_right C hC.toWeaklyPointedSuperfusionLaws,
    Biproduct.mapHom_add hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X Y k) (convolutionSum C hC t X' Y' k)]

theorem convolutionHom_smul_left {X X' Y Y' : PullbackObj C t}
    (r : ℝ) (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') :
    convolutionHom C hC t (fun k => C.smul r (f k)) g =
      fun k => C.smul r (convolutionHom C hC t f g k) := by
  funext k
  simp only [convolutionHom, twistSummandHom_smul_left C hC.toWeaklyPointedSuperfusionLaws,
    Biproduct.mapHom_smul hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X Y k) (convolutionSum C hC t X' Y' k)]

theorem convolutionHom_smul_right {X X' Y Y' : PullbackObj C t}
    (r : ℝ) (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') :
    convolutionHom C hC t f (fun k => C.smul r (g k)) =
      fun k => C.smul r (convolutionHom C hC t f g k) := by
  funext k
  simp only [convolutionHom, twistSummandHom_smul_right C hC.toWeaklyPointedSuperfusionLaws,
    Biproduct.mapHom_smul hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X Y k) (convolutionSum C hC t X' Y' k)]

theorem convolutionHom_interchange {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : PullbackObj C t}
    (f : PullbackHom C t Y₁ Z₁) (g : PullbackHom C t Y₂ Z₂)
    (h : PullbackHom C t X₁ Y₁) (k : PullbackHom C t X₂ Y₂) (p q : ZMod 2)
    (hg : ∀ b, C.IsHomogeneous p (g b)) (hh : ∀ a, C.IsHomogeneous q (h a)) :
    (fun d => C.comp (convolutionHom C hC t h k d) (convolutionHom C hC t f g d)) =
      fun d => C.smul ((-1 : ℝ) ^ (p * q).val)
        (convolutionHom C hC t (fun a => C.comp (h a) (f a))
          (fun b => C.comp (k b) (g b)) d) := by
  funext d
  simp only [convolutionHom, Biproduct.mapHom_comp hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X₁ X₂ d) (convolutionSum C hC t Y₁ Y₂ d)
      (convolutionSum C hC t Z₁ Z₂ d),
    twistSummandHom_interchange C hC.toWeaklyPointedSuperfusionLaws t f g h k p q hg hh,
    Biproduct.mapHom_smul hC.toWeaklyPointedSuperfusionLaws
      (convolutionSum C hC t X₁ X₂ d) (convolutionSum C hC t Z₁ Z₂ d)]

end RMod.Classification

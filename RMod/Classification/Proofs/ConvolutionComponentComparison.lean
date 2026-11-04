import RMod.Classification.Instances.ConvolutionComponentComparison
import RMod.Classification.Proofs.ConvolutionSupportedInclusion
import RMod.Classification.Proofs.RightFactorDeletion

/-!
# Degrees and signed naturality of the actual convolution comparison

Projection is even and deletion has precisely the prescribed binary
parity. Naturality is projection naturality followed by the deletion
square, so it holds against all pairs of homogeneous input morphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionComponentComparison_homogeneousIso
    (X Y : PullbackObj C t) (k g : t.group)
    (hX : ∀ l, l ≠ g → C.id (X l).val = C.zero) :
    HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData (t.nu g (g⁻¹ * k))
      (convolutionComponentComparisonData C hC t X Y k g) := by
  have h := ((convolutionSupportedInclusion_evenIso C hC t X Y g hX k).symm.homogeneous).trans
    hC.toWeaklyPointedSuperfusionLaws
    (hC.pi.rightFactorDeletion_homogeneousIso hC.toWeaklyPointedSuperfusionLaws _ _)
  rw [zero_add] at h
  exact h

theorem convolutionComponentComparison_naturality
    {X X' Y Y' : PullbackObj C t} {a b : ZMod 2}
    (f : PullbackHom C t X X') (q : PullbackHom C t Y Y')
    (hf : ∀ k, C.IsHomogeneous a (f k)) (hq : ∀ k, C.IsHomogeneous b (q k)) (k g : t.group) :
    C.comp (convolutionHom C hC t f q k)
      (convolutionComponentComparisonData C hC t X' Y' k g).hom =
      C.smul ((-1 : ℝ) ^ (t.nu g (g⁻¹ * k) * (a + b)).val)
        (C.comp (convolutionComponentComparisonData C hC t X Y k g).hom
          (C.tensorHom (f g) (q (g⁻¹ * k)))) := by
  let i := convolutionProjection C hC t X Y k g
  let i' := convolutionProjection C hC t X' Y' k g
  let d := C.pi.rightFactorDeletion (C.tensorObj (X g).val (Y (g⁻¹ * k)).val) (t.nu g (g⁻¹ * k))
  let d' := C.pi.rightFactorDeletion (C.tensorObj (X' g).val (Y' (g⁻¹ * k)).val) (t.nu g (g⁻¹ * k))
  let r := (-1 : ℝ) ^ (t.nu g (g⁻¹ * k) * (a + b)).val
  have hn := hC.pi.rightFactorDeletion_naturality hC.toWeaklyPointedSuperfusionLaws
    (t.nu g (g⁻¹ * k)) (C.tensorHom (f g) (q (g⁻¹ * k)))
    (hC.tensor_grade _ _ (hf g) (hq (g⁻¹ * k)))
  calc
    _ = C.comp (C.comp (convolutionHom C hC t f q k) i') d'.hom :=
      (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp i (twistSummandHom C t f q g (g⁻¹ * k))) d'.hom :=
      congrArg (fun m => C.comp m d'.hom) (convolutionMap_projection C hC t f q k g)
    _ = C.comp i (C.comp (twistSummandHom C t f q g (g⁻¹ * k)) d'.hom) :=
      hC.comp_assoc _ _ _
    _ = C.comp i (C.smul r (C.comp d.hom (C.tensorHom (f g) (q (g⁻¹ * k))))) :=
      congrArg (C.comp i) hn
    _ = _ := by rw [hC.comp_smul, ← hC.comp_assoc]; rfl

end RMod.Classification

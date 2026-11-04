import RMod.Classification.Proofs.PlacedDualPairing
import RMod.Classification.Proofs.ConvolutionPartialMaps
import RMod.Classification.Proofs.ConvolutionUnitInverseInsertions

/-!
# The pairing maps on their matching convolution summands

Coevaluation enters its chosen summand at the identity. Evaluation
restricted to the reverse summand is exactly the specified local block.
Tensoring the coevaluation gives the corresponding threefold inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

theorem placedTwistedCoevaluation_at : placedTwistedCoevaluation C hC t g hX q 1 =
    C.comp (placedCoevaluationBlock C hC t g hX q)
      (convolutionInclusion C hC t (placedObj C hC t g X hX) (placedRightDualObj C hC t g hX q) 1 g) :=
  singleComponentHom_at C t 1 _

theorem placedTwistedEvaluation_at : placedTwistedEvaluation C hC t ht g hX q 1 =
    C.comp
      (convolutionProjection C hC t (placedRightDualObj C hC t g hX q) (placedObj C hC t g X hX) 1 g⁻¹)
      (placedEvaluationBlock C hC t ht g hX q) :=
  singleComponentHom_at C t 1 _

theorem placedTwistedEvaluation_inclusion :
    C.comp
      (convolutionInclusion C hC t (placedRightDualObj C hC t g hX q) (placedObj C hC t g X hX) 1 g⁻¹)
      (placedTwistedEvaluation C hC t ht g hX q 1) = placedEvaluationBlock C hC t ht g hX q := by
  rw [placedTwistedEvaluation_at, ← hC.comp_assoc, convolutionInclusion_projection, hC.id_comp]

theorem placedTwistedCoevaluation_tensor_inclusion (k : t.group) :
    C.comp (convolutionInclusion C hC t (pullbackUnitObj C hC t) (placedObj C hC t g X hX) k 1)
      (convolutionHom C hC t (placedTwistedCoevaluation C hC t g hX q)
        (fun a => C.id (placedObj C hC t g X hX a).val) k) =
      C.comp
        (C.tensorHom (C.tensorHom (placedCoevaluationBlock C hC t g hX q)
          (C.id (placedObj C hC t g X hX (1⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu 1 (1⁻¹ * k)))))
        (convolutionLeftInsertionEven C hC t (placedObj C hC t g X hX)
          (placedRightDualObj C hC t g hX q) (placedObj C hC t g X hX) k 1 g).hom := by
  rw [convolutionInclusion_map]
  dsimp only [twistSummandHom]
  rw [placedTwistedCoevaluation_at]
  let D : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F := tensorRightFunctor D (placedObj C hC t g X hX (1⁻¹ * k)).val ⋙
    tensorRightFunctor D (C.pi.factor (t.nu 1 (1⁻¹ * k)))
  have he := F.map_comp (placedCoevaluationBlock C hC t g hX q)
    (convolutionInclusion C hC t (placedObj C hC t g X hX) (placedRightDualObj C hC t g hX q) 1 g)
  let f₀ := placedCoevaluationBlock C hC t g hX q
  let i₀ := convolutionInclusion C hC t (placedObj C hC t g X hX) (placedRightDualObj C hC t g hX q) 1 g
  let Z₀ := (placedObj C hC t g X hX (1⁻¹ * k)).val
  let P₀ := C.pi.factor (t.nu 1 (1⁻¹ * k))
  change C.tensorHom (C.tensorHom (C.comp f₀ i₀) (C.id Z₀)) (C.id P₀) =
    C.comp (C.tensorHom (C.tensorHom f₀ (C.id Z₀)) (C.id P₀))
      (C.tensorHom (C.tensorHom i₀ (C.id Z₀)) (C.id P₀)) at he
  rw [he, hC.comp_assoc]
  rfl

end RMod.Classification

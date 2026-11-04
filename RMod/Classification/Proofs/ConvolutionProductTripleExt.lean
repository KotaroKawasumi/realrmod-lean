import RMod.Classification.Proofs.ConvolutionProductLeftTransport
import RMod.Classification.Proofs.ConvolutionTripleExt
import RMod.Classification.Proofs.IsoEqualityCancellation

/-!
# Product-indexed triple inclusions detect equality of map families

Cancel the source equality comparison to recover the usual iterated
convolution inclusions. Every output and pair of free summand indices
arises from the three input degrees `b`, `b^-1*a`, and `a^-1*K`.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem hom_ext_of_convolutionProductLeftInsertions (X Y Z : PullbackObj C t)
    (M : t.group → C.Obj)
    (f q : ∀ K, C.Hom (convolutionObj C hC t (convolutionObj C hC t X Y) Z K).val (M K))
    (he : ∀ g h k, C.comp (convolutionProductLeftInsertion C hC t X Y Z g h k) (f ((g * h) * k)) =
      C.comp (convolutionProductLeftInsertion C hC t X Y Z g h k) (q ((g * h) * k))) : f = q := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  have hh : ∀ g h k, C.comp (convolutionLeftInsertionEven C hC t X Y Z ((g * h) * k) (g * h) g).hom
      (f ((g * h) * k)) =
    C.comp (convolutionLeftInsertionEven C hC t X Y Z ((g * h) * k) (g * h) g).hom
      (q ((g * h) * k)) := by
    intro g h k
    let hs : C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z k).val) (C.pi.factor (t.nu (g * h) k)) =
        (convolutionLeftFamily C hC t X Y Z ((g * h) * k) (g * h) g).obj := by
      dsimp [convolutionLeftFamily]
      simp only [inv_mul_cancel_left]
      exact congrArg (fun B => C.tensorObj (C.tensorObj (twistSummand C t X Y g h) B)
        (C.pi.factor (t.nu (g * h) k)))
        (congrArg (fun q => (Z q).val) (inv_mul_cancel_left (g * h) k)).symm
    have hi := he g h k
    rw [convolutionProductLeftInsertion_eq C hC t X Y Z g h k hs, hC.comp_assoc, hC.comp_assoc] at hi
    exact isoData_ofEq_cancel_left A hs _ _ hi
  funext K
  apply hom_ext_of_convolutionLeftInsertions C hC t X Y Z K
  intro a b
  let P : t.group → t.group → Prop := fun a' K' =>
    C.comp (convolutionLeftInsertionEven C hC t X Y Z K' a' b).hom (f K') =
      C.comp (convolutionLeftInsertionEven C hC t X Y Z K' a' b).hom (q K')
  have hK : (b * (b⁻¹ * a)) * (a⁻¹ * K) = K := by rw [mul_inv_cancel_left, mul_inv_cancel_left]
  exact Eq.mp (congrArg₂ P (mul_inv_cancel_left b a) hK) (hh b (b⁻¹ * a) (a⁻¹ * K))

end RMod.Classification

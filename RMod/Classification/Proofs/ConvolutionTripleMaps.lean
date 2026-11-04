import RMod.Classification.Instances.ConvolutionTripleMaps
import RMod.Classification.Proofs.ConvolutionInsertions
import RMod.Classification.Proofs.TensorSquares

/-!
# Threefold summand squares for arbitrary morphisms

The outer inclusion-map equation reduces to the inner one. Tensoring
that square introduces no sign because the inclusions and identity
parity-factor maps are even. This provides both block equations on the
full graded Hom spaces for associator naturality.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  {X X' Y Y' Z Z' : PullbackObj C t}

theorem convolutionLeftInsertion_map (f : PullbackHom C t X X') (g : PullbackHom C t Y Y')
    (h : PullbackHom C t Z Z') (k a b : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t X Y Z k a b).hom
      (convolutionHom C hC t (convolutionHom C hC t f g) h k) =
        C.comp (convolutionLeftBlockHom C hC t f g h k a b)
          (convolutionLeftInsertionEven C hC t X' Y' Z' k a b).hom := by
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a b) (C.id (Z (a⁻¹ * k)).val))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t (convolutionObj C hC t X Y) Z k a)) _ = _
  rw [hC.comp_assoc, convolutionInclusion_map, ← hC.comp_assoc]
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a b) (C.id (Z (a⁻¹ * k)).val))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (C.tensorHom (C.tensorHom (convolutionHom C hC t f g a) (h (a⁻¹ * k)))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))) _ =
    C.comp (convolutionLeftBlockHom C hC t f g h k a b)
      (C.comp (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X' Y' a b)
        (C.id (Z' (a⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k))))) _)
  rw [← hC.comp_assoc]
  apply congrArg (fun m => C.comp m (convolutionInclusion C hC t (convolutionObj C hC t X' Y') Z' k a))
  unfold convolutionLeftBlockHom
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _), hC.comp_id]
  apply congrArg (fun m => C.tensorHom m (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
  exact tensor_square_left hC.toWeaklyPointedSuperfusionLaws _ _ _ _ _
    (convolutionInclusion_grade C hC t X Y a b) (convolutionInclusion_map C hC t f g a b)

theorem convolutionRightInsertion_map (f : PullbackHom C t X X') (g : PullbackHom C t Y Y')
    (h : PullbackHom C t Z Z') (k a b : t.group) :
    C.comp (convolutionRightInsertionEven C hC t X Y Z k a b).hom
      (convolutionHom C hC t f (convolutionHom C hC t g h) k) =
        C.comp (convolutionRightBlockHom C hC t f g h k a b)
          (convolutionRightInsertionEven C hC t X' Y' Z' k a b).hom := by
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val) (convolutionInclusion C hC t Y Z (a⁻¹ * k) b))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t X (convolutionObj C hC t Y Z) k a)) _ = _
  rw [hC.comp_assoc, convolutionInclusion_map, ← hC.comp_assoc]
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val) (convolutionInclusion C hC t Y Z (a⁻¹ * k) b))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (C.tensorHom (C.tensorHom (f a) (convolutionHom C hC t g h (a⁻¹ * k)))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))) _ =
    C.comp (convolutionRightBlockHom C hC t f g h k a b)
      (C.comp (C.tensorHom (C.tensorHom (C.id (X' a).val)
        (convolutionInclusion C hC t Y' Z' (a⁻¹ * k) b)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k))))) _)
  rw [← hC.comp_assoc]
  apply congrArg (fun m => C.comp m (convolutionInclusion C hC t X' (convolutionObj C hC t Y' Z') k a))
  unfold convolutionRightBlockHom
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _), hC.comp_id]
  apply congrArg (fun m => C.tensorHom m (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
  exact tensor_square_right hC.toWeaklyPointedSuperfusionLaws _ _ _ _ _
    (convolutionInclusion_grade C hC t Y' Z' (a⁻¹ * k) b)
    (convolutionInclusion_map C hC t g h (a⁻¹ * k) b)

end RMod.Classification

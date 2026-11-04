import RMod.Classification.Proofs.ConvolutionProductInsertions

/-!
# Outer tensor maps on product-indexed triple inclusions

The inner pair may be mapped by an arbitrary morphism out of its
convolution, rather than by a tensor of two component maps. This is the
summand equation used for unitors and for the intermediate edges of the
coherence diagrams. Evenness of the inclusion removes interchange signs.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionProductLeftInsertion_outer_map {X Y Z M Z' : PullbackObj C t}
    (f : PullbackHom C t (convolutionObj C hC t X Y) M) (h : PullbackHom C t Z Z')
    (a b c : t.group) :
    C.comp (convolutionProductLeftInsertion C hC t X Y Z a b c)
      (convolutionHom C hC t f h ((a * b) * c)) =
        C.comp (C.tensorHom (C.tensorHom
          (C.comp (convolutionProductInclusion C hC t X Y a b) (f (a * b))) (h c))
          (C.id (C.pi.factor (t.nu (a * b) c))))
          (convolutionProductInclusion C hC t M Z' (a * b) c) := by
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (convolutionProductInclusion C hC t X Y a b) (C.id (Z c).val))
      (C.id (C.pi.factor (t.nu (a * b) c))))
    (convolutionProductInclusion C hC t (convolutionObj C hC t X Y) Z (a * b) c)) _ = _
  rw [hC.comp_assoc, convolutionProductInclusion_map, ← hC.comp_assoc]
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (convolutionProductInclusion C hC t X Y a b) (C.id (Z c).val))
      (C.id (C.pi.factor (t.nu (a * b) c))))
    (C.tensorHom (C.tensorHom (f (a * b)) (h c))
      (C.id (C.pi.factor (t.nu (a * b) c))))) _ = _
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.comp_id, interchange_first_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _
      (convolutionProductInclusion_grade C hC t X Y a b), hC.id_comp]

theorem convolutionProductRightInsertion_outer_map {X X' Y Z M : PullbackObj C t}
    (f : PullbackHom C t X X') (h : PullbackHom C t (convolutionObj C hC t Y Z) M)
    (a b c : t.group) :
    C.comp (convolutionProductRightInsertion C hC t X Y Z a b c)
      (convolutionHom C hC t f h (a * (b * c))) =
        C.comp (C.tensorHom (C.tensorHom (f a)
          (C.comp (convolutionProductInclusion C hC t Y Z b c) (h (b * c))))
          (C.id (C.pi.factor (t.nu a (b * c)))))
          (convolutionProductInclusion C hC t X' M a (b * c)) := by
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val) (convolutionProductInclusion C hC t Y Z b c))
      (C.id (C.pi.factor (t.nu a (b * c)))))
    (convolutionProductInclusion C hC t X (convolutionObj C hC t Y Z) a (b * c))) _ = _
  rw [hC.comp_assoc, convolutionProductInclusion_map, ← hC.comp_assoc]
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val) (convolutionProductInclusion C hC t Y Z b c))
      (C.id (C.pi.factor (t.nu a (b * c)))))
    (C.tensorHom (C.tensorHom (f a) (h (b * c)))
      (C.id (C.pi.factor (t.nu a (b * c)))))) _ = _
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.comp_id, interchange_first_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.id_comp]

end RMod.Classification

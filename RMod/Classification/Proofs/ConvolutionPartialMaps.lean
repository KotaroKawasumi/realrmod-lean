import RMod.Classification.Proofs.ConvolutionTripleMaps

/-!
# Mapping an outer tensor product after a threefold inclusion

The inner pair may be mapped by an arbitrary morphism out of its
convolution, rather than by a tensor of two component maps. This is the
summand equation used for unitors and for the intermediate edges of the
coherence diagrams. Evenness of the inclusion removes interchange signs.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionLeftInsertion_outer_map {X Y Z M Z' : PullbackObj C t}
    (f : PullbackHom C t (convolutionObj C hC t X Y) M) (h : PullbackHom C t Z Z')
    (k a b : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t X Y Z k a b).hom
      (convolutionHom C hC t f h k) =
        C.comp (C.tensorHom (C.tensorHom
          (C.comp (convolutionInclusion C hC t X Y a b) (f a)) (h (a⁻¹ * k)))
          (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
          (convolutionInclusion C hC t M Z' k a) := by
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a b) (C.id (Z (a⁻¹ * k)).val))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t (convolutionObj C hC t X Y) Z k a)) _ = _
  rw [hC.comp_assoc, convolutionInclusion_map, ← hC.comp_assoc]
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a b) (C.id (Z (a⁻¹ * k)).val))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (C.tensorHom (C.tensorHom (f a) (h (a⁻¹ * k)))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))) _ = _
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.comp_id, interchange_first_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _
      (convolutionInclusion_grade C hC t X Y a b), hC.id_comp]

theorem convolutionRightInsertion_outer_map {X X' Y Z M : PullbackObj C t}
    (f : PullbackHom C t X X') (h : PullbackHom C t (convolutionObj C hC t Y Z) M)
    (k a b : t.group) :
    C.comp (convolutionRightInsertionEven C hC t X Y Z k a b).hom
      (convolutionHom C hC t f h k) =
        C.comp (C.tensorHom (C.tensorHom (f a)
          (C.comp (convolutionInclusion C hC t Y Z (a⁻¹ * k) b) (h (a⁻¹ * k))))
          (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
          (convolutionInclusion C hC t X' M k a) := by
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val) (convolutionInclusion C hC t Y Z (a⁻¹ * k) b))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t X (convolutionObj C hC t Y Z) k a)) _ = _
  rw [hC.comp_assoc, convolutionInclusion_map, ← hC.comp_assoc]
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val) (convolutionInclusion C hC t Y Z (a⁻¹ * k) b))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (C.tensorHom (C.tensorHom (f a) (h (a⁻¹ * k)))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))) _ = _
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.comp_id, interchange_first_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.id_comp]

end RMod.Classification

import RMod.Classification.Instances.ConvolutionBiproduct
import RMod.Classification.Proofs.PullbackObjects
import RMod.Classification.Proofs.ZeroObjects

/-!
# The support of convolution with the unit family

Tensoring a zero coordinate gives a zero object. Thus the left unit
convolution has only the group-identity summand, and the right unit
convolution in degree k has only the k-th summand.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

theorem even_isZero_of_id_eq_zero (C : WeaklyPointedSuperfusion.{0, 0})
    (X : C.data.Obj) (hX : C.data.id X = C.data.zero) :
    IsZero (evenObj ℝ (LinearCategory C) X) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply WideSubcategory.hom_ext
  exact hX

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem pullbackUnit_id_zero (g : t.group) (hg : g ≠ 1) :
    C.id (pullbackUnitObj C hC t g).val = C.zero := by
  unfold pullbackUnitObj
  rw [supportedObj_ne_one C hC t _ _ g hg]
  exact pullbackZero_id C hC t g

theorem convolutionUnitLeft_isZero (X : PullbackObj C t) (k g : t.group) (hg : g ≠ 1) :
    IsZero (convolutionEvenFamily C hC t (pullbackUnitObj C hC t) X k g) := by
  apply even_isZero_of_id_eq_zero
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (twistSummand C t (pullbackUnitObj C hC t) X g (g⁻¹ * k))
  exact tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
    (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws (pullbackUnit_id_zero C hC t g hg) _) _

theorem convolutionUnitRight_isZero (X : PullbackObj C t) (k g : t.group) (hg : g ≠ k) :
    IsZero (convolutionEvenFamily C hC t X (pullbackUnitObj C hC t) k g) := by
  have hn : g⁻¹ * k ≠ 1 := by
    intro he
    exact hg (inv_mul_eq_one.mp he)
  apply even_isZero_of_id_eq_zero
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (twistSummand C t X (pullbackUnitObj C hC t) g (g⁻¹ * k))
  exact tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
    (tensor_id_zero_right hC.toWeaklyPointedSuperfusionLaws _
      (pullbackUnit_id_zero C hC t (g⁻¹ * k) hn)) _

end RMod.Classification

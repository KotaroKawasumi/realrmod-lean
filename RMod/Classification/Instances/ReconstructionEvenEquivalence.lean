import RMod.Classification.Proofs.ReconstructionUnderlyingEquivalence
import RMod.Classification.Instances.PullbackSupercategory
import RMod.Classification.Instances.LinearMonoidal

/-!
# Restricting the actual reconstruction equivalence to even morphisms

The underlying equivalence and its specified unit and counit are already
graded. Restriction therefore gives an ordinary equivalence of the even
categories before any scalar coherence in the model has been proved.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionEvenForward :
    EvenSubcategory ℝ (LinearCategory A.toWeaklyPointedSuperfusion) ⥤
      EvenSubcategory ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC)) where
  obj X := evenObj ℝ _ ((reconstructionUnderlyingEquivalence A C hC).functor.obj X.obj)
  map f := ⟨(reconstructionUnderlyingEquivalence A C hC).functor.map f.hom,
    reconstructionUnderlying_forward_grade A C hC f.hom f.property⟩
  map_id X := WideSubcategory.hom_ext _ ((reconstructionUnderlyingEquivalence A C hC).functor.map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _
    ((reconstructionUnderlyingEquivalence A C hC).functor.map_comp f.hom g.hom)

noncomputable def reconstructionEvenBackward :
    EvenSubcategory ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC)) ⥤
      EvenSubcategory ℝ (LinearCategory A.toWeaklyPointedSuperfusion) where
  obj X := evenObj ℝ _ ((reconstructionUnderlyingEquivalence A C hC).inverse.obj X.obj)
  map f := ⟨(reconstructionUnderlyingEquivalence A C hC).inverse.map f.hom,
    reconstructionUnderlying_backward_grade A C hC f.hom f.property⟩
  map_id X := WideSubcategory.hom_ext _ ((reconstructionUnderlyingEquivalence A C hC).inverse.map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _
    ((reconstructionUnderlyingEquivalence A C hC).inverse.map_comp f.hom g.hom)

noncomputable def reconstructionEvenEquivalence :
    EvenSubcategory ℝ (LinearCategory A.toWeaklyPointedSuperfusion) ≌
      EvenSubcategory ℝ (PullbackCategory C.data hC (reconstructionTwistData A C hC)) :=
  CategoryTheory.Equivalence.mk (reconstructionEvenForward A C hC) (reconstructionEvenBackward A C hC)
    (NatIso.ofComponents
      (fun X =>
        { hom := ⟨(reconstructionUnderlyingEquivalence A C hC).unitIso.hom.app X.obj,
            reconstructionUnderlying_unit_hom_even A C hC X.obj⟩
          inv := ⟨(reconstructionUnderlyingEquivalence A C hC).unitIso.inv.app X.obj,
            reconstructionUnderlying_unit_inv_even A C hC X.obj⟩
          hom_inv_id := WideSubcategory.hom_ext _
            ((reconstructionUnderlyingEquivalence A C hC).unitIso.hom_inv_id_app X.obj)
          inv_hom_id := WideSubcategory.hom_ext _
            ((reconstructionUnderlyingEquivalence A C hC).unitIso.inv_hom_id_app X.obj) })
      (fun f => WideSubcategory.hom_ext _
        ((reconstructionUnderlyingEquivalence A C hC).unitIso.hom.naturality f.hom)))
    (NatIso.ofComponents
      (fun X =>
        { hom := ⟨(reconstructionUnderlyingEquivalence A C hC).counitIso.hom.app X.obj,
            reconstructionUnderlying_counit_hom_even A C hC X.obj⟩
          inv := ⟨(reconstructionUnderlyingEquivalence A C hC).counitIso.inv.app X.obj,
            reconstructionUnderlying_counit_inv_even A C hC X.obj⟩
          hom_inv_id := WideSubcategory.hom_ext _
            ((reconstructionUnderlyingEquivalence A C hC).counitIso.hom_inv_id_app X.obj)
          inv_hom_id := WideSubcategory.hom_ext _
            ((reconstructionUnderlyingEquivalence A C hC).counitIso.inv_hom_id_app X.obj) })
      (fun f => WideSubcategory.hom_ext _
        ((reconstructionUnderlyingEquivalence A C hC).counitIso.hom.naturality f.hom)))

end RMod.Classification

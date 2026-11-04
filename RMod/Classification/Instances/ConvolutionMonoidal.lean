import RMod.Classification.Instances.PullbackSupercategory
import RMod.Classification.Proofs.PullbackStructuralLaws
import RMod.Classification.Proofs.ConvolutionMaps
import RMod.Classification.Proofs.ConvolutionTriangle
import RMod.Classification.Proofs.ConvolutionPentagon

/-!
# The monoidal supercategory carried by the constructed convolution

All operations are those of the advertised pullback Data, and every
coherence proof has already been established for those operations. This
adapter uses the existing category interfaces before proving rigidity;
no unproved fusion laws are bundled in order to obtain these instances.
-/

set_option autoImplicit false

namespace RMod.Classification

/-- Include the admissibility proof in the instance head, so the actual
associator and its proved coherence are determined by the category type. -/
@[implicit_reducible]
def ConvolutionCategory (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)
    (t : TwistData) (_ht : TwistLaws t) : Type := PullbackCategory C hC t

namespace ConvolutionCategory

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

instance category : Category (ConvolutionCategory C hC t ht) := PullbackCategory.category C hC t
instance preadditive : Preadditive (ConvolutionCategory C hC t ht) := PullbackCategory.preadditive C hC t
instance linear : Linear ℝ (ConvolutionCategory C hC t ht) := PullbackCategory.linear C hC t
instance supercategory : Superfusion.Category.Supercategory ℝ (ConvolutionCategory C hC t ht) :=
  PullbackCategory.supercategory C hC t

noncomputable instance monoidalStruct : MonoidalCategoryStruct (ConvolutionCategory C hC t ht) where
  tensorObj := (twistedPullbackData C hC t ht).tensorObj
  tensorHom := (twistedPullbackData C hC t ht).tensorHom
  whiskerLeft := (twistedPullbackData C hC t ht).whiskerLeft
  whiskerRight := (twistedPullbackData C hC t ht).whiskerRight
  tensorUnit := (twistedPullbackData C hC t ht).tensorUnit
  associator X Y Z :=
    { hom := (twistedPullbackData C hC t ht).associatorHom X Y Z
      inv := (twistedPullbackData C hC t ht).associatorInv X Y Z
      hom_inv_id := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).hom_inv
      inv_hom_id := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).inv_hom }
  leftUnitor X :=
    { hom := (twistedPullbackData C hC t ht).leftUnitorHom X
      inv := (twistedPullbackData C hC t ht).leftUnitorInv X
      hom_inv_id := (twistedPullbackLeftUnitor_evenIso C hC t ht X).hom_inv
      inv_hom_id := (twistedPullbackLeftUnitor_evenIso C hC t ht X).inv_hom }
  rightUnitor X :=
    { hom := (twistedPullbackData C hC t ht).rightUnitorHom X
      inv := (twistedPullbackData C hC t ht).rightUnitorInv X
      hom_inv_id := (twistedPullbackRightUnitor_evenIso C hC t ht X).hom_inv
      inv_hom_id := (twistedPullbackRightUnitor_evenIso C hC t ht X).inv_hom }

instance monoidalSupercategory :
    Superfusion.Category.MonoidalSupercategory ℝ (ConvolutionCategory C hC t ht) where
  tensorHom_mem f g hf hg := convolutionHom_grade C hC t f g _ _ hf hg
  tensor_id := convolutionHom_id C hC t
  tensor_add_left := convolutionHom_add_left C hC t
  tensor_add_right := convolutionHom_add_right C hC t
  tensor_smul_left := convolutionHom_smul_left C hC t
  tensor_smul_right := convolutionHom_smul_right C hC t
  super_interchange f g h k hg hh := convolutionHom_interchange C hC t f g h k _ _ hg hh
  whiskerLeft_eq := fun _ {_ _} _ => rfl
  whiskerRight_eq := fun {_ _} _ _ => rfl
  associator_hom_mem X Y Z := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).hom_even
  associator_inv_mem X Y Z := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).inv_even
  associator_naturality := twistedPullback_associator_naturality C hC t ht
  leftUnitor_hom_mem X := (twistedPullbackLeftUnitor_evenIso C hC t ht X).hom_even
  leftUnitor_inv_mem X := (twistedPullbackLeftUnitor_evenIso C hC t ht X).inv_even
  leftUnitor_naturality := twistedPullback_left_unitor_naturality C hC t ht
  rightUnitor_hom_mem X := (twistedPullbackRightUnitor_evenIso C hC t ht X).hom_even
  rightUnitor_inv_mem X := (twistedPullbackRightUnitor_evenIso C hC t ht X).inv_even
  rightUnitor_naturality := twistedPullback_right_unitor_naturality C hC t ht
  pentagon W X Y Z := by
    funext k
    exact (hC.comp_assoc _ _ _).symm.trans (convolution_pentagon C hC t ht W X Y Z k)
  triangle := twistedPullback_triangle C hC t ht

end ConvolutionCategory
end RMod.Classification

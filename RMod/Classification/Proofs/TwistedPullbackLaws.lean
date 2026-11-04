import RMod.Classification.Proofs.PullbackLeftDuals
import RMod.Classification.Proofs.PullbackWeaklyPointed
import RMod.Classification.Proofs.PullbackOrbits
import RMod.Classification.Proofs.PullbackLinearLaws

/-!
# Fusion and parity laws for the specified abstract pullback data

All operations have already been constructed from the abstract reference
category. Coordinatewise linear laws, convolution coherence, finite
semisimplicity, both dualities and weak pointedness are now assembled as
laws on precisely those operations. The specified odd unit comparison
then completes the public Pi-superfusion construction.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullbackBaseLaws :
    WeaklyPointedSuperfusionLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData where
  comp_id f := funext fun k => hC.comp_id (f k)
  id_comp f := funext fun k => hC.id_comp (f k)
  comp_assoc f g h := funext fun k => hC.comp_assoc (f k) (g k) (h k)
  add_assoc f g h := funext fun k => hC.add_assoc (f k) (g k) (h k)
  zero_add f := funext fun k => hC.zero_add (f k)
  add_zero f := funext fun k => hC.add_zero (f k)
  add_comm f g := funext fun k => hC.add_comm (f k) (g k)
  neg_add f := funext fun k => hC.neg_add (f k)
  one_smul f := funext fun k => hC.one_smul (f k)
  mul_smul a b f := funext fun k => hC.mul_smul a b (f k)
  add_smul a b f := funext fun k => hC.add_smul a b (f k)
  smul_add a f g := funext fun k => hC.smul_add a (f k) (g k)
  zero_smul f := funext fun k => hC.zero_smul (f k)
  smul_zero a := funext fun _ => hC.smul_zero a
  add_comp f g h := funext fun k => hC.add_comp (f k) (g k) (h k)
  comp_add f g h := funext fun k => hC.comp_add (f k) (g k) (h k)
  smul_comp a f g := funext fun k => hC.smul_comp a (f k) (g k)
  comp_smul a f g := funext fun k => hC.comp_smul a (f k) (g k)
  grade_zero X Y a k := hC.grade_zero (X k).val (Y k).val a
  grade_add f g hf hg k := hC.grade_add (f k) (g k) (hf k) (hg k)
  grade_neg f hf k := hC.grade_neg (f k) (hf k)
  grade_smul a f hf k := hC.grade_smul a (f k) (hf k)
  grade_decomposition := twistedPullback_grade_decomposition C hC t ht
  grade_disjoint := twistedPullback_grade_disjoint C hC t ht
  id_even X k := hC.id_even (X k).val
  comp_grade f g hf hg k := hC.comp_grade (f k) (g k) (hf k) (hg k)
  tensor_grade f g hf hg := convolutionHom_grade C hC t f g _ _ hf hg
  tensor_id := convolutionHom_id C hC t
  tensor_add_left := convolutionHom_add_left C hC t
  tensor_add_right := convolutionHom_add_right C hC t
  tensor_smul_left := convolutionHom_smul_left C hC t
  tensor_smul_right := convolutionHom_smul_right C hC t
  super_interchange f g h k hg hh := convolutionHom_interchange C hC t f g h k _ _ hg hh
  associator_hom_inv X Y Z := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).hom_inv
  associator_inv_hom X Y Z := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).inv_hom
  associator_hom_even X Y Z := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).hom_even
  associator_inv_even X Y Z := (twistedPullbackAssociator_evenIso C hC t ht X Y Z).inv_even
  associator_naturality := twistedPullback_associator_naturality C hC t ht
  left_unitor_hom_inv X := (twistedPullbackLeftUnitor_evenIso C hC t ht X).hom_inv
  left_unitor_inv_hom X := (twistedPullbackLeftUnitor_evenIso C hC t ht X).inv_hom
  left_unitor_hom_even X := (twistedPullbackLeftUnitor_evenIso C hC t ht X).hom_even
  left_unitor_inv_even X := (twistedPullbackLeftUnitor_evenIso C hC t ht X).inv_even
  left_unitor_naturality := twistedPullback_left_unitor_naturality C hC t ht
  right_unitor_hom_inv X := (twistedPullbackRightUnitor_evenIso C hC t ht X).hom_inv
  right_unitor_inv_hom X := (twistedPullbackRightUnitor_evenIso C hC t ht X).inv_hom
  right_unitor_hom_even X := (twistedPullbackRightUnitor_evenIso C hC t ht X).hom_even
  right_unitor_inv_even X := (twistedPullbackRightUnitor_evenIso C hC t ht X).inv_even
  right_unitor_naturality := twistedPullback_right_unitor_naturality C hC t ht
  pentagon := twistedPullback_pentagon C hC t ht
  triangle := twistedPullback_triangle C hC t ht
  has_finite_biproducts := twistedPullback_hasFiniteBiproduct C hC t ht
  semisimple := twistedPullback_semisimple C hC t ht
  graded_schur := twistedPullback_graded_schur C hC t ht
  finite_dimensional_hom := twistedPullback_hasFiniteBasis C hC t ht
  finite_simple_representatives := twistedPullback_finite_simple_representatives C hC t ht
  simple_unit := twistedPullback_simple_unit C hC t ht
  unit_end_scalar_injective := twistedPullback_unit_end_scalar_injective C hC t ht
  unit_end_scalar_surjective := twistedPullback_unit_end_scalar_surjective C hC t ht
  has_right_dual := twistedPullback_has_right_dual C hC t ht
  has_left_dual := twistedPullback_has_left_dual C hC t ht
  weakly_pointed := twistedPullback_weakly_pointed C hC t ht

theorem twistedPullbackLaws : PiSuperfusionLaws (twistedPullbackData C hC t ht) where
  toWeaklyPointedSuperfusionLaws := twistedPullbackBaseLaws C hC t ht
  pi := twistedPullbackPiLaws C hC t ht

end RMod.Classification

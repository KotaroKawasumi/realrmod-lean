import RMod.BrundanEllis.StackingBiproductInjection
import RMod.BrundanEllis.StackingReindexFaithful
import RMod.Classification.Instances.ConvolutionInsertions
import RMod.Classification.Proofs.TensorCalculus

/-! Restricting a supported convolution along an injective group map
removes only zero summands. This constructs its actual tensor comparison
using the selected convolution inclusions and projections. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (f : t.data.group →* s.data.group) (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
  (hν : ∀ g h, t.data.nu g h = s.data.nu (f g) (f h))
  (X Y : PullbackObj C s.data)

include hν in
/-- On raw reference objects, the surviving summands agree. -/
theorem coordinateRestriction_summandObj (k g : t.data.group) :
    twistSummand C t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) g (g⁻¹ * k) =
    twistSummand C s.data X Y (f g) ((f g)⁻¹ * f k) := by
  have hi : f (g⁻¹ * k) = (f g)⁻¹ * f k := by rw [map_mul, map_inv]
  have hy := congrArg (fun j => (Y j).val) hi
  have hn := (hν g (g⁻¹ * k)).trans (congrArg (s.data.nu (f g)) hi)
  exact congrArg₂ (fun A p =>
    C.tensorObj (C.tensorObj (X (f g)).val A) (C.pi.factor p)) hy hn

include hν in
/-- The surviving summands have exactly the restricted parity cochain. -/
theorem coordinateRestriction_summand (k g : t.data.group) :
    convolutionEvenFamily C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) k g =
    convolutionEvenFamily C hC s.data X Y (f k) (f g) :=
  congrArg (referenceEvenObj C hC)
    (coordinateRestriction_summandObj C hC s t f hρ hν X Y k g)

/-- Outside the image, the first tensor factor makes the summand zero. -/
theorem convolutionEvenFamily_zero_off_image
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero)
    (k b : s.data.group) (hb : ¬ ∃ g, f g = b) :
    IsZero (convolutionEvenFamily C hC s.data X Y k b) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply WideSubcategory.hom_ext
  exact tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
    (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws (hX b hb) _) _

/-- The tensor comparison is the canonical inclusion of the surviving summands. -/
def coordinateRestrictionTensorIso (hf : Function.Injective f)
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero) (k : t.data.group) :
    referenceEvenObj C hC (convolutionObj C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) k).val ≅
    referenceEvenObj C hC (convolutionObj C hC s.data X Y (f k)).val :=
  convolutionEvenIso C hC t.data
    ((coordinateRestrictionData C hC s t f hρ).obj X)
    ((coordinateRestrictionData C hC s t f hρ).obj Y) k ≪≫
  biproduct.mapIso (fun g => eqToIso (coordinateRestriction_summand C hC s t f hρ hν X Y k g)) ≪≫
  RMod.BrundanEllis.Stacking.biproductInjectionIso
    (convolutionEvenFamily C hC s.data X Y (f k)) ⟨f, hf⟩
    (fun b hb => convolutionEvenFamily_zero_off_image C hC s t f X Y hX (f k) b hb) ≪≫
  (convolutionEvenIso C hC s.data X Y (f k)).symm

/-- On each surviving summand the tensor comparison is the specified inclusion. -/
theorem coordinateRestrictionTensorIso_inclusion (hf : Function.Injective f)
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero) (k g : t.data.group) :
    convolutionInclusionEven C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) k g ≫
      (coordinateRestrictionTensorIso C hC s t f hρ hν X Y hf hX k).hom =
    eqToHom (coordinateRestriction_summand C hC s t f hρ hν X Y k g) ≫
      convolutionInclusionEven C hC s.data X Y (f k) (f g) := by
  simp only [coordinateRestrictionTensorIso, convolutionInclusionEven,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    biproduct.mapIso_hom, biproduct.ι_map_assoc,
    eqToIso.hom]
  erw [RMod.BrundanEllis.Stacking.biproductInjectionIso_inclusion_assoc
    (convolutionEvenFamily C hC s.data X Y (f k)) ⟨f, hf⟩
    (fun b hb => convolutionEvenFamily_zero_off_image C hC s t f X Y hX (f k) b hb) g]
  rfl

end RMod.Classification

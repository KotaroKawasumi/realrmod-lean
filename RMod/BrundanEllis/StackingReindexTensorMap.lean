import RMod.BrundanEllis.StackingReindexTensorNaturality

/-! The same coordinate tensor comparison exists before imposing support.
It is defined by its summand inclusions; support is only needed for invertibility. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (f : t.data.group →* s.data.group) (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
  (hν : ∀ g h, t.data.nu g h = s.data.nu (f g) (f h))

/-- The inclusion of all restricted summands into the original convolution. -/
def coordinateRestrictionTensorMap (X Y : PullbackObj C s.data) (k : t.data.group) :
    referenceEvenObj C hC (convolutionObj C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) k).val ⟶
    referenceEvenObj C hC (convolutionObj C hC s.data X Y (f k)).val :=
  (convolutionEvenIso C hC t.data
    ((coordinateRestrictionData C hC s t f hρ).obj X)
    ((coordinateRestrictionData C hC s t f hρ).obj Y) k).hom ≫
  biproduct.desc (fun g =>
    eqToHom (coordinateRestriction_summand C hC s t f hρ hν X Y k g) ≫
      convolutionInclusionEven C hC s.data X Y (f k) (f g))

/-- The comparison retains each specified inclusion. -/
theorem coordinateRestrictionTensorMap_inclusion (X Y : PullbackObj C s.data)
    (k g : t.data.group) :
    convolutionInclusionEven C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) k g ≫
      coordinateRestrictionTensorMap C hC s t f hρ hν X Y k =
    eqToHom (coordinateRestriction_summand C hC s t f hρ hν X Y k g) ≫
      convolutionInclusionEven C hC s.data X Y (f k) (f g) := by
  simp only [coordinateRestrictionTensorMap, convolutionInclusionEven,
    Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_desc]

/-- Retain the full graded map, rather than only the even-category packaging. -/
def coordinateRestrictionTensorHom (X Y : PullbackObj C s.data) :
    PullbackHom C t.data
      (convolutionObj C hC t.data
        ((coordinateRestrictionData C hC s t f hρ).obj X)
        ((coordinateRestrictionData C hC s t f hρ).obj Y))
      ((coordinateRestrictionData C hC s t f hρ).obj (convolutionObj C hC s.data X Y)) :=
  fun k => (coordinateRestrictionTensorMap C hC s t f hρ hν X Y k).hom

theorem coordinateRestrictionTensorHom_inclusion (X Y : PullbackObj C s.data)
    (k g : t.data.group) :
    C.comp (convolutionInclusion C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) k g)
      (coordinateRestrictionTensorHom C hC s t f hρ hν X Y k) =
    C.comp (eqToHom (coordinateRestriction_summand C hC s t f hρ hν X Y k g)).hom
      (convolutionInclusion C hC s.data X Y (f k) (f g)) :=
  congrArg (fun u => u.hom)
    (coordinateRestrictionTensorMap_inclusion C hC s t f hρ hν X Y k g)

/-- On supported objects the comparison is exactly the previously constructed isomorphism. -/
theorem coordinateRestrictionTensorMap_eq_iso (X Y : PullbackObj C s.data)
    (hf : Function.Injective f)
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero) (k : t.data.group) :
    coordinateRestrictionTensorMap C hC s t f hρ hν X Y k =
      (coordinateRestrictionTensorIso C hC s t f hρ hν X Y hf hX k).hom := by
  apply WideSubcategory.hom_ext
  apply hom_ext_of_convolutionInclusions C hC t.data
    ((coordinateRestrictionData C hC s t f hρ).obj X)
    ((coordinateRestrictionData C hC s t f hρ).obj Y) k
  intro g
  exact (coordinateRestrictionTensorHom_inclusion C hC s t f hρ hν X Y k g).trans
    (coordinateRestrictionTensorIso_raw_inclusion C hC s t f hρ hν X Y hf hX k g).symm

/-- Naturality of the comparison does not require support or injectivity. -/
theorem coordinateRestrictionTensorHom_naturality
    {X X' Y Y' : PullbackObj C s.data}
    (u : PullbackHom C s.data X X') (v : PullbackHom C s.data Y Y') (k : t.data.group) :
    C.comp (convolutionHom C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).map u)
      ((coordinateRestrictionData C hC s t f hρ).map v) k)
      (coordinateRestrictionTensorHom C hC s t f hρ hν X' Y' k) =
    C.comp (coordinateRestrictionTensorHom C hC s t f hρ hν X Y k)
      (convolutionHom C hC s.data u v (f k)) := by
  apply hom_ext_of_convolutionInclusions C hC t.data
    ((coordinateRestrictionData C hC s t f hρ).obj X)
    ((coordinateRestrictionData C hC s t f hρ).obj Y) k
  intro g
  rw [← hC.comp_assoc, convolutionInclusion_map, hC.comp_assoc,
    coordinateRestrictionTensorHom_inclusion, ← hC.comp_assoc,
    coordinateRestriction_summand_natural C hC s t f hρ hν, hC.comp_assoc,
    ← convolutionInclusion_map, ← hC.comp_assoc,
    ← coordinateRestrictionTensorHom_inclusion, hC.comp_assoc]

end RMod.Classification

import RMod.BrundanEllis.StackingReindexTensorMap
import RMod.Classification.Proofs.ConvolutionPartialMaps

/-! Transport of the left and right threefold convolution summands.
These lemmas concern the specified comparison maps, before the associator law. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)

include hC in
/-- Move equality transport past an inclusion in the first tensor factor. -/
theorem tensorFactor_left_transport {A A' B V V' : C.Obj}
    (hA : A = A') (hV : V = V') (p q : ZMod 2) (hp : p = q) (m : C.Hom A' B)
    (hL : C.tensorObj (C.tensorObj A V) (C.pi.factor p) =
      C.tensorObj (C.tensorObj A' V') (C.pi.factor q))
    (hR : C.tensorObj (C.tensorObj B V) (C.pi.factor p) =
      C.tensorObj (C.tensorObj B V') (C.pi.factor q)) :
    C.comp (C.tensorHom (C.tensorHom
      (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hA).hom m) (C.id V))
      (C.id (C.pi.factor p))) (IsoData.ofEq C.toWeaklyPointedSuperfusionData hR).hom =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hL).hom
      (C.tensorHom (C.tensorHom m (C.id V')) (C.id (C.pi.factor q))) := by
  subst A'
  subst V'
  subst q
  change C.comp (C.tensorHom (C.tensorHom (C.comp (C.id A) m) (C.id V))
    (C.id (C.pi.factor p))) (C.id _) =
    C.comp (C.id _) (C.tensorHom (C.tensorHom m (C.id V)) (C.id (C.pi.factor p)))
  rw [hC.id_comp, hC.comp_id, hC.id_comp]

include hC in
/-- Move a change of output index past an inclusion in the second tensor factor. -/
theorem tensorFactor_right_transport {I : Type} (U A : C.Obj)
    (V W : I → C.Obj) (v : ∀ i, C.Hom (V i) (W i))
    (i j : I) (hi : i = j) (hA : A = V i) (p q : ZMod 2) (hp : p = q)
    (hL : C.tensorObj (C.tensorObj U A) (C.pi.factor p) =
      C.tensorObj (C.tensorObj U (V j)) (C.pi.factor q))
    (hR : C.tensorObj (C.tensorObj U (W i)) (C.pi.factor p) =
      C.tensorObj (C.tensorObj U (W j)) (C.pi.factor q)) :
    C.comp (C.tensorHom (C.tensorHom (C.id U)
      (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hA).hom (v i)))
      (C.id (C.pi.factor p))) (IsoData.ofEq C.toWeaklyPointedSuperfusionData hR).hom =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hL).hom
      (C.tensorHom (C.tensorHom (C.id U) (v j)) (C.id (C.pi.factor q))) := by
  subst j
  subst q
  subst A
  change C.comp (C.tensorHom (C.tensorHom (C.id U) (C.comp (C.id _) (v i)))
    (C.id (C.pi.factor p))) (C.id _) =
    C.comp (C.id _) (C.tensorHom (C.tensorHom (C.id U) (v i)) (C.id (C.pi.factor p)))
  rw [hC.id_comp, hC.comp_id, hC.id_comp]

variable (s t : Twist) (f : t.data.group →* s.data.group)
  (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
  (hν : ∀ g h, t.data.nu g h = s.data.nu (f g) (f h))
  (X Y Z : PullbackObj C s.data)

include hν in
/-- The left-associated threefold summands agree under the group map. -/
theorem coordinateRestriction_leftFamily (k a g : t.data.group) :
    (convolutionLeftFamily C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k a g).obj =
    (convolutionLeftFamily C hC s.data X Y Z (f k) (f a) (f g)).obj := by
  have hi : f (a⁻¹ * k) = (f a)⁻¹ * f k := by rw [map_mul, map_inv]
  exact congrArg₂ C.tensorObj
    (congrArg₂ C.tensorObj
      (coordinateRestriction_summandObj C hC s t f hρ hν X Y a g)
      (congrArg (fun j => (Z j).val) hi))
    (congrArg C.pi.factor ((hν a (a⁻¹ * k)).trans (congrArg (s.data.nu (f a)) hi)))

include hν in
/-- The right-associated summands also retain their actual complementary indices. -/
theorem coordinateRestriction_rightFamily (k g h : t.data.group) :
    (convolutionRightFamily C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k g h).obj =
    (convolutionRightFamily C hC s.data X Y Z (f k) (f g) (f h)).obj := by
  have hi : f (g⁻¹ * k) = (f g)⁻¹ * f k := by rw [map_mul, map_inv]
  have hin := (coordinateRestriction_summandObj C hC s t f hρ hν Y Z (g⁻¹ * k) h).trans
    (congrArg (fun j => twistSummand C s.data Y Z (f h) ((f h)⁻¹ * j)) hi)
  exact congrArg₂ C.tensorObj (congrArg (C.tensorObj (X (f g)).val) hin)
    (congrArg C.pi.factor ((hν g (g⁻¹ * k)).trans (congrArg (s.data.nu (f g)) hi)))

/-- The left iterated comparison sends every triple inclusion to its reindexed inclusion. -/
theorem coordinateRestrictionTensorHom_left_inclusion (k a g : t.data.group) :
    C.comp (C.comp (convolutionLeftInsertionEven C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k a g).hom
      (convolutionHom C hC t.data
        (coordinateRestrictionTensorHom C hC s t f hρ hν X Y)
        (fun j => C.id (Z (f j)).val) k))
      (coordinateRestrictionTensorHom C hC s t f hρ hν (convolutionObj C hC s.data X Y) Z k) =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (coordinateRestriction_leftFamily C hC s t f hρ hν X Y Z k a g)).hom
      (convolutionLeftInsertionEven C hC s.data X Y Z (f k) (f a) (f g)).hom := by
  rw [convolutionLeftInsertion_outer_map, hC.comp_assoc,
    coordinateRestrictionTensorHom_inclusion C hC s t f hρ hν
      (convolutionObj C hC s.data X Y) Z k a, ← hC.comp_assoc,
    coordinateRestrictionTensorHom_inclusion C hC s t f hρ hν X Y a g,
    referenceEven_eqToHom_value C hC
      (coordinateRestriction_summandObj C hC s t f hρ hν X Y a g),
    referenceEven_eqToHom_value C hC
      (coordinateRestriction_summandObj C hC s t f hρ hν
        (convolutionObj C hC s.data X Y) Z k a)]
  change C.comp (C.comp _ _) _ = C.comp _ (C.comp _ _)
  rw [← hC.comp_assoc]
  apply congrArg (fun m => C.comp m
    (convolutionInclusion C hC s.data (convolutionObj C hC s.data X Y) Z (f k) (f a)))
  have hi : f (a⁻¹ * k) = (f a)⁻¹ * f k := by rw [map_mul, map_inv]
  exact tensorFactor_left_transport C hC
    (coordinateRestriction_summandObj C hC s t f hρ hν X Y a g)
    (congrArg (fun j => (Z j).val) hi) _ _
    ((hν a (a⁻¹ * k)).trans (congrArg (s.data.nu (f a)) hi))
    (convolutionInclusion C hC s.data X Y (f a) (f g)) _ _

/-- The right iterated comparison retains the complementary output index as well. -/
theorem coordinateRestrictionTensorHom_right_inclusion (k g h : t.data.group) :
    C.comp (C.comp (convolutionRightInsertionEven C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k g h).hom
      (convolutionHom C hC t.data
        (fun j => C.id (X (f j)).val)
        (coordinateRestrictionTensorHom C hC s t f hρ hν Y Z) k))
      (coordinateRestrictionTensorHom C hC s t f hρ hν X (convolutionObj C hC s.data Y Z) k) =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (coordinateRestriction_rightFamily C hC s t f hρ hν X Y Z k g h)).hom
      (convolutionRightInsertionEven C hC s.data X Y Z (f k) (f g) (f h)).hom := by
  rw [convolutionRightInsertion_outer_map, hC.comp_assoc,
    coordinateRestrictionTensorHom_inclusion C hC s t f hρ hν
      X (convolutionObj C hC s.data Y Z) k g, ← hC.comp_assoc,
    coordinateRestrictionTensorHom_inclusion C hC s t f hρ hν Y Z (g⁻¹ * k) h,
    referenceEven_eqToHom_value C hC
      (coordinateRestriction_summandObj C hC s t f hρ hν Y Z (g⁻¹ * k) h),
    referenceEven_eqToHom_value C hC
      (coordinateRestriction_summandObj C hC s t f hρ hν
        X (convolutionObj C hC s.data Y Z) k g)]
  change C.comp (C.comp _ _) _ = C.comp _ (C.comp _ _)
  rw [← hC.comp_assoc]
  apply congrArg (fun m => C.comp m
    (convolutionInclusion C hC s.data X (convolutionObj C hC s.data Y Z) (f k) (f g)))
  have hi : f (g⁻¹ * k) = (f g)⁻¹ * f k := by rw [map_mul, map_inv]
  exact tensorFactor_right_transport C hC (X (f g)).val _
    (fun j => twistSummand C s.data Y Z (f h) ((f h)⁻¹ * j))
    (fun j => (convolutionObj C hC s.data Y Z j).val)
    (fun j => convolutionInclusion C hC s.data Y Z j (f h)) _ _ hi
    (coordinateRestriction_summandObj C hC s t f hρ hν Y Z (g⁻¹ * k) h) _ _
    ((hν g (g⁻¹ * k)).trans (congrArg (s.data.nu (f g)) hi)) _ _

end RMod.Classification

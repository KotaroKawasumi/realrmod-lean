import RMod.BrundanEllis.StackingReindexFunctor
import RMod.Classification.Proofs.ZeroObjects

/-! Restriction is fully faithful on families supported on an injective
label map. Its inverse on homogeneous maps is extension by zero. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (f : t.data.group →* s.data.group) (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
  (X Y : PullbackObj C s.data)

/-- Extend a map between the restricted families by zero outside the image. -/
def coordinateHomExtension
    (u : PullbackHom C t.data ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)) : PullbackHom C s.data X Y := by
  classical
  intro k
  exact if h : ∃ g, f g = k then h.choose_spec ▸ u h.choose else C.zero

private theorem transport_coordinate (hf : Function.Injective f)
    (u : (g : t.data.group) → C.Hom (X (f g)).val (Y (f g)).val)
    (i j : t.data.group) (h : f i = f j) : (h ▸ u i) = u j := by
  obtain rfl := hf h
  rfl

/-- The extension recovers every original coordinate on the injective image. -/
theorem coordinateHomExtension_at (hf : Function.Injective f)
    (u : PullbackHom C t.data ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)) (g : t.data.group) :
    coordinateHomExtension C hC s t f hρ X Y u (f g) = u g := by
  classical
  simp only [coordinateHomExtension, dif_pos (show ∃ j, f j = f g from ⟨g, rfl⟩)]
  exact transport_coordinate C s t f X Y hf u _ g _

/-- Zero extension preserves each homogeneous degree. -/
theorem coordinateHomExtension_grade {a : ZMod 2}
    (u : PullbackHom C t.data ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y))
    (hu : ∀ g, C.IsHomogeneous a (u g)) :
    ∀ k, C.IsHomogeneous a (coordinateHomExtension C hC s t f hρ X Y u k) := by
  classical
  intro k
  dsimp only [coordinateHomExtension]
  split_ifs with h
  · have transport_grade (i j : s.data.group) (e : i = j)
        (v : C.Hom (X i).val (Y i).val) (hv : C.IsHomogeneous a v) :
        C.IsHomogeneous a (e ▸ v) := by
      cases e
      exact hv
    exact transport_grade _ _ h.choose_spec _ (hu h.choose)
  · exact hC.grade_zero _ _ _

/-- Maps out of a supported family are determined on the image labels. -/
theorem coordinateRestriction_injective
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero) :
    Function.Injective (fun u : PullbackHom C s.data X Y =>
      (coordinateRestrictionData C hC s t f hρ).map u) := by
  intro u v huv
  funext k
  by_cases hk : ∃ g, f g = k
  · obtain ⟨g, rfl⟩ := hk
    exact congrFun huv g
  · exact (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws (hX k hk) (u k)).trans
      (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws (hX k hk) (v k)).symm

/-- On supported sources the restriction is bijective in every homogeneous degree. -/
theorem coordinateRestriction_graded_bijective (hf : Function.Injective f)
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero) (a : ZMod 2) :
    Function.Bijective (fun u : {u : PullbackHom C s.data X Y // ∀ k, C.IsHomogeneous a (u k)} =>
      (⟨(coordinateRestrictionData C hC s t f hρ).map u.val, fun g => u.property (f g)⟩ :
        {v : PullbackHom C t.data ((coordinateRestrictionData C hC s t f hρ).obj X)
          ((coordinateRestrictionData C hC s t f hρ).obj Y) // ∀ g, C.IsHomogeneous a (v g)})) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    exact coordinateRestriction_injective C hC s t f hρ X Y hX
      (congrArg Subtype.val huv)
  · intro v
    refine ⟨⟨coordinateHomExtension C hC s t f hρ X Y v.val,
      coordinateHomExtension_grade C hC s t f hρ X Y v.val v.property⟩, ?_⟩
    apply Subtype.ext
    funext g
    exact coordinateHomExtension_at C hC s t f hρ X Y hf v.val g

end RMod.Classification

namespace RMod.BrundanEllis.Stacking
/-- The public enriched map is fully faithful on families supported on the image. -/
theorem pullbackReindex_bijective (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    (hf : Function.Injective f) (X Y : pullback s)
    (hX : ∀ k, (¬ ∃ g, f g = k) → reference.data.id (X k).val = reference.data.zero)
    (a : ZMod 2) : Function.Bijective ((pullbackReindex s f).map X Y a) := by
  with_unfolding_all
    exact RMod.Classification.coordinateRestriction_graded_bijective
      reference.data referenceProperty (oldTwist s) (oldTwist (reindexTwist s f).val)
      f (fun _ => rfl) X Y hf hX a
end RMod.BrundanEllis.Stacking

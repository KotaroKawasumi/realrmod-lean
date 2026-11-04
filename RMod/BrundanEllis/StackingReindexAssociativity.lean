import RMod.BrundanEllis.StackingReindexAssociatorBlock
import RMod.Classification.Proofs.ConvolutionBlocksOfParity
import RMod.Classification.Proofs.ConvolutionTripleExt

/-! Associativity of the actual coordinate restriction tensor comparison.
The equality is proved on every threefold convolution inclusion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)

/-- A change of a summand label does not change the transported inclusion. -/
theorem indexed_source_transport {I : Type} (P : I → C.Obj) (M A : C.Obj)
    (u : ∀ i, C.Hom (P i) M) (i j : I) (hi : i = j) (e : A = P i) (e' : A = P j) :
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData e).hom (u i) =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData e').hom (u j) := by
  subst j
  rfl

variable (s t : Twist) (f : t.data.group →* s.data.group)
  (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
  (hν : ∀ g h, t.data.nu g h = s.data.nu (f g) (f h))
  (hω : ∀ g h k, t.data.omega g h k = s.data.omega (f g) (f h) (f k))
  (X Y Z : PullbackObj C s.data)

include hω in
/-- The two complete threefold comparison routes have the same raw map. -/
theorem coordinateRestrictionTensorHom_associativity (k : t.data.group) :
    C.comp (C.comp (convolutionHom C hC t.data
      (coordinateRestrictionTensorHom C hC s t f hρ hν X Y)
      (fun j => C.id (Z (f j)).val) k)
      (coordinateRestrictionTensorHom C hC s t f hρ hν (convolutionObj C hC s.data X Y) Z k))
      (convolutionAssociatorDataOfParity C hC s.data s.laws.normalizer_parity X Y Z (f k)).hom =
    C.comp (convolutionAssociatorDataOfParity C hC t.data t.laws.normalizer_parity
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k).hom
      (C.comp (convolutionHom C hC t.data (fun j => C.id (X (f j)).val)
        (coordinateRestrictionTensorHom C hC s t f hρ hν Y Z) k)
        (coordinateRestrictionTensorHom C hC s t f hρ hν X (convolutionObj C hC s.data Y Z) k)) := by
  apply hom_ext_of_convolutionLeftInsertions C hC t.data
    ((coordinateRestrictionData C hC s t f hρ).obj X)
    ((coordinateRestrictionData C hC s t f hρ).obj Y)
    ((coordinateRestrictionData C hC s t f hρ).obj Z) k
  intro a g
  obtain ⟨h, rfl⟩ : ∃ h, g * h = a := ⟨g⁻¹ * a, mul_inv_cancel_left _ _⟩
  let eL := (coordinateRestriction_leftFamily C hC s t f hρ hν X Y Z k (g * h) g).trans
    (congrArg (fun b => (convolutionLeftFamily C hC s.data X Y Z (f k) b (f g)).obj)
      (map_mul f g h))
  let eR := coordinateRestriction_rightFamily C hC s t f hρ hν X Y Z k g h
  have hL := (coordinateRestrictionTensorHom_left_inclusion C hC s t f hρ hν X Y Z k (g * h) g).trans
    (indexed_source_transport C
      (fun b => (convolutionLeftFamily C hC s.data X Y Z (f k) b (f g)).obj) _ _
      (fun b => (convolutionLeftInsertionEven C hC s.data X Y Z (f k) b (f g)).hom)
      _ _ (map_mul f g h) _ eL)
  have hR := coordinateRestrictionTensorHom_right_inclusion C hC s t f hρ hν X Y Z k g h
  have hb := coordinateRestriction_associator_block C hC s t f hρ hν hω X Y Z k g h eL eR
  rw [← hC.comp_assoc, ← hC.comp_assoc, hL, hC.comp_assoc,
    convolutionAssociatorOfParity_inclusion_hom, ← hC.comp_assoc, hb,
    hC.comp_assoc, ← hR, ← hC.comp_assoc, ← hC.comp_assoc,
    ← convolutionAssociatorOfParity_inclusion_hom, hC.comp_assoc, hC.comp_assoc]

end RMod.Classification

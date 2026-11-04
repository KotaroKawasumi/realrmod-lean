import RMod.BrundanEllis.StackingReindexAssociativity
import RMod.BrundanEllis.StackingPullbackEvenCalculus
import RMod.BrundanEllis.StackingPullbackCoordinateIso

/-! Assemble the coordinate comparison into the actual public pullback functor.
The monoidal comparisons retain their specified even coordinate maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification RMod.Legacy.Hierarchy

/-- A family of even coordinate maps gives an actual public pullback morphism. -/
def pullbackCoordinateHom (s : Twist) (X Y : Even (pullback s))
    (e : ∀ g : s.group,
      referenceEvenObj reference.data referenceProperty (X g).val ⟶
        referenceEvenObj reference.data referenceProperty (Y g).val) : X ⟶ Y :=
  (evenHomEquiv (oldPullback s).toWeaklyPointedSuperfusion X Y).symm
    ⟨fun g => (e g).hom, fun g => (e g).property⟩

theorem pullbackCoordinateHom_value (s : Twist) (X Y : Even (pullback s))
    (e : ∀ g : s.group,
      referenceEvenObj reference.data referenceProperty (X g).val ⟶
        referenceEvenObj reference.data referenceProperty (Y g).val) :
    pullbackEvenValue s (pullbackCoordinateHom s X Y e) = fun g => (e g).hom := by
  unfold pullbackEvenValue pullbackCoordinateHom
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Evaluate the actual reindexing functor on even maps. -/
theorem pullbackReindex_map_value (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    {X Y : Even (pullback s)} (u : X ⟶ Y) :
    pullbackEvenValue (reindexTwist s f).val ((pullbackReindex s f).forget.map u) =
      fun k => pullbackEvenValue s u (f k) := by
  rfl

/-- The even tensor comparison exists on all pullback objects. -/
def pullbackReindexTensorMap (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    (X Y : Even (pullback s)) :
    (pullbackReindex s f).forget.obj X ⊗ (pullbackReindex s f).forget.obj Y ⟶
      (pullbackReindex s f).forget.obj (X ⊗ Y) :=
  pullbackCoordinateHom (reindexTwist s f).val _ _ (fun k =>
    coordinateRestrictionTensorMap reference.data referenceProperty
      (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl) (fun _ _ => rfl) X Y k)

theorem pullbackReindexTensorMap_value (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    (X Y : Even (pullback s)) :
    pullbackEvenValue (reindexTwist s f).val (pullbackReindexTensorMap s f X Y) =
      coordinateRestrictionTensorHom reference.data referenceProperty
        (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl) (fun _ _ => rfl) X Y :=
  pullbackCoordinateHom_value _ _ _ _

/-- On objects supported on the image, the comparison has a specified inverse. -/
def pullbackReindexTensorIso (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    (hf : Function.Injective f) (X Y : Even (pullback s))
    (hX : ∀ k, (¬ ∃ g, f g = k) → reference.data.id (X k).val = reference.data.zero) :
    (pullbackReindex s f).forget.obj X ⊗ (pullbackReindex s f).forget.obj Y ≅
      (pullbackReindex s f).forget.obj (X ⊗ Y) :=
  pullbackCoordinateIso (reindexTwist s f).val _ _ (fun k =>
    coordinateRestrictionTensorIso reference.data referenceProperty
      (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl) (fun _ _ => rfl) X Y hf hX k)

theorem pullbackReindexTensorIso_hom (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    (hf : Function.Injective f) (X Y : Even (pullback s))
    (hX : ∀ k, (¬ ∃ g, f g = k) → reference.data.id (X k).val = reference.data.zero) :
    (pullbackReindexTensorIso s f hf X Y hX).hom = pullbackReindexTensorMap s f X Y := by
  apply pullbackEvenValue_ext
  intro k
  rw [pullbackReindexTensorMap_value]
  unfold pullbackReindexTensorIso pullbackEvenValue
  rw [pullbackCoordinateIso_hom]
  exact congrArg (fun u => u.hom)
    (coordinateRestrictionTensorMap_eq_iso reference.data referenceProperty
      (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl) (fun _ _ => rfl)
      X Y hf hX k).symm

/-- Naturality on actual even morphisms is inherited from the full coordinate calculation. -/
theorem pullbackReindexTensorMap_naturality (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    {X X' Y Y' : Even (pullback s)} (u : X ⟶ X') (v : Y ⟶ Y') :
    ((pullbackReindex s f).forget.map u ⊗ₘ (pullbackReindex s f).forget.map v) ≫
      pullbackReindexTensorMap s f X' Y' =
    pullbackReindexTensorMap s f X Y ≫ (pullbackReindex s f).forget.map (u ⊗ₘ v) := by
  apply pullbackEvenValue_ext
  intro k
  simp only [pullbackEvenValue_comp, pullbackEvenValue_tensor,
    pullbackReindex_map_value, pullbackReindexTensorMap_value]
  exact coordinateRestrictionTensorHom_naturality reference.data referenceProperty
    (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl) (fun _ _ => rfl)
    (pullbackEvenValue s u) (pullbackEvenValue s v) k

/-- The actual even tensor comparison respects the public pullback associators. -/
theorem pullbackReindexTensorMap_associativity (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group)
    (X Y Z : Even (pullback s)) :
    pullbackReindexTensorMap s f X Y ▷ (pullbackReindex s f).forget.obj Z ≫
      pullbackReindexTensorMap s f (X ⊗ Y) Z ≫
      (pullbackReindex s f).forget.map (α_ X Y Z).hom =
    (α_ ((pullbackReindex s f).forget.obj X) ((pullbackReindex s f).forget.obj Y)
      ((pullbackReindex s f).forget.obj Z)).hom ≫
      (pullbackReindex s f).forget.obj X ◁ pullbackReindexTensorMap s f Y Z ≫
      pullbackReindexTensorMap s f X (Y ⊗ Z) := by
  simp only [← tensorHom_id, ← id_tensorHom]
  apply pullbackEvenValue_ext
  intro k
  have hid (W : Even (pullback (reindexTwist s f).val)) :
      pullbackEvenValue (reindexTwist s f).val (𝟙 W) =
        fun j => reference.data.id (W j).val :=
    funext (pullbackEvenValue_id (reindexTwist s f).val W)
  simp only [pullbackEvenValue_comp, pullbackEvenValue_tensor, pullbackReindexTensorMap_value,
    pullbackReindex_map_value, pullbackEvenValue_associator, hid]
  have ha := coordinateRestrictionTensorHom_associativity reference.data referenceProperty
    (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) X Y Z k
  rw [referenceProperty.comp_assoc] at ha
  with_unfolding_all exact ha

end RMod.BrundanEllis.Stacking

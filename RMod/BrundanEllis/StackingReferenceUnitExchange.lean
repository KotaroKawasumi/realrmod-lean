import RMod.BrundanEllis.StackingUnitHexagon
import RMod.BrundanEllis.StackingReferenceComponentHexagon
import RMod.BrundanEllis.StackingReferenceUnitHexagonCertificates
import RMod.Classification.Proofs.UnitComponent

/-! The actual reference exchanges with the tensor unit agree with the
specified unitors. This follows from the verified unit coefficient cases,
the component hexagons and their naturality, including arbitrary objects. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification CategoryTheory CategoryTheory.MonoidalCategory
local notation "C" => reference.data.toWeaklyPointedSuperfusionData
local notation "L" => referenceProperty.toWeaklyPointedSuperfusionLaws
local notation "R" => (⟨C, L⟩ : WeaklyPointedSuperfusion)

/-- A zero exchange degree gives even laws for the same specified maps. -/
theorem referenceExchange_even (a b : ZMod 8) (hd : ReferenceCommutor.degree a b = 0)
    (X Y : reference.data.Obj) (hX : InComponent C a X) (hY : InComponent C b Y) :
    EvenIsoLaws C (referenceExchangeData a b X Y hX hY) := by
  have h := referenceExchangeLaws a b X Y hX hY
  exact ⟨h.toIsoLaws, hd ▸ h.hom_grade, hd ▸ h.inv_grade⟩

/-- Exchanging X with the unit and then deleting the left unit is the right unitor. -/
theorem referenceExchange_rightUnit (a : ZMod 8) (X : reference.data.Obj)
    (hX : InComponent C a X) :
    reference.data.comp
      (referenceExchange a 0 X reference.data.tensorUnit hX (InComponent.tensor_unit referenceProperty))
      (reference.data.leftUnitorHom X) = reference.data.rightUnitorHom X := by
  let hI := InComponent.tensor_unit referenceProperty
  let hII := hI.tensor referenceProperty hI
  let U : Superfusion.Category.EvenSubcategory ℝ (LinearCategory R) := 𝟙_ _
  let V := Superfusion.Category.evenObj ℝ (LinearCategory R) X
  let e := (referenceExchangeData a 0 X reference.data.tensorUnit hX hI).toEvenIso R
    (referenceExchange_even a 0 (by simp [ReferenceCommutor.degree]) X _ hX hI)
  let e₂ := (referenceExchangeData a 0 X
    (reference.data.tensorObj reference.data.tensorUnit reference.data.tensorUnit) hX hII).toEvenIso R
    (referenceExchange_even a 0 (by simp [ReferenceCommutor.degree]) X _ hX hII)
  have hn : V ◁ (λ_ U).hom ≫ e.hom = e₂.hom ≫ (λ_ U).hom ▷ V := by
    apply WideSubcategory.hom_ext
    have h := referenceExchange_naturality a 0 X X
      (reference.data.tensorObj reference.data.tensorUnit reference.data.tensorUnit) reference.data.tensorUnit
      hX hX hII hI (reference.data.id X) (reference.data.leftUnitorHom reference.data.tensorUnit)
      0 0 (referenceProperty.toWeaklyPointedSuperfusionLaws.id_even X) (referenceProperty.toWeaklyPointedSuperfusionLaws.left_unitor_hom_even _)
    simp only [add_zero, mul_zero, ReferenceCommutor.paritySign_pow, ZMod.val_zero, pow_zero,
      referenceProperty.toWeaklyPointedSuperfusionLaws.one_smul] at h
    exact h
  have hh : (α_ V U U).hom ≫ e₂.hom ≫ (α_ U U V).hom =
      e.hom ▷ U ≫ (α_ U V U).hom ≫ U ◁ e.hom := by
    apply WideSubcategory.hom_ext
    exact referenceLeftHexagon a 0 0 (ReferenceCommutor.leftHexagon_unit a)
      X reference.data.tensorUnit reference.data.tensorUnit hX hI hI
  exact congrArg (fun f => f.hom) (exchange_rightUnit V e e₂ hn hh)

/-- Exchanging the unit with X and then deleting the right unit is the left unitor. -/
theorem referenceExchange_leftUnit (a : ZMod 8) (X : reference.data.Obj)
    (hX : InComponent C a X) :
    reference.data.comp
      (referenceExchange 0 a reference.data.tensorUnit X (InComponent.tensor_unit referenceProperty) hX)
      (reference.data.rightUnitorHom X) = reference.data.leftUnitorHom X := by
  let hI := InComponent.tensor_unit referenceProperty
  let hII := hI.tensor referenceProperty hI
  let U : Superfusion.Category.EvenSubcategory ℝ (LinearCategory R) := 𝟙_ _
  let V := Superfusion.Category.evenObj ℝ (LinearCategory R) X
  let e := (referenceExchangeData 0 a reference.data.tensorUnit X hI hX).toEvenIso R
    (referenceExchange_even 0 a (by simp [ReferenceCommutor.degree]) _ X hI hX)
  let e₂ := (referenceExchangeData 0 a
    (reference.data.tensorObj reference.data.tensorUnit reference.data.tensorUnit) X hII hX).toEvenIso R
    (referenceExchange_even 0 a (by simp [ReferenceCommutor.degree]) _ X hII hX)
  have hn : (ρ_ U).hom ▷ V ≫ e.hom = e₂.hom ≫ V ◁ (ρ_ U).hom := by
    apply WideSubcategory.hom_ext
    have h := referenceExchange_naturality 0 a
      (reference.data.tensorObj reference.data.tensorUnit reference.data.tensorUnit) reference.data.tensorUnit X X
      hII hI hX hX (reference.data.rightUnitorHom reference.data.tensorUnit) (reference.data.id X)
      0 0 (referenceProperty.toWeaklyPointedSuperfusionLaws.right_unitor_hom_even _) (referenceProperty.toWeaklyPointedSuperfusionLaws.id_even X)
    simp only [add_zero, mul_zero, ReferenceCommutor.paritySign_pow, ZMod.val_zero, pow_zero,
      referenceProperty.toWeaklyPointedSuperfusionLaws.one_smul] at h
    exact h
  have hh' : e₂.hom = (α_ U U V).hom ≫ U ◁ e.hom ≫
      (α_ U V U).inv ≫ e.hom ▷ U ≫ (α_ V U U).hom := by
    apply WideSubcategory.hom_ext
    have h := referenceRightHexagon 0 0 a (ReferenceCommutor.rightHexagon_unit a)
      reference.data.tensorUnit reference.data.tensorUnit X hI hI hX
    simp only [ReferenceCommutor.rightDefect, ZMod.val_zero, Nat.cast_zero, zero_mul,
      ReferenceCommutor.paritySign_pow, pow_zero, referenceProperty.toWeaklyPointedSuperfusionLaws.one_smul] at h
    exact h
  have hh : (α_ U U V).inv ≫ e₂.hom ≫ (α_ V U U).inv =
      U ◁ e.hom ≫ (α_ U V U).inv ≫ e.hom ▷ U := by
    rw [hh']
    simp
  exact congrArg (fun f => f.hom) (exchange_leftUnit V e e₂ hn hh)

end RMod.BrundanEllis.Stacking

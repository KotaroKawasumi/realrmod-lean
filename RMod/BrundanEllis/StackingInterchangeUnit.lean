import RMod.BrundanEllis.StackingInterchangeAssociativity

/-! Unit coherence of the ordinary four-object shuffle, assuming only the actual unit identities of its middle crossing. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v
namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.MonoidalCategory
variable {M : Type u} [Category.{v} M] [MonoidalCategory M]

/-- Left unit coherence of the specified shuffle needs only the middle
exchange with the unit and its actual unitor identity. -/
theorem interchangeMap_leftUnit (X Y : M)
    (e : (𝟙_ M) ⊗ X ⟶ X ⊗ (𝟙_ M))
    (he : e ≫ (ρ_ X).hom = (λ_ X).hom) :
    interchangeMap (𝟙_ M) (𝟙_ M) X Y (𝟙_ M) X e ≫
      ((λ_ X).hom ⊗ₘ (λ_ Y).hom) =
    ((λ_ (𝟙_ M)).hom ⊗ₘ 𝟙 (X ⊗ Y)) ≫ (λ_ (X ⊗ Y)).hom := by
  have hh := congrArg (fun f => f ≫ (ρ_ X).inv) he
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
  rw [hh]
  unfold interchangeMap
  monoidal

/-- Right unit coherence of the same shuffle. -/
theorem interchangeMap_rightUnit (X Y : M)
    (e : Y ⊗ (𝟙_ M) ⟶ (𝟙_ M) ⊗ Y)
    (he : e ≫ (λ_ Y).hom = (ρ_ Y).hom) :
    interchangeMap X Y (𝟙_ M) (𝟙_ M) Y (𝟙_ M) e ≫
      ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom) =
    (𝟙 (X ⊗ Y) ⊗ₘ (λ_ (𝟙_ M)).hom) ≫ (ρ_ (X ⊗ Y)).hom := by
  have hh := congrArg (fun f => f ≫ (λ_ Y).inv) he
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
  rw [hh]
  unfold interchangeMap
  monoidal

end RMod.BrundanEllis.Stacking

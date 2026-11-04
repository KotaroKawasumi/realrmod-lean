import RMod.BrundanEllis.StackingFusionParity
import RMod.BrundanEllis.StackingSimpleSpan
import RMod.BrundanEllis.StackingBinarySpan
import RMod.BrundanEllis.StackingRigidRetracts

/-! Weak invertibility passes to even retracts. The self-dual tensor of a
retract is a retract of the ambient self-dual tensor, and the finite span
of the simple unit and parity object is closed under such retracts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
namespace RMod.BrundanEllis.Stacking
variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)]
  [MonoidalPiSuperCategory C] [MonoidalSuperCategory C]
  [RigidCategory (Even C)] [Abelian (Even C)] [FusionPiSuperCategory C]

/-- The two simple types allowed in a weak inverse product. -/
def unitParityFamily (b : Bool) : Even C :=
  if b then evenObj C (MonoidalPiSuperCategory.pi (C := C)) else 𝟙_ (Even C)

theorem unitParityFamily_simple (b : Bool) : Simple (unitParityFamily C b) := by
  cases b
  · exact FusionPiSuperCategory.simple_unit (C := C)
  · exact fusion_pi_simple C

theorem weaklyInvertible_of_retract {X Y : Even C} (r : Retract X Y)
    (hY : IsWeaklyInvertible C Y) : IsWeaklyInvertible C X := by
  obtain ⟨p, q, ⟨e⟩⟩ := hY
  have hU : FiniteSpan (unitParityFamily C) (⨁ fun _ : Fin p => 𝟙_ (Even C)) :=
    FiniteSpan.of_finite_family (Z := unitParityFamily C) (fun _ : Fin p => false)
  have hP : FiniteSpan (unitParityFamily C)
      (⨁ fun _ : Fin q => evenObj C (MonoidalPiSuperCategory.pi (C := C))) :=
    FiniteSpan.of_finite_family (Z := unitParityFamily C) (fun _ : Fin q => true)
  have h := FiniteSpan.of_iso e (FiniteSpan.binary_biproduct hU hP)
  have hX := FiniteSpan.of_retract (FusionPiSuperCategory.semisimple (C := C))
    (unitParityFamily_simple C) (Retracts.selfDual r) h
  exact binary_multiplicities (𝟙_ (Even C))
    (evenObj C (MonoidalPiSuperCategory.pi (C := C))) hX

end RMod.BrundanEllis.Stacking

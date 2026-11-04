import RMod.BrundanEllis.StackingReferenceUniformOperator

/-! Changing the common algebra label only transports coefficient vectors.
These operators can be composed through differently parenthesized equal
labels, as required by the reference hexagon diagrams. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Retain the source and target labels separately in the free-module action. -/
def labelOperator (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (hab : a = b) (f : Hom realDData X Y) :
    (Fin X.size → Coeff a) →ₗ[ℝ] (Fin Y.size → Coeff b) :=
  (rowCoefficientCast hab).toLinearMap.comp
    (uniformOperator a X Y hX (fun j => (hY j).trans hab.symm) f)

/-- Endpoint transport preserves faithfulness. -/
theorem labelOperator_injective (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) (hab : a = b) :
    Function.Injective (labelOperator a b X Y hX hY hab) := by
  cases hab
  exact uniformOperator_injective a X Y hX hY

/-- Operator composition follows the same endpoint-label path as morphism composition. -/
theorem labelOperator_comp (a b c : ZMod 8) (X Y Z : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (hZ : ∀ k, (Z.atom k).label = c) (hab : a = b) (hbc : b = c)
    (f : Hom realDData X Y) (g : Hom realDData Y Z) :
    labelOperator a c X Z hX hZ (hab.trans hbc) (Hom.comp f g) =
      (labelOperator b c Y Z hY hZ hbc g).comp (labelOperator a b X Y hX hY hab f) := by
  cases hab
  cases hbc
  exact uniformOperator_comp a X Y Z hX hY hZ f g

/-- Real rescaling commutes with the endpoint transport. -/
theorem labelOperator_smul (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (hab : a = b) (r : ℝ) (f : Hom realDData X Y) :
    labelOperator a b X Y hX hY hab (Hom.smul r f) = r • labelOperator a b X Y hX hY hab f := by
  cases hab
  exact uniformOperator_smul a X Y hX hY r f

end RMod.BrundanEllis.Stacking.ReferenceCommutor

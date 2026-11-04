import RMod.Classification.Abstract.Pi
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# The intrinsic reference property

The statement needs only an intrinsic test for each of the eight types.
The endomorphisms of a finite sum within the simple's parity orbit must
be graded-isomorphic to Mathlib's negative-square Clifford algebra. The
bridge below uses the category's existing raw Hom operations; Mathlib
supplies the algebra, quadratic form, and even/odd grading.
-/

set_option autoImplicit false

namespace RMod.Classification

/-- Homogeneous isomorphism of either parity, without a chosen witness. -/
def SameParityOrbit (C : WeaklyPointedSuperfusionData.{0, 0})
    (X Y : C.Obj) : Prop := ∃ a, C.HasHomogeneousIso a X Y

/-- Graded real algebra isomorphism from Mathlib's `Cl_(0,n)` to End(Y).
The raw category uses diagrammatic composition, hence the reversed
arguments in the multiplication clause. This is only an existence
property; the pullback construction does not choose or evaluate this map. -/
def HasCliffordEnd (C : WeaklyPointedSuperfusionData.{0, 0}) (Y : C.Obj)
    (n : ℕ) : Prop :=
  let Q := QuadraticMap.weightedSumSquares ℝ (fun _ : Fin n => (-1 : ℝ))
  ∃ e : CliffordAlgebra Q ≃ C.Hom Y Y,
    e 1 = C.id Y ∧
    (∀ x y, e (x + y) = C.add (e x) (e y)) ∧
    (∀ (r : ℝ) x, e (r • x) = C.smul r (e x)) ∧
    (∀ x y, e (x * y) = C.comp (e y) (e x)) ∧
    ∀ a x, x ∈ CliffordAlgebra.evenOdd Q a ↔ C.IsHomogeneous a (e x)

/-- A simple has type `r` when a nonempty finite sum of its parity shifts
has endomorphism algebra `Cl_(0,r.val)`, with its standard grading. -/
def HasBWType (C : WeaklyPointedSuperfusionData.{0, 0}) (X : C.Obj)
    (r : ZMod 8) : Prop :=
  ∃ (n : ℕ) (S : Fin n → C.Obj) (Y : C.Obj),
    0 < n ∧ (∀ i, SameParityOrbit C X (S i)) ∧
      C.HasDecomposition Y S ∧ HasCliffordEnd C Y r.val

/-- P as a property of the specified triple. The intrinsic group law and
the multiplicativity of its type map are proof obligations, not inputs. -/
structure ReferenceProperty (C : PiSuperfusionData.{0, 0}) : Prop
    extends PiSuperfusionLaws C where
  simple_type : ∀ X, C.IsSimple X → ∃! r, HasBWType C.toWeaklyPointedSuperfusionData X r
  realizes_type : ∀ r, ∃ X, C.IsSimple X ∧ HasBWType C.toWeaklyPointedSuperfusionData X r
  type_detects_orbit : ∀ X Y r, C.IsSimple X → C.IsSimple Y →
    HasBWType C.toWeaklyPointedSuperfusionData X r →
    (HasBWType C.toWeaklyPointedSuperfusionData Y r ↔
      SameParityOrbit C.toWeaklyPointedSuperfusionData X Y)

/-- A type component is defined by actual even simple decompositions.
In particular zero lies in every component, through the empty family. -/
def InComponent (C : WeaklyPointedSuperfusionData.{0, 0})
    (r : ZMod 8) (X : C.Obj) : Prop :=
  ∃ (n : ℕ) (S : Fin n → C.Obj),
    (∀ i, C.IsSimple (S i) ∧ HasBWType C (S i) r) ∧ C.HasDecomposition X S

end RMod.Classification

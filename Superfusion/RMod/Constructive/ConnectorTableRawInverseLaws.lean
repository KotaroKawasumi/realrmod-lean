/-
Superfusion / RMod / Constructive / ConnectorTableRawInverseLaws

Entrywise consequences of the saved raw connector inverse certificates.
This proof-only module contains no connector data and performs no new closed
table reduction: it transports the already checked Boolean certificates to
the two integral coefficient convolutions needed by the raw `T` bundle.
-/
import Superfusion.RMod.Constructive.ConnectorTableInverseLaws

set_option autoImplicit false

namespace Superfusion

/-! ## Entrywise soundness of an ordinary product certificate

The executable checker works with nested lists.  Its mathematical content at
one row, column, and coefficient-basis index is precisely `convCoeff`.
-/

/-- A successful ordinary matrix-product certificate gives every coefficient
of the corresponding signed-monomial convolution. -/
theorem checkMatMulEq_entry_sound {sigma k : Nat}
    {co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → Int}
    (X Y Z : List (List (List Int)))
    (hcheck : checkMatMulEq sigma k (natCo k co) (natTable2 k sg) X Y Z = true)
    (r t : Fin sigma) (e : Fin k) :
    convCoeff sg co (coeffOf sigma k X) (coeffOf sigma k Y) r t e =
      coeffOf sigma k Z r t e := by
  have hentry := checkAll_sound hcheck r t e
  rw [beq_iff_eq, convL_eq] at hentry
  exact hentry

namespace RModCoordinate
namespace ConnectorTableLaws

open RMod.ConstructiveConnectorTable

/-! ## The checked scalar matrix

The checker target is the integral scalar matrix `lambda I`.  Reading one
entry produces a Kronecker delta in the route position and the unit basis
coefficient.
-/

/-- One coefficient of the stored scaled identity is `lambda` exactly on the
diagonal and in coefficient-basis degree zero. -/
theorem scaledIdentityCoeffNat_apply (a b c : Nat)
    (r t : Fin (sigmaNat a b c))
    (e : Fin (realRepDim ((a + b + c) % 8))) :
    coeffOf (sigmaNat a b c) (realRepDim ((a + b + c) % 8))
        (scaledIdentityCoeffNat a b c) r t e =
      if r = t ∧ e.val = 0 then (inverseScaleNat a b c : Int) else 0 := by
  simp [coeffOf, coeffGet, scaledIdentityCoeffNat,
    Fin.ext_iff, r.isLt, t.isLt, e.isLt]

/-! ## Two-sided raw coefficient identities

The saved certificates say that the frozen forward table and its explicit
conjugate-transpose numerator multiply, in either order, to the same scaled
identity.  These are coefficient-level statements; no semantic matrix inverse
or noncomputable choice is used.
-/

/-- Raw forward coefficients convolved with the stored inverse numerator give
the scaled Kronecker identity. -/
theorem rawForwardInverseCoeff (a b c : ZMod 8)
    (r t : Fin (sigma a b c))
    (e : Fin (realRepDim ((a.val + b.val + c.val) % 8))) :
    convCoeff
        (realRepMulSignAux ((a.val + b.val + c.val) % 8))
        (realRepMulIdxAux ((a.val + b.val + c.val) % 8))
        (coeffOf (sigma a b c) (realRepDim ((a.val + b.val + c.val) % 8))
          (forwardCoeff a b c))
        (coeffOf (sigma a b c) (realRepDim ((a.val + b.val + c.val) % 8))
          (inverseNumeratorCoeff a b c))
        r t e =
      if r = t ∧ e.val = 0 then (inverseScale a b c : Int) else 0 := by
  have hentry := checkMatMulEq_entry_sound
    (forwardCoeffNat a.val b.val c.val)
    (inverseNumeratorCoeffNat a.val b.val c.val)
    (scaledIdentityCoeffNat a.val b.val c.val)
    (checkForwardInverse_true a b c) r t e
  change convCoeff
      (realRepMulSignAux ((a.val + b.val + c.val) % 8))
      (realRepMulIdxAux ((a.val + b.val + c.val) % 8))
      (coeffOf (sigmaNat a.val b.val c.val)
        (realRepDim ((a.val + b.val + c.val) % 8))
        (forwardCoeffNat a.val b.val c.val))
      (coeffOf (sigmaNat a.val b.val c.val)
        (realRepDim ((a.val + b.val + c.val) % 8))
        (inverseNumeratorCoeffNat a.val b.val c.val))
      r t e = if r = t ∧ e.val = 0 then
        (inverseScaleNat a.val b.val c.val : Int) else 0
  exact hentry.trans (scaledIdentityCoeffNat_apply a.val b.val c.val r t e)

/-- The stored inverse numerator convolved with the raw forward coefficients
also gives the scaled Kronecker identity. -/
theorem rawInverseForwardCoeff (a b c : ZMod 8)
    (r t : Fin (sigma a b c))
    (e : Fin (realRepDim ((a.val + b.val + c.val) % 8))) :
    convCoeff
        (realRepMulSignAux ((a.val + b.val + c.val) % 8))
        (realRepMulIdxAux ((a.val + b.val + c.val) % 8))
        (coeffOf (sigma a b c) (realRepDim ((a.val + b.val + c.val) % 8))
          (inverseNumeratorCoeff a b c))
        (coeffOf (sigma a b c) (realRepDim ((a.val + b.val + c.val) % 8))
          (forwardCoeff a b c))
        r t e =
      if r = t ∧ e.val = 0 then (inverseScale a b c : Int) else 0 := by
  have hentry := checkMatMulEq_entry_sound
    (inverseNumeratorCoeffNat a.val b.val c.val)
    (forwardCoeffNat a.val b.val c.val)
    (scaledIdentityCoeffNat a.val b.val c.val)
    (checkInverseForward_true a b c) r t e
  change convCoeff
      (realRepMulSignAux ((a.val + b.val + c.val) % 8))
      (realRepMulIdxAux ((a.val + b.val + c.val) % 8))
      (coeffOf (sigmaNat a.val b.val c.val)
        (realRepDim ((a.val + b.val + c.val) % 8))
        (inverseNumeratorCoeffNat a.val b.val c.val))
      (coeffOf (sigmaNat a.val b.val c.val)
        (realRepDim ((a.val + b.val + c.val) % 8))
        (forwardCoeffNat a.val b.val c.val))
      r t e = if r = t ∧ e.val = 0 then
        (inverseScaleNat a.val b.val c.val : Int) else 0
  exact hentry.trans (scaledIdentityCoeffNat_apply a.val b.val c.val r t e)

end ConnectorTableLaws
end RModCoordinate
end Superfusion

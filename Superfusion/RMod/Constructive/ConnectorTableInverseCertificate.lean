/-
Superfusion / RMod / Constructive / ConnectorTableInverseCertificate

Proof-only executable certificates for the frozen raw connector table.
The generated coefficient data remains in `ConnectorTableData`; this leaf
adds only the Boolean inverse checks and their general soundness bridge.
-/
import Superfusion.RMod.Constructive.ConnectorTableData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion

open Module

/-! ## Ordinary matrix-product certificates

The coefficient checker already supplies the signed-monomial convolution.
This specialization records an ordinary product identity `X * Y = Z` and
turns a successful closed Boolean check into the corresponding matrix law.
-/

/-- A closed certificate for an ordinary product identity `X * Y = Z`. -/
def checkMatMulEq (σ k : ℕ) (coN : ℕ → ℕ → ℕ) (sgN : ℕ → ℕ → ℤ)
    (X Y Z : List (List (List ℤ))) : Bool :=
  checkAll σ k fun r t h =>
    convL σ k coN sgN X Y r t h == coeffGet Z r t h

/-- A successful closed product certificate gives the corresponding matrix
identity over any algebra with the recorded signed-monomial basis. -/
theorem checkMatMulEq_sound {R : Type*} [CommRing R] {P : Type*} [Ring P]
    [Algebra R P] {k σ : ℕ} (bP : Basis (Fin k) R P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (X Y Z : List (List (List ℤ)))
    (hchk : checkMatMulEq σ k (natCo k co) (natTable2 k sg) X Y Z = true) :
    matOfCoeff bP (coeffOf σ k X) * matOfCoeff bP (coeffOf σ k Y)
      = matOfCoeff bP (coeffOf σ k Z) := by
  rw [matOfCoeff_mul hmul hco hco']
  refine congrArg (matOfCoeff bP) ?_
  funext r t h
  have hb := checkAll_sound hchk r t h
  rw [beq_iff_eq, convL_eq] at hb
  exact hb

namespace RMod
namespace ConstructiveConnectorTable

/-! ## Positivity of the integral inverse scale -/

/-- Every generated inverse scale is a positive power of two. -/
theorem inverseScaleNat_pos (a b c : ℕ) : 0 < inverseScaleNat a b c := by
  simp [inverseScaleNat]

/-- In particular, the generated inverse scale never vanishes. -/
theorem inverseScaleNat_ne_zero (a b c : ℕ) : inverseScaleNat a b c ≠ 0 :=
  Nat.ne_of_gt (inverseScaleNat_pos a b c)

/-- Positivity at the public `ZMod 8` labels. -/
theorem inverseScale_pos (a b c : ZMod 8) : 0 < inverseScale a b c :=
  inverseScaleNat_pos a.val b.val c.val

/-- Nonvanishing at the public `ZMod 8` labels. -/
theorem inverseScale_ne_zero (a b c : ZMod 8) : inverseScale a b c ≠ 0 :=
  inverseScaleNat_ne_zero a.val b.val c.val

/-! ## Frozen two-sided inverse checks

For the stored connector `T`, the stored conjugate-transpose numerator `U`
is checked against the exact integral identities `T * U = λ I` and
`U * T = λ I`.  These are proof certificates over the data, not new table
data or a selected inverse.
-/

/-- Coefficient array of the scalar matrix `λ I`. -/
def scaledIdentityCoeffNat (a b c : ℕ) : List (List (List ℤ)) :=
  let m := (a + b + c) % 8
  let sigma := sigmaNat a b c
  let k := realRepDim m
  let scale : ℤ := inverseScaleNat a b c
  (List.range sigma).map fun r =>
    (List.range sigma).map fun s =>
      (List.range k).map fun e => if r = s && e = 0 then scale else 0

/-- Kernel-executable certificate for `T * U = λ I`. -/
def checkForwardInverseNat (a b c : ℕ) : Bool :=
  let m := (a + b + c) % 8
  checkMatMulEq (sigmaNat a b c) (realRepDim m) (realCoN m) (realSignN m)
    (forwardCoeffNat a b c) (inverseNumeratorCoeffNat a b c)
    (scaledIdentityCoeffNat a b c)

/-- Kernel-executable certificate for `U * T = λ I`. -/
def checkInverseForwardNat (a b c : ℕ) : Bool :=
  let m := (a + b + c) % 8
  checkMatMulEq (sigmaNat a b c) (realRepDim m) (realCoN m) (realSignN m)
    (inverseNumeratorCoeffNat a b c) (forwardCoeffNat a b c)
    (scaledIdentityCoeffNat a b c)

end ConstructiveConnectorTable
end RMod

namespace RModCoordinate
namespace ConnectorTableLaws

open RMod.ConstructiveConnectorTable

/-! ## Fixed-pair certificate batches -/

/-- The eight two-sided inverse checks at a fixed pair `(a,b)`.  The saved
kernel proofs split the 512 triples along these small batches. -/
def inverseCertificatesForAB (a b : Nat) : Bool :=
  (List.range 8).all fun c =>
    checkForwardInverseNat a b c && checkInverseForwardNat a b c

end ConnectorTableLaws
end RModCoordinate
end Superfusion

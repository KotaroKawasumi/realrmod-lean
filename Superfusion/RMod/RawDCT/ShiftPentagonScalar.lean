import Superfusion.RMod.RawDCT.NuBetaRegular

/-!
# Scalar ledger for the shifted raw pentagon

This file separates the two route signs and the five inverse `beta` factors
which occur when a raw connector is shifted by `(nu, beta)`.  The definitions
use only computational raw data.  The cancellation theorem uses the laws of
the same `NuBetaData`; it neither expands a fourfold route nor evaluates a
finite table.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Parity degrees contributed by the two pentagon routes -/

/-- The two Koszul exponents contributed by the three-edge top route.

They are the two summands of `nu cupOne rawParity` encountered at the first
and third shifted associator edges. -/
def shiftPentagonTopDegree (x : RawDCTData) (n : NuBetaData)
    (a b c d : RawDCTGroup) : ZMod 2 :=
  n.nu (a * b * c) d * rawParity x a b c +
    n.nu a (b * c * d) * rawParity x b c d

/-- The Koszul exponent contributed by the two-edge bottom route.

This is the cup-product term `nu(a,b) * nu(c,d)`. -/
def shiftPentagonBottomDegree (n : NuBetaData)
    (a b c d : RawDCTGroup) : ZMod 2 :=
  n.nu a b * n.nu c d

/-- The top and bottom route degrees partition the regular quadratic
correction `nu cup nu + nu cupOne rawParity`. -/
theorem shiftPentagonTopDegree_add_bottom
    (x : RawDCTData) (n : NuBetaData) (a b c d : RawDCTGroup) :
    shiftPentagonTopDegree x n a b c d +
        shiftPentagonBottomDegree n a b c d =
      Superfusion.regularQuadratic n.nu (rawParity x) a b c d := by
  simp only [shiftPentagonTopDegree, shiftPentagonBottomDegree,
    Superfusion.regularQuadratic, Superfusion.cup₂₂,
    Superfusion.cupOne₂₃]
  ac_rfl

/-- Unit-valued form of the route-degree decomposition. -/
theorem shiftPentagonQuadraticSign_split
    (x : RawDCTData) (n : NuBetaData) (a b c d : RawDCTGroup) :
    (Superfusion.sgn
        (Superfusion.regularQuadratic n.nu (rawParity x) a b c d) : ℝˣ) =
      (Superfusion.sgn (shiftPentagonTopDegree x n a b c d) : ℝˣ) *
        (Superfusion.sgn (shiftPentagonBottomDegree n a b c d) : ℝˣ) := by
  rw [← shiftPentagonTopDegree_add_bottom x n a b c d,
    Superfusion.sgn_add]

/-! ## Route scalars after connector rescaling -/

/-- Product of the three top-route `beta⁻¹` factors and its transport
sign. -/
def shiftPentagonTopScalar (x : RawDCTData) (n : NuBetaData)
    (a b c d : RawDCTGroup) : ℝˣ :=
  (n.beta a b c)⁻¹ *
    (n.beta a (b * c) d)⁻¹ *
    (n.beta b c d)⁻¹ *
    (Superfusion.sgn (shiftPentagonTopDegree x n a b c d) : ℝˣ)

/-- Product of the two bottom-route `beta⁻¹` factors and its transport
sign. -/
def shiftPentagonBottomScalar (n : NuBetaData)
    (a b c d : RawDCTGroup) : ℝˣ :=
  (n.beta (a * b) c d)⁻¹ *
    (n.beta a b (c * d))⁻¹ *
    (Superfusion.sgn (shiftPentagonBottomDegree n a b c d) : ℝˣ)

/-! ## Cancellation supplied by the exact `NuBeta` laws -/

/-- The top route scalar absorbs the original raw pentagon defect `chi` and
becomes the bottom route scalar.

This is the scalar identity used after a route-level theorem identifies the
unshifted top coordinate with `chi` times the corresponding bottom
coordinate. -/
theorem shiftPentagonTopScalar_mul_chi
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (a b c d : RawDCTGroup) :
    shiftPentagonTopScalar x n a b c d * pchi.chi a b c d =
      shiftPentagonBottomScalar n a b c d := by
  have h :=
    (regularTrivializationOfNuBetaData x hx pchi hpchi n hn).rescaledPentagon
      a b c d
  change
    (n.beta a b c)⁻¹ * (n.beta a (b * c) d)⁻¹ *
          (n.beta b c d)⁻¹ *
          (pchi.chi a b c d *
            (Superfusion.sgn
              (Superfusion.regularQuadratic n.nu (rawParity x)
                a b c d) : ℝˣ)) =
      (n.beta (a * b) c d)⁻¹ * (n.beta a b (c * d))⁻¹ at h
  rw [shiftPentagonQuadraticSign_split x n a b c d] at h
  unfold shiftPentagonTopScalar shiftPentagonBottomScalar
  calc
    _ = ((n.beta a b c)⁻¹ * (n.beta a (b * c) d)⁻¹ *
          (n.beta b c d)⁻¹ *
          (pchi.chi a b c d *
            (Superfusion.sgn
              (shiftPentagonTopDegree x n a b c d) : ℝˣ))) *
        ((Superfusion.sgn
            (shiftPentagonBottomDegree n a b c d) : ℝˣ) *
          (Superfusion.sgn
            (shiftPentagonBottomDegree n a b c d) : ℝˣ)) := by
      rw [Superfusion.sgn_mul_self', mul_one]
      ac_rfl
    _ = ((n.beta a b c)⁻¹ * (n.beta a (b * c) d)⁻¹ *
          (n.beta b c d)⁻¹ *
          (pchi.chi a b c d *
            ((Superfusion.sgn
                (shiftPentagonTopDegree x n a b c d) : ℝˣ) *
              (Superfusion.sgn
                (shiftPentagonBottomDegree n a b c d) : ℝˣ)))) *
        (Superfusion.sgn
          (shiftPentagonBottomDegree n a b c d) : ℝˣ) := by
      ac_rfl
    _ = _ := by rw [h]

/-- Real-valued cancellation after multiplying by an arbitrary source
defect.  The defect may vanish, so no unit-valued hypothesis is imposed.

Later coordinate soundness can instantiate `sourceDefect` with the actual
bottom-route coordinate. -/
theorem shiftPentagonScalar_mul_sourceDefect
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (a b c d : RawDCTGroup) (sourceDefect : ℝ) :
    (shiftPentagonTopScalar x n a b c d : ℝ) *
          ((pchi.chi a b c d : ℝ) * sourceDefect) =
      (shiftPentagonBottomScalar n a b c d : ℝ) * sourceDefect := by
  have h :
      (shiftPentagonTopScalar x n a b c d : ℝ) *
          (pchi.chi a b c d : ℝ) =
        (shiftPentagonBottomScalar n a b c d : ℝ) := by
    simpa only [Units.val_mul] using
      congrArg (fun z : ℝˣ => (z : ℝ))
        (shiftPentagonTopScalar_mul_chi x hx pchi hpchi n hn a b c d)
  rw [← mul_assoc, h]

/-- A route-level corollary: any unshifted equality
`topDefect = chi * bottomDefect` becomes a strict shifted scalar equality. -/
theorem shiftPentagonScalar_eq_of_sourceDefect
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (a b c d : RawDCTGroup) (topDefect bottomDefect : ℝ)
    (hdefect : topDefect = (pchi.chi a b c d : ℝ) * bottomDefect) :
    (shiftPentagonTopScalar x n a b c d : ℝ) * topDefect =
      (shiftPentagonBottomScalar n a b c d : ℝ) * bottomDefect := by
  rw [hdefect]
  exact shiftPentagonScalar_mul_sourceDefect
    x hx pchi hpchi n hn a b c d bottomDefect

/-! ## Completed-bundle entry points -/

/-- Bundled form of `shiftPentagonTopScalar_mul_chi`.  It introduces no new
data: all route scalars are still evaluated from `X.data` and `N.data`. -/
theorem shiftPentagonTopScalar_mul_chi_bundled
    (X : RawDCT) (P : PChi X) (N : NuBeta X P)
    (a b c d : RawDCTGroup) :
    shiftPentagonTopScalar X.data N.data a b c d * P.data.chi a b c d =
      shiftPentagonBottomScalar N.data a b c d :=
  shiftPentagonTopScalar_mul_chi
    X.data X.laws P.data P.laws N.data N.laws a b c d

/-- Bundled route-level form of the shifted scalar equality. -/
theorem shiftPentagonScalar_eq_of_sourceDefect_bundled
    (X : RawDCT) (P : PChi X) (N : NuBeta X P)
    (a b c d : RawDCTGroup) (topDefect bottomDefect : ℝ)
    (hdefect : topDefect = (P.data.chi a b c d : ℝ) * bottomDefect) :
    (shiftPentagonTopScalar X.data N.data a b c d : ℝ) * topDefect =
      (shiftPentagonBottomScalar N.data a b c d : ℝ) * bottomDefect :=
  shiftPentagonScalar_eq_of_sourceDefect
    X.data X.laws P.data P.laws N.data N.laws
      a b c d topDefect bottomDefect hdefect

end Superfusion.RMod.RawDCT

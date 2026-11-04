import Superfusion.RMod.RawDCT.Shift

/-!
# Gu--Wen obstruction after a raw cochain shift

This file transports the abstract `(p, χ)` cochain package across the raw
`(ν, β)` shift.  The new scalar cochain records exactly the quadratic sign
from regrading and the inverse coboundary from connector rescaling:

`χ' = χ · sgn (q(ν,p)) · (dm₃ β)⁻¹`.

The trivialization laws reduce this formula pointwise to `1`.  Likewise, the
stored parity formula for `shiftTData` reduces the shifted connector parity
to `0`.  These are formal cochain calculations; no fourfold route or finite
table is evaluated here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Computational shifted cochain data -/

/-- The obstruction cochain after regrading by `ν` and rescaling by `β⁻¹`.

Only cochain data is used in this definition, so it remains computational and
does not depend on any proof field. -/
def shiftPChiData (x : RawDCTData) (pchi : PChiData)
    (n : NuBetaData) : PChiData where
  chi := fun a b c e =>
    pchi.chi a b c e *
      (Superfusion.sgn
        (Superfusion.regularQuadratic n.nu (rawParity x) a b c e) : ℝˣ) *
      (Superfusion.dm₃ n.beta a b c e)⁻¹

/-! ## Pointwise cancellation supplied by the shift laws -/

/-- The shifted raw connector has even degree.  This uses only the stored
parity formula for `shiftTData` and the equation `d₂ν = p`. -/
theorem rawParity_shiftRawDCTData_eq_zero
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (a b c : RawDCTGroup) :
    rawParity (shiftRawDCTData x n) a b c = 0 := by
  change
    (shiftTData x.D x.C x.T n).parity a.toAdd b.toAdd c.toAdd = 0
  rw [shiftTData_parity]
  simp only [ofAdd_toAdd]
  have hparity := hn.parity a b c
  rw [hparity]
  exact CharTwo.add_self_eq_zero _

/-- The shifted scalar obstruction is identically one.  This is the direct
group cancellation of the single equation `χ · sgn(q) = dm₃β`. -/
theorem shiftPChiData_chi_eq_one
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (a b c e : RawDCTGroup) :
    (shiftPChiData x pchi n).chi a b c e = 1 := by
  simp only [shiftPChiData]
  rw [hn.pentagon a b c e]
  exact mul_inv_cancel _

/-! ## Laws and completed bundle -/

/-- The identically even/one shifted pair satisfies the Gu--Wen equations.

`hshift` supplies only the laws of the already-computed shifted DCT.  The
cochain proof itself uses the two pointwise cancellation theorems above. -/
def shiftPChiLaws
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (hshift : RawDCTLaws (shiftRawDCTData x n)) :
    PChiLaws (shiftRawDCTData x n) hshift (shiftPChiData x pchi n) := by
  have hp : rawParity (shiftRawDCTData x n) = fun _ _ _ => 0 := by
    funext a b c
    exact rawParity_shiftRawDCTData_eq_zero x hx pchi hpchi n hn a b c
  have hchi : (shiftPChiData x pchi n).chi = fun _ _ _ _ => 1 := by
    funext a b c e
    exact shiftPChiData_chi_eq_one x hx pchi hpchi n hn a b c e
  refine {
    p_cocycle := ?_
    chi_supercocycle := ?_ }
  · intro a b c e
    rw [hp]
    simp [Superfusion.d₃]
  · intro a b c e f
    rw [hp, hchi]
    simp [Superfusion.dm₄, Superfusion.cupOne₃₃]

/-- Bundle the shifted obstruction over any supplied proof that the computed
shifted raw data again satisfies the raw DCT laws. -/
def shiftPChi
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (hshift : RawDCTLaws (shiftRawDCTData x n)) :
    PChi { data := shiftRawDCTData x n, laws := hshift } where
  data := shiftPChiData x pchi n
  laws := shiftPChiLaws x hx pchi hpchi n hn hshift

/-! ## General theorem checks -/

/-- The shifted data has pointwise-zero parity. -/
example
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (a b c : RawDCTGroup) :
    rawParity (shiftRawDCTData x n) a b c = 0 :=
  rawParity_shiftRawDCTData_eq_zero x hx pchi hpchi n hn a b c

/-- The scalar projection of the completed adapter is pointwise one. -/
example
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n)
    (hshift : RawDCTLaws (shiftRawDCTData x n))
    (a b c e : RawDCTGroup) :
    (shiftPChi x hx pchi hpchi n hn hshift).data.chi a b c e = 1 :=
  shiftPChiData_chi_eq_one x hx pchi hpchi n hn a b c e

end Superfusion.RMod.RawDCT

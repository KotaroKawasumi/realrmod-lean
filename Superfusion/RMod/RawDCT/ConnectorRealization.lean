import Superfusion.GaugeChi.ConnectorFamily
import Superfusion.RMod.RawDCT.RawDCT

/-!
# Semantic realization of a raw connector

This file records the typed bridge between the actual route carriers of a
raw DCT and the existing semantic `GBL`/`GBR` routes.  The semantic connector,
its parity, the carrier maps, and their explicit inverses are data.  All
membership, nonvanishing, inverse, parity, and compatibility assertions are
propositions about that exact data.

No concrete gauge or coefficient table is constructed here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi

/-! ## Route-identification data -/

/-- A semantic connector together with explicit identifications of the two
raw ternary-route carriers with the left- and right-associated gauge routes.

The legacy `ConnectorFamily` is deliberately not stored here because it
mixes its computational fields with proofs. -/
structure ConnectorRealizationData (x : RawDCTData)
    (Γ : DivisionFusionGauge ℝ (ZMod 8)) where
  T : ∀ a b c, GBL Γ a b c →ₗ[ℝ] GBR Γ a b c
  parity : ZMod 8 → ZMod 8 → ZMod 8 → ZMod 2
  leftToSemantic : ∀ a b c, x.T.LeftCarrier a b c → GBL Γ a b c
  leftOfSemantic : ∀ a b c, GBL Γ a b c → x.T.LeftCarrier a b c
  rightToSemantic : ∀ a b c, x.T.RightCarrier a b c → GBR Γ a b c
  rightOfSemantic : ∀ a b c, GBR Γ a b c → x.T.RightCarrier a b c

/-! ## Laws of the exact route identifications -/

/-- The semantic connector is a nonzero homogeneous intertwiner, the route
maps are two-sided identifications, and under them it is exactly the raw
forward connector. -/
structure ConnectorRealizationLaws (x : RawDCTData) (hx : RawDCTLaws x)
    (Γ : DivisionFusionGauge ℝ (ZMod 8))
    (d : ConnectorRealizationData x Γ) : Prop where
  mem : ∀ a b c,
    d.T a b c ∈ gInterSpace ℝ Γ a b c (d.parity a b c)
  ne_zero : ∀ a b c, d.T a b c ≠ 0
  left_of_to : ∀ a b c (m : x.T.LeftCarrier a b c),
    d.leftOfSemantic a b c (d.leftToSemantic a b c m) = m
  left_to_of : ∀ a b c (m : GBL Γ a b c),
    d.leftToSemantic a b c (d.leftOfSemantic a b c m) = m
  right_of_to : ∀ a b c (m : x.T.RightCarrier a b c),
    d.rightOfSemantic a b c (d.rightToSemantic a b c m) = m
  right_to_of : ∀ a b c (m : GBR Γ a b c),
    d.rightToSemantic a b c (d.rightOfSemantic a b c m) = m
  parity : ∀ a b c, x.T.parity a b c = d.parity a b c
  hom_comm : ∀ a b c (m : x.T.LeftCarrier a b c),
    d.rightToSemantic a b c (x.T.hom a b c m) =
      d.T a b c (d.leftToSemantic a b c m)

/-! ## Completed realization -/

/-- A completed semantic realization of the raw connector of `X`. -/
structure ConnectorRealization (X : RawDCT)
    (Γ : DivisionFusionGauge ℝ (ZMod 8)) where
  data : ConnectorRealizationData X.data Γ
  laws : ConnectorRealizationLaws X.data X.laws Γ data

namespace ConnectorRealization

variable {X : RawDCT} {Γ : DivisionFusionGauge ℝ (ZMod 8)}

/-! ## Derived exact identifications -/

/-- The stored maps give an explicit equivalence with the semantic left
route; no inverse is selected by choice. -/
def leftEquiv (R : ConnectorRealization X Γ) (a b c : ZMod 8) :
    X.data.T.LeftCarrier a b c ≃ GBL Γ a b c where
  toFun := R.data.leftToSemantic a b c
  invFun := R.data.leftOfSemantic a b c
  left_inv := R.laws.left_of_to a b c
  right_inv := R.laws.left_to_of a b c

/-- The stored maps give an explicit equivalence with the semantic right
route; no inverse is selected by choice. -/
def rightEquiv (R : ConnectorRealization X Γ) (a b c : ZMod 8) :
    X.data.T.RightCarrier a b c ≃ GBR Γ a b c where
  toFun := R.data.rightToSemantic a b c
  invFun := R.data.rightOfSemantic a b c
  left_inv := R.laws.right_of_to a b c
  right_inv := R.laws.right_to_of a b c

/-- Compatibility of the explicit raw inverse follows from forward
compatibility and the stored two-sided inverse law of `T`. -/
theorem inv_comm (R : ConnectorRealization X Γ) (a b c : ZMod 8)
    (m : X.data.T.RightCarrier a b c) :
    R.data.T a b c
        (R.data.leftToSemantic a b c (X.data.T.inv a b c m)) =
      R.data.rightToSemantic a b c m := by
  rw [← R.laws.hom_comm, X.laws.T.hom_inv_id]

/-! ## Adapter to the existing semantic API -/

/-- Package separated realization data and laws for the legacy
`ConnectorFamily` API without first bundling either dependency. -/
def toConnectorFamilyOfData {x : RawDCTData} {hx : RawDCTLaws x}
    {Γ : DivisionFusionGauge ℝ (ZMod 8)}
    (d : ConnectorRealizationData x Γ)
    (h : ConnectorRealizationLaws x hx Γ d) : ConnectorFamily ℝ Γ where
  T := d.T
  parity := d.parity
  mem := h.mem
  ne_zero := h.ne_zero

/-- Package the separated realization fields for the legacy
`ConnectorFamily` API. -/
def toConnectorFamily (R : ConnectorRealization X Γ) : ConnectorFamily ℝ Γ :=
  toConnectorFamilyOfData R.data R.laws

end ConnectorRealization

end Superfusion.RMod.RawDCT

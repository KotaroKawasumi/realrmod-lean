/-
Superfusion / GaugeChi / ConnectorFamily

**Connector families**: an assignment, to every triple of labels, of a
nonzero intertwiner in the canonical triple space `gInterSpace`, at a
declared parity.  This is the thin abstraction shared by the canonical
(choice-produced) connectors `gTCanon` and any explicit certificate
family; it is deliberately a wrapper around the existing `gInterSpace`
API and introduces no new conditions.

Main results:

* `ConnectorFamily.parity_eq` — the declared parity of a family is forced
  to be `gParity` (`gParity_unique`).  For a family whose parity field is
  a certificate table this IS the parity identification `hp`.
* `ConnectorFamily.canonical` — `gTCanon` as a family.
* `gInterSpace_spanning` — the triple intertwiner space at `gParity` is
  spanned by any nonzero member (packaging of `parityConcentration`).
* `ConnectorFamily.ratio` / `ratio_spec` — two families differ by a
  unit-valued 3-cochain: `C'.T = ρ • C.T` pointwise
  (`connector_ratio_exists`/`connector_ratio_spec` of the design memo).
-/
import Superfusion.GaugeChi.ChiCanon

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-! ### The spanning lemma -/

/-- **The triple intertwiner space at `gParity` is spanned by any nonzero
member**: `gInterSpace_eq_gradedHomF` + `gradedHomF_sum_le_one` +
`parityConcentration`. -/
theorem gInterSpace_spanning {x y z : G} {t s : GBL Γ x y z →ₗ[K] GBR Γ x y z}
    (ht : t ∈ gInterSpace K Γ x y z (gParity K Γ x y z))
    (hs : s ∈ gInterSpace K Γ x y z (gParity K Γ x y z)) (hsne : s ≠ 0) :
    ∃ k : K, t = k • s := by
  haveI := gbl_finite K Γ x y z
  haveI := gbr_finite K Γ x y z
  have hle := gradedHomF_sum_le_one K Γ x y z
  have hspec := gParity_spec K Γ x y z
  rw [gInterSpace_eq_gradedHomF] at hspec ht hs
  obtain ⟨-, -, hspan⟩ := parityConcentration (GBL.grading Γ x y z) (gEnvGrading K Γ x y z)
    (GBR.grading Γ x y z) hle hspec
  exact hspan t ht s hs hsne

/-! ### Connector families -/

/-- A **connector family** on `Γ`: a nonzero intertwiner in the canonical
triple space at every triple of labels, at a declared parity.  The parity
field is data (for a certificate family it is a table); it is forced to
equal `gParity` by `parity_eq`. -/
structure ConnectorFamily where
  /-- The intertwiner at each triple. -/
  T : ∀ x y z : G, GBL Γ x y z →ₗ[K] GBR Γ x y z
  /-- The declared parity of each intertwiner. -/
  parity : G → G → G → ZMod 2
  /-- Full membership in the five-condition intertwiner space. -/
  mem : ∀ x y z : G, T x y z ∈ gInterSpace K Γ x y z (parity x y z)
  /-- Nonvanishing. -/
  ne_zero : ∀ x y z : G, T x y z ≠ 0

namespace ConnectorFamily

variable {K Γ}
variable (C : ConnectorFamily K Γ)

/-- **The declared parity is `gParity`** — the witness-determination
consequence of `gParity_unique`.  For a family built from a certificate
table this is precisely the parity identification. -/
theorem parity_eq (x y z : G) : C.parity x y z = gParity K Γ x y z :=
  gParity_unique K Γ x y z
    ((Submodule.ne_bot_iff _).mpr ⟨C.T x y z, C.mem x y z, C.ne_zero x y z⟩)

/-- Membership restated at `gParity`. -/
theorem mem_gParity (x y z : G) :
    C.T x y z ∈ gInterSpace K Γ x y z (gParity K Γ x y z) :=
  C.parity_eq x y z ▸ C.mem x y z

/-- Every member of a family is bijective (Schur). -/
theorem bijective (x y z : G) : Function.Bijective (C.T x y z) :=
  gIntertwiner_bijective K Γ x y z (C.mem_gParity x y z) (C.ne_zero x y z)

/-- The family member as a linear equivalence. -/
noncomputable def equiv (x y z : G) : GBL Γ x y z ≃ₗ[K] GBR Γ x y z :=
  LinearEquiv.ofBijective (C.T x y z) (C.bijective x y z)

@[simp] theorem equiv_toLinearMap (x y z : G) :
    (C.equiv x y z).toLinearMap = C.T x y z := rfl

/-! ### The slot conditions, extracted (the shapes `gChi` consumes) -/

/-- The right-slot (op) equivariance of a family member. -/
theorem right_equivariance (x y z : G) :
    ∀ (τ : (Γ.D (x + y + z)).carrier) (m : GBL Γ x y z),
      C.T x y z (MulOpposite.op τ • m) = MulOpposite.op τ • C.T x y z m :=
  (mem_rightSemilinear
      (ψ := (Γ.gaugeCast (add_assoc x y z)).toAlgEquiv.toAlgHom.toRingHom)).mp
    ((mem_gInterSpace_iff K Γ x y z).mp (C.mem_gParity x y z)).2.2.2.2

/-- The signed first-slot equivariance of the family member at
`(x + y, z, w)` — the `t₄`-shape of `gBotRoute`. -/
theorem slotFour (x y z w : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (x + y)).carrier⦄,
      τ ∈ (Γ.D (x + y)).grading i → ∀ n : GBL Γ (x + y) z w,
        C.T (x + y) z w (τ • n)
          = ((sgn (gParity K Γ (x + y) z w * i) : ℤˣ) : ℤ) • (τ • C.T (x + y) z w n) :=
  (mem_superEquivariant (Γ.D (x + y)).grading).mp
    ((mem_gInterSpace_iff K Γ (x + y) z w).mp (C.mem_gParity (x + y) z w)).2.1

/-- The signed third-slot equivariance of the family member at
`(x, y, z + w)` — the `t₅`-shape of `gBotRoute`. -/
theorem slotFive (x y z w : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (z + w)).carrier⦄,
      τ ∈ (Γ.D (z + w)).grading i → ∀ n : GBL Γ x y (z + w),
        C.T x y (z + w) (τ • n)
          = ((sgn (gParity K Γ x y (z + w) * i) : ℤˣ) : ℤ) • (τ • C.T x y (z + w) n) :=
  (mem_superEquivariant (Γ.D (z + w)).grading).mp
    ((mem_gInterSpace_iff K Γ x y (z + w)).mp (C.mem_gParity x y (z + w))).2.2.2.1

/-! ### The canonical family -/

variable (K Γ)

/-- **The canonical connector family**: `gTCanon` at every triple. -/
noncomputable def canonical : ConnectorFamily K Γ where
  T x y z := (gTCanon K Γ x y z).toLinearMap
  parity := gParity K Γ
  mem := gTCanon_mem_gInterSpace K Γ
  ne_zero x y z := by
    haveI := gbl_nontrivial K Γ x y z
    exact linearMap_ne_zero_of_bijective K (gTCanon K Γ x y z).bijective

@[simp] theorem canonical_T (x y z : G) :
    (canonical K Γ).T x y z = (gTCanon K Γ x y z).toLinearMap := rfl

variable {K Γ}

/-! ### The ratio of two families -/

/-- The spanning coefficient of `C'.T` against `C.T`, as a scalar. -/
private noncomputable def ratioAux (C C' : ConnectorFamily K Γ) (x y z : G) : K :=
  (gInterSpace_spanning K Γ (C'.mem_gParity x y z) (C.mem_gParity x y z)
    (C.ne_zero x y z)).choose

private theorem ratioAux_spec (C C' : ConnectorFamily K Γ) (x y z : G) :
    C'.T x y z = ratioAux C C' x y z • C.T x y z :=
  (gInterSpace_spanning K Γ (C'.mem_gParity x y z) (C.mem_gParity x y z)
    (C.ne_zero x y z)).choose_spec

private theorem ratioAux_ne_zero (C C' : ConnectorFamily K Γ) (x y z : G) :
    ratioAux C C' x y z ≠ 0 := by
  intro h0
  exact C'.ne_zero x y z (by rw [ratioAux_spec C C' x y z, h0, zero_smul])

/-- **The ratio of two connector families**: the unit-valued 3-cochain `ρ`
with `C'.T = ρ • C.T` pointwise (`connector_ratio_exists`).  Produced by
choice from the one-dimensionality of the intertwiner line; no value is
computed. -/
noncomputable def ratio (C C' : ConnectorFamily K Γ) (x y z : G) : Kˣ :=
  Units.mk0 (ratioAux C C' x y z) (ratioAux_ne_zero C C' x y z)

/-- **The defining property of the ratio** (`connector_ratio_spec`). -/
theorem ratio_spec (C C' : ConnectorFamily K Γ) (x y z : G) :
    C'.T x y z = ((ratio C C' x y z : Kˣ) : K) • C.T x y z :=
  ratioAux_spec C C' x y z

end ConnectorFamily

end GaugeChi

end Superfusion

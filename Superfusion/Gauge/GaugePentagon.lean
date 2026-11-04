/-
Superfusion / Gauge / GaugePentagon

Milestone M9-3b of the intrinsic gauge track: **the gauge-level route
comparison intertwiner** — super Skolem–Noether
(`Superfusion.Super.SkolemNoetherIso`) applied to the pair
`(gaugeRouteL, gaugeRouteR')` (M9-3a, `Superfusion.Gauge.GaugeRoutes`),
landing in the common frame `(Γ.D ((a+b)+c)).matrixSuper (gaugeSizeL a b c)`.

This is the gauge-level port of `Superfusion.Super.PentagonParity`'s
`pentagonT`/`pentagonParity`: the Skolem–Noether existence hypotheses
(finite-dimensionality/nontriviality/central-simplicity/graded-simplicity
of both the source triple tensor and the target matrix frame) are
supplied by `Γ`'s per-object fields (`central`, `gradedSimple`, `findim`,
`nontriv`) at the composite index `(a+b)+c`, transferred back to the
source along `gaugeRouteL`, exactly mirroring `pentagonT_exists`'s proof
with `stdTower` replaced by `Γ.D` throughout.

**Reuse note**: `PentagonParity`'s instance-transfer lemmas
(`isSuperCentral_matrixGradingA`/`isGradedSimple_matrixGradingA`, bundled
as `matrixSuper_isSuperCentral`/`matrixSuper_isGradedSimple`) are already
stated for a *general* coefficient `SuperAlgebra K` — not hardwired to
`stdTower` — so they are reused directly here with no restatement, as are
`isHomogeneousHom_of_map_grading` (`PentagonParity`) and
`isSuperCentral_of_equiv`/`isGradedSimple_of_equiv`
(`Superfusion.Super.GradedTransfer`).

**Contents:**

* `gaugeSizeL_total`/`gaugeSizeL_ne_zero`: the composite size of the left
  route is nonzero — a product of the two nonzero factor sizes
  (`DivisionFusionGauge.size_pos`), needed for the target matrix index
  type to be nonempty.
* `gaugePentagonT_exists`: the Skolem–Noether existence statement for the
  pair `(gaugeRouteL, gaugeRouteR')`.
* `gaugePentagonT`/`gaugeParity`: the extracted intertwiner and its
  parity.
* `gaugePentagonT_mem`/`gaugePentagonT_isUnit`/`gaugePentagonT_intertwines`:
  the three-point spec, in `PentagonParity.pentagonT_mem`/`_isUnit`/
  `_intertwines`'s exact orientation (`routeL ↦ gaugeRouteL`,
  `routeR ↦ gaugeRouteR'`).
-/
import Superfusion.Gauge.GaugeRoutes
import Superfusion.Super.PentagonParity

namespace Superfusion

namespace DivisionFusionGauge

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)] {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

/-! ### Positivity of the composite left-route size -/

/-- The composite size of the left route is the product of the two factor
sizes, in cross-multiplied `matrixSuperComp` form. -/
theorem gaugeSizeL_total (a b c : G) :
    (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2
      = ((Γ.size a b).1 + (Γ.size a b).2)
          * ((Γ.size (a + b) c).1 + (Γ.size (a + b) c).2) := by
  simp only [gaugeSizeL]
  ring

/-- The composite left-route size is nonzero: a product of the two
nonzero factor sizes (`size_pos`). -/
theorem gaugeSizeL_ne_zero (a b c : G) :
    (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2 ≠ 0 := by
  rw [Γ.gaugeSizeL_total]
  exact Nat.mul_ne_zero (Γ.size_pos a b) (Γ.size_pos (a + b) c)

/-! ### The Skolem–Noether existence statement -/

/-- The Skolem–Noether existence statement for the two gauge-level
fusion routes (M9-3b): hypotheses transferred back along `gaugeRouteL`
from the matrix superalgebra target, whose central simplicity comes from
`Γ`'s per-object fields (`central`, `gradedSimple`) at the composite
index `(a+b)+c`. Literal port of `PentagonParity.pentagonT_exists`. -/
theorem gaugePentagonT_exists (a b c : G) :
    ∃ (p : ZMod 2)
      (t : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
        (Γ.gaugeSizeL a b c).2).carrier),
      t ∈ ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
        (Γ.gaugeSizeL a b c).2).grading p ∧ IsUnit t ∧
      ∀ ⦃j : ZMod 2⦄
        ⦃x : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
        x ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
        (Γ.gaugeRouteR' a b c).toAlgEquiv x * t
          = ((sgn (j * p) : ℤˣ) : ℤ) • (t * (Γ.gaugeRouteL a b c).toAlgEquiv x) := by
  classical
  set A : SuperAlgebra K :=
    ((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c) with hA
  set B : SuperAlgebra K :=
    (Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2
    with hB
  haveI := Γ.findim (a + b + c)
  haveI := Γ.nontriv (a + b + c)
  -- the target is a matrix superalgebra over `Γ.D (a+b+c)`: finite-
  -- dimensional, nontrivial, supercentral, graded simple
  haveI hBfd : FiniteDimensional K B.carrier := by
    exact inferInstanceAs (Module.Finite K
      (Matrix _ _ (Γ.D (a + b + c)).carrier))
  haveI hBne : Nonempty (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) := by
    have h := Γ.gaugeSizeL_ne_zero a b c
    by_cases h1 : (Γ.gaugeSizeL a b c).1 = 0
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, by omega⟩⟩
  haveI hBnt : Nontrivial B.carrier := by
    exact inferInstanceAs (Nontrivial
      (Matrix _ _ (Γ.D (a + b + c)).carrier))
  haveI hBsc : IsSuperCentral B.grading :=
    matrixSuper_isSuperCentral (Γ.D (a + b + c)) _ _ (Γ.central (a + b + c))
  haveI hBgs : IsGradedSimple B.grading :=
    matrixSuper_isGradedSimple (Γ.D (a + b + c)) _ _ (Γ.gradedSimple (a + b + c))
  -- transfer back along `gaugeRouteL` to the triple tensor source
  haveI hAfd : FiniteDimensional K A.carrier :=
    Module.Finite.equiv (Γ.gaugeRouteL a b c).toAlgEquiv.symm.toLinearEquiv
  haveI hAnt : Nontrivial A.carrier :=
    (Γ.gaugeRouteL a b c).toAlgEquiv.symm.injective.nontrivial
  haveI hAsc : IsSuperCentral A.grading :=
    isSuperCentral_of_equiv B.grading A.grading
      (Γ.gaugeRouteL a b c).toAlgEquiv.symm
      (Γ.gaugeRouteL a b c).symm.map_grading
  haveI hAgs : IsGradedSimple A.grading :=
    isGradedSimple_of_equiv B.grading A.grading
      (Γ.gaugeRouteL a b c).toAlgEquiv.symm
      (Γ.gaugeRouteL a b c).symm.map_grading
  exact superSkolemNoether_exists_of_surjective A.grading B.grading
    (Γ.gaugeRouteL a b c).toAlgEquiv.toAlgHom (Γ.gaugeRouteR' a b c).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _ (Γ.gaugeRouteL a b c).map_grading)
    (isHomogeneousHom_of_map_grading _ (Γ.gaugeRouteR' a b c).map_grading)
    (Γ.gaugeRouteL a b c).toAlgEquiv.surjective
    (Γ.gaugeRouteR' a b c).toAlgEquiv.surjective

/-- **The gauge-level parity 3-cochain** (M9-3b): the parity of the
route intertwiner — the abstract analogue of `PentagonParity.pentagonParity`. -/
noncomputable def gaugeParity (a b c : G) : ZMod 2 :=
  (Γ.gaugePentagonT_exists a b c).choose

/-- **The gauge-level route intertwiner** `T_{a,b,c}` — the abstract
analogue of `PentagonParity.pentagonT`. -/
noncomputable def gaugePentagonT (a b c : G) :
    ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier :=
  (Γ.gaugePentagonT_exists a b c).choose_spec.choose

theorem gaugePentagonT_mem (a b c : G) :
    Γ.gaugePentagonT a b c
      ∈ ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
        (Γ.gaugeSizeL a b c).2).grading (Γ.gaugeParity a b c) :=
  (Γ.gaugePentagonT_exists a b c).choose_spec.choose_spec.1

theorem gaugePentagonT_isUnit (a b c : G) :
    IsUnit (Γ.gaugePentagonT a b c) :=
  (Γ.gaugePentagonT_exists a b c).choose_spec.choose_spec.2.1

theorem gaugePentagonT_intertwines (a b c : G) :
    ∀ ⦃j : ZMod 2⦄
      ⦃x : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      x ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv x * Γ.gaugePentagonT a b c
        = ((sgn (j * Γ.gaugeParity a b c) : ℤˣ) : ℤ)
          • (Γ.gaugePentagonT a b c * (Γ.gaugeRouteL a b c).toAlgEquiv x) :=
  (Γ.gaugePentagonT_exists a b c).choose_spec.choose_spec.2.2

end DivisionFusionGauge

end Superfusion

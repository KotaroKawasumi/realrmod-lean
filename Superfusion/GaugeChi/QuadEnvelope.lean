/-
Superfusion / GaugeChi / QuadEnvelope

Milestone M12-5 of the abstract `(p, χ)` arc (SN-FREE DESIGN): **the
quadruple envelope algebra** `gQuadEnv Γ a b c d` — the Γ-mirror of
`Superfusion.Bimod.PentagonB.QuadEnv` (`Bimod.QuadEnvelope`), one gtensor
level up from `GaugeChi.InterSpace`'s `gTripleEnv`.

1. **The composite quadruple route** `gQuadRoute1`: chaining the
   already-assembled triple route `Γ.gaugeRouteL a b c`
   (`Superfusion.Gauge.GaugeRoutes`) with one further fuse step at
   `(a+b+c, d)`, exactly the pattern `Γ.gaugeRouteL` itself uses to chain
   two fuse steps — `gtensorCongr` against the identity on `D_d`, the
   matrix pull-out `matrixSuperGtensor`, the entrywise lift
   `(Γ.fuse (a+b+c) d).matrixSuper`, and the nested-matrix collapse
   `matrixSuperComp`. Since `+` left-associates, `a+b+c+d` is literally
   `(a+b+c)+d`, so no cast is needed anywhere in the chain — `gQuadRoute1`
   lands exactly at `Γ.D (a+b+c+d)`, matching `GQ1`'s own right-coefficient
   tower (`GaugeChi.Pentagon`/`PentagonActions`) on the nose.

2. **`gQuadEnv Γ a b c d`**: the 4-fold gtensor `((D_a ᵍ⊗ D_b) ᵍ⊗ D_c) ᵍ⊗
   D_d` enveloped (`Bimod.Envelope`) with the super-opposite of
   `D_{a+b+c+d}` — finite-dimensional, and its splitting
   `gQuadEnvSplit : gQuadEnv Γ a b c d ≃ₐ[K] Matrix (Fin gQuadEnvSize)
   (Fin gQuadEnvSize) K`, chained through `gQuadRoute1`, the matrix
   pull-out, the Wall-map splitting of `D_{a+b+c+d}` (from
   `DivisionFusionGauge.instIsSuperAzumayaD`, `Superfusion.Gauge.DBW`), and
   the nested-matrix collapse/reindex — exactly `gTripleEnv`'s own
   splitting chain, one gtensor level up. `gQuadEnvSize_ne_zero` is
   supplied.
-/
import Superfusion.GaugeChi.InterSpace

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

/-! ### The composite quadruple route -/

/-- The composed matrix size of the quadruple route: the outer
`Γ.gaugeSizeL a b c` (the `(a+b)+c`-frame's own composite split) applied
to the inner `Γ.size (a+b+c) d`, in `matrixSuperComp`'s convention —
literally `gaugeSizeL`'s own formula, one level up. -/
def gQuadSizeL (a b c d : G) : ℕ × ℕ :=
  ((Γ.gaugeSizeL a b c).1 * (Γ.size (a + b + c) d).1
      + (Γ.gaugeSizeL a b c).2 * (Γ.size (a + b + c) d).2,
    (Γ.gaugeSizeL a b c).1 * (Γ.size (a + b + c) d).2
      + (Γ.gaugeSizeL a b c).2 * (Γ.size (a + b + c) d).1)

/-- **The quadruple fusion route**, at its natural frame `a+b+c+d`:
`((D_a ᵍ⊗ D_b) ᵍ⊗ D_c) ᵍ⊗ D_d ≅ M_{σ}(D_{a+b+c+d})` through `((ab)c)d` —
`Γ.gaugeRouteL a b c` chained with one further fuse step at `(a+b+c, d)`. -/
noncomputable def gQuadRoute1 (a b c d : G) :
    SuperAlgEquiv ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d))
      ((Γ.D (a + b + c + d)).matrixSuper (gQuadSizeL K Γ a b c d).1 (gQuadSizeL K Γ a b c d).2) :=
  ((Γ.gaugeRouteL a b c).gtensorCongr (SuperAlgEquiv.refl (Γ.D d))).trans
    ((matrixSuperGtensor (Γ.D (a + b + c)) (Γ.D d) (Γ.gaugeSizeL a b c).1
        (Γ.gaugeSizeL a b c).2).trans
      (((Γ.fuse (a + b + c) d).matrixSuper (Γ.gaugeSizeL a b c).1
          (Γ.gaugeSizeL a b c).2).trans
        (matrixSuperComp (Γ.D (a + b + c + d)) (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2
          (Γ.size (a + b + c) d).1 (Γ.size (a + b + c) d).2)))

/-! ### The quadruple envelope algebra -/

/-- **`gQuadEnv Γ a b c d`** (mirrors `Bimod.PentagonB.QuadEnv`, the
Γ-mirror one gtensor level up from `gTripleEnv`): the 4-fold gtensor
`((D_a ᵍ⊗ D_b) ᵍ⊗ D_c) ᵍ⊗ D_d` enveloped (`Bimod.Envelope`) with the
super-opposite of the total coefficient representative `D_{a+b+c+d}` —
matching `GQ1`'s own right-coefficient tower exactly. -/
noncomputable abbrev gQuadEnv : Type _ :=
  Envelope ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
    (Γ.D (a + b + c + d)).grading

noncomputable instance : FiniteDimensional K (gQuadEnv K Γ a b c d) := by
  haveI : Module.Finite K (SuperOp (Γ.D (a + b + c + d)).grading) :=
    Module.Finite.equiv (SuperOp.op (Γ.D (a + b + c + d)).grading)
  exact Module.Finite.equiv
    (GradedTensorProduct.of K ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (SuperOp.grading (Γ.D (a + b + c + d)).grading))

/-! ### Splitness -/

section Split

/-- The `K`-dimension of the coefficient representative `D_{a+b+c+d}`. -/
private noncomputable abbrev gQuadRank : ℕ :=
  Module.finrank K (Γ.D (a + b + c + d)).carrier

/-- The Fintype index collapsing the nested matrix structure of the
splitting chain: the quadruple-route frame index times `D_{a+b+c+d}`'s
own `K`-basis index. -/
private abbrev gQuadEnvIdx : Type :=
  (Fin (gQuadSizeL K Γ a b c d).1 ⊕ Fin (gQuadSizeL K Γ a b c d).2) × Fin (gQuadRank K Γ a b c d)

/-- **The size of the matrix algebra splitting `gQuadEnv`.** -/
noncomputable def gQuadEnvSize : ℕ :=
  Fintype.card (gQuadEnvIdx K Γ a b c d)

/-- The composite quadruple-route size is the product of the two factor
sizes' totals (pure `ℕ`-arithmetic unfolding of `gQuadSizeL`'s
definition). -/
private theorem gQuadSizeL_total :
    (gQuadSizeL K Γ a b c d).1 + (gQuadSizeL K Γ a b c d).2
      = ((Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2)
          * ((Γ.size (a + b + c) d).1 + (Γ.size (a + b + c) d).2) := by
  show (Γ.gaugeSizeL a b c).1 * (Γ.size (a + b + c) d).1
      + (Γ.gaugeSizeL a b c).2 * (Γ.size (a + b + c) d).2
      + ((Γ.gaugeSizeL a b c).1 * (Γ.size (a + b + c) d).2
        + (Γ.gaugeSizeL a b c).2 * (Γ.size (a + b + c) d).1)
    = _
  ring

theorem gQuadEnvSize_ne_zero : gQuadEnvSize K Γ a b c d ≠ 0 := by
  haveI : Nonempty (Fin (gQuadSizeL K Γ a b c d).1 ⊕ Fin (gQuadSizeL K Γ a b c d).2) := by
    have htotL : (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2 ≠ 0 := by
      have h : (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2
          = ((Γ.size a b).1 + (Γ.size a b).2) * ((Γ.size (a + b) c).1 + (Γ.size (a + b) c).2) := by
        show (Γ.size a b).1 * (Γ.size (a + b) c).1 + (Γ.size a b).2 * (Γ.size (a + b) c).2
            + ((Γ.size a b).1 * (Γ.size (a + b) c).2 + (Γ.size a b).2 * (Γ.size (a + b) c).1)
          = _
        ring
      rw [h]
      exact Nat.mul_ne_zero (Γ.size_pos a b) (Γ.size_pos (a + b) c)
    have htot : (gQuadSizeL K Γ a b c d).1 + (gQuadSizeL K Γ a b c d).2 ≠ 0 := by
      rw [gQuadSizeL_total]
      exact Nat.mul_ne_zero htotL (Γ.size_pos (a + b + c) d)
    rw [← Fintype.card_pos_iff, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact Nat.pos_of_ne_zero htot
  haveI : Nonempty (Fin (gQuadRank K Γ a b c d)) := by
    have hpos : 0 < gQuadRank K Γ a b c d :=
      Module.finrank_pos (R := K) (M := (Γ.D (a + b + c + d)).carrier)
    exact Fin.pos_iff_nonempty.mp hpos
  exact Fintype.card_ne_zero

/-- **The Wall-map splitting of `D_{a+b+c+d}`**, `D_{a+b+c+d} ᵍ⊗
D_{a+b+c+d}^sop ≅ Matrix (Fin gQuadRank) (Fin gQuadRank) K`: bijective
since `D_{a+b+c+d}` is super-Azumaya
(`DivisionFusionGauge.instIsSuperAzumayaD`, a global instance of
`Superfusion.Gauge.DBW`), then a chosen `K`-basis turns
`End_K(D_{a+b+c+d})` into a matrix algebra. -/
noncomputable def gQuadWallSplit :
    SuperEnvelope (Γ.D (a + b + c + d)).grading ≃ₐ[K]
      Matrix (Fin (gQuadRank K Γ a b c d)) (Fin (gQuadRank K Γ a b c d)) K :=
  (AlgEquiv.ofBijective (superMulLeftRight (Γ.D (a + b + c + d)).grading)
      (DivisionFusionGauge.instIsSuperAzumayaD Γ (a + b + c + d)).bij).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K (Γ.D (a + b + c + d)).carrier))

/-- **`gQuadEnv` splits**: the explicit chain of `gQuadRoute1` (turning the
source into the quadruple-route frame), the matrix pull-out
`matrixSuperGtensor`, the Wall-map splitting of `D_{a+b+c+d}`
(`gQuadWallSplit`), and the nested-matrix collapse/reindex
(`Matrix.compAlgEquiv`, `Matrix.reindexAlgEquiv`). -/
noncomputable def gQuadEnvSplit :
    gQuadEnv K Γ a b c d ≃ₐ[K]
      Matrix (Fin (gQuadEnvSize K Γ a b c d)) (Fin (gQuadEnvSize K Γ a b c d)) K :=
  ((gQuadRoute1 K Γ a b c d).gtensorCongr
      (SuperAlgEquiv.refl ((Γ.D (a + b + c + d)).sop))).toAlgEquiv.trans
    ((matrixSuperGtensor (Γ.D (a + b + c + d)) ((Γ.D (a + b + c + d)).sop)
        (gQuadSizeL K Γ a b c d).1 (gQuadSizeL K Γ a b c d).2).toAlgEquiv.trans
      ((AlgEquiv.mapMatrix (gQuadWallSplit K Γ a b c d)).trans
        ((Matrix.compAlgEquiv (Fin (gQuadSizeL K Γ a b c d).1 ⊕ Fin (gQuadSizeL K Γ a b c d).2)
            (Fin (gQuadRank K Γ a b c d)) K K).trans
          (Matrix.reindexAlgEquiv K K (Fintype.equivFin (gQuadEnvIdx K Γ a b c d))))))

end Split

end GaugeChi

end Superfusion

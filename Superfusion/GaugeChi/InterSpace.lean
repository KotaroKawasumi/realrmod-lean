/-
Superfusion / GaugeChi / InterSpace

Milestone M12-2 of the abstract `(p, χ)` arc (SN-FREE DESIGN): **the triple
intertwiner space** `gInterSpace Γ a b c d` — the Γ-mirror of
`Superfusion.Bimod.Intertwiner.interSpace` (M8a-8a) — together with **the
triple envelope algebra** `gTripleEnv Γ a b c`, its splitting, and the
resulting dimension count `finrank GBL = finrank GBR = gTripleEnvSize`.

`gParity Γ a b c`, the canonical concentrated parity (the paper's `p`, the
parity of the Hom super-line), and the abstract existence/bijectivity of a
nonzero intertwiner, are **not** reached this round: they need the full
interface `mem_gInterSpace_iff_gradedHomF` connecting `gInterSpace` to
`Superfusion.Bimod.ParityBridge.gradedHomF` (the layer where
`SplitIsotypy`/`ParityBridge`'s machinery actually applies), which in turn
needs `GBR` to carry a `gTripleEnv`-module structure matching `GBL`'s own
bracket `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c` exactly.  Unlike `GBL` (whose natural combined
action already has this shape, mirroring
`Superfusion.Bimod.QuadEnvModule`'s `BL`-level lift), `GBR`'s natural
combined action has the shape `(D_b ᵍ⊗ D_c) ᵍ⊗ D_a` — the *same*
bracket-association mismatch that `QuadEnvModule.lean` documents as the
reason `Q4`'s (the pentagon-level analogue of `GBR`) matching module
structure was left unbuilt.  Reconciling the two brackets needs an explicit
`gtensorAssoc`/`gtensorComm` algebra isomorphism transporting `GBR`'s own
module structure, *and* a full re-derivation of `QuadInterface.lean`/
`QuadInterface2.lean`'s sign bookkeeping at the reconciled action — out of
scope for this round; see the session report.

What *is* landed:

1. **`gInterSpace Γ a b c d`** (mirrors `Intertwiner.interSpace`): the
   five-condition intersection (`homGrading`, the three slot
   `superEquivariant`s, and `rightSemilinear` along `Γ.gaugeCast
   (add_assoc a b c)`) — together with the `SMulCommClass K _ _` instances
   on `GBL`/`GBR` needed for `superEquivariant`/`rightSemilinear` to
   typecheck (mirrors `Intertwiner.lean`'s `BL`/`BR` sections verbatim).

2. **`gTripleEnv Γ a b c`** (mirrors `QuadEnvelope.QuadEnv`, one gtensor
   level down): the envelope algebra `Envelope ((D_a ᵍ⊗ D_b) ᵍ⊗ D_c).grading
   D_{a+b+c}.grading`, finite-dimensional, and its splitting
   `gTripleEnvSplit : gTripleEnv Γ a b c ≃ₐ[K] Matrix (Fin gTripleEnvSize)
   (Fin gTripleEnvSize) K` — chained through `Γ.gaugeRouteL a b c` (the
   *already-assembled* composite route of `Superfusion.Gauge.GaugeRoutes`,
   in the role `QuadEnvelope.lean`'s `quadRoute1` plays), the matrix
   pull-out `matrixSuperGtensor`, the Wall-map splitting of `D_{a+b+c}`
   (`gTripleWallSplit`, from `IsSuperAzumaya`, a global instance of
   `Superfusion.Gauge.DBW`), and the nested-matrix collapse/reindex.
   `gTripleEnvSize_ne_zero` is supplied.

3. **The dimension count** `finrank_GBL_eq_gTripleEnvSize`/
   `finrank_GBR_eq_gTripleEnvSize`: both `GBL`/`GBR` collapse directly via
   `RelTensor.freeCollapse` (their first factor, a `FusionColumn`, is
   literally a free column type) to a product-indexed column over their own
   natural right-coefficient tower (`D_{a+b+c}` for `GBL`, `D_{a+(b+c)}` for
   `GBR`) — mirroring `ChiTower.lean`'s `q1FirstCollapse` pattern exactly,
   but landing at BOTH vertices independently (no `botRoute`-style shortcut
   needed).  The two natural right towers' dimensions agree
   (`Γ.gaugeCast (add_assoc a b c)`), and the two natural composite sizes'
   *totals* agree by `Superfusion.sizeRigidity_total` applied to
   `Γ.frameAlign a b c` — assembling both dimension counts against the same
   `gTripleEnvSize`.
-/
import Superfusion.GaugeChi.RouteBimod
import Superfusion.Bimod.HomGrading
import Superfusion.Bimod.FreeCollapse
import Superfusion.Gauge.GaugeRoutes
import Superfusion.Gauge.DBW
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

/-! ### Scalars commute with the slot and right actions -/

namespace GBL

instance : SMulCommClass K (Γ.D a).carrier (GBL Γ a b c) :=
  ⟨fun k x w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) x) k w).symm⟩

instance : SMulCommClass K (Γ.D b).carrier (GBL Γ a b c) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) y) k w).symm⟩

instance : SMulCommClass K (Γ.D c).carrier (GBL Γ a b c) :=
  ⟨fun k z w => (LinearMap.map_smul
    (midAlgHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) z) k w).symm⟩

instance : SMulCommClass K ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  ⟨fun k d w => (LinearMap.map_smul
    (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) d) k w).symm⟩

end GBL

namespace GBR

instance : SMulCommClass K (Γ.D b).carrier (GBR Γ a b c) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))) y) k w).symm⟩

instance : SMulCommClass K (Γ.D c).carrier (GBR Γ a b c) :=
  ⟨fun k z w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))) z) k w).symm⟩

instance : SMulCommClass K (Γ.D a).carrier (GBR Γ a b c) :=
  ⟨fun k x w => (LinearMap.map_smul
    (midAlgHom (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
      (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
        (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x) k w).symm⟩

instance : SMulCommClass K ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun k d w => (LinearMap.map_smul
    (rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))) d) k w).symm⟩

end GBR

/-! ### The triple intertwiner space -/

/-- **The degree-`d` triple intertwiner space** `Hom_d(GBL, GBR)` (§4.1, the
Γ-mirror of `Bimod.Intertwiner.interSpace`): homogeneous of degree `d`,
super-equivariant for the three slot actions of `D_a`, `D_b`, `D_c`,
right-linear along the associativity identification of the coefficient
representatives (`Γ.gaugeCast (add_assoc a b c)`). -/
noncomputable def gInterSpace (d : ZMod 2) :
    Submodule K (GBL Γ a b c →ₗ[K] GBR Γ a b c) :=
  homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c) d
    ⊓ superEquivariant (Γ.D a).grading d
    ⊓ superEquivariant (Γ.D b).grading d
    ⊓ superEquivariant (Γ.D c).grading d
    ⊓ rightSemilinear ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom)

/-- Membership unfolded: the five conditions of §4.1. -/
theorem mem_gInterSpace_iff {d : ZMod 2} {f : GBL Γ a b c →ₗ[K] GBR Γ a b c} :
    f ∈ gInterSpace K Γ a b c d ↔
      f ∈ homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c) d
      ∧ f ∈ superEquivariant (Γ.D a).grading d
      ∧ f ∈ superEquivariant (Γ.D b).grading d
      ∧ f ∈ superEquivariant (Γ.D c).grading d
      ∧ f ∈ rightSemilinear ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom) := by
  show f ∈ (_ ⊓ _ ⊓ _ ⊓ _ ⊓ _ : Submodule K _) ↔ _
  simp only [Submodule.mem_inf]
  tauto

/-! ### The triple envelope algebra -/

/-- **`gTripleEnv Γ a b c`** (mirrors `QuadEnvelope.QuadEnv`, one gtensor
level down): the 3-fold gtensor `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c` enveloped
(`Bimod.Envelope`) with the super-opposite of the total coefficient
representative `D_{a+b+c}` — matching `GBL`'s own right-coefficient tower
exactly. -/
noncomputable abbrev gTripleEnv : Type _ :=
  Envelope (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D (a + b + c)).grading

noncomputable instance : FiniteDimensional K (gTripleEnv K Γ a b c) := by
  haveI : Module.Finite K (SuperOp (Γ.D (a + b + c)).grading) :=
    Module.Finite.equiv (SuperOp.op (Γ.D (a + b + c)).grading)
  exact Module.Finite.equiv
    (GradedTensorProduct.of K (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (SuperOp.grading (Γ.D (a + b + c)).grading))

/-! ### Splitness -/

section Split

/-- The `K`-dimension of the coefficient representative `D_{a+b+c}`. -/
private noncomputable abbrev gTripleRank : ℕ :=
  Module.finrank K (Γ.D (a + b + c)).carrier

/-- The Fintype index collapsing the nested matrix structure of the
splitting chain: the left-route frame index times `D_{a+b+c}`'s own
`K`-basis index. -/
private abbrev gTripleEnvIdx : Type :=
  (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) × Fin (gTripleRank K Γ a b c)

/-- **The size of the matrix algebra splitting `gTripleEnv`.** -/
noncomputable def gTripleEnvSize : ℕ :=
  Fintype.card (gTripleEnvIdx K Γ a b c)

/-- The composite left-route size is the product of the two factor sizes'
totals (pure `ℕ`-arithmetic unfolding of `gaugeSizeL`'s definition). -/
private theorem gaugeSizeL_total :
    (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2
      = ((Γ.size a b).1 + (Γ.size a b).2) * ((Γ.size (a + b) c).1 + (Γ.size (a + b) c).2) := by
  show (Γ.size a b).1 * (Γ.size (a + b) c).1 + (Γ.size a b).2 * (Γ.size (a + b) c).2
      + ((Γ.size a b).1 * (Γ.size (a + b) c).2 + (Γ.size a b).2 * (Γ.size (a + b) c).1)
    = _
  ring

theorem gTripleEnvSize_ne_zero : gTripleEnvSize K Γ a b c ≠ 0 := by
  haveI : Nonempty (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) := by
    have htot : (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2 ≠ 0 := by
      rw [gaugeSizeL_total]
      exact Nat.mul_ne_zero (Γ.size_pos a b) (Γ.size_pos (a + b) c)
    rw [← Fintype.card_pos_iff, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact Nat.pos_of_ne_zero htot
  haveI : Nonempty (Fin (gTripleRank K Γ a b c)) := by
    have hpos : 0 < gTripleRank K Γ a b c :=
      Module.finrank_pos (R := K) (M := (Γ.D (a + b + c)).carrier)
    exact Fin.pos_iff_nonempty.mp hpos
  exact Fintype.card_ne_zero

/-- **The Wall-map splitting of `D_{a+b+c}`**, `D_{a+b+c} ᵍ⊗
D_{a+b+c}^sop ≅ Matrix (Fin gTripleRank) (Fin gTripleRank) K`: bijective
since `D_{a+b+c}` is super-Azumaya (`DivisionFusionGauge.instIsSuperAzumayaD`,
a global instance of `Superfusion.Gauge.DBW`), then a chosen `K`-basis turns
`End_K(D_{a+b+c})` into a matrix algebra. -/
noncomputable def gTripleWallSplit :
    SuperEnvelope (Γ.D (a + b + c)).grading ≃ₐ[K]
      Matrix (Fin (gTripleRank K Γ a b c)) (Fin (gTripleRank K Γ a b c)) K :=
  (AlgEquiv.ofBijective (superMulLeftRight (Γ.D (a + b + c)).grading)
      (DivisionFusionGauge.instIsSuperAzumayaD Γ (a + b + c)).bij).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K (Γ.D (a + b + c)).carrier))

/-- **`gTripleEnv` splits**: the explicit chain of `Superfusion.Gauge.
GaugeRoutes`'s already-assembled `Γ.gaugeRouteL a b c` (turning the source
into the left-route frame, in the role `QuadEnvelope.lean`'s `quadRoute1`
plays), the matrix pull-out `matrixSuperGtensor`, the Wall-map splitting of
`D_{a+b+c}` (`gTripleWallSplit`), and the nested-matrix collapse/reindex
(`Matrix.compAlgEquiv`, `Matrix.reindexAlgEquiv`). -/
noncomputable def gTripleEnvSplit :
    gTripleEnv K Γ a b c ≃ₐ[K]
      Matrix (Fin (gTripleEnvSize K Γ a b c)) (Fin (gTripleEnvSize K Γ a b c)) K :=
  ((Γ.gaugeRouteL a b c).gtensorCongr
      (SuperAlgEquiv.refl ((Γ.D (a + b + c)).sop))).toAlgEquiv.trans
    ((matrixSuperGtensor (Γ.D (a + b + c)) ((Γ.D (a + b + c)).sop)
        (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2).toAlgEquiv.trans
      ((AlgEquiv.mapMatrix (gTripleWallSplit K Γ a b c)).trans
        ((Matrix.compAlgEquiv (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
            (Fin (gTripleRank K Γ a b c)) K K).trans
          (Matrix.reindexAlgEquiv K K (Fintype.equivFin (gTripleEnvIdx K Γ a b c))))))

end Split

/-! ### Dimension: `finrank GBL = finrank GBR = gTripleEnvSize` -/

section Dimension

/-- Currying a nested Pi type over a product index, as a `LinearEquiv`
(local copy of `Bimod.ChiTower`'s `piProdCollapse`, general layer). -/
private def piProdCollapse (n₁ n₂ T : Type*) [AddCommMonoid T] [Module K T] :
    (n₁ → n₂ → T) ≃ₗ[K] (n₁ × n₂ → T) where
  toFun f p := f p.1 p.2
  invFun g i j := g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [Invertible (2 : K)] in
/-- `finrank K (n → M) = Fintype.card n * finrank K M` for a `Fintype n` and
finite-dimensional `M` (local copy of `Bimod.ChiTower`'s `finrank_pi_const`). -/
private theorem finrank_pi_const {M : Type*} [AddCommGroup M] [Module K M]
    [Module.Finite K M] (n : Type*) [Fintype n] :
    Module.finrank K (n → M) = Fintype.card n * Module.finrank K M := by
  rw [Module.finrank_pi_fintype K, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **`GBL`'s own collapse**: `GBL = C_{a,b} ⊗_{D_{a+b}} C_{a+b,c} ≅
(idx(a,b) × idx(a+b,c)) → D_{a+b+c}` — `RelTensor.freeCollapse` (the first
factor of `GBL`, a `FusionColumn`, is literally a free column type) followed
by currying the resulting nested Pi type. -/
noncomputable def gblFirstCollapse :
    GBL Γ a b c ≃ₗ[K]
      ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
          (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
        → (Γ.D (a + b + c)).carrier) :=
  RelTensor.freeCollapse.trans
    (piProdCollapse K (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
      (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2) (Γ.D (a + b + c)).carrier)

/-- **`GBR`'s own collapse**, at `GBR`'s own natural right tower
`D_{a+(b+c)}`. -/
noncomputable def gbrFirstCollapse :
    GBR Γ a b c ≃ₗ[K]
      ((Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) ×
          (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
        → (Γ.D (a + (b + c))).carrier) :=
  RelTensor.freeCollapse.trans
    (piProdCollapse K (Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
      (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2) (Γ.D (a + (b + c))).carrier)

/-- **`gTripleEnvSize`'s value, unfolded** to the product of the two factor
sizes' totals times `D_{a+b+c}`'s rank. -/
theorem gTripleEnvSize_eq :
    gTripleEnvSize K Γ a b c
      = ((Γ.size a b).1 + (Γ.size a b).2) * ((Γ.size (a + b) c).1 + (Γ.size (a + b) c).2)
          * Module.finrank K (Γ.D (a + b + c)).carrier := by
  show Fintype.card
      ((Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) × Fin (gTripleRank K Γ a b c))
    = _
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, gaugeSizeL_total]

/-- **`finrank K GBL = gTripleEnvSize K Γ a b c`.** -/
theorem finrank_GBL_eq_gTripleEnvSize :
    Module.finrank K (GBL Γ a b c) = gTripleEnvSize K Γ a b c := by
  rw [(gblFirstCollapse K Γ a b c).finrank_eq, gTripleEnvSize_eq,
    finrank_pi_const K ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
      (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)), Fintype.card_prod,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]

/-- **`GBL` is finite-dimensional** (transported off `gblFirstCollapse`). -/
theorem gbl_finite : Module.Finite K (GBL Γ a b c) :=
  Module.Finite.equiv (gblFirstCollapse K Γ a b c).symm

/-- **`GBL` is nontrivial**: `finrank K GBL = gTripleEnvSize ≠ 0`. -/
theorem gbl_nontrivial : Nontrivial (GBL Γ a b c) := by
  refine Module.nontrivial_of_finrank_pos (R := K) ?_
  rw [finrank_GBL_eq_gTripleEnvSize]
  exact Nat.pos_of_ne_zero (gTripleEnvSize_ne_zero K Γ a b c)

/-- The composite right-route size is the product of the two factor sizes'
totals (pure `ℕ`-arithmetic unfolding of `gaugeSizeR`'s definition, mirroring
`gaugeSizeL_total`). -/
private theorem gaugeSizeR_total :
    (Γ.gaugeSizeR a b c).1 + (Γ.gaugeSizeR a b c).2
      = ((Γ.size b c).1 + (Γ.size b c).2) * ((Γ.size a (b + c)).1 + (Γ.size a (b + c)).2) := by
  show (Γ.size b c).1 * (Γ.size a (b + c)).1 + (Γ.size b c).2 * (Γ.size a (b + c)).2
      + ((Γ.size b c).1 * (Γ.size a (b + c)).2 + (Γ.size b c).2 * (Γ.size a (b + c)).1)
    = _
  ring

/-- **`finrank K GBR = gTripleEnvSize K Γ a b c`**: `GBR`'s own collapse
lands at its own natural right tower `D_{a+(b+c)}`, whose `K`-dimension
agrees with `D_{a+b+c}`'s (`Γ.gaugeCast (add_assoc a b c)`), and whose own
composite size total agrees with `GBL`'s (`Superfusion.sizeRigidity_total`,
applied to the route-independent frame alignment `Γ.frameAlign a b c`). -/
theorem finrank_GBR_eq_gTripleEnvSize :
    Module.finrank K (GBR Γ a b c) = gTripleEnvSize K Γ a b c := by
  have hrank : Module.finrank K (Γ.D (a + (b + c))).carrier
      = Module.finrank K (Γ.D (a + b + c)).carrier :=
    (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toLinearEquiv.finrank_eq.symm
  have htot := sizeRigidity_total (Γ.frameAlign a b c)
  have hsize : ((Γ.size b c).1 + (Γ.size b c).2) * ((Γ.size a (b + c)).1 + (Γ.size a (b + c)).2)
      = ((Γ.size a b).1 + (Γ.size a b).2) * ((Γ.size (a + b) c).1 + (Γ.size (a + b) c).2) := by
    rw [← gaugeSizeR_total, htot, gaugeSizeL_total]
  rw [(gbrFirstCollapse K Γ a b c).finrank_eq, gTripleEnvSize_eq,
    finrank_pi_const K ((Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) ×
      (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)), Fintype.card_prod,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, hrank, ← hsize]

/-- **`GBR` is finite-dimensional**. -/
theorem gbr_finite : Module.Finite K (GBR Γ a b c) :=
  Module.Finite.equiv (gbrFirstCollapse K Γ a b c).symm

/-- **`GBR` is nontrivial**. -/
theorem gbr_nontrivial : Nontrivial (GBR Γ a b c) := by
  refine Module.nontrivial_of_finrank_pos (R := K) ?_
  rw [finrank_GBR_eq_gTripleEnvSize]
  exact Nat.pos_of_ne_zero (gTripleEnvSize_ne_zero K Γ a b c)

end Dimension

end GaugeChi

end Superfusion

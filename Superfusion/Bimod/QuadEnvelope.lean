/-
Superfusion / Bimod / QuadEnvelope

Milestone M8a-8d′-iii-a (roadmap v3): **instantiate the general
`SplitIsotypy` layer at the towers** — the quadruple envelope algebra
`QuadEnv K a b c d`, acting on `Q1`/`Q4`, and its splitness.

1. **The quadruple envelope.** `QuadEnv K a b c d := Envelope
   (quadSource K a b c d).grading (stdTower (a+b+c+d)).grading`
   (`Bimod.Basic`'s `𝒜 ᵍ⊗ B^sop` packaging, reused verbatim): the
   4-fold gtensor `quadSource K a b c d = (((T_a ᵍ⊗ T_b) ᵍ⊗ T_c) ᵍ⊗
   T_d)` (`PentagonChi.lean`, already landed for the pentagon
   coherence scalar) enveloped with the super-opposite of
   `T_{a+b+c+d}` — the LEFT-associated spelling, matching `Q1`'s own
   right-coefficient tower *exactly* (`QuadActions.lean`'s `Q1`
   right-action instance) and `quadRoute1`'s target, so that
   deliverable 4's splitting chain and `Q1`'s interface need no cast;
   `Q4`'s right tower `T_{a+(b+c+d)}` differs only by associativity
   (`quadRightCast_eq` in `QuadInterSpace.lean`), absorbed where
   needed via `stdTowerCast`.  `FiniteDimensional K (QuadEnv …)` is
   transported off `Module.Finite K (quadSource …).carrier` (landed:
   `quadSource_finiteDimensional`) and `Module.Finite K (stdTower …)`
   along `GradedTensorProduct.of`.

4. **Splitness.** `quadEnvSplit : QuadEnv K a b c d ≃ₐ[K]
   Matrix (Fin (quadEnvSize K a b c d)) (Fin (quadEnvSize K a b c d))
   K`, chained (existence-level, forgetting all gradings after the
   Wall step, per the design note):

   * `quadRoute1 : quadSource ≅ quadFrame = (stdTower s).matrixSuper
     n₁ n₂` (`s := a+b+c+d`, landed in `PentagonQuad.lean`/
     `PentagonChi.lean`) congruenced into the LEFT factor of the
     envelope tensor (`SuperAlgEquiv.gtensorCongr` against `refl` on
     the `sop` factor);
   * `matrixSuperGtensor (stdTower s) ((stdTower s).sop) n₁ n₂` pulls
     the matrix factor out of the tensor:
     `(M_{n₁|n₂}(T_s)) ᵍ⊗ T_s^sop ≅ M_{n₁|n₂}(T_s ᵍ⊗ T_s^sop)`;
   * **Wall's map** `superMulLeftRight (stdTower s).grading :
     SuperEnvelope (stdTower s).grading ≃ₐ[K] End_K(T_s)`, bijective
     since `stdTower s` is super-Azumaya (`stdTower_isSuperAzumaya`,
     M7c-2/M4) — the point where the grading is dropped (`End_K` has
     no compatible superalgebra structure in play here);
   * a `Fin m`-basis (`Module.finBasis`, `m := finrank K T_s`) turns
     `End_K(T_s)` into `Matrix (Fin m) (Fin m) K`
     (`LinearMap.toMatrixAlgEquiv`), mapped entrywise into the outer
     matrix factor (`AlgEquiv.mapMatrix`);
   * the nested matrix `Matrix (Fin n₁ ⊕ Fin n₂) _ (Matrix (Fin m)
     (Fin m) K)` collapses to a single matrix algebra over the
     product index (`Matrix.compAlgEquiv`, mathlib), reindexed to
     `Fin (quadEnvSize …)` along an arbitrary `Fintype` enumeration
     (`Matrix.reindexAlgEquiv`, `Fintype.equivFin`).

   `quadEnvSize_ne_zero` transports non-emptiness of the product index
   off `quadFrame_nonempty` (landed, `PentagonChi.lean`) and
   `Module.finrank_pos` (`Nontrivial`/`FiniteDimensional` of `T_s`,
   landed in `TowerStd.lean`).

Deliverable 2 (the `QuadEnv`-module structures on `Q1`, `Q4`, via
three iterated `MiddleActionHom.gtensorLeftActionHom` lifts) and
deliverable 3 (the `quadInterSpace = gradedHomF` interface) are
**deferred**: they need two further pieces of general-layer machinery
not yet landed anywhere in the repo — gradedness of
`gtensorLeftActionHom` itself (`SetLike.GradedSMul (ℬ ᵍ⊗ 𝒞)
(relGrading …)`, needed to iterate the lift a second/third time) and
its commutation with a *further* outer right action (needed for the
`SMulCommClass` hypothesis of `Bimod.Envelope`) — each comparable in
scope to `MiddleActionHom.lean`/`OuterActions.lean` themselves, and
out of scope for this milestone; see the session report.
-/
import Superfusion.Bimod.SplitIsotypy
import Superfusion.Bimod.QuadInterSpace
import Superfusion.Super.PentagonChi
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-! ### The quadruple envelope algebra -/

/-- **The quadruple envelope algebra**: the 4-fold gtensor `quadSource
K a b c d = (((T_a ᵍ⊗ T_b) ᵍ⊗ T_c) ᵍ⊗ T_d)` (`PentagonChi.lean`)
enveloped (`Bimod.Envelope`) with the super-opposite of the
LEFT-associated total coefficient tower `T_{a+b+c+d}` — matching
`Q1`'s own right-coefficient tower exactly. -/
noncomputable abbrev QuadEnv : Type _ :=
  Envelope (quadSource (K := K) a b c d).grading
    (stdTower (K := K) (a + b + c + d)).grading

noncomputable instance : FiniteDimensional K (QuadEnv K a b c d) := by
  haveI : Module.Finite K (SuperOp (stdTower (K := K) (a + b + c + d)).grading) :=
    Module.Finite.equiv (SuperOp.op (stdTower (K := K) (a + b + c + d)).grading)
  exact Module.Finite.equiv
    (GradedTensorProduct.of K (quadSource (K := K) a b c d).grading
      (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading))

/-! ### Splitness -/

section Split

/-- The size of the pentagon frame reached by `quadRoute1`
(`PentagonQuad.lean`/`PentagonChi.lean`). -/
private noncomputable abbrev frameSize : ℕ × ℕ :=
  extSize (sizeL a b c) (a + b + c) d

/-- The `K`-dimension of the standard tower floor `T_{a+b+c+d}`. -/
private noncomputable abbrev towerRank : ℕ :=
  Module.finrank K (stdTower (K := K) (a + b + c + d)).carrier

/-- The Fintype index collapsing the nested matrix structure of the
splitting chain: the pentagon-frame index times the tower's own
`K`-basis index. -/
private abbrev quadEnvIdx : Type :=
  (Fin (frameSize a b c d).1 ⊕ Fin (frameSize a b c d).2)
    × Fin (towerRank K a b c d)

/-- **The size of the matrix algebra splitting `QuadEnv`.** -/
noncomputable def quadEnvSize : ℕ :=
  Fintype.card (quadEnvIdx K a b c d)

omit [Invertible (2 : K)] in
theorem quadEnvSize_ne_zero : quadEnvSize K a b c d ≠ 0 := by
  haveI : Nonempty (Fin (frameSize a b c d).1 ⊕ Fin (frameSize a b c d).2) :=
    quadFrame_nonempty a b c d
  haveI : Nonempty (Fin (towerRank K a b c d)) := by
    have hpos : 0 < towerRank K a b c d :=
      Module.finrank_pos (R := K) (M := (stdTower (K := K) (a + b + c + d)).carrier)
    exact Fin.pos_iff_nonempty.mp hpos
  exact Fintype.card_ne_zero

/-- **The Wall-map splitting of the tower**, `T_s ᵍ⊗ T_s^sop ≅
Matrix (Fin (towerRank …)) (Fin (towerRank …)) K`: bijective since
`T_s` is super-Azumaya (`stdTower_isSuperAzumaya`), then a chosen
`K`-basis turns `End_K(T_s)` into a matrix algebra. -/
noncomputable def towerWallSplit :
    SuperEnvelope (stdTower (K := K) (a + b + c + d)).grading ≃ₐ[K]
      Matrix (Fin (towerRank K a b c d)) (Fin (towerRank K a b c d)) K :=
  (AlgEquiv.ofBijective (superMulLeftRight (stdTower (K := K) (a + b + c + d)).grading)
      (stdTower_isSuperAzumaya (K := K) (a + b + c + d)).bij).trans
    (LinearMap.toMatrixAlgEquiv
      (Module.finBasis K (stdTower (K := K) (a + b + c + d)).carrier))

/-- **`QuadEnv` splits**: the explicit chain of `PentagonQuad.lean`'s
`quadRoute1` (turning the source into the pentagon frame), the matrix
pull-out `matrixSuperGtensor`, the Wall-map splitting of the tower
(`towerWallSplit`), and the nested-matrix collapse/reindex
(`Matrix.compAlgEquiv`, `Matrix.reindexAlgEquiv`). -/
noncomputable def quadEnvSplit :
    QuadEnv K a b c d ≃ₐ[K]
      Matrix (Fin (quadEnvSize K a b c d)) (Fin (quadEnvSize K a b c d)) K :=
  ((quadRoute1 (K := K) a b c d).gtensorCongr
      (SuperAlgEquiv.refl ((stdTower (K := K) (a + b + c + d)).sop))).toAlgEquiv.trans
    ((matrixSuperGtensor (stdTower (K := K) (a + b + c + d))
        ((stdTower (K := K) (a + b + c + d)).sop)
        (frameSize a b c d).1 (frameSize a b c d).2).toAlgEquiv.trans
      ((AlgEquiv.mapMatrix (towerWallSplit K a b c d)).trans
        ((Matrix.compAlgEquiv (Fin (frameSize a b c d).1 ⊕ Fin (frameSize a b c d).2)
            (Fin (towerRank K a b c d)) K K).trans
          (Matrix.reindexAlgEquiv K K (Fintype.equivFin (quadEnvIdx K a b c d))))))

end Split

end PentagonB

end Bimod

end Superfusion

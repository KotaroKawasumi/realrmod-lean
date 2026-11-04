/-
Superfusion / Super / PentagonFactor13

Milestone M7d-5b-4-iii(c), part 1: **the cluster-edge factorization
for the (ab)-cluster edge e13**.  With `σ := fuseSize a b`:

- the common prefix `Π := (stdFuse a b ⊗c refl_c) ⊗c refl_d`,
- the matrix-frame change
  `Ξ := mSG ∘ (mSG ⊗c refl_d) :
    (M_σ(T_{a+b}) ⊗ C) ⊗ D ≅ M_σ((T_{a+b} ⊗ C) ⊗ D)`
  (the matrix layer sits in the LEFT slot throughout, so the plain
  `matrixSuperGtensor` applies twice — no braiding and no `gassoc`
  appear anywhere in this factorization),
- the factored tails
  `T1/T3 := Ξ ≫ (routeL/routeR (a+b) c d).matrixSuper σ ≫ Θ`,
  where the shared tail `Θ` collapses the `σ`-layer onto the cluster
  route size and reassociates the three-layer collapse via
  `matrixSuperCompAssoc⁻¹`, landing on the pentagon target size
  `extSize (sizeL a b c) (a+b+c) d` **definitionally** — both routes
  stay fully left-associated (`(a+b)+c ≡ a+b+c` as Lean terms), so
  no index or size cast legs arise,

satisfy `quadRoute3 = T3 ∘ Π` (definitional — vertex 3 is *defined*
through the prefix) and `quadRoute1 = T1 ∘ Π` (the F1 coherence,
proved on the post-prefix algebra by the interchange kit: `mSG` full
naturality, the collapse/`gtensor` interchange, collapse naturality,
and the collapse-reassociation `matrixSuperComp_assoc_apply`).
-/
import Superfusion.Super.PentagonEdge24

namespace Superfusion

open TensorProduct
open GradedTensorProduct

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

section Factor13

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- One step of `gtensorCongr_trans_apply`, specialized to `refl` on
the fixed second factor (local copy of the private helper of
`PentagonFactor.lean`): peels the outermost `.trans` of a chain
tensored (via `⊗c`) with `refl`. -/
private theorem gtensorCongr_trans_refl_apply {P P' P'' D : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (e' : SuperAlgEquiv P' P'')
    (w : (P.gtensor D).carrier) :
    ((e.trans e').gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv w
      = (e'.gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv
        ((e.gtensorCongr (SuperAlgEquiv.refl D)).toAlgEquiv w) :=
  gtensorCongr_trans_apply e e' (SuperAlgEquiv.refl D)
    (SuperAlgEquiv.refl D) w

/-- The common cluster-fusion prefix of the routes through `(ab)`:
the `(ab)`-fusion applied under both fixed tail factors. -/
noncomputable def cluster13Prefix (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      ((((stdTower (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).gtensor (stdTower c)).gtensor (stdTower d)) :=
  ((stdFuse a b).gtensorCongr
      (SuperAlgEquiv.refl (stdTower c))).gtensorCongr
    (SuperAlgEquiv.refl (stdTower d))

/-- The matrix-frame change: pull the `σ`-matrix layer out through
both `gtensor` layers.  The layer sits in the LEFT slot, so the plain
`matrixSuperGtensor` applies twice (mirror of `clusterFrame` in
`PentagonFactor.lean`, which needed `matrixSuperGtensorRight` for the
middle slot). -/
noncomputable def cluster13Frame (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).gtensor (stdTower c)).gtensor (stdTower d))
      ((((stdTower (a + b)).gtensor (stdTower c)).gtensor
        (stdTower d)).matrixSuper (fuseSize a b).1 (fuseSize a b).2) :=
  ((matrixSuperGtensor (stdTower (a + b)) (stdTower c)
      (fuseSize a b).1 (fuseSize a b).2).gtensorCongr
    (SuperAlgEquiv.refl (stdTower d))).trans
    (matrixSuperGtensor ((stdTower (a + b)).gtensor (stdTower c))
      (stdTower d) (fuseSize a b).1 (fuseSize a b).2)

/-- **The shared tail** of the `(ab)`-cluster factorizations: the
collapse of the `σ`-matrix layer onto the cluster route size,
followed by the collapse-reassociation bridge.  Its target is the
pentagon target size `extSize (sizeL a b c) (a+b+c) d`
*definitionally*: unfolding `extSize`, `sizeL` and the pair
projections turns the bridge's source spelling `(σ·τ)·ρ` into the
pentagon spelling — with no index cast, since the frames
`(a+b)+c+d` and `a+b+c+d` are the same Lean term. -/
noncomputable def cluster13SharedTail (a b c d : ZMod 8) :
    SuperAlgEquiv
      (((stdTower (K := K) (a + b + c + d)).matrixSuper
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2)
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (matrixSuperComp (stdTower (a + b + c + d))
      (fuseSize a b).1 (fuseSize a b).2
      (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).trans
    (matrixSuperCompAssoc (stdTower (a + b + c + d))
      (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
      (fuseSize a b).1 (fuseSize a b).2).symm

/-- The factored tail through the left-associated cluster triple
`((a+b), c, d)`: frame change, stabilized left route, shared tail. -/
noncomputable def cluster13Tail1 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).gtensor (stdTower c)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (cluster13Frame a b c d).trans
    (((routeL (a + b) c d).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).trans
      (cluster13SharedTail a b c d))

/-- The factored tail through the right-associated cluster triple:
frame change, stabilized right route (which already lands on the left
route's target via its built-in cast), shared tail. -/
noncomputable def cluster13Tail3 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).gtensor (stdTower c)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (cluster13Frame a b c d).trans
    (((routeR (a + b) c d).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).trans
      (cluster13SharedTail a b c d))

/-- **Vertex 3 of the pentagon**: `(ab)(cd)` — fuse `(ab)`, then run
the cluster triple `((a+b), c, d)` through its right route
(reassociate to `(a+b)(cd)`, fuse `(cd)`, fuse the pair), sharing the
frame of `quadRoute1`, `quadRoute2` and `alignedRoute4/5`. -/
noncomputable def quadRoute3 (a b c d : ZMod 8) :
    SuperAlgEquiv
      ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d))
      ((stdTower (a + b + c + d)).matrixSuper
        (extSize (sizeL a b c) (a + b + c) d).1
        (extSize (sizeL a b c) (a + b + c) d).2) :=
  (cluster13Prefix a b c d).trans (cluster13Tail3 a b c d)

/-- **Factorization of vertex 3** through the `(ab)`-cluster prefix —
definitional: vertex 3 is built from the prefix and the factored
tail. -/
theorem quadRoute3_factor (a b c d : ZMod 8)
    (w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).carrier) :
    (quadRoute3 a b c d).toAlgEquiv w
      = (cluster13Tail3 a b c d).toAlgEquiv
        ((cluster13Prefix a b c d).toAlgEquiv w) := rfl

/-- **Factorization of vertex 1** through the `(ab)`-cluster prefix
(the F1 coherence): the fully left-nested route also factors through
`Π`, with the tail replaced by the stabilized left route of the
cluster triple `((a+b), c, d)`.  Both sides are fully left-nested, so
the two sides differ only in the `gtensor` depth at which each fusion
is applied and in the collapse order — settled by the interchange kit
and `matrixSuperComp_assoc_apply`. -/
theorem quadRoute1_factor (a b c d : ZMod 8)
    (w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).carrier) :
    (quadRoute1 a b c d).toAlgEquiv w
      = (cluster13Tail1 a b c d).toAlgEquiv
        ((cluster13Prefix a b c d).toAlgEquiv w) := by
  show (extTail (a + b + c) (sizeL a b c) d).toAlgEquiv
      (((routeL a b c).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w)
    = (cluster13Tail1 a b c d).toAlgEquiv
      ((cluster13Prefix a b c d).toAlgEquiv w)
  show (extTail (a + b + c) (sizeL a b c) d).toAlgEquiv
      (((((stdFuse a b).gtensorCongr
            (SuperAlgEquiv.refl (stdTower c))).trans
          ((matrixSuperGtensor (stdTower (a + b)) (stdTower c)
              (fuseSize a b).1 (fuseSize a b).2).trans
            (((stdFuse (a + b) c).matrixSuper (fuseSize a b).1
                (fuseSize a b).2).trans
              (matrixSuperComp (stdTower (a + b + c))
                (fuseSize a b).1 (fuseSize a b).2
                (fuseSize (a + b) c).1
                (fuseSize (a + b) c).2)))).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w)
    = (cluster13Tail1 a b c d).toAlgEquiv
      ((cluster13Prefix a b c d).toAlgEquiv w)
  rw [gtensorCongr_trans_refl_apply, gtensorCongr_trans_refl_apply,
    gtensorCongr_trans_refl_apply]
  have hPre : (cluster13Prefix a b c d).toAlgEquiv w
      = (((stdFuse a b).gtensorCongr
            (SuperAlgEquiv.refl (stdTower c))).gtensorCongr
          (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w := rfl
  rw [hPre]
  have hFrame : ∀ v : ((((stdTower (K := K) (a + b)).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier,
      (cluster13Frame a b c d).toAlgEquiv v
      = (matrixSuperGtensor ((stdTower (a + b)).gtensor (stdTower c))
            (stdTower d) (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
          (((matrixSuperGtensor (stdTower (a + b)) (stdTower c)
                (fuseSize a b).1 (fuseSize a b).2).gtensorCongr
              (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv v) :=
    fun v => rfl
  have hTail1 : ∀ v : ((((stdTower (K := K) (a + b)).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier,
      (cluster13Tail1 a b c d).toAlgEquiv v
      = ((matrixSuperCompAssoc (stdTower (K := K) (a + b + c + d))
            (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
            (fuseSize a b).1 (fuseSize a b).2).symm).toAlgEquiv
          ((matrixSuperComp (stdTower (a + b + c + d))
              (fuseSize a b).1 (fuseSize a b).2
              (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).toAlgEquiv
            (((routeL (a + b) c d).matrixSuper (fuseSize a b).1
                  (fuseSize a b).2).toAlgEquiv
              ((cluster13Frame a b c d).toAlgEquiv v))) := fun v => rfl
  rw [hTail1, hFrame]
  set w' : ((((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).gtensor (stdTower c)).gtensor
      (stdTower d)).carrier :=
    (((stdFuse a b).gtensorCongr
          (SuperAlgEquiv.refl (stdTower c))).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w with hw'
  set u : ((((stdTower (K := K) (a + b)).gtensor
      (stdTower c)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).gtensor (stdTower d)).carrier :=
    ((matrixSuperGtensor (stdTower (a + b)) (stdTower c)
          (fuseSize a b).1 (fuseSize a b).2).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv w' with hu
  -- step A: `mSG` full naturality moves the matrix-slot congruence
  -- `stdFuse (a+b) c` past the outer stabilization (with `refl_d`
  -- fixed on the other slot)
  have hA := matrixSuperGtensor_full_natural_apply (stdFuse (a + b) c)
    (SuperAlgEquiv.refl (stdTower d)) (fuseSize a b).1 (fuseSize a b).2 u
  set L2L3L4 : SuperAlgEquiv
      (((stdTower (K := K) (a + b + c)).matrixSuper
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2).gtensor
        (stdTower d))
      ((stdTower (K := K) (a + b + c + d)).matrixSuper
        (sizeL (a + b) c d).1 (sizeL (a + b) c d).2) :=
    (matrixSuperGtensor (stdTower (K := K) (a + b + c)) (stdTower d)
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2).trans
      (((stdFuse (a + b + c) d).matrixSuper (fuseSize (a + b) c).1
          (fuseSize (a + b) c).2).trans
        (matrixSuperComp (stdTower (a + b + c + d))
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2))
    with hL2L3L4
  have hroute : routeL (a + b) c d
      = ((stdFuse (a + b) c).gtensorCongr
          (SuperAlgEquiv.refl (stdTower d))).trans L2L3L4 := rfl
  have hAstep : (((routeL (a + b) c d).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower (a + b)).gtensor (stdTower c))
            (stdTower d) (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv u))
      = (L2L3L4.matrixSuper (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
          ((((stdFuse (a + b) c).gtensorCongr
                (SuperAlgEquiv.refl (stdTower d))).matrixSuper
              (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
            ((matrixSuperGtensor ((stdTower (a + b)).gtensor (stdTower c))
                (stdTower d) (fuseSize a b).1
                (fuseSize a b).2).toAlgEquiv u)) := by
    rw [hroute]
    rfl
  rw [hAstep]
  conv_rhs => rw [← hA]
  set u2 : ((((stdTower (K := K) (a + b + c)).matrixSuper
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2).matrixSuper
      (fuseSize a b).1 (fuseSize a b).2).gtensor (stdTower d)).carrier :=
    (((stdFuse (a + b) c).matrixSuper (fuseSize a b).1
          (fuseSize a b).2).gtensorCongr
        (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv u with hu2
  -- step B: interchange the collapse with the tail `gtensor` layer
  have hB := matrixSuperComp_gtensor_apply
    (X := stdTower (K := K) (a + b + c)) (D := stdTower d)
    (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
    (fuseSize a b).1 (fuseSize a b).2 u2
  -- split the stabilized cluster route into its three stages
  have hCstep : (L2L3L4.matrixSuper (fuseSize a b).1
        (fuseSize a b).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower (a + b + c)).matrixSuper
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2)
            (stdTower d) (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv u2)
      = ((matrixSuperComp (stdTower (K := K) (a + b + c + d))
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
              (fuseSize (a + b + c) d).1
              (fuseSize (a + b + c) d).2).matrixSuper (fuseSize a b).1
            (fuseSize a b).2).toAlgEquiv
          ((((stdFuse (a + b + c) d).matrixSuper (fuseSize (a + b) c).1
                  (fuseSize (a + b) c).2).matrixSuper (fuseSize a b).1
                (fuseSize a b).2).toAlgEquiv
            (((matrixSuperGtensor (stdTower (K := K) (a + b + c))
                    (stdTower d) (fuseSize (a + b) c).1
                    (fuseSize (a + b) c).2).matrixSuper (fuseSize a b).1
                  (fuseSize a b).2).toAlgEquiv
              ((matrixSuperGtensor ((stdTower (a + b + c)).matrixSuper
                    (fuseSize (a + b) c).1 (fuseSize (a + b) c).2)
                  (stdTower d) (fuseSize a b).1
                  (fuseSize a b).2).toAlgEquiv u2))) := by
    rw [hL2L3L4]
    rfl
  rw [hCstep]
  -- collapse naturality for the final fusion `stdFuse (a+b+c) d`
  have hE := matrixSuperComp_natural_apply (stdFuse (a + b + c) d)
    (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
    (fuseSize a b).1 (fuseSize a b).2
    (((matrixSuperGtensor (stdTower (K := K) (a + b + c)) (stdTower d)
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2).matrixSuper
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
      ((matrixSuperGtensor ((stdTower (a + b + c)).matrixSuper
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2)
          (stdTower d) (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv u2))
  -- the fully-left tail in the flat spelling, with the interchange
  -- `hB` applied at the innermost stage
  have hLHS0 : (extTail (a + b + c) (sizeL a b c) d).toAlgEquiv
        (((matrixSuperComp (stdTower (a + b + c))
              (fuseSize a b).1 (fuseSize a b).2
              (fuseSize (a + b) c).1
              (fuseSize (a + b) c).2).gtensorCongr
            (SuperAlgEquiv.refl (stdTower d))).toAlgEquiv u2)
      = (matrixSuperComp (stdTower (K := K) (a + b + c + d))
            ((fuseSize a b).1 * (fuseSize (a + b) c).1
              + (fuseSize a b).2 * (fuseSize (a + b) c).2)
            ((fuseSize a b).1 * (fuseSize (a + b) c).2
              + (fuseSize a b).2 * (fuseSize (a + b) c).1)
            (fuseSize (a + b + c) d).1
            (fuseSize (a + b + c) d).2).toAlgEquiv
        (((stdFuse (a + b + c) d).matrixSuper
              ((fuseSize a b).1 * (fuseSize (a + b) c).1
                + (fuseSize a b).2 * (fuseSize (a + b) c).2)
              ((fuseSize a b).1 * (fuseSize (a + b) c).2
                + (fuseSize a b).2 * (fuseSize (a + b) c).1)).toAlgEquiv
          ((matrixSuperComp ((stdTower (K := K) (a + b + c)).gtensor
                (stdTower d)) (fuseSize a b).1 (fuseSize a b).2
                (fuseSize (a + b) c).1 (fuseSize (a + b) c).2).toAlgEquiv
            (((matrixSuperGtensor (stdTower (K := K) (a + b + c))
                  (stdTower d) (fuseSize (a + b) c).1
                  (fuseSize (a + b) c).2).matrixSuper (fuseSize a b).1
                (fuseSize a b).2).toAlgEquiv
              ((matrixSuperGtensor ((stdTower (a + b + c)).matrixSuper
                    (fuseSize (a + b) c).1 (fuseSize (a + b) c).2)
                  (stdTower d) (fuseSize a b).1
                  (fuseSize a b).2).toAlgEquiv u2)))) := by
    unfold sizeL extTail
    dsimp only
    exact congrArg
      ((((stdFuse (a + b + c) d).matrixSuper
            ((fuseSize a b).1 * (fuseSize (a + b) c).1
              + (fuseSize a b).2 * (fuseSize (a + b) c).2)
            ((fuseSize a b).1 * (fuseSize (a + b) c).2
              + (fuseSize a b).2 * (fuseSize (a + b) c).1)).trans
          (matrixSuperComp (stdTower (K := K) (a + b + c + d))
            ((fuseSize a b).1 * (fuseSize (a + b) c).1
              + (fuseSize a b).2 * (fuseSize (a + b) c).2)
            ((fuseSize a b).1 * (fuseSize (a + b) c).2
              + (fuseSize a b).2 * (fuseSize (a + b) c).1)
            (fuseSize (a + b + c) d).1
            (fuseSize (a + b + c) d).2)).toAlgEquiv)
      hB
  rw [hLHS0]
  set W : ((((stdTower (K := K) (a + b + c + d)).matrixSuper
      (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2).matrixSuper
      (fuseSize (a + b) c).1 (fuseSize (a + b) c).2).matrixSuper
      (fuseSize a b).1 (fuseSize a b).2).carrier :=
    (((stdFuse (a + b + c) d).matrixSuper (fuseSize (a + b) c).1
          (fuseSize (a + b) c).2).matrixSuper (fuseSize a b).1
        (fuseSize a b).2).toAlgEquiv
      (((matrixSuperGtensor (stdTower (K := K) (a + b + c)) (stdTower d)
            (fuseSize (a + b) c).1 (fuseSize (a + b) c).2).matrixSuper
          (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
        ((matrixSuperGtensor ((stdTower (a + b + c)).matrixSuper
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2)
            (stdTower d) (fuseSize a b).1
            (fuseSize a b).2).toAlgEquiv u2)) with hW
  -- reassociate the three-layer collapse
  have hAssoc :
      (matrixSuperComp (stdTower (K := K) (a + b + c + d))
          (fuseSize a b).1 (fuseSize a b).2
          (sizeL (a + b) c d).1 (sizeL (a + b) c d).2).toAlgEquiv
        (((matrixSuperComp (stdTower (K := K) (a + b + c + d))
              (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
              (fuseSize (a + b + c) d).1
              (fuseSize (a + b + c) d).2).matrixSuper
            (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv W)
      = (matrixSuperCompAssoc (stdTower (K := K) (a + b + c + d))
          (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
          (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
          (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv
        ((matrixSuperComp (stdTower (K := K) (a + b + c + d))
            ((fuseSize a b).1 * (fuseSize (a + b) c).1
              + (fuseSize a b).2 * (fuseSize (a + b) c).2)
            ((fuseSize a b).1 * (fuseSize (a + b) c).2
              + (fuseSize a b).2 * (fuseSize (a + b) c).1)
            (fuseSize (a + b + c) d).1
            (fuseSize (a + b + c) d).2).toAlgEquiv
          ((matrixSuperComp ((stdTower (K := K)
                (a + b + c + d)).matrixSuper
                (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2)
              (fuseSize a b).1 (fuseSize a b).2
              (fuseSize (a + b) c).1
              (fuseSize (a + b) c).2).toAlgEquiv W)) :=
    matrixSuperComp_assoc_apply (fuseSize (a + b + c) d).1
      (fuseSize (a + b + c) d).2 (fuseSize (a + b) c).1
      (fuseSize (a + b) c).2 (fuseSize a b).1 (fuseSize a b).2 W
  rw [hAssoc]
  have hcanc : ∀ X, ((matrixSuperCompAssoc
        (stdTower (K := K) (a + b + c + d))
        (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2).symm).toAlgEquiv
      ((matrixSuperCompAssoc (stdTower (K := K) (a + b + c + d))
        (fuseSize (a + b + c) d).1 (fuseSize (a + b + c) d).2
        (fuseSize (a + b) c).1 (fuseSize (a + b) c).2
        (fuseSize a b).1 (fuseSize a b).2).toAlgEquiv X) = X := fun X =>
    AlgEquiv.symm_apply_apply _ X
  rw [hcanc, hE]

end Factor13

end Superfusion

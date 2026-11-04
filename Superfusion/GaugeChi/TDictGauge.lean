/-
Superfusion / GaugeChi / TDictGauge

Items 4-5 of the §10 roadmap (`docs/real-trivialization-design.md`): **the
gauge `T ↔ t` dictionary** — the Γ-generic port of `Bimod/TDict.lean`, sitting
on top of the gauge column dictionary of `GaugeChi/ColumnDictGauge.lean`
(items 1-3: `gblColumnEquiv`, `gbrNativeColumnEquiv`, `gbrColumnEquiv hsz`).

## ITEM 4: **one module-correspondence lemma per vertex, not six
slot-equivariance lemmas**

The roadmap scoped item 4 as SIX separate slot equivariances, mirroring
`Bimod/ColumnSlots.lean` + `Bimod/ColumnDict3.lean` + `Bimod/TDict.lean`'s two
`_of_hom` upgrades.  **That shape is superseded.**  The whole triple-tensor
action is already carried by BOTH sides of each dictionary, so the six lemmas
are the three-fold specialization of ONE statement per vertex, and the
specialization is free (an existing `GaugeParity` rewrite).

### The module structures that make it work (all pre-existing)

* **Source.**  `GaugeChi/GaugeParity.lean` registers `GBL.instModuleGtensorABC`
  and `GBR.instModuleGtensorABC`, both of type `Module (((Γ.D a).gtensor
  (Γ.D b)).gtensor (Γ.D c)).carrier (GB? Γ a b c)` — `GBL` by a single
  `gtensorLeftActionHom`, `GBR` by the direct two-`lift` assembly
  `phi2 = lift (lift fA fB) fC` in the envelope's own bracket order.
* **Target.**  `Bimod.FusionColumn`'s `General` section registers
  `Module P.carrier (FusionColumn φ)` by `Module.compHom` along `φ`, and the
  matrix action on the bare column IS `Matrix.mulVec` — so at `φ :=
  Γ.gaugeRouteL/R/R'` the action is DEFINITIONALLY `mulVec` by the route
  matrix (`routeL_column_smul_eq_mulVec` & co. below).
* **The slot bridges.**  `GaugeParity`'s `GBL.aEmbed`/`bEmbed`/`cEmbed` and
  `GBR.aEmbed_smul`/`bEmbed_smul`/`cEmbed_smul` state that the triple-tensor
  action at an `includeLeft`/`includeRight`-embedded slot generator equals the
  vertex's own registered slot action, **for every element of the vertex** —
  the Koszul bookkeeping of the two signed slots (`GBL`'s `D_c`, `GBR`'s
  `D_a`) is already discharged there, once and for all.  Consequently the
  blueprint's `_of_hom` upgrades and the `Bimod/QuadMembership.lean` machinery
  they run on (which has no gauge-layer port) are not needed at all.

### The three item-4 deliverables (landed)

  `gblColumnEquiv_gtensor_smul   (y) (m) : gbl (y • m) = routeL y  *ᵥ gbl m`
  `gbrNativeColumnEquiv_gtensor_smul (y) (m) : gbrN (y • m) = routeR y  *ᵥ gbrN m`
  `gbrColumnEquiv_gtensor_smul (hsz) (y) (m) : gbr (y • m) = routeR' y *ᵥ gbr m`

Each says precisely "the column dictionary is an isomorphism of
`(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-modules"; they are stated with `*ᵥ` rather than a bare
`•` on purpose — `FusionColumn (Γ.gaugeRouteL a b c)` and `FusionColumn
(Γ.gaugeRouteR' a b c)` are literally the SAME type, so a bare `•` at the
target would be genuinely ambiguous between the two pulled-back actions (the
M14-B instance-ambiguity trap).  Only the aligned right statement carries the
hypothesis `hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c`, which is already
`gbrColumnEquiv`'s own standing hypothesis (see `ColumnDictGauge.lean`'s
header for why a shift-`0` aligned dictionary cannot exist without it); the
native right statement is hypothesis-free.

### How they are proved

Two route-entry chases on the left (`routeL_left_entry` for a GENERAL
`w : D_a ᵍ⊗ D_b` — one chase covering `ColumnSlots.lean`'s `routeL_aslot_entry`
AND `_bslot_entry`; `routeL_right_entry` for homogeneous `z : D_c`, the signed
`matrixInclRight`/`sdiag` diagonal) and three on the right
(`routeR_bslot_entry`, `routeR_cslot_entry` — plain,
`matrixSuperGtensorRight_one_tmul` being sign-free — and `routeR_aslot_entry`,
the signed diagonal of `matrixSuperGtensorRight_tmul_one_of_mem`).  Each entry
lemma is turned into a generator-level column identity
(`freeCollapse_mulVec_left` + `Equiv.sum_comp`/`Fintype.sum_prod_type`
reindexing, with `gaugeZZ_comm`/`gaugeZZ_comm2` supplying the Koszul
recombination for the two signed slots), then lifted to ALL of the vertex by
`RelTensor.induction_on` (plain slots) resp. the homogeneous-first-factor
induction `relTensor_induction_on_left_homog` (signed slots), then to ALL `y`
by the subalgebra argument: the "good set" is closed under `+`, `*` and `K`,
so `GradedTensorProduct`-induction plus `includeLeft_mul_includeRight` and an
even/odd split of the single homogeneous leg exhausts the triple tensor.

The aligned right statement is derived from the native one ENTRYWISE
(`routeR'_entry`), the two casts of `gbrColumnEquiv` being exactly the ones
`gbrColumnEquiv_rightEquiv` already handles, with `frameAlign_of_sizes_eq`
collapsing `gaugeRouteR'`'s `frameAlign` step to the pure frame cast.

## ITEM 5: `gmulVecMap`, `gtOfT`, and the five `gInterSpace` conditions

`gmulVecMap T` is the port of `TDict.lean:96`.  As in the `stdTower` case the
two column types are **literally the same type**: `Γ.gaugeRouteR'` (unlike
`Γ.gaugeRouteR`) targets `Γ.gaugeRouteL`'s own target superalgebra, so both
`FusionColumn`s unfold to `Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b
c).2 → (Γ.D (a+b+c)).carrier` — **`hsz` is NOT needed for `gmulVecMap`**, only
for the aligned dictionary itself.  Landed: `gmulVecMap`, `_apply`,
`_rightEquiv`, `_mem_grading`, `_slot_equivariant` (the `Matrix.mulVec_mulVec`
chase against the `pentagonT`-shaped hypothesis on `T`), `_bijective`.

`gtOfT hsz T := (gbrColumnEquiv hsz).symm ∘ₗ gmulVecMap T ∘ₗ gblColumnEquiv`
(port of `TDict.lean:272`), with all FIVE conditions of
`GaugeChi/InterSpace.lean`'s `mem_gInterSpace_iff` assembled in
`gtOfT_mem_interSpace`:

1. `gtOfT_mem_homGrading` — `gmulVecMap_mem_grading` conjugated through the
   dictionary (`gbrColumnEquiv_symm_mem_grading`);
2-4. `gtOfT_mem_superEquivariant_a/b/c` — three instances of ONE pattern:
   embed the slot generator (`GBL.aEmbed`/`bEmbed`/`cEmbed`,
   `GBR.aEmbed_smul`/`bEmbed_smul`/`cEmbed_smul`), rewrite the item-4
   correspondence lemma, apply `gmulVecMap_slot_equivariant`, and reverse
   through `gbrColumnEquiv` with `conjSymm`;
5. `gtOfT_mem_rightSemilinear` — via `grightSemilinear_iff_recast_equivariant`,
   the Γ-port of `Bimod/RouteRecast.lean`'s
   `rightSemilinear_iff_recast_equivariant`: `GBR`'s recast right action
   (`RouteBimod.lean`) is registered as `Module.compHom` along exactly the ring
   map `gInterSpace` quantifies over, so the port is `Iff.rfl`.

Plus `gtOfT_ne_zero` (nonzero `T` ↦ nonzero intertwiner, via
`Matrix.ext_of_mulVec_single`) and `gtOfT_bijective` (composite of three
bijections).

**Hypotheses.**  The only hypothesis anywhere beyond `T`'s own degree/
intertwining data is `hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c`,
inherited verbatim from `gbrColumnEquiv`; it is per-triple dischargeable at
the concrete gauges (at `ZMod 8` sizes it is `PentagonRoutes.sizeL_eq_sizeR`'s
arithmetic), matching the §10 plan's per-triple discharge of the `T`-matrix
hypothesis.

**One local instance.**  `gbrModuleGtensorRaw` re-registers `GBR`'s (already
existing) triple-tensor action at the third, syntactically distinct spelling
`((D_a).gtensor (D_b)).grading ᵍ⊗ (D_c).grading` — the one an
`includeLeft`/`includeRight` out of `(D_a).gtensor (D_b)` produces, and the one
`Bimod.FusionColumn`'s `Slots` bridge uses on the column side.  All three
spellings are definitionally equal; instance search does not unfold
`SuperAlgebra.gtensor`, so without this bridge the two sides of the `GBR`
correspondence lemma cannot even be stated at the same `y`.  It is `local`.
-/
import Superfusion.GaugeChi.ColumnDictGauge
import Superfusion.GaugeChi.GaugeParity

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open scoped Matrix
open Bimod
open GradedTensorProduct

universe u v

/-! ### A generic conjugation helper -/

section Generic

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- **Conjugating a "forward" identity along a linear equivalence**: if
`e (φ m) = ψ (e m)` for all `m`, then `e.symm (ψ n) = φ (e.symm n)` for all
`n` (verbatim copy of `Bimod.PentagonB.conjSymm`, `Bimod/TDict.lean:76`,
recopied to keep the concrete `ZMod 8` dictionary out of this import cone) —
the device that reverses an established "forward" slot/right-action identity
of `gblColumnEquiv`/`gbrColumnEquiv` through the inverse equivalence. -/
theorem conjSymm (e : M ≃ₗ[R] N) (φ : M → M) (ψ : N → N)
    (h : ∀ m, e (φ m) = ψ (e m)) (n : N) :
    e.symm (ψ n) = φ (e.symm n) := by
  have hn := h (e.symm n)
  rw [e.apply_symm_apply] at hn
  rw [← hn, e.symm_apply_apply]

end Generic

/-! ### Generic route-chase helpers -/

section Generic

universe w
variable {K' : Type w} [CommRing K']

private def toCA {P Q : SuperAlgebra K'} (x : P.grading ᵍ⊗[K'] Q.grading) :
    (P.gtensor Q).carrier := x

private theorem toCA_one_one {P Q : SuperAlgebra K'} :
    toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] (1 : Q.carrier)) = (1 : (P.gtensor Q).carrier) := by
  show ((1 : P.carrier) ᵍ⊗ₜ[K'] (1 : Q.carrier) : P.grading ᵍ⊗[K'] Q.grading) = 1
  rw [show ((1 : P.carrier) ᵍ⊗ₜ[K'] (1 : Q.carrier) : P.grading ᵍ⊗[K'] Q.grading)
      = of K' P.grading Q.grading ((1 : P.carrier) ⊗ₜ[K'] (1 : Q.carrier)) from rfl,
    show ((1 : P.carrier) ⊗ₜ[K'] (1 : Q.carrier) : P.carrier ⊗[K'] Q.carrier) = 1 from
      Algebra.TensorProduct.one_def.symm,
    of_one]

private theorem add_gtmulCA {P Q : SuperAlgebra K'}
    (u v : P.carrier) (z : Q.carrier) :
    toCA ((u + v) ᵍ⊗ₜ[K'] z) = toCA (u ᵍ⊗ₜ[K'] z) + toCA (v ᵍ⊗ₜ[K'] z) := by
  show ((u + v) ᵍ⊗ₜ[K'] z : P.grading ᵍ⊗[K'] Q.grading)
    = (u ᵍ⊗ₜ[K'] z) + (v ᵍ⊗ₜ[K'] z)
  rw [show ((u + v) ᵍ⊗ₜ[K'] z : P.grading ᵍ⊗[K'] Q.grading)
      = of K' P.grading Q.grading ((u + v) ⊗ₜ[K'] z) from rfl,
    TensorProduct.add_tmul, map_add]
  rfl

private theorem gtmulCA_add {P Q : SuperAlgebra K'}
    (x : P.carrier) (u v : Q.carrier) :
    toCA (x ᵍ⊗ₜ[K'] (u + v)) = toCA (x ᵍ⊗ₜ[K'] u) + toCA (x ᵍ⊗ₜ[K'] v) := by
  show (x ᵍ⊗ₜ[K'] (u + v) : P.grading ᵍ⊗[K'] Q.grading)
    = (x ᵍ⊗ₜ[K'] u) + (x ᵍ⊗ₜ[K'] v)
  rw [show (x ᵍ⊗ₜ[K'] (u + v) : P.grading ᵍ⊗[K'] Q.grading)
      = of K' P.grading Q.grading (x ⊗ₜ[K'] (u + v)) from rfl,
    TensorProduct.tmul_add, map_add]
  rfl

private theorem gtensorCongr_refl_right_tmul {P P' Q : SuperAlgebra K'}
    (e : SuperAlgEquiv P P') (x : P.carrier) (y : Q.carrier) :
    (e.gtensorCongr (SuperAlgEquiv.refl Q)).toAlgEquiv (toCA (x ᵍ⊗ₜ[K'] y))
      = toCA (e.toAlgEquiv x ᵍ⊗ₜ[K'] y) :=
  gcongr_tmul P.grading Q.grading P'.grading Q.grading e.toAlgEquiv
    (SuperAlgEquiv.refl Q).toAlgEquiv e.map_grading (SuperAlgEquiv.refl Q).map_grading x y

private theorem gtensorCongr_refl_left_tmul {P Q Q' : SuperAlgebra K'}
    (f : SuperAlgEquiv Q Q') (x : P.carrier) (y : Q.carrier) :
    ((SuperAlgEquiv.refl P).gtensorCongr f).toAlgEquiv (toCA (x ᵍ⊗ₜ[K'] y))
      = toCA (x ᵍ⊗ₜ[K'] f.toAlgEquiv y) :=
  gcongr_tmul P.grading Q.grading P.grading Q'.grading (SuperAlgEquiv.refl P).toAlgEquiv
    f.toAlgEquiv (SuperAlgEquiv.refl P).map_grading f.map_grading x y

private theorem gtensorAssoc_tmulCA {P Q R : SuperAlgebra K'}
    (x : P.carrier) (y : Q.carrier) (z : R.carrier) :
    (gtensorAssoc P Q R).toAlgEquiv (toCA (toCA (x ᵍ⊗ₜ[K'] y) ᵍ⊗ₜ[K'] z))
      = toCA (x ᵍ⊗ₜ[K'] (toCA (y ᵍ⊗ₜ[K'] z))) :=
  gassoc_tmul P.grading Q.grading R.grading x y z

private theorem matrixSuperGtensor_tmul_one {P Q : SuperAlgebra K'} (p q : ℕ)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) :
    (matrixSuperGtensor P Q p q).toAlgEquiv (toCA (M ᵍ⊗ₜ[K'] (1 : Q.carrier)))
      = matrixInclLeft P.grading Q.grading M := by
  show matrixTensorSuperHom (sumParity p q) P.grading Q.grading (M ᵍ⊗ₜ[K'] (1 : Q.carrier)) = _
  rw [matrixTensorSuperHom_tmul, map_one, mul_one]

private theorem matrixSuperGtensor_one_tmul {P Q : SuperAlgebra K'} (p q : ℕ)
    (y : Q.carrier) :
    (matrixSuperGtensor P Q p q).toAlgEquiv
        (toCA ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) ᵍ⊗ₜ[K'] y))
      = matrixInclRight (sumParity p q) P.grading Q.grading y := by
  show matrixTensorSuperHom (sumParity p q) P.grading Q.grading
      ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) ᵍ⊗ₜ[K'] y) = _
  rw [matrixTensorSuperHom_tmul, map_one, one_mul]

private theorem matrixSuper_entry {P Q : SuperAlgebra K'} (e : SuperAlgEquiv P Q) (p q : ℕ)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier) (r s : Fin p ⊕ Fin q) :
    (e.matrixSuper p q).toAlgEquiv M r s = e.toAlgEquiv (M r s) := by
  show e.toAlgEquiv.mapMatrix M r s = _
  rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply]

private theorem matrixSuperComp_entry {P : SuperAlgebra K'} (p' q' p q : ℕ)
    (M : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q')
      (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier))
    (i j : Fin (p' * p + q' * q) ⊕ Fin (p' * q + q' * p)) :
    (matrixSuperComp P p' q' p q).toAlgEquiv M i j
      = M ((collapseIndexEquiv p' q' p q).symm i).1
          ((collapseIndexEquiv p' q' p q).symm j).1
          ((collapseIndexEquiv p' q' p q).symm i).2
          ((collapseIndexEquiv p' q' p q).symm j).2 := by
  show (Matrix.reindexAlgEquiv K' _ (collapseIndexEquiv p' q' p q))
      ((Matrix.compAlgEquiv _ _ _ K') M) i j = _
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.compAlgEquiv_apply, Matrix.comp_apply]

private theorem gtensorComm_tmul_one {P Q : SuperAlgebra K'} (x : P.carrier) :
    (gtensorComm P Q).toAlgEquiv (toCA (x ᵍ⊗ₜ[K'] (1 : Q.carrier)))
      = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K'] x) := by
  have hsplit : ∀ (j : ZMod 2) (y : P.carrier), y ∈ P.grading j →
      (gtensorComm P Q).toAlgEquiv (toCA (y ᵍ⊗ₜ[K'] (1 : Q.carrier)))
        = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K'] y) := by
    intro j y hy
    show comm P.grading Q.grading (y ᵍ⊗ₜ[K'] (1 : Q.carrier))
      = ((1 : Q.carrier) ᵍ⊗ₜ[K'] y)
    rw [show (y ᵍ⊗ₜ[K'] (1 : Q.carrier) : P.grading ᵍ⊗[K'] Q.grading)
        = (((⟨y, hy⟩ : P.grading j) : P.carrier) ᵍ⊗ₜ[K']
            ((⟨(1 : Q.carrier), SetLike.one_mem_graded Q.grading⟩ :
              Q.grading 0) : Q.carrier)) from rfl,
      comm_coe_tmul_coe, zero_mul,
      show ((-1 : ℤˣ) ^ (0 : ZMod 2)) = 1 from
        (sgn_eq_neg_one_uzpow 0).symm.trans sgn_zero,
      one_smul]
  calc (gtensorComm P Q).toAlgEquiv (toCA (x ᵍ⊗ₜ[K'] (1 : Q.carrier)))
      = (gtensorComm P Q).toAlgEquiv
          (toCA ((evenPart P.grading x + oddPart P.grading x)
            ᵍ⊗ₜ[K'] (1 : Q.carrier))) := by
        rw [evenPart_add_oddPart]
    _ = (gtensorComm P Q).toAlgEquiv
          (toCA ((evenPart P.grading x) ᵍ⊗ₜ[K'] (1 : Q.carrier)))
        + (gtensorComm P Q).toAlgEquiv
          (toCA ((oddPart P.grading x) ᵍ⊗ₜ[K'] (1 : Q.carrier))) := by
        rw [add_gtmulCA, map_add]
    _ = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K'] evenPart P.grading x)
        + toCA ((1 : Q.carrier) ᵍ⊗ₜ[K'] oddPart P.grading x) := by
        rw [hsplit 0 _ (evenPart_mem P.grading x),
          hsplit 1 _ (oddPart_mem P.grading x)]
    _ = toCA ((1 : Q.carrier) ᵍ⊗ₜ[K'] x) := by
        rw [← gtmulCA_add, evenPart_add_oddPart]

private theorem gtensorComm_one_tmul {P Q : SuperAlgebra K'} (y : Q.carrier) :
    (gtensorComm P Q).toAlgEquiv (toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] y))
      = toCA (y ᵍ⊗ₜ[K'] (1 : P.carrier)) := by
  have hsplit : ∀ (j : ZMod 2) (z : Q.carrier), z ∈ Q.grading j →
      (gtensorComm P Q).toAlgEquiv (toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] z))
        = toCA (z ᵍ⊗ₜ[K'] (1 : P.carrier)) := by
    intro j z hz
    show comm P.grading Q.grading ((1 : P.carrier) ᵍ⊗ₜ[K'] z)
      = (z ᵍ⊗ₜ[K'] (1 : P.carrier))
    rw [show ((1 : P.carrier) ᵍ⊗ₜ[K'] z : P.grading ᵍ⊗[K'] Q.grading)
        = (((⟨(1 : P.carrier), SetLike.one_mem_graded P.grading⟩ :
              P.grading 0) : P.carrier) ᵍ⊗ₜ[K']
            ((⟨z, hz⟩ : Q.grading j) : Q.carrier)) from rfl,
      comm_coe_tmul_coe, mul_zero,
      show ((-1 : ℤˣ) ^ (0 : ZMod 2)) = 1 from
        (sgn_eq_neg_one_uzpow 0).symm.trans sgn_zero,
      one_smul]
  calc (gtensorComm P Q).toAlgEquiv (toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] y))
      = (gtensorComm P Q).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K']
            (evenPart Q.grading y + oddPart Q.grading y))) := by
        rw [evenPart_add_oddPart]
    _ = (gtensorComm P Q).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] evenPart Q.grading y))
        + (gtensorComm P Q).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] oddPart Q.grading y)) := by
        rw [gtmulCA_add, map_add]
    _ = toCA ((evenPart Q.grading y) ᵍ⊗ₜ[K'] (1 : P.carrier))
        + toCA ((oddPart Q.grading y) ᵍ⊗ₜ[K'] (1 : P.carrier)) := by
        rw [hsplit 0 _ (evenPart_mem Q.grading y),
          hsplit 1 _ (oddPart_mem Q.grading y)]
    _ = toCA (y ᵍ⊗ₜ[K'] (1 : P.carrier)) := by
        rw [← add_gtmulCA, evenPart_add_oddPart]

private theorem matrixSuperGtensorRight_one_tmul {P Q : SuperAlgebra K'}
    (p q : ℕ) (N₀ : (Q.matrixSuper p q).carrier) :
    (matrixSuperGtensorRight P Q p q).toAlgEquiv
        (toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] N₀))
      = Matrix.map
          (N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
          (fun z => toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] z)) := by
  show ((gtensorComm Q P).matrixSuper p q).toAlgEquiv
      ((matrixSuperGtensor Q P p q).toAlgEquiv
        ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv
          (toCA ((1 : P.carrier) ᵍ⊗ₜ[K'] N₀))))
    = _
  rw [gtensorComm_one_tmul,
    show (matrixSuperGtensor Q P p q).toAlgEquiv
        (toCA (N₀ ᵍ⊗ₜ[K'] (1 : P.carrier)))
      = matrixInclLeft Q.grading P.grading
          (N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
        * matrixInclRight (sumParity p q) Q.grading P.grading
          (1 : P.carrier) from
      matrixTensorSuperHom_tmul (sumParity p q) Q.grading P.grading N₀ 1,
    map_one, mul_one]
  show (matrixInclLeft Q.grading P.grading
      (N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)).map
      (gtensorComm Q P).toAlgEquiv = _
  refine Matrix.ext fun r s => ?_
  rw [Matrix.map_apply, matrixInclLeft_apply, Matrix.map_apply]
  exact gtensorComm_tmul_one
    ((N₀ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier) r s)

private theorem matrixSuperGtensorRight_tmul_one_of_mem {P Q : SuperAlgebra K'}
    (p q : ℕ) {d : ZMod 2} {x : P.carrier} (hx : x ∈ P.grading d) :
    (matrixSuperGtensorRight P Q p q).toAlgEquiv
        (toCA (x ᵍ⊗ₜ[K'] (1 : (Q.matrixSuper p q).carrier)))
      = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
          ((sgn (sumParity p q s * d) : ℤˣ) : ℤ) •
            toCA (x ᵍ⊗ₜ[K'] (1 : Q.carrier))) := by
  show ((gtensorComm Q P).matrixSuper p q).toAlgEquiv
      ((matrixSuperGtensor Q P p q).toAlgEquiv
        ((gtensorComm P (Q.matrixSuper p q)).toAlgEquiv
          (toCA (x ᵍ⊗ₜ[K'] (1 : (Q.matrixSuper p q).carrier)))))
    = _
  rw [gtensorComm_tmul_one,
    show (matrixSuperGtensor Q P p q).toAlgEquiv
        (toCA ((1 : (Q.matrixSuper p q).carrier) ᵍ⊗ₜ[K'] x))
      = matrixInclLeft Q.grading P.grading
          (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) Q.carrier)
        * matrixInclRight (sumParity p q) Q.grading P.grading x from
      matrixTensorSuperHom_tmul (sumParity p q) Q.grading P.grading 1 x,
    map_one, one_mul, matrixInclRight_apply, sdiag_of_mem _ _ _ hx]
  refine Matrix.ext fun r s => ?_
  show (gtensorComm Q P).toAlgEquiv
      (Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
          ((sgn (sumParity p q s * d) : ℤˣ) : ℤ) •
            toCA ((1 : Q.carrier) ᵍ⊗ₜ[K'] x)) r s)
    = Matrix.diagonal (fun s : Fin p ⊕ Fin q =>
        ((sgn (sumParity p q s * d) : ℤˣ) : ℤ) •
          toCA (x ᵍ⊗ₜ[K'] (1 : Q.carrier))) r s
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zsmul, gtensorComm_one_tmul]
  · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs, map_zero]

end Generic

/-! ### Generic collapse distributivity -/

section Collapse

variable {K' : Type*} [CommRing K']
variable {A : Type*} [Ring A] [Algebra K' A]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [AddCommGroup N] [Module K' N] [Module A N] [IsScalarTower K' A N]

private theorem freeCollapse_mulVec_left (X : Matrix n n A) (v : n → A) (w : N) (j : n) :
    RelTensor.freeCollapse (RelTensor.mk K' A (n → A) N (X *ᵥ v) w) j
      = ∑ l, X j l • RelTensor.freeCollapse (RelTensor.mk K' A (n → A) N v w) l := by
  rw [RelTensor.freeCollapse_mk, RelTensor.freeCollapse_mk]
  show (∑ l, X j l * v l) • w = ∑ l, X j l • (v l • w)
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun l _ => mul_smul (X j l) (v l) w

end Collapse

/-! ### Homogeneous-generator induction for `RelTensor` -/

section HomogInduction

variable {K' : Type*} [CommRing K']
variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K' M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K' M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K' N] [Module A N]

@[elab_as_elim]
private theorem relTensor_induction_on_left_homog
    {motive : M ⊗[A;K'] N → Prop} (z : M ⊗[A;K'] N)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (m : M) (n : N), m ∈ ℳ j →
      motive (RelTensor.mk K' A M N m n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z := by
  induction z using RelTensor.induction_on with
  | zero => exact zero
  | mk m n =>
      induction m using DirectSum.Decomposition.inductionOn ℳ with
      | zero =>
          rw [show RelTensor.mk K' A M N (0 : M) n = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | add m m' hm hm' =>
          rw [show RelTensor.mk K' A M N (m + m') n
              = RelTensor.mk K' A M N m n + RelTensor.mk K' A M N m' n from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hm hm'
      | homogeneous xm =>
          exact homog _ xm.1 n xm.2
  | add x y hx hy => exact add x y hx hy

end HomogInduction

/-! ### Additive induction on a folded graded tensor product -/

section GtInduction

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A] {B : Type*} [Ring B] [Algebra R B]
variable (𝒜 : ZMod 2 → Submodule R A) (ℬ : ZMod 2 → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

@[elab_as_elim]
private theorem gtensor_induction_on {p : (𝒜 ᵍ⊗[R] ℬ) → Prop} (x : 𝒜 ᵍ⊗[R] ℬ)
    (tmul : ∀ (u : A) (w : B), p (u ᵍ⊗ₜ[R] w))
    (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) :
    p x := by
  have key : ∀ t : A ⊗[R] B, p (GradedTensorProduct.of R 𝒜 ℬ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact zero
    | tmul u w => exact tmul u w
    | add x y hx hy =>
        rw [map_add]
        exact add _ _ hx hy
  have h := key ((GradedTensorProduct.of R 𝒜 ℬ).symm x)
  rwa [GradedTensorProduct.symm_of_of] at h

end GtInduction


variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

attribute [local instance 500] leftModule rightModule

/-! ### The `•`/`*ᵥ` bridge at the two route columns

The three lemmas below are the concrete content of the verdict's "the target
column already carries the triple-tensor action": `Bimod.FusionColumn`'s
pulled-back `Module P.carrier` instance at `P := (D_a ᵍ⊗ D_b) ᵍ⊗ D_c` is, by
`FusionColumn.smul_def` + `Matrix.smul_eq_mulVec`, DEFINITIONALLY `mulVec` by
the route matrix.  Hence item 4's correspondence lemmas — stated below with
`*ᵥ` to dodge the instance ambiguity of a bare `•` at the column — say exactly
that the column dictionaries are isomorphisms of `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-modules,
and consumers may read them in either spelling for free. -/

theorem routeL_column_smul_eq_mulVec
    (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (w : FusionColumn (Γ.gaugeRouteL a b c)) :
    y • w = (Γ.gaugeRouteL a b c).toAlgEquiv y *ᵥ w := rfl

theorem routeR_column_smul_eq_mulVec
    (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (w : FusionColumn (Γ.gaugeRouteR a b c)) :
    y • w = (Γ.gaugeRouteR a b c).toAlgEquiv y *ᵥ w := rfl

theorem routeR'_column_smul_eq_mulVec
    (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (w : FusionColumn (Γ.gaugeRouteR' a b c)) :
    y • w = (Γ.gaugeRouteR' a b c).toAlgEquiv y *ᵥ w := rfl

/-! ### `gmulVecMap`: the column-side transport of a matrix element -/

/-- **The column-side map of a matrix element** `T : M_σ(D_{(a+b)+c})`
(§10 roadmap item 5, the Γ-port of `Bimod.PentagonB.mulVecMap`): both
`FusionColumn (Γ.gaugeRouteL a b c)` and `FusionColumn (Γ.gaugeRouteR' a b c)`
are literally the column type `Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL
a b c).2 → (Γ.D (a+b+c)).carrier` — `gaugeRouteR'` (the frame-aligned right
route, `Gauge/GaugeRoutes.lean`) shares `gaugeRouteL`'s target superalgebra
exactly — so the map is plain `Matrix.mulVec`, with no size or value cast and
in particular **no `hsz` hypothesis**. -/
noncomputable def gmulVecMap
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) :
    FusionColumn (Γ.gaugeRouteL a b c) →ₗ[K] FusionColumn (Γ.gaugeRouteR' a b c) where
  toFun v := T *ᵥ v
  map_add' u v := Matrix.mulVec_add T u v
  map_smul' k v := Matrix.mulVec_smul T k v

theorem gmulVecMap_apply
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier)
    (v : FusionColumn (Γ.gaugeRouteL a b c)) :
    gmulVecMap K Γ a b c T v = T *ᵥ v := rfl

/-- **`gmulVecMap` is right `D_{(a+b)+c}`-equivariant** (port of
`mulVecMap_rightEquiv`, `Bimod/TDict.lean:114`): entries multiply on the left
of the coefficients, the right action on the right — plain associativity, i.e.
the `SMulCommClass` of the matrix action and the right action registered by
`Bimod.FusionColumn`. -/
theorem gmulVecMap_rightEquiv
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier)
    (τ : (Γ.D (a + b + c)).carrier) (v : FusionColumn (Γ.gaugeRouteL a b c)) :
    gmulVecMap K Γ a b c T (MulOpposite.op τ • v)
      = MulOpposite.op τ • gmulVecMap K Γ a b c T v := by
  show T *ᵥ (MulOpposite.op τ • v) = MulOpposite.op τ • (T *ᵥ v)
  rw [← Matrix.smul_eq_mulVec, ← Matrix.smul_eq_mulVec]
  exact smul_comm T (MulOpposite.op τ) v

/-- **`gmulVecMap` is graded** (port of `mulVecMap_mem_grading`,
`Bimod/TDict.lean:129`): if `T` has degree `e`, `gmulVecMap T` maps the
degree-`j` layer of `FusionColumn (Γ.gaugeRouteL a b c)` into the
degree-`(j+e)` layer of `FusionColumn (Γ.gaugeRouteR' a b c)` — entry degrees
add (`Bimod.columnGrading_smul_mem`; `(P.matrixSuper p q).grading` IS
`matrixGradingA (sumParity p q) P.grading`, so no bridge is needed). -/
theorem gmulVecMap_mem_grading
    {T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier} {e : ZMod 2}
    (hT : T ∈ ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).grading e)
    {j : ZMod 2} {v : FusionColumn (Γ.gaugeRouteL a b c)}
    (hv : v ∈ FusionColumn.grading (Γ.gaugeRouteL a b c) j) :
    gmulVecMap K Γ a b c T v
      ∈ FusionColumn.grading (Γ.gaugeRouteR' a b c) (j + e) := by
  show T • v ∈ columnGrading (sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2)
      (Γ.D (a + b + c)).grading (j + e)
  rw [add_comm j e]
  exact columnGrading_smul_mem _ _ hT hv

/-- **`gmulVecMap` is slot-equivariant for the FULL triple-tensor action**
(port of `mulVecMap_slot_equivariant`, `Bimod/TDict.lean:149`), *given* the
`pentagonT`-shaped intertwining hypothesis on `T` (`hT_int`; at the concrete
gauges this is the finite matrix identity discharged per triple from the
generated route-image literals, §10 of the design memo): for homogeneous `y`
of degree `j` in the triple tensor,
`gmulVecMap T (routeL y *ᵥ v) = sgn (j·e) • (routeR' y *ᵥ gmulVecMap T v)`.
Pure `Matrix.mulVec_mulVec` chasing plus the sign-squaring identity
`sgn_mul_self'`; no `Γ`-specific content, no column dictionary. -/
theorem gmulVecMap_slot_equivariant
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * (Γ.gaugeRouteL a b c).toAlgEquiv y))
    {j : ZMod 2} {y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier}
    (hy : y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j)
    (v : FusionColumn (Γ.gaugeRouteL a b c)) :
    gmulVecMap K Γ a b c T ((Γ.gaugeRouteL a b c).toAlgEquiv y *ᵥ v)
      = ((sgn (j * e) : ℤˣ) : ℤ) •
          ((Γ.gaugeRouteR' a b c).toAlgEquiv y *ᵥ gmulVecMap K Γ a b c T v) := by
  have hint := hT_int hy
  set TM : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Γ.D (a + b + c)).carrier := T with hTdef
  set Y : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Γ.D (a + b + c)).carrier := (Γ.gaugeRouteL a b c).toAlgEquiv y with hYdef
  set X : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Γ.D (a + b + c)).carrier := (Γ.gaugeRouteR' a b c).toAlgEquiv y with hXdef
  set vraw : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2
      → (Γ.D (a + b + c)).carrier := v with hvdef
  show TM *ᵥ (Y *ᵥ vraw) = ((sgn (j * e) : ℤˣ) : ℤ) • (X *ᵥ (TM *ᵥ vraw))
  have hcomm : TM * Y = ((sgn (j * e) : ℤˣ) : ℤ) • (X * TM) := by
    have h1 : ((sgn (j * e) : ℤˣ) : ℤ) • (((sgn (j * e) : ℤˣ) : ℤ) • (TM * Y))
        = ((sgn (j * e) : ℤˣ) : ℤ) • (X * TM) :=
      congrArg (fun w => ((sgn (j * e) : ℤˣ) : ℤ) • w) hint.symm
    rw [smul_smul,
      show ((sgn (j * e) : ℤˣ) : ℤ) * ((sgn (j * e) : ℤˣ) : ℤ) = 1 from by
        rw [← Units.val_mul, sgn_mul_self', Units.val_one],
      one_smul] at h1
    exact h1
  have e1 : TM *ᵥ (Y *ᵥ vraw) = (TM * Y) *ᵥ vraw := Matrix.mulVec_mulVec vraw TM Y
  have e2 : (TM * Y) *ᵥ vraw
      = (((sgn (j * e) : ℤˣ) : ℤ) • (X * TM)) *ᵥ vraw := congrArg (· *ᵥ vraw) hcomm
  have e3 : (((sgn (j * e) : ℤˣ) : ℤ) • (X * TM)) *ᵥ vraw
      = ((sgn (j * e) : ℤˣ) : ℤ) • ((X * TM) *ᵥ vraw) := Matrix.smul_mulVec _ _ _
  have e4 : (X * TM) *ᵥ vraw = X *ᵥ (TM *ᵥ vraw) := (Matrix.mulVec_mulVec vraw X TM).symm
  rw [e1, e2, e3, e4]

/-- **`gmulVecMap` by a unit matrix is bijective** (port of
`mulVecMap_bijective`, `Bimod/TDict.lean:196`): mutual inverse to
`gmulVecMap (↑hT.unit⁻¹)`, via `Matrix.mulVec_mulVec`/`Matrix.one_mulVec`. -/
theorem gmulVecMap_bijective
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) (hT : IsUnit T) :
    Function.Bijective (gmulVecMap K Γ a b c T) := by
  set Tinv : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier := ↑hT.unit⁻¹ with hTinvdef
  have hTTinv : T * Tinv = 1 := hTinvdef ▸ hT.mul_val_inv
  have hTinvT : Tinv * T = 1 := hTinvdef ▸ hT.val_inv_mul
  refine Function.bijective_iff_has_inverse.mpr ⟨fun w => Tinv *ᵥ w, ?_, ?_⟩
  · intro v
    show Tinv *ᵥ (T *ᵥ v) = v
    have e1 : Tinv *ᵥ (T *ᵥ v) = (Tinv * T) *ᵥ v := Matrix.mulVec_mulVec v Tinv T
    have e2 : (Tinv * T) *ᵥ v
        = (1 : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
          (Γ.gaugeSizeL a b c).2).carrier) *ᵥ v :=
      congrArg (· *ᵥ v) hTinvT
    exact e1.trans (e2.trans (Matrix.one_mulVec v))
  · intro v
    show T *ᵥ (Tinv *ᵥ v) = v
    have e1 : T *ᵥ (Tinv *ᵥ v) = (T * Tinv) *ᵥ v := Matrix.mulVec_mulVec v T Tinv
    have e2 : (T * Tinv) *ᵥ v
        = (1 : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
          (Γ.gaugeSizeL a b c).2).carrier) *ᵥ v :=
      congrArg (· *ᵥ v) hTTinv
    exact e1.trans (e2.trans (Matrix.one_mulVec v))


/-! ### The two `gaugeRouteL` entry chases -/

theorem routeL_left_entry (w : ((Γ.D a).gtensor (Γ.D b)).carrier)
    (i j : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    (Γ.gaugeRouteL a b c).toAlgEquiv
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
          (Γ.D c).grading w) i j
      = (Γ.fuse (a + b) c).toAlgEquiv
          (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading
            ((Γ.fuse a b).toAlgEquiv w
              ((gblIndexEquiv K Γ a b c).symm i).1 ((gblIndexEquiv K Γ a b c).symm j).1))
          ((gblIndexEquiv K Γ a b c).symm i).2 ((gblIndexEquiv K Γ a b c).symm j).2 := by
  show ((matrixSuperComp (Γ.D (a + b + c)) (Γ.size a b).1 (Γ.size a b).2
        (Γ.size (a + b) c).1 (Γ.size (a + b) c).2).toAlgEquiv
      (((Γ.fuse (a + b) c).matrixSuper (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
        ((matrixSuperGtensor (Γ.D (a + b)) (Γ.D c) (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
          (((Γ.fuse a b).gtensorCongr (SuperAlgEquiv.refl (Γ.D c))).toAlgEquiv
            (toCA (w ᵍ⊗ₜ[K] (1 : (Γ.D c).carrier))))))) i j = _
  rw [gtensorCongr_refl_right_tmul]
  show ((matrixSuperComp (Γ.D (a + b + c)) (Γ.size a b).1 (Γ.size a b).2
        (Γ.size (a + b) c).1 (Γ.size (a + b) c).2).toAlgEquiv
      (((Γ.fuse (a + b) c).matrixSuper (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
        ((matrixSuperGtensor (Γ.D (a + b)) (Γ.D c) (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
          (toCA (((Γ.fuse a b).toAlgEquiv w :
              Matrix (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
                (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) (Γ.D (a + b)).carrier)
            ᵍ⊗ₜ[K] (1 : (Γ.D c).carrier)))))) i j = _
  rw [matrixSuperGtensor_tmul_one, matrixSuperComp_entry, matrixSuper_entry,
    matrixInclLeft_apply]
  rfl

theorem routeL_right_entry {k : ZMod 2} {z : (Γ.D c).carrier}
    (hz : z ∈ (Γ.D c).grading k)
    (i j : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    (Γ.gaugeRouteL a b c).toAlgEquiv
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
          (Γ.D c).grading z) i j
      = if ((gblIndexEquiv K Γ a b c).symm i).1 = ((gblIndexEquiv K Γ a b c).symm j).1 then
          ((sgn (sumParity (Γ.size a b).1 (Γ.size a b).2
              ((gblIndexEquiv K Γ a b c).symm i).1 * k) : ℤˣ) : ℤ) •
            (Γ.fuse (a + b) c).toAlgEquiv
              (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
              ((gblIndexEquiv K Γ a b c).symm i).2 ((gblIndexEquiv K Γ a b c).symm j).2
        else 0 := by
  show ((matrixSuperComp (Γ.D (a + b + c)) (Γ.size a b).1 (Γ.size a b).2
        (Γ.size (a + b) c).1 (Γ.size (a + b) c).2).toAlgEquiv
      (((Γ.fuse (a + b) c).matrixSuper (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
        ((matrixSuperGtensor (Γ.D (a + b)) (Γ.D c) (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
          (((Γ.fuse a b).gtensorCongr (SuperAlgEquiv.refl (Γ.D c))).toAlgEquiv
            (toCA ((1 : ((Γ.D a).gtensor (Γ.D b)).carrier) ᵍ⊗ₜ[K] z)))))) i j = _
  rw [gtensorCongr_refl_right_tmul, map_one]
  show ((matrixSuperComp (Γ.D (a + b + c)) (Γ.size a b).1 (Γ.size a b).2
        (Γ.size (a + b) c).1 (Γ.size (a + b) c).2).toAlgEquiv
      (((Γ.fuse (a + b) c).matrixSuper (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
        ((matrixSuperGtensor (Γ.D (a + b)) (Γ.D c) (Γ.size a b).1 (Γ.size a b).2).toAlgEquiv
          (toCA ((1 : Matrix (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
              (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) (Γ.D (a + b)).carrier)
            ᵍ⊗ₜ[K] z))))) i j = _
  rw [matrixSuperGtensor_one_tmul, matrixSuperComp_entry, matrixSuper_entry,
    matrixInclRight_apply, sdiag_of_mem _ _ _ hz, Matrix.diagonal_apply]
  show (Γ.fuse (a + b) c).toAlgEquiv
      (if ((gblIndexEquiv K Γ a b c).symm i).1 = ((gblIndexEquiv K Γ a b c).symm j).1 then
          ((sgn (sumParity (Γ.size a b).1 (Γ.size a b).2
              ((gblIndexEquiv K Γ a b c).symm i).1 * k) : ℤˣ) : ℤ) •
            (toCA ((1 : (Γ.D (a + b)).carrier) ᵍ⊗ₜ[K] z))
        else 0)
      ((gblIndexEquiv K Γ a b c).symm i).2 ((gblIndexEquiv K Γ a b c).symm j).2 = _
  by_cases hrs : ((gblIndexEquiv K Γ a b c).symm i).1 = ((gblIndexEquiv K Γ a b c).symm j).1
  · rw [if_pos hrs, if_pos hrs, map_zsmul (Γ.fuse (a + b) c).toAlgEquiv]
    rfl
  · rw [if_neg hrs, if_neg hrs, map_zero]
    rfl


/-! ### `gblColumnEquiv` is a module map: the two generator families -/

private noncomputable def gblOfRaw :
    (FusionColumn (Γ.fuse a b) ⊗[(Γ.D (a + b)).carrier;K] FusionColumn (Γ.fuse (a + b) c))
      →ₗ[K] GBL Γ a b c :=
  LinearMap.id

private theorem gblOfRaw_apply
    (z : FusionColumn (Γ.fuse a b) ⊗[(Γ.D (a + b)).carrier;K]
      FusionColumn (Γ.fuse (a + b) c)) :
    gblOfRaw K Γ a b c z = z := rfl

theorem gblColumnEquiv_includeLeft_mk (w : ((Γ.D a).gtensor (Γ.D b)).carrier)
    (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c)) :
    gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w
          • GBL.mk Γ a b c u v)
      = (Γ.gaugeRouteL a b c).toAlgEquiv
          (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w)
        *ᵥ gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v) := by
  have hact : (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading w) • GBL.mk Γ a b c u v
      = GBL.mk Γ a b c (w • u) v := by
    rw [GBL.gtensorABCRaw_smul_def, gtensorLeftActionHom_includeLeft]
    exact leftActionEnd_mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) w u v
  have hwu : w • u = (Γ.fuse a b).toAlgEquiv w *ᵥ u := rfl
  funext k
  rw [hact, hwu, gblColumnEquiv_apply]
  show RelTensor.freeCollapse
      (RelTensor.mk K (Γ.D (a + b)).carrier
        ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) → (Γ.D (a + b)).carrier)
        (FusionColumn (Γ.fuse (a + b) c))
        ((Γ.fuse a b).toAlgEquiv w *ᵥ u) v)
      ((gblIndexEquiv K Γ a b c).symm k).1 ((gblIndexEquiv K Γ a b c).symm k).2 = _
  rw [freeCollapse_mulVec_left]
  show (∑ l, (Γ.fuse a b).toAlgEquiv w ((gblIndexEquiv K Γ a b c).symm k).1 l •
      RelTensor.freeCollapse (GBL.mk Γ a b c u v) l : FusionColumn (Γ.fuse (a + b) c))
      ((gblIndexEquiv K Γ a b c).symm k).2 = _
  have hsum : (∑ l, (Γ.fuse a b).toAlgEquiv w ((gblIndexEquiv K Γ a b c).symm k).1 l •
        RelTensor.freeCollapse (GBL.mk Γ a b c u v) l : FusionColumn (Γ.fuse (a + b) c))
        ((gblIndexEquiv K Γ a b c).symm k).2
      = ∑ l, ((Γ.fuse a b).toAlgEquiv w ((gblIndexEquiv K Γ a b c).symm k).1 l •
          RelTensor.freeCollapse (GBL.mk Γ a b c u v) l) ((gblIndexEquiv K Γ a b c).symm k).2 :=
    Finset.sum_apply _ Finset.univ _
  rw [hsum]
  have hZ : ∀ (l : Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
      (x : FusionColumn (Γ.fuse (a + b) c)),
      (Γ.fuse a b).toAlgEquiv w ((gblIndexEquiv K Γ a b c).symm k).1 l • x
        = ((Γ.fuse (a + b) c).toAlgEquiv
              (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading
                ((Γ.fuse a b).toAlgEquiv w ((gblIndexEquiv K Γ a b c).symm k).1 l))
            : Matrix (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
                (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
                (Γ.D (a + b + c)).carrier)
          *ᵥ x := fun _ _ => rfl
  rw [Finset.sum_congr rfl fun l _ =>
    congrFun (hZ l (RelTensor.freeCollapse (GBL.mk Γ a b c u v) l))
      ((gblIndexEquiv K Γ a b c).symm k).2]
  show (∑ l : Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2,
      ∑ kk : Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2,
        (Γ.fuse (a + b) c).toAlgEquiv
            (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading
              ((Γ.fuse a b).toAlgEquiv w ((gblIndexEquiv K Γ a b c).symm k).1 l))
            ((gblIndexEquiv K Γ a b c).symm k).2 kk
          * RelTensor.freeCollapse (GBL.mk Γ a b c u v) l kk)
    = ∑ kp, (Γ.gaugeRouteL a b c).toAlgEquiv
          (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
            (Γ.D c).grading w) k kp
        * gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v) kp
  conv_rhs => rw [← Equiv.sum_comp (gblIndexEquiv K Γ a b c)
      (fun kp => (Γ.gaugeRouteL a b c).toAlgEquiv
          (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
            (Γ.D c).grading w) k kp
        * gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v) kp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun kk _ => ?_
  have hentry := routeL_left_entry K Γ a b c w k (gblIndexEquiv K Γ a b c (l, kk))
  rw [(gblIndexEquiv K Γ a b c).symm_apply_apply] at hentry
  rw [hentry, gblColumnEquiv_apply, (gblIndexEquiv K Γ a b c).symm_apply_apply]

/-! ### The Koszul generator family of `gblColumnEquiv` -/

private theorem zmod2_c_sign : ∀ j k r : ZMod 2, k * j + (j + r) * k = r * k := by decide

theorem gaugeZZ_comm {d k : ZMod 2} {c0 : (Γ.D (a + b)).carrier}
    (hc0 : c0 ∈ (Γ.D (a + b)).grading d)
    {z : (Γ.D c).carrier} (hz : z ∈ (Γ.D c).grading k) :
    ((Γ.fuse (a + b) c).toAlgEquiv
        (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0)
      * (Γ.fuse (a + b) c).toAlgEquiv
          (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
        : Matrix (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
            (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2) (Γ.D (a + b + c)).carrier)
      = ((sgn (d * k) : ℤˣ) : ℤ) •
          ((Γ.fuse (a + b) c).toAlgEquiv
              (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
            * (Γ.fuse (a + b) c).toAlgEquiv
                (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0)) := by
  have h1 := map_mul (Γ.fuse (a + b) c).toAlgEquiv
    (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0)
    (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
  have h2 := includeLeft_mul_includeRight_supercomm
    (Γ.D (a + b)).grading (Γ.D c).grading hc0 hz
  have h3 := map_mul (Γ.fuse (a + b) c).toAlgEquiv
    (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
    (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0)
  calc (Γ.fuse (a + b) c).toAlgEquiv
        (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0)
      * (Γ.fuse (a + b) c).toAlgEquiv
        (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
      = (Γ.fuse (a + b) c).toAlgEquiv
          (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0
            * GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z) :=
        h1.symm
    _ = (Γ.fuse (a + b) c).toAlgEquiv
          (((sgn (d * k) : ℤˣ) : ℤ) •
            (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z
              * GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0)) := by
        rw [h2]
    _ = ((sgn (d * k) : ℤˣ) : ℤ) •
          (Γ.fuse (a + b) c).toAlgEquiv
            (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z
              * GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0) :=
        map_zsmul (Γ.fuse (a + b) c).toAlgEquiv _ _
    _ = ((sgn (d * k) : ℤˣ) : ℤ) •
          ((Γ.fuse (a + b) c).toAlgEquiv
              (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
            * (Γ.fuse (a + b) c).toAlgEquiv
                (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading c0)) :=
        congrArg (fun w => ((sgn (d * k) : ℤˣ) : ℤ) • w) h3

theorem gblColumnEquiv_includeRight_mk {j k : ZMod 2} {z : (Γ.D c).carrier}
    (hz : z ∈ (Γ.D c).grading k)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) :
    gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
          • GBL.mk Γ a b c u v)
      = (Γ.gaugeRouteL a b c).toAlgEquiv
          (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z)
        *ᵥ gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v) := by
  have hemb : (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
      (Γ.D c).grading z) • GBL.mk Γ a b c u v = z • GBL.mk Γ a b c u v :=
    GBL.cEmbed K Γ a b c _ z rfl (GBL.mk Γ a b c u v)
  have hcslot := GBL.cslot_smul_mk_of_mem Γ a b c hz hu v
  funext idx
  set p1 := ((gblIndexEquiv K Γ a b c).symm idx).1 with hp1
  set p2 := ((gblIndexEquiv K Γ a b c).symm idx).2 with hp2
  have step : gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
          • GBL.mk Γ a b c u v) idx
      = ((sgn (k * j) : ℤˣ) : ℤ) • RelTensor.freeCollapse (GBL.mk Γ a b c u (z • v)) p1 p2 := by
    rw [hemb, hcslot, map_zsmul]
    show (((sgn (k * j) : ℤˣ) : ℤ) • gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u (z • v))) idx = _
    rw [show (((sgn (k * j) : ℤˣ) : ℤ) •
          gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u (z • v))) idx
        = ((sgn (k * j) : ℤˣ) : ℤ) •
            (gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u (z • v)) idx) from rfl,
      gblColumnEquiv_apply]
  rw [step]
  have hfc : RelTensor.freeCollapse (GBL.mk Γ a b c u (z • v)) p1 = u p1 • (z • v) :=
    congrFun (RelTensor.freeCollapse_mk u (z • v)) p1
  rw [hfc]
  set Zz : Matrix (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
      (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2) (Γ.D (a + b + c)).carrier :=
    (Γ.fuse (a + b) c).toAlgEquiv
      (GradedTensorProduct.includeRight (Γ.D (a + b)).grading (Γ.D c).grading z)
    with hZzdef
  set Zu : Matrix (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
      (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2) (Γ.D (a + b + c)).carrier :=
    (Γ.fuse (a + b) c).toAlgEquiv
      (GradedTensorProduct.includeLeft (Γ.D (a + b)).grading (Γ.D c).grading (u p1))
    with hZudef
  have hzv : z • v = Zz *ᵥ v := rfl
  have hux : ∀ w : FusionColumn (Γ.fuse (a + b) c), u p1 • w = Zu *ᵥ w := fun _ => rfl
  rw [hzv, hux]
  have hup1 : u p1 ∈ (Γ.D (a + b)).grading
      (j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) := hu p1
  have hcomm : Zu * Zz
      = ((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ) • (Zz * Zu) :=
    gaugeZZ_comm K Γ a b c hup1 hz
  have huv : Zu *ᵥ v = u p1 • v := (hux v).symm
  have e1 : Zu *ᵥ Zz *ᵥ v = (Zu * Zz) *ᵥ v := Matrix.mulVec_mulVec v Zu Zz
  have e2 : (Zu * Zz) *ᵥ v
      = (((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ) • (Zz * Zu)) *ᵥ v :=
    congrArg (· *ᵥ v) hcomm
  have e3 : (((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
        • (Zz * Zu)) *ᵥ v
      = ((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
        • ((Zz * Zu) *ᵥ v) :=
    Matrix.smul_mulVec _ _ _
  have e4 : (Zz * Zu) *ᵥ v = Zz *ᵥ (Zu *ᵥ v) := (Matrix.mulVec_mulVec v Zz Zu).symm
  have echain : (Zu *ᵥ Zz *ᵥ v) p2
      = ((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
        • (Zz *ᵥ (u p1 • v)) p2 :=
    calc (Zu *ᵥ Zz *ᵥ v) p2 = ((Zu * Zz) *ᵥ v) p2 := congrFun e1 p2
      _ = ((((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
            • (Zz * Zu)) *ᵥ v) p2 := congrFun e2 p2
      _ = (((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
            • ((Zz * Zu) *ᵥ v)) p2 := congrFun e3 p2
      _ = ((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
            • (((Zz * Zu) *ᵥ v) p2) := rfl
      _ = ((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
            • ((Zz *ᵥ (Zu *ᵥ v)) p2) := congrArg _ (congrFun e4 p2)
      _ = ((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
            • ((Zz *ᵥ (u p1 • v)) p2) := by rw [huv]
  rw [show ((sgn (k * j) : ℤˣ) : ℤ) • (Zu *ᵥ Zz *ᵥ v) p2
        = ((sgn (k * j) : ℤˣ) : ℤ) •
            (((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ)
              • (Zz *ᵥ (u p1 • v)) p2) from congrArg _ echain,
    smul_smul]
  rw [show (((sgn (k * j) : ℤˣ) : ℤ)
      * ((sgn ((j + sumParity (Γ.size a b).1 (Γ.size a b).2 p1) * k) : ℤˣ) : ℤ))
      = ((sgn (sumParity (Γ.size a b).1 (Γ.size a b).2 p1 * k) : ℤˣ) : ℤ) from by
    rw [← Units.val_mul, ← sgn_add, zmod2_c_sign]]
  set ww : FusionColumn (Γ.fuse (a + b) c) :=
    RelTensor.freeCollapse (GBL.mk Γ a b c u v) p1 with hwdef
  have hfc2 : u p1 • v = ww := (congrFun (RelTensor.freeCollapse_mk u v) p1).symm
  rw [hfc2]
  show ((sgn (sumParity (Γ.size a b).1 (Γ.size a b).2 p1 * k) : ℤˣ) : ℤ) •
      (∑ s' : Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2, Zz p2 s' * ww s')
    = ∑ idx' : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2,
        (Γ.gaugeRouteL a b c).toAlgEquiv
            (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
              (Γ.D c).grading z) idx idx'
          * gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v) idx'
  rw [← Equiv.sum_comp (gblIndexEquiv K Γ a b c)
    (fun idx' => (Γ.gaugeRouteL a b c).toAlgEquiv
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
          (Γ.D c).grading z) idx idx'
      * gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v) idx'),
    Fintype.sum_prod_type]
  rw [Finset.smul_sum]
  symm
  rw [Finset.sum_eq_single p1
    (fun s _ hsne => Finset.sum_eq_zero fun s' _ => by
      have hentry := routeL_right_entry K Γ a b c hz idx (gblIndexEquiv K Γ a b c (s, s'))
      rw [(gblIndexEquiv K Γ a b c).symm_apply_apply] at hentry
      rw [hentry, if_neg (fun heq => hsne (hp1 ▸ heq.symm)), zero_mul])
    (fun hp1nu => absurd (Finset.mem_univ p1) hp1nu)]
  refine Finset.sum_congr rfl fun s' _ => ?_
  have hentry := routeL_right_entry K Γ a b c hz idx (gblIndexEquiv K Γ a b c (p1, s'))
  rw [(gblIndexEquiv K Γ a b c).symm_apply_apply] at hentry
  rw [hentry, if_pos rfl, gblColumnEquiv_apply, (gblIndexEquiv K Γ a b c).symm_apply_apply,
    smul_mul_assoc]

/-! ### `gblColumnEquiv` is a module map (all of `GBL`, all of the triple tensor) -/

theorem gblColumnEquiv_smul_includeLeft (w : ((Γ.D a).gtensor (Γ.D b)).carrier)
    (m : GBL Γ a b c) :
    gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w • m)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w
        • gblColumnEquiv K Γ a b c m := by
  refine RelTensor.induction_on (K := K) (A := (Γ.D (a + b)).carrier)
    (M := FusionColumn (Γ.fuse a b)) (N := FusionColumn (Γ.fuse (a + b) c))
    (motive := fun t => gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w
          • gblOfRaw K Γ a b c t)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w
        • gblColumnEquiv K Γ a b c (gblOfRaw K Γ a b c t)) m ?_ ?_ ?_
  · rw [map_zero, smul_zero, map_zero, smul_zero]
  · intro u v
    rw [gblOfRaw_apply]
    exact gblColumnEquiv_includeLeft_mk K Γ a b c w u v
  · intro t₁ t₂ h₁ h₂
    rw [map_add, smul_add, map_add, map_add, smul_add, h₁, h₂]

theorem gblColumnEquiv_smul_includeRight_of_mem {k : ZMod 2} {z : (Γ.D c).carrier}
    (hz : z ∈ (Γ.D c).grading k) (m : GBL Γ a b c) :
    gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z • m)
      = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
        • gblColumnEquiv K Γ a b c m := by
  refine relTensor_induction_on_left_homog (FusionColumn.grading (Γ.fuse a b))
    (A := (Γ.D (a + b)).carrier) (N := FusionColumn (Γ.fuse (a + b) c))
    (motive := fun t => gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
          • gblOfRaw K Γ a b c t)
      = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
        • gblColumnEquiv K Γ a b c (gblOfRaw K Γ a b c t)) m ?_ ?_ ?_
  · rw [map_zero, smul_zero, map_zero, smul_zero]
  · intro j u v hu
    rw [gblOfRaw_apply]
    exact gblColumnEquiv_includeRight_mk K Γ a b c hz hu v
  · intro t₁ t₂ h₁ h₂
    rw [map_add, smul_add, map_add, map_add, smul_add, h₁, h₂]

theorem gblColumnEquiv_smul_includeRight (z : (Γ.D c).carrier) (m : GBL Γ a b c) :
    gblColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z • m)
      = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
        • gblColumnEquiv K Γ a b c m := by
  obtain ⟨ze, hze, zo, hzo, rfl⟩ :
      ∃ ze, ze ∈ (Γ.D c).grading 0 ∧ ∃ zo, zo ∈ (Γ.D c).grading 1 ∧ z = ze + zo :=
    ⟨_, evenPart_mem (Γ.D c).grading z, _, oddPart_mem (Γ.D c).grading z,
      (evenPart_add_oddPart (Γ.D c).grading z).symm⟩
  rw [map_add, add_smul, map_add, add_smul,
    gblColumnEquiv_smul_includeRight_of_mem K Γ a b c hze,
    gblColumnEquiv_smul_includeRight_of_mem K Γ a b c hzo]

theorem gblColumnEquiv_smul
    (y : ((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (m : GBL Γ a b c) :
    gblColumnEquiv K Γ a b c (y • m) = y • gblColumnEquiv K Γ a b c m := by
  refine gtensor_induction_on ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
    (p := fun t => gblColumnEquiv K Γ a b c (t • m) = t • gblColumnEquiv K Γ a b c m) y ?_ ?_ ?_
  · intro w z
    rw [show (w ᵍ⊗ₜ[K] z : ((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading)
        = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w
          * GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
      from (includeLeft_mul_includeRight _ _ w z).symm,
      mul_smul, gblColumnEquiv_smul_includeLeft, gblColumnEquiv_smul_includeRight, mul_smul]
  · rw [zero_smul, map_zero, zero_smul]
  · intro t₁ t₂ h₁ h₂
    rw [add_smul, map_add, h₁, h₂, add_smul]

/-- **Item 4, left vertex**: the column dictionary `gblColumnEquiv` is an
isomorphism of `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-modules. -/
theorem gblColumnEquiv_gtensor_smul
    (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) (m : GBL Γ a b c) :
    gblColumnEquiv K Γ a b c (y • m)
      = (Γ.gaugeRouteL a b c).toAlgEquiv y *ᵥ gblColumnEquiv K Γ a b c m :=
  gblColumnEquiv_smul K Γ a b c y m

/-! ### The three `gaugeRouteR` entry chases -/

theorem routeR_bslot_entry (y : (Γ.D b).carrier)
    (i j : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    (Γ.gaugeRouteR a b c).toAlgEquiv
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)) i j
      = (Γ.fuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading
            ((Γ.fuse b c).toAlgEquiv
                (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y)
              ((gbrNativeIndexEquiv K Γ a b c).symm i).1
              ((gbrNativeIndexEquiv K Γ a b c).symm j).1))
          ((gbrNativeIndexEquiv K Γ a b c).symm i).2
          ((gbrNativeIndexEquiv K Γ a b c).symm j).2 := by
  show ((matrixSuperComp (Γ.D (a + (b + c))) (Γ.size b c).1 (Γ.size b c).2
        (Γ.size a (b + c)).1 (Γ.size a (b + c)).2).toAlgEquiv
      (((Γ.fuse a (b + c)).matrixSuper (Γ.size b c).1 (Γ.size b c).2).toAlgEquiv
        ((matrixSuperGtensorRight (Γ.D a) (Γ.D (b + c))
              (Γ.size b c).1 (Γ.size b c).2).toAlgEquiv
          (((SuperAlgEquiv.refl (Γ.D a)).gtensorCongr (Γ.fuse b c)).toAlgEquiv
            ((gtensorAssoc (Γ.D a) (Γ.D b) (Γ.D c)).toAlgEquiv
              (toCA (toCA ((1 : (Γ.D a).carrier) ᵍ⊗ₜ[K] y)
                ᵍ⊗ₜ[K] (1 : (Γ.D c).carrier)))))))) i j = _
  rw [gtensorAssoc_tmulCA, gtensorCongr_refl_left_tmul, matrixSuperGtensorRight_one_tmul,
    matrixSuperComp_entry, matrixSuper_entry, Matrix.map_apply]
  rfl

theorem routeR_cslot_entry (z : (Γ.D c).carrier)
    (i j : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    (Γ.gaugeRouteR a b c).toAlgEquiv
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z)
        i j
      = (Γ.fuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading
            ((Γ.fuse b c).toAlgEquiv
                (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z)
              ((gbrNativeIndexEquiv K Γ a b c).symm i).1
              ((gbrNativeIndexEquiv K Γ a b c).symm j).1))
          ((gbrNativeIndexEquiv K Γ a b c).symm i).2
          ((gbrNativeIndexEquiv K Γ a b c).symm j).2 := by
  rw [show GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
      = toCA (toCA ((1 : (Γ.D a).carrier) ᵍ⊗ₜ[K] (1 : (Γ.D b).carrier)) ᵍ⊗ₜ[K] z) from by
    rw [toCA_one_one]; rfl]
  show ((matrixSuperComp (Γ.D (a + (b + c))) (Γ.size b c).1 (Γ.size b c).2
        (Γ.size a (b + c)).1 (Γ.size a (b + c)).2).toAlgEquiv
      (((Γ.fuse a (b + c)).matrixSuper (Γ.size b c).1 (Γ.size b c).2).toAlgEquiv
        ((matrixSuperGtensorRight (Γ.D a) (Γ.D (b + c))
              (Γ.size b c).1 (Γ.size b c).2).toAlgEquiv
          (((SuperAlgEquiv.refl (Γ.D a)).gtensorCongr (Γ.fuse b c)).toAlgEquiv
            ((gtensorAssoc (Γ.D a) (Γ.D b) (Γ.D c)).toAlgEquiv
              (toCA (toCA ((1 : (Γ.D a).carrier) ᵍ⊗ₜ[K] (1 : (Γ.D b).carrier))
                ᵍ⊗ₜ[K] z))))))) i j = _
  rw [gtensorAssoc_tmulCA, gtensorCongr_refl_left_tmul, matrixSuperGtensorRight_one_tmul,
    matrixSuperComp_entry, matrixSuper_entry, Matrix.map_apply]
  rfl

theorem routeR_aslot_entry {d : ZMod 2} {x : (Γ.D a).carrier} (hx : x ∈ (Γ.D a).grading d)
    (i j : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    (Γ.gaugeRouteR a b c).toAlgEquiv
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)) i j
      = if ((gbrNativeIndexEquiv K Γ a b c).symm i).1
            = ((gbrNativeIndexEquiv K Γ a b c).symm j).1 then
          ((sgn (sumParity (Γ.size b c).1 (Γ.size b c).2
              ((gbrNativeIndexEquiv K Γ a b c).symm i).1 * d) : ℤˣ) : ℤ) •
            (Γ.fuse a (b + c)).toAlgEquiv
              (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
              ((gbrNativeIndexEquiv K Γ a b c).symm i).2
              ((gbrNativeIndexEquiv K Γ a b c).symm j).2
        else 0 := by
  show ((matrixSuperComp (Γ.D (a + (b + c))) (Γ.size b c).1 (Γ.size b c).2
        (Γ.size a (b + c)).1 (Γ.size a (b + c)).2).toAlgEquiv
      (((Γ.fuse a (b + c)).matrixSuper (Γ.size b c).1 (Γ.size b c).2).toAlgEquiv
        ((matrixSuperGtensorRight (Γ.D a) (Γ.D (b + c))
              (Γ.size b c).1 (Γ.size b c).2).toAlgEquiv
          (((SuperAlgEquiv.refl (Γ.D a)).gtensorCongr (Γ.fuse b c)).toAlgEquiv
            ((gtensorAssoc (Γ.D a) (Γ.D b) (Γ.D c)).toAlgEquiv
              (toCA (toCA (x ᵍ⊗ₜ[K] (1 : (Γ.D b).carrier))
                ᵍ⊗ₜ[K] (1 : (Γ.D c).carrier)))))))) i j = _
  rw [gtensorAssoc_tmulCA, gtensorCongr_refl_left_tmul, toCA_one_one, map_one,
    matrixSuperGtensorRight_tmul_one_of_mem (K' := K) _ _ hx,
    matrixSuperComp_entry, matrixSuper_entry, Matrix.diagonal_apply]
  show (Γ.fuse a (b + c)).toAlgEquiv
      (if ((gbrNativeIndexEquiv K Γ a b c).symm i).1
            = ((gbrNativeIndexEquiv K Γ a b c).symm j).1 then
          ((sgn (sumParity (Γ.size b c).1 (Γ.size b c).2
              ((gbrNativeIndexEquiv K Γ a b c).symm i).1 * d) : ℤˣ) : ℤ) •
            (toCA (x ᵍ⊗ₜ[K] (1 : (Γ.D (b + c)).carrier)))
        else 0)
      ((gbrNativeIndexEquiv K Γ a b c).symm i).2
      ((gbrNativeIndexEquiv K Γ a b c).symm j).2 = _
  by_cases hrs : ((gbrNativeIndexEquiv K Γ a b c).symm i).1
      = ((gbrNativeIndexEquiv K Γ a b c).symm j).1
  · rw [if_pos hrs, if_pos hrs, map_zsmul (Γ.fuse a (b + c)).toAlgEquiv]
    rfl
  · rw [if_neg hrs, if_neg hrs, map_zero]
    rfl

/-! ### `gbrNativeColumnEquiv` is a module map: the three generator families -/

/-- **A spelling bridge for `GBR`'s triple-tensor action.**  `GaugeParity`
registers `GBR`'s combined action at the two spellings `Superfusion.tensorGrading
(D_a).grading (D_b).grading ᵍ⊗ (D_c).grading` (raw) and
`(((D_a).gtensor (D_b)).gtensor (D_c)).carrier` (bundled).  `Bimod.FusionColumn`'s
own `Slots` bridge registers the column action at the third, *syntactically
distinct* spelling `((D_a).gtensor (D_b)).grading ᵍ⊗ (D_c).grading` — the one an
`includeLeft`/`includeRight` out of `((D_a).gtensor (D_b))` produces.  All three
types are definitionally equal, but instance search does not unfold
`SuperAlgebra.gtensor`, so this local re-registration is what lets the two sides
of the correspondence lemma be stated at the same `y`. -/
noncomputable local instance gbrModuleGtensorRaw :
    Module (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (GBR Γ a b c) :=
  GBR.instModuleGtensorABC K Γ a b c

private noncomputable def gbrOfRaw :
    (FusionColumn (Γ.fuse b c) ⊗[(Γ.D (b + c)).carrier;K] FusionColumn (Γ.fuse a (b + c)))
      →ₗ[K] GBR Γ a b c :=
  LinearMap.id

private theorem gbrOfRaw_apply
    (z : FusionColumn (Γ.fuse b c) ⊗[(Γ.D (b + c)).carrier;K]
      FusionColumn (Γ.fuse a (b + c))) :
    gbrOfRaw K Γ a b c z = z := rfl

theorem gbrNativeColumnEquiv_smul_bEmbed_mk (y : (Γ.D b).carrier)
    (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c))) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
          • GBR.mk Γ a b c u v)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
        • gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) := by
  have hemb : (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y))
        • GBR.mk Γ a b c u v = y • GBR.mk Γ a b c u v :=
    GBR.bEmbed_smul K Γ a b c _ y rfl _ rfl (GBR.mk Γ a b c u v)
  have hyu : y • u = (Γ.fuse b c).toAlgEquiv
      (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y) *ᵥ u := rfl
  funext k
  rw [hemb, GBR.bslot_smul_mk, hyu, gbrNativeColumnEquiv_apply]
  show RelTensor.freeCollapse
      (RelTensor.mk K (Γ.D (b + c)).carrier
        ((Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) → (Γ.D (b + c)).carrier)
        (FusionColumn (Γ.fuse a (b + c)))
        ((Γ.fuse b c).toAlgEquiv
          (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y) *ᵥ u) v)
      ((gbrNativeIndexEquiv K Γ a b c).symm k).1
      ((gbrNativeIndexEquiv K Γ a b c).symm k).2 = _
  rw [freeCollapse_mulVec_left]
  show (∑ l, (Γ.fuse b c).toAlgEquiv
        (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y)
        ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l •
      RelTensor.freeCollapse (GBR.mk Γ a b c u v) l : FusionColumn (Γ.fuse a (b + c)))
      ((gbrNativeIndexEquiv K Γ a b c).symm k).2 = _
  have hsum : (∑ l, (Γ.fuse b c).toAlgEquiv
          (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y)
          ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l •
        RelTensor.freeCollapse (GBR.mk Γ a b c u v) l : FusionColumn (Γ.fuse a (b + c)))
        ((gbrNativeIndexEquiv K Γ a b c).symm k).2
      = ∑ l, ((Γ.fuse b c).toAlgEquiv
            (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y)
            ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l •
          RelTensor.freeCollapse (GBR.mk Γ a b c u v) l)
          ((gbrNativeIndexEquiv K Γ a b c).symm k).2 :=
    Finset.sum_apply _ Finset.univ _
  rw [hsum]
  have hZ : ∀ (l : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
      (x : FusionColumn (Γ.fuse a (b + c))),
      (Γ.fuse b c).toAlgEquiv
          (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y)
          ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l • x
        = ((Γ.fuse a (b + c)).toAlgEquiv
              (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading
                ((Γ.fuse b c).toAlgEquiv
                  (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y)
                  ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l))
            : Matrix (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
                (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
                (Γ.D (a + (b + c))).carrier)
          *ᵥ x := fun _ _ => rfl
  rw [Finset.sum_congr rfl fun l _ =>
    congrFun (hZ l (RelTensor.freeCollapse (GBR.mk Γ a b c u v) l))
      ((gbrNativeIndexEquiv K Γ a b c).symm k).2]
  show (∑ l : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2,
      ∑ kk : Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2,
        (Γ.fuse a (b + c)).toAlgEquiv
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading
              ((Γ.fuse b c).toAlgEquiv
                (GradedTensorProduct.includeLeft (Γ.D b).grading (Γ.D c).grading y)
                ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l))
            ((gbrNativeIndexEquiv K Γ a b c).symm k).2 kk
          * RelTensor.freeCollapse (GBR.mk Γ a b c u v) l kk)
    = ∑ kp, (Γ.gaugeRouteR a b c).toAlgEquiv
          (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)) k kp
        * gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) kp
  conv_rhs => rw [← Equiv.sum_comp (gbrNativeIndexEquiv K Γ a b c)
      (fun kp => (Γ.gaugeRouteR a b c).toAlgEquiv
          (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)) k kp
        * gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) kp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun kk _ => ?_
  have hentry := routeR_bslot_entry K Γ a b c y k (gbrNativeIndexEquiv K Γ a b c (l, kk))
  rw [(gbrNativeIndexEquiv K Γ a b c).symm_apply_apply] at hentry
  rw [hentry, gbrNativeColumnEquiv_apply, (gbrNativeIndexEquiv K Γ a b c).symm_apply_apply]

theorem gbrNativeColumnEquiv_smul_cEmbed_mk (z : (Γ.D c).carrier)
    (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c))) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
          • GBR.mk Γ a b c u v)
      = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
        • gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) := by
  have hemb : (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading z) • GBR.mk Γ a b c u v = z • GBR.mk Γ a b c u v :=
    GBR.cEmbed_smul K Γ a b c _ z rfl (GBR.mk Γ a b c u v)
  have hzu : z • u = (Γ.fuse b c).toAlgEquiv
      (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z) *ᵥ u := rfl
  funext k
  rw [hemb, GBR.cslot_smul_mk, hzu, gbrNativeColumnEquiv_apply]
  show RelTensor.freeCollapse
      (RelTensor.mk K (Γ.D (b + c)).carrier
        ((Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) → (Γ.D (b + c)).carrier)
        (FusionColumn (Γ.fuse a (b + c)))
        ((Γ.fuse b c).toAlgEquiv
          (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z) *ᵥ u) v)
      ((gbrNativeIndexEquiv K Γ a b c).symm k).1
      ((gbrNativeIndexEquiv K Γ a b c).symm k).2 = _
  rw [freeCollapse_mulVec_left]
  show (∑ l, (Γ.fuse b c).toAlgEquiv
        (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z)
        ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l •
      RelTensor.freeCollapse (GBR.mk Γ a b c u v) l : FusionColumn (Γ.fuse a (b + c)))
      ((gbrNativeIndexEquiv K Γ a b c).symm k).2 = _
  have hsum : (∑ l, (Γ.fuse b c).toAlgEquiv
          (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z)
          ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l •
        RelTensor.freeCollapse (GBR.mk Γ a b c u v) l : FusionColumn (Γ.fuse a (b + c)))
        ((gbrNativeIndexEquiv K Γ a b c).symm k).2
      = ∑ l, ((Γ.fuse b c).toAlgEquiv
            (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z)
            ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l •
          RelTensor.freeCollapse (GBR.mk Γ a b c u v) l)
          ((gbrNativeIndexEquiv K Γ a b c).symm k).2 :=
    Finset.sum_apply _ Finset.univ _
  rw [hsum]
  have hZ : ∀ (l : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
      (x : FusionColumn (Γ.fuse a (b + c))),
      (Γ.fuse b c).toAlgEquiv
          (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z)
          ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l • x
        = ((Γ.fuse a (b + c)).toAlgEquiv
              (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading
                ((Γ.fuse b c).toAlgEquiv
                  (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z)
                  ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l))
            : Matrix (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
                (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
                (Γ.D (a + (b + c))).carrier)
          *ᵥ x := fun _ _ => rfl
  rw [Finset.sum_congr rfl fun l _ =>
    congrFun (hZ l (RelTensor.freeCollapse (GBR.mk Γ a b c u v) l))
      ((gbrNativeIndexEquiv K Γ a b c).symm k).2]
  show (∑ l : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2,
      ∑ kk : Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2,
        (Γ.fuse a (b + c)).toAlgEquiv
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading
              ((Γ.fuse b c).toAlgEquiv
                (GradedTensorProduct.includeRight (Γ.D b).grading (Γ.D c).grading z)
                ((gbrNativeIndexEquiv K Γ a b c).symm k).1 l))
            ((gbrNativeIndexEquiv K Γ a b c).symm k).2 kk
          * RelTensor.freeCollapse (GBR.mk Γ a b c u v) l kk)
    = ∑ kp, (Γ.gaugeRouteR a b c).toAlgEquiv
          (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
            (Γ.D c).grading z) k kp
        * gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) kp
  conv_rhs => rw [← Equiv.sum_comp (gbrNativeIndexEquiv K Γ a b c)
      (fun kp => (Γ.gaugeRouteR a b c).toAlgEquiv
          (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
            (Γ.D c).grading z) k kp
        * gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) kp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun kk _ => ?_
  have hentry := routeR_cslot_entry K Γ a b c z k (gbrNativeIndexEquiv K Γ a b c (l, kk))
  rw [(gbrNativeIndexEquiv K Γ a b c).symm_apply_apply] at hentry
  rw [hentry, gbrNativeColumnEquiv_apply, (gbrNativeIndexEquiv K Γ a b c).symm_apply_apply]

/-! ### The Koszul generator family of `gbrNativeColumnEquiv` -/

theorem gaugeZZ_comm2 {kk d : ZMod 2} {x : (Γ.D a).carrier} (hx : x ∈ (Γ.D a).grading kk)
    {t : (Γ.D (b + c)).carrier} (ht : t ∈ (Γ.D (b + c)).grading d) :
    ((Γ.fuse a (b + c)).toAlgEquiv
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t)
      * (Γ.fuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
        : Matrix (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
            (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
            (Γ.D (a + (b + c))).carrier)
      = ((sgn (d * kk) : ℤˣ) : ℤ) •
          ((Γ.fuse a (b + c)).toAlgEquiv
              (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
            * (Γ.fuse a (b + c)).toAlgEquiv
                (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t)) := by
  have h1 := map_mul (Γ.fuse a (b + c)).toAlgEquiv
    (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t)
    (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
  have h2 := includeRight_mul_includeLeft_supercomm
    (Γ.D a).grading (Γ.D (b + c)).grading hx ht
  have h3 := map_mul (Γ.fuse a (b + c)).toAlgEquiv
    (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
    (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t)
  calc (Γ.fuse a (b + c)).toAlgEquiv
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t)
      * (Γ.fuse a (b + c)).toAlgEquiv
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
      = (Γ.fuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t
            * GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x) :=
        h1.symm
    _ = (Γ.fuse a (b + c)).toAlgEquiv
          (((sgn (d * kk) : ℤˣ) : ℤ) •
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x
              * GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t)) := by
        rw [h2]
    _ = ((sgn (d * kk) : ℤˣ) : ℤ) •
          (Γ.fuse a (b + c)).toAlgEquiv
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x
              * GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t) :=
        map_zsmul (Γ.fuse a (b + c)).toAlgEquiv _ _
    _ = ((sgn (d * kk) : ℤˣ) : ℤ) •
          ((Γ.fuse a (b + c)).toAlgEquiv
              (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
            * (Γ.fuse a (b + c)).toAlgEquiv
                (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading t)) :=
        congrArg (fun w => ((sgn (d * kk) : ℤˣ) : ℤ) • w) h3

theorem gbrNativeColumnEquiv_smul_aEmbed_mk {j k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
          • GBR.mk Γ a b c u v)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
        • gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) := by
  have hemb : (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x))
        • GBR.mk Γ a b c u v = x • GBR.mk Γ a b c u v :=
    GBR.aEmbed_smul K Γ a b c _ x rfl _ rfl (GBR.mk Γ a b c u v)
  have haslot := GBR.aslot_smul_mk_of_mem Γ a b c hx hu v
  funext idx
  set p1 := ((gbrNativeIndexEquiv K Γ a b c).symm idx).1 with hp1
  set p2 := ((gbrNativeIndexEquiv K Γ a b c).symm idx).2 with hp2
  have step : gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
          • GBR.mk Γ a b c u v) idx
      = ((sgn (k * j) : ℤˣ) : ℤ) • RelTensor.freeCollapse (GBR.mk Γ a b c u (x • v)) p1 p2 := by
    rw [hemb, haslot, map_zsmul]
    show (((sgn (k * j) : ℤˣ) : ℤ) •
        gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u (x • v))) idx = _
    rw [show (((sgn (k * j) : ℤˣ) : ℤ) •
          gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u (x • v))) idx
        = ((sgn (k * j) : ℤˣ) : ℤ) •
            (gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u (x • v)) idx) from rfl,
      gbrNativeColumnEquiv_apply]
  rw [step]
  have hfc : RelTensor.freeCollapse (GBR.mk Γ a b c u (x • v)) p1 = u p1 • (x • v) :=
    congrFun (RelTensor.freeCollapse_mk u (x • v)) p1
  rw [hfc]
  set Xx : Matrix (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
      (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2) (Γ.D (a + (b + c))).carrier :=
    (Γ.fuse a (b + c)).toAlgEquiv
      (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D (b + c)).grading x)
    with hXxdef
  set Yu : Matrix (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
      (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2) (Γ.D (a + (b + c))).carrier :=
    (Γ.fuse a (b + c)).toAlgEquiv
      (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D (b + c)).grading (u p1))
    with hYudef
  have hxv : x • v = Xx *ᵥ v := rfl
  have hup1x : ∀ w : FusionColumn (Γ.fuse a (b + c)), u p1 • w = Yu *ᵥ w := fun _ => rfl
  rw [hxv, hup1x]
  have hup1 : u p1 ∈ (Γ.D (b + c)).grading
      (j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) := hu p1
  have hcomm : Yu * Xx
      = ((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ) • (Xx * Yu) :=
    gaugeZZ_comm2 K Γ a b c hx hup1
  have huv : Yu *ᵥ v = u p1 • v := (hup1x v).symm
  have e1 : Yu *ᵥ Xx *ᵥ v = (Yu * Xx) *ᵥ v := Matrix.mulVec_mulVec v Yu Xx
  have e2 : (Yu * Xx) *ᵥ v
      = (((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
        • (Xx * Yu)) *ᵥ v := congrArg (· *ᵥ v) hcomm
  have e3 : (((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
        • (Xx * Yu)) *ᵥ v
      = ((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
        • ((Xx * Yu) *ᵥ v) := Matrix.smul_mulVec _ _ _
  have e4 : (Xx * Yu) *ᵥ v = Xx *ᵥ (Yu *ᵥ v) := (Matrix.mulVec_mulVec v Xx Yu).symm
  have echain : (Yu *ᵥ Xx *ᵥ v) p2
      = ((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
        • (Xx *ᵥ (u p1 • v)) p2 :=
    calc (Yu *ᵥ Xx *ᵥ v) p2 = ((Yu * Xx) *ᵥ v) p2 := congrFun e1 p2
      _ = ((((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
            • (Xx * Yu)) *ᵥ v) p2 := congrFun e2 p2
      _ = (((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
            • ((Xx * Yu) *ᵥ v)) p2 := congrFun e3 p2
      _ = ((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
            • (((Xx * Yu) *ᵥ v) p2) := rfl
      _ = ((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
            • ((Xx *ᵥ (Yu *ᵥ v)) p2) := congrArg _ (congrFun e4 p2)
      _ = ((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
            • ((Xx *ᵥ (u p1 • v)) p2) := by rw [huv]
  rw [show ((sgn (k * j) : ℤˣ) : ℤ) • (Yu *ᵥ Xx *ᵥ v) p2
        = ((sgn (k * j) : ℤˣ) : ℤ) •
            (((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ)
              • (Xx *ᵥ (u p1 • v)) p2) from congrArg _ echain,
    smul_smul]
  rw [show (((sgn (k * j) : ℤˣ) : ℤ)
      * ((sgn ((j + sumParity (Γ.size b c).1 (Γ.size b c).2 p1) * k) : ℤˣ) : ℤ))
      = ((sgn (sumParity (Γ.size b c).1 (Γ.size b c).2 p1 * k) : ℤˣ) : ℤ) from by
    rw [← Units.val_mul, ← sgn_add, zmod2_c_sign]]
  set ww : FusionColumn (Γ.fuse a (b + c)) :=
    RelTensor.freeCollapse (GBR.mk Γ a b c u v) p1 with hwdef
  have hfc2 : u p1 • v = ww := (congrFun (RelTensor.freeCollapse_mk u v) p1).symm
  rw [hfc2]
  show ((sgn (sumParity (Γ.size b c).1 (Γ.size b c).2 p1 * k) : ℤˣ) : ℤ) •
      (∑ s' : Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2, Xx p2 s' * ww s')
    = ∑ idx' : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2,
        (Γ.gaugeRouteR a b c).toAlgEquiv
            (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
              (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)) idx idx'
          * gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) idx'
  rw [← Equiv.sum_comp (gbrNativeIndexEquiv K Γ a b c)
    (fun idx' => (Γ.gaugeRouteR a b c).toAlgEquiv
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)) idx idx'
      * gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) idx'),
    Fintype.sum_prod_type]
  rw [Finset.smul_sum]
  symm
  rw [Finset.sum_eq_single p1
    (fun s _ hsne => Finset.sum_eq_zero fun s' _ => by
      have hentry := routeR_aslot_entry K Γ a b c hx idx (gbrNativeIndexEquiv K Γ a b c (s, s'))
      rw [(gbrNativeIndexEquiv K Γ a b c).symm_apply_apply] at hentry
      rw [hentry, if_neg (fun heq => hsne (hp1 ▸ heq.symm)), zero_mul])
    (fun hp1nu => absurd (Finset.mem_univ p1) hp1nu)]
  refine Finset.sum_congr rfl fun s' _ => ?_
  have hentry := routeR_aslot_entry K Γ a b c hx idx (gbrNativeIndexEquiv K Γ a b c (p1, s'))
  rw [(gbrNativeIndexEquiv K Γ a b c).symm_apply_apply] at hentry
  rw [hentry, if_pos rfl, gbrNativeColumnEquiv_apply,
    (gbrNativeIndexEquiv K Γ a b c).symm_apply_apply, smul_mul_assoc]

/-! ### `gbrNativeColumnEquiv` is a module map (all of `GBR`, all of the triple tensor) -/

theorem gbrNativeColumnEquiv_smul_aEmbed_of_mem {k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k) (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) • m)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
        • gbrNativeColumnEquiv K Γ a b c m := by
  refine relTensor_induction_on_left_homog (FusionColumn.grading (Γ.fuse b c))
    (A := (Γ.D (b + c)).carrier) (N := FusionColumn (Γ.fuse a (b + c)))
    (motive := fun t => gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
          • gbrOfRaw K Γ a b c t)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
        • gbrNativeColumnEquiv K Γ a b c (gbrOfRaw K Γ a b c t)) m ?_ ?_ ?_
  · rw [map_zero, smul_zero, map_zero, smul_zero]
  · intro j u v hu
    rw [gbrOfRaw_apply]
    exact gbrNativeColumnEquiv_smul_aEmbed_mk K Γ a b c hx hu v
  · intro t₁ t₂ h₁ h₂
    rw [map_add, smul_add, map_add, map_add, smul_add, h₁, h₂]

theorem gbrNativeColumnEquiv_smul_aEmbed (x : (Γ.D a).carrier) (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) • m)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
        • gbrNativeColumnEquiv K Γ a b c m := by
  obtain ⟨xe, hxe, xo, hxo, rfl⟩ :
      ∃ xe, xe ∈ (Γ.D a).grading 0 ∧ ∃ xo, xo ∈ (Γ.D a).grading 1 ∧ x = xe + xo :=
    ⟨_, evenPart_mem (Γ.D a).grading x, _, oddPart_mem (Γ.D a).grading x,
      (evenPart_add_oddPart (Γ.D a).grading x).symm⟩
  have hsplit :
      GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading (xe + xo))
        = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading xe)
          + GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading xo) :=
    (congrArg (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading)
        (map_add (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading) xe xo)).trans
      (map_add _ _ _)
  rw [hsplit, add_smul, add_smul, map_add,
    gbrNativeColumnEquiv_smul_aEmbed_of_mem K Γ a b c hxe,
    gbrNativeColumnEquiv_smul_aEmbed_of_mem K Γ a b c hxo]

theorem gbrNativeColumnEquiv_smul_bEmbed (y : (Γ.D b).carrier) (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) • m)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
        • gbrNativeColumnEquiv K Γ a b c m := by
  refine RelTensor.induction_on (K := K) (A := (Γ.D (b + c)).carrier)
    (M := FusionColumn (Γ.fuse b c)) (N := FusionColumn (Γ.fuse a (b + c)))
    (motive := fun t => gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
          • gbrOfRaw K Γ a b c t)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
          (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
        • gbrNativeColumnEquiv K Γ a b c (gbrOfRaw K Γ a b c t)) m ?_ ?_ ?_
  · rw [map_zero, smul_zero, map_zero, smul_zero]
  · intro u v
    rw [gbrOfRaw_apply]
    exact gbrNativeColumnEquiv_smul_bEmbed_mk K Γ a b c y u v
  · intro t₁ t₂ h₁ h₂
    rw [map_add, smul_add, map_add, map_add, smul_add, h₁, h₂]

theorem gbrNativeColumnEquiv_smul_cEmbed (z : (Γ.D c).carrier) (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z • m)
      = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
        • gbrNativeColumnEquiv K Γ a b c m := by
  refine RelTensor.induction_on (K := K) (A := (Γ.D (b + c)).carrier)
    (M := FusionColumn (Γ.fuse b c)) (N := FusionColumn (Γ.fuse a (b + c)))
    (motive := fun t => gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
          • gbrOfRaw K Γ a b c t)
      = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
        • gbrNativeColumnEquiv K Γ a b c (gbrOfRaw K Γ a b c t)) m ?_ ?_ ?_
  · rw [map_zero, smul_zero, map_zero, smul_zero]
  · intro u v
    rw [gbrOfRaw_apply]
    exact gbrNativeColumnEquiv_smul_cEmbed_mk K Γ a b c z u v
  · intro t₁ t₂ h₁ h₂
    rw [map_add, smul_add, map_add, map_add, smul_add, h₁, h₂]

theorem gbrNativeColumnEquiv_smul_includeLeft (w : ((Γ.D a).gtensor (Γ.D b)).carrier)
    (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w • m)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w
        • gbrNativeColumnEquiv K Γ a b c m := by
  refine gtensor_induction_on (Γ.D a).grading (Γ.D b).grading
    (p := fun t => gbrNativeColumnEquiv K Γ a b c
        (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading t • m)
      = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading t
        • gbrNativeColumnEquiv K Γ a b c m) w ?_ ?_ ?_
  · intro x y
    have hmul :
        GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x
              * GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
          = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
              (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
            * GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
              (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) :=
      map_mul _ _ _
    rw [show (x ᵍ⊗ₜ[K] y : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading)
        = GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x
          * GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y
      from (includeLeft_mul_includeRight _ _ x y).symm,
      hmul, mul_smul, gbrNativeColumnEquiv_smul_aEmbed, gbrNativeColumnEquiv_smul_bEmbed,
      mul_smul]
  · have hzero : GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading (0 : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) = 0 := map_zero _
    rw [hzero, zero_smul, map_zero, zero_smul]
  · intro t₁ t₂ h₁ h₂
    have hadd : GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
          (Γ.D c).grading ((t₁ + t₂ : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading))
        = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading t₁
          + GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading t₂ :=
      map_add _ _ _
    rw [hadd, add_smul, map_add, h₁, h₂, add_smul]

theorem gbrNativeColumnEquiv_smul
    (y : ((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c (y • m) = y • gbrNativeColumnEquiv K Γ a b c m := by
  refine gtensor_induction_on ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
    (p := fun t => gbrNativeColumnEquiv K Γ a b c (t • m)
      = t • gbrNativeColumnEquiv K Γ a b c m) y ?_ ?_ ?_
  · intro w z
    rw [show (w ᵍ⊗ₜ[K] z : ((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading)
        = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w
          * GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z
      from (includeLeft_mul_includeRight _ _ w z).symm,
      mul_smul, gbrNativeColumnEquiv_smul_includeLeft, gbrNativeColumnEquiv_smul_cEmbed,
      mul_smul]
  · rw [zero_smul, map_zero, zero_smul]
  · intro t₁ t₂ h₁ h₂
    rw [add_smul, map_add, h₁, h₂, add_smul]

/-- **Item 4, right vertex (native frame)**: the native column dictionary
`gbrNativeColumnEquiv` is an isomorphism of `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-modules. -/
theorem gbrNativeColumnEquiv_gtensor_smul
    (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c (y • m)
      = (Γ.gaugeRouteR a b c).toAlgEquiv y *ᵥ gbrNativeColumnEquiv K Γ a b c m :=
  gbrNativeColumnEquiv_smul K Γ a b c y m

/-! ### The aligned right dictionary: frame-cast entries -/

/-- Cast of a flat `p|q`-index along an equality of size pairs. -/
private def sumFinCast {s t : ℕ × ℕ} (h : s = t) :
    Fin s.1 ⊕ Fin s.2 → Fin t.1 ⊕ Fin t.2 :=
  Sum.map (Fin.cast (congrArg Prod.fst h)) (Fin.cast (congrArg Prod.snd h))

private theorem gaugeMatrixCast_entry {x y : G} (h : x = y) {s t : ℕ × ℕ} (hs : s = t)
    (M : ((Γ.D x).matrixSuper s.1 s.2).carrier) (i j : Fin t.1 ⊕ Fin t.2) :
    (Γ.gaugeMatrixCast h hs).toAlgEquiv M i j
      = (Γ.gaugeCast h).toAlgEquiv
          (M (sumFinCast hs.symm i) (sumFinCast hs.symm j)) := by
  subst h
  subst hs
  show M i j = (Γ.gaugeCast (rfl : x = x)).toAlgEquiv
    (M (sumFinCast (rfl : s = s) i) (sumFinCast (rfl : s = s) j))
  have hi : sumFinCast (rfl : s = s) i = i := by rcases i with i | i <;> rfl
  have hj : sumFinCast (rfl : s = s) j = j := by rcases j with j | j <;> rfl
  rw [hi, hj]
  rfl

private theorem gaugeSizeCastEquiv_symm_apply
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (y : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    (gaugeSizeCastEquiv K Γ a b c hsz).symm y = sumFinCast hsz.symm y := by
  rcases y with y | y <;> rfl

/-- **The entry formula of the aligned right route** under the sizes-equal
hypothesis: `gaugeRouteR'` is `gaugeRouteR` read through the value cast
`Γ.gaugeCast (add_assoc a b c).symm` and the index cast
`gaugeSizeCastEquiv hsz` (`frameAlign` collapsing to the pure frame cast by
`frameAlign_of_sizes_eq`). -/
theorem routeR'_entry (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (i j : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    (Γ.gaugeRouteR' a b c).toAlgEquiv y i j
      = (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
          ((Γ.gaugeRouteR a b c).toAlgEquiv y
            ((gaugeSizeCastEquiv K Γ a b c hsz).symm i)
            ((gaugeSizeCastEquiv K Γ a b c hsz).symm j)) := by
  show ((Γ.frameAlign a b c).toAlgEquiv
      ((Γ.gaugeMatrixCast (add_assoc a b c).symm rfl).toAlgEquiv
        ((Γ.gaugeRouteR a b c).toAlgEquiv y))) i j = _
  rw [frameAlign_of_sizes_eq K Γ a b c hsz, gaugeMatrixCast_entry, gaugeMatrixCast_entry,
    gaugeSizeCastEquiv_symm_apply, gaugeSizeCastEquiv_symm_apply]
  show (Γ.gaugeCast (rfl : a + b + c = a + b + c)).toAlgEquiv
      ((Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
        ((Γ.gaugeRouteR a b c).toAlgEquiv y
          (sumFinCast (rfl : Γ.gaugeSizeR a b c = Γ.gaugeSizeR a b c)
            (sumFinCast hsz.symm i))
          (sumFinCast (rfl : Γ.gaugeSizeR a b c = Γ.gaugeSizeR a b c)
            (sumFinCast hsz.symm j)))) = _
  have hi : ∀ t : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2,
      sumFinCast (rfl : Γ.gaugeSizeR a b c = Γ.gaugeSizeR a b c) t = t := by
    intro t; rcases t with t | t <;> rfl
  rw [hi, hi]
  rfl

/-- **Item 4, right vertex (aligned frame)**: under the sizes-equal
hypothesis `hsz` the aligned column dictionary `gbrColumnEquiv hsz` is an
isomorphism of `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-modules, against `gaugeRouteR'`. -/
theorem gbrColumnEquiv_gtensor_smul (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) (m : GBR Γ a b c) :
    gbrColumnEquiv K Γ a b c hsz (y • m)
      = (Γ.gaugeRouteR' a b c).toAlgEquiv y *ᵥ gbrColumnEquiv K Γ a b c hsz m := by
  funext x
  have hval : ∀ (n : GBR Γ a b c)
      (t : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2),
      gbrColumnEquiv K Γ a b c hsz n t
        = (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
            (gbrNativeColumnEquiv K Γ a b c n
              ((gaugeSizeCastEquiv K Γ a b c hsz).symm t)) := fun _ _ => rfl
  rw [hval, gbrNativeColumnEquiv_gtensor_smul]
  show (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
      (∑ x' : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2,
        (Γ.gaugeRouteR a b c).toAlgEquiv y ((gaugeSizeCastEquiv K Γ a b c hsz).symm x) x'
          * gbrNativeColumnEquiv K Γ a b c m x')
    = ∑ x'' : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2,
        (Γ.gaugeRouteR' a b c).toAlgEquiv y x x'' * gbrColumnEquiv K Γ a b c hsz m x''
  rw [map_sum, ← Equiv.sum_comp (gaugeSizeCastEquiv K Γ a b c hsz).symm
      (fun x' => (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
        ((Γ.gaugeRouteR a b c).toAlgEquiv y ((gaugeSizeCastEquiv K Γ a b c hsz).symm x) x'
          * gbrNativeColumnEquiv K Γ a b c m x'))]
  refine Finset.sum_congr rfl fun x'' _ => ?_
  rw [map_mul, routeR'_entry K Γ a b c hsz, hval]

/-! ### Item 5: `gtOfT`, the transport of a matrix element into an intertwiner -/

/-- **Right-semilinearity is plain equivariance for `GBR`'s recast right
action** (the Γ-port of `Bimod.rightSemilinear_iff_recast_equivariant`,
`Bimod/RouteRecast.lean`): `GaugeChi/RouteBimod.lean` registers `GBR`'s
right `D_{(a+b)+c}`-action as exactly `Module.compHom` along
`Γ.gaugeCast (add_assoc a b c)`, which is the ring map `gInterSpace`'s
`rightSemilinear` condition is stated against — so the two sides are
literally the same proposition. -/
theorem grightSemilinear_iff_recast_equivariant {f : GBL Γ a b c →ₗ[K] GBR Γ a b c} :
    f ∈ rightSemilinear ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom)
      ↔ ∀ (t : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
          f (MulOpposite.op t • m) = MulOpposite.op t • f m :=
  Iff.rfl

/-- **`gtOfT T`** (§10 roadmap item 5, the Γ-port of `Bimod.PentagonB.tOfT`):
`gbrColumnEquiv.symm ∘ₗ gmulVecMap T ∘ₗ gblColumnEquiv`, transporting a matrix
element `T : M_σ(D_{(a+b)+c})` into a `K`-linear map `GBL → GBR` through the
gauge column dictionary.  Takes `ColumnDictGauge`'s standing hypothesis
`hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c` (the frame-alignment
hypothesis of `gbrColumnEquiv`; see that file's header for why a shift-`0`
aligned dictionary cannot exist without it). -/
noncomputable def gtOfT (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) :
    GBL Γ a b c →ₗ[K] GBR Γ a b c :=
  (gbrColumnEquiv K Γ a b c hsz).symm.toLinearMap ∘ₗ
    gmulVecMap K Γ a b c T ∘ₗ (gblColumnEquiv K Γ a b c).toLinearMap

theorem gtOfT_apply (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) (m : GBL Γ a b c) :
    gtOfT K Γ a b c hsz T m
      = (gbrColumnEquiv K Γ a b c hsz).symm
          (gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m)) := rfl

/-- **Condition 1 of 5**: `gtOfT T` is homogeneous of `T`'s degree. -/
theorem gtOfT_mem_homGrading (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier} {e : ZMod 2}
    (hT : T ∈ ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).grading e) :
    gtOfT K Γ a b c hsz T ∈ homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c) e := by
  refine (mem_homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c)).mpr ?_
  intro i m hm
  rw [gtOfT_apply]
  exact gbrColumnEquiv_symm_mem_grading K Γ a b c hsz
    (gmulVecMap_mem_grading K Γ a b c hT (gblColumnEquiv_mem_grading K Γ a b c hm))

/-- **Condition 2 of 5**: `gtOfT T` is `D_a`-slot super-equivariant of
`T`'s degree.  Both vertices are handled by the ONE module-correspondence
lemma of item 4, specialized at the `a`-slot generator through
`GaugeParity`'s embedding bridges `GBL.aEmbed`/`GBR.aEmbed_smul` (which
already discharge `GBR`'s Koszul sign, for every element of the vertex). -/
theorem gtOfT_mem_superEquivariant_a (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * (Γ.gaugeRouteL a b c).toAlgEquiv y)) :
    gtOfT K Γ a b c hsz T ∈ superEquivariant (Γ.D a).grading e := by
  refine (mem_superEquivariant (Γ.D a).grading).mpr ?_
  intro i x hx m
  obtain ⟨Y, hY⟩ : ∃ Y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier,
      Y = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) := ⟨_, rfl⟩
  have hembL : Y • m = x • m := GBL.aEmbed K Γ a b c _ x rfl Y hY m
  have hembR : ∀ n : GBR Γ a b c, Y • n = x • n := fun n => GBR.aEmbed_smul K Γ a b c _ x rfl Y hY n
  have hmem : Y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading i := by
    rw [hY]
    exact includeLeft_mem_tensorGrading _ _ (includeLeft_mem_tensorGrading _ _ hx)
  calc gtOfT K Γ a b c hsz T (x • m)
      = (gbrColumnEquiv K Γ a b c hsz).symm
          (gmulVecMap K Γ a b c T
            ((Γ.gaugeRouteL a b c).toAlgEquiv Y *ᵥ gblColumnEquiv K Γ a b c m)) := by
        rw [gtOfT_apply, ← hembL, gblColumnEquiv_gtensor_smul]
    _ = (gbrColumnEquiv K Γ a b c hsz).symm
          (((sgn (i * e) : ℤˣ) : ℤ) •
            ((Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ
              gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m))) := by
        rw [gmulVecMap_slot_equivariant K Γ a b c T hT_int hmem]
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (gbrColumnEquiv K Γ a b c hsz).symm
          ((Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ
            gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m)) :=
        map_zsmul (gbrColumnEquiv K Γ a b c hsz).symm _ _
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (Y • (gbrColumnEquiv K Γ a b c hsz).symm
          (gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m))) :=
        congrArg (fun v => ((sgn (i * e) : ℤˣ) : ℤ) • v)
          (conjSymm (gbrColumnEquiv K Γ a b c hsz) (fun n => Y • n)
            (fun v => (Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ v)
            (gbrColumnEquiv_gtensor_smul K Γ a b c hsz Y) _)
    _ = ((sgn (e * i) : ℤˣ) : ℤ) • (x • gtOfT K Γ a b c hsz T m) := by
        rw [hembR, mul_comm i e]
        rfl

/-- **Condition 3 of 5**: `gtOfT T` is `D_b`-slot super-equivariant. -/
theorem gtOfT_mem_superEquivariant_b (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * (Γ.gaugeRouteL a b c).toAlgEquiv y)) :
    gtOfT K Γ a b c hsz T ∈ superEquivariant (Γ.D b).grading e := by
  refine (mem_superEquivariant (Γ.D b).grading).mpr ?_
  intro i y hy m
  obtain ⟨Y, hY⟩ : ∃ Y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier,
      Y = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) := ⟨_, rfl⟩
  have hembL : Y • m = y • m := GBL.bEmbed K Γ a b c _ y rfl Y hY m
  have hembR : ∀ n : GBR Γ a b c, Y • n = y • n := fun n => GBR.bEmbed_smul K Γ a b c _ y rfl Y hY n
  have hmem : Y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading i := by
    rw [hY]
    exact includeLeft_mem_tensorGrading _ _ (includeRight_mem_tensorGrading _ _ hy)
  calc gtOfT K Γ a b c hsz T (y • m)
      = (gbrColumnEquiv K Γ a b c hsz).symm
          (gmulVecMap K Γ a b c T
            ((Γ.gaugeRouteL a b c).toAlgEquiv Y *ᵥ gblColumnEquiv K Γ a b c m)) := by
        rw [gtOfT_apply, ← hembL, gblColumnEquiv_gtensor_smul]
    _ = (gbrColumnEquiv K Γ a b c hsz).symm
          (((sgn (i * e) : ℤˣ) : ℤ) •
            ((Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ
              gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m))) := by
        rw [gmulVecMap_slot_equivariant K Γ a b c T hT_int hmem]
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (gbrColumnEquiv K Γ a b c hsz).symm
          ((Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ
            gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m)) :=
        map_zsmul (gbrColumnEquiv K Γ a b c hsz).symm _ _
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (Y • (gbrColumnEquiv K Γ a b c hsz).symm
          (gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m))) :=
        congrArg (fun v => ((sgn (i * e) : ℤˣ) : ℤ) • v)
          (conjSymm (gbrColumnEquiv K Γ a b c hsz) (fun n => Y • n)
            (fun v => (Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ v)
            (gbrColumnEquiv_gtensor_smul K Γ a b c hsz Y) _)
    _ = ((sgn (e * i) : ℤˣ) : ℤ) • (y • gtOfT K Γ a b c hsz T m) := by
        rw [hembR, mul_comm i e]
        rfl

/-- **Condition 4 of 5**: `gtOfT T` is `D_c`-slot super-equivariant (the
`GBL` side is the Koszul slot, already discharged universally by
`GBL.cEmbed`). -/
theorem gtOfT_mem_superEquivariant_c (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * (Γ.gaugeRouteL a b c).toAlgEquiv y)) :
    gtOfT K Γ a b c hsz T ∈ superEquivariant (Γ.D c).grading e := by
  refine (mem_superEquivariant (Γ.D c).grading).mpr ?_
  intro i z hz m
  obtain ⟨Y, hY⟩ : ∃ Y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier,
      Y = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading z := ⟨_, rfl⟩
  have hembL : Y • m = z • m := GBL.cEmbed K Γ a b c Y z hY m
  have hembR : ∀ n : GBR Γ a b c, Y • n = z • n := fun n => GBR.cEmbed_smul K Γ a b c Y z hY n
  have hmem : Y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading i := by
    rw [hY]
    exact includeRight_mem_tensorGrading _ _ hz
  calc gtOfT K Γ a b c hsz T (z • m)
      = (gbrColumnEquiv K Γ a b c hsz).symm
          (gmulVecMap K Γ a b c T
            ((Γ.gaugeRouteL a b c).toAlgEquiv Y *ᵥ gblColumnEquiv K Γ a b c m)) := by
        rw [gtOfT_apply, ← hembL, gblColumnEquiv_gtensor_smul]
    _ = (gbrColumnEquiv K Γ a b c hsz).symm
          (((sgn (i * e) : ℤˣ) : ℤ) •
            ((Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ
              gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m))) := by
        rw [gmulVecMap_slot_equivariant K Γ a b c T hT_int hmem]
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (gbrColumnEquiv K Γ a b c hsz).symm
          ((Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ
            gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m)) :=
        map_zsmul (gbrColumnEquiv K Γ a b c hsz).symm _ _
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (Y • (gbrColumnEquiv K Γ a b c hsz).symm
          (gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m))) :=
        congrArg (fun v => ((sgn (i * e) : ℤˣ) : ℤ) • v)
          (conjSymm (gbrColumnEquiv K Γ a b c hsz) (fun n => Y • n)
            (fun v => (Γ.gaugeRouteR' a b c).toAlgEquiv Y *ᵥ v)
            (gbrColumnEquiv_gtensor_smul K Γ a b c hsz Y) _)
    _ = ((sgn (e * i) : ℤˣ) : ℤ) • (z • gtOfT K Γ a b c hsz T m) := by
        rw [hembR, mul_comm i e]
        rfl

/-- **Condition 5 of 5**: `gtOfT T` is right-semilinear along
`Γ.gaugeCast (add_assoc a b c)`. -/
theorem gtOfT_mem_rightSemilinear (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) :
    gtOfT K Γ a b c hsz T
      ∈ rightSemilinear ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom) := by
  rw [grightSemilinear_iff_recast_equivariant]
  intro t m
  rw [gtOfT_apply, gtOfT_apply, gblColumnEquiv_rightEquiv, gmulVecMap_rightEquiv,
    conjSymm (gbrColumnEquiv K Γ a b c hsz) (fun n => MulOpposite.op t • n)
      (fun w => MulOpposite.op t • w) (gbrColumnEquiv_rightEquiv K Γ a b c hsz t)]

/-- **`gtOfT T` lies in `gInterSpace K Γ a b c e`** (§10 roadmap item 5, FULL
membership: all five conditions of `mem_gInterSpace_iff`), given

* `hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c` — the standing frame
  hypothesis of the aligned column dictionary `gbrColumnEquiv`;
* `hT` : `T` is homogeneous of degree `e` in the matrix superalgebra;
* `hT_int` : the finite matrix intertwining identity in the gauge shape,
  `routeR'(y) * T = sgn(|y|·e) • (T * routeL(y))` on homogeneous `y`. -/
theorem gtOfT_mem_interSpace (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier} {e : ZMod 2}
    (hT : T ∈ ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).grading e)
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * (Γ.gaugeRouteL a b c).toAlgEquiv y)) :
    gtOfT K Γ a b c hsz T ∈ gInterSpace K Γ a b c e := by
  rw [mem_gInterSpace_iff]
  exact ⟨gtOfT_mem_homGrading K Γ a b c hsz hT,
    gtOfT_mem_superEquivariant_a K Γ a b c hsz T hT_int,
    gtOfT_mem_superEquivariant_b K Γ a b c hsz T hT_int,
    gtOfT_mem_superEquivariant_c K Γ a b c hsz T hT_int,
    gtOfT_mem_rightSemilinear K Γ a b c hsz T⟩

/-- **`gtOfT` is injective on matrix elements**: a nonzero `T` gives a
nonzero intertwiner (the two column dictionaries are equivalences and
`mulVec` by `T` recovers `T`'s columns at the standard basis vectors). -/
theorem gtOfT_ne_zero (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier} (hT : T ≠ 0) :
    gtOfT K Γ a b c hsz T ≠ 0 := by
  intro h0
  refine hT ?_
  have hmv : ∀ v : FusionColumn (Γ.gaugeRouteL a b c), T *ᵥ v = 0 := by
    intro v
    have h1 : gtOfT K Γ a b c hsz T ((gblColumnEquiv K Γ a b c).symm v) = 0 := by
      rw [h0]; rfl
    rw [gtOfT_apply, LinearEquiv.apply_symm_apply] at h1
    have h2 := congrArg (gbrColumnEquiv K Γ a b c hsz) h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact h2
  refine Matrix.ext_of_mulVec_single ?_
  intro j
  exact (hmv (Pi.single j 1)).trans (Matrix.zero_mulVec _).symm

/-- **`gtOfT T` is bijective when `T` is invertible**: the composite of the
three bijections `gblColumnEquiv`, `gmulVecMap T`, `gbrColumnEquiv.symm`. -/
theorem gtOfT_bijective (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) (hT : IsUnit T) :
    Function.Bijective (gtOfT K Γ a b c hsz T) := by
  have hcomp : (gtOfT K Γ a b c hsz T : GBL Γ a b c → GBR Γ a b c)
      = (gbrColumnEquiv K Γ a b c hsz).symm ∘ (gmulVecMap K Γ a b c T)
        ∘ (gblColumnEquiv K Γ a b c) := rfl
  rw [hcomp]
  exact (gbrColumnEquiv K Γ a b c hsz).symm.bijective.comp
    ((gmulVecMap_bijective K Γ a b c T hT).comp (gblColumnEquiv K Γ a b c).bijective)


end GaugeChi

end Superfusion

/-
Superfusion / GaugeChi / QuintRecog

Milestone M13-4a of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase): **the recognition-statement DESIGN for the `PAB` face**
(`docs/m13-design.md`'s ledger) and its landing for the three tractable
`PAB` edges `E4M`, `E13M`, `E12M`.

## The design task: two candidate forms, and the choice

`PAB`'s target identity is `E12M∘E11M∘E4M = χ(a+b,c,d,e) • (E14M∘E13M)`
as maps `V1 → V9` (`docs/m13-design.md`). Structurally each `K₅` edge in
this face is a WHISKERED copy of a four-letter pentagon-edge map at the
SHIFTED quadruple `(a+b,c,d,e)` (`ChiCanon.lean`'s `gChiCanon_spec`
instantiated there), with the column `F_{a,b}` riding as an outer factor
— e.g. `V1 = ((F_{a,b}⊗F_{a+b,c})⊗F_{a+b+c,d})⊗F_{a+b+c+d,e}` reassociates
(two `RelTensor.assoc` steps around `gq1Assoc`) to `F_{a,b} ⊗
GQ1(a+b,c,d,e)`, and `E4M` (built, per `QuintEdges.lean`, via `GE4` at the
ORIGINAL quadruple `(a,b,c,d)`) becomes, after this reassociation, exactly
the `F_{a,b}`-signed-whisker of `GE1` at the SHIFTED quadruple.

Two candidate statement shapes were weighed (as directed):

**(A) CONJUGATION FORM.** Build, once, vertex identification equivalences
`ωv : V_v ≃ₗ[K] (F_{a,b}-whisker of the four-letter vertex at
(a+b,c,d,e))` for `v ∈ {1,3,6,8,9}` (`RelTensor.assoc`/`gq1Assoc`
composites), and state each recognition as `ω_target ∘ E_kM =
signedWhisker(GE_j at (a+b,c,d,e)) ∘ ω_source`. This is mathematically
the cleaner statement (it is literally what the ledger's shifted-pentagon
picture says), but EXPERIMENTALLY (worked by hand on `E4M`, see the
computation below) it needs a genuinely NEW toolkit fact beyond anything
currently public to this file: the naturality of `smap` against
`RelTensor.assoc` (`smap ∘ assoc = assoc ∘ (map (smap …) id)`-shaped, to
transport the whiskered-`GE4`/`gq1Assoc` composite already built into
`E4M`'s OWN definition past the `ωv` conjugation into "whiskered `GE1` at
the shifted quadruple" form). This EXACT fact is being built concurrently,
UNDER A DIFFERENT NAME, in `QuintSquares.lean` (`assoc_comp_mapFirstOuter`,
"the naturality of `RelTensor.assoc` against an OUTER first-slot
`RelTensor.map`") by another session working the square faces — this file
must not import or depend on that file (active concurrent edits, per the
round's instructions), and duplicating the fact here under a different
name would be wasteful and risks divergence once the two branches merge.

**(B) GENERATOR-FORMULA FORM.** Leaf lemmas `EkM_leaf`: `EkM` applied to a
FULLY-DECOMPOSED homogeneous generator of its domain vertex equals a
Koszul sign times a "reinsertion" of the four-letter edge's own canonical
map applied to the appropriately-nested inner generator — linear in the
un-decomposed part. EXPERIMENTALLY (worked by hand and then in Lean,
below) this is close to FREE for all three edges landed here: each leaf
lemma is a two-to-four-line `rw`/`show` chase through generator formulas
that are ALREADY PUBLIC (`E4M_mk` + `GE4_mk_of_mem`; `RelTensor.assoc_mk`
+ `smap_mk_of_mem`; `E12MInnerEquiv_toLinearMap` + `RelTensor.map_mk` +
`smap_mk_of_mem`) — NO new toolkit content, and no dependency on the
concurrently-developed `assoc`-vs-`smap` naturality fact.

**CHOSEN: form (B).** The generator-formula form is landed for all three
edges this round with zero new toolkit lemmas. Face assembly (round 4d)
will proceed as: decompose a generic `V1` generator via nested
`RelTensor.induction_on`/`DirectSum.Decomposition.inductionOn` into the
homogeneous flat form `u,v,w,x` (`u : F_{a,b}` homogeneous, `v,w,x`
arbitrary) that BOTH `E4M_leaf` and `E13M_leaf` are stated against
(confirmed compatible below — this is the key consistency check the
design task asked for), extend `E11M_leaf`/`E12M_leaf`/`E14M_leaf` in the
same style in rounds 4b/4c, chain the leaves along each route, and match
the resulting signs/reinserted elements against `gChiCanon_spec K Γ
(a+b) c d e`'s own pointwise instantiation (`LinearMap.congr_fun`
+ `congrArg (mk · n)`, exactly `face_P6`/`face_P1`'s own closing move,
`QuintFaces.lean`) — "one nested-induction span argument per face
chaining the leaves + `gChiCanon_spec` pointwise", per the round's
prescription for 4b–4d.

## The hand computation validating the choice (on `E4M`)

Write a generic `V1`-generator as `u ⊗ v ⊗ w ⊗ x` (`u : F_{a,b}` degree
`j`, `v : F_{a+b,c}`, `w : F_{a+b+c,d}`, `x : F_{a+b+c+d,e}`, fully
left-nested: `((u⊗v)⊗w)⊗x`). Chasing `E4M`'s own definition (`RelTensor.
map (GE4 …) id`, `QuintEdges.lean`) through `GE4`'s generator formula
(`GE4_mk_of_mem`, `PentagonEdges.lean`) gives directly

  `E4M (mk (mk (GBL.mk u v) w) x) = sgn(gParity(a+b,c,d)·j) •
    mk (mk u (gTCanon(a+b,c,d) (GBL.mk v w))) x`,

landing in `V3 = GQ5(a,b,c,d) ⊗ F_{a+b+c+d,e}` — and `GQ5(a,b,c,d)`
unfolds DEFINITIONALLY to `F_{a,b} ⊗ GBR(a+b,c,d)` (no `assoc` needed on
the codomain side at all), matching exactly the shape `smap`-whiskering
`GE1` at the shifted quadruple `(a+b,c,d,e)` would produce after
conjugating by the two-stage `ω1`/`ω3` of form (A) — confirming the
mathematical content is identical; form (B) simply records it without
building the conjugating equivalences.

## Instructions for later edges/rounds (4b: `E11M`; 4c: `E14M`; 4d:
assembly)

Each remaining `PAB` edge should get its own `EkM_leaf`, stated on the
generator decomposition natural to ITS domain vertex (matching whichever
of `V1`/`V3`/`V6`/`V8` it starts from — `E11M : V3 → V8`, `E14M : V6 →
V9`), by the SAME discipline: unfold the edge's own definition one
`assoc`/`smap`/`map` layer at a time via already-public `_mk`/
`_mk_of_mem` lemmas, never introducing a fresh conjugating `LinearEquiv`.
Assembly (4d) then chains: for `E12M∘E11M∘E4M` starting from a fully
`V1`-flattened generator, and separately `E14M∘E13M` from the SAME
generator, and shows the two results agree up to `gChiCanon K Γ (a+b) c
d e`, using `gChiCanon_spec` pointwise the way `face_P6`/`face_P1`
already do.
-/
import Superfusion.GaugeChi.QuintFaces

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

variable (a b c d e : G)

/-! ### `E4M_leaf`: the `PAB`-face leaf lemma for edge 4 (`V1 → V3`) -/

/-- **`E4M_leaf`**: `E4M`'s generator formula on a FULLY-DECOMPOSED
homogeneous generator of `V1` (`u` homogeneous of degree `j` in the
`F_{a,b}` column, `v,w,x` arbitrary) — the `PAB`-face leaf lemma for edge
4, a direct consequence of the already-public `E4M_mk` (`QuintFaces.lean`)
and `GE4_mk_of_mem` (`PentagonEdges.lean`): no new toolkit content. The
target lands in `V3`, whose inner factor `GQ5 K Γ a b c d` unfolds
DEFINITIONALLY to `F_{a,b} ⊗ GBR(a+b,c,d)` (no `assoc` needed on the
codomain), matching the module docstring's hand computation. -/
theorem E4M_leaf {j : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d))
    (x : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E4M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)
      = ((sgn (gParity K Γ (a + b) c d * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
              (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w))) x := by
  rw [E4M_mk, GE4_mk_of_mem K Γ a b c d (gParity K Γ (a + b) c d)
    (gTCanon K Γ (a + b) c d).toLinearMap (gCanonHphi4 K Γ a b c d) hu]
  show RelTensor.mk K (Γ.D (a + b + c + d)).carrier
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d))
      (FusionColumn (Γ.fuse (a + b + c + d) e))
      (((sgn (gParity K Γ (a + b) c d * j) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
          (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w))) x = _
  rw [map_zsmul, LinearMap.smul_apply]
  rfl

/-! ### `E13M_leaf`: the `PAB`-face leaf lemma for edge 13 (`V1 → V6`) -/

/-- **`E13M_leaf`**: `E13M`'s generator formula on the SAME
fully-decomposed `V1`-generator `E4M_leaf` uses (`u` homogeneous of
degree `ju`, `v` homogeneous of degree `jv`, `w,x` arbitrary — `E13M`'s
own `smap` amplifies over the WHOLE `GBL(a,b,c)`-column, whose degree is
`ju + jv` by `GBL.mk_mem_grading`) — chased through `E13M`'s own
definition (`gV1Assoc.trans gE13Step`, `QuintEdges3.lean`) via the
already-public `RelTensor.assoc_mk` and `smap_mk_of_mem`: no new toolkit
content. -/
theorem E13M_leaf {ju jv : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {v : FusionColumn (Γ.fuse (a + b) c)} (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) (x : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E13M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)
      = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
            (GBL.mk Γ a b c u v) (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)) := by
  have h1 : gV1Assoc K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)
    = RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBL Γ (a + b + c) d e)
        (GBL.mk Γ a b c u v) (GBL.mk Γ (a + b + c) d e w x) :=
    RelTensor.assoc_mk K (Γ.D (a + b + c)).carrier (Γ.D (a + b + c + d)).carrier
      (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) (FusionColumn (Γ.fuse (a + b + c + d) e))
      (GBL.mk Γ a b c u v) w x
  have h2 : gE13Step K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBL Γ (a + b + c) d e)
        (GBL.mk Γ a b c u v) (GBL.mk Γ (a + b + c) d e w x))
    = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
          (GBL.mk Γ a b c u v) (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)) := by
    show smap (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
        (gTCanon K Γ (a + b + c) d e).toLinearMap (gParity K Γ (a + b + c) d e)
        (gCanonHphi4 K Γ (a + b) c d e)
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBL Γ (a + b + c) d e)
          (GBL.mk Γ a b c u v) (GBL.mk Γ (a + b + c) d e w x)) = _
    rw [smap_mk_of_mem (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
      (gTCanon K Γ (a + b + c) d e).toLinearMap (gParity K Γ (a + b + c) d e)
      (gCanonHphi4 K Γ (a + b) c d e) (GBL.mk_mem_grading Γ a b c hu hv)]
    rfl
  show gE13Step K Γ a b c d e (gV1Assoc K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)) = _
  rw [h1, h2]

/-! ### `E12M_leaf`: the `PAB`-face leaf lemma for edge 12 (`V8 → V9`) -/

/-- **`E12M_leaf`**: `E12M`'s generator formula on a `V8`-generator split
only at the OUTER `F_{a,b}` slot (`t` homogeneous of degree `i`; the
INNER `V8Inner`-generator is taken already flattened as `p ⊗ q` since
`E12M`'s own inner map `gTCanon Γ c d e` acts on the whole `p : GBL Γ c d
e` at once, needing no further decomposition) — chased through `E12M`'s
own definition (`E12Mequiv = smapEquiv (E12MInnerEquiv) …`,
`QuintEdges.lean`) via the already-public `smap_mk_of_mem`,
`E12MInnerEquiv_toLinearMap`, and `RelTensor.map_mk`: no new toolkit
content. -/
theorem E12M_leaf {i : ZMod 2} {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) i)
    (p : GBL Γ c d e) (q : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    E12M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) p q))
      = ((sgn (gParity K Γ c d e * i) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
              (FusionColumn (Γ.fuse (a + b) (c + d + e))) (gTCanon K Γ c d e p) q) := by
  have h1 : (E12MInnerEquiv K Γ a b c d e).toLinearMap
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e))) p q)
    = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e))) (gTCanon K Γ c d e p) q := by
    show RelTensor.map (gTCanon K Γ c d e).toLinearMap LinearMap.id (gCanonRight K Γ c d e)
        (fun _ _ => rfl)
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) p q) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    rfl
  show smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (E12MInnerEquiv K Γ a b c d e).toLinearMap (gParity K Γ c d e)
      (E12MInnerEquiv_aSlot K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) p q)) = _
  rw [smap_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    (E12MInnerEquiv K Γ a b c d e).toLinearMap (gParity K Γ c d e)
    (E12MInnerEquiv_aSlot K Γ a b c d e) ht, h1]

end GaugeChi

end Superfusion

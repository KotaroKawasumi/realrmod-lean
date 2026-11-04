/-
Superfusion / GaugeChi / QuintSquares

Milestone M13-5a of the abstract `(p, χ)` arc (the K₅ chain, SQUARE
phase): **the three square faces `S1`, `S2`, `S3`** (`docs/m13-design.md`'s
ledger), built on the 14 vertex types (`Quint.lean`), the 21 edge maps
(`QuintEdges.lean` .. `QuintEdges8.lean`), and the square toolkit
(`Quint.lean`'s `smap_comp_mapFirst`/`map_comm_midEndFirst`).

**The general mechanism**: each square is two amplifications of `gTCanon`
in DISJOINT slots of a common vertex's bracketing tree, which
supercommute up to the Koszul sign `(-1)^{p(inner)·p(outer)}` — the sign
of `smap`'s own FIRST-SLOT sign law (`smap_mk_of_mem`). Concretely, each
square's four corner vertices/edges factor (via the fixed `RelTensor.assoc`
reassociations already built for the individual edges, `gV1Assoc` etc.)
through a COMMON intermediate shape `(M ⊗[A] N) ⊗[B] P`/`M ⊗[A] (N ⊗[B] P)`
where the "inner" edge is `RelTensor.map f id` (`f` the inner move,
degree `ein`) and the "outer" edge is `smap 𝒜 ℳ g eout hg` (`g` the outer
move, degree `eout`); `smap_comp_mapFirst` then gives the square directly.

**The one new reusable toolkit piece** (`assoc_comp_mapFirstOuter`,
deliverable of this round): the naturality of `RelTensor.assoc` against
an OUTER first-slot `RelTensor.map` — `assoc ∘ (map F id) = (map f id) ∘
assoc` for `F : M ⊗[A] N →ₗ M' ⊗[A] N` any map with a given `mk`-formula
`F (mk m n) = mk (f m) n` and its own `B`-equivariance witness (supplied,
for the edges landed here, by the ALREADY-PUBLIC `GE1_rightTotal`/
`GE3_rightTotal`-style facts of `QuintEdges.lean`, since `F` is always one
of the fixed `GE_k`-style edge generators). Proved ONCE, entirely at the
level of raw `RelTensor` types (no `def`-wrapped vertex codomain, so none
of `QuintEdges.lean`'s documented `induction`/`rw` transparency traps
apply), by `RelTensor.hom_ext` + `RelTensor.induction_on` + the two
generator formulas `RelTensor.map_mk`/`RelTensor.assoc.assoc_mk` — reused
identically for `S1`'s `gV1Assoc`/`gV2Assoc` step.

**`S1` landed this round** (`docs/m13-design.md`'s ledger, `{v1,v2,v6,v7}`):

  `E16M ∘ₗ E1M = sgn (gParity K Γ a b c * gParity K Γ (a+b+c) d e) •
    (E20M ∘ₗ E13M)`,  `V1 K Γ a b c d e → V7 K Γ a b c d e`.

Method: `gV2Assoc.comp E1M = (map (gTCanon a b c) id).comp gV1Assoc`
(`assoc_comp_mapFirstOuter`, `f := gTCanon a b c`, `F := GE1 (gTCanon a b
c)`); `gE13Step`/`gE16Step` are ALREADY literally `smap`'s at the shared
post-`gV1Assoc`/`gV2Assoc` level (`smapEquiv_toLinearMap`); `E20M` is
already a bare `map (gTCanon a b c) id` at THAT level (no further assoc
needed, `V6`/`V7` already in post-assoc form) — so `smap_comp_mapFirst`
applies directly at the `gV1Assoc`-transported level, and `E13M`/`E20M`
being pre/post-composed with the identity `gV1Assoc`/`gV2Assoc`
inverses collapses the assembly to the ledger's statement exactly.

**Sign spelling**: `sgn : ZMod 2 → M` for `[CommGroup M] [GroupSign M]`
(`Conventions.lean`), the scalar acting on the `K`-vector space
`V1 →ₗ[K] V7` via the `ℤ`-cast `((sgn (…) : ℤˣ) : ℤ) • (…)` — the exact
spelling `smap_comp_mapFirst` itself produces (`Quint.lean`), matching the
convention the eventual `dm₄`/`cupOne₃₃` assembly (M13-6) will need to
respell over `K`/`Kˣ`.
-/
import Superfusion.GaugeChi.QuintEdges8

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-! ### The one new reusable toolkit piece: `assoc` naturality against an
outer first-slot map -/

section AssocMapFirst

variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {M M' : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module K M'] [Module Aᵐᵒᵖ M']
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [Module Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [IsScalarTower K A N] [IsScalarTower K Bᵐᵒᵖ N]
variable {P : Type*} [AddCommGroup P] [Module K P] [Module B P]

omit [Invertible (2 : K)] in
/-- **`RelTensor.assoc` naturality against an outer first-slot map**:
for `f : M →ₗ M'` right-`A`-equivariant and `F : M ⊗[A] N →ₗ M' ⊗[A] N`
ANY map with `F`'s own `mk`-formula `F (mk m n) = mk (f m) n` and its own
right-`B`-equivariance witness `hF` (supplied, at each use site, by the
edge's own already-public `_rightTotal` fact — `F` is always a FIXED
`GE_k`-style edge generator, never abstracted further), `assoc` conjugates
`map F id` (at the `(M ⊗[A] N) ⊗[B] P` level) to `map f id` (at the
`M ⊗[A] (N ⊗[B] P)` level). Proved once, entirely on raw `RelTensor`
types — no `def`-wrapped vertex codomain, so none of `QuintEdges.lean`'s
documented transparency traps apply. -/
theorem assoc_comp_mapFirstOuter
    (f : M →ₗ[K] M') (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (F : (M ⊗[A;K] N) →ₗ[K] (M' ⊗[A;K] N))
    (hFmk : ∀ (m : M) (n : N), F (RelTensor.mk K A M N m n) = RelTensor.mk K A M' N (f m) n)
    (hF : ∀ (b : B) (z : M ⊗[A;K] N), F (MulOpposite.op b • z) = MulOpposite.op b • F z) :
    (RelTensor.assoc K A B M' N P).toLinearMap ∘ₗ
        RelTensor.map F (LinearMap.id : P →ₗ[K] P) hF (fun _ _ => rfl)
      = RelTensor.map f (LinearMap.id : (N ⊗[B;K] P) →ₗ[K] (N ⊗[B;K] P)) hf (fun _ _ => rfl) ∘ₗ
          (RelTensor.assoc K A B M N P).toLinearMap := by
  refine gHomExtAssoc K fun m n p => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_toLinearMap, RelTensor.map_mk, hFmk, LinearMap.id_apply,
    RelTensor.assoc_mk, RelTensor.assoc_mk, RelTensor.map_mk, LinearMap.id_apply]

end AssocMapFirst

/-! ### A second reusable toolkit piece: an outer first-slot `map`
commutes with `RelTensor.mapEquivRight` (needed for `S2`'s `gFourCast`
stage) -/

section MapEquivRightCommMapFirst

variable {A : Type*} [Ring A]
variable {M M' : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module K M'] [Module Aᵐᵒᵖ M']
variable {N N' : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [AddCommGroup N'] [Module K N'] [Module A N']

omit [Invertible (2 : K)] in
/-- `RelTensor.mapEquivRight`'s `.toLinearMap` is the raw `map id φ` it
was built from (the `RelTensor.mapEquivLeft_toLinearMap` companion,
`ChiAbs.lean`, one slot over — `LinearEquiv.ofLinear`'s `.toLinearMap`
field is its first argument by `rfl`). -/
theorem RelTensor.mapEquivRight_toLinearMap (φ : N ≃ₗ[K] N')
    (hφ : ∀ (a : A) (n : N), φ (a • n) = a • φ n) :
    (RelTensor.mapEquivRight K φ hφ (M := M)).toLinearMap
      = RelTensor.map (LinearMap.id : M →ₗ[K] M) φ.toLinearMap (fun _ _ => rfl) hφ :=
  rfl

omit [Invertible (2 : K)] in
/-- **An outer first-slot `map` commutes with `mapEquivRight`** (disjoint
slots, sign-free — both are plain, unsigned `RelTensor.map`s): for
`f : M →ₗ M'` right-`A`-equivariant and `φ : N ≃ₗ N'` left-`A`-equivariant,
`mapEquivRight φ ∘ (map f id) = (map f id) ∘ mapEquivRight φ` — the two
combined conjuncts of `map_id_comp_map_id` (`Quint.lean`), both equal to
`map f φ.toLinearMap`. -/
theorem mapEquivRight_comp_mapFirst
    (f : M →ₗ[K] M') (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (φ : N ≃ₗ[K] N') (hφ : ∀ (a : A) (n : N), φ (a • n) = a • φ n)
    (z : M ⊗[A;K] N) :
    (RelTensor.mapEquivRight K φ hφ)
        (RelTensor.map f (LinearMap.id : N →ₗ[K] N) hf (fun _ _ => rfl) z)
      = RelTensor.map f (LinearMap.id : N' →ₗ[K] N') hf (fun _ _ => rfl)
          ((RelTensor.mapEquivRight K φ hφ) z) := by
  have h := LinearMap.congr_fun
    ((map_id_comp_map_id K f φ.toLinearMap hf hφ).1.trans
      (map_id_comp_map_id K f φ.toLinearMap hf hφ).2.symm) z
  simpa only [LinearMap.comp_apply, ← RelTensor.mapEquivRight_toLinearMap,
    LinearEquiv.coe_toLinearMap] using h

end MapEquivRightCommMapFirst

variable (a b c d e : G)

/-! ### `S1` `{V1,V2,V6,V7}`: `E16M ∘ E1M = sgn(p(a,b,c)·p(a+b+c,d,e)) •
(E20M ∘ E13M)` -/

section S1

/-- **`gV2Assoc` conjugates `E1M` to the whiskered `gTCanon Γ a b c`**
at the `gV1Assoc`-transported level — `assoc_comp_mapFirstOuter`
specialized at `f := gTCanon Γ a b c`, `F := GE1 (gTCanon Γ a b c)`. -/
theorem gV2Assoc_comp_E1M :
    (gV2Assoc K Γ a b c d e).toLinearMap ∘ₗ E1M K Γ a b c d e
      = RelTensor.map (gTCanon K Γ a b c).toLinearMap (LinearMap.id : GBL Γ (a + b + c) d e →ₗ[K] _)
          (gCanonRight K Γ a b c) (fun _ _ => rfl) ∘ₗ (gV1Assoc K Γ a b c d e).toLinearMap :=
  assoc_comp_mapFirstOuter K (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c)
    (GE1 K Γ a b c d (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
    (GE1_mk K Γ a b c d (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
    (GE1_rightTotal K Γ a b c d)

/-- **`gE13Step`/`gE16Step` are `smap`'s of the same generator at the
`gV1Assoc`/`gV2Assoc`-transported level** — `smapEquiv_toLinearMap`,
restated at both first-slot spectators `GBL Γ a b c`/`GBR Γ a b c`. -/
theorem gE13Step_toLinearMap :
    (gE13Step K Γ a b c d e).toLinearMap
      = smap (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) (gTCanon K Γ (a + b + c) d e).toLinearMap
          (gParity K Γ (a + b + c) d e) (gCanonHphi4 K Γ (a + b) c d e) :=
  PentagonB.smapEquiv_toLinearMap K (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
    (gTCanon K Γ (a + b + c) d e) (gParity K Γ (a + b + c) d e) (gCanonHphi4 K Γ (a + b) c d e)

theorem gE16Step_toLinearMap :
    (gE16Step K Γ a b c d e).toLinearMap
      = smap (Γ.D (a + b + c)).grading (GBR.grading Γ a b c) (gTCanon K Γ (a + b + c) d e).toLinearMap
          (gParity K Γ (a + b + c) d e) (gCanonHphi4 K Γ (a + b) c d e) :=
  PentagonB.smapEquiv_toLinearMap K (Γ.D (a + b + c)).grading (GBR.grading Γ a b c)
    (gTCanon K Γ (a + b + c) d e) (gParity K Γ (a + b + c) d e) (gCanonHphi4 K Γ (a + b) c d e)

/-- **The square lemma, at the `gV1Assoc`-transported level**, restated
directly against `gE13Step`/`gE16Step`'s own `.toLinearMap` (folding
`smap_comp_mapFirst`'s raw conclusion back through `gE13Step_toLinearMap`/
`gE16Step_toLinearMap`): `f := gTCanon Γ a b c` (`ein := p(a,b,c)`),
`g := gTCanon Γ (a+b+c) d e` (`eout := p(a+b+c,d,e)`). -/
theorem gE16Step_comp_map_gTCanon :
    (gE16Step K Γ a b c d e).toLinearMap ∘ₗ
        RelTensor.map (gTCanon K Γ a b c).toLinearMap
          (LinearMap.id : GBL Γ (a + b + c) d e →ₗ[K] _) (gCanonRight K Γ a b c) (fun _ _ => rfl)
      = ((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : ℤˣ) : ℤ) •
          (RelTensor.map (gTCanon K Γ a b c).toLinearMap
            (LinearMap.id : GBR Γ (a + b + c) d e →ₗ[K] _) (gCanonRight K Γ a b c) (fun _ _ => rfl)) ∘ₗ
          (gE13Step K Γ a b c d e).toLinearMap := by
  rw [gE16Step_toLinearMap, gE13Step_toLinearMap]
  exact smap_comp_mapFirst K (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) (GBR.grading Γ a b c)
    (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c) (gCanonDeg K Γ a b c)
    (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)

/-- **`S1`**: `E16M ∘ E1M = sgn(p(a,b,c)·p(a+b+c,d,e)) • (E20M ∘ E13M)`,
maps `V1 → V7` (`docs/m13-design.md`'s ledger). Assembled POINTWISE
(`LinearMap.ext`), sidestepping `QuintEdges.lean`'s documented `rw`-at-
`def`-wrapped-type transparency trap: each step is either a value-level
`rfl` unfolding of an edge's own definition (`E16M`/`E13M`/`E20M`, all
`.toLinearMap`/`.trans`-composites, unfold to nested application by
`rfl`) or a direct term-mode instance of an already-proven `LinearMap`
equation via `LinearMap.congr_fun` (never `rw`-ing the named equation
itself). -/
theorem square_S1 :
    E16M K Γ a b c d e ∘ₗ E1M K Γ a b c d e
      = ((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : ℤˣ) : ℤ) •
          (E20M K Γ a b c d e ∘ₗ E13M K Γ a b c d e) := by
  refine LinearMap.ext fun x => ?_
  have step1 : E16M K Γ a b c d e (E1M K Γ a b c d e x)
      = (gE16Step K Γ a b c d e) ((gV2Assoc K Γ a b c d e) (E1M K Γ a b c d e x)) := rfl
  have step2 : (gV2Assoc K Γ a b c d e) (E1M K Γ a b c d e x)
      = RelTensor.map (gTCanon K Γ a b c).toLinearMap
          (LinearMap.id : GBL Γ (a + b + c) d e →ₗ[K] _) (gCanonRight K Γ a b c) (fun _ _ => rfl)
          ((gV1Assoc K Γ a b c d e) x) :=
    LinearMap.congr_fun (gV2Assoc_comp_E1M K Γ a b c d e) x
  have step3 : (gE16Step K Γ a b c d e)
        (RelTensor.map (gTCanon K Γ a b c).toLinearMap
          (LinearMap.id : GBL Γ (a + b + c) d e →ₗ[K] _) (gCanonRight K Γ a b c) (fun _ _ => rfl)
          ((gV1Assoc K Γ a b c d e) x))
      = ((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : ℤˣ) : ℤ) •
          (RelTensor.map (gTCanon K Γ a b c).toLinearMap
            (LinearMap.id : GBR Γ (a + b + c) d e →ₗ[K] _) (gCanonRight K Γ a b c) (fun _ _ => rfl)
            ((gE13Step K Γ a b c d e) ((gV1Assoc K Γ a b c d e) x))) :=
    LinearMap.congr_fun (gE16Step_comp_map_gTCanon K Γ a b c d e) ((gV1Assoc K Γ a b c d e) x)
  have step4 : E20M K Γ a b c d e (E13M K Γ a b c d e x)
      = RelTensor.map (gTCanon K Γ a b c).toLinearMap
          (LinearMap.id : GBR Γ (a + b + c) d e →ₗ[K] _) (gCanonRight K Γ a b c) (fun _ _ => rfl)
          ((gE13Step K Γ a b c d e) ((gV1Assoc K Γ a b c d e) x)) := rfl
  show E16M K Γ a b c d e (E1M K Γ a b c d e x)
      = ((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : ℤˣ) : ℤ) •
          (E20M K Γ a b c d e (E13M K Γ a b c d e x))
  rw [step1, step2, step3, ← step4]
  rfl

end S1

/-! ### `S2` `{V4,V5,V10,V11}`: `E18M ∘ E3M = sgn(p(b,c,d)·p(a,b+c+d,e)) •
(E6M ∘ E15M)` -/

section S2

/-- **The `D_{a+b+c+d}`-equivariance of the bare `map (gTCanon Γ b c d) id`**
at the `gq3Assoc`-precursor level `GBL(b,c,d) ⊗ F_{a,b+c+d}` (needed to
whisker it one level further, `E3M`'s own OUTER map): derived from
`GE3`'s `Total`-equivariance (`GE3_rightTotal`) transported through
`gq3Assoc`'s OWN `Total`-naturality (`gq3Assoc_rightTotal_general`) and
its factoring identity (`GE3_comp_gq3Assoc`) — `GE3(t₃) = map(t₃,id) ∘
gq3Assoc.symm`, so `map(t₃,id)`'s equivariance is `GE3(t₃)`'s conjugated
back through `gq3Assoc`. -/
theorem mapT3_rightTotal (τ : (Γ.D (a + b + c + d)).carrier)
    (z : RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (FusionColumn (Γ.fuse a (b + c + d)))) :
    RelTensor.map (gTCanon K Γ b c d).toLinearMap
        (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] _) (gCanonRight K Γ b c d)
        (fun _ _ => rfl) (MulOpposite.op τ • z)
      = MulOpposite.op τ •
          RelTensor.map (gTCanon K Γ b c d).toLinearMap
            (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] _) (gCanonRight K Γ b c d)
            (fun _ _ => rfl) z := by
  have h1 : gq3Assoc K Γ a b c d (MulOpposite.op τ • z)
      = MulOpposite.op τ • gq3Assoc K Γ a b c d z := by
    show gq3Assoc K Γ a b c d
        (rightActionEnd K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) (MulOpposite.op τ) z)
      = MulOpposite.op τ • gq3Assoc K Γ a b c d z
    exact gq3Assoc_rightTotal_general K Γ a b c d τ z
  have e1 : RelTensor.map (gTCanon K Γ b c d).toLinearMap
        (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] _) (gCanonRight K Γ b c d)
        (fun _ _ => rfl) (MulOpposite.op τ • z)
      = GE3 K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d)
          (gq3Assoc K Γ a b c d (MulOpposite.op τ • z)) :=
    (GE3_comp_gq3Assoc K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d)
      (MulOpposite.op τ • z)).symm
  rw [e1, h1, GE3_rightTotal, GE3_comp_gq3Assoc]
  rfl

/-- **`E3M` factors through `gV4AssocA`**: `E3M = (map (map (gTCanon Γ b c d)
id) id) ∘ gV4AssocA` — `GE3`'s own `.comp gq3Assoc.symm` factoring,
whiskered one level up (`map_comp`-free: proved directly on `V4`'s TOP-level
generators, `GE3`'s definitional unfolding closes the `mk`-case by `rfl`). -/
theorem E3M_eq_mapMap_comp_gV4AssocA :
    E3M K Γ a b c d e
      = RelTensor.map
          (RelTensor.map (gTCanon K Γ b c d).toLinearMap
            (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] _) (gCanonRight K Γ b c d)
            (fun _ _ => rfl))
          (LinearMap.id : FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K] _)
          (mapT3_rightTotal K Γ a b c d) (fun _ _ => rfl)
        ∘ₗ (gV4AssocA K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun z p => ?_
  show RelTensor.map (GE3 K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
      LinearMap.id (GE3_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) z p)
    = RelTensor.map
        (RelTensor.map (gTCanon K Γ b c d).toLinearMap
          (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] _) (gCanonRight K Γ b c d)
          (fun _ _ => rfl))
        (LinearMap.id : FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K] _)
        (mapT3_rightTotal K Γ a b c d) (fun _ _ => rfl)
        (RelTensor.map (gq3Assoc K Γ a b c d).symm.toLinearMap
          (LinearMap.id : FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K] _)
          (gq3Assoc_symm_rightTotal K Γ a b c d) (fun _ _ => rfl)
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) z p))
  rw [RelTensor.map_mk, RelTensor.map_mk, RelTensor.map_mk]
  rfl

/-- **`gV5Assoc` conjugates `E3M` to the whiskered `gTCanon Γ b c d`** at
the `gV4Assoc`-transported level: chains `E3M_eq_mapMap_comp_gV4AssocA`
(the outer `mapT3`-factoring), `assoc_comp_mapFirstOuter` (naturality
against `gV4AssocB`, the plain `RelTensor.assoc` stage), and
`mapEquivRight_comp_mapFirst` (commutation past `gV4AssocC`, the
`gFourCast` stage) — POINTWISE, mirroring `square_S1`'s discipline. -/
theorem gV5Assoc_comp_E3M :
    (gV5Assoc K Γ a b c d e).toLinearMap ∘ₗ E3M K Γ a b c d e
      = RelTensor.map (gTCanon K Γ b c d).toLinearMap
          (LinearMap.id : GBL Γ a (b + c + d) e →ₗ[K] _) (gCanonRight K Γ b c d) (fun _ _ => rfl)
          ∘ₗ (gV4Assoc K Γ a b c d e).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have step1 : E3M K Γ a b c d e x
      = RelTensor.map (RelTensor.map (gTCanon K Γ b c d).toLinearMap
          (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] _) (gCanonRight K Γ b c d)
          (fun _ _ => rfl))
        (LinearMap.id : FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K] _)
        (mapT3_rightTotal K Γ a b c d) (fun _ _ => rfl) ((gV4AssocA K Γ a b c d e) x) :=
    LinearMap.congr_fun (E3M_eq_mapMap_comp_gV4AssocA K Γ a b c d e) x
  have step2 := LinearMap.congr_fun
    (assoc_comp_mapFirstOuter K (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d)
      (RelTensor.map (gTCanon K Γ b c d).toLinearMap
        (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] _) (gCanonRight K Γ b c d)
        (fun _ _ => rfl))
      (fun m n => RelTensor.map_mk _ _ _ _ m n) (mapT3_rightTotal K Γ a b c d))
    ((gV4AssocA K Γ a b c d e) x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at step2
  have step3 := mapEquivRight_comp_mapFirst K (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d)
    (gFourCast K Γ a b c d e) (gFourCast_midSlot K Γ a b c d e)
    ((RelTensor.assoc K (Γ.D (b + c + d)).carrier (Γ.D (a + b + c + d)).carrier (GBL Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) (FusionColumn (Γ.fuse (a + b + c + d) e)))
      ((gV4AssocA K Γ a b c d e) x))
  show (RelTensor.mapEquivRight K (gFourCast K Γ a b c d e) (gFourCast_midSlot K Γ a b c d e))
      ((RelTensor.assoc K (Γ.D (b + c + d)).carrier (Γ.D (a + b + c + d)).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) (FusionColumn (Γ.fuse (a + b + c + d) e)))
        (E3M K Γ a b c d e x))
    = RelTensor.map (gTCanon K Γ b c d).toLinearMap
        (LinearMap.id : GBL Γ a (b + c + d) e →ₗ[K] _) (gCanonRight K Γ b c d) (fun _ _ => rfl)
        ((RelTensor.mapEquivRight K (gFourCast K Γ a b c d e) (gFourCast_midSlot K Γ a b c d e))
          ((gV4AssocB K Γ a b c d e) ((gV4AssocA K Γ a b c d e) x)))
  rw [step1, step2, step3]
  rfl

/-- **`gE15Step`/`gE18Step` are `smap`'s of the same generator at the
`gV4Assoc`/`gV5Assoc`-transported level**, the `S2`-mirror of `S1`'s
`gE13Step_toLinearMap`/`gE16Step_toLinearMap`. -/
theorem gE15Step_toLinearMap :
    (gE15Step K Γ a b c d e).toLinearMap
      = smap (Γ.D (b + c + d)).grading (GBL.grading Γ b c d) (gTCanon K Γ a (b + c + d) e).toLinearMap
          (gParity K Γ a (b + c + d) e) (gCanonMidSlot K Γ a (b + c + d) e) :=
  PentagonB.smapEquiv_toLinearMap K (Γ.D (b + c + d)).grading (GBL.grading Γ b c d)
    (gTCanon K Γ a (b + c + d) e) (gParity K Γ a (b + c + d) e) (gCanonMidSlot K Γ a (b + c + d) e)

theorem gE18Step_toLinearMap :
    (gE18Step K Γ a b c d e).toLinearMap
      = smap (Γ.D (b + c + d)).grading (GBR.grading Γ b c d) (gTCanon K Γ a (b + c + d) e).toLinearMap
          (gParity K Γ a (b + c + d) e) (gCanonMidSlot K Γ a (b + c + d) e) :=
  PentagonB.smapEquiv_toLinearMap K (Γ.D (b + c + d)).grading (GBR.grading Γ b c d)
    (gTCanon K Γ a (b + c + d) e) (gParity K Γ a (b + c + d) e) (gCanonMidSlot K Γ a (b + c + d) e)

/-- **The square lemma, at the `gV4Assoc`-transported level**: `f :=
gTCanon Γ b c d` (`ein := p(b,c,d)`), `g := gTCanon Γ a (b+c+d) e`
(`eout := p(a,b+c+d,e)`) — the `S2`-mirror of `S1`'s
`gE16Step_comp_map_gTCanon`. -/
theorem gE18Step_comp_map_gTCanon :
    (gE18Step K Γ a b c d e).toLinearMap ∘ₗ
        RelTensor.map (gTCanon K Γ b c d).toLinearMap
          (LinearMap.id : GBL Γ a (b + c + d) e →ₗ[K] _) (gCanonRight K Γ b c d) (fun _ _ => rfl)
      = ((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : ℤˣ) : ℤ) •
          (RelTensor.map (gTCanon K Γ b c d).toLinearMap
            (LinearMap.id : GBR Γ a (b + c + d) e →ₗ[K] _) (gCanonRight K Γ b c d) (fun _ _ => rfl)) ∘ₗ
          (gE15Step K Γ a b c d e).toLinearMap := by
  rw [gE18Step_toLinearMap, gE15Step_toLinearMap]
  exact smap_comp_mapFirst K (Γ.D (b + c + d)).grading (GBL.grading Γ b c d) (GBR.grading Γ b c d)
    (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d) (gCanonDeg K Γ b c d)
    (gTCanon K Γ a (b + c + d) e).toLinearMap (gCanonMidSlot K Γ a (b + c + d) e)

/-- **`gV10Assoc` cancels `E15M`'s own closing `gV10Assoc.symm`**:
`E15M := (gV4Assoc.trans gE15Step).trans gV10Assoc.symm`, so
`gV10Assoc ∘ E15M = gE15Step ∘ gV4Assoc`. -/
theorem gV10Assoc_comp_E15M :
    (gV10Assoc K Γ a b c d e).toLinearMap ∘ₗ E15M K Γ a b c d e
      = (gE15Step K Γ a b c d e).toLinearMap ∘ₗ (gV4Assoc K Γ a b c d e).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  show (gV10Assoc K Γ a b c d e) (E15M K Γ a b c d e x)
    = (gE15Step K Γ a b c d e) ((gV4Assoc K Γ a b c d e) x)
  have h : E15M K Γ a b c d e x
      = (gV10Assoc K Γ a b c d e).symm
          ((gE15Step K Γ a b c d e) ((gV4Assoc K Γ a b c d e) x)) := rfl
  rw [h, LinearEquiv.apply_symm_apply]

/-- **`gV11Assoc` cancels `E18M`'s own closing `gV11Assoc.symm`**, the
`S2`-mirror of `gV10Assoc_comp_E15M`. -/
theorem gV11Assoc_comp_E18M :
    (gV11Assoc K Γ a b c d e).toLinearMap ∘ₗ E18M K Γ a b c d e
      = (gE18Step K Γ a b c d e).toLinearMap ∘ₗ (gV5Assoc K Γ a b c d e).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  show (gV11Assoc K Γ a b c d e) (E18M K Γ a b c d e x)
    = (gE18Step K Γ a b c d e) ((gV5Assoc K Γ a b c d e) x)
  have h : E18M K Γ a b c d e x
      = (gV11Assoc K Γ a b c d e).symm
          ((gE18Step K Γ a b c d e) ((gV5Assoc K Γ a b c d e) x)) := rfl
  rw [h, LinearEquiv.apply_symm_apply]

/-- **`gV11Assoc` conjugates `E6M` to the whiskered `gTCanon Γ b c d`**
at the `gV10Assoc`-transported level — `assoc_comp_mapFirstOuter`
specialized at `f := gTCanon Γ b c d`, `F := GE1 (gTCanon Γ b c d)` at
the quadruple `(b,c,d,e)`, the `S1`-mirror of `gV2Assoc_comp_E1M`. -/
theorem gV11Assoc_comp_E6M :
    (gV11Assoc K Γ a b c d e).toLinearMap ∘ₗ E6M K Γ a b c d e
      = RelTensor.map (gTCanon K Γ b c d).toLinearMap
          (LinearMap.id : GBR Γ a (b + c + d) e →ₗ[K] _) (gCanonRight K Γ b c d) (fun _ _ => rfl)
          ∘ₗ (gV10Assoc K Γ a b c d e).toLinearMap :=
  assoc_comp_mapFirstOuter K (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d)
    (GE1 K Γ b c d e (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
    (GE1_mk K Γ b c d e (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
    (GE1_rightTotal K Γ b c d e)

/-- **`S2`**: `E18M ∘ E3M = sgn(p(b,c,d)·p(a,b+c+d,e)) • (E6M ∘ E15M)`,
maps `V4 → V11` (`docs/m13-design.md`'s ledger). Assembled by cancelling
`gV11Assoc` (injective) from both sides, mirroring `square_S1` but routing
through the extra `gV5Assoc`/`gV10Assoc` legs. -/
theorem square_S2 :
    E18M K Γ a b c d e ∘ₗ E3M K Γ a b c d e
      = ((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : ℤˣ) : ℤ) •
          (E6M K Γ a b c d e ∘ₗ E15M K Γ a b c d e) := by
  refine LinearMap.ext fun x => ?_
  refine (gV11Assoc K Γ a b c d e).injective ?_
  show (gV11Assoc K Γ a b c d e) (E18M K Γ a b c d e (E3M K Γ a b c d e x))
    = (gV11Assoc K Γ a b c d e)
        (((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : ℤˣ) : ℤ) •
          (E6M K Γ a b c d e (E15M K Γ a b c d e x)))
  rw [map_zsmul]
  have hA : E18M K Γ a b c d e (E3M K Γ a b c d e x)
      = (gV11Assoc K Γ a b c d e).symm
          ((gE18Step K Γ a b c d e) ((gV5Assoc K Γ a b c d e) (E3M K Γ a b c d e x))) := rfl
  have hB := LinearMap.congr_fun (gV5Assoc_comp_E3M K Γ a b c d e) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hB
  have hC := LinearMap.congr_fun (gE18Step_comp_map_gTCanon K Γ a b c d e)
    ((gV4Assoc K Γ a b c d e) x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.smul_apply] at hC
  have hD := LinearMap.congr_fun (gV11Assoc_comp_E6M K Γ a b c d e) (E15M K Γ a b c d e x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hD
  have hE := LinearMap.congr_fun (gV10Assoc_comp_E15M K Γ a b c d e) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hE
  rw [hA, LinearEquiv.apply_symm_apply, hB, hC, hD, hE]

end S2

end GaugeChi

end Superfusion

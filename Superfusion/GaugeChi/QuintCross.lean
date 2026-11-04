/-
Superfusion / GaugeChi / QuintCross

Milestone M13-4g-ii of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase): an attempt to **dissolve the CROSS-BRACKETING GAP** that blocks
`face_PDE` (`QuintFaces4.lean`'s module docstring gives the full diagnosis;
read it first — this file's own analysis sharpens it and is not
self-contained without it).

## What lands

**(1) `gTCanon`'s three plain slot equivariances, at a GENERIC (unshifted)
triple `x y z`**, extracted from `gTCanon_mem_gInterSpace`'s
`gInterSpace`-membership exactly as `ChiCanon.lean`'s `private canon_right`/
`canon_hφ₄`/`canon_hφ₅` and `QuintEdges.lean`'s public re-statements
`gCanonRight`/`gCanonHphi4`/`gCanonHphi5` already do — but those four
existing lemmas only ever expose the RIGHT-slot conjunct (`canon_right`) and
the FIRST/THIRD slot conjuncts at a triple whose first or third letter is
itself a SUM (`gCanonHphi4` at `(x+y,z,w)`'s first slot, `gCanonHphi5` at
`(x,y,z+w)`'s third slot). The plain, unshifted-triple form of all three
slots — in particular the **middle (`D_y`) slot**, which (per
`QuintFaces4.lean`'s diagnosis) had NEVER been publicly restated anywhere in
`GaugeChi` — is landed here as `gTCanon_aSlot_equivariant`,
`gTCanon_bSlot_equivariant`, `gTCanon_cSlot_equivariant`. Also landed:
`gTCanon_mem_grading`, the pointwise (non-`Submodule`-membership) form of
`gTCanon`'s own homogeneity transport `m ∈ GBL.grading j → gTCanon m ∈
GBR.grading (j + gParity x y z)` (`QuintEdges.lean`'s `gCanonDeg`, unfolded
via `mem_homGrading` at a point).

**(2)/(3): NOT landed**, after a genuine attempt and a sharpened diagnosis
of exactly why the natural "use the new `D_b`-slot equivariance as a
naturality bridge" idea (`QuintFaces4.lean`'s "one promising lead") does
NOT, in fact, work — see below. No pair-recognition lemma, no cross-
bracketing naturality square, and no new `E10M` recognition are landed;
`E10M_mk` (the closing recast's own leaf lemma) turns out to ALREADY be
public, at `QuintFaces.lean:244` (`E10M_mk`, landed by the `P1`-face round,
reused verbatim — no new content needed there).

## Why the `D_b`-equivariance bridge does not work: the sharpened diagnosis

`QuintFaces4.lean` identifies the obstruction correctly at a high level
(`gTCanon K Γ a b c`'s raw output on a generator is an OPAQUE element of
`GBR Γ a b c`) and flags `gTCanon`'s `D_b`-slot equivariance as "the natural
candidate bridge," since `b` is the shared middle letter of both `GBL`'s
`(a,b),(a+b,c)` bracketing and `GBR`'s `(b,c),(a,b+c)` bracketing. Having
now landed that equivariance (`gTCanon_bSlot_equivariant`, this file) and
traced precisely what `E17M`'s own first two stages
(`gV7AssocA`/`gV7Swap`, `QuintEdges7.lean`) actually need from `gTCanon`'s
image, the bridge does not close, for a structural reason that no slot
equivariance can repair:

* `gV7AssocA` (`RelTensor.assoc`, sign-free) exposes `GBR Γ a b c = F_{b,c}
  ⊗_{D_{b+c}} F_{a,b+c}`'s SECOND factor `F_{a,b+c}` as a value in the
  intermediate type `F_{b,c} ⊗ (F_{a,b+c} ⊗ GBR(a+b+c,d,e))` — well-defined
  as a LINEAR map of `gTCanon`'s (possibly non-`GBR.mk`-shaped) image, but
  this does not by itself hand back an EXPLICIT `F_{a,b+c}`-valued vector to
  feed the next stage.
* `gV7Swap` (`Bimod.midSwap`, `MiddleSwap.lean`) then needs THAT
  `F_{a,b+c}`-component's OWN `FusionColumn.grading (Γ.fuse a (b+c))`-degree
  to fix a Koszul sign — concretely, `midSwap`'s underlying closed trilinear
  form (`MiddleSwap.lean`'s `swapTri`, `n ⊗ (m ⊗ p) - 2 (modProj 𝒩 1 n) ⊗
  ((modProj ℳ 1 m) ⊗ p)`) is built from `modProj ℳ 1`, the ODD-PART
  PROJECTION of the swapped `M`-slot element (`M := FusionColumn (Γ.fuse a
  (b+c))` in `gV7Swap`'s instantiation) taken INSIDE `M`'s OWN grading
  decomposition — i.e. it depends on the individual `F_{a,b+c}`-graded
  pieces of `gTCanon`'s image, not merely on the TOTAL `GBR Γ a b c`-degree
  of that image.

  `gTCanon`'s equivariance conjuncts (`gTCanon_aSlot_equivariant` /
  `_bSlot_equivariant` / `_cSlot_equivariant`, this file; `gCanonRight`,
  `QuintEdges.lean`) are all statements of the SCALAR-ACTION shape `f (x •
  m) = ± x • f m` for `x` ranging over `D_a`/`D_b`/`D_c`/`D_{a+b+c}`. None of
  these actions is "project onto the `F_{a,b+c}`-graded component of degree
  `k`": `D_b`/`D_c` both act on `GBR Γ a b c` ONLY through its FIRST factor
  `F_{b,c}` (`GBR.bslot_smul_mk`/`GBR.cslot_smul_mk`, `RouteBimod.lean`,
  both bare `leftActionEnd`s on the first slot); `D_a` acts through the
  SECOND factor `F_{a,b+c}` but via the Koszul-signed MIDDLE action
  (`GBR.aslot_smul_mk_of_mem`), which likewise only reveals how the WHOLE
  vector transforms under a further `D_a`-scalar, not how it decomposes
  along `F_{a,b+c}`'s OWN internal grading. **A homogeneous element of a
  balanced tensor product need not be a single bi-homogeneous generator**
  (`GBR Γ a b c`'s degree-`d` piece is typically spanned by several `GBR.mk
  u_i v_i` terms with different individual splits `(i_k, d - i_k)`), so no
  amount of SCALAR-action equivariance — however many slots one restates —
  can substitute for actually knowing that decomposition. This is not a
  missing support lemma; it is a `gTCanon`-specific structural fact (or its
  absence) that the ABSTRACT, `Exists.choose`-built `gTCanon`
  (`ChiCanon.lean`) carries no witness of.

  The identical argument applies, mutatis mutandis, to the bottom route's
  `E21M`-after-`E14M` step (`gV6Swap`, `QuintEdges5.lean`, needing
  `gblPslotRslotSuperComm`'s target slot `F_{a+b,c}`'s own grading, from
  `E14M`'s opaque `gq4Close`-wrapped output) — so scoping the *other* pair
  is not cheaper: both pairs fail for the same underlying reason, not two
  independent ones.

## The sound route, and why it is out of scope this round

The one route that WOULD work is the one `gParity_cocycle`/`gChiCanon`
themselves use one level down (`ChiCanon.lean`): never chase `GE1`'s (there,
`gTCanon`'s own) opaque image through a generator computation at all — show
instead that BOTH the composite route and the target reinsertion are
nonzero elements of a COMMON degree-graded piece of an intertwiner space of
total dimension `≤ 1` (`gQuadInterSpace`, via `gradedHomF_finrank_sum_le_one`
and `parityConcentration`), forcing them equal up to a scalar pinned down by
bijectivity. Transplanting this to the K₅ level for the `V6 → V12`
(`E17M∘E20M`) and `V6 → V14`-via-`V9` (`E21M∘E14M`) pairs would need a
genuinely new **quintuple-level intertwiner-space uniqueness apparatus** —
a `gQuintInterSpace`-shaped construction, together with its own envelope
algebra, splitting, and dimension count — mirroring the ENTIRE `M12`
catalog (`InterSpace.lean`, `QuadInterface.lean`, `QuadInterface2.lean`,
`QuadEnvelope.lean`, `QuadEnvModule.lean`, `QuadEnvModule2.lean`) one
tensor-factor deeper. That is substantial new mathematical content on the
scale of a full milestone, not a support lemma, and is out of scope for
this round's budget; it is the concrete, scoped recommendation for any
continuation of `face_PDE`.
-/
import Superfusion.GaugeChi.QuintFaces4

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-! ### `gTCanon`'s three plain slot equivariances, at a generic triple -/

/-- **The `D_x`-slot ("`a`-slot") equivariance of `gTCanon Γ x y z`**, at a
GENERIC (unshifted) triple — public re-statement, extracted directly from
`gTCanon_mem_gInterSpace`'s FIRST `superEquivariant` conjunct, mirroring
`ChiCanon.lean`'s `private canon_hφ₄` (there specialized to a triple whose
first letter is itself a sum `x+y`; here landed at a bare `x`). -/
theorem gTCanon_aSlot_equivariant (x y z : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D x).carrier⦄,
      τ ∈ (Γ.D x).grading i → ∀ m : GBL Γ x y z,
        gTCanon K Γ x y z (τ • m)
          = ((sgn (gParity K Γ x y z * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ x y z m) :=
  (mem_superEquivariant (Γ.D x).grading).mp
    ((mem_gInterSpace_iff K Γ x y z).mp (gTCanon_mem_gInterSpace K Γ x y z)).2.1

/-- **The `D_y`-slot ("`b`-slot") equivariance of `gTCanon Γ x y z`** — the
MIDDLE slot, at a generic (unshifted) triple. Per `QuintFaces4.lean`'s
diagnosis this conjunct had never been publicly restated anywhere in
`GaugeChi` (`gCanonRight`/`gCanonHphi4`/`gCanonHphi5` only ever cover the
right-slot and the two SHIFTED-quadruple first/third-slot cases) — it is
the natural candidate bridge for the cross-bracketing gap (`b` is the
shared middle letter of both `GBL`'s and `GBR`'s bracketings of `a,b,c`),
though this file's own module docstring records precisely why it does not,
by itself, close that gap. -/
theorem gTCanon_bSlot_equivariant (x y z : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D y).carrier⦄,
      τ ∈ (Γ.D y).grading i → ∀ m : GBL Γ x y z,
        gTCanon K Γ x y z (τ • m)
          = ((sgn (gParity K Γ x y z * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ x y z m) :=
  (mem_superEquivariant (Γ.D y).grading).mp
    ((mem_gInterSpace_iff K Γ x y z).mp (gTCanon_mem_gInterSpace K Γ x y z)).2.2.1

/-- **The `D_z`-slot ("`c`-slot") equivariance of `gTCanon Γ x y z`**, at a
generic (unshifted) triple — the mirror of `gTCanon_aSlot_equivariant`,
extracted from the THIRD `superEquivariant` conjunct. -/
theorem gTCanon_cSlot_equivariant (x y z : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D z).carrier⦄,
      τ ∈ (Γ.D z).grading i → ∀ m : GBL Γ x y z,
        gTCanon K Γ x y z (τ • m)
          = ((sgn (gParity K Γ x y z * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ x y z m) :=
  (mem_superEquivariant (Γ.D z).grading).mp
    ((mem_gInterSpace_iff K Γ x y z).mp (gTCanon_mem_gInterSpace K Γ x y z)).2.2.2.1

/-! ### `gTCanon`'s homogeneity transport, pointwise -/

/-- **`gTCanon`'s homogeneity transport, pointwise**: a homogeneous element
of `GBL Γ x y z` of degree `j` maps to a homogeneous element of `GBR Γ x y z`
of degree `j + gParity Γ x y z` — the pointwise form of `QuintEdges.lean`'s
`gCanonDeg` (itself the `homGrading` conjunct of `gTCanon_mem_gInterSpace`),
unfolded via `mem_homGrading` at a point. This is the "t's image of a
homogeneous element is homogeneous of the shifted degree" fact the round's
brief anticipated as part of deliverable (1); it is exactly as far as
homogeneity-tracking can go without the INDIVIDUAL bi-grading information
the cross-bracketing gap actually needs (see the module docstring). -/
theorem gTCanon_mem_grading (x y z : G) {j : ZMod 2} {m : GBL Γ x y z}
    (hm : m ∈ GBL.grading Γ x y z j) :
    gTCanon K Γ x y z m ∈ GBR.grading Γ x y z (j + gParity K Γ x y z) :=
  (mem_homGrading (GBL.grading Γ x y z) (GBR.grading Γ x y z)).mp (gCanonDeg K Γ x y z) j m hm

end GaugeChi

end Superfusion

/-
Superfusion / GaugeChi / QuintFaces4

Milestone M13-4g of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase): investigation of **`face_PDE`**, the `(d+e)`-cluster pentagon face
(`E10M ∘ₗ E17M ∘ₗ E20M = gChiCanon K Γ a b c (d+e) • (E21M ∘ₗ E14M)`, as
maps `V6 → V14`).

**STATUS: `face_PDE` itself is NOT landed.** This file lands the one
genuinely free-standing support the round produced (`E20M_mk`, the
`_mk`-unfolding lemma edge 20 was missing — the "easy first-slot genre"
the round's brief anticipated), together with a full record of the
mathematical investigation, because the investigation located a REAL
mathematical gap, not merely a Lean elaboration-performance wall (contrast
`QuintFaces2.lean`'s `face_PAB`, whose obstruction is purely
elaboration-performance — the math there was verified in full by hand).

## What DOES carry over from `face_PAB`'s mechanism, verified

`gChiCanon_spec K Γ a b c (d+e)`'s five canonical intertwiners are
LITERALLY the ones `E20M`/`E17M`/`E14M`/`E21M` already use, confirmed by
direct inspection of each edge's `noncomputable def` (not just the leaf
lemmas):

* `t₁ = gTCanon K Γ a b c` — `E20M`'s own map (`QuintEdges.lean`,
  `E20M := RelTensor.map (gTCanon K Γ a b c).toLinearMap id ...`,
  literally `GE1`'s own `t₁` at `(a,b,c,d+e)`, no reinterpretation needed).
* `t₂ = gt2Canon K Γ a b c (d+e) (gTCanon K Γ a (b+c) (d+e))` — `E17M`'s
  own reinsertion (`QuintRecog4.lean`'s `E17M_leaf`, confirmed via
  `gt2Canon_mk` folding `gq2rCast`+`gTCanon (a,b+c,d+e)` together).
* `t₄ = gTCanon K Γ (a+b) c (d+e)` — `E14M`'s own reinsertion
  (`QuintRecog3.lean`'s `E14M_leaf`).
* `t₅ = gTCanon K Γ a b (c+d+e)` — `E21M`'s own reinsertion
  (`QuintRecog5.lean`'s `E21M_leaf`).
* `E10M` does **NOT** literally match `t₃ = gTCanon K Γ b c (d+e)`'s
  `GE3`-shape: `E10M`'s own `noncomputable def` (`QuintEdges2.lean`) is
  `RelTensor.map (gq4Close K Γ b c d e ∘ GE5 K Γ b c d e (gParity K Γ b c
  (d+e)) (gTCanon K Γ b c (d+e)) (gCanonHphi5 K Γ b c d e)) id ...` — a
  **`GE5`+`gq4Close`-style composite at the quadruple `(b,c,d,e)`**
  (mirroring `E5M`, `P1`'s own closing edge), not a bare `GE3`-style move
  at `(a,b,c,d+e)`. It DOES use the same `t₅`-shaped datum
  `gTCanon K Γ b c (d+e)`, but wrapped completely differently. Reconciling
  this with `gChiCanon_spec`'s own `t₃`-slot is itself nontrivial (see
  below) — the round's own hint ("`E10 = GE3`-genre") is a *positional*
  reading (E10M is the K₅ chain's third top-route edge), not a literal
  formula match, and should be corrected in any continuation.

## The genuine mathematical gap (why `face_PAB`'s method does not transfer)

`face_PAB`'s whole mechanism rests on ONE structural fact: `F_{a,b}` is
the outer-left tensor factor of **every** vertex `V1,V3,V6,V8,V9` it
touches (`V1 = ((F_{a,b}⊗F_{a+b,c})⊗F_{a+b+c,d})⊗F_{a+b+c+d,e}`, etc.), so
each edge's own `smap`-style outer layer can be keyed to `F_{a,b}`'s
grading **alone**, with the rest of the structure staying fully opaque
between consecutive edges (`E11M_general`/`E14M_general`,
`QuintFaces2.lean`) — chaining edges never needs to re-split `F_{a,b}`
because it is never "buried" inside a differently-bracketed factor along
the way.

`face_PDE`'s candidate spectator `F_{d,e}` has NO such uniform position.
Concretely, tracing `E20M` (`gTCanon K Γ a b c`, acting on `V6`'s
outer-LEFT factor `GBL Γ a b c`) into `E17M` (whose first stage
`gV7AssocA` needs `V7`'s outer-left factor `GBR Γ a b c` split via ITS
OWN natural decomposition `GBR Γ a b c = F_{b,c} ⊗_{D_{b+c}} F_{a,b+c}`,
`RouteBimod.lean`) requires relating:

* `GBL Γ a b c = F_{a,b} ⊗_{D_{a+b}} F_{a+b,c}` (the `(a,b)`-then-`c`
  bracketing `E20M`'s domain carries), and
* `GBR Γ a b c = F_{b,c} ⊗_{D_{b+c}} F_{a,b+c}` (the `a`-then-`(b,c)`
  bracketing `E17M`'s FIRST reassociation stage needs),

through `gTCanon K Γ a b c : GBL Γ a b c ≃ₗ[K] GBR Γ a b c` — a
Skolem–Noether-free, ABSTRACT (`Exists.choose`-built) canonical
intertwiner (`ChiCanon.lean`) that mixes the two bracketings NONTRIVIALLY
and is not itself built from any explicit assoc/swap formula. `E20M`'s
raw output on a generator, `gTCanon K Γ a b c (GBL.mk Γ a b c u v)`, is
therefore an OPAQUE element of `GBR Γ a b c` — not (for general `u,v`) of
the form `GBR.mk Γ a b c u' v'` for any recognizable `u',v'` — so it
cannot be fed into `E17M`'s own generator formula (`E17M_leaf`,
`QuintRecog4.lean`), which genuinely needs its domain's `GBR Γ a b c`
factor pre-split at `GBR.mk`, with the FIRST piece (`F_{b,c}`) homogeneous
(`E17M`'s own middle swap `gV7Swap` crosses it against `F_{d,e}`, needing
a definite Koszul sign). The identical obstruction recurs at the
`E21M`-after-`E14M` step of the BOTTOM route: `E14M`'s raw output (even
via the already-landed `E14M_general`, `QuintFaces2.lean`) is an opaque
`V9Inner`-element `gq4Close K Γ (a+b) c d e (RelTensor.mk ... w
(gTCanon K Γ (a+b) c (d+e) (RelTensor.mk ... v x)))`, not split as
`RelTensor.mk ... n p` — but `E21M`'s own first stage `gV9Swap` needs
EXACTLY that split (with `n : GBR Γ c d e` homogeneous) for a definite
sign.

This is a *categorical-coherence* gap, not a bookkeeping one: closing it
needs a genuinely NEW naturality fact relating `gTCanon K Γ a b c` to the
TWO DIFFERENT associators `gV6AssocA`/`gV7AssocA` (equivalently: a
"cross-bracketing" analogue of `QuintSquares.lean`'s
`assoc_comp_mapFirstOuter`, which only handles the case where BOTH sides
of the naturality square use the SAME bracketing of `GBL`/`GBR Γ a b c`,
e.g. `square_S1`'s `E20M ∘ E13M` — always `GBL`/`GBR Γ a b c` treated as
a single opaque outer factor, never split further). The one PROMISING
lead located: `gTCanon K Γ a b c` is a member of `gInterSpace K Γ a b c
(gParity K Γ a b c)` (`ChiCanon.lean`'s `gTCanon_mem_gInterSpace`), whose
THREE `superEquivariant` conjuncts include the `D_b`-slot
(`InterSpace.lean`'s `gInterSpace`, the middle letter — `gCanonRight`/
`gCanonHphi4`/`gCanonHphi5` only ever public-restate the `D_a`-adjacent
"right-semilinear" and shifted-quadruple conjuncts actually needed so
far; the plain `D_b`-slot conjunct has NEVER been publicly restated or
used anywhere in `GaugeChi`). Since `b` is the shared "middle" letter of
both `GBL`'s and `GBR`'s bracketings of `a,b,c`, `gTCanon`'s `D_b`-slot
equivariance is the natural candidate bridge — but turning it into a
working naturality square (a `smap_comp_mapFirst`/`map_comm_midEndFirst`
-style argument, `Quint.lean`, matched against `gV6AssocA`'s/
`gV7AssocA`'s own `(b+c)`/`(a+b)`-slot exposure) is substantial NEW
mathematical content, well beyond a "support lemma," and was not
attempted here given the round's time budget.

## What IS landed

`E20M_mk`: the `_mk`-unfolding lemma for edge 20 (the "easy first-slot
genre" the round's brief anticipated — `E20M` is *already* a bare
`RelTensor.map (gTCanon K Γ a b c) id`, no `GE_k`-wrapper, no sign, unlike
`QuintFaces.lean`'s `E1M_mk .. E10M_mk` which each unwrap one `GE_k`
layer first). Kept public for reuse by any future continuation.
-/
import Superfusion.GaugeChi.QuintRecog5

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

/-! ### `E20M_mk`: the missing `_mk`-unfolding lemma for edge 20 -/

/-- **`E20M_mk`**: `E20M`'s action on a `V6`-generator — `E20M` is already
a bare `RelTensor.map (gTCanon K Γ a b c) id` (no `GE_k`-wrapper, no
`GQ`-`Total` layer, `QuintEdges.lean`'s docstring calls this the
"S-adjacent, simplest genre"), so unlike `QuintFaces.lean`'s `E1M_mk ..
E10M_mk` (which each unwrap one `GE_k` layer via `show` before hitting
`RelTensor.map_mk`), this is a direct, UNSIGNED `RelTensor.map_mk`
computation — no homogeneity hypothesis needed on `m`. -/
theorem E20M_mk (m : GBL Γ a b c) (n : GBR Γ (a + b + c) d e) :
    E20M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e) m n)
      = RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
          (gTCanon K Γ a b c m) n := by
  show RelTensor.map (gTCanon K Γ a b c).toLinearMap LinearMap.id (gCanonRight K Γ a b c)
      (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e) m n) = _
  rw [RelTensor.map_mk]
  rfl

end GaugeChi

end Superfusion

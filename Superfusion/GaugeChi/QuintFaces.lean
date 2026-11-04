/-
Superfusion / GaugeChi / QuintFaces

Milestone M13-3b of the abstract `(p, χ)` arc (the K₅ chain, FACE phase):
**the two end-slot pentagon faces `face_P6`, `face_P1`** (`docs/m13-design.md`'s
ledger), built on the 14 vertex types (`Quint.lean`) and 21 edge maps
(`QuintEdges.lean` .. `QuintEdges8.lean`).

**`P6`** is the `K₄` pentagon at `(a,b,c,d)` (`ChiCanon.lean`'s
`gChiCanon_spec`) whiskered by the TRAILING letter `e` (the end slot):
`V1 = GQ1(a,b,c,d) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}`, .., `V5 = GQ4(a,b,c,d) ⊗
F_{a+b+c+d,e}`, and `E1M .. E5M` are each *literally* `RelTensor.map (-) id`
of the corresponding `K₄` pentagon edge map (`GE1 .. GE4`, `gq4Close ∘ GE5`)
at the SAME canonical `gTCanon`/`gt2Canon` data `gChiCanon_spec` uses — so
the whole face is a `RelTensor.map_mk` unfolding plus one pointwise
application of `gChiCanon_spec`, no assoc coherence needed at all (referee
correction 5: the end-slot faces need only this definitional factorization).

**`P1`** is the mirror at `(b,c,d,e)` whiskered by the LEADING letter `a`:
`V10 = GQ1(b,c,d,e) ⊗_{D_{b+c+d+e}} F_{a,b+c+d+e}`, .., `V14 = GQ4(b,c,d,e)
⊗ F_{a,b+c+d+e}`, `E6M .. E10M` the `V10..V14`-mirrors of `E1M .. E5M` at
the SAME canonical data instantiated at the quadruple `(b,c,d,e)`.

**Orientation** (referee-mandated, `docs/m13-design.md`'s referee
verification record, item 1): both faces are stated in `gChiCanon_spec`'s
OWN direction — the 3-edge route equals `gChiCanon` acting on the 2-edge
route (`gChiCanon_spec : gTopRoute = gChiCanon • gBotRoute`, TOP = 3-edge,
BOT = 2-edge) — NOT the design ledger's mirrored form (`docs/m13-design.md`
states `P6 : E5∘E4 = χ • (E3∘E2∘E1)`, 2-edge = χ • 3-edge; the mirroring is
uniform across all six pentagon faces and cancels at chain assembly, per
the referee record). Landed here:
* `face_P6 : E3M ∘ₗ E2M ∘ₗ E1M = gChiCanon K Γ a b c d • (E5M ∘ₗ E4M)`
  (`V1 → V5`; both routes land at `V5` on the nose — `E5M` already
  incorporates `gq4Close`, so no separate "close" map is needed at the
  `K₅` level, matching the ledger's edge table `E1:v1v2, E2:v2v4, E3:v4v5,
  E4:v1v3, E5:v3v5`).
* `face_P1 : E8M ∘ₗ E7M ∘ₗ E6M = gChiCanon K Γ b c d e • (E10M ∘ₗ E9M)`
  (`V10 → V14`; `E6:v10v11, E7:v11v13, E8:v13v14, E9:v10v12, E10:v12v14`).

**The recognition toolkit** (the bulk of the round, reused identically by
both faces — ONE simple genre suffices for the end-slot faces, no assoc
conjugators): `E1M_mk .. E10M_mk`, unfolding each edge's action on a
`RelTensor.mk m n` generator to `RelTensor.mk (innerEdgeMap m) n` — a
single `RelTensor.map_mk` computation each, since every `EkM` is *itself*
already `RelTensor.map (innerEdgeMap) id` by definition (`QuintEdges.lean`/
`QuintEdges2.lean`); landed and kept PUBLIC for reuse by the cluster faces
(`PAB`/`PBC`/`PCD`/`PDE`), even though the two face proofs below do not
call them directly (see next paragraph).

**The face proofs**: `RelTensor.hom_ext` reduces each face to one equation
at a generator `RelTensor.mk m n`; that goal is then closed by a SINGLE
`show`, jumping directly from `EkM (E(k-1)M (... (mk m n)))` to the fully
unfolded `RelTensor.mk (GE.. (GE.. (GE.. m))) n` form in one step (rather
than `rw`-ing through `E1M_mk .. E5M_mk` one at a time): `RelTensor.map f
id hf hg (mk m n) = mk (f m) n` is *definitionally* true (default
transparency unfolds `RelTensor.map`/`RelTensor.lift`/`Submodule.liftQ`
down to the `Quot.lift`-on-`Quot.mk` reduction, even though the library's
own `RelTensor.map_mk` states it via an explicit `rw [lift_mk]` for
robustness elsewhere), but `rw`ing `EkM_mk` *inside* a goal whose ambient
type is the `def`-wrapped vertex type `V_j` hits exactly the
`instances`-transparency motive-check trap `QuintEdges.lean`'s file
docstring records (the substituted term's ELABORATED type becomes the raw
`RelTensor K A M N` spelling, distinct from `V_j` at `rw`'s weaker
transparency) — `show` sidesteps it by using full defeq once, for the
whole composite, instead of `rw`'s per-step motive. After the `show`, one
`rw [← LinearMap.map_smul₂]` pulls `gChiCanon` inside the `mk`, and the
whole equation closes by `congrArg (mk · n)` applied to the pointwise
instance of `gChiCanon_spec` (`LinearMap.congr_fun`) at `m` — the
`gTopRoute`/`gBotRoute` compositions unfold definitionally to the same
`GE1 ∘ GE2 ∘ GE3`/`gq4Close ∘ GE5 ∘ GE4` chains the `show`'s target
carries (`gCanonRight`/`gCanonHphi4`/`gCanonHphi5` are public
re-statements of the exact `Prop`s `ChiCanon.lean`'s private
`canon_right`/`canon_hφ₄`/`canon_hφ₅` supply, hence definitionally equal
to them by proof irrelevance), so the whole recognition is a matter of
Lean's own defeq checker, no cluster-tier assoc/recast layer required.
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

variable (a b c d e : G)

/-! ### The ten `mk`-unfolding lemmas -/

theorem E1M_mk (m : GQ1 K Γ a b c d) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E1M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m n)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GE1 K Γ a b c d (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c) m) n := by
  show RelTensor.map (GE1 K Γ a b c d (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
      LinearMap.id (GE1_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E2M_mk (m : GQ2 K Γ a b c d) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E2M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m n)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
            (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
              (gTCanon_mem_gInterSpace K Γ a (b + c) d)) m) n := by
  show RelTensor.map (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
        (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
          (gTCanon_mem_gInterSpace K Γ a (b + c) d)))
      LinearMap.id (GE2_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E3M_mk (m : GQ3 K Γ a b c d) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E3M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m n)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ4 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GE3 K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d) m) n := by
  show RelTensor.map (GE3 K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
      LinearMap.id (GE3_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E4M_mk (m : GQ1 K Γ a b c d) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E4M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m n)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GE4 K Γ a b c d (gParity K Γ (a + b) c d)
            (gTCanon K Γ (a + b) c d).toLinearMap (gCanonHphi4 K Γ a b c d) m) n := by
  show RelTensor.map (GE4 K Γ a b c d (gParity K Γ (a + b) c d)
        (gTCanon K Γ (a + b) c d).toLinearMap (gCanonHphi4 K Γ a b c d))
      LinearMap.id (GE4_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E5M_mk (m : GQ5 K Γ a b c d) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E5M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m n)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ4 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (gq4Close K Γ a b c d
            (GE5 K Γ a b c d (gParity K Γ a b (c + d))
              (gTCanon K Γ a b (c + d)).toLinearMap (gCanonHphi5 K Γ a b c d) m)) n := by
  show RelTensor.map ((gq4Close K Γ a b c d).toLinearMap.comp
        (GE5 K Γ a b c d (gParity K Γ a b (c + d))
          (gTCanon K Γ a b (c + d)).toLinearMap (gCanonHphi5 K Γ a b c d)))
      LinearMap.id (E5MInner_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E6M_mk (m : GQ1 K Γ b c d e) (n : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E6M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m n)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ2 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GE1 K Γ b c d e (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d) m) n := by
  show RelTensor.map (GE1 K Γ b c d e (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
      LinearMap.id (GE1_rightTotal K Γ b c d e) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E7M_mk (m : GQ2 K Γ b c d e) (n : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E7M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ2 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m n)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GE2 K Γ b c d e (gParity K Γ b (c + d) e)
            (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e) (gParity K Γ b (c + d) e)
              (gTCanon_mem_gInterSpace K Γ b (c + d) e)) m) n := by
  show RelTensor.map (GE2 K Γ b c d e (gParity K Γ b (c + d) e)
        (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e) (gParity K Γ b (c + d) e)
          (gTCanon_mem_gInterSpace K Γ b (c + d) e)))
      LinearMap.id (GE2_rightTotal K Γ b c d e) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ2 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E8M_mk (m : GQ3 K Γ b c d e) (n : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E8M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m n)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GE3 K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e) m) n := by
  show RelTensor.map (GE3 K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e))
      LinearMap.id (GE3_rightTotal K Γ b c d e) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E9M_mk (m : GQ1 K Γ b c d e) (n : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E9M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m n)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GE4 K Γ b c d e (gParity K Γ (b + c) d e)
            (gTCanon K Γ (b + c) d e).toLinearMap (gCanonHphi4 K Γ b c d e) m) n := by
  show RelTensor.map (GE4 K Γ b c d e (gParity K Γ (b + c) d e)
        (gTCanon K Γ (b + c) d e).toLinearMap (gCanonHphi4 K Γ b c d e))
      LinearMap.id (GE4_rightTotal K Γ b c d e) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) m n) = _
  rw [RelTensor.map_mk]
  rfl

theorem E10M_mk (m : GQ5 K Γ b c d e) (n : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E10M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m n)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (gq4Close K Γ b c d e
            (GE5 K Γ b c d e (gParity K Γ b c (d + e))
              (gTCanon K Γ b c (d + e)).toLinearMap (gCanonHphi5 K Γ b c d e) m)) n := by
  show RelTensor.map ((gq4Close K Γ b c d e).toLinearMap.comp
        (GE5 K Γ b c d e (gParity K Γ b c (d + e))
          (gTCanon K Γ b c (d + e)).toLinearMap (gCanonHphi5 K Γ b c d e)))
      LinearMap.id (E5MInner_rightTotal K Γ b c d e) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) m n) = _
  rw [RelTensor.map_mk]
  rfl

/-! ### Face `P6`: the end-slot pentagon at `(a,b,c,d)`, whiskered by `e` -/

/-- **`face_P6`**: the `K₄` pentagon at `(a,b,c,d)` (`gChiCanon_spec`)
whiskered by the trailing letter `e`, in `gChiCanon_spec`'s OWN
orientation — the 3-edge route `E3M ∘ E2M ∘ E1M : V1 → V5` equals
`gChiCanon K Γ a b c d` acting on the 2-edge route `E5M ∘ E4M : V1 → V5`
(`E5M` already incorporates `gq4Close`, so both routes land at `V5` with
no further "close" needed at the `K₅` level). -/
theorem face_P6 :
    E3M K Γ a b c d e ∘ₗ E2M K Γ a b c d e ∘ₗ E1M K Γ a b c d e
      = gChiCanon K Γ a b c d • (E5M K Γ a b c d e ∘ₗ E4M K Γ a b c d e) := by
  refine RelTensor.hom_ext fun m n => ?_
  show RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ4 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (GE3 K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d)
          (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
            (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
              (gTCanon_mem_gInterSpace K Γ a (b + c) d))
            (GE1 K Γ a b c d (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c) m))) n
    = gChiCanon K Γ a b c d •
        RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ4 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (gq4Close K Γ a b c d
            (GE5 K Γ a b c d (gParity K Γ a b (c + d))
              (gTCanon K Γ a b (c + d)).toLinearMap (gCanonHphi5 K Γ a b c d)
              (GE4 K Γ a b c d (gParity K Γ (a + b) c d)
                (gTCanon K Γ (a + b) c d).toLinearMap (gCanonHphi4 K Γ a b c d) m))) n
  rw [← LinearMap.map_smul₂]
  exact congrArg (fun z => RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ4 K Γ a b c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e)) z n)
    (LinearMap.congr_fun (gChiCanon_spec K Γ a b c d) m)

/-! ### Face `P1`: the end-slot pentagon at `(b,c,d,e)`, whiskered by `a` -/

/-- **`face_P1`**: the `V10..V14`-mirror of `face_P6`, the `K₄` pentagon at
`(b,c,d,e)` whiskered by the LEADING letter `a` — same `gChiCanon_spec`,
instantiated at the quadruple `(b,c,d,e)`. -/
theorem face_P1 :
    E8M K Γ a b c d e ∘ₗ E7M K Γ a b c d e ∘ₗ E6M K Γ a b c d e
      = gChiCanon K Γ b c d e • (E10M K Γ a b c d e ∘ₗ E9M K Γ a b c d e) := by
  refine RelTensor.hom_ext fun m n => ?_
  show RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e)))
        (GE3 K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
          (GE2 K Γ b c d e (gParity K Γ b (c + d) e)
            (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e) (gParity K Γ b (c + d) e)
              (gTCanon_mem_gInterSpace K Γ b (c + d) e))
            (GE1 K Γ b c d e (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d) m))) n
    = gChiCanon K Γ b c d e •
        RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (gq4Close K Γ b c d e
            (GE5 K Γ b c d e (gParity K Γ b c (d + e))
              (gTCanon K Γ b c (d + e)).toLinearMap (gCanonHphi5 K Γ b c d e)
              (GE4 K Γ b c d e (gParity K Γ (b + c) d e)
                (gTCanon K Γ (b + c) d e).toLinearMap (gCanonHphi4 K Γ b c d e) m))) n
  rw [← LinearMap.map_smul₂]
  exact congrArg (fun z => RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e))) z n)
    (LinearMap.congr_fun (gChiCanon_spec K Γ b c d e) m)

end GaugeChi

end Superfusion

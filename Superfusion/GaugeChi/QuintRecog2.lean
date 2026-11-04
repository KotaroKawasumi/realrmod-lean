/-
Superfusion / GaugeChi / QuintRecog2

Milestone M13-4b of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase, continuing `GaugeChi.QuintRecog`'s form (B) program): **`E11M_leaf`**
— the recognition leaf lemma for the hardest `PAB` edge `E11M` (`V3 → V8`,
the move `t_{a+b,c+d,e}`, `QuintEdges4.lean`).

## The edge's four-letter identification

`E11M`'s route (`QuintEdges4.lean`'s `E11Mequiv`, five composed
equivalences `gV3AssocA`/`gV3AssocBC = gV3StepB.trans gV3StepC`/
`gE11InnerStep`/`gE11OuterStep`/`gE11FinalStep`) reassociates `V3` down to
expose `GBL(a+b,c+d,e)` through BOTH the `F_{a,b}` and `F_{c,d}` whiskers,
applies `gTCanon Γ (a+b) (c+d) e` through the nested `(a+b)`/`(c+d)`
mid-actions, and recasts onto `V8`'s fixed `F_{a,b} ⊗ (GBL(c,d,e) ⊗
F_{a+b,c+d+e})` shape.  Structurally this is `PentagonEdges.lean`'s `GE2`
(`GE2 t₂ = (id ⊗_signed t₂) ∘ gq2Assoc : GQ2 → GQ3`, generator formula
`mk (GBR.mk u v) w ↦ sgn(e·|u|) • mk u (t₂ (mk v w))`) instantiated at the
SHIFTED quadruple `(a+b,c,d,e)`, with `t₂ := gt2Canon K Γ (a+b) c d e
(gTCanon K Γ (a+b) (c+d) e)` — literally the intertwiner `φ₂` that
`gChiCanon_htop`/`gChiCanon_spec K Γ (a+b) c d e`'s `gTopRoute` uses at its
own second edge (`ChiCanon.lean`).  `E11M`'s own construction reaches
`gt2Canon`'s recast (`gq2rCast`) INSIDE `gV3StepC` (before the `gTCanon`
move) rather than folding it into a single `t₂`-application the way `GE2`
does, but `gt2Canon_mk` bridges the two spellings in one rewrite — the
leaf below states the target with `gt2Canon (gTCanon ...)` applied to the
UNCAST inner generator (`GQ2rInner`-shaped, `RelTensor.mk q w`), exactly
`GE2`'s own domain shape, so that round 4d's face assembly can chain this
leaf directly against `gChiCanon_spec K Γ (a+b) c d e` pointwise, matching
`E4M_leaf`/`E12M_leaf`'s own reinsertion conventions (`QuintRecog.lean`).

## The generator shape and the sign

A fully-decomposed homogeneous `V3`-generator is `t ⊗ (p ⊗ q) ⊗ w` (fully
left-nested per `V3 = GQ5(a,b,c,d) ⊗ F_{a+b+c+d,e}` and `GQ5 = F_{a,b} ⊗
GBR(a+b,c,d)`, `GBR(a+b,c,d) = F_{c,d} ⊗ F_{a+b,c+d}`): `t : F_{a,b}`
homogeneous of degree `i`, `p : F_{c,d}` homogeneous of degree `j` (BOTH
whisker degrees are needed, unlike `E4M_leaf`/`E13M_leaf`'s single
homogeneous slot — `E11M`'s route amplifies `gTCanon` through TWO nested
mid-actions, `(c+d)` first then `(a+b)`, each contributing its own
`sgn(gParity(a+b,c+d,e)·(-))` factor, which combine via `sgn_add` to the
single `sgn(gParity(a+b,c+d,e)·(i+j))` below), `q : F_{a+b,c+d}` and `w :
F_{a+b+c+d,e}` arbitrary.  The target lands in `V8 = F_{a,b} ⊗ V8Inner`,
`V8Inner = GBL(c,d,e) ⊗ F_{a+b,c+d+e}`, via `gE11GBRAssoc` (the plain,
UNSIGNED `RelTensor.assoc` closing `F_{c,d} ⊗ GBR(a+b,c+d,e)` onto
`V8Inner` — the pentagon-vertex-shape difference between `GE2`'s own
`GQ3`-style `F_{c,d} ⊗ GBR(a+b,c+d,e)` landing and `V8`'s
`GBL(c,d,e)`-style landing, NOT a further `GE`-edge move).

## Method

Chased through `E11M`'s five stages via their own already-public `_mk`
generator lemmas (`RelTensor.assoc_mk` for `gV3AssocA`/`gV3StepB`/
`gE11GBRAssoc`'s outer `mapEquivRight` shell, `gq2rCast_mk` for
`gV3StepC`'s inner cast, `smap_mk_of_mem` for `gE11InnerStep`/
`gE11OuterStep`'s two signed mid-action amplifications, `gt2Canon_mk` to
re-fold the cast into the `GE2`-genre `t₂`-application at the very end):
no new toolkit content, following `QuintRecog.lean`'s form (B) discipline
throughout (`show` + raw respelling before every `rw` across a
`def`-wrapped vertex type, `map_zsmul` for the ℤ-valued Koszul signs).
-/
import Superfusion.GaugeChi.QuintRecog

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

/-! ### `E11M_leaf`: the `PAB`-face leaf lemma for edge 11 (`V3 → V8`) -/

/-- **`E11M_leaf`**: `E11M`'s generator formula on a FULLY-DECOMPOSED
homogeneous generator of `V3` (`t : F_{a,b}` homogeneous of degree `i`,
`p : F_{c,d}` homogeneous of degree `j`, `q, w` arbitrary) — the `PAB`-face
leaf lemma for the hardest edge, `E11M`, chased through the five stages of
`E11Mequiv` (`QuintEdges4.lean`) via their own already-public generator
formulas.  The target's reinserted map `gt2Canon K Γ (a + b) c d e
(gTCanon K Γ (a + b) (c + d) e)` is literally the intertwiner
`gChiCanon_htop`/`gChiCanon_spec K Γ (a + b) c d e`'s `gTopRoute` uses at
its own second edge (`ChiCanon.lean`), so round 4d's face assembly can
chain this leaf directly against `gChiCanon_spec` pointwise. -/
theorem E11M_leaf {i j : ZMod 2} {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) i)
    {p : FusionColumn (Γ.fuse c d)} (hp : p ∈ FusionColumn.grading (Γ.fuse c d) j)
    (q : FusionColumn (Γ.fuse (a + b) (c + d))) (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E11M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) t
            (GBR.mk Γ (a + b) c d p q)) w)
      = ((sgn (gParity K Γ (a + b) (c + d) e * (i + j)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
            (gE11GBRAssoc K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (GBR Γ (a + b) (c + d) e) p
                (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)
                  (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (FusionColumn (Γ.fuse (a + b) (c + d))) (FusionColumn (Γ.fuse (a + b + c + d) e))
                    q w)))) := by
  show gE11FinalStep K Γ a b c d e
      (gE11OuterStep K Γ a b c d e
        (gV3AssocABC K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) t
              (GBR.mk Γ (a + b) c d p q)) w))) = _
  -- Stage 1a: `gV3AssocA`, the plain `RelTensor.assoc` exposing `F_{a,b}`.
  have hAssocA : gV3AssocA K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) t
          (GBR.mk Γ (a + b) c d p q)) w)
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))) t
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d p q) w) :=
    RelTensor.assoc_mk K (Γ.D (a + b)).carrier (Γ.D (a + b + c + d)).carrier
      (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
      t (GBR.mk Γ (a + b) c d p q) w
  -- Stage 1b: `gV3StepB`, the plain `RelTensor.assoc` exposing `F_{c,d}`.
  have hStepB : gV3StepB K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d p q) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e)
          p (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e)) q w) :=
    RelTensor.assoc_mk K (Γ.D (c + d)).carrier (Γ.D (a + b + c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (a + b) (c + d)))
      (FusionColumn (Γ.fuse (a + b + c + d) e)) p q w
  -- The cast element `w' : F_{(a+b)+(c+d),e}`, `gq2rCast`'s own second slot.
  let w' : FusionColumn (Γ.fuse (a + b + (c + d)) e) :=
    gColumnCastFst K Γ e (add_assoc (a + b) c d) w
  -- Stage 1c: `gV3StepC`, the cast `gq2rCast`, exposing `GBL(a+b,c+d,e)`.
  have hStepC : gV3StepC K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e)
        p (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e)) q w))
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) p
          (GBL.mk Γ (a + b) (c + d) e q w') := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K] FusionColumn (Γ.fuse c d))
        (gq2rCast K Γ (a + b) c d e).toLinearMap (fun _ _ => rfl)
        (gq2rCast_bcSlot K Γ (a + b) c d e)
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e)
          p (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e)) q w)) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    show RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) p
        (gq2rCast K Γ (a + b) c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e)) q w)) = _
    rw [gq2rCast_mk]
  -- Stages 1a–1c combined: `gV3AssocABC`'s value on the `V3`-generator.
  have hABC : gV3AssocABC K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) t
          (GBR.mk Γ (a + b) c d p q)) w)
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) t
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)
            p (GBL.mk Γ (a + b) (c + d) e q w')) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gV3AssocBC K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gV3AssocBC_aSlot_general K Γ a b c d e)
        (gV3AssocA K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) t
              (GBR.mk Γ (a + b) c d p q)) w)) = _
    rw [hAssocA, RelTensor.map_mk, LinearMap.id_apply]
    show RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) t
        (gV3StepC K Γ a b c d e
          (gV3StepB K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d p q) w))) = _
    rw [hStepB, hStepC]
  -- Stage 2 (inner): `gE11InnerStep`, the `(c+d)`-mid-slot signed move.
  have hInnerStep : gE11InnerStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) p
        (GBL.mk Γ (a + b) (c + d) e q w'))
      = ((sgn (gParity K Γ (a + b) (c + d) e * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)
            p (gTCanon K Γ (a + b) (c + d) e (GBL.mk Γ (a + b) (c + d) e q w')) := by
    show smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        (gTCanon K Γ (a + b) (c + d) e).toLinearMap (gParity K Γ (a + b) (c + d) e)
        (gCanonMidSlot K Γ (a + b) (c + d) e)
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) p
          (GBL.mk Γ (a + b) (c + d) e q w')) = _
    rw [smap_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      (gTCanon K Γ (a + b) (c + d) e).toLinearMap (gParity K Γ (a + b) (c + d) e)
      (gCanonMidSlot K Γ (a + b) (c + d) e) hp]
    rfl
  -- Stage 2 (outer): `gE11OuterStep`, the `(a+b)`-mid-slot signed wrap.
  have hOuterStep : gE11OuterStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) t
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) p
          (GBL.mk Γ (a + b) (c + d) e q w')))
      = ((sgn (gParity K Γ (a + b) (c + d) e * i) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e))
            t
            (gE11InnerStep K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (GBL Γ (a + b) (c + d) e) p (GBL.mk Γ (a + b) (c + d) e q w'))) := by
    show smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (gE11InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) (c + d) e)
        (gE11OuterHg K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) t
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)
            p (GBL.mk Γ (a + b) (c + d) e q w'))) = _
    rw [smap_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (gE11InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) (c + d) e)
      (gE11OuterHg K Γ a b c d e) ht]
    rfl
  -- Stages 1–2 combined, signs fused via `sgn_add`.
  have hOuterFull : gE11OuterStep K Γ a b c d e
      (gV3AssocABC K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) t
            (GBR.mk Γ (a + b) c d p q)) w))
      = ((sgn (gParity K Γ (a + b) (c + d) e * (i + j)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e))
            t
            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ (a + b) (c + d) e) p
              (gTCanon K Γ (a + b) (c + d) e (GBL.mk Γ (a + b) (c + d) e q w'))) := by
    rw [hABC, hOuterStep, hInnerStep, map_zsmul, smul_smul, ← Units.val_mul, ← sgn_add,
      show gParity K Γ (a + b) (c + d) e * i + gParity K Γ (a + b) (c + d) e * j
          = gParity K Γ (a + b) (c + d) e * (i + j) from by ring]
  -- Stage 3: `gE11FinalStep`, the plain `RelTensor.assoc` closing onto `V8Inner`.
  have hFinal : gE11FinalStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) t
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)
          p (gTCanon K Γ (a + b) (c + d) e (GBL.mk Γ (a + b) (c + d) e q w'))))
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
          (gE11GBRAssoc K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ (a + b) (c + d) e) p
              (gTCanon K Γ (a + b) (c + d) e (GBL.mk Γ (a + b) (c + d) e q w')))) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gE11GBRAssoc K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gE11GBRAssoc_aSlot_general K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) t
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)
            p (gTCanon K Γ (a + b) (c + d) e (GBL.mk Γ (a + b) (c + d) e q w')))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    rfl
  -- Re-fold `gq2rCast`+`gTCanon` into the single `GE2`-genre `gt2Canon` application.
  have hGt2 : gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) q w)
      = gTCanon K Γ (a + b) (c + d) e (GBL.mk Γ (a + b) (c + d) e q w') :=
    gt2Canon_mk K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e) q w
  rw [hOuterFull, map_zsmul, hFinal, ← hGt2]
  rfl

end GaugeChi

end Superfusion

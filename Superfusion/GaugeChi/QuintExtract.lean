/-
Superfusion / GaugeChi / QuintExtract

Milestone M13-R1 of the `(p, χ)` arc's CLUSTER-FACE phase, executing round
R1 of `docs/m13-cluster-route.md` (the referee-verified SPECTATOR-WHISKER
RECOGNITION ROUTE): the five `PDE` spectator-extraction equivalences
`omegaV6`/`omegaV7`/`omegaV9`/`omegaV12`/`omegaV14`, each landing the
face's spectator column `F_{d,e}` at the OUTER-LEFT position of the
corresponding vertex, `V_v ≃ₗ F_{d,e} ⊗_{D_{d+e}} GQ_k(a,b,c,d+e)` — built
only from already-landed gadgets (`Bimod.midSwap`, `RelTensor.assoc`,
`RelTensor.mapEquivRight`, `gq4Close⁻¹`, `gV12Assoc`), plus their
"fully split" generator leaves.

## What lands

* `omegaV6 : V6 ≃ₗ F_{d,e} ⊗ GQ1(a,b,c,d+e)` — a single `midSwap`
  (`M := GBL Γ a b c`), `omegaV6_mk_of_mem`.
* `omegaV7 : V7 ≃ₗ F_{d,e} ⊗ GQ2(a,b,c,d+e)` — the mirror, `M := GBR Γ a b c`,
  `omegaV7_mk_of_mem`.
* `omegaV9 : V9 ≃ₗ F_{d,e} ⊗ GQ5(a,b,c,d+e)` — `mapEquivRight
  (gq4Close (a+b) c d e).symm` then `midSwap`, `omegaV9_mk_of_mem`.
* `omegaV12 : V12 ≃ₗ F_{d,e} ⊗ GQ3(a,b,c,d+e)` — `gV12Assoc` then the
  `F_{b,c}`-whisker of `(gq4Close a (b+c) d e).symm` then `midSwap`,
  `omegaV12_mk_of_mem`.
* `omegaV14`: **NOT landed** — see the module-docstring finding below
  (the associativity obstruction), and the deviation record at the end
  of this file.

## THE GATE (R1's mandatory paper mk-ledger, §5 tripwire 1 check)

**(α) `recog_E21M`'s transport — `c+(d+e)` vs `c+d+e`.** `E21M_leaf`
(`QuintRecog5.lean:300-315`, confirmed by direct `#check` this session)
states its RHS through `gTCanon K Γ a b (c+d+e)` (i.e. through the
LEFT-associated argument `(a+b)+(c+d+e)`'s own THIRD slot spelled as the
literal group element `c+d+e`, which — as WRITTEN in `E21M_leaf`'s own
statement — is the term `c + d + e` reached via `gV14StepFinal`'s/
`gq3rCast`'s own construction, i.e. syntactically `(c+d)+e`). The spec's
own datum for the PDE face's bottom route (per `docs/m13-design.md`'s own
row and `gChiCanon_spec`'s orientation) is `gTCanon K Γ a b (c+(d+e))`
— note the DELIBERATE right-bracketing `c+(d+e)`, matching the fact that
`(d+e)` is the face's OWN shifted quadruple argument. The transport
between these two spellings of `gTCanon`'s third-slot argument is
`add_assoc c d e : c + d + e = c + (d + e)` (`Mathlib`, i.e. exactly the
group-element identity, NOT an argument-generator-level fact); composing
`gTCanon`'s own `Γ.gaugeCast`-based recast (available as `gCanonHphi5 K Γ
a b c (d + e)`, per the round brief, `QuintEdges.lean`) along this single
`add_assoc` rewrite reconciles `E21M_leaf`'s internal
`gTCanon K Γ a b (c + d + e)` with the spec's `gTCanon K Γ a b (c + (d+e))`
via `congrArg (gTCanon K Γ a b) (add_assoc c d e).symm` — REWRITING THE
GROUP-ELEMENT ARGUMENT of a single, fixed, opaque map (`gTCanon K Γ a b`
applied to different but EQUAL group elements); no generator of
`E21M_leaf`'s domain is touched, and no scalar or sign depends on which
spelling is used (the rewrite is along a `Prop`-valued group identity,
composed with the ALREADY-PUBLIC `gCanonHphi5`, entirely orthogonal to the
domain's own `(ju, jv, jw)` splitting). **VERDICT: no generator-dependent
residual — (α) is a clean `add_assoc`-transport, safe to schedule for R3.**

**(β) `recog_E10M`'s double-route cast check — the shared atom
`gTCanon K Γ b c (d+e)`.** Route 1 (`E10M`'s own definition,
`QuintEdges2.lean:1044-1054`, confirmed by `#check`): `E10M = RelTensor.map
((gq4Close K Γ b c d e).toLinearMap.comp (GE5 K Γ b c d e ... (gTCanon K Γ
b c (d+e)) ...)) id`, i.e. `gTCanon K Γ b c (d+e)`'s image is fed through
`GE5` (a `gq5Swap`-based intertwiner, `PentagonEdges.lean`) and THEN
`gq4Close K Γ b c d e` — landing directly in `V14`'s own OWN `GQ4 K Γ b c d
e`-shaped first factor. Route 2 (the composite recognition, via `ω12`/
`ω14`): `GE3`-at-`(a,b,c,d+e)` (the top route's third edge, closing
`gq3Assoc⁻¹` on `GQ3(a,b,c,d+e)`'s own generic construction) reaches the
SAME atom `gTCanon K Γ b c (d+e)` from `ω12`'s codomain `GQ3(a,b,c,d+e)`,
and the recognition's RHS composite passes it through `ω14` on the way
back down. **Both routes' only column recasts are `gq4Close K Γ b c d e`
(Route 1, applied directly) and `gq3Assoc`/`(gq4Close K Γ a (b+c) d e)`
(Route 2, inside `ω12`) plus — per THIS FILE's own finding below — an
UNAVOIDABLE THIRD recast bridging `GBR Γ b c (d+e)`'s `((b+c)+d)+e`-total
(the bracketing native to `V14`/`ω14`'s own construction, via
`gV14StepFinal`) against its `(b+c)+(d+e)`-total (the bracketing native to
`GQ3`/`GQ4`'s own generic 4th-argument definition, hence to `ω12`'s and
`GE3`'s own codomains) — i.e. a genuine `Γ.gaugeCast (add_assoc (b+c) d
e)`-shaped device, VERIFIED THIS SESSION to be a non-defeq gap (`(Γ.D (b +
c + d + e)).carrier` and `(Γ.D (b + c + (d + e))).carrier` do NOT `rfl`
against each other — checked directly). This cast is GENERATOR-INDEPENDENT
(it depends only on the group elements `b, c, d, e`, never on a domain
generator's own homogeneous splitting), so it is NOT itself a tripwire-1
violation, but it DOES mean `ω14` cannot be landed in the literal
`GQ4 K Γ a b c (d+e)`-spelled codomain the route doc's summary claimed
"cast-free" — see the finding below. **VERDICT: no generator-dependent
residual on EITHER route (both casts are pure group-element transports,
composing by path-irrelevance of `Γ.gaugeCast`/`fusionColumnCast`, which
are canonical `SuperAlgEquiv`/`LinearEquiv`s depending only on their
`Eq`-proof argument, hence equal for any two proofs of the same equation
by `Subsingleton`/proof irrelevance) — safe to schedule for R4, PROVIDED
`ω14` (or its consuming recognition `recog_E10M`) carries the one extra
`Γ.gaugeCast (add_assoc (b+c) d e)`-shaped recast explicitly.**

## Finding: `ω14` is NOT cast-free (a correction to the route doc)

The route doc's §2 "Type-level exactness" paragraph claims all five PDE
`ω`-codomains are cast-free, including `ω14 = assoc ∘ map (gq4Close K Γ b c
d e).symm id : V14 ≃ F_{d,e} ⊗ GQ4 K Γ a b c (d+e)`. Tracing this
construction literally: after `RelTensor.map (gq4Close K Γ b c d e).symm
id` and one `RelTensor.assoc`, the landing type's inner factor is
`RelTensor K (Γ.D (b+c+d+e)).carrier (GBR Γ b c (d+e)) (FusionColumn
(Γ.fuse a (b+c+d+e)))` — with algebra `Γ.D (b+c+d+e)`, i.e. the term
`((b+c)+d)+e` (V14's OWN native left-associated total, unchanged by `map`/
`assoc`, which never touch the surrounding algebra term). `GQ4 K Γ a b c
(d+e)`, by contrast, unfolds (substituting GQ4's own 4th parameter with
the compound term `d+e`) to algebra `Γ.D (b+c+(d+e))`, i.e. the term
`(b+c)+(d+e)` — a DIFFERENT (though `add_assoc`-equal) term. Checked
directly this session (`(Γ.D (b + c + d + e)).carrier = (Γ.D (b + c + (d +
e))).carrier` FAILS `rfl`), confirming these are genuinely different
Lean types, not merely different instances on the same type — reaching
`GQ4 K Γ a b c (d+e)` literally therefore needs an actual
`Γ.gaugeCast`-based recast (mirroring `GQ4.instModuleRightRecast`/
`gq4Recast`'s own pattern, but one level of nesting deeper than either),
which is NOT among the already-landed devices. Per the round brief's own
fallback clause ("if you hit a cast, re-check your spelling before
inventing a device; the fallback ... is the pure-assoc W-variant spelling
for the affected ω"): `ω14` is left UNLANDED this round rather than
inventing the new cast device under this round's budget; `omegaV12`
(`priority` list's final entry) is landed instead (its own `gV12Assoc`/
`instModuleE17GBRBCSlot` toolkit was built PRECISELY to avoid the analogous
gap, per `QuintEdges7.lean`'s own docstring). `ω14`'s construction, and the
one extra recast it needs, is recorded above (gate (β)) for the round that
schedules it (R1's own fallback authorizes deferring it; `recog_E10M`
(R4) already anticipates absorbing this exact cast).
-/
import Superfusion.GaugeChi.QuintSquares2
import Superfusion.GaugeChi.QuintCross

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d e : G)

attribute [local instance 500] leftModule rightModule

/-! ### `omegaV6 : V6 ≃ₗ F_{d,e} ⊗ GQ1(a,b,c,d+e)` -/

section OmegaV6

/-- `inferInstanceAs` bridge: `GQ1 K Γ a b c (d+e)`'s own `dslot` action
(PentagonActions' literal instance, at the shifted 4th argument), in the
raw `RelTensor` spelling `midSwap` needs. -/
noncomputable instance instModuleOmegaV6GQ1DSlot :
    Module (Γ.D (d + e)).carrier
      (GBL Γ a b c ⊗[(Γ.D (a + b + c)).carrier;K] FusionColumn (Γ.fuse (a + b + c) (d + e))) :=
  inferInstanceAs (Module (Γ.D (d + e)).carrier (GQ1 K Γ a b c (d + e)))

/-- The `D_{a+b+c}`-slot sign law on `GBR (a+b+c) d e` (`GBR`'s own
`aslot` pattern, mirroring `gV7LawA`). -/
private theorem omegaV6LawA :
    MidSignLaw K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (a + b + c)).grading (FusionColumn.grading (Γ.fuse d e)) := by
  intro l i x hx n hn p
  exact GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b + c) (b := d) (c := e) hx hn p

/-- The `D_{d+e}`-slot sign law on `M ⊗[A] P = GQ1 K Γ a b c (d+e)`
(`GQ1`'s own `dslot` pattern, at the shifted 4th argument `d+e`). -/
private theorem omegaV6LawB :
    MidSignLaw K (Γ.D (d + e)).carrier (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (d + e)).grading (GBL.grading Γ a b c) := by
  intro l i t ht u hu p
  exact GQ1.dslot_smul_mk_of_mem K Γ a b c (d + e) ht hu p

/-- **`omegaV6`**: a single `midSwap` (`M := GBL Γ a b c`), exposing the
`PDE` face's spectator column `F_{d,e}` at the outer-left position of
`V6`, landing the literal, cast-free `GQ1 K Γ a b c (d+e)`. -/
noncomputable def omegaV6 : V6 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ1 K Γ a b c (d + e)) :=
  midSwap K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (GBL Γ a b c)
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse (a + b + c) (d + e)))
    (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (GBL.grading Γ a b c) (FusionColumn.grading (Γ.fuse d e))
    (omegaV6LawA K Γ a b c d e) (omegaV6LawB K Γ a b c d e)

/-- **The sign law of `omegaV6` on homogeneous generators.** -/
theorem omegaV6_mk_of_mem {jm jw : ZMod 2} {m : GBL Γ a b c}
    (hm : m ∈ GBL.grading Γ a b c jm) {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (p : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    omegaV6 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e) m
          (GBR.mk Γ (a + b + c) d e w p))
      = ((sgn (jw * jm) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ1 K Γ a b c (d + e)) w
            (GQ1.mk K Γ a b c (d + e) m p) :=
  midSwap_mk_of_mem K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (GBL Γ a b c)
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse (a + b + c) (d + e)))
    (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (GBL.grading Γ a b c) (FusionColumn.grading (Γ.fuse d e))
    (omegaV6LawA K Γ a b c d e) (omegaV6LawB K Γ a b c d e) hw hm p

end OmegaV6

/-! ### `omegaV7 : V7 ≃ₗ F_{d,e} ⊗ GQ2(a,b,c,d+e)` -/

section OmegaV7

/-- `inferInstanceAs` bridge: `GQ2 K Γ a b c (d+e)`'s own `dslot` action,
in the raw `RelTensor` spelling `midSwap` needs. -/
noncomputable instance instModuleOmegaV7GQ2DSlot :
    Module (Γ.D (d + e)).carrier
      (GBR Γ a b c ⊗[(Γ.D (a + b + c)).carrier;K] FusionColumn (Γ.fuse (a + b + c) (d + e))) :=
  inferInstanceAs (Module (Γ.D (d + e)).carrier (GQ2 K Γ a b c (d + e)))

/-- The `D_{a+b+c}`-slot sign law on `GBR (a+b+c) d e` (mirroring
`omegaV6LawA`). -/
private theorem omegaV7LawA :
    MidSignLaw K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (a + b + c)).grading (FusionColumn.grading (Γ.fuse d e)) := by
  intro l i x hx n hn p
  exact GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b + c) (b := d) (c := e) hx hn p

/-- The `D_{d+e}`-slot sign law on `M ⊗[A] P = GQ2 K Γ a b c (d+e)`
(`GQ2`'s own `dslot` pattern). -/
private theorem omegaV7LawB :
    MidSignLaw K (Γ.D (d + e)).carrier (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (d + e)).grading (GBR.grading Γ a b c) := by
  intro l i t ht u hu p
  exact GQ2.dslot_smul_mk_of_mem K Γ a b c (d + e) ht hu p

/-- **`omegaV7`**: the mirror of `omegaV6`, `M := GBR Γ a b c`, landing the
literal, cast-free `GQ2 K Γ a b c (d+e)`. -/
noncomputable def omegaV7 : V7 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ2 K Γ a b c (d + e)) :=
  midSwap K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (GBR Γ a b c)
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse (a + b + c) (d + e)))
    (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (GBR.grading Γ a b c) (FusionColumn.grading (Γ.fuse d e))
    (omegaV7LawA K Γ a b c d e) (omegaV7LawB K Γ a b c d e)

/-- **The sign law of `omegaV7` on homogeneous generators.** -/
theorem omegaV7_mk_of_mem {jm jw : ZMod 2} {m : GBR Γ a b c}
    (hm : m ∈ GBR.grading Γ a b c jm) {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (p : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    omegaV7 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e) m
          (GBR.mk Γ (a + b + c) d e w p))
      = ((sgn (jw * jm) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ2 K Γ a b c (d + e)) w
            (GQ2.mk K Γ a b c (d + e) m p) :=
  midSwap_mk_of_mem K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (GBR Γ a b c)
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse (a + b + c) (d + e)))
    (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (GBR.grading Γ a b c) (FusionColumn.grading (Γ.fuse d e))
    (omegaV7LawA K Γ a b c d e) (omegaV7LawB K Γ a b c d e) hw hm p

end OmegaV7

/-! ### `omegaV9 : V9 ≃ₗ F_{d,e} ⊗ GQ5(a,b,c,d+e)` -/

section OmegaV9

/-- **`gq4Close`'s `a`-slot transport, generalized off homogeneity**: the
sign-free `GQ4Close.comp_aslot_univ` extended from homogeneous `x` to all
`x`, by `Decomposition`-induction (the RHS/LHS are both linear in `x` with
no sign correction, so additivity over `x`'s grading pieces suffices). -/
private theorem omegaV9_gq4Close_aslot_general
    (x : (Γ.D (a + b)).carrier) (n : GQ4r K Γ (a + b) c d e) :
    gq4Close K Γ (a + b) c d e (x • n) = x • gq4Close K Γ (a + b) c d e n := by
  induction x using DirectSum.Decomposition.inductionOn (Γ.D (a + b)).grading with
  | zero => simp only [zero_smul, map_zero]
  | add x x' hx hx' => simp only [add_smul, map_add, hx, hx']
  | homogeneous x => exact GQ4Close.comp_aslot_univ K Γ (a + b) c d e x.2 n

/-- `inferInstanceAs` bridge: `GQ4r K Γ (a+b) c d e`'s own `aslot` action,
in the raw `RelTensor` spelling `midSwap` needs. -/
noncomputable instance instModuleOmegaV9GQ4rASlot :
    Module (Γ.D (a + b)).carrier
      (FusionColumn (Γ.fuse d e) ⊗[(Γ.D (d + e)).carrier;K] GBR Γ (a + b) c (d + e)) :=
  inferInstanceAs (Module (Γ.D (a + b)).carrier (GQ4r K Γ (a + b) c d e))

/-- `inferInstanceAs` bridge: `GQ5 K Γ a b c (d+e)`'s own `dslot` action,
in the raw `RelTensor` spelling `midSwap` needs. -/
noncomputable instance instModuleOmegaV9GQ5DSlot :
    Module (Γ.D (d + e)).carrier
      (FusionColumn (Γ.fuse a b) ⊗[(Γ.D (a + b)).carrier;K] GBR Γ (a + b) c (d + e)) :=
  inferInstanceAs (Module (Γ.D (d + e)).carrier (GQ5 K Γ a b c (d + e)))

/-- The `D_{a+b}`-slot sign law on `N ⊗[B] P = GQ4r K Γ (a+b) c d e`
(`GQ4r`'s own `aslot` pattern, at the shifted 1st argument `a+b`). -/
private theorem omegaV9LawA :
    MidSignLaw K (Γ.D (a + b)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GBR Γ (a + b) c (d + e))
      (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse d e)) := by
  intro l i x hx n hn p
  exact GQ4r.aslot_smul_mk_of_mem K Γ (a + b) c d e hx hn p

/-- The `D_{d+e}`-slot sign law on `M ⊗[A] P = GQ5 K Γ a b c (d+e)`
(`GQ5`'s own `dslot` pattern). -/
private theorem omegaV9LawB :
    MidSignLaw K (Γ.D (d + e)).carrier (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (GBR Γ (a + b) c (d + e))
      (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse a b)) := by
  intro l i t ht u hu p
  exact GQ5.dslot_smul_mk_of_mem K Γ a b c (d + e) ht hu p

/-- **`omegaV9`**: `mapEquivRight (gq4Close K Γ (a+b) c d e).symm` (closing
`V9Inner`'s literal `GQ4 K Γ (a+b) c d e` into `GQ4r`, exposing `F_{d,e}`)
then a single `midSwap`, landing the literal, cast-free
`GQ5 K Γ a b c (d+e)`. -/
noncomputable def omegaV9 : V9 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ5 K Γ a b c (d + e)) :=
  (RelTensor.mapEquivRight K (gq4Close K Γ (a + b) c d e).symm
      (leftEquivariant_symm K (gq4Close K Γ (a + b) c d e)
        (omegaV9_gq4Close_aslot_general K Γ a b c d e))).trans
    (midSwap K (Γ.D (a + b)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
      (Γ.D (a + b)).grading (Γ.D (d + e)).grading
      (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse d e))
      (omegaV9LawA K Γ a b c d e) (omegaV9LawB K Γ a b c d e))

/-- The raw `GQ4 K Γ (a+b) c d e`-value produced by `gq4Close`,
respelled ONCE at `V9Inner`'s own (defeq) type as a top-level `def` — the
`QuintFaces3` "auxiliary raw-domain relocation" discipline, avoiding the
`have`-wrapped coercion artifact a bare `show ... from ...` term produces
inline (which defeats `rw`'s pattern matching). -/
private noncomputable def omegaV9Gen (w : FusionColumn (Γ.fuse d e))
    (p : GBR Γ (a + b) c (d + e)) : V9Inner K Γ a b c d e :=
  (gq4Close K Γ (a + b) c d e) (GQ4r.mk K Γ (a + b) c d e w p)

private theorem omegaV9Gen_eq (w : FusionColumn (Γ.fuse d e)) (p : GBR Γ (a + b) c (d + e)) :
    omegaV9Gen K Γ a b c d e w p
      = (gq4Close K Γ (a + b) c d e) (GQ4r.mk K Γ (a + b) c d e w p) :=
  rfl

/-- `omegaV9`'s `mapEquivRight`-stage, GENERIC in the (already
`V9Inner`-typed) second slot `n` — avoids re-elaborating a fresh
`gq4Close`-shaped term at `V9Inner`'s type (which fails, per the
instances-transparency trap), by keeping `n` an abstract bound variable
throughout. -/
private theorem omegaV9_mapEquivRight_mk (u : FusionColumn (Γ.fuse a b))
    (n : V9Inner K Γ a b c d e) :
    (RelTensor.mapEquivRight K (gq4Close K Γ (a + b) c d e).symm
        (leftEquivariant_symm K (gq4Close K Γ (a + b) c d e)
          (omegaV9_gq4Close_aslot_general K Γ a b c d e)))
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (V9Inner K Γ a b c d e) u n)
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (GQ4r K Γ (a + b) c d e) u ((gq4Close K Γ (a + b) c d e).symm n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
    ((gq4Close K Γ (a + b) c d e).symm.toLinearMap) (fun _ _ => rfl)
    (leftEquivariant_symm K (gq4Close K Γ (a + b) c d e)
      (omegaV9_gq4Close_aslot_general K Γ a b c d e)) u n

/-- **The sign law of `omegaV9` on fully split generators.** -/
theorem omegaV9_mk_of_mem {ju jw : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju) {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw) (p : GBR Γ (a + b) c (d + e)) :
    omegaV9 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V9Inner K Γ a b c d e) u (omegaV9Gen K Γ a b c d e w p))
      = ((sgn (jw * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ5 K Γ a b c (d + e)) w (GQ5.mk K Γ a b c (d + e) u p) := by
  have step1 :
      (RelTensor.mapEquivRight K (gq4Close K Γ (a + b) c d e).symm
          (leftEquivariant_symm K (gq4Close K Γ (a + b) c d e)
            (omegaV9_gq4Close_aslot_general K Γ a b c d e)))
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V9Inner K Γ a b c d e) u (omegaV9Gen K Γ a b c d e w p))
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (GQ4r K Γ (a + b) c d e) u (GQ4r.mk K Γ (a + b) c d e w p) := by
    rw [omegaV9_mapEquivRight_mk, omegaV9Gen_eq, LinearEquiv.symm_apply_apply]
  show midSwap K (Γ.D (a + b)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
      (Γ.D (a + b)).grading (Γ.D (d + e)).grading
      (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse d e))
      (omegaV9LawA K Γ a b c d e) (omegaV9LawB K Γ a b c d e)
      (RelTensor.mapEquivRight K (gq4Close K Γ (a + b) c d e).symm
          (leftEquivariant_symm K (gq4Close K Γ (a + b) c d e)
            (omegaV9_gq4Close_aslot_general K Γ a b c d e))
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V9Inner K Γ a b c d e) u (omegaV9Gen K Γ a b c d e w p))) = _
  rw [step1]
  exact midSwapMap_mk_of_mem K (Γ.D (a + b)).carrier (Γ.D (d + e)).carrier
    (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
    (Γ.D (a + b)).grading (Γ.D (d + e)).grading
    (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse d e))
    (omegaV9LawA K Γ a b c d e) (omegaV9LawB K Γ a b c d e) hw hu p

end OmegaV9

/-! ### `omegaV12 : V12 ≃ₗ F_{d,e} ⊗ GQ3(a,b,c,d+e)` -/

section OmegaV12

/-- **`gq4Close`'s `b`-slot transport, generalized off homogeneity**
(mirrors `omegaV9_gq4Close_aslot_general`). -/
private theorem omegaV12_gq4Close_bslot_general
    (x : (Γ.D (b + c)).carrier) (n : GQ4r K Γ a (b + c) d e) :
    gq4Close K Γ a (b + c) d e (x • n) = x • gq4Close K Γ a (b + c) d e n := by
  induction x using DirectSum.Decomposition.inductionOn (Γ.D (b + c)).grading with
  | zero => simp only [zero_smul, map_zero]
  | add x x' hx hx' => simp only [add_smul, map_add, hx, hx']
  | homogeneous x => exact GQ4Close.comp_bslot_univ K Γ a (b + c) d e x.2 n

/-- `inferInstanceAs` bridge: `GQ3 K Γ a b c (d+e)`'s own `dslot` action,
in the raw `RelTensor` spelling `midSwap` needs. -/
noncomputable instance instModuleOmegaV12GQ3DSlot :
    Module (Γ.D (d + e)).carrier
      (FusionColumn (Γ.fuse b c) ⊗[(Γ.D (b + c)).carrier;K] GBR Γ a (b + c) (d + e)) :=
  inferInstanceAs (Module (Γ.D (d + e)).carrier (GQ3 K Γ a b c (d + e)))

/-- The `D_{b+c}`-slot sign law on `N ⊗[B] P = GQ4r K Γ a (b+c) d e`
(`GQ4r`'s own `bslot` pattern, at the shifted 2nd argument `b+c`). -/
private theorem omegaV12LawA :
    MidSignLaw K (Γ.D (b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GBR Γ a (b + c) (d + e))
      (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse d e)) := by
  intro l i x hx n hn p
  exact GQ4r.bslot_smul_mk_of_mem K Γ a (b + c) d e hx hn p

/-- The `D_{d+e}`-slot sign law on `M ⊗[A] P = GQ3 K Γ a b c (d+e)`
(`GQ3`'s own `dslot` pattern). -/
private theorem omegaV12LawB :
    MidSignLaw K (Γ.D (d + e)).carrier (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (GBR Γ a (b + c) (d + e))
      (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse b c)) := by
  intro l i t ht u hu p
  exact GQ3.dslot_smul_mk_of_mem K Γ a b c (d + e) ht hu p

/-- **`omegaV12`**: `gV12Assoc` (exposing `F_{b,c} ⊗ GQ4(a,b+c,d,e)`) then
`mapEquivRight (gq4Close K Γ a (b+c) d e).symm` (closing `GQ4` into
`GQ4r`, exposing `F_{d,e}`) then a single `midSwap`, landing the literal,
cast-free `GQ3 K Γ a b c (d+e)`. -/
noncomputable def omegaV12 : V12 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ3 K Γ a b c (d + e)) :=
  ((gV12Assoc K Γ a b c d e).trans
      (RelTensor.mapEquivRight K (gq4Close K Γ a (b + c) d e).symm
        (leftEquivariant_symm K (gq4Close K Γ a (b + c) d e)
          (omegaV12_gq4Close_bslot_general K Γ a b c d e)))).trans
    (midSwap K (Γ.D (b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
      (Γ.D (b + c)).grading (Γ.D (d + e)).grading
      (FusionColumn.grading (Γ.fuse b c)) (FusionColumn.grading (Γ.fuse d e))
      (omegaV12LawA K Γ a b c d e) (omegaV12LawB K Γ a b c d e))

/-- `omegaV12`'s `mapEquivRight`-stage, GENERIC in the second slot `n`
(mirrors `omegaV9_mapEquivRight_mk`). -/
private theorem omegaV12_mapEquivRight_mk (u : FusionColumn (Γ.fuse b c))
    (n : GQ4 K Γ a (b + c) d e) :
    (RelTensor.mapEquivRight K (gq4Close K Γ a (b + c) d e).symm
        (leftEquivariant_symm K (gq4Close K Γ a (b + c) d e)
          (omegaV12_gq4Close_bslot_general K Γ a b c d e)))
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (GQ4 K Γ a (b + c) d e) u n)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (GQ4r K Γ a (b + c) d e) u ((gq4Close K Γ a (b + c) d e).symm n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse b c))
    ((gq4Close K Γ a (b + c) d e).symm.toLinearMap) (fun _ _ => rfl)
    (leftEquivariant_symm K (gq4Close K Γ a (b + c) d e)
      (omegaV12_gq4Close_bslot_general K Γ a b c d e)) u n

/-- **The sign law of `omegaV12` on fully split generators.** -/
theorem omegaV12_mk_of_mem {ju jw : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju) {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw) (p : GBR Γ a (b + c) (d + e)) :
    omegaV12 K Γ a b c d e
        ((gV12Assoc K Γ a b c d e).symm
          (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
            (GQ4 K Γ a (b + c) d e) u
            ((gq4Close K Γ a (b + c) d e) (GQ4r.mk K Γ a (b + c) d e w p))))
      = ((sgn (jw * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ3 K Γ a b c (d + e)) w (GQ3.mk K Γ a b c (d + e) u p) := by
  have step1 :
      (RelTensor.mapEquivRight K (gq4Close K Γ a (b + c) d e).symm
          (leftEquivariant_symm K (gq4Close K Γ a (b + c) d e)
            (omegaV12_gq4Close_bslot_general K Γ a b c d e)))
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (GQ4 K Γ a (b + c) d e) u
          ((gq4Close K Γ a (b + c) d e) (GQ4r.mk K Γ a (b + c) d e w p)))
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (GQ4r K Γ a (b + c) d e) u (GQ4r.mk K Γ a (b + c) d e w p) := by
    rw [omegaV12_mapEquivRight_mk, LinearEquiv.symm_apply_apply]
  show midSwap K (Γ.D (b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
      (Γ.D (b + c)).grading (Γ.D (d + e)).grading
      (FusionColumn.grading (Γ.fuse b c)) (FusionColumn.grading (Γ.fuse d e))
      (omegaV12LawA K Γ a b c d e) (omegaV12LawB K Γ a b c d e)
      ((RelTensor.mapEquivRight K (gq4Close K Γ a (b + c) d e).symm
          (leftEquivariant_symm K (gq4Close K Γ a (b + c) d e)
            (omegaV12_gq4Close_bslot_general K Γ a b c d e)))
        ((gV12Assoc K Γ a b c d e)
          ((gV12Assoc K Γ a b c d e).symm
            (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ4 K Γ a (b + c) d e) u
              ((gq4Close K Γ a (b + c) d e) (GQ4r.mk K Γ a (b + c) d e w p)))))) = _
  rw [LinearEquiv.apply_symm_apply, step1]
  exact midSwapMap_mk_of_mem K (Γ.D (b + c)).carrier (Γ.D (d + e)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
    (Γ.D (b + c)).grading (Γ.D (d + e)).grading
    (FusionColumn.grading (Γ.fuse b c)) (FusionColumn.grading (Γ.fuse d e))
    (omegaV12LawA K Γ a b c d e) (omegaV12LawB K Γ a b c d e) hw hu p

end OmegaV12

end GaugeChi

end Superfusion

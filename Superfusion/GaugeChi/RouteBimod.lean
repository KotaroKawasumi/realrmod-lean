/-
Superfusion / GaugeChi / RouteBimod

Milestone M12-1 of the abstract `(p, χ)` track: **the gauge route bimodules** — the
`DivisionFusionGauge`-mirror of `Superfusion.Bimod.RouteBimod`, over the skeletal data
`(G, D_a, F_{a,b})` of a general division fusion gauge `Γ : DivisionFusionGauge K G`
(`Superfusion.Gauge.FusionGauge`).

For `a b c : G`, the paper's two iterated fusions of §4.1,

  `GBL Γ a b c = F_{a,b} ⊗_{D_{a+b}} F_{a+b,c}`,
  `GBR Γ a b c = F_{b,c} ⊗_{D_{b+c}} F_{a,b+c}`,

are built as balanced tensor products (`Bimod.RelTensor`) of the fusion columns
`Bimod.FusionColumn (Γ.fuse a b)` (M11-1) — the Γ-mirror of `Bimod.TowerColumn` — with their
full super-bimodule structure:

* the balancing action is the matching slot action of the second column (the `(a+b)`-slot of
  `F_{a+b,c}` for `GBL`, the `(b+c)`-slot of `F_{a,b+c}` for `GBR` — both supplied verbatim by
  `Bimod.FusionColumn`'s `Slots` section, M11-1's `instModuleSlotLeft`/`instModuleSlotRight`) vs.
  the right coefficient action of the first column;
* the three **slot actions** of `D_a`, `D_b`, `D_c`: two through the outer left action on the
  first column, one through the Koszul-signed middle action (`Bimod.midAlgHom`) on the second —
  with the supercommutation supplied by `Bimod.FusionColumn.superCommSMul` (M11-1, itself a
  corollary of `Bimod.GtensorSlots.superCommSMul_of_algHom`), and its swap
  `Bimod.superCommSMul_symm` for `GBR`, where the middle algebra is `D_a`;
* the right action of the total coefficient algebra;
* the descended grading (`Bimod.relGrading`) with its decomposition.

`GBR`'s natural right coefficient tower is `D_{a+(b+c)}`; §4.4 of the routes ultimately compares
it against `GBL`'s `D_{(a+b)+c}` — for an abstract `[AddGroup G]` these are two *distinct* terms
(unlike `ZMod 8`'s literal-parse coincidences), so a second right-action instance is registered on
`GBR`, pulled back along the gauge-index cast `Γ.gaugeCast (add_assoc a b c) : SuperAlgEquiv
(Γ.D (a + b + c)) (Γ.D (a + (b + c)))` (`Superfusion.Gauge.GaugeRoutes`, M9-3a) — the Γ-mirror of
`Bimod.RouteRecast`'s M8a-8c′-0 device, `BR`'s recast along `stdTowerCast`.

Every instance in this file is assembled *verbatim* from `FusionColumn`'s already-general `General`
and `Slots` sections (M11-1) and the already-general `Bimod.OuterActions`/`Bimod.MiddleActionHom`
machinery (M8a-4a/M8a-7b) — no new algebraic content beyond `RouteBimod`'s was needed to reach a
general `[AddGroup G]`; this file is purely the Γ-level assembly.

At `Γ = bwGauge` (`Superfusion.Wedderburn.BWGauge`) or a `ZMod 8`-valued gauge reproducing
`stdTower`/`stdFuse` (the `Superfusion.Super.TowerStd` skeleton), `GBL`/`GBR` specialize to
`Bimod.bwColumn`-built route bimodules and to `Bimod.BL`/`Bimod.BR` respectively — the fusion
routes of the skeletal data `(G, D_a, F_{a,b})`, now available over an arbitrary division fusion
gauge.
-/
import Superfusion.Wedderburn.FusionColumn
import Superfusion.Bimod.RouteBimod

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

/-! ### The left route `GBL` -/

/-- **`GBL Γ a b c = F_{a,b} ⊗_{D_{a+b}} F_{a+b,c}`** (§4.1): the left iterated fusion route of
the skeletal data `(G, D_a, F_{a,b})`, balanced over the `(a+b)`-slot of the second fusion
column. The Γ-mirror of `Bimod.BL`. -/
def GBL : Type _ :=
  RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c))

namespace GBL

noncomputable instance : AddCommGroup (GBL Γ a b c) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c))))

noncomputable instance : Module K (GBL Γ a b c) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c))))

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse (a + b) c) →ₗ[K] GBL Γ a b c :=
  RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse (a + b) c))

/-- The descended grading of `GBL`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GBL Γ a b c) :=
  relGrading (Γ.D (a + b)).carrier (FusionColumn.grading (Γ.fuse a b))
    (FusionColumn.grading (Γ.fuse (a + b) c))

noncomputable instance : DirectSum.Decomposition (grading Γ a b c) :=
  relDecomposition (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    (FusionColumn.grading (Γ.fuse (a + b) c))

theorem mk_mem_grading {j k : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    {v : FusionColumn (Γ.fuse (a + b) c)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) k) :
    mk Γ a b c u v ∈ grading Γ a b c (j + k) :=
  mk_mem_relGrading (A := (Γ.D (a + b)).carrier)
    (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse (a + b) c)) hu hv

/-! #### The three slot actions and the right action -/

/-- The `D_a`-slot action (through the first fusion column). -/
noncomputable instance : Module (Γ.D a).carrier (GBL Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)))
    ((leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) (B := (Γ.D a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (Γ.D a).carrier) (u : FusionColumn (Γ.fuse a b))
    (v : FusionColumn (Γ.fuse (a + b) c)) :
    x • mk Γ a b c u v = mk Γ a b c (x • u) v :=
  leftActionEnd_mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse (a + b) c)) x u v

/-- The `D_b`-slot action (through the first fusion column). -/
noncomputable instance : Module (Γ.D b).carrier (GBL Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)))
    ((leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) (B := (Γ.D b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (Γ.D b).carrier) (u : FusionColumn (Γ.fuse a b))
    (v : FusionColumn (Γ.fuse (a + b) c)) :
    y • mk Γ a b c u v = mk Γ a b c (y • u) v :=
  leftActionEnd_mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse (a + b) c)) y u v

/-- The `D_c`-slot action: the Koszul-signed middle action through the second fusion column. -/
noncomputable instance : Module (Γ.D c).carrier (GBL Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)))
    ((midAlgHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) c))).toRingHom)

/-- **The sign law of the middle slot** (the handoff convention): for homogeneous `z`, `u`,
`z • (u ⊗ v) = (-1)^{|z||u|} u ⊗ (z • v)`. -/
theorem cslot_smul_mk_of_mem {j k : ZMod 2} {z : (Γ.D c).carrier} (hz : z ∈ (Γ.D c).grading k)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) :
    z • mk Γ a b c u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk Γ a b c u (z • v) :=
  midEnd_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
    (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) hu hz v

/-- The right action of the total coefficient algebra `D_{(a+b)+c}`. -/
noncomputable instance : Module ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)))
    ((rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) (C := (Γ.D (a + b + c)).carrier)).toRingHom)

theorem right_smul_mk (d : ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ) (u : FusionColumn (Γ.fuse a b))
    (v : FusionColumn (Γ.fuse (a + b) c)) :
    d • mk Γ a b c u v = mk Γ a b c u (d • v) :=
  rightActionEnd_mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse (a + b) c)) d u v

end GBL

/-! ### The right route `GBR` -/

/-- **`GBR Γ a b c = F_{b,c} ⊗_{D_{b+c}} F_{a,b+c}`** (§4.1): the right iterated fusion route,
balanced over the `(b+c)`-slot of the second fusion column. The Γ-mirror of `Bimod.BR`. -/
def GBR : Type _ :=
  RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c)))

namespace GBR

noncomputable instance : AddCommGroup (GBR Γ a b c) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c)))))

noncomputable instance : Module K (GBR Γ a b c) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c)))))

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse a (b + c)) →ₗ[K] GBR Γ a b c :=
  RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c)))

/-- The descended grading of `GBR`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GBR Γ a b c) :=
  relGrading (Γ.D (b + c)).carrier (FusionColumn.grading (Γ.fuse b c))
    (FusionColumn.grading (Γ.fuse a (b + c)))

noncomputable instance : DirectSum.Decomposition (grading Γ a b c) :=
  relDecomposition (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
    (FusionColumn.grading (Γ.fuse a (b + c)))

theorem mk_mem_grading {j k : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    {v : FusionColumn (Γ.fuse a (b + c))} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) k) :
    mk Γ a b c u v ∈ grading Γ a b c (j + k) :=
  mk_mem_relGrading (A := (Γ.D (b + c)).carrier)
    (FusionColumn.grading (Γ.fuse b c)) (FusionColumn.grading (Γ.fuse a (b + c))) hu hv

/-! #### The three slot actions and the right action -/

/-- The `D_b`-slot action (through the first fusion column). -/
noncomputable instance : Module (Γ.D b).carrier (GBR Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))))
    ((leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))) (B := (Γ.D b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (Γ.D b).carrier) (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse a (b + c))) :
    y • mk Γ a b c u v = mk Γ a b c (y • u) v :=
  leftActionEnd_mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) y u v

/-- The `D_c`-slot action (through the first fusion column). -/
noncomputable instance : Module (Γ.D c).carrier (GBR Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))))
    ((leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))) (B := (Γ.D c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (Γ.D c).carrier) (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse a (b + c))) :
    z • mk Γ a b c u v = mk Γ a b c (z • u) v :=
  leftActionEnd_mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) z u v

/-- The `D_a`-slot action: the Koszul-signed middle action through the second fusion column,
with the swapped supercommutation (`Bimod.superCommSMul_symm`). -/
noncomputable instance : Module (Γ.D a).carrier (GBR Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))))
    ((midAlgHom (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
      (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
        (FusionColumn.superCommSMul (Γ.fuse a (b + c))))).toRingHom)

/-- The sign law of the middle slot of `GBR`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2} {x : (Γ.D a).carrier} (hx : x ∈ (Γ.D a).grading k)
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) :
    x • mk Γ a b c u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk Γ a b c u (x • v) :=
  midEnd_mk_of_mem (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) hu hx v

/-- The right action of the total coefficient algebra `D_{a+(b+c)}` (`GBR`'s natural frame). -/
noncomputable instance : Module ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))))
    ((rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))) (C := (Γ.D (a + (b + c))).carrier)).toRingHom)

theorem right_smul_mk (d : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ) (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse a (b + c))) :
    d • mk Γ a b c u v = mk Γ a b c u (d • v) :=
  rightActionEnd_mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) d u v

/-! #### The coefficient recast: `D_{(a+b)+c}` in place of the natural `D_{a+(b+c)}` -/

/-- The right action of the *left-associated* coefficient algebra `D_{(a+b)+c}` on `GBR`, pulled
back along the gauge-index cast `Γ.gaugeCast (add_assoc a b c) : SuperAlgEquiv (Γ.D (a+b+c))
(Γ.D (a+(b+c)))` — the Γ-mirror of `Bimod.RouteRecast`'s M8a-8c′-0 device (`BR`'s recast along
`stdTowerCast`). Unlike the `ZMod 8` case, `Γ.D (a+b+c)` and `Γ.D (a+(b+c))` are genuinely
distinct types for an abstract `[AddGroup G]`, so this second right-action instance coexists with
the natural one without a diamond. -/
noncomputable instance : Module ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  Module.compHom _ (((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toRingHom).op)

theorem recast_op_smul_def (t : (Γ.D (a + b + c)).carrier) (w : GBR Γ a b c) :
    MulOpposite.op t • w
      = MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t) • w := rfl

/-- The recast action is coefficientwise: it acts through the natural right action on the second
factor, after transporting the coefficient along `Γ.gaugeCast (add_assoc a b c)`. -/
theorem recast_smul_mk (t : (Γ.D (a + b + c)).carrier) (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse a (b + c))) :
    MulOpposite.op t • mk Γ a b c u v
      = mk Γ a b c u (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t) • v) := by
  rw [recast_op_smul_def, right_smul_mk]

end GBR

end GaugeChi

end Superfusion

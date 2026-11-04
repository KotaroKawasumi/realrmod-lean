/-
Superfusion / GaugeChi / Pentagon

Milestone M12-3 of the abstract `(p, χ)` arc (SN-FREE DESIGN): **the
quadruple pentagon vertices, associators, and connectors** — the
Γ-mirror of `Superfusion.Bimod.PentagonB`'s structural layer
(`QuadRoutes`/`RouteRecast`/`QuadEdge2`/`QuadEdge2b`/`QuadEdge3`/
`QuadEdge4`/`QuadEdge5`/`MiddleSwap`/`QuadClose`), over the skeletal
data `(G, D_a, F_{a,b})` of a general division fusion gauge
`Γ : DivisionFusionGauge K G`.

For `a b c d : G` the pentagon compares five iterated fusions of
`a, b, c, d`; this file assembles the five vertices

* `GQ1  = GBL(a,b,c) ⊗_{D_{a+b+c}} F_{a+b+c,d}`         (`((ab)c)d`),
* `GQ2  = GBR(a,b,c) ⊗_{D_{a+b+c}} F_{a+b+c,d}`          (`(a(bc))d`,
  recast-balanced — the Γ-mirror of `RouteRecast`'s M8a-8c′-0 device,
  now on the raw column `F_{a,b+c}` as well as on `GBR` itself),
* `GQ4  = GBR(b,c,d) ⊗_{D_{b+c+d}} F_{a,b+c+d}`          (`a(b(cd))`,
  recast-balanced),
* `GQ5  = F_{a,b} ⊗_{D_{a+b}} GBR(a+b,c,d)`              (`(ab)(cd)`),
* `GQ4r = F_{c,d} ⊗_{D_{c+d}} GBR(a,b,c+d)`              (the
  right-associated landing of the last edge, reconciled with `GQ4` by
  `gq4Close`),

together with the associators (`gq2Assoc`, `gq3Assoc`, `gq1Assoc`,
`gq4lAssoc`), the middle swap (`gq5Swap`, discharging its `MidSignLaw`
hypotheses with `GBR.aslot_smul_mk_of_mem`/`GBL.cslot_smul_mk_of_mem`
from `GaugeChi.RouteBimod`), and the closing connector `gq4Close`.
Every associator/swap instantiation reuses the already-general
`Bimod.RelTensorAssoc`/`Bimod.MiddleSwap` machinery verbatim; the only
new algebraic content is the *column-level* recast of `F_{a,b+c}`
along `Γ.gaugeCast (add_assoc a b c)` (mirroring `RouteRecast.lean`'s
column-level recast of `TowerColumn K a (b+c)`) and the index-equality
cast `fusionColumnCast` on fusion columns (mirroring `columnCast`).

The five EDGES (`GE1`–`GE5`) and their generator formulas continue in
`GaugeChi.PentagonEdges`; no equivariance packages are built this
round (M12-4's job, mirroring how the tower separated `1a`/`1b` from
`2b`).
-/
import Superfusion.GaugeChi.RouteBimod
import Superfusion.Bimod.RelTensorAssoc
import Superfusion.Bimod.MiddleSwap

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-! ### The first two vertices -/

/-- **`GQ1 = GBL(a,b,c) ⊗_{D_{a+b+c}} F_{a+b+c,d}`** (§4.1): the
`((ab)c)d`-vertex. -/
def GQ1 : Type _ :=
  RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d))

noncomputable instance : AddCommGroup (GQ1 K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d))))

noncomputable instance : Module K (GQ1 K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d))))

/-- **`GQ2 = GBR(a,b,c) ⊗_{D_{a+b+c}} F_{a+b+c,d}`** (§4.1): the
`(a(bc))d`-vertex, balanced through the recast right action of `GBR`
(`GaugeChi.RouteBimod`'s `GBR`-level recast). -/
def GQ2 : Type _ :=
  RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d))

noncomputable instance : AddCommGroup (GQ2 K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d))))

noncomputable instance : Module K (GQ2 K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d))))

/-! ### The column-level recast: `D_{a+b+c}` in place of the natural
`D_{a+(b+c)}` on `F_{a,b+c}`

The Γ-mirror of `Bimod.RouteRecast`'s column-level recast of
`TowerColumn K a (b+c)` — needed so that `gq2Assoc` (below) can
instantiate `RelTensor.assoc` with the SAME algebra `D_{a+b+c}` on both
sides of the association. -/

/-- The right action of the *left-associated* coefficient algebra
`D_{a+b+c}` on `F_{a,b+c}`, pulled back along the gauge-index cast
`Γ.gaugeCast (add_assoc a b c)`. -/
noncomputable instance :
    Module ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse a (b + c))) :=
  Module.compHom _ (((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toRingHom).op)

theorem fusionColumn_recast_op_smul_def
    (t : (Γ.D (a + b + c)).carrier) (v : FusionColumn (Γ.fuse a (b + c))) :
    MulOpposite.op t • v
      = MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t) • v := rfl

/-- The recast slot actions still commute (transported from the
canonical-coefficient instances). -/
instance : SMulCommClass (Γ.D (b + c)).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse a (b + c))) :=
  ⟨fun y t v => smul_comm y
    (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) v⟩

instance : SMulCommClass (Γ.D a).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse a (b + c))) :=
  ⟨fun x t v => smul_comm x
    (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) v⟩

instance : IsScalarTower K
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse a (b + c))) :=
  ⟨fun k t v => by
    show (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
        (MulOpposite.unop (k • t)))) • v
      = k • ((MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          (MulOpposite.unop t))) • v)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ v⟩

/-! ### The associator at the `(a(bc))d`-vertex -/

/-- The right-associated form of the `(a(bc))d`-vertex. -/
def GQ2r : Type _ :=
  RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (FusionColumn (Γ.fuse (a + b + c) d)))

noncomputable instance : AddCommGroup (GQ2r K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) d)))))

noncomputable instance : Module K (GQ2r K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) d)))))

/-- **The associator at the `(a(bc))d`-vertex**: the abstract
`RelTensor.assoc`, instantiated through the column-level recast. -/
noncomputable def gq2Assoc : GQ2 K Γ a b c d ≃ₗ[K] GQ2r K Γ a b c d :=
  RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c)))
    (FusionColumn (Γ.fuse (a + b + c) d))

theorem gq2Assoc_mk (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    gq2Assoc K Γ a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBR.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d))) u
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v w) :=
  RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c)))
    (FusionColumn (Γ.fuse (a + b + c) d)) u v w

/-! ### The `a((bc)d)`-vertex, right-associated -/

/-- The middle factor of `GQ2r`: the spelled `GBL(a,b+c,d)`. -/
abbrev GQ2rInner : Type _ :=
  RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
    (FusionColumn (Γ.fuse (a + b + c) d))

/-- The spelled `GBR(a,b+c,d)` (no recast is needed at this spelling —
`GBR Γ a (b+c) d`'s own natural coefficient tower is literally
`D_{(b+c)+d} = D_{b+c+d}`). -/
def GQ3Inner : Type _ :=
  RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
    (FusionColumn (Γ.fuse a (b + c + d)))

noncomputable instance : AddCommGroup (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
      (FusionColumn (Γ.fuse a (b + c + d)))))

noncomputable instance : Module K (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
      (FusionColumn (Γ.fuse a (b + c + d)))))

/-- The outer-left `D_{b+c}`-action on `GQ3Inner` (through the
`(b+c)`-slot of its first column). -/
noncomputable instance : Module (Γ.D (b + c)).carrier (GQ3Inner K Γ a b c d) :=
  leftModule K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
    (FusionColumn (Γ.fuse a (b + c + d))) (B := (Γ.D (b + c)).carrier)

/-- Pentagon vertex `a((bc)d)`, in right-associated form. -/
def GQ3 : Type _ :=
  RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)

noncomputable instance : AddCommGroup (GQ3 K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)))

noncomputable instance : Module K (GQ3 K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)))

/-! ### The fourth vertex `a(b(cd))`, and the associator at `a((bc)d)` -/

/-- **`GQ4 = GBR(b,c,d) ⊗_{D_{b+c+d}} F_{a,b+c+d}`** (§4.1): the
`a(b(cd))`-vertex, balanced through the recast right action of `GBR`. -/
def GQ4 : Type _ :=
  RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d)))

noncomputable instance : AddCommGroup (GQ4 K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d)))))

noncomputable instance : Module K (GQ4 K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d)))))

/-- The associator at the `a((bc)d)`-vertex: the left-associated form
`GBL(b,c,d) ⊗ F_{a,(b+c)+d}` re-associates to `GQ3` (all balancings
canonical). -/
noncomputable def gq3Assoc :
    (RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))))
      ≃ₗ[K] GQ3 K Γ a b c d :=
  RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse (b + c) d))
    (FusionColumn (Γ.fuse a (b + c + d)))

theorem gq3Assoc_mk (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    gq3Assoc K Γ a b c d
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) (GBL.mk Γ b c d u v) w)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
            (FusionColumn (Γ.fuse a (b + c + d))) v w) :=
  RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse (b + c) d))
    (FusionColumn (Γ.fuse a (b + c + d))) u v w

/-! ### The fifth vertex `(ab)(cd)`, and the associator at `((ab)c)d` -/

/-- **`GQ5 = F_{a,b} ⊗_{D_{a+b}} GBR(a+b,c,d)`** (§4.1): the
`(ab)(cd)`-vertex, the two-sided fusion. -/
def GQ5 : Type _ :=
  RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)

noncomputable instance : AddCommGroup (GQ5 K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)))

noncomputable instance : Module K (GQ5 K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)))

/-- The associator at the `((ab)c)d`-vertex: the right-associated form
exposes the canonical `GBL(a+b,c,d)` (all balancings canonical). -/
noncomputable def gq1Assoc :
    GQ1 K Γ a b c d ≃ₗ[K]
      RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) c d) :=
  RelTensor.assoc K (Γ.D (a + b)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c))
    (FusionColumn (Γ.fuse (a + b + c) d))

theorem gq1Assoc_mk (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c))
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    gq1Assoc K Γ a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) c d) u
          (GBL.mk Γ (a + b) c d v w) :=
  RelTensor.assoc_mk K (Γ.D (a + b)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c))
    (FusionColumn (Γ.fuse (a + b + c) d)) u v w

/-! ### The middle swap at the `(ab)(cd)`-vertex -/

/-- `inferInstanceAs` bridge: the signed middle `D_{a+b}`-action of
`GBR(a+b,c,d)` in the raw `RelTensor` spelling (the inner factor of
`GQ5` as the middle swap sees it). -/
noncomputable instance : Module (Γ.D (a + b)).carrier
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (FusionColumn (Γ.fuse (a + b) (c + d)))) :=
  inferInstanceAs (Module (Γ.D (a + b)).carrier (GBR Γ (a + b) c d))

/-- `inferInstanceAs` bridge: the signed middle `D_{c+d}`-action of
`GBL(a,b,c+d)` in the raw `RelTensor` spelling (the inner factor of the
swapped vertex). -/
noncomputable instance : Module (Γ.D (c + d)).carrier
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) (c + d)))) :=
  inferInstanceAs (Module (Γ.D (c + d)).carrier (GBL Γ a b (c + d)))

/-- The sign law of the `GQ5`-side balancing: the `D_{a+b}`-slot of
`GBR(a+b,c,d)` is a signed middle action. -/
private theorem gq5LawA :
    MidSignLaw K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (FusionColumn (Γ.fuse (a + b) (c + d)))
      (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse c d)) := by
  intro l i x hx n hn p
  exact GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b) (b := c) (c := d) hx hn p

/-- The sign law of the swapped-side balancing: the `D_{c+d}`-slot of
`GBL(a,b,c+d)` is a signed middle action. -/
private theorem gq5LawB :
    MidSignLaw K (Γ.D (c + d)).carrier (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) (c + d)))
      (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse a b)) := by
  intro l i z hz m hm p
  exact GBL.cslot_smul_mk_of_mem (Γ := Γ) (a := a) (b := b) (c := c + d) hz hm p

/-- The swapped presentation of the `(ab)(cd)`-vertex: the middle swap
exposes the canonical `GBL(a,b,c+d)`. -/
def GQ5s : Type _ :=
  RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ a b (c + d))

noncomputable instance : AddCommGroup (GQ5s K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ a b (c + d))))

noncomputable instance : Module K (GQ5s K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ a b (c + d))))

/-- **The middle swap at the `(ab)(cd)`-vertex**: the direct
instantiation of `midSwap` at the fusion columns. -/
noncomputable def gq5Swap : GQ5 K Γ a b c d ≃ₗ[K] GQ5s K Γ a b c d :=
  midSwap K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (a + b) (c + d)))
    (Γ.D (a + b)).grading (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse c d))
    (gq5LawA K Γ a b c d) (gq5LawB K Γ a b c d)

/-- The sign law of the swap on homogeneous generators:
`u ⊗ (v ⊗ w) ↦ (-1)^{|u||v|} v ⊗ (u ⊗ w)`. -/
theorem gq5Swap_mk_of_mem {i j : ZMod 2} {v : FusionColumn (Γ.fuse c d)}
    {u : FusionColumn (Γ.fuse a b)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    gq5Swap K Γ a b c d
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
          (GBR.mk Γ (a + b) c d v w))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ a b (c + d)) v
            (GBL.mk Γ a b (c + d) u w) :=
  midSwap_mk_of_mem K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (a + b) (c + d)))
    (Γ.D (a + b)).grading (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse c d))
    (gq5LawA K Γ a b c d) (gq5LawB K Γ a b c d) hv hu w

/-! ### Closing the bottom route: `GQ4r ≃ GQ4` -/

/-- The landing of the fifth edge: the right-associated presentation
`F_{c,d} ⊗_{D_{c+d}} GBR(a,b,c+d)` of the `a(b(cd))`-vertex. Its
reconciliation with `GQ4` is `gq4Close`. -/
def GQ4r : Type _ :=
  RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))

noncomputable instance : AddCommGroup (GQ4r K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))))

noncomputable instance : Module K (GQ4r K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))))

/-- The left-associated, natural-coefficient presentation of the
`a(b(cd))`-vertex: `GBR(b,c,d) ⊗_{D_{b+(c+d)}} F_{a,b+(c+d)}` (all
balancings canonical). -/
def GQ4l : Type _ :=
  RelTensor K (Γ.D (b + (c + d))).carrier (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + (c + d))))

noncomputable instance : AddCommGroup (GQ4l K Γ a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + (c + d))))))

noncomputable instance : Module K (GQ4l K Γ a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + (c + d))))))

/-! #### The associator leg -/

/-- The associator at the `a(b(cd))`-vertex: the left-associated
natural form re-associates to `GQ4r`. -/
noncomputable def gq4lAssoc : GQ4l K Γ a b c d ≃ₗ[K] GQ4r K Γ a b c d :=
  RelTensor.assoc K (Γ.D (c + d)).carrier (Γ.D (b + (c + d))).carrier
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
    (FusionColumn (Γ.fuse a (b + (c + d))))

theorem gq4lAssoc_mk (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4lAssoc K Γ a b c d
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + (c + d)))) (GBR.mk Γ b c d v u) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
          (RelTensor.mk K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
            (FusionColumn (Γ.fuse a (b + (c + d)))) u w) :=
  RelTensor.assoc_mk K (Γ.D (c + d)).carrier (Γ.D (b + (c + d))).carrier
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
    (FusionColumn (Γ.fuse a (b + (c + d)))) v u w

/-! #### The recast leg: `fusionColumnCast` -/

/-- Cast of a fusion column along an index equality of its second slot
(the `subst`-`refl` pattern of `Γ.gaugeCast`) — the Γ-mirror of
`Bimod.RouteRecast`'s `columnCast`. -/
noncomputable def fusionColumnCast (a : G) {x y : G} (h : x = y) :
    FusionColumn (Γ.fuse a x) ≃ₗ[K] FusionColumn (Γ.fuse a y) := by
  subst h
  exact LinearEquiv.refl K _

/-- The column cast intertwines the second-slot actions along
`Γ.gaugeCast`. -/
theorem fusionColumnCast_symm_rslot {x y : G} (h : x = y)
    (β : (Γ.D y).carrier) (v : FusionColumn (Γ.fuse a y)) :
    fusionColumnCast K Γ a h.symm (β • v)
      = ((Γ.gaugeCast h).toAlgEquiv.symm β) • fusionColumnCast K Γ a h.symm v := by
  subst h
  rfl

/-- The inverse column cast intertwines the second-slot actions along
`Γ.gaugeCast`. -/
theorem fusionColumnCast_symm_symm_rslot {x y : G} (h : x = y)
    (t : (Γ.D x).carrier) (w : FusionColumn (Γ.fuse a x)) :
    (fusionColumnCast K Γ a h.symm).symm (t • w)
      = ((Γ.gaugeCast h).toAlgEquiv t) • (fusionColumnCast K Γ a h.symm).symm w := by
  subst h
  rfl

/-- The forward bilinear of the recast leg: `(m, v) ↦ m ⊗ (columnCast v)`. -/
private noncomputable def gq4CloseFwdBilin :
    GBR Γ b c d →ₗ[K] FusionColumn (Γ.fuse a (b + (c + d))) →ₗ[K] GQ4 K Γ a b c d :=
  (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d)))).compl₂
    (fusionColumnCast K Γ a (add_assoc b c d).symm).toLinearMap

private theorem gq4CloseFwdBilin_apply (m : GBR Γ b c d)
    (v : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4CloseFwdBilin K Γ a b c d m v
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m
          (fusionColumnCast K Γ a (add_assoc b c d).symm v) :=
  rfl

/-- Balancedness of the forward leg: the natural balancing of `GQ4l`
maps to the recast balancing of `GQ4` through the gauge-index cast. -/
private theorem gq4CloseFwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + (c + d))).carrier (gq4CloseFwdBilin K Γ a b c d) := by
  intro β m v
  rw [gq4CloseFwdBilin_apply, gq4CloseFwdBilin_apply, fusionColumnCast_symm_rslot,
    show (MulOpposite.op β • m : GBR Γ b c d)
        = MulOpposite.op ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv.symm β) • m from by
      rw [GBR.recast_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

/-- The backward bilinear of the recast leg: `(m, w) ↦ m ⊗ (columnCast⁻¹ w)`. -/
private noncomputable def gq4CloseBwdBilin :
    GBR Γ b c d →ₗ[K] FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] GQ4l K Γ a b c d :=
  (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + (c + d))))).compl₂
    (fusionColumnCast K Γ a (add_assoc b c d).symm).symm.toLinearMap

private theorem gq4CloseBwdBilin_apply (m : GBR Γ b c d)
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    gq4CloseBwdBilin K Γ a b c d m w
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + (c + d)))) m
          ((fusionColumnCast K Γ a (add_assoc b c d).symm).symm w) :=
  rfl

/-- Balancedness of the backward leg: the recast balancing of `GQ4`
maps to the natural balancing of `GQ4l` through the gauge-index cast. -/
private theorem gq4CloseBwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + d)).carrier (gq4CloseBwdBilin K Γ a b c d) := by
  intro t m w
  rw [gq4CloseBwdBilin_apply, gq4CloseBwdBilin_apply,
    fusionColumnCast_symm_symm_rslot, GBR.recast_op_smul_def, RelTensor.mk_op_smul]

private noncomputable def gq4CloseFwd : GQ4l K Γ a b c d →ₗ[K] GQ4 K Γ a b c d :=
  RelTensor.lift (gq4CloseFwdBilin K Γ a b c d) (gq4CloseFwd_balanced K Γ a b c d)

private noncomputable def gq4CloseBwd : GQ4 K Γ a b c d →ₗ[K] GQ4l K Γ a b c d :=
  RelTensor.lift (gq4CloseBwdBilin K Γ a b c d) (gq4CloseBwd_balanced K Γ a b c d)

private theorem gq4CloseFwd_mk (m : GBR Γ b c d) (v : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4CloseFwd K Γ a b c d
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + (c + d)))) m v)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m
          (fusionColumnCast K Γ a (add_assoc b c d).symm v) := by
  show RelTensor.lift (gq4CloseFwdBilin K Γ a b c d) (gq4CloseFwd_balanced K Γ a b c d)
      (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + (c + d)))) m v) = _
  rw [RelTensor.lift_mk, gq4CloseFwdBilin_apply]

private theorem gq4CloseBwd_mk (m : GBR Γ b c d) (w : FusionColumn (Γ.fuse a (b + c + d))) :
    gq4CloseBwd K Γ a b c d
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m w)
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + (c + d)))) m
          ((fusionColumnCast K Γ a (add_assoc b c d).symm).symm w) := by
  show RelTensor.lift (gq4CloseBwdBilin K Γ a b c d) (gq4CloseBwd_balanced K Γ a b c d)
      (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) m w) = _
  rw [RelTensor.lift_mk, gq4CloseBwdBilin_apply]

private theorem gq4CloseFwd_gq4CloseBwd :
    (gq4CloseFwd K Γ a b c d).comp (gq4CloseBwd K Γ a b c d) = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show gq4CloseFwd K Γ a b c d (gq4CloseBwd K Γ a b c d
      (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) m w))
    = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) m w
  rw [gq4CloseBwd_mk, gq4CloseFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gq4CloseBwd_gq4CloseFwd :
    (gq4CloseBwd K Γ a b c d).comp (gq4CloseFwd K Γ a b c d) = LinearMap.id := by
  refine RelTensor.hom_ext fun m v => ?_
  show gq4CloseBwd K Γ a b c d (gq4CloseFwd K Γ a b c d
      (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + (c + d)))) m v))
    = RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + (c + d)))) m v
  rw [gq4CloseFwd_mk, gq4CloseBwd_mk, LinearEquiv.symm_apply_apply]

/-- **The coefficient recast** `GQ4l ≃ GQ4`: identity on `GBR(b,c,d)`,
the column cast on the second factor. -/
noncomputable def gq4Recast : GQ4l K Γ a b c d ≃ₗ[K] GQ4 K Γ a b c d :=
  LinearEquiv.ofLinear (gq4CloseFwd K Γ a b c d) (gq4CloseBwd K Γ a b c d)
    (gq4CloseFwd_gq4CloseBwd K Γ a b c d) (gq4CloseBwd_gq4CloseFwd K Γ a b c d)

theorem gq4Recast_mk (m : GBR Γ b c d) (v : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4Recast K Γ a b c d
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + (c + d)))) m v)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m
          (fusionColumnCast K Γ a (add_assoc b c d).symm v) :=
  gq4CloseFwd_mk K Γ a b c d m v

/-! ### The connector -/

/-- **Closing the bottom route**: the connector between the two
presentations of the `a(b(cd))`-vertex — the associator followed by
the coefficient recast. Both pentagon routes now land in `GQ4`. -/
noncomputable def gq4Close : GQ4r K Γ a b c d ≃ₗ[K] GQ4 K Γ a b c d :=
  (gq4lAssoc K Γ a b c d).symm.trans (gq4Recast K Γ a b c d)

/-- The generator formula of the connector (no signs). -/
theorem gq4Close_mk (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4Close K Γ a b c d
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
          (RelTensor.mk K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
            (FusionColumn (Γ.fuse a (b + (c + d)))) u w))
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d v u)
          (fusionColumnCast K Γ a (add_assoc b c d).symm w) := by
  show gq4Recast K Γ a b c d ((gq4lAssoc K Γ a b c d).symm
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d)))) u w))) = _
  rw [← gq4lAssoc_mk, LinearEquiv.symm_apply_apply, gq4Recast_mk]

end GaugeChi

end Superfusion

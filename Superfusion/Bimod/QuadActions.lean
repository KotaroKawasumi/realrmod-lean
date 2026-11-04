/-
Superfusion / Bimod / QuadActions

Milestone M8a-8c′-2a″ (roadmap v3): **the four slot actions of the
pentagon endpoints** — `Q1` (the `((ab)c)d`-vertex) and `Q4` (the
`a(b(cd))`-vertex) carry, besides their balancing, the four slot
actions of `T_a`, `T_b`, `T_c`, `T_d`, the right action of the total
coefficient algebra, and the descended grading:

* on `Q1 = B_L(a,b,c) ⊗_{T_{(a+b)+c}} C_{(a+b)+c,d}` the `a`, `b`,
  `c` slots act through the `B_L`-factor (outer left action — the
  compatibility instances of M8a-8c′-2a), and the `d`-slot through
  the column by the Koszul-signed middle action;
* on `Q4 = B_R(b,c,d) ⊗_{T_{(b+c)+d}} C_{a,(b+c)+d}` (recast
  balancing) the `b`, `c`, `d` slots act through the `B_R`-factor,
  and the `a`-slot through the column by the signed middle action —
  with the graded right coefficient action supplied by the recast
  `GradedRightSMul` of M8a-8c′-2a.

This is the `(D_a ⊗̂ D_b ⊗̂ D_c ⊗̂ D_d, D_{abcd})`-superbimodule
structure of the pentagon endpoints, slot-wise, ready for the
quadruple intertwiner space.
-/
import Superfusion.Bimod.RouteCompat

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-! ### The slot actions of `Q1` -/

namespace Q1

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    BL K a b c →ₗ[K] TowerColumn K (a + b + c) d →ₗ[K] Q1 K a b c d :=
  RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
    (TowerColumn K (a + b + c) d)

/-- The `T_a`-slot action (through the `B_L`-factor). -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (Q1 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d))
    ((leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d)
      (B := (stdTower (K := K) a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (stdTower (K := K) a).carrier)
    (u : BL K a b c) (v : TowerColumn K (a + b + c) d) :
    x • mk K a b c d u v
      = mk K a b c d (x • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BL K a b c) (TowerColumn K (a + b + c) d) x u v

/-- The `T_b`-slot action (through the `B_L`-factor). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (Q1 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d))
    ((leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d)
      (B := (stdTower (K := K) b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (stdTower (K := K) b).carrier)
    (u : BL K a b c) (v : TowerColumn K (a + b + c) d) :
    y • mk K a b c d u v
      = mk K a b c d (y • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BL K a b c) (TowerColumn K (a + b + c) d) y u v

/-- The `T_c`-slot action (through the `B_L`-factor). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (Q1 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d))
    ((leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d)
      (B := (stdTower (K := K) c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (stdTower (K := K) c).carrier)
    (u : BL K a b c) (v : TowerColumn K (a + b + c) d) :
    z • mk K a b c d u v
      = mk K a b c d (z • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BL K a b c) (TowerColumn K (a + b + c) d) z u v

/-- The `T_d`-slot action: the Koszul-signed middle action through
the column. -/
noncomputable instance : Module (stdTower (K := K) d).carrier
    (Q1 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d))
    ((midAlgHom (stdTower (K := K) (a + b + c)).grading
      (BL.grading K a b c) (stdTower (K := K) d).grading
      (TowerColumn.superCommSMul K (a + b + c) d)).toRingHom)

/-- The sign law of the `d`-slot: for homogeneous `t`, `u`,
`t • (u ⊗ v) = (-1)^{|t||u|} u ⊗ (t • v)`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2}
    {t : (stdTower (K := K) d).carrier}
    (ht : t ∈ (stdTower (K := K) d).grading k)
    {u : BL K a b c} (hu : u ∈ BL.grading K a b c j)
    (v : TowerColumn K (a + b + c) d) :
    t • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          mk K a b c d u (t • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (a + b + c)).grading
    (BL.grading K a b c) (stdTower (K := K) d).grading
    (TowerColumn.superCommSMul K (a + b + c) d) hu ht v

/-- The right action of the total coefficient algebra
`T_{((a+b)+c)+d}`. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q1 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d))
    ((rightActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d)
      (C := (stdTower (K := K) (a + b + c + d)).carrier)).toRingHom)

theorem right_smul_mk
    (τ : ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ)
    (u : BL K a b c) (v : TowerColumn K (a + b + c) d) :
    τ • mk K a b c d u v
      = mk K a b c d u (τ • v) :=
  rightActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BL K a b c) (TowerColumn K (a + b + c) d) τ u v

/-- The descended grading of `Q1`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (Q1 K a b c d) :=
  relGrading (stdTower (K := K) (a + b + c)).carrier
    (BL.grading K a b c) (TowerColumn.grading K (a + b + c) d)

noncomputable instance : DirectSum.Decomposition (grading K a b c d) :=
  relDecomposition (stdTower (K := K) (a + b + c)).grading
    (BL.grading K a b c) (TowerColumn.grading K (a + b + c) d)

theorem mk_mem_grading {j k : ZMod 2} {u : BL K a b c}
    {v : TowerColumn K (a + b + c) d}
    (hu : u ∈ BL.grading K a b c j)
    (hv : v ∈ TowerColumn.grading K (a + b + c) d k) :
    mk K a b c d u v
      ∈ grading K a b c d (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (a + b + c)).carrier)
    (BL.grading K a b c) (TowerColumn.grading K (a + b + c) d) hu hv

end Q1

/-! ### The slot actions of `Q4` -/

namespace Q4

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    BR K b c d →ₗ[K] TowerColumn K a ((b + c) + d) →ₗ[K] Q4 K a b c d :=
  RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d))

/-- The `T_b`-slot action (through the `B_R`-factor, over the recast
balancing). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (Q4 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
      (TowerColumn K a ((b + c) + d)))
    ((leftActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d))
      (B := (stdTower (K := K) b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (stdTower (K := K) b).carrier)
    (u : BR K b c d) (v : TowerColumn K a ((b + c) + d)) :
    y • mk K a b c d u v
      = mk K a b c d (y • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (b + c + d)).carrier
    (BR K b c d) (TowerColumn K a ((b + c) + d)) y u v

/-- The `T_c`-slot action (through the `B_R`-factor). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (Q4 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
      (TowerColumn K a ((b + c) + d)))
    ((leftActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d))
      (B := (stdTower (K := K) c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (stdTower (K := K) c).carrier)
    (u : BR K b c d) (v : TowerColumn K a ((b + c) + d)) :
    z • mk K a b c d u v
      = mk K a b c d (z • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (b + c + d)).carrier
    (BR K b c d) (TowerColumn K a ((b + c) + d)) z u v

/-- The `T_d`-slot action (through the `B_R`-factor). -/
noncomputable instance : Module (stdTower (K := K) d).carrier
    (Q4 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
      (TowerColumn K a ((b + c) + d)))
    ((leftActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d))
      (B := (stdTower (K := K) d).carrier)).toRingHom)

theorem dslot_smul_mk (t : (stdTower (K := K) d).carrier)
    (u : BR K b c d) (v : TowerColumn K a ((b + c) + d)) :
    t • mk K a b c d u v
      = mk K a b c d (t • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (b + c + d)).carrier
    (BR K b c d) (TowerColumn K a ((b + c) + d)) t u v

/-- The `T_a`-slot action: the Koszul-signed middle action through
the column, with the swapped supercommutation. -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (Q4 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
      (TowerColumn K a ((b + c) + d)))
    ((midAlgHom (stdTower (K := K) (b + c + d)).grading
      (BR.grading K b c d) (stdTower (K := K) a).grading
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (b + c + d)).grading
        (TowerColumn.superCommSMul K a ((b + c) + d)))).toRingHom)

/-- The sign law of the `a`-slot of `Q4`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    {u : BR K b c d} (hu : u ∈ BR.grading K b c d j)
    (v : TowerColumn K a ((b + c) + d)) :
    x • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          mk K a b c d u (x • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (b + c + d)).grading
    (BR.grading K b c d) (stdTower (K := K) a).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c + d)).grading
      (TowerColumn.superCommSMul K a ((b + c) + d))) hu hx v

/-- The right action of the total coefficient algebra
`T_{a+((b+c)+d)}`. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ
    (Q4 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
      (TowerColumn K a ((b + c) + d)))
    ((rightActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d))
      (C := (stdTower (K := K) (a + (b + c + d))).carrier)).toRingHom)

theorem right_smul_mk
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (u : BR K b c d) (v : TowerColumn K a ((b + c) + d)) :
    τ • mk K a b c d u v
      = mk K a b c d u (τ • v) :=
  rightActionEnd_mk K (stdTower (K := K) (b + c + d)).carrier
    (BR K b c d) (TowerColumn K a ((b + c) + d)) τ u v

/-- The descended grading of `Q4`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (Q4 K a b c d) :=
  relGrading (stdTower (K := K) (b + c + d)).carrier
    (BR.grading K b c d) (TowerColumn.grading K a ((b + c) + d))

noncomputable instance : DirectSum.Decomposition (grading K a b c d) :=
  relDecomposition (stdTower (K := K) (b + c + d)).grading
    (BR.grading K b c d) (TowerColumn.grading K a ((b + c) + d))

theorem mk_mem_grading {j k : ZMod 2} {u : BR K b c d}
    {v : TowerColumn K a ((b + c) + d)}
    (hu : u ∈ BR.grading K b c d j)
    (hv : v ∈ TowerColumn.grading K a ((b + c) + d) k) :
    mk K a b c d u v
      ∈ grading K a b c d (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (b + c + d)).carrier)
    (BR.grading K b c d) (TowerColumn.grading K a ((b + c) + d)) hu hv

end Q4


/-! ### The slot actions of `Q2` -/

namespace Q2

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    BR K a b c →ₗ[K] TowerColumn K (a + b + c) d →ₗ[K] Q2 K a b c d :=
  RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
    (TowerColumn K (a + b + c) d)

/-- The `T_a`-slot action (through the `B_R`-factor, over the recast
balancing). -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (Q2 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
      (TowerColumn K (a + b + c) d))
    ((leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BR K a b c) (TowerColumn K (a + b + c) d)
      (B := (stdTower (K := K) a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (stdTower (K := K) a).carrier)
    (u : BR K a b c) (v : TowerColumn K (a + b + c) d) :
    x • mk K a b c d u v = mk K a b c d (x • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BR K a b c) (TowerColumn K (a + b + c) d) x u v

/-- The `T_b`-slot action (through the `B_R`-factor). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (Q2 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
      (TowerColumn K (a + b + c) d))
    ((leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BR K a b c) (TowerColumn K (a + b + c) d)
      (B := (stdTower (K := K) b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (stdTower (K := K) b).carrier)
    (u : BR K a b c) (v : TowerColumn K (a + b + c) d) :
    y • mk K a b c d u v = mk K a b c d (y • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BR K a b c) (TowerColumn K (a + b + c) d) y u v

/-- The `T_c`-slot action (through the `B_R`-factor). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (Q2 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
      (TowerColumn K (a + b + c) d))
    ((leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BR K a b c) (TowerColumn K (a + b + c) d)
      (B := (stdTower (K := K) c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (stdTower (K := K) c).carrier)
    (u : BR K a b c) (v : TowerColumn K (a + b + c) d) :
    z • mk K a b c d u v = mk K a b c d (z • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BR K a b c) (TowerColumn K (a + b + c) d) z u v

/-- The `T_d`-slot action: the Koszul-signed middle action through
the column. -/
noncomputable instance : Module (stdTower (K := K) d).carrier
    (Q2 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
      (TowerColumn K (a + b + c) d))
    ((midAlgHom (stdTower (K := K) (a + b + c)).grading
      (BR.grading K a b c) (stdTower (K := K) d).grading
      (TowerColumn.superCommSMul K (a + b + c) d)).toRingHom)

/-- The sign law of the `d`-slot of `Q2`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2}
    {t : (stdTower (K := K) d).carrier}
    (ht : t ∈ (stdTower (K := K) d).grading k)
    {u : BR K a b c} (hu : u ∈ BR.grading K a b c j)
    (v : TowerColumn K (a + b + c) d) :
    t • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c d u (t • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (a + b + c)).grading
    (BR.grading K a b c) (stdTower (K := K) d).grading
    (TowerColumn.superCommSMul K (a + b + c) d) hu ht v

/-- The right action of the total coefficient algebra
`T_{((a+b)+c)+d}`. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q2 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
      (TowerColumn K (a + b + c) d))
    ((rightActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BR K a b c) (TowerColumn K (a + b + c) d)
      (C := (stdTower (K := K) (a + b + c + d)).carrier)).toRingHom)

theorem right_smul_mk
    (τ : ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ)
    (u : BR K a b c) (v : TowerColumn K (a + b + c) d) :
    τ • mk K a b c d u v = mk K a b c d u (τ • v) :=
  rightActionEnd_mk K (stdTower (K := K) (a + b + c)).carrier
    (BR K a b c) (TowerColumn K (a + b + c) d) τ u v

/-- The descended grading of `Q2`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (Q2 K a b c d) :=
  relGrading (stdTower (K := K) (a + b + c)).carrier
    (BR.grading K a b c) (TowerColumn.grading K (a + b + c) d)

noncomputable instance : DirectSum.Decomposition (grading K a b c d) :=
  relDecomposition (stdTower (K := K) (a + b + c)).grading
    (BR.grading K a b c) (TowerColumn.grading K (a + b + c) d)

theorem mk_mem_grading {j k : ZMod 2} {u : BR K a b c}
    {v : TowerColumn K (a + b + c) d}
    (hu : u ∈ BR.grading K a b c j)
    (hv : v ∈ TowerColumn.grading K (a + b + c) d k) :
    mk K a b c d u v ∈ grading K a b c d (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (a + b + c)).carrier)
    (BR.grading K a b c) (TowerColumn.grading K (a + b + c) d) hu hv

end Q2


/-! ### The slot actions of `Q5` -/

namespace Q5

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    TowerColumn K a b →ₗ[K] BR K (a + b) c d →ₗ[K] Q5 K a b c d :=
  RelTensor.mk K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
    (BR K (a + b) c d)

/-- The `T_a`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (Q5 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (BR K (a + b) c d))
    ((leftActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (BR K (a + b) c d)
      (B := (stdTower (K := K) a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (stdTower (K := K) a).carrier)
    (u : TowerColumn K a b) (v : BR K (a + b) c d) :
    x • mk K a b c d u v = mk K a b c d (x • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b)).carrier
    (TowerColumn K a b) (BR K (a + b) c d) x u v

/-- The `T_b`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (Q5 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (BR K (a + b) c d))
    ((leftActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (BR K (a + b) c d)
      (B := (stdTower (K := K) b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (stdTower (K := K) b).carrier)
    (u : TowerColumn K a b) (v : BR K (a + b) c d) :
    y • mk K a b c d u v = mk K a b c d (y • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b)).carrier
    (TowerColumn K a b) (BR K (a + b) c d) y u v

/-- The `T_c`-slot action: the Koszul-signed middle action through
the outer `c`-slot of the `B_R`-factor (mid-of-mid). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (Q5 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (BR K (a + b) c d))
    ((midAlgHom (stdTower (K := K) (a + b)).grading
      (TowerColumn.grading K a b) (stdTower (K := K) c).grading
      (BR.superCommSMul_aslot_bslot K (a + b) c d)).toRingHom)

/-- The sign law of the `c`-slot of `Q5`. -/
theorem cslot_smul_mk_of_mem {j k : ZMod 2}
    {z : (stdTower (K := K) c).carrier}
    (hz : z ∈ (stdTower (K := K) c).grading k)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (v : BR K (a + b) c d) :
    z • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c d u (z • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (a + b)).grading
    (TowerColumn.grading K a b) (stdTower (K := K) c).grading
    (BR.superCommSMul_aslot_bslot K (a + b) c d) hu hz v

/-- The `T_d`-slot action: the Koszul-signed middle action through
the outer `d`-slot of the `B_R`-factor (mid-of-mid). -/
noncomputable instance : Module (stdTower (K := K) d).carrier
    (Q5 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (BR K (a + b) c d))
    ((midAlgHom (stdTower (K := K) (a + b)).grading
      (TowerColumn.grading K a b) (stdTower (K := K) d).grading
      (BR.superCommSMul_aslot_cslot K (a + b) c d)).toRingHom)

/-- The sign law of the `d`-slot of `Q5`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2}
    {t : (stdTower (K := K) d).carrier}
    (ht : t ∈ (stdTower (K := K) d).grading k)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (v : BR K (a + b) c d) :
    t • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c d u (t • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (a + b)).grading
    (TowerColumn.grading K a b) (stdTower (K := K) d).grading
    (BR.superCommSMul_aslot_cslot K (a + b) c d) hu ht v

/-- The right action of the total coefficient algebra
`T_{(a+b)+(c+d)}`. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + b + (c + d))).carrier)ᵐᵒᵖ
    (Q5 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (BR K (a + b) c d))
    ((rightActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (BR K (a + b) c d)
      (C := (stdTower (K := K) (a + b + (c + d))).carrier)).toRingHom)

theorem right_smul_mk
    (τ : ((stdTower (K := K) (a + b + (c + d))).carrier)ᵐᵒᵖ)
    (u : TowerColumn K a b) (v : BR K (a + b) c d) :
    τ • mk K a b c d u v = mk K a b c d u (τ • v) :=
  rightActionEnd_mk K (stdTower (K := K) (a + b)).carrier
    (TowerColumn K a b) (BR K (a + b) c d) τ u v

/-- The descended grading of `Q5`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (Q5 K a b c d) :=
  relGrading (stdTower (K := K) (a + b)).carrier
    (TowerColumn.grading K a b) (BR.grading K (a + b) c d)

noncomputable instance : DirectSum.Decomposition (grading K a b c d) :=
  relDecomposition (stdTower (K := K) (a + b)).grading
    (TowerColumn.grading K a b) (BR.grading K (a + b) c d)

theorem mk_mem_grading {j k : ZMod 2} {u : TowerColumn K a b}
    {v : BR K (a + b) c d}
    (hu : u ∈ TowerColumn.grading K a b j)
    (hv : v ∈ BR.grading K (a + b) c d k) :
    mk K a b c d u v ∈ grading K a b c d (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (a + b)).carrier)
    (TowerColumn.grading K a b) (BR.grading K (a + b) c d) hu hv

end Q5


/-! ### The slot actions of `Q3` -/

/-- `inferInstanceAs` bridges: `Q3Inner` is the spelled
`B_R(a,b{+}c,d)`, so it inherits its slot and right actions. -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (Q3Inner K a b c d) :=
  inferInstanceAs
    (Module (stdTower (K := K) a).carrier (BR K a (b + c) d))

noncomputable instance : Module (stdTower (K := K) d).carrier
    (Q3Inner K a b c d) :=
  inferInstanceAs
    (Module (stdTower (K := K) d).carrier (BR K a (b + c) d))

noncomputable instance : Module
    ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ
    (Q3Inner K a b c d) :=
  inferInstanceAs (Module
    ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ
    (BR K a (b + c) d))

instance : IsScalarTower K (stdTower (K := K) a).carrier
    (Q3Inner K a b c d) :=
  inferInstanceAs
    (IsScalarTower K (stdTower (K := K) a).carrier (BR K a (b + c) d))

instance : IsScalarTower K (stdTower (K := K) d).carrier
    (Q3Inner K a b c d) :=
  inferInstanceAs
    (IsScalarTower K (stdTower (K := K) d).carrier (BR K a (b + c) d))

instance : IsScalarTower K
    ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ
    (Q3Inner K a b c d) :=
  inferInstanceAs (IsScalarTower K
    ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ
    (BR K a (b + c) d))

instance : SMulCommClass (stdTower (K := K) (b + c)).carrier
    ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ
    (Q3Inner K a b c d) :=
  inferInstanceAs (SMulCommClass (stdTower (K := K) (b + c)).carrier
    ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ
    (BR K a (b + c) d))

/-- The grading of `Q3Inner`, inherited from `B_R(a,b{+}c,d)`. -/
noncomputable abbrev Q3Inner.grading :
    ZMod 2 → Submodule K (Q3Inner K a b c d) :=
  BR.grading K a (b + c) d

noncomputable instance : DirectSum.Decomposition
    (Q3Inner.grading K a b c d) :=
  inferInstanceAs
    (DirectSum.Decomposition (BR.grading K a (b + c) d))

instance : SetLike.GradedSMul (stdTower (K := K) (b + c)).grading
    (Q3Inner.grading K a b c d) :=
  inferInstanceAs (SetLike.GradedSMul
    (stdTower (K := K) (b + c)).grading (BR.grading K a (b + c) d))

/-- The supercommutation data of `Q3Inner`, retyped at its
spelling. -/
private theorem q3InnerCommA :
    SuperCommSMul (stdTower (K := K) (b + c)).grading
      (stdTower (K := K) a).grading (Q3Inner K a b c d) :=
  superCommSMul_symm (stdTower (K := K) a).grading
    (stdTower (K := K) (b + c)).grading
    (BR.superCommSMul_aslot_bslot K a (b + c) d)

private theorem q3InnerCommD :
    SuperCommSMul (stdTower (K := K) (b + c)).grading
      (stdTower (K := K) d).grading (Q3Inner K a b c d) :=
  BR.superCommSMul_bslot_cslot K a (b + c) d

namespace Q3

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    TowerColumn K b c →ₗ[K] Q3Inner K a b c d →ₗ[K] Q3 K a b c d :=
  RelTensor.mk K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
    (Q3Inner K a b c d)

/-- The `T_b`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (Q3 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (Q3Inner K a b c d))
    ((leftActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (Q3Inner K a b c d)
      (B := (stdTower (K := K) b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (stdTower (K := K) b).carrier)
    (u : TowerColumn K b c) (v : Q3Inner K a b c d) :
    y • mk K a b c d u v = mk K a b c d (y • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (Q3Inner K a b c d) y u v

/-- The `T_c`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (Q3 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (Q3Inner K a b c d))
    ((leftActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (Q3Inner K a b c d)
      (B := (stdTower (K := K) c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (stdTower (K := K) c).carrier)
    (u : TowerColumn K b c) (v : Q3Inner K a b c d) :
    z • mk K a b c d u v = mk K a b c d (z • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (Q3Inner K a b c d) z u v

/-- The `T_a`-slot action: the Koszul-signed middle action through
the middle `a`-slot of the `B_R`-factor (mid-of-mid). -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (Q3 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (Q3Inner K a b c d))
    ((midAlgHom (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) (stdTower (K := K) a).grading
      (q3InnerCommA K a b c d)).toRingHom)

/-- The sign law of the `a`-slot of `Q3`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : Q3Inner K a b c d) :
    x • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c d u (x • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (b + c)).grading
    (TowerColumn.grading K b c) (stdTower (K := K) a).grading
    (q3InnerCommA K a b c d) hu hx v

/-- The `T_d`-slot action: the Koszul-signed middle action through
the outer `d`-slot of the `B_R`-factor (mid-of-mid). -/
noncomputable instance : Module (stdTower (K := K) d).carrier
    (Q3 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (Q3Inner K a b c d))
    ((midAlgHom (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) (stdTower (K := K) d).grading
      (q3InnerCommD K a b c d)).toRingHom)

/-- The sign law of the `d`-slot of `Q3`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2}
    {t : (stdTower (K := K) d).carrier}
    (ht : t ∈ (stdTower (K := K) d).grading k)
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : Q3Inner K a b c d) :
    t • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c d u (t • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (b + c)).grading
    (TowerColumn.grading K b c) (stdTower (K := K) d).grading
    (q3InnerCommD K a b c d) hu ht v

/-- The right action of the total coefficient algebra
`T_{a+((b+c)+d)}`. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ
    (Q3 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (Q3Inner K a b c d))
    ((rightActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (Q3Inner K a b c d)
      (C := (stdTower (K := K) (a + ((b + c) + d))).carrier)).toRingHom)

theorem right_smul_mk
    (τ : ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ)
    (u : TowerColumn K b c) (v : Q3Inner K a b c d) :
    τ • mk K a b c d u v = mk K a b c d u (τ • v) :=
  rightActionEnd_mk K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (Q3Inner K a b c d) τ u v

/-- The descended grading of `Q3`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (Q3 K a b c d) :=
  relGrading (stdTower (K := K) (b + c)).carrier
    (TowerColumn.grading K b c) (Q3Inner.grading K a b c d)

noncomputable instance : DirectSum.Decomposition (grading K a b c d) :=
  relDecomposition (stdTower (K := K) (b + c)).grading
    (TowerColumn.grading K b c) (Q3Inner.grading K a b c d)

theorem mk_mem_grading {j k : ZMod 2} {u : TowerColumn K b c}
    {v : Q3Inner K a b c d}
    (hu : u ∈ TowerColumn.grading K b c j)
    (hv : v ∈ Q3Inner.grading K a b c d k) :
    mk K a b c d u v ∈ grading K a b c d (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (b + c)).carrier)
    (TowerColumn.grading K b c) (Q3Inner.grading K a b c d) hu hv

end Q3

end PentagonB

end Bimod

end Superfusion

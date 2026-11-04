/-
Superfusion / Bimod / RouteBimod

Milestone M8a-7c-3: **the two iterated fusions** (§4.1) —

  `B_L = C_{a,b} ⊗_{T_{a+b}} C_{a+b,c}`,
  `B_R = C_{b,c} ⊗_{T_{b+c}} C_{a,b+c}`,

as balanced tensor products of the concrete tower columns, with their
full super-bimodule structure:

* the balancing action is the matching slot action of the second
  column (the `(a+b)`-slot for `B_L`, the `(b+c)`-slot for `B_R` —
  instance resolution picks the correct slot by its index pattern);
* the three **slot actions** of `T_a`, `T_b`, `T_c`: two through the
  outer left action on the first column, one through the
  Koszul-signed middle action (M8a-7a/b) on the second — with the
  supercommutation supplied by `TowerColumn.superCommSMul` (and its
  swap `superCommSMul_symm` for `B_R`, where the middle algebra is
  `T_a`);
* the right action of the total coefficient algebra;
* the descended grading (`relGrading`) with its decomposition.

The paper's `(D_a ⊗̂ D_b ⊗̂ D_c, D_{abc})`-bimodule structure is
recovered slot-wise; the sign convention of the middle slot is the
handoff formula (M8a-7b).  The intertwiner space `Hom(B_L, B_R)` is
the next milestone.
-/
import Superfusion.Bimod.TowerColumn
import Superfusion.Bimod.MiddleActionHom

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c : ZMod 8)

/-! ### The left route `B_L` -/

/-- **`B_L = C_{a,b} ⊗_{T_{a+b}} C_{a+b,c}`** (§4.1): the left iterated
fusion, balanced over the `(a+b)`-slot of the second column. -/
def BL : Type _ :=
  RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
    (TowerColumn K (a + b) c)

namespace BL

noncomputable instance : AddCommGroup (BL K a b c) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c)))

noncomputable instance : Module K (BL K a b c) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c)))

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    TowerColumn K a b →ₗ[K] TowerColumn K (a + b) c →ₗ[K] BL K a b c :=
  RelTensor.mk K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
    (TowerColumn K (a + b) c)

/-- The descended grading of `B_L`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (BL K a b c) :=
  relGrading (stdTower (K := K) (a + b)).carrier
    (TowerColumn.grading K a b) (TowerColumn.grading K (a + b) c)

noncomputable instance : DirectSum.Decomposition (grading K a b c) :=
  relDecomposition (stdTower (K := K) (a + b)).grading
    (TowerColumn.grading K a b) (TowerColumn.grading K (a + b) c)

theorem mk_mem_grading {j k : ZMod 2} {u : TowerColumn K a b}
    {v : TowerColumn K (a + b) c} (hu : u ∈ TowerColumn.grading K a b j)
    (hv : v ∈ TowerColumn.grading K (a + b) c k) :
    mk K a b c u v ∈ grading K a b c (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (a + b)).carrier)
    (TowerColumn.grading K a b) (TowerColumn.grading K (a + b) c) hu hv

/-! #### The three slot actions and the right action -/

/-- The `T_a`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (BL K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c))
    ((leftActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (TowerColumn K (a + b) c)
      (B := (stdTower (K := K) a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (stdTower (K := K) a).carrier)
    (u : TowerColumn K a b) (v : TowerColumn K (a + b) c) :
    x • mk K a b c u v = mk K a b c (x • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b)).carrier
    (TowerColumn K a b) (TowerColumn K (a + b) c) x u v

/-- The `T_b`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (BL K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c))
    ((leftActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (TowerColumn K (a + b) c)
      (B := (stdTower (K := K) b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (stdTower (K := K) b).carrier)
    (u : TowerColumn K a b) (v : TowerColumn K (a + b) c) :
    y • mk K a b c u v = mk K a b c (y • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (a + b)).carrier
    (TowerColumn K a b) (TowerColumn K (a + b) c) y u v

/-- The `T_c`-slot action: the Koszul-signed middle action through the
second column (M8a-7a/b). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (BL K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c))
    ((midAlgHom (stdTower (K := K) (a + b)).grading
      (TowerColumn.grading K a b) (stdTower (K := K) c).grading
      (TowerColumn.superCommSMul K (a + b) c)).toRingHom)

/-- **The sign law of the middle slot** (the handoff convention): for
homogeneous `z`, `u`, `z • (u ⊗ v) = (-1)^{|z||u|} u ⊗ (z • v)`. -/
theorem cslot_smul_mk_of_mem {j k : ZMod 2}
    {z : (stdTower (K := K) c).carrier}
    (hz : z ∈ (stdTower (K := K) c).grading k)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (v : TowerColumn K (a + b) c) :
    z • mk K a b c u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c u (z • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (a + b)).grading
    (TowerColumn.grading K a b) (stdTower (K := K) c).grading
    (TowerColumn.superCommSMul K (a + b) c) hu hz v

/-- The right action of the total coefficient algebra `T_{a+b+c}`. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BL K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c))
    ((rightActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (TowerColumn K (a + b) c)
      (C := (stdTower (K := K) (a + b + c)).carrier)).toRingHom)

theorem right_smul_mk (d : ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ)
    (u : TowerColumn K a b) (v : TowerColumn K (a + b) c) :
    d • mk K a b c u v = mk K a b c u (d • v) :=
  rightActionEnd_mk K (stdTower (K := K) (a + b)).carrier
    (TowerColumn K a b) (TowerColumn K (a + b) c) d u v

end BL

/-! ### The right route `B_R` -/

/-- **`B_R = C_{b,c} ⊗_{T_{b+c}} C_{a,b+c}`** (§4.1): the right
iterated fusion, balanced over the `(b+c)`-slot of the second
column. -/
def BR : Type _ :=
  RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
    (TowerColumn K a (b + c))

namespace BR

noncomputable instance : AddCommGroup (BR K a b c) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c))))

noncomputable instance : Module K (BR K a b c) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c))))

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    TowerColumn K b c →ₗ[K] TowerColumn K a (b + c) →ₗ[K] BR K a b c :=
  RelTensor.mk K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
    (TowerColumn K a (b + c))

/-- The descended grading of `B_R`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (BR K a b c) :=
  relGrading (stdTower (K := K) (b + c)).carrier
    (TowerColumn.grading K b c) (TowerColumn.grading K a (b + c))

noncomputable instance : DirectSum.Decomposition (grading K a b c) :=
  relDecomposition (stdTower (K := K) (b + c)).grading
    (TowerColumn.grading K b c) (TowerColumn.grading K a (b + c))

theorem mk_mem_grading {j k : ZMod 2} {u : TowerColumn K b c}
    {v : TowerColumn K a (b + c)} (hu : u ∈ TowerColumn.grading K b c j)
    (hv : v ∈ TowerColumn.grading K a (b + c) k) :
    mk K a b c u v ∈ grading K a b c (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (b + c)).carrier)
    (TowerColumn.grading K b c) (TowerColumn.grading K a (b + c)) hu hv

/-! #### The three slot actions and the right action -/

/-- The `T_b`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (BR K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c)))
    ((leftActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (TowerColumn K a (b + c))
      (B := (stdTower (K := K) b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (stdTower (K := K) b).carrier)
    (u : TowerColumn K b c) (v : TowerColumn K a (b + c)) :
    y • mk K a b c u v = mk K a b c (y • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (TowerColumn K a (b + c)) y u v

/-- The `T_c`-slot action (through the first column). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (BR K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c)))
    ((leftActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (TowerColumn K a (b + c))
      (B := (stdTower (K := K) c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (stdTower (K := K) c).carrier)
    (u : TowerColumn K b c) (v : TowerColumn K a (b + c)) :
    z • mk K a b c u v = mk K a b c (z • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (TowerColumn K a (b + c)) z u v

/-- The `T_a`-slot action: the Koszul-signed middle action through the
second column, with the swapped supercommutation. -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (BR K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c)))
    ((midAlgHom (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) (stdTower (K := K) a).grading
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (b + c)).grading
        (TowerColumn.superCommSMul K a (b + c)))).toRingHom)

/-- The sign law of the middle slot of `B_R`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K a (b + c)) :
    x • mk K a b c u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c u (x • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (b + c)).grading
    (TowerColumn.grading K b c) (stdTower (K := K) a).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c)).grading
      (TowerColumn.superCommSMul K a (b + c))) hu hx v

/-- The right action of the total coefficient algebra `T_{a+(b+c)}`. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + (b + c))).carrier)ᵐᵒᵖ (BR K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c)))
    ((rightActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (TowerColumn K a (b + c))
      (C := (stdTower (K := K) (a + (b + c))).carrier)).toRingHom)

theorem right_smul_mk
    (d : ((stdTower (K := K) (a + (b + c))).carrier)ᵐᵒᵖ)
    (u : TowerColumn K b c) (v : TowerColumn K a (b + c)) :
    d • mk K a b c u v = mk K a b c u (d • v) :=
  rightActionEnd_mk K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (TowerColumn K a (b + c)) d u v

end BR

end Bimod

end Superfusion

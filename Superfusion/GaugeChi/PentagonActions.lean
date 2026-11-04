/-
Superfusion / GaugeChi / PentagonActions

Milestone M12-4 of the abstract `(p, χ)` arc: **the vertex slot actions** —
the Γ-mirror of `Superfusion.Bimod.QuadActions` (M8a-8c′-2a″), giving each of
the five pentagon vertices `GQ1`, `GQ2`, `GQ3`, `GQ5`, `GQ4r`, `GQ4`
(`GaugeChi.Pentagon`) its four slot actions of `D_a`, `D_b`, `D_c`, `D_d`, the
right action of the total coefficient algebra, and the descended grading.

A preliminary section mirrors `Superfusion.Bimod.RouteCompat` (M8a-8c′-2a),
supplying the slot–coefficient compatibility instances of `GBL`/`GBR`
(`GaugeChi.RouteBimod`) that the vertex-level `leftActionEnd`/`midAlgHom`
constructions need as typeclass arguments: `SMulCommClass` between each slot
action and the (natural, resp. recast) right coefficient action, the
`K`-scalar towers of the slot actions, and — for `GBR`'s own two outer slots
supercommuting with its own signed middle slot (needed at the mid-of-mid
vertices `GQ5`, `GQ4r`, `GQ3`) — the three pairwise `SuperCommSMul`
certificates `GBR.superCommSMul_aslot_bslot`/`_aslot_cslot`/`_bslot_cslot`.
The gradedness of the right actions (`GradedRightSMul`) and the `K`-scalar
towers of the right actions themselves are already registered in
`GaugeChi.GaugeParity`.

Each vertex suite is a verbatim transcription of `QuadActions.lean`'s
corresponding sub-namespace, under the established substitutions
(`stdTower → Γ.D`, `TowerColumn K a b → FusionColumn (Γ.fuse a b)`,
`BL/BR K a b c → GBL/GBR Γ a b c`); `midAlgHom for the outer, mid-of-mid
slots, `leftActionEnd` for the direct ones, per vertex as recorded in the
handoff.  `GQ4r`'s suite (the tower had it in `EdgeEquiv5.lean`, ahead of the
`Q4r`-vertex needing its own slot structure) is included here for
completeness, since `GaugeChi.Pentagon` already has `GQ4r` as a bare type.
-/
import Superfusion.GaugeChi.GaugeParity
import Superfusion.GaugeChi.Pentagon

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

/-! ### Preliminary: `GBL`/`GBR` slot–coefficient compatibility

The Γ-mirror of `Bimod.RouteCompat`'s `BL`/`BR` sections — precisely the
instances the vertex-level `leftActionEnd`/`midAlgHom` constructions below
need as typeclass arguments (`GradedRightSMul` and the `K`-scalar towers of
the right actions themselves are already registered in `GaugeChi.GaugeParity`,
lines building `IsScalarTower K (Γ.D (a+b+c)).carrierᵐᵒᵖ (GBL Γ a b c)` and
its `GBR` natural/recast counterparts). -/

namespace GBL

instance : SMulCommClass (Γ.D a).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  ⟨fun x τ w => by
    show leftActionEnd K (Γ.D (a + b)).carrier
        (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) x
        (rightActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) τ w)
      = rightActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) τ
          (leftActionEnd K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) x w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (Γ.D b).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  ⟨fun y τ w => by
    show leftActionEnd K (Γ.D (a + b)).carrier
        (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) y
        (rightActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) τ w)
      = rightActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) τ
          (leftActionEnd K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) y w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (Γ.D c).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  ⟨fun z τ w => by
    show midEnd (Γ.D (a + b)).grading
        (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) z
        (rightActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) τ w)
      = rightActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) τ
          (midEnd (Γ.D (a + b)).grading
            (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
            (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) z w)
    rw [← Module.End.mul_apply, midEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : IsScalarTower K (Γ.D a).carrier (GBL Γ a b c) :=
  ⟨fun k x w => by
    show leftActionEnd K (Γ.D (a + b)).carrier
        (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) (k • x) w
      = k • leftActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) x w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (Γ.D b).carrier (GBL Γ a b c) :=
  ⟨fun k y w => by
    show leftActionEnd K (Γ.D (a + b)).carrier
        (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) (k • y) w
      = k • leftActionEnd K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) y w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (Γ.D c).carrier (GBL Γ a b c) :=
  ⟨fun k z w => by
    show midAlgHom (Γ.D (a + b)).grading
        (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) (k • z) w
      = k • midAlgHom (Γ.D (a + b)).grading
          (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
          (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) z w
    rw [map_smul, LinearMap.smul_apply]⟩

end GBL

namespace GBR

instance : SMulCommClass (Γ.D b).carrier
    ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun y τ w => by
    show leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y
        (rightActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) τ w)
      = rightActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) τ
          (leftActionEnd K (Γ.D (b + c)).carrier
            (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (Γ.D c).carrier
    ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun z τ w => by
    show leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) z
        (rightActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) τ w)
      = rightActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) τ
          (leftActionEnd K (Γ.D (b + c)).carrier
            (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) z w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (Γ.D a).carrier
    ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun x τ w => by
    show midEnd (Γ.D (b + c)).grading
        (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
        (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
          (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x
        (rightActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) τ w)
      = rightActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) τ
          (midEnd (Γ.D (b + c)).grading
            (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
            (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
              (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x w)
    rw [← Module.End.mul_apply, midEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : IsScalarTower K (Γ.D b).carrier (GBR Γ a b c) :=
  ⟨fun k y w => by
    show leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) (k • y) w
      = k • leftActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (Γ.D c).carrier (GBR Γ a b c) :=
  ⟨fun k z w => by
    show leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) (k • z) w
      = k • leftActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) z w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (Γ.D a).carrier (GBR Γ a b c) :=
  ⟨fun k x w => by
    show midAlgHom (Γ.D (b + c)).grading
        (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
        (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
          (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) (k • x) w
      = k • midAlgHom (Γ.D (b + c)).grading
          (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
          (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
            (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : SMulCommClass (Γ.D b).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun y t w => smul_comm y
    (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) w⟩

instance : SMulCommClass (Γ.D c).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun z t w => smul_comm z
    (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) w⟩

instance : SMulCommClass (Γ.D a).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun x t w => smul_comm x
    (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) w⟩

/-! #### Mid-of-mid supercommutation: the balancing middle slot of `GBR`
supercommutes with its outer slots -/

private theorem zmod2_self_cancel : ∀ i k : ZMod 2, i * k + i * k = 0 := by
  decide

/-- The middle `a`-slot of `GBR` supercommutes with its outer `b`-slot. -/
theorem superCommSMul_aslot_bslot :
    SuperCommSMul (Γ.D a).grading (Γ.D b).grading (GBR Γ a b c) := by
  intro i k x y hx hy w
  have h := leftActionEnd_anticommutes_midAlgHom
    (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
    (Γ.D a).grading (Γ.D b).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c))))
    (⟨y, hy⟩ : (Γ.D b).grading k)
    (⟨x, hx⟩ : (Γ.D a).grading i)
  have h' := congrArg (fun f : Module.End K
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c)))) => f w) h
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h'
  show midAlgHom (Γ.D (b + c)).grading
      (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
      (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
        (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x
      (leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        leftActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y
          (midAlgHom (Γ.D (b + c)).grading
            (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
            (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
              (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x w)
  rw [h', Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_self_cancel, sgn_zero,
    Units.val_one, one_smul]

/-- The middle `a`-slot of `GBR` supercommutes with its outer `c`-slot. -/
theorem superCommSMul_aslot_cslot :
    SuperCommSMul (Γ.D a).grading (Γ.D c).grading (GBR Γ a b c) := by
  intro i k x z hx hz w
  have h := leftActionEnd_anticommutes_midAlgHom
    (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
    (Γ.D a).grading (Γ.D c).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c))))
    (⟨z, hz⟩ : (Γ.D c).grading k)
    (⟨x, hx⟩ : (Γ.D a).grading i)
  have h' := congrArg (fun f : Module.End K
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c)))) => f w) h
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h'
  show midAlgHom (Γ.D (b + c)).grading
      (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
      (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
        (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x
      (leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) z w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        leftActionEnd K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) z
          (midAlgHom (Γ.D (b + c)).grading
            (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
            (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
              (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x w)
  rw [h', Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_self_cancel, sgn_zero,
    Units.val_one, one_smul]

private theorem bslot_cslot_end {i k : ZMod 2}
    {y : (Γ.D b).carrier} {z : (Γ.D c).carrier}
    (hy : y ∈ (Γ.D b).grading i) (hz : z ∈ (Γ.D c).grading k) :
    leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y *
      leftActionEnd K (Γ.D (b + c)).carrier
        (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) z
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (leftActionEnd K (Γ.D (b + c)).carrier
              (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) z *
            leftActionEnd K (Γ.D (b + c)).carrier
              (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y) := by
  refine RelTensor.hom_ext fun u v => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply,
    leftActionEnd_mk, leftActionEnd_mk, leftActionEnd_mk,
    leftActionEnd_mk, FusionColumn.superCommSMul (Γ.fuse b c) hy hz u,
    map_zsmul, LinearMap.smul_apply]

/-- The two outer slots of `GBR` supercommute (the column supercommutation
lifted through the outer left action). -/
theorem superCommSMul_bslot_cslot :
    SuperCommSMul (Γ.D b).grading (Γ.D c).grading (GBR Γ a b c) := by
  intro i k y z hy hz w
  have h' := congrArg (fun f : Module.End K
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c)))) => f w)
    (bslot_cslot_end K Γ a b c hy hz)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h'
  exact h'

/-! #### Gradedness of `GBR`'s three slots -/

instance : SetLike.GradedSMul (Γ.D a).grading (GBR.grading Γ a b c) :=
  ⟨fun _ _ _ _ hx hw => by
    rw [vadd_eq_add]
    exact midEnd_mem_relGrading (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
      (Γ.D a).grading (FusionColumn.grading (Γ.fuse a (b + c)))
      (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
        (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) hx hw⟩

instance : SetLike.GradedSMul (Γ.D b).grading (GBR.grading Γ a b c) :=
  ⟨fun _ _ _ _ hy hw => by
    rw [vadd_eq_add]
    exact leftActionEnd_mem_relGrading (FusionColumn.grading (Γ.fuse b c))
      (FusionColumn.grading (Γ.fuse a (b + c))) hy hw⟩

instance : SetLike.GradedSMul (Γ.D c).grading (GBR.grading Γ a b c) :=
  ⟨fun _ _ _ _ hz hw => by
    rw [vadd_eq_add]
    exact leftActionEnd_mem_relGrading (FusionColumn.grading (Γ.fuse b c))
      (FusionColumn.grading (Γ.fuse a (b + c))) hz hw⟩

end GBR

/-! ### The slot actions of `GQ1` -/

namespace GQ1

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    GBL Γ a b c →ₗ[K] FusionColumn (Γ.fuse (a + b + c) d) →ₗ[K] GQ1 K Γ a b c d :=
  RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d))

/-- The `D_a`-slot action (through the `GBL`-factor). -/
noncomputable instance : Module (Γ.D a).carrier (GQ1 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (Γ.D a).carrier) (u : GBL Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    x • mk K Γ a b c d u v = mk K Γ a b c d (x • u) v :=
  leftActionEnd_mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) x u v

/-- The `D_b`-slot action (through the `GBL`-factor). -/
noncomputable instance : Module (Γ.D b).carrier (GQ1 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (Γ.D b).carrier) (u : GBL Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    y • mk K Γ a b c d u v = mk K Γ a b c d (y • u) v :=
  leftActionEnd_mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) y u v

/-- The `D_c`-slot action (through the `GBL`-factor). -/
noncomputable instance : Module (Γ.D c).carrier (GQ1 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (Γ.D c).carrier) (u : GBL Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    z • mk K Γ a b c d u v = mk K Γ a b c d (z • u) v :=
  leftActionEnd_mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) z u v

/-- The `D_d`-slot action: the Koszul-signed middle action through the
column. -/
noncomputable instance : Module (Γ.D d).carrier (GQ1 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((midAlgHom (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) (Γ.D d).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d))).toRingHom)

/-- The sign law of the `d`-slot: for homogeneous `t`, `u`,
`t • (u ⊗ v) = (-1)^{|t||u|} u ⊗ (t • v)`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2} {t : (Γ.D d).carrier}
    (ht : t ∈ (Γ.D d).grading k) {u : GBL Γ a b c} (hu : u ∈ GBL.grading Γ a b c j)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    t • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (t • v) :=
  midEnd_mk_of_mem (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) (Γ.D d).grading
    (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) hu ht v

/-- The right action of the total coefficient algebra `D_{((a+b)+c)+d}`. -/
noncomputable instance : Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ1 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((rightActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (C := (Γ.D (a + b + c + d)).carrier)).toRingHom)

theorem right_smul_mk (τ : ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ) (u : GBL Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    τ • mk K Γ a b c d u v = mk K Γ a b c d u (τ • v) :=
  rightActionEnd_mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) τ u v

/-- The descended grading of `GQ1`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GQ1 K Γ a b c d) :=
  relGrading (Γ.D (a + b + c)).carrier (GBL.grading Γ a b c)
    (FusionColumn.grading (Γ.fuse (a + b + c) d))

noncomputable instance : DirectSum.Decomposition (grading K Γ a b c d) :=
  relDecomposition (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
    (FusionColumn.grading (Γ.fuse (a + b + c) d))

theorem mk_mem_grading {j k : ZMod 2} {u : GBL Γ a b c}
    {v : FusionColumn (Γ.fuse (a + b + c) d)} (hu : u ∈ GBL.grading Γ a b c j)
    (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) k) :
    mk K Γ a b c d u v ∈ grading K Γ a b c d (j + k) :=
  mk_mem_relGrading (A := (Γ.D (a + b + c)).carrier)
    (GBL.grading Γ a b c) (FusionColumn.grading (Γ.fuse (a + b + c) d)) hu hv

end GQ1

/-! ### The slot actions of `GQ4` -/

namespace GQ4

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    GBR Γ b c d →ₗ[K] FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] GQ4 K Γ a b c d :=
  RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d)))

/-- The `D_b`-slot action (through the `GBR`-factor, over the recast
balancing). -/
noncomputable instance : Module (Γ.D b).carrier (GQ4 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))))
    ((leftActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))) (B := (Γ.D b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (Γ.D b).carrier) (u : GBR Γ b c d)
    (v : FusionColumn (Γ.fuse a (b + c + d))) :
    y • mk K Γ a b c d u v = mk K Γ a b c d (y • u) v :=
  leftActionEnd_mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) y u v

/-- The `D_c`-slot action (through the `GBR`-factor). -/
noncomputable instance : Module (Γ.D c).carrier (GQ4 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))))
    ((leftActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))) (B := (Γ.D c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (Γ.D c).carrier) (u : GBR Γ b c d)
    (v : FusionColumn (Γ.fuse a (b + c + d))) :
    z • mk K Γ a b c d u v = mk K Γ a b c d (z • u) v :=
  leftActionEnd_mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) z u v

/-- The `D_d`-slot action (through the `GBR`-factor). -/
noncomputable instance : Module (Γ.D d).carrier (GQ4 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))))
    ((leftActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))) (B := (Γ.D d).carrier)).toRingHom)

theorem dslot_smul_mk (t : (Γ.D d).carrier) (u : GBR Γ b c d)
    (v : FusionColumn (Γ.fuse a (b + c + d))) :
    t • mk K Γ a b c d u v = mk K Γ a b c d (t • u) v :=
  leftActionEnd_mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) t u v

/-- The `D_a`-slot action: the Koszul-signed middle action through the
column, with the swapped supercommutation. -/
noncomputable instance : Module (Γ.D a).carrier (GQ4 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))))
    ((midAlgHom (Γ.D (b + c + d)).grading (GBR.grading Γ b c d) (Γ.D a).grading
      (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
        (FusionColumn.superCommSMul (Γ.fuse a (b + c + d))))).toRingHom)

/-- The sign law of the `a`-slot of `GQ4`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k) {u : GBR Γ b c d} (hu : u ∈ GBR.grading Γ b c d j)
    (v : FusionColumn (Γ.fuse a (b + c + d))) :
    x • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (x • v) :=
  midEnd_mk_of_mem (Γ.D (b + c + d)).grading (GBR.grading Γ b c d) (Γ.D a).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c + d)))) hu hx v

/-- The right action of the total coefficient algebra `D_{a+((b+c)+d)}`. -/
noncomputable instance : Module ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GQ4 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))))
    ((rightActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))) (C := (Γ.D (a + (b + c + d))).carrier)).toRingHom)

theorem right_smul_mk (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ) (u : GBR Γ b c d)
    (v : FusionColumn (Γ.fuse a (b + c + d))) :
    τ • mk K Γ a b c d u v = mk K Γ a b c d u (τ • v) :=
  rightActionEnd_mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) τ u v

/-- The descended grading of `GQ4`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GQ4 K Γ a b c d) :=
  relGrading (Γ.D (b + c + d)).carrier (GBR.grading Γ b c d)
    (FusionColumn.grading (Γ.fuse a (b + c + d)))

noncomputable instance : DirectSum.Decomposition (grading K Γ a b c d) :=
  relDecomposition (Γ.D (b + c + d)).grading (GBR.grading Γ b c d)
    (FusionColumn.grading (Γ.fuse a (b + c + d)))

theorem mk_mem_grading {j k : ZMod 2} {u : GBR Γ b c d}
    {v : FusionColumn (Γ.fuse a (b + c + d))} (hu : u ∈ GBR.grading Γ b c d j)
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c + d)) k) :
    mk K Γ a b c d u v ∈ grading K Γ a b c d (j + k) :=
  mk_mem_relGrading (A := (Γ.D (b + c + d)).carrier)
    (GBR.grading Γ b c d) (FusionColumn.grading (Γ.fuse a (b + c + d))) hu hv

end GQ4

/-! ### The slot actions of `GQ2` -/

namespace GQ2

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    GBR Γ a b c →ₗ[K] FusionColumn (Γ.fuse (a + b + c) d) →ₗ[K] GQ2 K Γ a b c d :=
  RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d))

/-- The `D_a`-slot action (through the `GBR`-factor, over the recast
balancing). -/
noncomputable instance : Module (Γ.D a).carrier (GQ2 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (Γ.D a).carrier) (u : GBR Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    x • mk K Γ a b c d u v = mk K Γ a b c d (x • u) v :=
  leftActionEnd_mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) x u v

/-- The `D_b`-slot action (through the `GBR`-factor). -/
noncomputable instance : Module (Γ.D b).carrier (GQ2 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (Γ.D b).carrier) (u : GBR Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    y • mk K Γ a b c d u v = mk K Γ a b c d (y • u) v :=
  leftActionEnd_mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) y u v

/-- The `D_c`-slot action (through the `GBR`-factor). -/
noncomputable instance : Module (Γ.D c).carrier (GQ2 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (Γ.D c).carrier) (u : GBR Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    z • mk K Γ a b c d u v = mk K Γ a b c d (z • u) v :=
  leftActionEnd_mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) z u v

/-- The `D_d`-slot action: the Koszul-signed middle action through the
column. -/
noncomputable instance : Module (Γ.D d).carrier (GQ2 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((midAlgHom (Γ.D (a + b + c)).grading (GBR.grading Γ a b c) (Γ.D d).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d))).toRingHom)

/-- The sign law of the `d`-slot of `GQ2`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2} {t : (Γ.D d).carrier}
    (ht : t ∈ (Γ.D d).grading k) {u : GBR Γ a b c} (hu : u ∈ GBR.grading Γ a b c j)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    t • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (t • v) :=
  midEnd_mk_of_mem (Γ.D (a + b + c)).grading (GBR.grading Γ a b c) (Γ.D d).grading
    (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) hu ht v

/-- The right action of the total coefficient algebra `D_{((a+b)+c)+d}`. -/
noncomputable instance : Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ2 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)))
    ((rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (C := (Γ.D (a + b + c + d)).carrier)).toRingHom)

theorem right_smul_mk (τ : ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ) (u : GBR Γ a b c)
    (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    τ • mk K Γ a b c d u v = mk K Γ a b c d u (τ • v) :=
  rightActionEnd_mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
    (FusionColumn (Γ.fuse (a + b + c) d)) τ u v

/-- The descended grading of `GQ2`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GQ2 K Γ a b c d) :=
  relGrading (Γ.D (a + b + c)).carrier (GBR.grading Γ a b c)
    (FusionColumn.grading (Γ.fuse (a + b + c) d))

noncomputable instance : DirectSum.Decomposition (grading K Γ a b c d) :=
  relDecomposition (Γ.D (a + b + c)).grading (GBR.grading Γ a b c)
    (FusionColumn.grading (Γ.fuse (a + b + c) d))

theorem mk_mem_grading {j k : ZMod 2} {u : GBR Γ a b c}
    {v : FusionColumn (Γ.fuse (a + b + c) d)} (hu : u ∈ GBR.grading Γ a b c j)
    (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) k) :
    mk K Γ a b c d u v ∈ grading K Γ a b c d (j + k) :=
  mk_mem_relGrading (A := (Γ.D (a + b + c)).carrier)
    (GBR.grading Γ a b c) (FusionColumn.grading (Γ.fuse (a + b + c) d)) hu hv

end GQ2

/-! ### The slot actions of `GQ5` -/

namespace GQ5

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    FusionColumn (Γ.fuse a b) →ₗ[K] GBR Γ (a + b) c d →ₗ[K] GQ5 K Γ a b c d :=
  RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)

/-- The `D_a`-slot action (through the first column). -/
noncomputable instance : Module (Γ.D a).carrier (GQ5 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d))
    ((leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)
      (B := (Γ.D a).carrier)).toRingHom)

theorem aslot_smul_mk (x : (Γ.D a).carrier) (u : FusionColumn (Γ.fuse a b))
    (v : GBR Γ (a + b) c d) :
    x • mk K Γ a b c d u v = mk K Γ a b c d (x • u) v :=
  leftActionEnd_mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
    (GBR Γ (a + b) c d) x u v

/-- The `D_b`-slot action (through the first column). -/
noncomputable instance : Module (Γ.D b).carrier (GQ5 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d))
    ((leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)
      (B := (Γ.D b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (Γ.D b).carrier) (u : FusionColumn (Γ.fuse a b))
    (v : GBR Γ (a + b) c d) :
    y • mk K Γ a b c d u v = mk K Γ a b c d (y • u) v :=
  leftActionEnd_mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
    (GBR Γ (a + b) c d) y u v

/-- The `D_c`-slot action: the Koszul-signed middle action through the
outer `c`-slot of the `GBR`-factor (mid-of-mid). -/
noncomputable instance : Module (Γ.D c).carrier (GQ5 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d))
    ((midAlgHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
      (GBR.superCommSMul_aslot_bslot K Γ (a + b) c d)).toRingHom)

/-- The sign law of the `c`-slot of `GQ5`. -/
theorem cslot_smul_mk_of_mem {j k : ZMod 2} {z : (Γ.D c).carrier}
    (hz : z ∈ (Γ.D c).grading k) {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j) (v : GBR Γ (a + b) c d) :
    z • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (z • v) :=
  midEnd_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
    (GBR.superCommSMul_aslot_bslot K Γ (a + b) c d) hu hz v

/-- The `D_d`-slot action: the Koszul-signed middle action through the
outer `d`-slot of the `GBR`-factor (mid-of-mid). -/
noncomputable instance : Module (Γ.D d).carrier (GQ5 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d))
    ((midAlgHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D d).grading
      (GBR.superCommSMul_aslot_cslot K Γ (a + b) c d)).toRingHom)

/-- The sign law of the `d`-slot of `GQ5`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2} {t : (Γ.D d).carrier}
    (ht : t ∈ (Γ.D d).grading k) {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j) (v : GBR Γ (a + b) c d) :
    t • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (t • v) :=
  midEnd_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D d).grading
    (GBR.superCommSMul_aslot_cslot K Γ (a + b) c d) hu ht v

/-- The right action of the total coefficient algebra `D_{(a+b)+(c+d)}`. -/
noncomputable instance : Module ((Γ.D (a + b + (c + d))).carrier)ᵐᵒᵖ (GQ5 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d))
    ((rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)
      (C := (Γ.D (a + b + (c + d))).carrier)).toRingHom)

theorem right_smul_mk (τ : ((Γ.D (a + b + (c + d))).carrier)ᵐᵒᵖ)
    (u : FusionColumn (Γ.fuse a b)) (v : GBR Γ (a + b) c d) :
    τ • mk K Γ a b c d u v = mk K Γ a b c d u (τ • v) :=
  rightActionEnd_mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
    (GBR Γ (a + b) c d) τ u v

/-- The descended grading of `GQ5`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GQ5 K Γ a b c d) :=
  relGrading (Γ.D (a + b)).carrier (FusionColumn.grading (Γ.fuse a b)) (GBR.grading Γ (a + b) c d)

noncomputable instance : DirectSum.Decomposition (grading K Γ a b c d) :=
  relDecomposition (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    (GBR.grading Γ (a + b) c d)

theorem mk_mem_grading {j k : ZMod 2} {u : FusionColumn (Γ.fuse a b)} {v : GBR Γ (a + b) c d}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j) (hv : v ∈ GBR.grading Γ (a + b) c d k) :
    mk K Γ a b c d u v ∈ grading K Γ a b c d (j + k) :=
  mk_mem_relGrading (A := (Γ.D (a + b)).carrier)
    (FusionColumn.grading (Γ.fuse a b)) (GBR.grading Γ (a + b) c d) hu hv

end GQ5

/-! ### The slot actions of `GQ4r`

`GQ4r`'s own structure mirrors `GQ5`'s exactly: outer `FusionColumn (Γ.fuse c
d)` factor (direct `D_c`, `D_d`-slots), inner `GBR Γ a b (c+d)` factor
(signed mid-of-mid `D_a`-, `D_b`-slots, keyed against the outer column's
degree), and a right action matching `GBR Γ a b (c+d)`'s own natural right
tower `D_{a+(b+(c+d))}`.  The Γ-mirror of `EdgeEquiv5.lean`'s `Q4r`
namespace. -/

namespace GQ4r

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    FusionColumn (Γ.fuse c d) →ₗ[K] GBR Γ a b (c + d) →ₗ[K] GQ4r K Γ a b c d :=
  RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))

/-- The `D_c`-slot action (through the outer column). -/
noncomputable instance : Module (Γ.D c).carrier (GQ4r K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)))
    ((leftActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))
      (B := (Γ.D c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (Γ.D c).carrier) (u : FusionColumn (Γ.fuse c d))
    (v : GBR Γ a b (c + d)) :
    z • mk K Γ a b c d u v = mk K Γ a b c d (z • u) v :=
  leftActionEnd_mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
    (GBR Γ a b (c + d)) z u v

/-- The `D_d`-slot action (through the outer column). -/
noncomputable instance : Module (Γ.D d).carrier (GQ4r K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)))
    ((leftActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))
      (B := (Γ.D d).carrier)).toRingHom)

theorem dslot_smul_mk (t : (Γ.D d).carrier) (u : FusionColumn (Γ.fuse c d))
    (v : GBR Γ a b (c + d)) :
    t • mk K Γ a b c d u v = mk K Γ a b c d (t • u) v :=
  leftActionEnd_mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
    (GBR Γ a b (c + d)) t u v

/-- The `D_a`-slot action: the Koszul-signed middle action through the
`a`-slot of the `GBR Γ a b (c+d)`-factor (mid-of-mid). -/
noncomputable instance : Module (Γ.D a).carrier (GQ4r K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)))
    ((midAlgHom (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D a).grading
      (superCommSMul_symm (Γ.D a).grading (Γ.D (c + d)).grading
        (GBR.superCommSMul_aslot_cslot K Γ a b (c + d)))).toRingHom)

/-- The sign law of the `a`-slot of `GQ4r`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k) {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) j) (v : GBR Γ a b (c + d)) :
    x • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (x • v) :=
  midEnd_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D a).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (c + d)).grading
      (GBR.superCommSMul_aslot_cslot K Γ a b (c + d))) hu hx v

/-- The `D_b`-slot action: the Koszul-signed middle action through the
`b`-slot of the `GBR Γ a b (c+d)`-factor (mid-of-mid). -/
noncomputable instance : Module (Γ.D b).carrier (GQ4r K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)))
    ((midAlgHom (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D b).grading
      (superCommSMul_symm (Γ.D b).grading (Γ.D (c + d)).grading
        (GBR.superCommSMul_bslot_cslot K Γ a b (c + d)))).toRingHom)

/-- The sign law of the `b`-slot of `GQ4r`. -/
theorem bslot_smul_mk_of_mem {j k : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading k) {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) j) (v : GBR Γ a b (c + d)) :
    y • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (y • v) :=
  midEnd_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D b).grading
    (superCommSMul_symm (Γ.D b).grading (Γ.D (c + d)).grading
      (GBR.superCommSMul_bslot_cslot K Γ a b (c + d))) hu hy v

/-- The right action of the total coefficient algebra `D_{a+(b+(c+d))}`,
matching `GBR Γ a b (c+d)`'s own natural right tower. -/
noncomputable instance : Module ((Γ.D (a + (b + (c + d)))).carrier)ᵐᵒᵖ (GQ4r K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)))
    ((rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))
      (C := (Γ.D (a + (b + (c + d)))).carrier)).toRingHom)

theorem right_smul_mk (τ : ((Γ.D (a + (b + (c + d)))).carrier)ᵐᵒᵖ)
    (u : FusionColumn (Γ.fuse c d)) (v : GBR Γ a b (c + d)) :
    τ • mk K Γ a b c d u v = mk K Γ a b c d u (τ • v) :=
  rightActionEnd_mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
    (GBR Γ a b (c + d)) τ u v

/-- The descended grading of `GQ4r`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GQ4r K Γ a b c d) :=
  relGrading (Γ.D (c + d)).carrier (FusionColumn.grading (Γ.fuse c d)) (GBR.grading Γ a b (c + d))

noncomputable instance : DirectSum.Decomposition (grading K Γ a b c d) :=
  relDecomposition (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
    (GBR.grading Γ a b (c + d))

theorem mk_mem_grading {j k : ZMod 2} {u : FusionColumn (Γ.fuse c d)} {v : GBR Γ a b (c + d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) j) (hv : v ∈ GBR.grading Γ a b (c + d) k) :
    mk K Γ a b c d u v ∈ grading K Γ a b c d (j + k) :=
  mk_mem_relGrading (A := (Γ.D (c + d)).carrier)
    (FusionColumn.grading (Γ.fuse c d)) (GBR.grading Γ a b (c + d)) hu hv

end GQ4r

/-! ### The slot actions of `GQ3` -/

/-- `inferInstanceAs` bridges: `GQ3Inner` is the spelled `GBR Γ a (b+c) d`, so
it inherits its slot and right actions. -/
noncomputable instance : Module (Γ.D a).carrier (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (Module (Γ.D a).carrier (GBR Γ a (b + c) d))

noncomputable instance : Module (Γ.D d).carrier (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (Module (Γ.D d).carrier (GBR Γ a (b + c) d))

noncomputable instance : Module ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (Module ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GBR Γ a (b + c) d))

instance : IsScalarTower K (Γ.D a).carrier (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (IsScalarTower K (Γ.D a).carrier (GBR Γ a (b + c) d))

instance : IsScalarTower K (Γ.D d).carrier (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (IsScalarTower K (Γ.D d).carrier (GBR Γ a (b + c) d))

instance : IsScalarTower K ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (IsScalarTower K ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GBR Γ a (b + c) d))

instance : SMulCommClass (Γ.D (b + c)).carrier
    ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GQ3Inner K Γ a b c d) :=
  inferInstanceAs (SMulCommClass (Γ.D (b + c)).carrier
    ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GBR Γ a (b + c) d))

/-- The grading of `GQ3Inner`, inherited from `GBR Γ a (b+c) d`. -/
noncomputable abbrev GQ3Inner.grading : ZMod 2 → Submodule K (GQ3Inner K Γ a b c d) :=
  GBR.grading Γ a (b + c) d

noncomputable instance : DirectSum.Decomposition (GQ3Inner.grading K Γ a b c d) :=
  inferInstanceAs (DirectSum.Decomposition (GBR.grading Γ a (b + c) d))

instance : SetLike.GradedSMul (Γ.D (b + c)).grading (GQ3Inner.grading K Γ a b c d) :=
  inferInstanceAs (SetLike.GradedSMul (Γ.D (b + c)).grading (GBR.grading Γ a (b + c) d))

/-- The supercommutation data of `GQ3Inner`, retyped at its spelling. -/
private theorem q3InnerCommA :
    SuperCommSMul (Γ.D (b + c)).grading (Γ.D a).grading (GQ3Inner K Γ a b c d) :=
  superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
    (GBR.superCommSMul_aslot_bslot K Γ a (b + c) d)

private theorem q3InnerCommD :
    SuperCommSMul (Γ.D (b + c)).grading (Γ.D d).grading (GQ3Inner K Γ a b c d) :=
  GBR.superCommSMul_bslot_cslot K Γ a (b + c) d

namespace GQ3

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    FusionColumn (Γ.fuse b c) →ₗ[K] GQ3Inner K Γ a b c d →ₗ[K] GQ3 K Γ a b c d :=
  RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)

/-- The `D_b`-slot action (through the first column). -/
noncomputable instance : Module (Γ.D b).carrier (GQ3 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d))
    ((leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)
      (B := (Γ.D b).carrier)).toRingHom)

theorem bslot_smul_mk (y : (Γ.D b).carrier) (u : FusionColumn (Γ.fuse b c))
    (v : GQ3Inner K Γ a b c d) :
    y • mk K Γ a b c d u v = mk K Γ a b c d (y • u) v :=
  leftActionEnd_mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (GQ3Inner K Γ a b c d) y u v

/-- The `D_c`-slot action (through the first column). -/
noncomputable instance : Module (Γ.D c).carrier (GQ3 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d))
    ((leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)
      (B := (Γ.D c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (Γ.D c).carrier) (u : FusionColumn (Γ.fuse b c))
    (v : GQ3Inner K Γ a b c d) :
    z • mk K Γ a b c d u v = mk K Γ a b c d (z • u) v :=
  leftActionEnd_mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (GQ3Inner K Γ a b c d) z u v

/-- The `D_a`-slot action: the Koszul-signed middle action through the
middle `a`-slot of the `GBR`-factor (mid-of-mid). -/
noncomputable instance : Module (Γ.D a).carrier (GQ3 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d))
    ((midAlgHom (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
      (q3InnerCommA K Γ a b c d)).toRingHom)

/-- The sign law of the `a`-slot of `GQ3`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k) {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j) (v : GQ3Inner K Γ a b c d) :
    x • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (x • v) :=
  midEnd_mk_of_mem (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
    (q3InnerCommA K Γ a b c d) hu hx v

/-- The `D_d`-slot action: the Koszul-signed middle action through the
outer `d`-slot of the `GBR`-factor (mid-of-mid). -/
noncomputable instance : Module (Γ.D d).carrier (GQ3 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d))
    ((midAlgHom (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D d).grading
      (q3InnerCommD K Γ a b c d)).toRingHom)

/-- The sign law of the `d`-slot of `GQ3`. -/
theorem dslot_smul_mk_of_mem {j k : ZMod 2} {t : (Γ.D d).carrier}
    (ht : t ∈ (Γ.D d).grading k) {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j) (v : GQ3Inner K Γ a b c d) :
    t • mk K Γ a b c d u v = ((sgn (k * j) : ℤˣ) : ℤ) • mk K Γ a b c d u (t • v) :=
  midEnd_mk_of_mem (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D d).grading
    (q3InnerCommD K Γ a b c d) hu ht v

/-- The right action of the total coefficient algebra `D_{a+((b+c)+d)}`. -/
noncomputable instance : Module ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GQ3 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d))
    ((rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)
      (C := (Γ.D (a + (b + c + d))).carrier)).toRingHom)

theorem right_smul_mk (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (u : FusionColumn (Γ.fuse b c)) (v : GQ3Inner K Γ a b c d) :
    τ • mk K Γ a b c d u v = mk K Γ a b c d u (τ • v) :=
  rightActionEnd_mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (GQ3Inner K Γ a b c d) τ u v

/-- The descended grading of `GQ3`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (GQ3 K Γ a b c d) :=
  relGrading (Γ.D (b + c)).carrier (FusionColumn.grading (Γ.fuse b c)) (GQ3Inner.grading K Γ a b c d)

noncomputable instance : DirectSum.Decomposition (grading K Γ a b c d) :=
  relDecomposition (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
    (GQ3Inner.grading K Γ a b c d)

theorem mk_mem_grading {j k : ZMod 2} {u : FusionColumn (Γ.fuse b c)} {v : GQ3Inner K Γ a b c d}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j) (hv : v ∈ GQ3Inner.grading K Γ a b c d k) :
    mk K Γ a b c d u v ∈ grading K Γ a b c d (j + k) :=
  mk_mem_relGrading (A := (Γ.D (b + c)).carrier)
    (FusionColumn.grading (Γ.fuse b c)) (GQ3Inner.grading K Γ a b c d) hu hv

end GQ3

end GaugeChi

end Superfusion

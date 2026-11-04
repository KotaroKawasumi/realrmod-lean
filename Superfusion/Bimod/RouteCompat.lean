/-
Superfusion / Bimod / RouteCompat

Milestone M8a-8c′-2a (roadmap v3): **slot–coefficient compatibility
of the route bimodules** — the instance infrastructure needed to put
the four slot actions on the pentagon vertices (`Q1`, `Q4`, …):

* the three slot actions of `B_L` (outer `T_a`, `T_b`, middle `T_c`)
  commute with its right coefficient action (`SMulCommClass`), and
  likewise for `B_R` — for both its *natural* right action
  (`T_{a+(b+c)}`) and the *recast* one (`T_{(a+b)+c}`, M8a-8c′-0);
* the slot actions are `K`-scalar towers (`IsScalarTower`);
* the right coefficient actions are graded
  (`GradedRightSMul … (BL.grading …)`, natural and recast — the
  recast case through `stdTowerCast_mem_grading`).

All proofs descend from the `End`-level commutation theorems
(`leftActionEnd_comm_rightActionEnd`, `midEnd_comm_rightActionEnd`)
and the gradedness of the outer right action
(`rightActionEnd_mem_relGrading`); the `compHom`-based `smul`s are
bridged by `show` at the `End`-application level, as everywhere.
-/
import Superfusion.Bimod.QuadClose

namespace Superfusion

namespace Bimod

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c : ZMod 8)

/-! ### `B_L`: slot–coefficient compatibility -/

namespace BL

instance : SMulCommClass (stdTower (K := K) a).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BL K a b c) :=
  ⟨fun x τ w => by
    show leftActionEnd K (stdTower (K := K) (a + b)).carrier
        (TowerColumn K a b) (TowerColumn K (a + b) c) x
        (rightActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) τ w)
      = rightActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) τ
          (leftActionEnd K (stdTower (K := K) (a + b)).carrier
            (TowerColumn K a b) (TowerColumn K (a + b) c) x w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (stdTower (K := K) b).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BL K a b c) :=
  ⟨fun y τ w => by
    show leftActionEnd K (stdTower (K := K) (a + b)).carrier
        (TowerColumn K a b) (TowerColumn K (a + b) c) y
        (rightActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) τ w)
      = rightActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) τ
          (leftActionEnd K (stdTower (K := K) (a + b)).carrier
            (TowerColumn K a b) (TowerColumn K (a + b) c) y w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (stdTower (K := K) c).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BL K a b c) :=
  ⟨fun z τ w => by
    show midEnd (stdTower (K := K) (a + b)).grading
        (TowerColumn.grading K a b) (stdTower (K := K) c).grading
        (TowerColumn.superCommSMul K (a + b) c) z
        (rightActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) τ w)
      = rightActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) τ
          (midEnd (stdTower (K := K) (a + b)).grading
            (TowerColumn.grading K a b) (stdTower (K := K) c).grading
            (TowerColumn.superCommSMul K (a + b) c) z w)
    rw [← Module.End.mul_apply, midEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : IsScalarTower K (stdTower (K := K) a).carrier (BL K a b c) :=
  ⟨fun k x w => by
    show leftActionEnd K (stdTower (K := K) (a + b)).carrier
        (TowerColumn K a b) (TowerColumn K (a + b) c) (k • x) w
      = k • leftActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) x w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (stdTower (K := K) b).carrier (BL K a b c) :=
  ⟨fun k y w => by
    show leftActionEnd K (stdTower (K := K) (a + b)).carrier
        (TowerColumn K a b) (TowerColumn K (a + b) c) (k • y) w
      = k • leftActionEnd K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (TowerColumn K (a + b) c) y w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (stdTower (K := K) c).carrier (BL K a b c) :=
  ⟨fun k z w => by
    show midAlgHom (stdTower (K := K) (a + b)).grading
        (TowerColumn.grading K a b) (stdTower (K := K) c).grading
        (TowerColumn.superCommSMul K (a + b) c) (k • z) w
      = k • midAlgHom (stdTower (K := K) (a + b)).grading
          (TowerColumn.grading K a b) (stdTower (K := K) c).grading
          (TowerColumn.superCommSMul K (a + b) c) z w
    rw [map_smul, LinearMap.smul_apply]⟩

/-- The right coefficient action of `B_L` is graded. -/
instance : GradedRightSMul (stdTower (K := K) (a + b + c)).grading
    (BL.grading K a b c) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (TowerColumn.grading K a b)
      (TowerColumn.grading K (a + b) c) hτ hw

end BL

/-! ### `B_R`: slot–coefficient compatibility (natural coefficients) -/

namespace BR

instance : SMulCommClass (stdTower (K := K) b).carrier
    ((stdTower (K := K) (a + (b + c))).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun y τ w => by
    show leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) y
        (rightActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) τ w)
      = rightActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) τ
          (leftActionEnd K (stdTower (K := K) (b + c)).carrier
            (TowerColumn K b c) (TowerColumn K a (b + c)) y w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (stdTower (K := K) c).carrier
    ((stdTower (K := K) (a + (b + c))).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun z τ w => by
    show leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) z
        (rightActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) τ w)
      = rightActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) τ
          (leftActionEnd K (stdTower (K := K) (b + c)).carrier
            (TowerColumn K b c) (TowerColumn K a (b + c)) z w)
    rw [← Module.End.mul_apply, leftActionEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : SMulCommClass (stdTower (K := K) a).carrier
    ((stdTower (K := K) (a + (b + c))).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun x τ w => by
    show midEnd (stdTower (K := K) (b + c)).grading
        (TowerColumn.grading K b c) (stdTower (K := K) a).grading
        (superCommSMul_symm (stdTower (K := K) a).grading
          (stdTower (K := K) (b + c)).grading
          (TowerColumn.superCommSMul K a (b + c))) x
        (rightActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) τ w)
      = rightActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) τ
          (midEnd (stdTower (K := K) (b + c)).grading
            (TowerColumn.grading K b c) (stdTower (K := K) a).grading
            (superCommSMul_symm (stdTower (K := K) a).grading
              (stdTower (K := K) (b + c)).grading
              (TowerColumn.superCommSMul K a (b + c))) x w)
    rw [← Module.End.mul_apply, midEnd_comm_rightActionEnd,
      Module.End.mul_apply]⟩

instance : IsScalarTower K (stdTower (K := K) b).carrier (BR K a b c) :=
  ⟨fun k y w => by
    show leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) (k • y) w
      = k • leftActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) y w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (stdTower (K := K) c).carrier (BR K a b c) :=
  ⟨fun k z w => by
    show leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) (k • z) w
      = k • leftActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) z w
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (stdTower (K := K) a).carrier (BR K a b c) :=
  ⟨fun k x w => by
    show midAlgHom (stdTower (K := K) (b + c)).grading
        (TowerColumn.grading K b c) (stdTower (K := K) a).grading
        (superCommSMul_symm (stdTower (K := K) a).grading
          (stdTower (K := K) (b + c)).grading
          (TowerColumn.superCommSMul K a (b + c))) (k • x) w
      = k • midAlgHom (stdTower (K := K) (b + c)).grading
          (TowerColumn.grading K b c) (stdTower (K := K) a).grading
          (superCommSMul_symm (stdTower (K := K) a).grading
            (stdTower (K := K) (b + c)).grading
            (TowerColumn.superCommSMul K a (b + c))) x w
    rw [map_smul, LinearMap.smul_apply]⟩

/-- The natural right coefficient action of `B_R` is graded. -/
instance : GradedRightSMul (stdTower (K := K) (a + (b + c))).grading
    (BR.grading K a b c) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (TowerColumn.grading K b c)
      (TowerColumn.grading K a (b + c)) hτ hw

/-! ### `B_R`: slot–coefficient compatibility (recast coefficients) -/

instance : SMulCommClass (stdTower (K := K) b).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun y t w => smul_comm y
    (MulOpposite.op ((stdTowerCast (K := K)
      (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) w⟩

instance : SMulCommClass (stdTower (K := K) c).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun z t w => smul_comm z
    (MulOpposite.op ((stdTowerCast (K := K)
      (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) w⟩

instance : SMulCommClass (stdTower (K := K) a).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun x t w => smul_comm x
    (MulOpposite.op ((stdTowerCast (K := K)
      (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) w⟩

/-- The recast right coefficient action of `B_R` is graded (through
the grading-preservation of the tower cast). -/
instance : GradedRightSMul (stdTower (K := K) (a + b + c)).grading
    (BR.grading K a b c) where
  smul_mem _ _ _ _ hτ hw := by
    rw [BR.recast_op_smul_def]
    exact GradedRightSMul.smul_mem
      (stdTowerCast_mem_grading K (add_assoc a b c) hτ) hw


/-! ### Mid-of-mid supercommutation: the balancing middle slot of
`B_R` supercommutes with its outer slots -/

private theorem zmod2_self_cancel : ∀ i k : ZMod 2, i * k + i * k = 0 := by
  decide

/-- The middle `a`-slot of `B_R` supercommutes with its outer
`b`-slot — the `SuperCommSMul` datum for lifting the outer slots of
an inner `B_R` through a signed middle action (the mid-of-mid
pattern of the pentagon vertices `Q3`, `Q5`). -/
theorem superCommSMul_aslot_bslot :
    SuperCommSMul (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading (BR K a b c) := by
  intro i k x y hx hy w
  have h := leftActionEnd_anticommutes_midAlgHom
    (stdTower (K := K) (b + c)).grading (TowerColumn.grading K b c)
    (stdTower (K := K) a).grading (stdTower (K := K) b).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c)).grading
      (TowerColumn.superCommSMul K a (b + c)))
    (⟨y, hy⟩ : (stdTower (K := K) b).grading k)
    (⟨x, hx⟩ : (stdTower (K := K) a).grading i)
  have h' := congrArg (fun f : Module.End K
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c))) => f w) h
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h'
  show midAlgHom (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) (stdTower (K := K) a).grading
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (b + c)).grading
        (TowerColumn.superCommSMul K a (b + c))) x
      (leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) y w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        leftActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) y
          (midAlgHom (stdTower (K := K) (b + c)).grading
            (TowerColumn.grading K b c) (stdTower (K := K) a).grading
            (superCommSMul_symm (stdTower (K := K) a).grading
              (stdTower (K := K) (b + c)).grading
              (TowerColumn.superCommSMul K a (b + c))) x w)
  rw [h', Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_self_cancel, sgn_zero,
    Units.val_one, one_smul]

/-- The middle `a`-slot of `B_R` supercommutes with its outer
`c`-slot. -/
theorem superCommSMul_aslot_cslot :
    SuperCommSMul (stdTower (K := K) a).grading
      (stdTower (K := K) c).grading (BR K a b c) := by
  intro i k x z hx hz w
  have h := leftActionEnd_anticommutes_midAlgHom
    (stdTower (K := K) (b + c)).grading (TowerColumn.grading K b c)
    (stdTower (K := K) a).grading (stdTower (K := K) c).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c)).grading
      (TowerColumn.superCommSMul K a (b + c)))
    (⟨z, hz⟩ : (stdTower (K := K) c).grading k)
    (⟨x, hx⟩ : (stdTower (K := K) a).grading i)
  have h' := congrArg (fun f : Module.End K
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c))) => f w) h
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h'
  show midAlgHom (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) (stdTower (K := K) a).grading
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (b + c)).grading
        (TowerColumn.superCommSMul K a (b + c))) x
      (leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) z w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        leftActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) z
          (midAlgHom (stdTower (K := K) (b + c)).grading
            (TowerColumn.grading K b c) (stdTower (K := K) a).grading
            (superCommSMul_symm (stdTower (K := K) a).grading
              (stdTower (K := K) (b + c)).grading
              (TowerColumn.superCommSMul K a (b + c))) x w)
  rw [h', Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_self_cancel, sgn_zero,
    Units.val_one, one_smul]

/-- The `K`-scalar tower of the natural right coefficient action. -/
instance : IsScalarTower K
    ((stdTower (K := K) (a + (b + c))).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun k τ w => by
    show rightActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) (k • τ) w
      = k • rightActionEnd K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (TowerColumn K a (b + c)) τ w
    rw [map_smul, LinearMap.smul_apply]⟩


private theorem bslot_cslot_end {i k : ZMod 2}
    {y : (stdTower (K := K) b).carrier}
    {z : (stdTower (K := K) c).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading i)
    (hz : z ∈ (stdTower (K := K) c).grading k) :
    leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) y *
      leftActionEnd K (stdTower (K := K) (b + c)).carrier
        (TowerColumn K b c) (TowerColumn K a (b + c)) z
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (leftActionEnd K (stdTower (K := K) (b + c)).carrier
              (TowerColumn K b c) (TowerColumn K a (b + c)) z *
            leftActionEnd K (stdTower (K := K) (b + c)).carrier
              (TowerColumn K b c) (TowerColumn K a (b + c)) y) := by
  refine RelTensor.hom_ext fun u v => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply,
    leftActionEnd_mk, leftActionEnd_mk, leftActionEnd_mk,
    leftActionEnd_mk, TowerColumn.superCommSMul K b c hy hz u,
    map_zsmul, LinearMap.smul_apply]

/-- The two outer slots of `B_R` supercommute (the column
supercommutation lifted through the outer left action). -/
theorem superCommSMul_bslot_cslot :
    SuperCommSMul (stdTower (K := K) b).grading
      (stdTower (K := K) c).grading (BR K a b c) := by
  intro i k y z hy hz w
  have h' := congrArg (fun f : Module.End K
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (TowerColumn K a (b + c))) => f w)
    (bslot_cslot_end K a b c hy hz)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h'
  exact h'


/-- The middle `a`-slot of `B_R` is graded. -/
instance : SetLike.GradedSMul (stdTower (K := K) a).grading
    (BR.grading K a b c) :=
  ⟨fun _ _ _ _ hx hw => by
    rw [vadd_eq_add]
    exact midEnd_mem_relGrading (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) (stdTower (K := K) a).grading
      (TowerColumn.grading K a (b + c))
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (b + c)).grading
        (TowerColumn.superCommSMul K a (b + c))) hx hw⟩

/-- The outer `b`-slot of `B_R` is graded. -/
instance : SetLike.GradedSMul (stdTower (K := K) b).grading
    (BR.grading K a b c) :=
  ⟨fun _ _ _ _ hy hw => by
    rw [vadd_eq_add]
    exact leftActionEnd_mem_relGrading (TowerColumn.grading K b c)
      (TowerColumn.grading K a (b + c)) hy hw⟩

/-- The outer `c`-slot of `B_R` is graded. -/
instance : SetLike.GradedSMul (stdTower (K := K) c).grading
    (BR.grading K a b c) :=
  ⟨fun _ _ _ _ hz hw => by
    rw [vadd_eq_add]
    exact leftActionEnd_mem_relGrading (TowerColumn.grading K b c)
      (TowerColumn.grading K a (b + c)) hz hw⟩

end BR

end Bimod

end Superfusion

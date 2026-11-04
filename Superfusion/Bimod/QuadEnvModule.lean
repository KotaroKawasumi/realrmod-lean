/-
Superfusion / Bimod / QuadEnvModule

Milestone M8a-8d′-iii-a (roadmap v3, continued): **the `QuadEnv`-module
structure on `Q1`**, assembled by iterating
`GtensorLeftActionGraded.lean`'s general lemmas twice.

* **Level 1** (`namespace BL`): `B_L`'s own outer combined
  `(T_a ᵍ⊗ T_b)`-action (`TowerColumn.lean`'s pulled-back `stdFuse`
  action) and its Koszul-signed middle `T_c`-action
  (`TowerColumn.superCommSMul`) assemble via `gtensorLeftActionHom`
  into a genuine `((T_a ᵍ⊗ T_b) ᵍ⊗ T_c)`-module structure on `B_L`
  (`instModuleGtensorABCRaw`, stated at the raw `ᵍ⊗` type to keep the
  `rw`-based proofs inside `instances`-transparency; `instModuleGtensorABC`
  bridges to the `.gtensor.carrier` spelling `quadSource` uses) — no new
  general machinery needed beyond `GtensorLeftActionGraded.lean`, every
  other hypothesis (`SetLike.GradedSMul`, `SMulCommClass`,
  `IsScalarTower`) is already landed on `TowerColumn`.  `SMulCommClass`
  with `B_L`'s own right `T_{a+b+c}`-action is
  `gtensorLeftActionHom_comm_rightActionEnd`; gradedness of the
  combined action (needed as the `[SetLike.GradedSMul …]` input of
  Level 2) is `gtensorLeftActionHom_mem_relGrading`.

* **Level 2** (`namespace Q1`): the exact same pattern one level up —
  `Q1`'s own outer combined action (Level 1's `B_L`-action) and its
  Koszul-signed middle `T_d`-action (`Q1`'s own `T_d`-slot,
  `QuadActions.lean`) assemble into a genuine `quadSource K a b c d`
  -module structure on `Q1` (`instModuleQuadSource`).  Two further
  pieces, not needed at Level 1, are supplied directly (no landed
  precedent): `IsScalarTower K (T_{a+b+c+d})ᵐᵒᵖ (Q1 …)` (the same
  `compHom`-of-an-`AlgHom` argument as everywhere) and
  `GradedRightSMul (T_{a+b+c+d}) (Q1.grading …)`
  (`rightActionEnd_mem_relGrading`, mirroring `RouteCompat.lean`'s
  `B_L`/`B_R` instances) — together with the two actions above, these
  are exactly `Bimod.Basic`'s `Envelope`/`actionHom` section's
  hypotheses, assembled into **`Module (QuadEnv K a b c d) (Q1 K a b c
  d)`** (`instModuleQuadEnv`, via `Bimod.module`).

`Q4`'s mirror construction is **not** attempted: `B_R`'s own natural
combined action (`T_b` as the *outer* mid-slot over the `(T_c ᵍ⊗
T_d)`-combined inner pair, from `BR K b c d`'s own definition) is
bracketed as `(T_c ᵍ⊗ T_d) ᵍ⊗ T_b`, and `Q4`'s own further combination
with the `T_a`-slot gives `((T_c ᵍ⊗ T_d) ᵍ⊗ T_b) ᵍ⊗ T_a` — a different
association *and* a different slot *order* from `quadSource`'s
`((T_a ᵍ⊗ T_b) ᵍ⊗ T_c) ᵍ⊗ T_d`.  Reconciling the two needs an explicit
algebra isomorphism combining associativity (`gtensorAssoc`) *and*
Koszul commutativity (`gtensorComm`, introducing signs to reorder
`b, c, d, a ↦ a, b, c, d`), and transporting `Q4`'s action along it —
out of scope for this milestone; see the session report.
-/
import Superfusion.Bimod.QuadEnvelope
import Superfusion.Bimod.GtensorLeftActionGraded

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-! ### Level 1: `B_L`'s combined `(T_a ᵍ⊗ T_b) ᵍ⊗ T_c`-action -/

namespace BL

/-- **The combined `(T_a ᵍ⊗ T_b) ᵍ⊗ T_c`-action on `B_L`, raw
spelling**: the outer combined `(T_a ᵍ⊗ T_b)`-action of `TowerColumn K
a b` (pulled back along `stdFuse`) and the Koszul-signed middle
`T_c`-action assemble via `gtensorLeftActionHom`.  Stated at the raw
`ᵍ⊗` type (matching `gtensorLeftActionHom`'s own domain exactly, so
that the `rw`-based proofs below never mix it with the `.gtensor
.carrier` spelling — a mixed term is defeq but not `instances`
-transparency type-correct, defeating `rw`/`simp`'s pattern matching);
`instModuleGtensorABC` bridges to the `.gtensor.carrier` spelling
`quadSource`-style code expects. -/
noncomputable instance instModuleGtensorABCRaw :
    Module (((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading)
      (BL K a b c) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c))
    ((gtensorLeftActionHom (stdTower (K := K) (a + b)).grading (TowerColumn.grading K a b)
        (stdTower (K := K) c).grading ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (TowerColumn.superCommSMul K (a + b) c)).toRingHom)

theorem gtensorABCRaw_smul_def
    (w : ((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading)
    (m : BL K a b c) :
    w • m = gtensorLeftActionHom (stdTower (K := K) (a + b)).grading
        (TowerColumn.grading K a b) (stdTower (K := K) c).grading
        ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (TowerColumn.superCommSMul K (a + b) c) w m := rfl

/-- `B_L`'s own right action, elementwise (rather than only on
generators `mk u v` as `right_smul_mk` does). -/
theorem right_smul_apply (τ : ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ) (m : BL K a b c) :
    τ • m = rightActionEnd K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c) τ m := rfl

instance : IsScalarTower K
    (((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading)
    (BL K a b c) :=
  ⟨fun k w m => by
    rw [gtensorABCRaw_smul_def, gtensorABCRaw_smul_def, map_smul, LinearMap.smul_apply]
    rfl⟩

/-- **`B_L`'s combined action commutes with its own right
`T_{a+b+c}`-action**: `gtensorLeftActionHom_comm_rightActionEnd`
instantiated at `B_L`'s own construction. -/
instance : SMulCommClass
    (((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading)
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BL K a b c) :=
  ⟨fun w τ m => by
    rw [right_smul_apply, gtensorABCRaw_smul_def, gtensorABCRaw_smul_def, right_smul_apply]
    have h := gtensorLeftActionHom_comm_rightActionEnd (stdTower (K := K) (a + b)).grading
      (TowerColumn.grading K a b) (stdTower (K := K) c).grading
      ((stdTower (K := K) a).gtensor (stdTower b)).grading
      (TowerColumn.superCommSMul K (a + b) c) w τ
    have h' := congrArg (fun f : Module.End K
        (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
          (TowerColumn K (a + b) c)) => f m) h
    rw [Module.End.mul_apply, Module.End.mul_apply] at h'
    exact h'⟩

/-- **Bridge**: `B_L`'s combined action, at the `.gtensor.carrier`
spelling `quadSource K a b c d` (`PentagonChi.lean`) is built from. -/
noncomputable instance instModuleGtensorABC :
    Module (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier
      (BL K a b c) :=
  inferInstanceAs (Module
    (((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading)
    (BL K a b c))

instance : IsScalarTower K
    (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier (BL K a b c) :=
  inferInstanceAs (IsScalarTower K
    (((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading)
    (BL K a b c))

instance : SMulCommClass
    (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BL K a b c) :=
  inferInstanceAs (SMulCommClass
    (((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading)
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BL K a b c))

/-- **`B_L`'s combined action is graded**: `gtensorLeftActionHom_mem_relGrading`
instantiated at `B_L`'s own construction — `relGrading (stdTower (a+b)).carrier
(TowerColumn.grading K a b) (TowerColumn.grading K (a+b) c)` is `B_L.grading`
by definition, and `tensorGrading ((T_a ᵍ⊗ T_b)) (T_c)` is `(((T_a).gtensor
T_b).gtensor T_c).grading` by definition, so `exact` accepts the term
directly (full elaboration-time defeq, unlike `rw`). -/
instance : SetLike.GradedSMul
    (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
    (BL.grading K a b c) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact gtensorLeftActionHom_mem_relGrading (stdTower (K := K) (a + b)).grading
      (TowerColumn.grading K a b) (stdTower (K := K) c).grading
      ((stdTower (K := K) a).gtensor (stdTower b)).grading (TowerColumn.grading K (a + b) c)
      (TowerColumn.superCommSMul K (a + b) c) hw hz

end BL

/-! ### Level 2: `Q1`'s combined `quadSource`-action -/

namespace Q1

/-- **The combined `quadSource K a b c d`-action on `Q1`, raw
spelling**: Level 1's `B_L`-action and the Koszul-signed middle
`T_d`-action (already `Q1`'s own `T_d`-slot, `QuadActions.lean`)
assemble via a further `gtensorLeftActionHom`. -/
noncomputable instance instModuleGtensorABCDRaw :
    Module ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
        (stdTower (K := K) d).grading)
      (Q1 K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d))
    ((gtensorLeftActionHom (stdTower (K := K) (a + b + c)).grading (BL.grading K a b c)
        (stdTower (K := K) d).grading
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (TowerColumn.superCommSMul K (a + b + c) d)).toRingHom)

theorem gtensorABCDRaw_smul_def
    (w : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
      (stdTower (K := K) d).grading)
    (m : Q1 K a b c d) :
    w • m = gtensorLeftActionHom (stdTower (K := K) (a + b + c)).grading (BL.grading K a b c)
        (stdTower (K := K) d).grading
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (TowerColumn.superCommSMul K (a + b + c) d) w m := rfl

/-- `Q1`'s own right action, elementwise. -/
theorem right_smul_apply (τ : ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ)
    (m : Q1 K a b c d) :
    τ • m = rightActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d) τ m := rfl

instance : IsScalarTower K
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
      (stdTower (K := K) d).grading) (Q1 K a b c d) :=
  ⟨fun k w m => by
    rw [gtensorABCDRaw_smul_def, gtensorABCDRaw_smul_def, map_smul, LinearMap.smul_apply]
    rfl⟩

/-- **`Q1`'s combined action commutes with its own right
`T_{a+b+c+d}`-action**. -/
instance : SMulCommClass
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
      (stdTower (K := K) d).grading)
    ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q1 K a b c d) :=
  ⟨fun w τ m => by
    rw [right_smul_apply, gtensorABCDRaw_smul_def, gtensorABCDRaw_smul_def, right_smul_apply]
    have h := gtensorLeftActionHom_comm_rightActionEnd (stdTower (K := K) (a + b + c)).grading
      (BL.grading K a b c) (stdTower (K := K) d).grading
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
      (TowerColumn.superCommSMul K (a + b + c) d) w τ
    have h' := congrArg (fun f : Module.End K
        (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
          (TowerColumn K (a + b + c) d)) => f m) h
    rw [Module.End.mul_apply, Module.End.mul_apply] at h'
    exact h'⟩

/-- **Bridge**: `Q1`'s combined action, at the `quadSource K a b c d`
(`PentagonChi.lean`) `.gtensor.carrier` spelling. -/
noncomputable instance instModuleQuadSource :
    Module (quadSource (K := K) a b c d).carrier (Q1 K a b c d) :=
  inferInstanceAs (Module
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
      (stdTower (K := K) d).grading) (Q1 K a b c d))

instance : IsScalarTower K (quadSource (K := K) a b c d).carrier (Q1 K a b c d) :=
  inferInstanceAs (IsScalarTower K
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
      (stdTower (K := K) d).grading) (Q1 K a b c d))

instance : SMulCommClass (quadSource (K := K) a b c d).carrier
    ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q1 K a b c d) :=
  inferInstanceAs (SMulCommClass
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
      (stdTower (K := K) d).grading) ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ
    (Q1 K a b c d))

/-- **`Q1`'s combined action is graded** (needs `instModuleQuadSource`
already registered, since its `w • z` is at the `quadSource`-carrier
spelling). -/
instance : SetLike.GradedSMul (quadSource (K := K) a b c d).grading (grading K a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact gtensorLeftActionHom_mem_relGrading (stdTower (K := K) (a + b + c)).grading
      (BL.grading K a b c) (stdTower (K := K) d).grading
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
      (TowerColumn.grading K (a + b + c) d) (TowerColumn.superCommSMul K (a + b + c) d) hw hz

/-- `Q1`'s own right action is a `K`-scalar tower. -/
instance : IsScalarTower K ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q1 K a b c d) :=
  ⟨fun k τ m => by
    show rightActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
        (TowerColumn K (a + b + c) d) (k • τ) m
      = k • rightActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
          (TowerColumn K (a + b + c) d) τ m
    rw [map_smul, LinearMap.smul_apply]⟩

/-- `Q1`'s own right action is graded (`rightActionEnd_mem_relGrading`,
mirroring `RouteCompat.lean`'s `BL`/`BR` instances). -/
instance : GradedRightSMul (stdTower (K := K) (a + b + c + d)).grading (grading K a b c d) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (BL.grading K a b c) (TowerColumn.grading K (a + b + c) d) hτ hw

/-- **`Q1` is a `QuadEnv K a b c d`-module**: the two actions (the
`quadSource`-action of Level 1–2 and `Q1`'s own right
`T_{a+b+c+d}`-action) assemble via `Bimod.module`
(`Basic.lean`'s envelope-action packaging). -/
noncomputable instance instModuleQuadEnv : Module (QuadEnv K a b c d) (Q1 K a b c d) :=
  Bimod.module (quadSource (K := K) a b c d).grading (stdTower (K := K) (a + b + c + d)).grading
    (grading K a b c d)

end Q1

end PentagonB

end Bimod

end Superfusion

/-
Superfusion / GaugeChi / QuadEnvModule

Milestone M12-6 of the abstract `(p, χ)` arc: **`GQ1`'s `gQuadEnv`-module
structure**, via the STRUCTURAL route (mirroring
`GaugeChi.GaugeParity`'s `GBL` section one gtensor level up): `GQ1`'s own
combined action already has the envelope's own bracket `((D_a ᵍ⊗ D_b) ᵍ⊗
D_c) ᵍ⊗ D_d`, so a SINGLE `gtensorLeftActionHom` combines `GBL Γ a b c`'s
own registered combined `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-action (`GaugeChi.GaugeParity`'s
`GBL.instModuleGtensorABC`) with the Koszul-signed `D_d`-action on the
second factor `FusionColumn (Γ.fuse (a+b+c) d)`, fed by
`FusionColumn.superCommSMul (Γ.fuse (a+b+c) d)` — the exact `GBL`-pattern of
`GaugeParity.lean`, one level up. `Module (gQuadEnv Γ a b c d) (GQ1 Γ a b c
d)` assembles via `Bimod.module`.
-/
import Superfusion.GaugeChi.QuadEnvelope
import Superfusion.GaugeChi.PentagonActions

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

namespace GQ1

/-- **The combined `((D_a ᵍ⊗ D_b) ᵍ⊗ D_c) ᵍ⊗ D_d`-action on `GQ1`, raw
spelling**: `GBL Γ a b c`'s own registered combined `(D_a ᵍ⊗ D_b) ᵍ⊗
D_c`-action (`GaugeChi.GaugeParity`'s `GBL.instModuleGtensorABC`) and the
Koszul-signed `D_d`-action assemble via `gtensorLeftActionHom`. Stated at
the raw `ᵍ⊗` type (mirroring `GaugeParity.lean`'s `GBL.instModuleGtensorABCRaw`),
so the `rw`-based proofs below stay `instances`-transparent;
`instModuleGtensorABCD` bridges to the `.gtensor.carrier` spelling
`gQuadEnv` uses. -/
noncomputable instance instModuleGtensorABCDRaw :
    Module ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading)
      (GQ1 K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)))
    ((gtensorLeftActionHom (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
        (Γ.D d).grading (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d))).toRingHom)

theorem gtensorABCDRaw_smul_def
    (w : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading)
    (m : GQ1 K Γ a b c d) :
    w • m = gtensorLeftActionHom (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
        (Γ.D d).grading (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) w m := rfl

/-- `GQ1`'s own right action, elementwise. -/
theorem right_smul_apply (τ : ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ) (m : GQ1 K Γ a b c d) :
    τ • m = rightActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) τ m := rfl

instance : IsScalarTower K
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading)
    (GQ1 K Γ a b c d) :=
  ⟨fun k w m => by
    rw [gtensorABCDRaw_smul_def, gtensorABCDRaw_smul_def, map_smul, LinearMap.smul_apply]
    rfl⟩

/-- **`GQ1`'s combined action commutes with its own right
`D_{a+b+c+d}`-action**: `gtensorLeftActionHom_comm_rightActionEnd`
instantiated at `GQ1`'s own construction. -/
instance : SMulCommClass
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading)
    ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ1 K Γ a b c d) :=
  ⟨fun w τ m => by
    rw [right_smul_apply, gtensorABCDRaw_smul_def, gtensorABCDRaw_smul_def, right_smul_apply]
    have h := gtensorLeftActionHom_comm_rightActionEnd (Γ.D (a + b + c)).grading
      (GBL.grading Γ a b c) (Γ.D d).grading
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) w τ
    have h' := congrArg (fun f : Module.End K
        (RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d))) => f m) h
    rw [Module.End.mul_apply, Module.End.mul_apply] at h'
    exact h'⟩

/-- **Bridge**: `GQ1`'s combined action, at the `.gtensor.carrier`
spelling `gQuadEnv` is built from. -/
noncomputable instance instModuleGtensorABCD :
    Module ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier
      (GQ1 K Γ a b c d) :=
  inferInstanceAs (Module
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading)
    (GQ1 K Γ a b c d))

instance : IsScalarTower K
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier (GQ1 K Γ a b c d) :=
  inferInstanceAs (IsScalarTower K
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading)
    (GQ1 K Γ a b c d))

instance : SMulCommClass
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier
    ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ1 K Γ a b c d) :=
  inferInstanceAs (SMulCommClass
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading)
    ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ1 K Γ a b c d))

/-- **`GQ1`'s combined action is graded**: `gtensorLeftActionHom_mem_relGrading`
instantiated at `GQ1`'s own construction. -/
instance : SetLike.GradedSMul
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
    (grading K Γ a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact gtensorLeftActionHom_mem_relGrading (Γ.D (a + b + c)).grading
      (GBL.grading Γ a b c) (Γ.D d).grading
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (FusionColumn.grading (Γ.fuse (a + b + c) d))
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) hw hz

/-- `GQ1`'s own right action is a `K`-scalar tower. -/
instance : IsScalarTower K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ1 K Γ a b c d) :=
  ⟨fun k τ m => by
    show rightActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) (k • τ) m
      = k • rightActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) τ m
    rw [map_smul, LinearMap.smul_apply]⟩

/-- `GQ1`'s own right action is graded (`rightActionEnd_mem_relGrading`,
mirroring `GaugeParity.lean`'s `GBL` instance). -/
instance : GradedRightSMul (Γ.D (a + b + c + d)).grading (grading K Γ a b c d) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (GBL.grading Γ a b c)
      (FusionColumn.grading (Γ.fuse (a + b + c) d)) hτ hw

/-- **`GQ1` is a `gQuadEnv Γ a b c d`-module**: the two actions (the
combined action above and `GQ1`'s own right `D_{a+b+c+d}`-action) assemble
via `Bimod.module`. -/
noncomputable instance instModuleGQuadEnv : Module (gQuadEnv K Γ a b c d) (GQ1 K Γ a b c d) :=
  Bimod.module ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
    (Γ.D (a + b + c + d)).grading (grading K Γ a b c d)

end GQ1

end GaugeChi

end Superfusion

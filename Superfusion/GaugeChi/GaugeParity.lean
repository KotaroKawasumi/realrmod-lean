/-
Superfusion / GaugeChi / GaugeParity

Milestone M12-2′ of the abstract `(p, χ)` arc: **the envelope-module
structures, the interface, and `gParity` — the abstract `p`**.

Deliverable 1: `Module (gTripleEnv Γ a b c) (GBL Γ a b c)` and
`Module (gTripleEnv Γ a b c) (GBR Γ a b c)` — the Γ-mirror of
`Superfusion.Bimod.QuadEnvModule`/`QuadEnvModule2`, one gtensor level
down.

* **`GBL`** takes the *structural route*: its own natural combined
  action already has the envelope's own bracket `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`
  (mirroring `QuadEnvModule.lean`'s `BL`-level assembly): a single
  `gtensorLeftActionHom` combining `FusionColumn (Γ.fuse a b)`'s own
  registered combined `(D_a ᵍ⊗ D_b)`-action (from `FusionColumn`'s
  `Slots` section) with the Koszul-signed middle `D_c`-action, fed by
  `FusionColumn.superCommSMul (Γ.fuse (a+b) c)`.

* **`GBR`** takes the *direct multi-fold lift* (per `QuadEnvModule2.lean`'s
  resolution of the identical bracket mismatch at `Q4`): `GBR`'s own
  natural combined action has the shape `(D_b ᵍ⊗ D_c) ᵍ⊗ D_a`, a
  different bracket from the envelope's `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`.  Rather
  than transporting along `gtensorAssoc`/`gtensorComm`, the envelope
  action is assembled *directly*, in the envelope's own slot order,
  from `GBR`'s three individual slot `End`-maps (already registered in
  `GaugeChi.RouteBimod`) and their three pairwise supercommutation
  certificates (`comm_ab`/`comm_ac` from `leftActionEnd_anticommutes_midAlgHom`,
  `comm_bc` from `leftActionEnd_leftActionEnd_supercomm_end` fed by
  `FusionColumn.superCommSMul (Γ.fuse b c)`), via two iterated
  `GradedTensorProduct.lift`s (`phi1` for `(a,b)`, `phi2` for `((a,b),c)`
  — one level shorter than `Q4`'s three lifts, since there is no fourth
  slot here).  The general lemmas `leftActionEnd_leftActionEnd_supercomm_end`,
  `lift_anticommute_sgn`, `lift_comm_right` (`Superfusion.Bimod.QuadEnvModule2`)
  are reused verbatim.

Both vertices are equipped with the `IsScalarTower K`/`SetLike.GradedSMul`/
`GradedRightSMul` instances `Bimod.Basic`'s `Envelope`/`module` machinery
needs, and the slot-generator evaluation lemmas (`aEmbed`/`bEmbed`/`cEmbed`)
identifying the envelope action at a slot generator with the vertex's own
registered slot action — the `QuadInterface.lean` `(b)`-suite pattern, one
level shorter.
-/
import Superfusion.GaugeChi.InterSpace
import Superfusion.Bimod.QuadEnvModule2
import Superfusion.Bimod.QuadInterface2
import Superfusion.Bimod.SplitIsotypy

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

/-! ### A general `FusionColumn` slot-embedding fact -/

omit [Invertible (2 : K)] in
/-- **A slot generator embedded via `includeLeft` acts on a `FusionColumn`
exactly as the slot action**: `FusionColumn`'s `Slots`-section `smul_def`
(the combined `(P₁ ᵍ⊗ P₂)`-action) and `slotLeft_smul_def` (the `P₁`-slot
action) both unfold to the identical matrix expression, so the two agree
at an `includeLeft`-embedded generator. -/
private theorem fcSlotLeftEmbed {P₁ P₂ B : SuperAlgebra K} {p q : ℕ}
    (φ : SuperAlgEquiv (P₁.gtensor P₂) (B.matrixSuper p q))
    (x₀ : (P₁.gtensor P₂).carrier) (x : P₁.carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft P₁.grading P₂.grading x)
    (v : FusionColumn φ) : x₀ • v = x • v := by
  rw [FusionColumn.smul_def, hx₀, FusionColumn.slotLeft_smul_def]

omit [Invertible (2 : K)] in
/-- The `includeRight` counterpart of `fcSlotLeftEmbed`. -/
private theorem fcSlotRightEmbed {P₁ P₂ B : SuperAlgebra K} {p q : ℕ}
    (φ : SuperAlgEquiv (P₁.gtensor P₂) (B.matrixSuper p q))
    (y₀ : (P₁.gtensor P₂).carrier) (y : P₂.carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight P₁.grading P₂.grading y)
    (v : FusionColumn φ) : y₀ • v = y • v := by
  rw [FusionColumn.smul_def, hy₀, FusionColumn.slotRight_smul_def]

/-! ### `GBL`'s combined `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-action (structural route) -/

namespace GBL

/-- **The combined `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-action on `GBL`, raw spelling**:
the outer combined `(D_a ᵍ⊗ D_b)`-action of `FusionColumn (Γ.fuse a b)`
(already registered by `FusionColumn`'s `Slots` section) and the
Koszul-signed middle `D_c`-action assemble via `gtensorLeftActionHom`.
Stated at the raw `ᵍ⊗` type (mirroring `QuadEnvModule.lean`'s
`BL.instModuleGtensorABCRaw`), so the `rw`-based proofs below stay
`instances`-transparent; `instModuleGtensorABC` bridges to the
`.gtensor.carrier` spelling `gTripleEnv` uses. -/
noncomputable instance instModuleGtensorABCRaw :
    Module (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (GBL Γ a b c) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)))
    ((gtensorLeftActionHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (Γ.D c).grading ((Γ.D a).gtensor (Γ.D b)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) c))).toRingHom)

theorem gtensorABCRaw_smul_def
    (w : ((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (m : GBL Γ a b c) :
    w • m = gtensorLeftActionHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (Γ.D c).grading ((Γ.D a).gtensor (Γ.D b)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) w m := rfl

/-- `GBL`'s own right action, elementwise (rather than only on
generators `mk u v` as `right_smul_mk` does). -/
theorem right_smul_apply (τ : ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ) (m : GBL Γ a b c) :
    τ • m = rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) τ m := rfl

instance : IsScalarTower K
    (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (GBL Γ a b c) :=
  ⟨fun k w m => by
    rw [gtensorABCRaw_smul_def, gtensorABCRaw_smul_def, map_smul, LinearMap.smul_apply]
    rfl⟩

/-- **`GBL`'s combined action commutes with its own right
`D_{a+b+c}`-action**: `gtensorLeftActionHom_comm_rightActionEnd`
instantiated at `GBL`'s own construction. -/
instance : SMulCommClass
    (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading)
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  ⟨fun w τ m => by
    rw [right_smul_apply, gtensorABCRaw_smul_def, gtensorABCRaw_smul_def, right_smul_apply]
    have h := gtensorLeftActionHom_comm_rightActionEnd (Γ.D (a + b)).grading
      (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
      ((Γ.D a).gtensor (Γ.D b)).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) w τ
    have h' := congrArg (fun f : Module.End K
        (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) c))) => f m) h
    rw [Module.End.mul_apply, Module.End.mul_apply] at h'
    exact h'⟩

/-- **Bridge**: `GBL`'s combined action, at the `.gtensor.carrier`
spelling `gTripleEnv` is built from. -/
noncomputable instance instModuleGtensorABC :
    Module (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier (GBL Γ a b c) :=
  inferInstanceAs (Module
    (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (GBL Γ a b c))

instance : IsScalarTower K (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier (GBL Γ a b c) :=
  inferInstanceAs (IsScalarTower K
    (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) (GBL Γ a b c))

instance : SMulCommClass
    (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  inferInstanceAs (SMulCommClass
    (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading)
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c))

/-- **`GBL`'s combined action is graded**: `gtensorLeftActionHom_mem_relGrading`
instantiated at `GBL`'s own construction. -/
instance : SetLike.GradedSMul
    (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (GBL.grading Γ a b c) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact gtensorLeftActionHom_mem_relGrading (Γ.D (a + b)).grading
      (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
      ((Γ.D a).gtensor (Γ.D b)).grading (FusionColumn.grading (Γ.fuse (a + b) c))
      (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) hw hz

/-- `GBL`'s own right action is a `K`-scalar tower. -/
instance : IsScalarTower K ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBL Γ a b c) :=
  ⟨fun k τ m => by
    show rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) c)) (k • τ) m
      = k • rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) c)) τ m
    rw [map_smul, LinearMap.smul_apply]⟩

/-- `GBL`'s own right action is graded (`rightActionEnd_mem_relGrading`,
mirroring `RouteCompat.lean`'s `BL`/`BR` instances). -/
instance : GradedRightSMul (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (FusionColumn.grading (Γ.fuse a b))
      (FusionColumn.grading (Γ.fuse (a + b) c)) hτ hw

/-- **`GBL` is a `gTripleEnv Γ a b c`-module**: the two actions (the
combined action above and `GBL`'s own right `D_{a+b+c}`-action) assemble
via `Bimod.module`. -/
noncomputable instance instModuleGTripleEnv : Module (gTripleEnv K Γ a b c) (GBL Γ a b c) :=
  Bimod.module (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D (a + b + c)).grading
    (GBL.grading Γ a b c)

/-! #### Slot-generator evaluation: the combined action at a slot
generator, embedded through the matching `includeLeft`/`includeRight`
chain, literally IS `GBL`'s own registered slot action -/

theorem aslot_apply (x : (Γ.D a).carrier) (w : GBL Γ a b c) :
    x • w = leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) x w := rfl

theorem bslot_apply (y : (Γ.D b).carrier) (w : GBL Γ a b c) :
    y • w = leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) c)) y w := rfl

theorem cslot_apply (z : (Γ.D c).carrier) (w : GBL Γ a b c) :
    z • w = midAlgHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D c).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) z w := rfl

/-- `GBL`'s combined action at the bridged `.gtensor.carrier` spelling,
elementwise (`rfl`, matching the spelling the embedding lemmas below need). -/
theorem gtensorABC_smul_def (w : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (m : GBL Γ a b c) :
    w • m = gtensorLeftActionHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (Γ.D c).grading ((Γ.D a).gtensor (Γ.D b)).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) c)) w m := rfl

/-- **The `a`-slot-embedding bridge**: the envelope-source element
obtained by embedding `x : D_a` via the two-fold `includeLeft` chain
matching the envelope's own bracket order acts on `GBL`, on *every*
element, exactly as `GBL`'s own registered `a`-slot action of `x`. -/
theorem aEmbed
    (x₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (x : (Γ.D a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
    (x₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading x₀)
    (w : GBL Γ a b c) :
    x₁ • w = x • w := by
  have key : (leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) c)) x₀
      : Module.End K (GBL Γ a b c))
      = leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) c)) (B := (Γ.D a).carrier) x := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, fcSlotLeftEmbed K (Γ.fuse a b) x₀ x hx₀]
  rw [gtensorABC_smul_def, hx₁, gtensorLeftActionHom_includeLeft, key, ← aslot_apply]

/-- **The `b`-slot-embedding bridge**. -/
theorem bEmbed
    (y₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (y : (Γ.D b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
    (y₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading y₀)
    (w : GBL Γ a b c) :
    y₁ • w = y • w := by
  have key : (leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) c)) y₀
      : Module.End K (GBL Γ a b c))
      = leftActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) c)) (B := (Γ.D b).carrier) y := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, fcSlotRightEmbed K (Γ.fuse a b) y₀ y hy₀]
  rw [gtensorABC_smul_def, hy₁, gtensorLeftActionHom_includeLeft, key, ← bslot_apply]

/-- **The `c`-slot-embedding bridge** — a single `includeRight`, since
`D_c` is the envelope source's own outermost right factor. -/
theorem cEmbed
    (w₀ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) (w' : (Γ.D c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading w')
    (u : GBL Γ a b c) :
    w₀ • u = w' • u := by
  rw [gtensorABC_smul_def, hw₀, gtensorLeftActionHom_includeRight, ← cslot_apply]

end GBL

/-! ### `GBR`'s combined `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c`-action (direct lift) -/

namespace GBR

/-- `GBR`'s `D_a`-slot, as an algebra map (`midAlgHom`, mid-of-mid through
the outer column) — literally the term `GaugeChi.RouteBimod` uses to build
`GBR`'s registered `D_a`-slot `Module` instance. -/
private noncomputable abbrev fA :
    (Γ.D a).carrier →ₐ[K] Module.End K (GBR Γ a b c) :=
  midAlgHom (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c))))

/-- `GBR`'s `D_b`-slot, as an algebra map (`leftActionEnd`). -/
private noncomputable abbrev fB :
    (Γ.D b).carrier →ₐ[K] Module.End K (GBR Γ a b c) :=
  leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) (B := (Γ.D b).carrier)

/-- `GBR`'s `D_c`-slot, as an algebra map (`leftActionEnd`). -/
private noncomputable abbrev fC :
    (Γ.D c).carrier →ₐ[K] Module.End K (GBR Γ a b c) :=
  leftActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) (B := (Γ.D c).carrier)

theorem aslot_apply (x : (Γ.D a).carrier) (z : GBR Γ a b c) : x • z = fA K Γ a b c x z := rfl

theorem bslot_apply (y : (Γ.D b).carrier) (z : GBR Γ a b c) : y • z = fB K Γ a b c y z := rfl

theorem cslot_apply (w : (Γ.D c).carrier) (z : GBR Γ a b c) : w • z = fC K Γ a b c w z := rfl

/-! #### The three pairwise supercommutation certificates for `GBR`'s
slots.  `(a,b)`/`(a,c)` reduce directly to
`leftActionEnd_anticommutes_midAlgHom` (`D_a` is the mid-of-mid slot for
both); `(b,c)` is `leftActionEnd_leftActionEnd_supercomm_end` applied to
`FusionColumn.superCommSMul (Γ.fuse b c)` — since `D_b`, `D_c` are already
*direct* `leftActionEnd` slots of `GBR` (no further lifting needed, unlike
`Q4`'s `comm_bc` which had to lift through an inner `B_R`). -/

/-- **The `Units.smul` swap of an anticommutation fact** (local copy of
`QuadEnvModule2.lean`'s private `uzpow_smul_symm`). -/
private theorem uzpow_smul_symm {X : Type*} [AddCommGroup X] {n : ZMod 2}
    {u v : X} (h : u = (-1 : ℤˣ) ^ n • v) : v = (-1 : ℤˣ) ^ n • u := by
  have hc : (-1 : ℤˣ) ^ n * (-1 : ℤˣ) ^ n = 1 := by
    rw [← sgn_eq_neg_one_uzpow, sgn_mul_self']
  rw [h, smul_smul, hc, one_smul]

/-- Local copy of `QuadEnvModule2.lean`'s private `toUzpow`. -/
private theorem toUzpow {X : Type*} [AddCommGroup X] {n : ZMod 2} {u v : X}
    (h : u = ((sgn n : ℤˣ) : ℤ) • v) : u = (-1 : ℤˣ) ^ n • v := by
  rw [Units.smul_def, ← sgn_eq_neg_one_uzpow]; exact h

/-- Local copy of `QuadEnvModule2.lean`'s private `fromUzpow`. -/
private theorem fromUzpow {X : Type*} [AddCommGroup X] {n : ZMod 2} {u v : X}
    (h : u = (-1 : ℤˣ) ^ n • v) : u = ((sgn n : ℤˣ) : ℤ) • v := by
  rw [h, Units.smul_def, ← sgn_eq_neg_one_uzpow]

theorem comm_ab ⦃i k : ZMod 2⦄ (x : (Γ.D a).grading i) (y : (Γ.D b).grading k) :
    fA K Γ a b c (x : (Γ.D a).carrier) * fB K Γ a b c (y : (Γ.D b).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fB K Γ a b c (y : (Γ.D b).carrier) * fA K Γ a b c (x : (Γ.D a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (b + c)).grading
    (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading (Γ.D b).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) y x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_ac ⦃i k : ZMod 2⦄ (x : (Γ.D a).grading i) (z : (Γ.D c).grading k) :
    fA K Γ a b c (x : (Γ.D a).carrier) * fC K Γ a b c (z : (Γ.D c).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fC K Γ a b c (z : (Γ.D c).carrier) * fA K Γ a b c (x : (Γ.D a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (b + c)).grading
    (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading (Γ.D c).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) z x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_bc ⦃i k : ZMod 2⦄ (y : (Γ.D b).grading i) (z : (Γ.D c).grading k) :
    fB K Γ a b c (y : (Γ.D b).carrier) * fC K Γ a b c (z : (Γ.D c).carrier)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (fC K Γ a b c (z : (Γ.D c).carrier) * fB K Γ a b c (y : (Γ.D b).carrier)) :=
  leftActionEnd_leftActionEnd_supercomm_end (Γ.D b).grading (Γ.D c).grading
    (FusionColumn.superCommSMul (Γ.fuse b c)) y.2 z.2

private theorem comm_ac_sgn ⦃i k : ZMod 2⦄ (x : (Γ.D a).grading i) (z : (Γ.D c).grading k) :
    fA K Γ a b c (x : (Γ.D a).carrier) * fC K Γ a b c (z : (Γ.D c).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fC K Γ a b c (z : (Γ.D c).carrier) * fA K Γ a b c (x : (Γ.D a).carrier)) :=
  fromUzpow (comm_ac K Γ a b c x z)

private theorem comm_bc_sgn ⦃i k : ZMod 2⦄ (y : (Γ.D b).grading i) (z : (Γ.D c).grading k) :
    fB K Γ a b c (y : (Γ.D b).carrier) * fC K Γ a b c (z : (Γ.D c).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fC K Γ a b c (z : (Γ.D c).carrier) * fB K Γ a b c (y : (Γ.D b).carrier)) := by
  rw [comm_bc K Γ a b c y z, mul_comm i k]

/-! #### The two iterated `GradedTensorProduct.lift`s, in the envelope's
own order `(D_a, D_b)` then `D_c` -/

/-- **Step 1**: `D_a ᵍ⊗ D_b` acts on `GBR`. -/
private noncomputable def phi1 :
    ((Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) →ₐ[K] Module.End K (GBR Γ a b c) :=
  GradedTensorProduct.lift (Γ.D a).grading (Γ.D b).grading
    (fA K Γ a b c) (fB K Γ a b c) (comm_ab K Γ a b c)

private theorem phi1_tmul (x : (Γ.D a).carrier) (y : (Γ.D b).carrier) :
    (phi1 K Γ a b c) (x ᵍ⊗ₜ[K] y) = fA K Γ a b c x * fB K Γ a b c y := rfl

/-- `D_a ᵍ⊗ D_b` (already combined, Step 1) anticommutes with `D_c`
(`sgn`-scalar convention, feeding Step 2's own `hanti`). -/
private theorem phi1_comm_c ⦃i j : ZMod 2⦄
    (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading i)
    (z : (Γ.D c).grading j) :
    (phi1 K Γ a b c) (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading)
        * fC K Γ a b c (z : (Γ.D c).carrier)
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (fC K Γ a b c (z : (Γ.D c).carrier) *
            (phi1 K Γ a b c) (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading)) :=
  lift_anticommute_sgn (Γ.D a).grading (Γ.D b).grading (Γ.D c).grading
    (fA K Γ a b c) (fB K Γ a b c) (comm_ab K Γ a b c)
    (fC K Γ a b c) (comm_ac_sgn K Γ a b c) (comm_bc_sgn K Γ a b c) w z

/-- **Step 2**: `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c` acts on `GBR` — this is the
envelope's own source carrier, verbatim (`(((Γ.D a).gtensor (Γ.D b)).gtensor
(Γ.D c)).carrier = ((Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) ᵍ⊗[K]
(Γ.D c).grading` by `SuperAlgebra.gtensor`'s definition). -/
private noncomputable def phi2 :
    (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading) →ₐ[K]
      Module.End K (GBR Γ a b c) :=
  GradedTensorProduct.lift (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading)
    (Γ.D c).grading (phi1 K Γ a b c) (fC K Γ a b c)
    (fun _ _ w z => toUzpow (phi1_comm_c K Γ a b c w z))

private theorem phi2_tmul (w1 : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) (z1 : (Γ.D c).carrier) :
    (phi2 K Γ a b c) (w1 ᵍ⊗ₜ[K] z1) = (phi1 K Γ a b c) w1 * fC K Γ a b c z1 := rfl

/-! #### Gradedness of `GBR`'s three slots, and of `phi1`, `phi2` -/

theorem fA_mem_grading ⦃i j : ZMod 2⦄ {x : (Γ.D a).carrier} (hx : x ∈ (Γ.D a).grading i)
    {z : GBR Γ a b c} (hz : z ∈ GBR.grading Γ a b c j) :
    fA K Γ a b c x z ∈ GBR.grading Γ a b c (i + j) :=
  midEnd_mem_relGrading (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) (Γ.D a).grading
    (FusionColumn.grading (Γ.fuse a (b + c)))
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) hx hz

theorem fB_mem_grading ⦃i j : ZMod 2⦄ {y : (Γ.D b).carrier} (hy : y ∈ (Γ.D b).grading i)
    {z : GBR Γ a b c} (hz : z ∈ GBR.grading Γ a b c j) :
    fB K Γ a b c y z ∈ GBR.grading Γ a b c (i + j) :=
  leftActionEnd_mem_relGrading (FusionColumn.grading (Γ.fuse b c))
    (FusionColumn.grading (Γ.fuse a (b + c))) hy hz

theorem fC_mem_grading ⦃i j : ZMod 2⦄ {w : (Γ.D c).carrier} (hw : w ∈ (Γ.D c).grading i)
    {z : GBR Γ a b c} (hz : z ∈ GBR.grading Γ a b c j) :
    fC K Γ a b c w z ∈ GBR.grading Γ a b c (i + j) :=
  leftActionEnd_mem_relGrading (FusionColumn.grading (Γ.fuse b c))
    (FusionColumn.grading (Γ.fuse a (b + c))) hw hz

private theorem phi1_mem_grading ⦃i j : ZMod 2⦄
    {w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading}
    (hw : w ∈ Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading i)
    {z : GBR Γ a b c} (hz : z ∈ GBR.grading Γ a b c j) :
    (phi1 K Γ a b c) w z ∈ GBR.grading Γ a b c (i + j) := by
  have key : ∀ z' ∈ GBR.grading Γ a b c j, (phi1 K Γ a b c) w z' ∈ GBR.grading Γ a b c (i + j) := by
    refine Superfusion.tensorGrading_induction (Γ.D a).grading (Γ.D b).grading
      (p := fun w' => ∀ z' ∈ GBR.grading Γ a b c j,
        (phi1 K Γ a b c) w' z' ∈ GBR.grading Γ a b c (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ x y hij hx hy z' hz'
      have hev : (phi1 K Γ a b c) (x ᵍ⊗ₜ[K] y) z' = fA K Γ a b c x (fB K Γ a b c y z') := by
        rw [phi1_tmul, Module.End.mul_apply]
      rw [hev]
      have h := fA_mem_grading K Γ a b c hx (fB_mem_grading K Γ a b c hy hz')
      rwa [← add_assoc, hij] at h
    · intro z' _
      rw [map_zero, LinearMap.zero_apply]
      exact zero_mem _
    · intro w1 w2 h1 h2 z' hz'
      rw [map_add, LinearMap.add_apply]
      exact add_mem (h1 z' hz') (h2 z' hz')
    · intro c w1 h1 z' hz'
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (h1 z' hz')
  exact key z hz

private theorem phi2_mem_grading ⦃i j : ZMod 2⦄
    {w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading}
    (hw : w ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading i)
    {z : GBR Γ a b c} (hz : z ∈ GBR.grading Γ a b c j) :
    (phi2 K Γ a b c) w z ∈ GBR.grading Γ a b c (i + j) := by
  have key : ∀ z' ∈ GBR.grading Γ a b c j, (phi2 K Γ a b c) w z' ∈ GBR.grading Γ a b c (i + j) := by
    refine Superfusion.tensorGrading_induction
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
      (p := fun w' => ∀ z' ∈ GBR.grading Γ a b c j,
        (phi2 K Γ a b c) w' z' ∈ GBR.grading Γ a b c (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ w1 z1 hij hw1 hz1 z' hz'
      have hev : (phi2 K Γ a b c) (w1 ᵍ⊗ₜ[K] z1) z' = (phi1 K Γ a b c) w1 (fC K Γ a b c z1 z') := by
        rw [phi2_tmul, Module.End.mul_apply]
      rw [hev]
      have h := phi1_mem_grading K Γ a b c hw1 (fC_mem_grading K Γ a b c hz1 hz')
      rwa [← add_assoc, hij] at h
    · intro z' _
      rw [map_zero, LinearMap.zero_apply]
      exact zero_mem _
    · intro w1 w2 h1 h2 z' hz'
      rw [map_add, LinearMap.add_apply]
      exact add_mem (h1 z' hz') (h2 z' hz')
    · intro c w1 h1 z' hz'
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (h1 z' hz')
  exact key z hz

/-! #### Commutation with `GBR`'s own native right `D_{a+(b+c)}`-action
(unsigned; the recast to `QuadEnv`'s sop-side `D_{a+b+c}` reuses
`GaugeChi.RouteBimod`'s already-registered recast action). -/

private noncomputable def rGBR (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ) :
    Module.End K (GBR Γ a b c) :=
  rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) τ

theorem rGBR_apply (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ) (z : GBR Γ a b c) :
    τ • z = rGBR K Γ a b c τ z := rfl

theorem fA_comm_right (x : (Γ.D a).carrier) (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ) :
    fA K Γ a b c x * rGBR K Γ a b c τ = rGBR K Γ a b c τ * fA K Γ a b c x :=
  midEnd_comm_rightActionEnd (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
    (Γ.D a).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c)))) x τ

theorem fB_comm_right (y : (Γ.D b).carrier) (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ) :
    fB K Γ a b c y * rGBR K Γ a b c τ = rGBR K Γ a b c τ * fB K Γ a b c y :=
  leftActionEnd_comm_rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) y τ

theorem fC_comm_right (w : (Γ.D c).carrier) (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ) :
    fC K Γ a b c w * rGBR K Γ a b c τ = rGBR K Γ a b c τ * fC K Γ a b c w :=
  leftActionEnd_comm_rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (FusionColumn (Γ.fuse a (b + c))) w τ

private theorem phi1_comm_right (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ)
    (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) :
    (phi1 K Γ a b c) w * rGBR K Γ a b c τ = rGBR K Γ a b c τ * (phi1 K Γ a b c) w :=
  lift_comm_right (Γ.D a).grading (Γ.D b).grading (fA K Γ a b c) (fB K Γ a b c) (comm_ab K Γ a b c)
    (fun x => fA_comm_right K Γ a b c x τ) (fun y => fB_comm_right K Γ a b c y τ) w

private theorem phi2_comm_right (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ)
    (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading) :
    (phi2 K Γ a b c) w * rGBR K Γ a b c τ = rGBR K Γ a b c τ * (phi2 K Γ a b c) w :=
  lift_comm_right (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
    (phi1 K Γ a b c) (fC K Γ a b c) (fun _ _ w' z' => toUzpow (phi1_comm_c K Γ a b c w' z'))
    (fun w' => phi1_comm_right K Γ a b c τ w') (fun z' => fC_comm_right K Γ a b c z' τ) w

/-! #### Assembling `Module (gTripleEnv K Γ a b c) (GBR Γ a b c)` -/

/-- **Bridge**: `GBR`'s combined `phi2`-action, at the envelope's own
source carrier spelling. -/
noncomputable instance instModuleGtensorABCRaw :
    Module (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
      (GBR Γ a b c) :=
  Module.compHom (GBR Γ a b c) (phi2 K Γ a b c).toRingHom

noncomputable instance instModuleGtensorABC :
    Module (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier (GBR Γ a b c) :=
  inferInstanceAs (Module
    (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (GBR Γ a b c))

instance : IsScalarTower K
    (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (GBR Γ a b c) :=
  ⟨fun k w m => by
    show (phi2 K Γ a b c) (k • w) m = k • (phi2 K Γ a b c) w m
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier (GBR Γ a b c) :=
  inferInstanceAs (IsScalarTower K
    (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (GBR Γ a b c))

/-- **`GBR`'s combined action is graded** (`phi2_mem_grading`). -/
instance : SetLike.GradedSMul
    (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (GBR.grading Γ a b c) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact phi2_mem_grading K Γ a b c hw hz

/-- `GBR`'s own native right action is a `K`-scalar tower. -/
instance : IsScalarTower K ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun k τ z => by
    show rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (FusionColumn (Γ.fuse a (b + c))) (k • τ) z
      = k • rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (FusionColumn (Γ.fuse a (b + c))) τ z
    rw [map_smul, LinearMap.smul_apply]⟩

/-- **`GBR`'s combined action commutes with the recast right action**
(`phi2_comm_right`, transported along the recast via
`GBR.recast_op_smul_def`, `GaugeChi.RouteBimod`). -/
instance : SMulCommClass (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier
    ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun w t z => by
    show (phi2 K Γ a b c) w (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
        (MulOpposite.unop t)) • z)
      = MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))
          • (phi2 K Γ a b c) w z
    rw [rGBR_apply, rGBR_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
      phi2_comm_right]⟩

/-- `GBR`'s own native right action is graded. -/
instance : GradedRightSMul (Γ.D (a + (b + c))).grading (GBR.grading Γ a b c) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (FusionColumn.grading (Γ.fuse b c))
      (FusionColumn.grading (Γ.fuse a (b + c))) hτ hw

/-- The gauge-index cast preserves the grading (a `subst`-`rfl` fact,
mirroring `Bimod.RouteRecast`'s `stdTowerCast_mem_grading`). -/
private theorem gaugeCast_mem_grading {x y : G} (h : x = y) {i : ZMod 2}
    {τ : (Γ.D x).carrier} (hτ : τ ∈ (Γ.D x).grading i) :
    (Γ.gaugeCast h).toAlgEquiv τ ∈ (Γ.D y).grading i := by
  subst h
  exact hτ

/-- `GBR`'s recast right action (`D_{a+b+c}`) is graded (through the
grading-preservation of the gauge-index cast). -/
instance : GradedRightSMul (Γ.D (a + b + c)).grading (GBR.grading Γ a b c) where
  smul_mem _ _ _ _ hτ hw := by
    rw [GBR.recast_op_smul_def]
    exact GradedRightSMul.smul_mem (gaugeCast_mem_grading K Γ (add_assoc a b c) hτ) hw

instance : IsScalarTower K ((Γ.D (a + b + c)).carrier)ᵐᵒᵖ (GBR Γ a b c) :=
  ⟨fun k τ z => by
    show MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
        (MulOpposite.unop (k • τ))) • z
      = k • (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          (MulOpposite.unop τ)) • z)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ z⟩

/-- **`GBR` is a `gTripleEnv Γ a b c`-module**: the combined `phi1`/`phi2`
action (direct iteration, in the envelope's own order) and `GBR`'s own
recast right `D_{a+b+c}`-action assemble via `Bimod.module`. -/
noncomputable instance instModuleGTripleEnv : Module (gTripleEnv K Γ a b c) (GBR Γ a b c) :=
  Bimod.module (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D (a + b + c)).grading
    (GBR.grading Γ a b c)

/-! #### Slot-generator evaluation (M8a-8d′-iii-a″-style, one level
shorter than `Q4`'s, since `GBR` has only three slots) -/

theorem gtensorSourceRaw_smul_def
    (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (z : GBR Γ a b c) :
    w • z = phi2 K Γ a b c w z := rfl

/-- **The `a`-slot-embedding bridge**: the envelope-source element
obtained by embedding `x : D_a` via the two-fold `includeLeft` chain
matching the envelope's own bracket order acts on `GBR`, on *every*
element, exactly as `GBR`'s own registered `a`-slot action of `x`. -/
theorem aEmbed_smul
    (x₀ : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) (x : (Γ.D a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
    (x₁ : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading x₀)
    (z : GBR Γ a b c) :
    x₁ • z = x • z := by
  rw [gtensorSourceRaw_smul_def, aslot_apply]
  have h1 : phi1 K Γ a b c x₀ = fA K Γ a b c x := by
    rw [hx₀]
    show fA K Γ a b c x * fB K Γ a b c 1 = fA K Γ a b c x
    rw [map_one, mul_one]
  rw [hx₁]
  show (phi1 K Γ a b c x₀ * fC K Γ a b c 1) z = fA K Γ a b c x z
  rw [map_one, mul_one, h1]

/-- **The `b`-slot-embedding bridge**. -/
theorem bEmbed_smul
    (y₀ : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) (y : (Γ.D b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
    (y₁ : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading y₀)
    (z : GBR Γ a b c) :
    y₁ • z = y • z := by
  rw [gtensorSourceRaw_smul_def, bslot_apply]
  have h1 : phi1 K Γ a b c y₀ = fB K Γ a b c y := by
    rw [hy₀]
    show fA K Γ a b c 1 * fB K Γ a b c y = fB K Γ a b c y
    rw [map_one, one_mul]
  rw [hy₁]
  show (phi1 K Γ a b c y₀ * fC K Γ a b c 1) z = fB K Γ a b c y z
  rw [map_one, mul_one, h1]

/-- **The `c`-slot-embedding bridge** — a single `includeRight`, since
`D_c` is the envelope source's own outermost right factor. -/
theorem cEmbed_smul
    (w₀ : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (w : (Γ.D c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading w)
    (z : GBR Γ a b c) :
    w₀ • z = w • z := by
  rw [gtensorSourceRaw_smul_def, cslot_apply, hw₀]
  show (phi1 K Γ a b c 1 * fC K Γ a b c w) z = fC K Γ a b c w z
  rw [map_one, one_mul]

end GBR

/-! ### The interface: `gInterSpace = gradedHomF` -/

/-- The tensor grading of `gTripleEnv`'s own envelope tensor
(`Superfusion.tensorGrading`, M7f-1a's grading making `𝒜 ᵍ⊗ ℬ` a graded
algebra) — the grading `superEquivariant`/`gradedHomF` quantify over
when `𝒯 := gTripleEnv K Γ a b c`. -/
noncomputable abbrev gEnvGrading : ZMod 2 → Submodule K (gTripleEnv K Γ a b c) :=
  Superfusion.tensorGrading (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
    (SuperOp.grading (Γ.D (a + b + c)).grading)

namespace GBL

/-- **`GBL`'s `gTripleEnv`-action is graded**: `actionHom_mem_tensorGrading`
instantiated at `GBL`'s own `gTripleEnv`-module structure. -/
instance : SetLike.GradedSMul (gEnvGrading K Γ a b c) (grading Γ a b c) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact actionHom_mem_tensorGrading _ _ _ hw hz

end GBL

namespace GBR

/-- **`GBR`'s `gTripleEnv`-action is graded**. -/
instance : SetLike.GradedSMul (gEnvGrading K Γ a b c) (grading Γ a b c) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact actionHom_mem_tensorGrading _ _ _ hw hz

end GBR

theorem GBL_gEnv_smul_def (w : gTripleEnv K Γ a b c) (m : GBL Γ a b c) :
    w • m = actionHom (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) w m := rfl

theorem GBR_gEnv_smul_def (w : gTripleEnv K Γ a b c) (m : GBR Γ a b c) :
    w • m = actionHom (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (Γ.D (a + b + c)).grading (GBR.grading Γ a b c) w m := rfl

/-- `SMulCommClass K (gTripleEnv K Γ a b c) (GBL Γ a b c)`: `actionHom w`
is already `K`-linear for every fixed `w`, since it is a bundled
`M →ₗ[K] M` map by construction. Needed for `gradedHomF`'s own
`[SMulCommClass K T N]` hypothesis. -/
instance : SMulCommClass K (gTripleEnv K Γ a b c) (GBL Γ a b c) :=
  ⟨fun k w m => (map_smul (actionHom (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) w) k m).symm⟩

instance : SMulCommClass K (gTripleEnv K Γ a b c) (GBR Γ a b c) :=
  ⟨fun k w m => (map_smul (actionHom (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (Γ.D (a + b + c)).grading (GBR.grading Γ a b c) w) k m).symm⟩

/-- `K` is a scalar tower for `gTripleEnv K Γ a b c` on `GBL`/`GBR` —
needed as the `[IsScalarTower K T M] [IsScalarTower K T N]` hypothesis of
`superEquivariantAt_of_includeLeft_includeRight` at the OUTER (sop-tensor)
level. -/
instance : IsScalarTower K (gTripleEnv K Γ a b c) (GBL Γ a b c) :=
  ⟨fun k w m => by simp only [GBL_gEnv_smul_def, map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (gTripleEnv K Γ a b c) (GBR Γ a b c) :=
  ⟨fun k w m => by simp only [GBR_gEnv_smul_def, map_smul, LinearMap.smul_apply]⟩

/-! #### Bridging `GBR`'s slot-embedding lemmas to the bundled
`.gtensor.carrier` spelling

`GBR.aEmbed_smul`–`cEmbed_smul` (defined above) are stated at the
UNFOLDED `Superfusion.tensorGrading … ᵍ⊗[K] …` spelling (matching `phi1`/
`phi2`'s own domains); `actionHom_includeLeft_apply`'s own conclusion, by
contrast, lands at the BUNDLED `.gtensor.carrier` spelling (since
`actionHom`'s algebra parameter `𝒜` is stated as a bundled `.grading`
projection).  The two spellings are `rfl`-equal elementwise but not
`instances`-transparently equal (the M8a-8d′-iii-a′ lesson), so each
bridge below is a single elementwise `rfl` transport — mirroring
`QuadInterface2.lean`'s `Q4_aEmbed_bundled`–`_dEmbed_bundled`. -/

private theorem GBR_aEmbed_bundled
    (x₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (x : (Γ.D a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
    (x₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading x₀)
    (z : GBR Γ a b c) :
    x₁ • z = x • z := by
  have hcol : x₁ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
      (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) := by
    rw [hx₁, hx₀]; rfl
  rw [hcol]
  exact GBR.aEmbed_smul K Γ a b c _ x rfl _ rfl z

private theorem GBR_bEmbed_bundled
    (y₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (y : (Γ.D b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
    (y₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading y₀)
    (z : GBR Γ a b c) :
    y₁ • z = y • z := by
  have hcol : y₁ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
      (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) := by
    rw [hy₁, hy₀]; rfl
  rw [hcol]
  exact GBR.bEmbed_smul K Γ a b c _ y rfl _ rfl z

private theorem GBR_cEmbed_bundled
    (w₀ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) (w' : (Γ.D c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading w')
    (z : GBR Γ a b c) :
    w₀ • z = w' • z := by
  have hcol : w₀ = GradedTensorProduct.includeRight
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading w' := by
    rw [hw₀]; rfl
  rw [hcol]
  exact GBR.cEmbed_smul K Γ a b c _ w' rfl z

variable {K} {Γ} {a b c}

/-- **The `⊇` direction, `a`-slot**: a `gTripleEnv`-super-equivariant `f`
of degree `e` is super-equivariant for the `D_a`-slot action, of the same
degree. -/
theorem superEquivariant_a_of_gEnv {e : ZMod 2} (f : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gTripleEnv K Γ a b c⦄,
      w ∈ gEnvGrading K Γ a b c i → ∀ m : GBL Γ a b c,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D a).carrier⦄, x ∈ (Γ.D a).grading i →
      ∀ m : GBL Γ a b c, f (x • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • f m) := by
  intro i x hx m
  have hx0mem := Superfusion.includeLeft_mem_tensorGrading (Γ.D a).grading (Γ.D b).grading hx
  set x₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier :=
    GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
      (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
    with hx1def
  have hx1mem : x₁ ∈ Superfusion.tensorGrading ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading i := by
    rw [hx1def]
    exact Superfusion.includeLeft_mem_tensorGrading ((Γ.D a).gtensor (Γ.D b)).grading
      (Γ.D c).grading hx0mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (SuperOp.grading (Γ.D (a + b + c)).grading) hx1mem
  have key := hequiv hwmem m
  rw [GBL_gEnv_smul_def, actionHom_includeLeft_apply,
    GBL.aEmbed K Γ a b c
      (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) x rfl x₁ hx1def] at key
  rw [key, GBR_gEnv_smul_def, actionHom_includeLeft_apply,
    GBR_aEmbed_bundled K Γ a b c
      (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) x rfl x₁ hx1def]

/-- **The `⊇` direction, `b`-slot**. -/
theorem superEquivariant_b_of_gEnv {e : ZMod 2} (f : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gTripleEnv K Γ a b c⦄,
      w ∈ gEnvGrading K Γ a b c i → ∀ m : GBL Γ a b c,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D b).carrier⦄, y ∈ (Γ.D b).grading i →
      ∀ m : GBL Γ a b c, f (y • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • f m) := by
  intro i y hy m
  have hy0mem := Superfusion.includeRight_mem_tensorGrading (Γ.D a).grading (Γ.D b).grading hy
  set y₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier :=
    GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
      (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
    with hy1def
  have hy1mem : y₁ ∈ Superfusion.tensorGrading ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading i := by
    rw [hy1def]
    exact Superfusion.includeLeft_mem_tensorGrading ((Γ.D a).gtensor (Γ.D b)).grading
      (Γ.D c).grading hy0mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (SuperOp.grading (Γ.D (a + b + c)).grading) hy1mem
  have key := hequiv hwmem m
  rw [GBL_gEnv_smul_def, actionHom_includeLeft_apply,
    GBL.bEmbed K Γ a b c
      (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) y rfl y₁ hy1def] at key
  rw [key, GBR_gEnv_smul_def, actionHom_includeLeft_apply,
    GBR_bEmbed_bundled K Γ a b c
      (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) y rfl y₁ hy1def]

/-- **The `⊇` direction, `c`-slot** — a single `includeRight`, since
`D_c` is the envelope source's own outermost right factor. -/
theorem superEquivariant_c_of_gEnv {e : ZMod 2} (f : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gTripleEnv K Γ a b c⦄,
      w ∈ gEnvGrading K Γ a b c i → ∀ m : GBL Γ a b c,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃w' : (Γ.D c).carrier⦄, w' ∈ (Γ.D c).grading i →
      ∀ m : GBL Γ a b c, f (w' • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w' • f m) := by
  intro i w' hw' m
  set w₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier :=
    GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w'
    with hw1def
  have hw1mem : w₁ ∈ Superfusion.tensorGrading ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading i := by
    rw [hw1def]
    exact Superfusion.includeRight_mem_tensorGrading ((Γ.D a).gtensor (Γ.D b)).grading
      (Γ.D c).grading hw'
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (SuperOp.grading (Γ.D (a + b + c)).grading) hw1mem
  have key := hequiv hwmem m
  rw [GBL_gEnv_smul_def, actionHom_includeLeft_apply,
    GBL.cEmbed K Γ a b c w₁ w' hw1def] at key
  rw [key, GBR_gEnv_smul_def, actionHom_includeLeft_apply,
    GBR_cEmbed_bundled K Γ a b c w₁ w' hw1def]

variable (K) (Γ) (a b c)

/-- **The `⊇` direction, assembled (five conditions)**: a `f ∈
gradedHomF` (i.e. `gTripleEnv`-homogeneous of degree `e` and
`gTripleEnv`-super-equivariant of degree `e`) satisfies `gInterSpace`'s
`homGrading` condition and the three slot super-equivariances. -/
theorem gInterSpace_four_conditions_of_mem_gradedHomF {e : ZMod 2}
    {f : GBL Γ a b c →ₗ[K] GBR Γ a b c}
    (hf : f ∈ gradedHomF (GBL.grading Γ a b c) (gEnvGrading K Γ a b c) (GBR.grading Γ a b c) e) :
    f ∈ homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c) e
      ∧ f ∈ superEquivariant (Γ.D a).grading e
      ∧ f ∈ superEquivariant (Γ.D b).grading e
      ∧ f ∈ superEquivariant (Γ.D c).grading e := by
  rw [mem_gradedHomF_iff] at hf
  obtain ⟨hgrad, hequiv⟩ := hf
  rw [mem_superEquivariant] at hequiv
  exact ⟨hgrad, superEquivariant_a_of_gEnv f hequiv, superEquivariant_b_of_gEnv f hequiv,
    superEquivariant_c_of_gEnv f hequiv⟩

/-- The associativity recast between `GBL`'s natural right-coefficient
tower `D_{a+b+c}` and `GBR`'s natural tower `D_{a+(b+c)}` — the same
`Γ.gaugeCast (add_assoc a b c)` `gInterSpace`'s own `rightSemilinear`
condition is stated along. -/
theorem rightSemilinear_of_gEnv {e : ZMod 2} {f : GBL Γ a b c →ₗ[K] GBR Γ a b c}
    (hgrad : f ∈ homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c) e)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gTripleEnv K Γ a b c⦄,
      w ∈ gEnvGrading K Γ a b c i → ∀ m : GBL Γ a b c,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    f ∈ rightSemilinear ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom) := by
  have hsop : ∀ ⦃j : ZMod 2⦄ ⦃τ : (Γ.D (a + b + c)).carrier⦄,
      τ ∈ (Γ.D (a + b + c)).grading j → ∀ m : GBL Γ a b c,
        f (rightActionHom (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
            (SuperOp.op _ τ) m)
          = ((sgn (e * j) : ℤˣ) : ℤ) •
              rightActionHom (Γ.D (a + b + c)).grading (GBR.grading Γ a b c)
                (SuperOp.op _ τ) (f m) := by
    intro j τ hτ m
    have hmem := Superfusion.includeRight_mem_tensorGrading
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (SuperOp.grading (Γ.D (a + b + c)).grading) hτ
    have key := hequiv hmem m
    rwa [GBL_gEnv_smul_def, actionHom_includeRight_apply, GBR_gEnv_smul_def,
      actionHom_includeRight_apply] at key
  have hunsigned : ∀ ⦃j : ZMod 2⦄ ⦃τ : (Γ.D (a + b + c)).carrier⦄,
      τ ∈ (Γ.D (a + b + c)).grading j → ∀ m : GBL Γ a b c,
        f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
    intro j τ hτ m
    exact (rightActionHom_equivariant_iff_rightSemilinear (Γ.D (a + b + c)).grading
      (GBL.grading Γ a b c) (GBR.grading Γ a b c) hgrad hτ).mp (hsop hτ) m
  rw [mem_rightSemilinear]
  intro t m
  show f (MulOpposite.op t • m)
    = MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t) • f m
  induction t using DirectSum.Decomposition.inductionOn (Γ.D (a + b + c)).grading with
  | zero => simp [map_zero, MulOpposite.op_zero, zero_smul]
  | homogeneous t' => exact hunsigned t'.2 m
  | add t1 t2 h1 h2 => simp only [MulOpposite.op_add, add_smul, map_add]; rw [h1, h2]

/-- **The `⊇` direction, assembled**: a `f ∈ gradedHomF` (i.e.
`gTripleEnv`-homogeneous and `gTripleEnv`-super-equivariant of degree `e`)
satisfies all five of `gInterSpace`'s conditions. -/
theorem gInterSpace_of_mem_gradedHomF {e : ZMod 2} {f : GBL Γ a b c →ₗ[K] GBR Γ a b c}
    (hf : f ∈ gradedHomF (GBL.grading Γ a b c) (gEnvGrading K Γ a b c) (GBR.grading Γ a b c) e) :
    f ∈ gInterSpace K Γ a b c e := by
  obtain ⟨hgrad, ha, hb, hc⟩ := gInterSpace_four_conditions_of_mem_gradedHomF K Γ a b c hf
  rw [mem_gradedHomF_iff] at hf
  obtain ⟨_, hequiv⟩ := hf
  rw [mem_superEquivariant] at hequiv
  rw [mem_gInterSpace_iff]
  exact ⟨hgrad, ha, hb, hc, rightSemilinear_of_gEnv K Γ a b c hgrad hequiv⟩

/-! ### The `⊆` direction: `gInterSpace`'s conditions imply `gTripleEnv`-super-equivariance

Everything below uses the BUNDLED `.gtensor.grading`/`.gtensor.carrier`
spelling throughout — matching `GBL.aEmbed`–`cEmbed`'s own spelling
verbatim, since `T := (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier`
(the ONLY spelling carrying `GBL`/`GBR`'s registered `Module`/
`IsScalarTower` instances) unifies against `𝒜 ᵍ⊗[K] ℬ` without an
instance mismatch (the M8a-8d′-iii-a′ lesson). -/

/-- The `(D_a, D_b) → ((D_a ᵍ⊗ D_b), D_c) = ` envelope-source embed, as a
single `AlgHom` (needed so `superEquivariantAt_of_includeLeft_includeRight`'s
`map_mul`/`map_add`/`map_smul` machinery applies to it directly). -/
private noncomputable def ιAB :
    ((Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) →ₐ[K]
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier :=
  GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading

/-- The identity, re-typed from the RAW `AB.grading ᵍ⊗ C.grading` to the
envelope's own SOURCE carrier — the two are `rfl`-equal (both ultimately
reduce to the same `GradedTensorProduct` construction) but NOT
`instances`-transparently equal, so `AlgHom.id` itself does not typecheck
against the mismatched instance packaging; built by hand instead, with
`rfl` proofs for every field (mirrors `QuadInterface2.lean`'s `ιABCD`). -/
private noncomputable def ιABC :
    (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) →ₐ[K]
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **The `⊆` direction, envelope-source-level equivariance**: the three
slot super-equivariances assemble, via `superEquivariantAt_of_includeLeft_includeRight`
applied at the envelope source's own two internal levels (`(A,B)`,
`(AB,C)`, both landing at `T := ` the envelope source's own carrier),
chained through `GBL.aEmbed`–`cEmbed`/`GBR_aEmbed_bundled`–`_cEmbed_bundled`,
into super-equivariance for the envelope source's OWN action on `GBL`/
`GBR`, at EVERY homogeneous element (not merely generators). -/
theorem gSource_equivariant_of_slots {e : ZMod 2} {f : GBL Γ a b c →ₗ[K] GBR Γ a b c}
    (ha : f ∈ superEquivariant (Γ.D a).grading e)
    (hb : f ∈ superEquivariant (Γ.D b).grading e)
    (hc : f ∈ superEquivariant (Γ.D c).grading e) :
    ∀ ⦃i : ZMod 2⦄ ⦃w : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      w ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading i → ∀ m : GBL Γ a b c,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m) := by
  rw [mem_superEquivariant] at ha hb hc
  have hAB := superEquivariantAt_of_includeLeft_includeRight
      (Γ.D a).grading (Γ.D b).grading (ιAB K Γ a b c)
      (f := f) (e := e)
      (fun j x hx m => by
        have hcol : ιAB K Γ a b c
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
          = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
              (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) := rfl
        rw [hcol, GBL.aEmbed K Γ a b c _ x rfl _ rfl,
          GBR_aEmbed_bundled K Γ a b c _ x rfl _ rfl]
        exact ha hx m)
      (fun k y hy m => by
        have hcol : ιAB K Γ a b c
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
          = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
              (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) := rfl
        rw [hcol, GBL.bEmbed K Γ a b c _ y rfl _ rfl,
          GBR_bEmbed_bundled K Γ a b c _ y rfl _ rfl]
        exact hb hy m)
  have hABC := superEquivariantAt_of_includeLeft_includeRight
      ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading (ιABC K Γ a b c)
      (f := f) (e := e)
      (fun j w hw m => by
        have hcol : ιABC K Γ a b c
            (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w)
          = ιAB K Γ a b c w := rfl
        rw [hcol]
        exact hAB hw m)
      (fun k w' hw' m => by
        have hcol : ιABC K Γ a b c
            (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w')
          = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading w' :=
          rfl
        rw [hcol, GBL.cEmbed K Γ a b c _ w' rfl, GBR_cEmbed_bundled K Γ a b c _ w' rfl]
        exact hc hw' m)
  intro i w hw m
  exact hABC hw m

set_option maxHeartbeats 1000000 in
/-- **The `⊆` direction, assembled**: all five `gInterSpace` conditions
(`homGrading`, the three slot super-equivariances, and `rightSemilinear`)
assemble into full `gTripleEnv`-super-equivariance — the source-level
equivariance of `gSource_equivariant_of_slots` supplies `hL` (via
`GBL_gEnv_smul_def`/`GBR_gEnv_smul_def` + `actionHom_includeLeft_apply`,
since `gTripleEnv`, unlike the envelope source, is a plain `abbrev` for
the RAW graded tensor product, so `AlgHom.id` typechecks against it
directly with no instance mismatch); `hR` is the sop-generator condition
of `rightActionHom_equivariant_iff_rightSemilinear`, reconciled with
`rightSemilinear` via `GBR.recast_op_smul_def`. -/
theorem gEnv_equivariant_of_gInterSpace {e : ZMod 2} {f : GBL Γ a b c →ₗ[K] GBR Γ a b c}
    (hgrad : f ∈ homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c) e)
    (ha : f ∈ superEquivariant (Γ.D a).grading e)
    (hb : f ∈ superEquivariant (Γ.D b).grading e)
    (hc : f ∈ superEquivariant (Γ.D c).grading e)
    (hR : f ∈ rightSemilinear ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom)) :
    ∀ ⦃i : ZMod 2⦄ ⦃w : gTripleEnv K Γ a b c⦄,
      w ∈ gEnvGrading K Γ a b c i → ∀ m : GBL Γ a b c,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m) := by
  rw [mem_rightSemilinear] at hR
  have hslots := gSource_equivariant_of_slots K Γ a b c ha hb hc
  have hunsigned : ∀ ⦃j : ZMod 2⦄ ⦃τ : (Γ.D (a + b + c)).carrier⦄,
      τ ∈ (Γ.D (a + b + c)).grading j → ∀ m : GBL Γ a b c,
        f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
    intro j τ hτ m
    rw [GBR.recast_op_smul_def]
    exact hR τ m
  exact superEquivariantAt_of_includeLeft_includeRight
    (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
    (SuperOp.grading (Γ.D (a + b + c)).grading)
    (AlgHom.id K (gTripleEnv K Γ a b c)) (f := f) (e := e)
    (fun j x hx m => by
      have hcol : (AlgHom.id K (gTripleEnv K Γ a b c))
          (GradedTensorProduct.includeLeft (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
            (SuperOp.grading (Γ.D (a + b + c)).grading) x)
        = GradedTensorProduct.includeLeft (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
            (SuperOp.grading (Γ.D (a + b + c)).grading) x := rfl
      rw [hcol, GBL_gEnv_smul_def, actionHom_includeLeft_apply,
        GBR_gEnv_smul_def, actionHom_includeLeft_apply]
      exact hslots hx m)
    (fun k τ hτ m => by
      have hcol : (AlgHom.id K (gTripleEnv K Γ a b c))
          (GradedTensorProduct.includeRight (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
            (SuperOp.grading (Γ.D (a + b + c)).grading) τ)
        = GradedTensorProduct.includeRight (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
            (SuperOp.grading (Γ.D (a + b + c)).grading) τ := rfl
      rw [hcol, GBL_gEnv_smul_def, actionHom_includeRight_apply,
        GBR_gEnv_smul_def, actionHom_includeRight_apply]
      set τ' := SuperOp.unop (Γ.D (a + b + c)).grading τ with hτ'def
      have hτ'mem : τ' ∈ (Γ.D (a + b + c)).grading k := hτ
      rw [show τ = SuperOp.op (Γ.D (a + b + c)).grading τ'
          from (SuperOp.op_unop (Γ.D (a + b + c)).grading τ).symm]
      exact (rightActionHom_equivariant_iff_rightSemilinear (Γ.D (a + b + c)).grading
        (GBL.grading Γ a b c) (GBR.grading Γ a b c) hgrad hτ'mem).mpr (hunsigned hτ'mem) m)

/-! ### The interface, assembled -/

/-- **`mem_gInterSpace_iff_gradedHomF`**: `gInterSpace`'s five conditions
(`homGrading`, the three slot super-equivariances, `rightSemilinear`) are
EXACTLY `gradedHomF`'s two (`homGrading` and `gTripleEnv`-super
-equivariance) — the interface completing this milestone.  `⊇` is
`gInterSpace_of_mem_gradedHomF`; `⊆` assembles
`gEnv_equivariant_of_gInterSpace` (the three slots plus `rightSemilinear`
give full `gTripleEnv`-equivariance) with the verbatim `homGrading`
match. -/
theorem mem_gInterSpace_iff_gradedHomF {e : ZMod 2} {f : GBL Γ a b c →ₗ[K] GBR Γ a b c} :
    f ∈ gInterSpace K Γ a b c e ↔
      f ∈ gradedHomF (GBL.grading Γ a b c) (gEnvGrading K Γ a b c) (GBR.grading Γ a b c) e := by
  constructor
  · intro hf
    rw [mem_gInterSpace_iff] at hf
    obtain ⟨hgrad, ha, hb, hc, hR⟩ := hf
    rw [mem_gradedHomF_iff, mem_superEquivariant]
    exact ⟨hgrad, gEnv_equivariant_of_gInterSpace K Γ a b c hgrad ha hb hc hR⟩
  · exact gInterSpace_of_mem_gradedHomF K Γ a b c

/-! ### General layer: extracting the two `homGrading`-homogeneous parts
of an arbitrary `T`-linear map

For a genuinely `T`-linear (UNSIGNED, unrestricted) map `g : M →ₗ[K] N`
between two `T`-modules with `ZMod 2`-gradings `ℳ`/`𝒩` (both graded for
the `T`-action), `g` need not itself be `homGrading`-homogeneous — but it
splits, via the parity operators `parityOp ℳ`/`parityOp 𝒩` (halved by
`⅟2`, using the standing `Invertible (2 : K)`), into an even part
(`evenPartHom`, `homGrading`-degree `0`) and an odd part (`oddPartHom`,
`homGrading`-degree `1`), BOTH still (UNSIGNED) `T`-linear — since
`T`-linearity carries no sign at all, it survives the parity-projection
verbatim; the sign only enters afterwards, converting the odd part into
a genuine `gradedHomF`-degree-`1` witness via `compParityOp`
(`ParityBridge.lean`'s `compParityOp_mem_gradedHomF_of_mem_succ`). This
is the "mask" construction `ParityBridge.lean`'s docstring flags as
optional future work, specialized to exactly the amount needed here:
producing a NONZERO `gradedHomF`-witness from a nonzero `T`-linear map,
without the full internal-direct-sum packaging. -/

section ExtractHomogeneous

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]
variable {T : Type*} [Ring T] [Algebra K T]
variable [Module T M] [Module T N] [SMulCommClass K T N]

/-- **The even part** of an arbitrary `K`-linear map, via the halved
`g ± P_N ∘ g ∘ P_M` trick. -/
noncomputable def evenPartHom (g : M →ₗ[K] N) : M →ₗ[K] N :=
  (⅟(2 : K)) • (g + (parityOp 𝒩).toLinearMap ∘ₗ g ∘ₗ (parityOp ℳ).toLinearMap)

/-- **The odd part**. -/
noncomputable def oddPartHom (g : M →ₗ[K] N) : M →ₗ[K] N :=
  (⅟(2 : K)) • (g - (parityOp 𝒩).toLinearMap ∘ₗ g ∘ₗ (parityOp ℳ).toLinearMap)

/-- `evenPartHom`, elementwise, at the DIRECT `parityOp`-application
spelling (bridging the `.toLinearMap`-application spelling `evenPartHom`'s
own definition uses, via `LinearEquiv.coe_toLinearMap`, ONCE — every
downstream proof uses this bridge instead of re-deriving it). -/
theorem evenPartHom_apply (g : M →ₗ[K] N) (m : M) :
    evenPartHom ℳ 𝒩 g m = (⅟(2 : K)) • (g m + parityOp 𝒩 (g (parityOp ℳ m))) := by
  simp only [evenPartHom, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap]

/-- `oddPartHom`, elementwise. -/
theorem oddPartHom_apply (g : M →ₗ[K] N) (m : M) :
    oddPartHom ℳ 𝒩 g m = (⅟(2 : K)) • (g m - parityOp 𝒩 (g (parityOp ℳ m))) := by
  simp only [oddPartHom, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap]

theorem evenPartHom_add_oddPartHom (g : M →ₗ[K] N) :
    evenPartHom ℳ 𝒩 g + oddPartHom ℳ 𝒩 g = g := by
  refine LinearMap.ext fun m => ?_
  rw [LinearMap.add_apply, evenPartHom_apply, oddPartHom_apply, ← smul_add,
    show (g m + parityOp 𝒩 (g (parityOp ℳ m))) + (g m - parityOp 𝒩 (g (parityOp ℳ m)))
        = (2 : K) • g m from by module,
    smul_smul, invOf_mul_self, one_smul]

omit [Invertible (2 : K)] in
/-- **The key sign/degree computation**, shared by the `homGrading`
membership of both `evenPartHom` and `oddPartHom`: for `m ∈ ℳ i`,
`g m ± sgn(i) • P_𝒩(g m) = 2 • modProj 𝒩 (i + ε) (g m)`, where `ε = 0`
for the `+` sign and `ε = 1` for the `-` sign — the closed form of
"`P_𝒩` sorts `g m`'s own two graded pieces by the requested sign". -/
private theorem hPgP (g : M →ₗ[K] N) {i : ZMod 2} {m : M} (hm : m ∈ ℳ i) :
    parityOp 𝒩 (g (parityOp ℳ m)) = ((sgn i : ℤˣ) : ℤ) • parityOp 𝒩 (g m) := by
  rw [parityOp_of_mem ℳ hm, map_zsmul, map_zsmul]

omit [Invertible (2 : K)] in
private theorem parityOp_apply_eq_modProj_sub (n : N) :
    parityOp 𝒩 n = modProj 𝒩 0 n - modProj 𝒩 1 n := by
  rw [parityOp_apply]; rfl

theorem evenPartHom_mem_homGrading (g : M →ₗ[K] N) :
    evenPartHom ℳ 𝒩 g ∈ homGrading ℳ 𝒩 (0 : ZMod 2) := by
  intro i m hm
  rw [add_zero, evenPartHom_apply, hPgP ℳ 𝒩 g hm, parityOp_apply_eq_modProj_sub 𝒩 (g m)]
  have hgm := modProj_zero_add_modProj_one 𝒩 (g m)
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [sgn_zero]
    simp only [Units.val_one, one_smul]
    rw [show g m + (modProj 𝒩 0 (g m) - modProj 𝒩 1 (g m)) = modProj 𝒩 0 (g m) + modProj 𝒩 0 (g m)
        from by nth_rewrite 1 [← hgm]; abel, ← two_smul K, smul_smul, invOf_mul_self, one_smul]
    exact modProj_mem 𝒩 0 (g m)
  · rw [sgn_one]
    simp only [units_sign_eq, Units.val_neg, Units.val_one, neg_smul, one_smul]
    rw [show g m + -(modProj 𝒩 0 (g m) - modProj 𝒩 1 (g m)) = modProj 𝒩 1 (g m) + modProj 𝒩 1 (g m)
        from by nth_rewrite 1 [← hgm]; abel, ← two_smul K, smul_smul, invOf_mul_self, one_smul]
    exact modProj_mem 𝒩 1 (g m)

theorem oddPartHom_mem_homGrading (g : M →ₗ[K] N) :
    oddPartHom ℳ 𝒩 g ∈ homGrading ℳ 𝒩 (1 : ZMod 2) := by
  intro i m hm
  rw [oddPartHom_apply, hPgP ℳ 𝒩 g hm, parityOp_apply_eq_modProj_sub 𝒩 (g m)]
  have hgm := modProj_zero_add_modProj_one 𝒩 (g m)
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [sgn_zero]
    simp only [Units.val_one, one_smul, show (0 : ZMod 2) + 1 = 1 from by decide]
    rw [show g m - (modProj 𝒩 0 (g m) - modProj 𝒩 1 (g m)) = modProj 𝒩 1 (g m) + modProj 𝒩 1 (g m)
        from by nth_rewrite 1 [← hgm]; abel, ← two_smul K, smul_smul, invOf_mul_self, one_smul]
    exact modProj_mem 𝒩 1 (g m)
  · rw [sgn_one]
    simp only [units_sign_eq, Units.val_neg, Units.val_one, neg_smul, one_smul,
      show (1 : ZMod 2) + 1 = 0 from by decide]
    rw [show g m - -(modProj 𝒩 0 (g m) - modProj 𝒩 1 (g m)) = modProj 𝒩 0 (g m) + modProj 𝒩 0 (g m)
        from by nth_rewrite 1 [← hgm]; abel, ← two_smul K, smul_smul, invOf_mul_self, one_smul]
    exact modProj_mem 𝒩 0 (g m)

variable (𝒯 : ZMod 2 → Submodule K T)
variable [SetLike.GradedSMul 𝒯 ℳ] [SetLike.GradedSMul 𝒯 𝒩]

omit [Invertible (2 : K)] [SMulCommClass K T N] in
/-- **`evenPartHom`/`oddPartHom` are (UNSIGNED) `T`-equivariant**,
provided `g` itself is plainly `T`-linear: `T`-linearity carries no sign,
so it commutes with the `⅟2 • (g ± P_𝒩 g P_ℳ)` construction directly,
via `parityOp_smul_of_mem` applied twice (once on each side of `g`) and
the sign-squares-to-`1` cancellation (`sgn_mul_self'`). -/
private theorem parityConj_smul_eq (g : M →ₗ[K] N) (hgT : ∀ (t : T) (m : M), g (t • m) = t • g m)
    ⦃i : ZMod 2⦄ {x : T} (hx : x ∈ 𝒯 i) (m : M) :
    parityOp 𝒩 (g (parityOp ℳ (x • m))) = x • parityOp 𝒩 (g (parityOp ℳ m)) := by
  rw [parityOp_smul_of_mem ℳ 𝒯 hx m, map_zsmul, hgT, map_zsmul,
    parityOp_smul_of_mem 𝒩 𝒯 hx (g (parityOp ℳ m)), smul_smul,
    ← Units.val_mul, sgn_mul_self', Units.val_one, one_smul]

theorem evenPartHom_mem_superEquivariant_zero (g : M →ₗ[K] N)
    (hgT : ∀ (t : T) (m : M), g (t • m) = t • g m) :
    evenPartHom ℳ 𝒩 g ∈ superEquivariant 𝒯 (M := M) (N := N) (0 : ZMod 2) := by
  rw [mem_superEquivariant_zero_iff]
  intro i x hx m
  rw [evenPartHom_apply, evenPartHom_apply, hgT, parityConj_smul_eq ℳ 𝒩 𝒯 g hgT hx,
    ← smul_add, smul_comm]

theorem oddPartHom_mem_superEquivariant_zero (g : M →ₗ[K] N)
    (hgT : ∀ (t : T) (m : M), g (t • m) = t • g m) :
    oddPartHom ℳ 𝒩 g ∈ superEquivariant 𝒯 (M := M) (N := N) (0 : ZMod 2) := by
  rw [mem_superEquivariant_zero_iff]
  intro i x hx m
  rw [oddPartHom_apply, oddPartHom_apply, hgT, parityConj_smul_eq ℳ 𝒩 𝒯 g hgT hx,
    ← smul_sub, smul_comm]

/-- **`evenPartHom g ∈ gradedHomF ℳ 𝒯 𝒩 0`**, for `g` plainly
`T`-linear. -/
theorem evenPartHom_mem_gradedHomF_zero (g : M →ₗ[K] N)
    (hgT : ∀ (t : T) (m : M), g (t • m) = t • g m) :
    evenPartHom ℳ 𝒩 g ∈ gradedHomF ℳ 𝒯 𝒩 (0 : ZMod 2) :=
  ⟨evenPartHom_mem_homGrading ℳ 𝒩 g, evenPartHom_mem_superEquivariant_zero ℳ 𝒩 𝒯 g hgT⟩

/-- **`compParityOp ℳ (oddPartHom g) ∈ gradedHomF ℳ 𝒯 𝒩 1`**, for `g`
plainly `T`-linear — via `ParityBridge.lean`'s
`compParityOp_mem_gradedHomF_of_mem_succ` (`d := 1`, `1 + 1 = 0`). -/
theorem compParityOp_oddPartHom_mem_gradedHomF_one (g : M →ₗ[K] N)
    (hgT : ∀ (t : T) (m : M), g (t • m) = t • g m) :
    compParityOp ℳ (oddPartHom ℳ 𝒩 g) ∈ gradedHomF ℳ 𝒯 𝒩 (1 : ZMod 2) := by
  have h : oddPartHom ℳ 𝒩 g ∈ homGrading ℳ 𝒩 (1 : ZMod 2)
      ⊓ superEquivariant 𝒯 (M := M) (N := N) ((1 : ZMod 2) + 1) := by
    rw [show (1 : ZMod 2) + 1 = 0 from by decide]
    exact ⟨oddPartHom_mem_homGrading ℳ 𝒩 g, oddPartHom_mem_superEquivariant_zero ℳ 𝒩 𝒯 g hgT⟩
  exact compParityOp_mem_gradedHomF_of_mem_succ ℳ 𝒯 𝒩 h

/-- **The existence witness**: from a NONZERO plainly `T`-linear map `g`,
at least one of `gradedHomF ℳ 𝒯 𝒩 0`, `gradedHomF ℳ 𝒯 𝒩 1` is nonzero —
either `evenPartHom g` itself, or `compParityOp ℳ (oddPartHom g)`
(`compParityOp` being an involution, hence injective, transports
`oddPartHom g ≠ 0` to a nonzero witness). -/
theorem exists_gradedHomF_ne_bot_of_ne_zero {g : M →ₗ[K] N} (hg : g ≠ 0)
    (hgT : ∀ (t : T) (m : M), g (t • m) = t • g m) :
    ∃ d : ZMod 2, gradedHomF ℳ 𝒯 𝒩 d ≠ ⊥ := by
  by_cases hev : evenPartHom ℳ 𝒩 g = 0
  · refine ⟨1, ?_⟩
    have hodd : oddPartHom ℳ 𝒩 g ≠ 0 := by
      intro hodd0
      apply hg
      rw [← evenPartHom_add_oddPartHom ℳ 𝒩 g, hev, hodd0, add_zero]
    have hcp : compParityOp ℳ (oddPartHom ℳ 𝒩 g) ≠ 0 := by
      intro hcp0
      exact hodd (by rw [← compParityOp_compParityOp ℳ (oddPartHom ℳ 𝒩 g), hcp0, map_zero])
    rw [Submodule.ne_bot_iff]
    exact ⟨_, compParityOp_oddPartHom_mem_gradedHomF_one ℳ 𝒩 𝒯 g hgT, hcp⟩
  · refine ⟨0, ?_⟩
    rw [Submodule.ne_bot_iff]
    exact ⟨_, evenPartHom_mem_gradedHomF_zero ℳ 𝒩 𝒯 g hgT, hev⟩

end ExtractHomogeneous

/-! ### The payoff: `gParity`, the abstract `p`

`gInterSpace = gradedHomF` (the interface) turns `SplitIsotypy.lean`'s
ungraded machinery into statements about `gInterSpace` directly: the
total dimension bound (`gradedHomF_sum_le_one`), and — via the
`ExtractHomogeneous` general layer just built, applied to the
`gTripleEnv`-linear isomorphism `GBL ≅ GBR` supplied by
`linearEquiv_splitColumn_of_finrank_eq` (both have `K`-dimension exactly
`gTripleEnvSize`) — the EXISTENCE of a parity `d` with `gInterSpace … d ≠
⊥`.  Combined, `gParity` is extracted canonically as *the* parity of the
Hom super-line: no Skolem–Noether, no choices beyond the parity itself
being determined. -/

section GParity

/-- **`gInterSpace = gradedHomF`, as submodules** (not merely membership
-wise): `Submodule.ext` off `mem_gInterSpace_iff_gradedHomF`. -/
theorem gInterSpace_eq_gradedHomF (e : ZMod 2) :
    gInterSpace K Γ a b c e
      = gradedHomF (GBL.grading Γ a b c) (gEnvGrading K Γ a b c) (GBR.grading Γ a b c) e :=
  Submodule.ext fun _ => mem_gInterSpace_iff_gradedHomF K Γ a b c

/-- **The total-dimension bound**: `SplitIsotypy.lean`'s
`gradedHomF_finrank_sum_le_one`, instantiated at `gTripleEnvSplit` (both
`GBL`/`GBR` have `K`-dimension exactly `gTripleEnvSize`). -/
theorem gradedHomF_sum_le_one :
    Module.finrank K
        ↥(gradedHomF (GBL.grading Γ a b c) (gEnvGrading K Γ a b c) (GBR.grading Γ a b c) 0)
      + Module.finrank K
          ↥(gradedHomF (GBL.grading Γ a b c) (gEnvGrading K Γ a b c) (GBR.grading Γ a b c) 1)
      ≤ 1 := by
  haveI := gbl_finite K Γ a b c
  haveI := gbr_finite K Γ a b c
  exact gradedHomF_finrank_sum_le_one (GBL.grading Γ a b c) (GBR.grading Γ a b c)
    (gEnvGrading K Γ a b c) (gTripleEnvSplit K Γ a b c) (gTripleEnvSize_ne_zero K Γ a b c)
    (finrank_GBL_eq_gTripleEnvSize K Γ a b c) (finrank_GBR_eq_gTripleEnvSize K Γ a b c)

/-- **Existence**: `GBL` and `GBR`, both `K`-dimension `gTripleEnvSize`,
are both `gTripleEnv`-linearly isomorphic to the same `SplitColumn`
(`linearEquiv_splitColumn_of_finrank_eq`); composing gives a NONZERO
`gTripleEnv`-linear isomorphism `GBL ≃ₗ[gTripleEnv] GBR`, which
`exists_gradedHomF_ne_bot_of_ne_zero` (the `ExtractHomogeneous` general
layer) turns into a nonzero witness at SOME parity. -/
theorem exists_gInterSpace_ne_bot : ∃ d : ZMod 2, gInterSpace K Γ a b c d ≠ ⊥ := by
  haveI := gbl_finite K Γ a b c
  haveI := gbr_finite K Γ a b c
  haveI := gbl_nontrivial K Γ a b c
  obtain ⟨fM⟩ := linearEquiv_splitColumn_of_finrank_eq (gTripleEnvSplit K Γ a b c)
    (gTripleEnvSize_ne_zero K Γ a b c) (finrank_GBL_eq_gTripleEnvSize K Γ a b c)
  obtain ⟨fN⟩ := linearEquiv_splitColumn_of_finrank_eq (gTripleEnvSplit K Γ a b c)
    (gTripleEnvSize_ne_zero K Γ a b c) (finrank_GBR_eq_gTripleEnvSize K Γ a b c)
  set φ := fM.trans fN.symm with hφdef
  set g : GBL Γ a b c →ₗ[K] GBR Γ a b c := φ.toLinearMap.restrictScalars K with hgdef
  have hφT : ∀ (t : gTripleEnv K Γ a b c) (m : GBL Γ a b c), g (t • m) = t • g m :=
    fun t m => φ.map_smul t m
  have hφne : g ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : GBL Γ a b c)
    have h2 : ∀ y : GBL Γ a b c, φ y = 0 := fun y => by
      have := LinearMap.congr_fun h0 y
      simpa [hgdef] using this
    exact hx (φ.injective (by rw [h2 x, h2 0]))
  obtain ⟨d, hd⟩ := exists_gradedHomF_ne_bot_of_ne_zero (GBL.grading Γ a b c) (GBR.grading Γ a b c)
    (gEnvGrading K Γ a b c) hφne hφT
  exact ⟨d, by rw [gInterSpace_eq_gradedHomF]; exact hd⟩

/-- **`gParity Γ a b c`**: THE PAPER'S `p`, defined canonically as the
parity of the Hom super-line — the unique `d : ZMod 2` with
`gInterSpace Γ a b c d ≠ ⊥`.  No Skolem–Noether, no choices beyond the
parity itself being determined (`Exists.choose` on
`exists_gInterSpace_ne_bot`). -/
noncomputable def gParity : ZMod 2 :=
  (exists_gInterSpace_ne_bot K Γ a b c).choose

theorem gParity_spec : gInterSpace K Γ a b c (gParity K Γ a b c) ≠ ⊥ :=
  (exists_gInterSpace_ne_bot K Γ a b c).choose_spec

/-- **Uniqueness of `gParity`**: if `gInterSpace … d ≠ ⊥` for some `d`,
then `d = gParity Γ a b c` — via `ParityBridge.lean`'s
`parityConcentration` (fed by `gradedHomF_sum_le_one`): the witness at
`gParity` forces the OTHER parity's `gradedHomF` piece to be `⊥`, so no
other `d` can also be nonzero. -/
theorem gParity_unique {d : ZMod 2} (hd : gInterSpace K Γ a b c d ≠ ⊥) :
    d = gParity K Γ a b c := by
  by_contra hne
  have hd1 : d = gParity K Γ a b c + 1 := by
    rcases zmod2_cases d with h0 | h1
    · rcases zmod2_cases (gParity K Γ a b c) with h0' | h1'
      · exact absurd (h0.trans h0'.symm) hne
      · rw [h0, h1']; decide
    · rcases zmod2_cases (gParity K Γ a b c) with h0' | h1'
      · rw [h1, h0']; decide
      · exact absurd (h1.trans h1'.symm) hne
  haveI := gbl_finite K Γ a b c
  haveI := gbr_finite K Γ a b c
  have hle := gradedHomF_sum_le_one K Γ a b c
  have hspec := gParity_spec K Γ a b c
  rw [gInterSpace_eq_gradedHomF] at hspec hd
  obtain ⟨hbot, -, -⟩ := parityConcentration (GBL.grading Γ a b c) (gEnvGrading K Γ a b c)
    (GBR.grading Γ a b c) hle hspec
  rw [hd1] at hd
  exact hd hbot

theorem exists_gIntertwiner : ∃ t ∈ gInterSpace K Γ a b c (gParity K Γ a b c), t ≠ 0 :=
  Submodule.ne_bot_iff _ |>.mp (gParity_spec K Γ a b c)

/-- **`gIntertwiner_bijective`**: every nonzero member of `gInterSpace …
(gParity …)` is bijective — the split-isotypy Schur route.  Both `GBL`
and `GBR`, at `K`-dimension exactly `gTripleEnvSize`, are SIMPLE
`gTripleEnv`-modules (`isSimpleModule_of_finrank_eq_split`); at
`gParity = 0`, `t` itself is already `gTripleEnv`-linear
(`toTLinearOfMemSuperEquivariantZero`); at `gParity = 1`, `compParityOp t`
is (`compParityOp_mem_superEquivariant_succ`, landing back at degree
`1 + 1 = 0`), and `t` is recovered as `(compParityOp t) ∘ (parityOp …)`
(an involution) — a composite of two bijections. Either way, Schur's
Lemma (`LinearMap.bijective_of_ne_zero`) gives bijectivity of the
`gTripleEnv`-linear witness, transported back to `t`. -/
theorem gIntertwiner_bijective {t : GBL Γ a b c →ₗ[K] GBR Γ a b c}
    (ht : t ∈ gInterSpace K Γ a b c (gParity K Γ a b c)) (htne : t ≠ 0) :
    Function.Bijective t := by
  haveI := gbl_finite K Γ a b c
  haveI := gbr_finite K Γ a b c
  haveI : IsSimpleModule (gTripleEnv K Γ a b c) (GBL Γ a b c) :=
    isSimpleModule_of_finrank_eq_split (gTripleEnvSplit K Γ a b c) (gTripleEnvSize_ne_zero K Γ a b c)
      (finrank_GBL_eq_gTripleEnvSize K Γ a b c)
  haveI : IsSimpleModule (gTripleEnv K Γ a b c) (GBR Γ a b c) :=
    isSimpleModule_of_finrank_eq_split (gTripleEnvSplit K Γ a b c) (gTripleEnvSize_ne_zero K Γ a b c)
      (finrank_GBR_eq_gTripleEnvSize K Γ a b c)
  rw [gInterSpace_eq_gradedHomF, mem_gradedHomF_iff] at ht
  obtain ⟨-, hequivMem⟩ := ht
  rcases zmod2_cases (gParity K Γ a b c) with hp | hp
  · rw [hp] at hequivMem
    have hbij : Function.Bijective
        (toTLinearOfMemSuperEquivariantZero (gEnvGrading K Γ a b c) t hequivMem) :=
      LinearMap.bijective_of_ne_zero (fun h => htne (by
        have heq := congrArg (fun f : GBL Γ a b c →ₗ[gTripleEnv K Γ a b c] GBR Γ a b c =>
          (f : GBL Γ a b c → GBR Γ a b c)) h
        simp only [toTLinearOfMemSuperEquivariantZero] at heq
        exact DFunLike.coe_injective heq))
    exact hbij
  · have hequivMem1 : t ∈ superEquivariant (gEnvGrading K Γ a b c) (M := GBL Γ a b c)
        (N := GBR Γ a b c) (1 : ZMod 2) := by rw [hp] at hequivMem; exact hequivMem
    have hcpMem : compParityOp (GBL.grading Γ a b c) t
        ∈ superEquivariant (gEnvGrading K Γ a b c) (M := GBL Γ a b c) (N := GBR Γ a b c)
          ((1 : ZMod 2) + 1) :=
      compParityOp_mem_superEquivariant_succ (GBL.grading Γ a b c) (gEnvGrading K Γ a b c) hequivMem1
    rw [show (1 : ZMod 2) + 1 = 0 from by decide] at hcpMem
    have hcpne : compParityOp (GBL.grading Γ a b c) t ≠ 0 := by
      intro h0
      exact htne (by
        have := compParityOp_compParityOp (GBL.grading Γ a b c) t
        rw [h0, map_zero] at this
        exact this.symm)
    have hbij : Function.Bijective
        (toTLinearOfMemSuperEquivariantZero (gEnvGrading K Γ a b c)
          (compParityOp (GBL.grading Γ a b c) t) hcpMem) :=
      LinearMap.bijective_of_ne_zero (fun h => hcpne (by
        have heq := congrArg (fun f : GBL Γ a b c →ₗ[gTripleEnv K Γ a b c] GBR Γ a b c =>
          (f : GBL Γ a b c → GBR Γ a b c)) h
        simp only [toTLinearOfMemSuperEquivariantZero] at heq
        exact DFunLike.coe_injective heq))
    have hteq : (t : GBL Γ a b c → GBR Γ a b c)
        = (compParityOp (GBL.grading Γ a b c) t : GBL Γ a b c → GBR Γ a b c)
          ∘ (parityOp (GBL.grading Γ a b c) : GBL Γ a b c → GBL Γ a b c) := by
      funext m
      rw [Function.comp_apply, compParityOp_apply, parityOp_parityOp]
    show Function.Bijective (t : GBL Γ a b c → GBR Γ a b c)
    rw [hteq]
    exact hbij.comp (parityOp (GBL.grading Γ a b c)).bijective

end GParity

end GaugeChi

end Superfusion

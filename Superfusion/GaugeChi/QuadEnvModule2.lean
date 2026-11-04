/-
Superfusion / GaugeChi / QuadEnvModule2

Milestone M12-6′ of the abstract `(p, χ)` arc: **`GQ4`'s `gQuadEnv`-module
structure**, by DIRECT iteration (mirroring `Superfusion.Bimod.PentagonB`'s
`QuadEnvModule2` — `Q4`'s construction — one level up from
`GaugeChi.GaugeParity`'s `GBR` section, which resolves the identical
bracket mismatch at the triple level).

`GQ4`'s four slot actions (`GaugeChi.PentagonActions`) are already separate
algebra maps into `End K GQ4`: `D_b`, `D_c`, `D_d` via `leftActionEnd`
(lifting `GBR Γ b c d`'s own slot actions), `D_a` via `midAlgHom` (through
the outer column `F_{a,b+c+d}`). Three raw `GradedTensorProduct.lift`s
combine them in `gQuadEnv`'s own order `(D_a, D_b)` then `D_c` then `D_d`,
using the six pairwise supercommutation certificates: `(a,b)`, `(a,c)`,
`(a,d)` reduce directly to `leftActionEnd_anticommutes_midAlgHom` (`D_a` is
the mid-of-mid slot for all three); `(b,c)`, `(b,d)`, `(c,d)` are lifted
from `GBR Γ b c d`'s own pairwise `SuperCommSMul` certificates
(`GaugeChi.PentagonActions`'s `GBR.superCommSMul_aslot_bslot`/`_aslot_cslot`/
`_bslot_cslot`, instantiated at `(b,c,d)`) via
`leftActionEnd_leftActionEnd_supercomm_end`. `GQ4`'s own native right
`D_{a+(b+c+d)}`-action is recast to `D_{a+b+c+d}` via `Γ.gaugeCast`
(the associativity identity `a+b+c+d = a+(b+c+d)`, `add_assoc` alone —
no commutativity needed), landing **`Module (gQuadEnv Γ a b c d)
(GQ4 Γ a b c d)`** via `Bimod.module`.
-/
import Superfusion.GaugeChi.QuadEnvModule

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

namespace GQ4

/-! ### `GQ4`'s four slot actions, as algebra maps into `End K GQ4`

Literally the terms `PentagonActions.lean` uses to build `GQ4`'s registered
`Module` instances, so that `x • z = fA x z` etc. hold by `rfl`
(`aslot_apply`–`dslot_apply` below). -/

/-- `GQ4`'s `D_a`-slot, as an algebra map (`midAlgHom`, mid-of-mid through
the outer column). -/
private noncomputable abbrev fA :
    (Γ.D a).carrier →ₐ[K] Module.End K (GQ4 K Γ a b c d) :=
  midAlgHom (Γ.D (b + c + d)).grading (GBR.grading Γ b c d) (Γ.D a).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c + d))))

/-- `GQ4`'s `D_b`-slot, as an algebra map (`leftActionEnd`, lifting
`GBR Γ b c d`'s own `b`-slot). -/
private noncomputable abbrev fB :
    (Γ.D b).carrier →ₐ[K] Module.End K (GQ4 K Γ a b c d) :=
  leftActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) (B := (Γ.D b).carrier)

/-- `GQ4`'s `D_c`-slot, as an algebra map. -/
private noncomputable abbrev fC :
    (Γ.D c).carrier →ₐ[K] Module.End K (GQ4 K Γ a b c d) :=
  leftActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) (B := (Γ.D c).carrier)

/-- `GQ4`'s `D_d`-slot, as an algebra map. -/
private noncomputable abbrev fD :
    (Γ.D d).carrier →ₐ[K] Module.End K (GQ4 K Γ a b c d) :=
  leftActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) (B := (Γ.D d).carrier)

theorem aslot_apply (x : (Γ.D a).carrier) (z : GQ4 K Γ a b c d) :
    x • z = fA K Γ a b c d x z := rfl

theorem bslot_apply (y : (Γ.D b).carrier) (z : GQ4 K Γ a b c d) :
    y • z = fB K Γ a b c d y z := rfl

theorem cslot_apply (w : (Γ.D c).carrier) (z : GQ4 K Γ a b c d) :
    w • z = fC K Γ a b c d w z := rfl

theorem dslot_apply (t : (Γ.D d).carrier) (z : GQ4 K Γ a b c d) :
    t • z = fD K Γ a b c d t z := rfl

/-! ### The six pairwise supercommutation certificates for `GQ4`'s slots

`(a,b)`, `(a,c)`, `(a,d)` reduce directly to
`leftActionEnd_anticommutes_midAlgHom` (`D_a` is the mid-of-mid slot for
all three); `(b,c)`, `(b,d)`, `(c,d)` are fresh, lifted from `GBR Γ b c
d`'s own pairwise `SuperCommSMul` certificates (`PentagonActions.lean`)
via `leftActionEnd_leftActionEnd_supercomm_end`. -/

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
    fA K Γ a b c d (x : (Γ.D a).carrier) * fB K Γ a b c d (y : (Γ.D b).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fB K Γ a b c d (y : (Γ.D b).carrier) * fA K Γ a b c d (x : (Γ.D a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (b + c + d)).grading
    (GBR.grading Γ b c d) (Γ.D a).grading (Γ.D b).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c + d)))) y x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_ac ⦃i k : ZMod 2⦄ (x : (Γ.D a).grading i) (w : (Γ.D c).grading k) :
    fA K Γ a b c d (x : (Γ.D a).carrier) * fC K Γ a b c d (w : (Γ.D c).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fC K Γ a b c d (w : (Γ.D c).carrier) * fA K Γ a b c d (x : (Γ.D a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (b + c + d)).grading
    (GBR.grading Γ b c d) (Γ.D a).grading (Γ.D c).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c + d)))) w x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_ad ⦃i k : ZMod 2⦄ (x : (Γ.D a).grading i) (t : (Γ.D d).grading k) :
    fA K Γ a b c d (x : (Γ.D a).carrier) * fD K Γ a b c d (t : (Γ.D d).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) * fA K Γ a b c d (x : (Γ.D a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (b + c + d)).grading
    (GBR.grading Γ b c d) (Γ.D a).grading (Γ.D d).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c + d)))) t x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_bc ⦃i k : ZMod 2⦄ (y : (Γ.D b).grading i) (w : (Γ.D c).grading k) :
    fB K Γ a b c d (y : (Γ.D b).carrier) * fC K Γ a b c d (w : (Γ.D c).carrier)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (fC K Γ a b c d (w : (Γ.D c).carrier) * fB K Γ a b c d (y : (Γ.D b).carrier)) :=
  leftActionEnd_leftActionEnd_supercomm_end (Γ.D b).grading (Γ.D c).grading
    (GBR.superCommSMul_aslot_bslot K Γ b c d) y.2 w.2

theorem comm_bd ⦃i k : ZMod 2⦄ (y : (Γ.D b).grading i) (t : (Γ.D d).grading k) :
    fB K Γ a b c d (y : (Γ.D b).carrier) * fD K Γ a b c d (t : (Γ.D d).carrier)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) * fB K Γ a b c d (y : (Γ.D b).carrier)) :=
  leftActionEnd_leftActionEnd_supercomm_end (Γ.D b).grading (Γ.D d).grading
    (GBR.superCommSMul_aslot_cslot K Γ b c d) y.2 t.2

theorem comm_cd ⦃i k : ZMod 2⦄ (w : (Γ.D c).grading i) (t : (Γ.D d).grading k) :
    fC K Γ a b c d (w : (Γ.D c).carrier) * fD K Γ a b c d (t : (Γ.D d).carrier)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) * fC K Γ a b c d (w : (Γ.D c).carrier)) :=
  leftActionEnd_leftActionEnd_supercomm_end (Γ.D c).grading (Γ.D d).grading
    (GBR.superCommSMul_bslot_cslot K Γ b c d) w.2 t.2

/-! ### The same six facts, in the `sgn`-scalar convention feeding
`lift_anticommute_sgn`'s `h1`/`h2` parameters -/

private theorem comm_ac_sgn ⦃i k : ZMod 2⦄ (x : (Γ.D a).grading i) (w : (Γ.D c).grading k) :
    fA K Γ a b c d (x : (Γ.D a).carrier) * fC K Γ a b c d (w : (Γ.D c).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fC K Γ a b c d (w : (Γ.D c).carrier) * fA K Γ a b c d (x : (Γ.D a).carrier)) :=
  fromUzpow (comm_ac K Γ a b c d x w)

private theorem comm_ad_sgn ⦃i k : ZMod 2⦄ (x : (Γ.D a).grading i) (t : (Γ.D d).grading k) :
    fA K Γ a b c d (x : (Γ.D a).carrier) * fD K Γ a b c d (t : (Γ.D d).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) * fA K Γ a b c d (x : (Γ.D a).carrier)) :=
  fromUzpow (comm_ad K Γ a b c d x t)

private theorem comm_bc_sgn ⦃i k : ZMod 2⦄ (y : (Γ.D b).grading i) (w : (Γ.D c).grading k) :
    fB K Γ a b c d (y : (Γ.D b).carrier) * fC K Γ a b c d (w : (Γ.D c).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fC K Γ a b c d (w : (Γ.D c).carrier) * fB K Γ a b c d (y : (Γ.D b).carrier)) := by
  rw [comm_bc K Γ a b c d y w, mul_comm i k]

private theorem comm_bd_sgn ⦃i k : ZMod 2⦄ (y : (Γ.D b).grading i) (t : (Γ.D d).grading k) :
    fB K Γ a b c d (y : (Γ.D b).carrier) * fD K Γ a b c d (t : (Γ.D d).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) * fB K Γ a b c d (y : (Γ.D b).carrier)) := by
  rw [comm_bd K Γ a b c d y t, mul_comm i k]

private theorem comm_cd_sgn ⦃i k : ZMod 2⦄ (w : (Γ.D c).grading i) (t : (Γ.D d).grading k) :
    fC K Γ a b c d (w : (Γ.D c).carrier) * fD K Γ a b c d (t : (Γ.D d).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) * fC K Γ a b c d (w : (Γ.D c).carrier)) := by
  rw [comm_cd K Γ a b c d w t, mul_comm i k]

/-! ### The three iterated `GradedTensorProduct.lift`s, in `gQuadEnv`'s
own order `(D_a, D_b)` then `D_c` then `D_d` -/

/-- **Step 1**: `D_a ᵍ⊗ D_b` acts on `GQ4`. -/
private noncomputable def phi1 :
    ((Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) →ₐ[K] Module.End K (GQ4 K Γ a b c d) :=
  GradedTensorProduct.lift (Γ.D a).grading (Γ.D b).grading
    (fA K Γ a b c d) (fB K Γ a b c d) (comm_ab K Γ a b c d)

private theorem phi1_tmul (x : (Γ.D a).carrier) (y : (Γ.D b).carrier) :
    (phi1 K Γ a b c d) (x ᵍ⊗ₜ[K] y) = fA K Γ a b c d x * fB K Γ a b c d y := rfl

/-- `D_a ᵍ⊗ D_b` (already combined, Step 1) anticommutes with `D_c`
(`sgn`-scalar convention, feeding Step 2's own `hanti`). -/
private theorem phi1_comm_c ⦃i j : ZMod 2⦄
    (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading i)
    (z : (Γ.D c).grading j) :
    (phi1 K Γ a b c d) (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading)
        * fC K Γ a b c d (z : (Γ.D c).carrier)
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (fC K Γ a b c d (z : (Γ.D c).carrier) *
            (phi1 K Γ a b c d) (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading)) :=
  lift_anticommute_sgn (Γ.D a).grading (Γ.D b).grading (Γ.D c).grading
    (fA K Γ a b c d) (fB K Γ a b c d) (comm_ab K Γ a b c d)
    (fC K Γ a b c d) (comm_ac_sgn K Γ a b c d) (comm_bc_sgn K Γ a b c d) w z

/-- `D_a ᵍ⊗ D_b` (already combined, Step 1) anticommutes with `D_d` —
preparation for Step 3, needed *before* `D_c` is folded in. -/
private theorem phi1_comm_d ⦃i j : ZMod 2⦄
    (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading i)
    (t : (Γ.D d).grading j) :
    (phi1 K Γ a b c d) (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading)
        * fD K Γ a b c d (t : (Γ.D d).carrier)
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) *
            (phi1 K Γ a b c d) (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading)) :=
  lift_anticommute_sgn (Γ.D a).grading (Γ.D b).grading (Γ.D d).grading
    (fA K Γ a b c d) (fB K Γ a b c d) (comm_ab K Γ a b c d)
    (fD K Γ a b c d) (comm_ad_sgn K Γ a b c d) (comm_bd_sgn K Γ a b c d) w t

/-- **Step 2**: `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c` acts on `GQ4`. -/
private noncomputable def phi2 :
    (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading) →ₐ[K]
      Module.End K (GQ4 K Γ a b c d) :=
  GradedTensorProduct.lift (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading)
    (Γ.D c).grading (phi1 K Γ a b c d) (fC K Γ a b c d)
    (fun _ _ w z => toUzpow (phi1_comm_c K Γ a b c d w z))

private theorem phi2_tmul (w1 : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) (z1 : (Γ.D c).carrier) :
    (phi2 K Γ a b c d) (w1 ᵍ⊗ₜ[K] z1) = (phi1 K Γ a b c d) w1 * fC K Γ a b c d z1 := rfl

/-- `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c` (already combined, Step 2) anticommutes with
`D_d`, using the Step-3-preparation fact `phi1_comm_d` and the fresh
pairwise `(c,d)` fact `comm_cd_sgn`. -/
private theorem phi2_comm_d ⦃i j : ZMod 2⦄
    (w : Superfusion.tensorGrading
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading i)
    (t : (Γ.D d).grading j) :
    (phi2 K Γ a b c d)
        (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
        * fD K Γ a b c d (t : (Γ.D d).carrier)
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (fD K Γ a b c d (t : (Γ.D d).carrier) *
            (phi2 K Γ a b c d)
              (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading
                  ᵍ⊗[K] (Γ.D c).grading)) :=
  lift_anticommute_sgn
    (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading (Γ.D d).grading
    (phi1 K Γ a b c d) (fC K Γ a b c d) (fun _ _ w' z' => toUzpow (phi1_comm_c K Γ a b c d w' z'))
    (fD K Γ a b c d) (phi1_comm_d K Γ a b c d) (comm_cd_sgn K Γ a b c d) w t

/-- **Step 3**: `((D_a ᵍ⊗ D_b) ᵍ⊗ D_c) ᵍ⊗ D_d` acts on `GQ4` — this is
`gQuadEnv`'s own source carrier, verbatim. -/
private noncomputable def phi3 :
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading) →ₐ[K] Module.End K (GQ4 K Γ a b c d) :=
  GradedTensorProduct.lift
    (Superfusion.tensorGrading (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading)
      (Γ.D c).grading)
    (Γ.D d).grading (phi2 K Γ a b c d) (fD K Γ a b c d)
    (fun _ _ w t => toUzpow (phi2_comm_d K Γ a b c d w t))

private theorem phi3_tmul
    (w1 : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (t1 : (Γ.D d).carrier) :
    (phi3 K Γ a b c d) (w1 ᵍ⊗ₜ[K] t1) = (phi2 K Γ a b c d) w1 * fD K Γ a b c d t1 := rfl

/-! ### Gradedness of `GQ4`'s four slots, and of the combined `phi1`,
`phi2`, `phi3` -/

theorem fA_mem_grading ⦃i j : ZMod 2⦄ {x : (Γ.D a).carrier} (hx : x ∈ (Γ.D a).grading i)
    {z : GQ4 K Γ a b c d} (hz : z ∈ GQ4.grading K Γ a b c d j) :
    fA K Γ a b c d x z ∈ GQ4.grading K Γ a b c d (i + j) :=
  midEnd_mem_relGrading (Γ.D (b + c + d)).grading (GBR.grading Γ b c d) (Γ.D a).grading
    (FusionColumn.grading (Γ.fuse a (b + c + d)))
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c + d)))) hx hz

theorem fB_mem_grading ⦃i j : ZMod 2⦄ {y : (Γ.D b).carrier} (hy : y ∈ (Γ.D b).grading i)
    {z : GQ4 K Γ a b c d} (hz : z ∈ GQ4.grading K Γ a b c d j) :
    fB K Γ a b c d y z ∈ GQ4.grading K Γ a b c d (i + j) :=
  leftActionEnd_mem_relGrading (GBR.grading Γ b c d)
    (FusionColumn.grading (Γ.fuse a (b + c + d))) hy hz

theorem fC_mem_grading ⦃i j : ZMod 2⦄ {w : (Γ.D c).carrier} (hw : w ∈ (Γ.D c).grading i)
    {z : GQ4 K Γ a b c d} (hz : z ∈ GQ4.grading K Γ a b c d j) :
    fC K Γ a b c d w z ∈ GQ4.grading K Γ a b c d (i + j) :=
  leftActionEnd_mem_relGrading (GBR.grading Γ b c d)
    (FusionColumn.grading (Γ.fuse a (b + c + d))) hw hz

theorem fD_mem_grading ⦃i j : ZMod 2⦄ {t : (Γ.D d).carrier} (ht : t ∈ (Γ.D d).grading i)
    {z : GQ4 K Γ a b c d} (hz : z ∈ GQ4.grading K Γ a b c d j) :
    fD K Γ a b c d t z ∈ GQ4.grading K Γ a b c d (i + j) :=
  leftActionEnd_mem_relGrading (GBR.grading Γ b c d)
    (FusionColumn.grading (Γ.fuse a (b + c + d))) ht hz

private theorem phi1_mem_grading ⦃i j : ZMod 2⦄
    {w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading}
    (hw : w ∈ Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading i)
    {z : GQ4 K Γ a b c d} (hz : z ∈ GQ4.grading K Γ a b c d j) :
    (phi1 K Γ a b c d) w z ∈ GQ4.grading K Γ a b c d (i + j) := by
  have key : ∀ z' ∈ GQ4.grading K Γ a b c d j,
      (phi1 K Γ a b c d) w z' ∈ GQ4.grading K Γ a b c d (i + j) := by
    refine Superfusion.tensorGrading_induction (Γ.D a).grading (Γ.D b).grading
      (p := fun w' => ∀ z' ∈ GQ4.grading K Γ a b c d j,
        (phi1 K Γ a b c d) w' z' ∈ GQ4.grading K Γ a b c d (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ x y hij hx hy z' hz'
      have hev : (phi1 K Γ a b c d) (x ᵍ⊗ₜ[K] y) z'
          = fA K Γ a b c d x (fB K Γ a b c d y z') := by
        rw [phi1_tmul, Module.End.mul_apply]
      rw [hev]
      have h := fA_mem_grading K Γ a b c d hx (fB_mem_grading K Γ a b c d hy hz')
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
    {z : GQ4 K Γ a b c d} (hz : z ∈ GQ4.grading K Γ a b c d j) :
    (phi2 K Γ a b c d) w z ∈ GQ4.grading K Γ a b c d (i + j) := by
  have key : ∀ z' ∈ GQ4.grading K Γ a b c d j,
      (phi2 K Γ a b c d) w z' ∈ GQ4.grading K Γ a b c d (i + j) := by
    refine Superfusion.tensorGrading_induction
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
      (p := fun w' => ∀ z' ∈ GQ4.grading K Γ a b c d j,
        (phi2 K Γ a b c d) w' z' ∈ GQ4.grading K Γ a b c d (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ w1 z1 hij hw1 hz1 z' hz'
      have hev : (phi2 K Γ a b c d) (w1 ᵍ⊗ₜ[K] z1) z'
          = (phi1 K Γ a b c d) w1 (fC K Γ a b c d z1 z') := by
        rw [phi2_tmul, Module.End.mul_apply]
      rw [hev]
      have h := phi1_mem_grading K Γ a b c d hw1 (fC_mem_grading K Γ a b c d hz1 hz')
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

private theorem phi3_mem_grading ⦃i j : ZMod 2⦄
    {w : Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading}
    (hw : w ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading i)
    {z : GQ4 K Γ a b c d} (hz : z ∈ GQ4.grading K Γ a b c d j) :
    (phi3 K Γ a b c d) w z ∈ GQ4.grading K Γ a b c d (i + j) := by
  have key : ∀ z' ∈ GQ4.grading K Γ a b c d j,
      (phi3 K Γ a b c d) w z' ∈ GQ4.grading K Γ a b c d (i + j) := by
    refine Superfusion.tensorGrading_induction
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading
      (p := fun w' => ∀ z' ∈ GQ4.grading K Γ a b c d j,
        (phi3 K Γ a b c d) w' z' ∈ GQ4.grading K Γ a b c d (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ w1 t1 hij hw1 ht1 z' hz'
      have hev : (phi3 K Γ a b c d) (w1 ᵍ⊗ₜ[K] t1) z'
          = (phi2 K Γ a b c d) w1 (fD K Γ a b c d t1 z') := by
        rw [phi3_tmul, Module.End.mul_apply]
      rw [hev]
      have h := phi2_mem_grading K Γ a b c d hw1 (fD_mem_grading K Γ a b c d ht1 hz')
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

/-! ### Commutation with `GQ4`'s own native right `D_{a+(b+c+d)}`-action
(unsigned; the recast to `gQuadEnv`'s sop-side `D_{a+b+c+d}` follows) -/

private noncomputable def rGQ4 (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    Module.End K (GQ4 K Γ a b c d) :=
  rightActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))) τ

theorem rGQ4_apply (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ) (z : GQ4 K Γ a b c d) :
    τ • z = rGQ4 K Γ a b c d τ z := rfl

theorem fA_comm_right (x : (Γ.D a).carrier) (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fA K Γ a b c d x * rGQ4 K Γ a b c d τ = rGQ4 K Γ a b c d τ * fA K Γ a b c d x :=
  midEnd_comm_rightActionEnd (Γ.D (b + c + d)).grading (GBR.grading Γ b c d) (Γ.D a).grading
    (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
      (FusionColumn.superCommSMul (Γ.fuse a (b + c + d)))) x τ

theorem fB_comm_right (y : (Γ.D b).carrier) (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fB K Γ a b c d y * rGQ4 K Γ a b c d τ = rGQ4 K Γ a b c d τ * fB K Γ a b c d y :=
  leftActionEnd_comm_rightActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) y τ

theorem fC_comm_right (w : (Γ.D c).carrier) (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fC K Γ a b c d w * rGQ4 K Γ a b c d τ = rGQ4 K Γ a b c d τ * fC K Γ a b c d w :=
  leftActionEnd_comm_rightActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) w τ

theorem fD_comm_right (t : (Γ.D d).carrier) (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fD K Γ a b c d t * rGQ4 K Γ a b c d τ = rGQ4 K Γ a b c d τ * fD K Γ a b c d t :=
  leftActionEnd_comm_rightActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) t τ

private theorem phi1_comm_right (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (w : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) :
    (phi1 K Γ a b c d) w * rGQ4 K Γ a b c d τ = rGQ4 K Γ a b c d τ * (phi1 K Γ a b c d) w :=
  lift_comm_right (Γ.D a).grading (Γ.D b).grading (fA K Γ a b c d) (fB K Γ a b c d)
    (comm_ab K Γ a b c d) (fun x => fA_comm_right K Γ a b c d x τ)
    (fun y => fB_comm_right K Γ a b c d y τ) w

private theorem phi2_comm_right (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (w : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading) :
    (phi2 K Γ a b c d) w * rGQ4 K Γ a b c d τ = rGQ4 K Γ a b c d τ * (phi2 K Γ a b c d) w :=
  lift_comm_right (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
    (phi1 K Γ a b c d) (fC K Γ a b c d)
    (fun _ _ w' z' => toUzpow (phi1_comm_c K Γ a b c d w' z'))
    (fun w' => phi1_comm_right K Γ a b c d τ w') (fun z' => fC_comm_right K Γ a b c d z' τ) w

private theorem phi3_comm_right (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (w : Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading) :
    (phi3 K Γ a b c d) w * rGQ4 K Γ a b c d τ = rGQ4 K Γ a b c d τ * (phi3 K Γ a b c d) w :=
  lift_comm_right
    (Superfusion.tensorGrading (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading)
      (Γ.D c).grading)
    (Γ.D d).grading (phi2 K Γ a b c d) (fD K Γ a b c d)
    (fun _ _ w' t' => toUzpow (phi2_comm_d K Γ a b c d w' t'))
    (fun w' => phi2_comm_right K Γ a b c d τ w') (fun t' => fD_comm_right K Γ a b c d t' τ) w

/-! ### Assembling `Module (gQuadEnv K Γ a b c d) (GQ4 K Γ a b c d)` -/

/-- **Bridge**: `GQ4`'s combined `phi3`-action, at the envelope's own
source carrier spelling. -/
noncomputable instance instModuleGtensorABCDRaw :
    Module (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading) (GQ4 K Γ a b c d) :=
  Module.compHom (GQ4 K Γ a b c d) (phi3 K Γ a b c d).toRingHom

noncomputable instance instModuleGtensorABCD :
    Module ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier
      (GQ4 K Γ a b c d) :=
  inferInstanceAs (Module
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading) (GQ4 K Γ a b c d))

instance : IsScalarTower K
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading) (GQ4 K Γ a b c d) :=
  ⟨fun k w m => by
    show (phi3 K Γ a b c d) (k • w) m = k • (phi3 K Γ a b c d) w m
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier (GQ4 K Γ a b c d) :=
  inferInstanceAs (IsScalarTower K
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading) (GQ4 K Γ a b c d))

/-- **`GQ4`'s combined action is graded** (`phi3_mem_grading`). -/
instance : SetLike.GradedSMul
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
    (grading K Γ a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact phi3_mem_grading K Γ a b c d hw hz

/-- The associativity recast between `GQ4`'s own native right tower
`D_{a+(b+c+d)}` and `gQuadEnv`'s sop-side tower `D_{a+b+c+d}` — pure
`add_assoc` arithmetic (no commutativity needed for an abstract
`[AddGroup G]`). -/
private theorem quadRightCast_eq : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

/-- `GQ4`'s own native right action is a `K`-scalar tower. -/
instance : IsScalarTower K ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GQ4 K Γ a b c d) :=
  ⟨fun k τ z => by
    show rightActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) (k • τ) z
      = k • rightActionEnd K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) τ z
    rw [map_smul, LinearMap.smul_apply]⟩

/-- `gQuadEnv`'s sop-side right `D_{a+b+c+d}`-action on `GQ4`, pulled back
along the associativity cast from `GQ4`'s own native
`D_{a+(b+c+d)}`-action. -/
noncomputable instance instModuleRightRecast :
    Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ4 K Γ a b c d) :=
  Module.compHom (GQ4 K Γ a b c d)
    (((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv.toRingHom).op)

theorem rightRecast_op_smul_def (τ : (Γ.D (a + b + c + d)).carrier) (z : GQ4 K Γ a b c d) :
    MulOpposite.op τ • z
      = MulOpposite.op ((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv τ) • z := rfl

instance : IsScalarTower K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ4 K Γ a b c d) :=
  ⟨fun k τ z => by
    show MulOpposite.op ((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv
        (MulOpposite.unop (k • τ))) • z
      = k • (MulOpposite.op ((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv
          (MulOpposite.unop τ)) • z)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ z⟩

/-- **`GQ4`'s combined action commutes with the recast right action**
(`phi3_comm_right`, transported along the recast). -/
instance : SMulCommClass
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier
    ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ4 K Γ a b c d) :=
  ⟨fun w t z => by
    show (phi3 K Γ a b c d) w
        (MulOpposite.op ((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv
          (MulOpposite.unop t)) • z)
      = MulOpposite.op ((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv
          (MulOpposite.unop t)) • (phi3 K Γ a b c d) w z
    rw [rGQ4_apply, rGQ4_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
      phi3_comm_right]⟩

/-- `GQ4`'s own native right `D_{a+(b+c+d)}`-action is graded
(`rightActionEnd_mem_relGrading`). -/
instance : GradedRightSMul (Γ.D (a + (b + c + d))).grading (grading K Γ a b c d) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (GBR.grading Γ b c d)
      (FusionColumn.grading (Γ.fuse a (b + c + d))) hτ hw

/-- The gauge-index cast preserves the grading (a `subst`-`rfl` fact,
local copy of `GaugeParity.lean`'s private `gaugeCast_mem_grading`). -/
private theorem gaugeCast_mem_grading {x y : G} (h : x = y) {i : ZMod 2}
    {τ : (Γ.D x).carrier} (hτ : τ ∈ (Γ.D x).grading i) :
    (Γ.gaugeCast h).toAlgEquiv τ ∈ (Γ.D y).grading i := by
  subst h
  exact hτ

/-- `GQ4`'s own right action is graded, for `gQuadEnv`'s sop-side tower
(the recast right coefficient action). -/
instance : GradedRightSMul (Γ.D (a + b + c + d)).grading (grading K Γ a b c d) where
  smul_mem _ _ _ _ hτ hw := by
    rw [rightRecast_op_smul_def]
    exact GradedRightSMul.smul_mem (gaugeCast_mem_grading K Γ (quadRightCast_eq a b c d) hτ) hw

/-- **`GQ4` is a `gQuadEnv K Γ a b c d`-module**: the `gQuadEnv`-source
action (`phi1`–`phi3`, direct iteration in the envelope's own order) and
`GQ4`'s own right `D_{a+(b+c+d)}`-action (recast to `D_{a+b+c+d}`)
assemble via `Bimod.module`. -/
noncomputable instance instModuleGQuadEnv : Module (gQuadEnv K Γ a b c d) (GQ4 K Γ a b c d) :=
  Bimod.module ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
    (Γ.D (a + b + c + d)).grading (grading K Γ a b c d)

/-! ### The four slot-embedding generators (mirroring
`Superfusion.Bimod.QuadEnvModule2`'s `Q4.aEmbed_smul`–`_dEmbed_smul`,
one gtensor level up from `GaugeChi.GaugeParity`'s `GBR.aEmbed_smul`–
`_cEmbed_smul`): `GQ4`'s `gQuadEnv`-source action, restricted to a slot
generator embedded through the three-fold `includeLeft`/`includeRight`
chain matching the envelope's own bracket order, literally *is* the slot
action `fA`–`fD` — a direct consequence of `GradedTensorProduct.lift_tmul`
(itself `rfl`) and `map_one` at each of the (at most three) levels, no
induction anywhere. -/

theorem gtensorSourceRaw_smul_def
    (w : Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        ᵍ⊗[K] (Γ.D d).grading)
    (z : GQ4 K Γ a b c d) :
    w • z = phi3 K Γ a b c d w z := rfl

/-- `gtensorSourceRaw_smul_def`, at the BUNDLED `.gtensor.carrier`
spelling `gQuadEnvGrading` (`QuadInterface.lean`) needs — the two
spellings are `rfl`-equal elementwise but not `instances`-transparently
equal (the M8a-8d′-iii-a′ lesson), so every downstream slot-embedding
bridge below is stated at THIS bundled spelling (matching `GQ1.aEmbed`–
`GQ1.dEmbed`, `QuadInterface.lean`), one further `rfl` past
`gtensorSourceRaw_smul_def`. -/
theorem gtensorABCD_smul_def
    (w : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (z : GQ4 K Γ a b c d) :
    w • z = phi3 K Γ a b c d w z := rfl

/-- **The `a`-slot-embedding bridge**: the envelope-source element
obtained by embedding `x : D_a` via the three-fold `includeLeft` chain
matching the envelope's own bracket order acts on `GQ4`, on *every*
element, exactly as `GQ4`'s own registered `a`-slot action of `x`. -/
theorem aEmbed_smul
    (x₀ : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) (x : (Γ.D a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
    (x₁ : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading x₀)
    (x₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hx₂ : x₂ = GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading
          (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
        (Γ.D d).grading x₁)
    (z : GQ4 K Γ a b c d) :
    x₂ • z = x • z := by
  rw [gtensorABCD_smul_def, aslot_apply]
  have h1 : phi1 K Γ a b c d x₀ = fA K Γ a b c d x := by
    rw [hx₀]
    show fA K Γ a b c d x * fB K Γ a b c d 1 = fA K Γ a b c d x
    rw [map_one, mul_one]
  have h2 : phi2 K Γ a b c d x₁ = fA K Γ a b c d x := by
    rw [hx₁]
    show phi1 K Γ a b c d x₀ * fC K Γ a b c d 1 = fA K Γ a b c d x
    rw [map_one, mul_one, h1]
  rw [hx₂]
  show (phi2 K Γ a b c d x₁ * fD K Γ a b c d 1) z = fA K Γ a b c d x z
  rw [map_one, mul_one, h2]

/-- **The `b`-slot-embedding bridge**. -/
theorem bEmbed_smul
    (y₀ : (Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) (y : (Γ.D b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
    (y₁ : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading y₀)
    (y₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hy₂ : y₂ = GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading
          (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
        (Γ.D d).grading y₁)
    (z : GQ4 K Γ a b c d) :
    y₂ • z = y • z := by
  rw [gtensorABCD_smul_def, bslot_apply]
  have h1 : phi1 K Γ a b c d y₀ = fB K Γ a b c d y := by
    rw [hy₀]
    show fA K Γ a b c d 1 * fB K Γ a b c d y = fB K Γ a b c d y
    rw [map_one, one_mul]
  have h2 : phi2 K Γ a b c d y₁ = fB K Γ a b c d y := by
    rw [hy₁]
    show phi1 K Γ a b c d y₀ * fC K Γ a b c d 1 = fB K Γ a b c d y
    rw [map_one, mul_one, h1]
  rw [hy₂]
  show (phi2 K Γ a b c d y₁ * fD K Γ a b c d 1) z = fB K Γ a b c d y z
  rw [map_one, mul_one, h2]

/-- **The `c`-slot-embedding bridge**. -/
theorem cEmbed_smul
    (w₀ : Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading ᵍ⊗[K] (Γ.D c).grading)
    (w : (Γ.D c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading w)
    (w₁ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hw₁ : w₁ = GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading
          (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
        (Γ.D d).grading w₀)
    (z : GQ4 K Γ a b c d) :
    w₁ • z = w • z := by
  rw [gtensorABCD_smul_def, cslot_apply]
  have h2 : phi2 K Γ a b c d w₀ = fC K Γ a b c d w := by
    rw [hw₀]
    show phi1 K Γ a b c d 1 * fC K Γ a b c d w = fC K Γ a b c d w
    rw [map_one, one_mul]
  rw [hw₁]
  show (phi2 K Γ a b c d w₀ * fD K Γ a b c d 1) z = fC K Γ a b c d w z
  rw [map_one, mul_one, h2]

/-- **The `d`-slot-embedding bridge** — a single `includeRight`, since
`D_d` is the envelope source's own outermost right factor. -/
theorem dEmbed_smul
    (t₀ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (t : (Γ.D d).carrier)
    (ht₀ : t₀ = GradedTensorProduct.includeRight
        (Superfusion.tensorGrading
          (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
        (Γ.D d).grading t)
    (z : GQ4 K Γ a b c d) :
    t₀ • z = t • z := by
  rw [gtensorABCD_smul_def, dslot_apply, ht₀]
  show (phi2 K Γ a b c d 1 * fD K Γ a b c d t) z = fD K Γ a b c d t z
  rw [map_one, one_mul]

end GQ4

end GaugeChi

end Superfusion

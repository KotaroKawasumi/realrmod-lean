/-
Superfusion / Bimod / QuadEnvModule2

Milestone M8a-8d′-iii-a′ (roadmap v3): **the `QuadEnv`-module structure
on `Q4`**, built by DIRECT iteration (not bracket surgery through
`gtensorAssoc`/`gtensorComm`) — matching `quadSource`'s own
left-associated bracket `(((T_a ᵍ⊗ T_b) ᵍ⊗ T_c) ᵍ⊗ T_d)` exactly, even
though `Q4`'s own natural nesting (through `B_R(b,c,d)`'s own
`(T_c ᵍ⊗ T_d) ᵍ⊗ T_b` combination) is a *different* bracket/order.

`Q4`'s four slot actions (`QuadActions.lean`) are already separate
algebra maps into `End K Q4`: `T_b`, `T_c`, `T_d` via `leftActionEnd`
(lifting `B_R(b,c,d)`'s own slot actions), `T_a` via `midAlgHom`
(through the outer column `C_{a,(b+c)+d}`).  Three raw
`GradedTensorProduct.lift`s combine them in `quadSource`'s own order:

* **Step 1** (`T_a`, `T_b`): `leftActionEnd_anticommutes_midAlgHom`
  supplies the anticommutation directly (a single generator-level fact,
  no induction).
* **Step 2** (`(T_a ᵍ⊗ T_b)`, `T_c`) and, as preparation for Step 3, the
  companion fact `(T_a ᵍ⊗ T_b)` vs `T_d`: both need the anticommutation
  of the *already-combined* Step-1 map with a single further factor —
  established by `lift_anticommute_sgn` (general layer below), fed by
  the *two* new pairwise facts `(T_a,T_c)`/`(T_a,T_d)` (again
  `leftActionEnd_anticommutes_midAlgHom`) and `(T_b,T_c)`/`(T_b,T_d)`
  (new: `leftActionEnd_leftActionEnd_supercomm`, lifting `B_R(b,c,d)`'s
  own pairwise `SuperCommSMul` certificates, `RouteCompat.lean`'s
  `superCommSMul_aslot_bslot`/`_aslot_cslot`, through the further
  `leftActionEnd` that builds `Q4`'s own `b`, `c`, `d` slots from
  `B_R(b,c,d)`'s).
* **Step 3** (`((T_a ᵍ⊗ T_b) ᵍ⊗ T_c)`, `T_d`): `lift_anticommute_sgn`
  again, fed by the Step-2-preparation fact and the new pairwise
  `(T_c,T_d)` fact (`leftActionEnd_leftActionEnd_supercomm` applied to
  `B_R(b,c,d)`'s `superCommSMul_bslot_cslot`).

So **all six pairwise supercommutation certificates for `Q4`'s slots**
are needed and none are landed at `Q4`'s own level beforehand: three
reduce directly to `leftActionEnd_anticommutes_midAlgHom`
(`(a,b)`,`(a,c)`,`(a,d)`, `T_a` being the mid-of-mid slot for all three)
and three are freshly derived from `B_R(b,c,d)`'s own pairwise
`SuperCommSMul` certificates via the new general lemma
`leftActionEnd_leftActionEnd_supercomm` (`(b,c)`,`(b,d)`,`(c,d)`).

The resulting `quadSource`-action on `Q4` is graded (a parallel
single-induction-per-level cascade, `fA_mem_grading`/`fB_mem_grading`/
`fC_mem_grading`/`fD_mem_grading` at the generator level and
`phi1_mem_grading`/`phi2_mem_grading`/`phi3_mem_grading` at each combined
level, off the already-general
`leftActionEnd_mem_relGrading`/`midEnd_mem_relGrading`) and commutes with
`Q4`'s own *native* right `T_{a+(b+c+d)}`-action (an unsigned cascade,
`lift_comm_right`, mirroring
`gtensorLeftActionHom_comm_rightActionEnd`'s induction pattern exactly
since no sign tracking is needed there).  `Q4`'s native right tower is
absorbed into `QuadEnv`'s own `T_{a+b+c+d}` sop-side via the
`RouteRecast.lean` device (`Module.compHom` along
`(stdTowerCast _).toAlgEquiv.toRingHom.op`, so that `rightSemilinear`
along the recast is literally the native right-equivariance,
`Iff.rfl` — the M8a-8c′-0 lesson), landing
**`Module (QuadEnv K a b c d) (Q4 K a b c d)`** via `Bimod.module`
(`instModuleQuadEnv`).

A hard-won implementation note: every degree-index computation that
feeds a **dependent-type membership goal** (`… ∈ Q4.grading K a b c d
(i + j)`) must be normalized by an *explicit* `rw [← add_assoc, hij]`
(or similar) on a `have`, never by rewriting the goal's index directly
and then `exact`-ing a differently-associated fact — for *variable*
(non-literal) `ZMod 2` exponents, `(i₁ + i₂) + j` and `i₁ + (i₂ + j)`
are propositionally but not definitionally equal, and letting `exact`
discover this via unification triggers a catastrophic (multi-minute,
budget-independent) `whnf`/`isDefEq` search rather than failing fast;
`GtensorLeftActionGraded.lean`'s own `gtensorLeftActionHom_mem_relGrading`
already follows this discipline (its own degree-fixing `rwa [...] at h`
step) and every new gradedness lemma in this file (`phi1_mem_grading`
etc.) now does too.

Deliverable 2 (the interface `quadInterSpace = gradedHomF`) is
**deferred**: `Q4`'s module structure above is a genuine prerequisite for
it (`Module (QuadEnv K a b c d) (Q4 K a b c d)`, needed for `gradedHomF`'s
own `[Module T N]` hypothesis with `N := Q4 K a b c d`), but assembling
the interface itself additionally needs (a) a *general* gradedness lemma
for `Bimod.Basic`'s `actionHom` — `SetLike.GradedSMul (Superfusion.
tensorGrading 𝒜 (SuperOp.grading ℬ)) ℳ`, i.e. gradedness of `Envelope`'s
own action, not built anywhere in the repo yet — needed to even *state*
`gradedHomF (Q1.grading) (QuadEnv-grading) (Q4.grading) e`; (b) the four
slot-generator/right-generator evaluation lemmas *for the full envelope*
(not just `Q4`'s raw `quadSource`-carrier action, which this file
supplies via `fA_mem_grading` etc. and the `rfl` bridges
`aslot_apply`–`dslot_apply`/`rQ4_apply`, but the *sop-wrapped* generators
`x ᵍ⊗ₜ 1 : QuadEnv K a b c d` for each slot and the sop generator
`1 ᵍ⊗ₜ (op τ)`); (c) the `⊇` direction (`gradedHomF → quadInterSpace`,
restriction to these generators — comparatively direct once (a)/(b) are
in place); (d) the `⊆` direction (extending slot-wise super-equivariance
to *all* homogeneous `QuadEnv`-elements via nested `tensorGrading_induction`
over quadSource's three internal levels *and* the outer sop-tensor level
— flagged by the design note as the round's hardest piece).  Given this
file's own `phi*_mem_grading`/`comm_*` cascades already needed the
degree-associativity discipline above at every level, (d)'s four-fold
nested induction is a substantial further undertaking; it is left to a
follow-up milestone rather than risking an unverified landing here. See
the session report for the precise scoping.
-/
import Superfusion.Bimod.QuadEnvModule
import Superfusion.Bimod.ParityBridge

namespace Superfusion

namespace Bimod

open scoped TensorProduct

/-! ### General layer I: lifting a `SuperCommSMul` fact on `M` through
two `leftActionEnd`s to `M ⊗[A] N` -/

section GeneralLift

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]

/-- **Two outer `leftActionEnd`-lifted actions supercommute on
`M ⊗[A] N`, once they supercommute on `M`**, at the level of the
`End`-multiplication (mirroring `RouteCompat.lean`'s
`bslot_cslot_end`, generalized off any two outer algebras `B₁`, `B₂`
rather than the two halves of a single pre-combined tower). -/
theorem leftActionEnd_leftActionEnd_supercomm_end
    {B₁ : Type*} [Ring B₁] [Algebra K B₁]
    [Module B₁ M] [SMulCommClass B₁ Aᵐᵒᵖ M] [IsScalarTower K B₁ M]
    (𝓑₁ : ZMod 2 → Submodule K B₁)
    {B₂ : Type*} [Ring B₂] [Algebra K B₂]
    [Module B₂ M] [SMulCommClass B₂ Aᵐᵒᵖ M] [IsScalarTower K B₂ M]
    (𝓑₂ : ZMod 2 → Submodule K B₂)
    (hsc : SuperCommSMul 𝓑₁ 𝓑₂ M)
    ⦃i k : ZMod 2⦄ ⦃x : B₁⦄ ⦃y : B₂⦄ (hx : x ∈ 𝓑₁ i) (hy : y ∈ 𝓑₂ k) :
    leftActionEnd K A M N x * leftActionEnd K A M N y
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (leftActionEnd K A M N y * leftActionEnd K A M N x) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [leftActionEnd_mk]
  rw [hsc hx hy m, map_zsmul, LinearMap.smul_apply]

/-- **Two outer `leftActionEnd`-lifted actions supercommute on
`M ⊗[A] N`, once they supercommute on `M`**, at the level of elements
(the `congrArg`-specialization of
`leftActionEnd_leftActionEnd_supercomm_end`, mirroring
`RouteCompat.lean`'s `superCommSMul_bslot_cslot`). -/
theorem leftActionEnd_leftActionEnd_supercomm
    {B₁ : Type*} [Ring B₁] [Algebra K B₁]
    [Module B₁ M] [SMulCommClass B₁ Aᵐᵒᵖ M] [IsScalarTower K B₁ M]
    (𝓑₁ : ZMod 2 → Submodule K B₁)
    {B₂ : Type*} [Ring B₂] [Algebra K B₂]
    [Module B₂ M] [SMulCommClass B₂ Aᵐᵒᵖ M] [IsScalarTower K B₂ M]
    (𝓑₂ : ZMod 2 → Submodule K B₂)
    (hsc : SuperCommSMul 𝓑₁ 𝓑₂ M)
    ⦃i k : ZMod 2⦄ ⦃x : B₁⦄ ⦃y : B₂⦄ (hx : x ∈ 𝓑₁ i) (hy : y ∈ 𝓑₂ k)
    (z : M ⊗[A;K] N) :
    leftActionEnd K A M N x (leftActionEnd K A M N y z)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          leftActionEnd K A M N y (leftActionEnd K A M N x z) := by
  have h := leftActionEnd_leftActionEnd_supercomm_end (A := A) (N := N) 𝓑₁ 𝓑₂ hsc hx hy
  have h' := congrArg (fun f : Module.End K (M ⊗[A;K] N) => f z) h
  simpa only [Module.End.mul_apply, LinearMap.smul_apply] using h'

end GeneralLift

/-! ### General layer II: combining a `GradedTensorProduct.lift`'d
action with a further algebra map, both signed (anticommutation) and
unsigned (commutation with a further right/outer action) -/

section LiftCombine

/-- **The `Units.smul`/`zsmul` sign bridge**: `GradedTensorProduct.lift`
insists on the `(-1 : ℤˣ) ^ n • x` spelling of a Koszul sign; every
supercommutation fact in this project is proved in the `((sgn n : ℤˣ) :
ℤ) • x` spelling instead (`sgn_add`, `Units.val_mul`, …).  One-line
bridge (`Units.smul_def`, `sgn_eq_neg_one_uzpow`). -/
private theorem toUzpow {X : Type*} [AddCommGroup X] {n : ZMod 2} {u v : X}
    (h : u = ((sgn n : ℤˣ) : ℤ) • v) : u = (-1 : ℤˣ) ^ n • v := by
  rw [Units.smul_def, ← sgn_eq_neg_one_uzpow]; exact h

/-- The converse bridge, `(-1 : ℤˣ) ^ n • x ↦ ((sgn n : ℤˣ) : ℤ) • x`. -/
private theorem fromUzpow {X : Type*} [AddCommGroup X] {n : ZMod 2} {u v : X}
    (h : u = (-1 : ℤˣ) ^ n • v) : u = ((sgn n : ℤˣ) : ℤ) • v := by
  rw [h, Units.smul_def, ← sgn_eq_neg_one_uzpow]

/-- **Combining a `GradedTensorProduct.lift`'d action with a further
factor**: if `f₁`, `f₂` anticommute (feeding `lift`) and BOTH
separately anticommute with a further algebra map `g` (`sgn`-scalar
convention), then the lifted map anticommutes with `g` too, on every
homogeneous element of the combined grading — the two-step "commute
past each summand of the tensor generator, multiply the two signs"
computation, generalized off `MiddleActionHom.lean`'s single-slot
pattern to an *already-combined* left factor. -/
theorem lift_anticommute_sgn
    {K A₁ A₂ A' E : Type*} [CommRing K]
    [Ring A₁] [Algebra K A₁] [Ring A₂] [Algebra K A₂]
    [Ring A'] [Algebra K A'] [Ring E] [Algebra K E]
    (𝒜₁ : ZMod 2 → Submodule K A₁) [GradedAlgebra 𝒜₁]
    (𝒜₂ : ZMod 2 → Submodule K A₂) [GradedAlgebra 𝒜₂]
    (𝒜' : ZMod 2 → Submodule K A')
    (f₁ : A₁ →ₐ[K] E) (f₂ : A₂ →ₐ[K] E)
    (hanti : ∀ ⦃i j⦄ (x : 𝒜₁ i) (y : 𝒜₂ j),
      f₁ x * f₂ y = (-1 : ℤˣ) ^ (j * i) • (f₂ y * f₁ x))
    (g : A' →ₐ[K] E)
    (h1 : ∀ ⦃i j⦄ (x : 𝒜₁ i) (z : 𝒜' j),
      f₁ x * g z = ((sgn (j * i) : ℤˣ) : ℤ) • (g z * f₁ x))
    (h2 : ∀ ⦃i j⦄ (y : 𝒜₂ i) (z : 𝒜' j),
      f₂ y * g z = ((sgn (j * i) : ℤˣ) : ℤ) • (g z * f₂ y))
    ⦃i j : ZMod 2⦄ (w : Superfusion.tensorGrading 𝒜₁ 𝒜₂ i) (z : 𝒜' j) :
    (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) (w : 𝒜₁ ᵍ⊗[K] 𝒜₂) * g (z : A')
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (g (z : A') *
            (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) (w : 𝒜₁ ᵍ⊗[K] 𝒜₂)) := by
  refine Superfusion.tensorGrading_induction 𝒜₁ 𝒜₂
    (p := fun w' => (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) w' * g (z : A')
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (g (z : A') * (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) w'))
    w.2 ?_ ?_ ?_ ?_
  · intro i₁ i₂ x y hij hx hy
    have hL : (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) (x ᵍ⊗ₜ[K] y) * g (z : A')
        = (((sgn (j * i₂) : ℤˣ) : ℤ) * ((sgn (j * i₁) : ℤˣ) : ℤ)) •
            ((g (z : A') * f₁ x) * f₂ y) := by
      rw [GradedTensorProduct.lift_tmul, mul_assoc, h2 ⟨y, hy⟩ z, mul_smul_comm,
        ← mul_assoc, h1 ⟨x, hx⟩ z, smul_mul_assoc, smul_smul]
    rw [hL, GradedTensorProduct.lift_tmul, ← mul_assoc]
    congr 1
    rw [← Units.val_mul, ← sgn_add,
      show j * i₂ + j * i₁ = j * i from by rw [← hij]; ring]
  · simp
  · intro w1 w2 hw1 hw2
    simp only [map_add, add_mul, mul_add, smul_add]
    rw [hw1, hw2]
  · intro c w1 hw1
    simp only [map_smul]
    rw [smul_mul_assoc, hw1, mul_smul_comm]
    exact smul_comm c _ _

/-- **Combining a `GradedTensorProduct.lift`'d action with a further
right/outer action**: if `f₁`, `f₂` commute *unconditionally* (no sign)
with a fixed element `r`, so does their lift, on all of `A₁ ᵍ⊗ A₂` (no
homogeneity needed at all) — mirrors
`GtensorLeftActionGraded.lean`'s `gtensorLeftActionHom_comm_rightActionEnd`
exactly (`GradedTensorProduct.of` + `TensorProduct.induction_on`, since
no sign bookkeeping enters). -/
theorem lift_comm_right
    {K A₁ A₂ E : Type*} [CommRing K]
    [Ring A₁] [Algebra K A₁] [Ring A₂] [Algebra K A₂] [Ring E] [Algebra K E]
    (𝒜₁ : ZMod 2 → Submodule K A₁) [GradedAlgebra 𝒜₁]
    (𝒜₂ : ZMod 2 → Submodule K A₂) [GradedAlgebra 𝒜₂]
    (f₁ : A₁ →ₐ[K] E) (f₂ : A₂ →ₐ[K] E)
    (hanti : ∀ ⦃i j⦄ (x : 𝒜₁ i) (y : 𝒜₂ j),
      f₁ x * f₂ y = (-1 : ℤˣ) ^ (j * i) • (f₂ y * f₁ x))
    {r : E} (h1 : ∀ x : A₁, f₁ x * r = r * f₁ x)
    (h2 : ∀ y : A₂, f₂ y * r = r * f₂ y)
    (w : 𝒜₁ ᵍ⊗[K] 𝒜₂) :
    (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) w * r
      = r * (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) w := by
  have hgen : ∀ x : A₁ ⊗[K] A₂,
      (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) (GradedTensorProduct.of K 𝒜₁ 𝒜₂ x) * r
        = r * (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti)
            (GradedTensorProduct.of K 𝒜₁ 𝒜₂ x) := by
    intro x
    induction x with
    | zero => simp
    | tmul p q =>
        show (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) (p ᵍ⊗ₜ[K] q) * r
          = r * (GradedTensorProduct.lift 𝒜₁ 𝒜₂ f₁ f₂ hanti) (p ᵍ⊗ₜ[K] q)
        rw [GradedTensorProduct.lift_tmul, mul_assoc, h2 q, ← mul_assoc, h1 p, mul_assoc]
    | add x y hx hy =>
        simp only [map_add, add_mul, mul_add]
        rw [hx, hy]
  have h := hgen ((GradedTensorProduct.of K 𝒜₁ 𝒜₂).symm w)
  rwa [LinearEquiv.apply_symm_apply] at h

end LiftCombine

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-! ### `Q4`'s four slot actions, as algebra maps into `End K Q4`

Literally the terms `QuadActions.lean` uses to build `Q4`'s registered
`Module` instances, so that `x • z = fA x z` etc. hold by `rfl`
(`aslot_apply`–`dslot_apply` below). -/

namespace Q4

/-- `Q4`'s `T_a`-slot, as an algebra map (`midAlgHom`, mid-of-mid
through the outer column). -/
private noncomputable abbrev fA :
    (stdTower (K := K) a).carrier →ₐ[K] Module.End K (Q4 K a b c d) :=
  midAlgHom (stdTower (K := K) (b + c + d)).grading (BR.grading K b c d)
    (stdTower (K := K) a).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c + d)).grading
      (TowerColumn.superCommSMul K a ((b + c) + d)))

/-- `Q4`'s `T_b`-slot, as an algebra map (`leftActionEnd`, lifting
`B_R(b,c,d)`'s own `b`-slot). -/
private noncomputable abbrev fB :
    (stdTower (K := K) b).carrier →ₐ[K] Module.End K (Q4 K a b c d) :=
  leftActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d)) (B := (stdTower (K := K) b).carrier)

/-- `Q4`'s `T_c`-slot, as an algebra map. -/
private noncomputable abbrev fC :
    (stdTower (K := K) c).carrier →ₐ[K] Module.End K (Q4 K a b c d) :=
  leftActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d)) (B := (stdTower (K := K) c).carrier)

/-- `Q4`'s `T_d`-slot, as an algebra map. -/
private noncomputable abbrev fD :
    (stdTower (K := K) d).carrier →ₐ[K] Module.End K (Q4 K a b c d) :=
  leftActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d)) (B := (stdTower (K := K) d).carrier)

theorem aslot_apply (x : (stdTower (K := K) a).carrier) (z : Q4 K a b c d) :
    x • z = fA K a b c d x z := rfl

theorem bslot_apply (y : (stdTower (K := K) b).carrier) (z : Q4 K a b c d) :
    y • z = fB K a b c d y z := rfl

theorem cslot_apply (w : (stdTower (K := K) c).carrier) (z : Q4 K a b c d) :
    w • z = fC K a b c d w z := rfl

theorem dslot_apply (t : (stdTower (K := K) d).carrier) (z : Q4 K a b c d) :
    t • z = fD K a b c d t z := rfl

/-! ### The six pairwise supercommutation certificates for `Q4`'s slots

`(a,b)`, `(a,c)`, `(a,d)` reduce directly to
`leftActionEnd_anticommutes_midAlgHom` (`T_a` is the mid-of-mid slot for
all three); `(b,c)`, `(b,d)`, `(c,d)` are fresh, lifted from
`B_R(b,c,d)`'s own pairwise `SuperCommSMul` certificates
(`RouteCompat.lean`) via `leftActionEnd_leftActionEnd_supercomm`. -/

/-- **The `Units.smul` swap of an anticommutation fact**: from `u = c •
v` with `c` an involutive `ℤˣ`-power, deduce `v = c • u` (multiply both
sides by `c` and use `c * c = 1`, `sgn_mul_self'`). -/
private theorem uzpow_smul_symm {X : Type*} [AddCommGroup X] {n : ZMod 2}
    {u v : X} (h : u = (-1 : ℤˣ) ^ n • v) : v = (-1 : ℤˣ) ^ n • u := by
  have hc : (-1 : ℤˣ) ^ n * (-1 : ℤˣ) ^ n = 1 := by
    rw [← sgn_eq_neg_one_uzpow, sgn_mul_self']
  rw [h, smul_smul, hc, one_smul]

theorem comm_ab ⦃i k : ZMod 2⦄ (x : (stdTower (K := K) a).grading i)
    (y : (stdTower (K := K) b).grading k) :
    fA K a b c d (x : (stdTower (K := K) a).carrier)
        * fB K a b c d (y : (stdTower (K := K) b).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fB K a b c d (y : (stdTower (K := K) b).carrier)
            * fA K a b c d (x : (stdTower (K := K) a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (stdTower (K := K) (b + c + d)).grading
    (BR.grading K b c d) (stdTower (K := K) a).grading (stdTower (K := K) b).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c + d)).grading
      (TowerColumn.superCommSMul K a ((b + c) + d))) y x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_ac ⦃i k : ZMod 2⦄ (x : (stdTower (K := K) a).grading i)
    (w : (stdTower (K := K) c).grading k) :
    fA K a b c d (x : (stdTower (K := K) a).carrier)
        * fC K a b c d (w : (stdTower (K := K) c).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fC K a b c d (w : (stdTower (K := K) c).carrier)
            * fA K a b c d (x : (stdTower (K := K) a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (stdTower (K := K) (b + c + d)).grading
    (BR.grading K b c d) (stdTower (K := K) a).grading (stdTower (K := K) c).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c + d)).grading
      (TowerColumn.superCommSMul K a ((b + c) + d))) w x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_ad ⦃i k : ZMod 2⦄ (x : (stdTower (K := K) a).grading i)
    (t : (stdTower (K := K) d).grading k) :
    fA K a b c d (x : (stdTower (K := K) a).carrier)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = (-1 : ℤˣ) ^ (k * i) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier)
            * fA K a b c d (x : (stdTower (K := K) a).carrier)) := by
  have h := leftActionEnd_anticommutes_midAlgHom (stdTower (K := K) (b + c + d)).grading
    (BR.grading K b c d) (stdTower (K := K) a).grading (stdTower (K := K) d).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c + d)).grading
      (TowerColumn.superCommSMul K a ((b + c) + d))) t x
  have h' := uzpow_smul_symm h
  rwa [mul_comm i k] at h'

theorem comm_bc ⦃i k : ZMod 2⦄ (y : (stdTower (K := K) b).grading i)
    (w : (stdTower (K := K) c).grading k) :
    fB K a b c d (y : (stdTower (K := K) b).carrier)
        * fC K a b c d (w : (stdTower (K := K) c).carrier)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (fC K a b c d (w : (stdTower (K := K) c).carrier)
            * fB K a b c d (y : (stdTower (K := K) b).carrier)) :=
  leftActionEnd_leftActionEnd_supercomm_end (stdTower (K := K) b).grading
    (stdTower (K := K) c).grading (BR.superCommSMul_aslot_bslot K b c d) y.2 w.2

theorem comm_bd ⦃i k : ZMod 2⦄ (y : (stdTower (K := K) b).grading i)
    (t : (stdTower (K := K) d).grading k) :
    fB K a b c d (y : (stdTower (K := K) b).carrier)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier)
            * fB K a b c d (y : (stdTower (K := K) b).carrier)) :=
  leftActionEnd_leftActionEnd_supercomm_end (stdTower (K := K) b).grading
    (stdTower (K := K) d).grading (BR.superCommSMul_aslot_cslot K b c d) y.2 t.2

theorem comm_cd ⦃i k : ZMod 2⦄ (w : (stdTower (K := K) c).grading i)
    (t : (stdTower (K := K) d).grading k) :
    fC K a b c d (w : (stdTower (K := K) c).carrier)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = ((sgn (i * k) : ℤˣ) : ℤ) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier)
            * fC K a b c d (w : (stdTower (K := K) c).carrier)) :=
  leftActionEnd_leftActionEnd_supercomm_end (stdTower (K := K) c).grading
    (stdTower (K := K) d).grading (BR.superCommSMul_bslot_cslot K b c d) w.2 t.2

/-! ### The same six facts, in the `sgn`-scalar convention feeding
`lift_anticommute_sgn`'s `h1`/`h2` parameters -/

private theorem comm_ac_sgn ⦃i k : ZMod 2⦄ (x : (stdTower (K := K) a).grading i)
    (w : (stdTower (K := K) c).grading k) :
    fA K a b c d (x : (stdTower (K := K) a).carrier)
        * fC K a b c d (w : (stdTower (K := K) c).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fC K a b c d (w : (stdTower (K := K) c).carrier)
            * fA K a b c d (x : (stdTower (K := K) a).carrier)) :=
  fromUzpow (comm_ac K a b c d x w)

private theorem comm_ad_sgn ⦃i k : ZMod 2⦄ (x : (stdTower (K := K) a).grading i)
    (t : (stdTower (K := K) d).grading k) :
    fA K a b c d (x : (stdTower (K := K) a).carrier)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier)
            * fA K a b c d (x : (stdTower (K := K) a).carrier)) :=
  fromUzpow (comm_ad K a b c d x t)

private theorem comm_bc_sgn ⦃i k : ZMod 2⦄ (y : (stdTower (K := K) b).grading i)
    (w : (stdTower (K := K) c).grading k) :
    fB K a b c d (y : (stdTower (K := K) b).carrier)
        * fC K a b c d (w : (stdTower (K := K) c).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fC K a b c d (w : (stdTower (K := K) c).carrier)
            * fB K a b c d (y : (stdTower (K := K) b).carrier)) := by
  rw [comm_bc K a b c d y w, mul_comm i k]

private theorem comm_bd_sgn ⦃i k : ZMod 2⦄ (y : (stdTower (K := K) b).grading i)
    (t : (stdTower (K := K) d).grading k) :
    fB K a b c d (y : (stdTower (K := K) b).carrier)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier)
            * fB K a b c d (y : (stdTower (K := K) b).carrier)) := by
  rw [comm_bd K a b c d y t, mul_comm i k]

private theorem comm_cd_sgn ⦃i k : ZMod 2⦄ (w : (stdTower (K := K) c).grading i)
    (t : (stdTower (K := K) d).grading k) :
    fC K a b c d (w : (stdTower (K := K) c).carrier)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier)
            * fC K a b c d (w : (stdTower (K := K) c).carrier)) := by
  rw [comm_cd K a b c d w t, mul_comm i k]

/-! ### The three iterated `GradedTensorProduct.lift`s, in `quadSource`'s
own order `(T_a, T_b)` then `T_c` then `T_d` -/

/-- **Step 1**: `T_a ᵍ⊗ T_b` acts on `Q4`. -/
private noncomputable def phi1 :
    ((stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading) →ₐ[K]
      Module.End K (Q4 K a b c d) :=
  GradedTensorProduct.lift (stdTower (K := K) a).grading (stdTower (K := K) b).grading
    (fA K a b c d) (fB K a b c d) (comm_ab K a b c d)

/-- The generator formula for `phi1` (`rfl`, isolated so downstream
`rw`-based proofs never re-trigger the defeq check). -/
private theorem phi1_tmul (x : (stdTower (K := K) a).carrier)
    (y : (stdTower (K := K) b).carrier) :
    (phi1 K a b c d) (x ᵍ⊗ₜ[K] y) = fA K a b c d x * fB K a b c d y := rfl

/-- `T_a ᵍ⊗ T_b` (already combined, Step 1) anticommutes with `T_c`
(`sgn`-scalar convention, feeding Step 2's own `hanti`). -/
private theorem phi1_comm_c ⦃i j : ZMod 2⦄
    (w : Superfusion.tensorGrading (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading i)
    (z : (stdTower (K := K) c).grading j) :
    (phi1 K a b c d) (w : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading)
        * fC K a b c d (z : (stdTower (K := K) c).carrier)
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (fC K a b c d (z : (stdTower (K := K) c).carrier) *
            (phi1 K a b c d)
              (w : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading)) :=
  lift_anticommute_sgn (stdTower (K := K) a).grading (stdTower (K := K) b).grading
    (stdTower (K := K) c).grading (fA K a b c d) (fB K a b c d) (comm_ab K a b c d)
    (fC K a b c d) (comm_ac_sgn K a b c d) (comm_bc_sgn K a b c d) w z

/-- `T_a ᵍ⊗ T_b` (already combined, Step 1) anticommutes with `T_d` —
preparation for Step 3, needed *before* `T_c` is folded in. -/
private theorem phi1_comm_d ⦃i j : ZMod 2⦄
    (w : Superfusion.tensorGrading (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading i)
    (t : (stdTower (K := K) d).grading j) :
    (phi1 K a b c d) (w : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier) *
            (phi1 K a b c d)
              (w : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading)) :=
  lift_anticommute_sgn (stdTower (K := K) a).grading (stdTower (K := K) b).grading
    (stdTower (K := K) d).grading (fA K a b c d) (fB K a b c d) (comm_ab K a b c d)
    (fD K a b c d) (comm_ad_sgn K a b c d) (comm_bd_sgn K a b c d) w t

/-- **Step 2**: `(T_a ᵍ⊗ T_b) ᵍ⊗ T_c` acts on `Q4`. -/
private noncomputable def phi2 :
    (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading
        ᵍ⊗[K] (stdTower (K := K) c).grading) →ₐ[K] Module.End K (Q4 K a b c d) :=
  GradedTensorProduct.lift
    (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
    (stdTower (K := K) c).grading (phi1 K a b c d) (fC K a b c d)
    (fun _ _ w z => toUzpow (phi1_comm_c K a b c d w z))

/-- The generator formula for `phi2` (`rfl`). -/
private theorem phi2_tmul
    (w1 : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading)
    (z1 : (stdTower (K := K) c).carrier) :
    (phi2 K a b c d) (w1 ᵍ⊗ₜ[K] z1) = (phi1 K a b c d) w1 * fC K a b c d z1 := rfl

/-- `(T_a ᵍ⊗ T_b) ᵍ⊗ T_c` (already combined, Step 2) anticommutes with
`T_d`, using the Step-3-preparation fact `phi1_comm_d` and the fresh
pairwise `(c,d)` fact `comm_cd_sgn`. -/
private theorem phi2_comm_d ⦃i j : ZMod 2⦄
    (w : Superfusion.tensorGrading
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading i)
    (t : (stdTower (K := K) d).grading j) :
    (phi2 K a b c d)
        (w : Superfusion.tensorGrading (stdTower (K := K) a).grading
              (stdTower (K := K) b).grading
            ᵍ⊗[K] (stdTower (K := K) c).grading)
        * fD K a b c d (t : (stdTower (K := K) d).carrier)
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          (fD K a b c d (t : (stdTower (K := K) d).carrier) *
            (phi2 K a b c d)
              (w : Superfusion.tensorGrading (stdTower (K := K) a).grading
                    (stdTower (K := K) b).grading
                  ᵍ⊗[K] (stdTower (K := K) c).grading)) :=
  lift_anticommute_sgn
    (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
    (stdTower (K := K) c).grading (stdTower (K := K) d).grading (phi1 K a b c d) (fC K a b c d)
    (fun _ _ w' z' => toUzpow (phi1_comm_c K a b c d w' z'))
    (fD K a b c d) (phi1_comm_d K a b c d) (comm_cd_sgn K a b c d) w t

/-- **Step 3**: `((T_a ᵍ⊗ T_b) ᵍ⊗ T_c) ᵍ⊗ T_d` acts on `Q4` — this is
`quadSource K a b c d`'s own carrier type, verbatim (`quadSource
(K := K) a b c d).carrier = (((stdTower a).gtensor (stdTower b)).gtensor
(stdTower c)).grading ᵍ⊗[K] (stdTower d).grading` by `PentagonChi.lean`'s
definition of `SuperAlgebra.gtensor`). -/
private noncomputable def phi3 :
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading
        ᵍ⊗[K] (stdTower (K := K) d).grading) →ₐ[K] Module.End K (Q4 K a b c d) :=
  GradedTensorProduct.lift
    (Superfusion.tensorGrading
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading)
    (stdTower (K := K) d).grading (phi2 K a b c d) (fD K a b c d)
    (fun _ _ w t => toUzpow (phi2_comm_d K a b c d w t))

/-- The generator formula for `phi3` (`rfl`). -/
private theorem phi3_tmul
    (w1 : Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading
        ᵍ⊗[K] (stdTower (K := K) c).grading)
    (t1 : (stdTower (K := K) d).carrier) :
    (phi3 K a b c d) (w1 ᵍ⊗ₜ[K] t1) = (phi2 K a b c d) w1 * fD K a b c d t1 := rfl

/-! ### Gradedness of `Q4`'s four slots, and of the combined `phi1`,
`phi2`, `phi3` -/

theorem fA_mem_grading ⦃i j : ZMod 2⦄ {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading i) {z : Q4 K a b c d}
    (hz : z ∈ Q4.grading K a b c d j) :
    fA K a b c d x z ∈ Q4.grading K a b c d (i + j) :=
  midEnd_mem_relGrading (stdTower (K := K) (b + c + d)).grading (BR.grading K b c d)
    (stdTower (K := K) a).grading (TowerColumn.grading K a ((b + c) + d))
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c + d)).grading
      (TowerColumn.superCommSMul K a ((b + c) + d))) hx hz

theorem fB_mem_grading ⦃i j : ZMod 2⦄ {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading i) {z : Q4 K a b c d}
    (hz : z ∈ Q4.grading K a b c d j) :
    fB K a b c d y z ∈ Q4.grading K a b c d (i + j) :=
  leftActionEnd_mem_relGrading (BR.grading K b c d) (TowerColumn.grading K a ((b + c) + d)) hy hz

theorem fC_mem_grading ⦃i j : ZMod 2⦄ {w : (stdTower (K := K) c).carrier}
    (hw : w ∈ (stdTower (K := K) c).grading i) {z : Q4 K a b c d}
    (hz : z ∈ Q4.grading K a b c d j) :
    fC K a b c d w z ∈ Q4.grading K a b c d (i + j) :=
  leftActionEnd_mem_relGrading (BR.grading K b c d) (TowerColumn.grading K a ((b + c) + d)) hw hz

theorem fD_mem_grading ⦃i j : ZMod 2⦄ {t : (stdTower (K := K) d).carrier}
    (ht : t ∈ (stdTower (K := K) d).grading i) {z : Q4 K a b c d}
    (hz : z ∈ Q4.grading K a b c d j) :
    fD K a b c d t z ∈ Q4.grading K a b c d (i + j) :=
  leftActionEnd_mem_relGrading (BR.grading K b c d) (TowerColumn.grading K a ((b + c) + d)) ht hz

private theorem phi1_mem_grading ⦃i j : ZMod 2⦄
    {w : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading}
    (hw : w ∈ Superfusion.tensorGrading (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading i)
    {z : Q4 K a b c d} (hz : z ∈ Q4.grading K a b c d j) :
    (phi1 K a b c d) w z ∈ Q4.grading K a b c d (i + j) := by
  have key : ∀ z' ∈ Q4.grading K a b c d j,
      (phi1 K a b c d) w z' ∈ Q4.grading K a b c d (i + j) := by
    refine Superfusion.tensorGrading_induction (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading
      (p := fun w' => ∀ z' ∈ Q4.grading K a b c d j,
        (phi1 K a b c d) w' z' ∈ Q4.grading K a b c d (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ x y hij hx hy z' hz'
      have hev : (phi1 K a b c d) (x ᵍ⊗ₜ[K] y) z' = fA K a b c d x (fB K a b c d y z') := by
        rw [phi1_tmul, Module.End.mul_apply]
      rw [hev]
      have h := fA_mem_grading K a b c d hx (fB_mem_grading K a b c d hy hz')
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
    {w : Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading
        ᵍ⊗[K] (stdTower (K := K) c).grading}
    (hw : w ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading i)
    {z : Q4 K a b c d} (hz : z ∈ Q4.grading K a b c d j) :
    (phi2 K a b c d) w z ∈ Q4.grading K a b c d (i + j) := by
  have key : ∀ z' ∈ Q4.grading K a b c d j,
      (phi2 K a b c d) w z' ∈ Q4.grading K a b c d (i + j) := by
    refine Superfusion.tensorGrading_induction
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading
      (p := fun w' => ∀ z' ∈ Q4.grading K a b c d j,
        (phi2 K a b c d) w' z' ∈ Q4.grading K a b c d (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ w1 z1 hij hw1 hz1 z' hz'
      have hev : (phi2 K a b c d) (w1 ᵍ⊗ₜ[K] z1) z'
          = (phi1 K a b c d) w1 (fC K a b c d z1 z') := by
        rw [phi2_tmul, Module.End.mul_apply]
      rw [hev]
      have h := phi1_mem_grading K a b c d hw1 (fC_mem_grading K a b c d hz1 hz')
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
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading
        ᵍ⊗[K] (stdTower (K := K) d).grading}
    (hw : w ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading i)
    {z : Q4 K a b c d} (hz : z ∈ Q4.grading K a b c d j) :
    (phi3 K a b c d) w z ∈ Q4.grading K a b c d (i + j) := by
  have key : ∀ z' ∈ Q4.grading K a b c d j,
      (phi3 K a b c d) w z' ∈ Q4.grading K a b c d (i + j) := by
    refine Superfusion.tensorGrading_induction
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading
      (p := fun w' => ∀ z' ∈ Q4.grading K a b c d j,
        (phi3 K a b c d) w' z' ∈ Q4.grading K a b c d (i + j))
      hw ?_ ?_ ?_ ?_
    · intro i₁ i₂ w1 t1 hij hw1 ht1 z' hz'
      have hev : (phi3 K a b c d) (w1 ᵍ⊗ₜ[K] t1) z'
          = (phi2 K a b c d) w1 (fD K a b c d t1 z') := by
        rw [phi3_tmul, Module.End.mul_apply]
      rw [hev]
      have h := phi2_mem_grading K a b c d hw1 (fD_mem_grading K a b c d ht1 hz')
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

/-! ### Commutation with `Q4`'s own native right `T_{a+(b+c+d)}`-action
(unsigned; `Q4`'s right tower matches `B_R(b,c,d)`'s own natural tower
exactly, no cast needed here — the cast to `QuadEnv`'s sop side comes
later) -/

/-- `Q4`'s own native right `T_{a+(b+c+d)}`-action, typed at `Module.End
K (Q4 K a b c d)` explicitly (`Q4` is a `def`, not `abbrev`, so bare
`rightActionEnd` applications do not automatically unify against it for
`HMul`/ring-multiplication instance search — this ascription is the
one-line fix). -/
private noncomputable def rQ4 (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    Module.End K (Q4 K a b c d) :=
  rightActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d)) τ

theorem rQ4_apply (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ) (z : Q4 K a b c d) :
    τ • z = rQ4 K a b c d τ z := rfl


theorem fA_comm_right (x : (stdTower (K := K) a).carrier)
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fA K a b c d x * rQ4 K a b c d τ
      = rQ4 K a b c d τ * fA K a b c d x :=
  midEnd_comm_rightActionEnd (stdTower (K := K) (b + c + d)).grading (BR.grading K b c d)
    (stdTower (K := K) a).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (b + c + d)).grading
      (TowerColumn.superCommSMul K a ((b + c) + d))) x τ

theorem fB_comm_right (y : (stdTower (K := K) b).carrier)
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fB K a b c d y * rQ4 K a b c d τ
      = rQ4 K a b c d τ * fB K a b c d y :=
  leftActionEnd_comm_rightActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d)) y τ

theorem fC_comm_right (w : (stdTower (K := K) c).carrier)
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fC K a b c d w * rQ4 K a b c d τ
      = rQ4 K a b c d τ * fC K a b c d w :=
  leftActionEnd_comm_rightActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d)) w τ

theorem fD_comm_right (t : (stdTower (K := K) d).carrier)
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ) :
    fD K a b c d t * rQ4 K a b c d τ
      = rQ4 K a b c d τ * fD K a b c d t :=
  leftActionEnd_comm_rightActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d)) t τ

private theorem phi1_comm_right
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (w : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading) :
    (phi1 K a b c d) w
        * rQ4 K a b c d τ
      = rQ4 K a b c d τ * (phi1 K a b c d) w :=
  lift_comm_right (stdTower (K := K) a).grading (stdTower (K := K) b).grading
    (fA K a b c d) (fB K a b c d) (comm_ab K a b c d)
    (fun x => fA_comm_right K a b c d x τ) (fun y => fB_comm_right K a b c d y τ) w

private theorem phi2_comm_right
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (w : Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading
        ᵍ⊗[K] (stdTower (K := K) c).grading) :
    (phi2 K a b c d) w
        * rQ4 K a b c d τ
      = rQ4 K a b c d τ * (phi2 K a b c d) w :=
  lift_comm_right
    (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
    (stdTower (K := K) c).grading (phi1 K a b c d) (fC K a b c d)
    (fun _ _ w' z' => toUzpow (phi1_comm_c K a b c d w' z'))
    (fun w' => phi1_comm_right K a b c d τ w') (fun z' => fC_comm_right K a b c d z' τ) w

private theorem phi3_comm_right
    (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (w : Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading
        ᵍ⊗[K] (stdTower (K := K) d).grading) :
    (phi3 K a b c d) w
        * rQ4 K a b c d τ
      = rQ4 K a b c d τ * (phi3 K a b c d) w :=
  lift_comm_right
    (Superfusion.tensorGrading
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading)
    (stdTower (K := K) d).grading (phi2 K a b c d) (fD K a b c d)
    (fun _ _ w' t' => toUzpow (phi2_comm_d K a b c d w' t'))
    (fun w' => phi2_comm_right K a b c d τ w') (fun t' => fD_comm_right K a b c d t' τ) w

/-! ### Assembling `Module (QuadEnv K a b c d) (Q4 K a b c d)` -/

/-- **Bridge**: `Q4`'s combined `phi3`-action, at the `quadSource K a
b c d` `.gtensor.carrier` spelling `phi3`'s own domain is definitionally
identical to (`PentagonChi.lean`'s `SuperAlgebra.gtensor`). -/
noncomputable instance instModuleGtensorABCDRaw :
    Module (Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading
        ᵍ⊗[K] (stdTower (K := K) d).grading) (Q4 K a b c d) :=
  Module.compHom (Q4 K a b c d) (phi3 K a b c d).toRingHom

noncomputable instance instModuleQuadSource :
    Module (quadSource (K := K) a b c d).carrier (Q4 K a b c d) :=
  inferInstanceAs (Module
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading
        ᵍ⊗[K] (stdTower (K := K) d).grading) (Q4 K a b c d))

instance : IsScalarTower K
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading
        ᵍ⊗[K] (stdTower (K := K) d).grading) (Q4 K a b c d) :=
  ⟨fun k w m => by
    show (phi3 K a b c d) (k • w) m = k • (phi3 K a b c d) w m
    rw [map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (quadSource (K := K) a b c d).carrier (Q4 K a b c d) :=
  inferInstanceAs (IsScalarTower K
    (Superfusion.tensorGrading
        (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
        (stdTower (K := K) c).grading
        ᵍ⊗[K] (stdTower (K := K) d).grading) (Q4 K a b c d))

/-- **`Q4`'s combined action is graded** (`phi3_mem_grading`, from the
gradedness cascade above). -/
instance : SetLike.GradedSMul (quadSource (K := K) a b c d).grading (grading K a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact phi3_mem_grading K a b c d hw hz

/-- The associativity recast between `Q4`'s own native right tower
`T_{a+(b+c+d)}` and `QuadEnv`'s sop-side tower `T_{a+b+c+d}` — matches
`QuadInterSpace.lean`'s `quadRightCast_eq` (reproved locally, that one
being `private`). -/
private theorem quadRightCast_eq : a + b + c + d = a + (b + c + d) := by ring

/-- `Q4`'s own native right action is a `K`-scalar tower (needed by the
recast `IsScalarTower` instance below, via `smul_assoc`). -/
instance : IsScalarTower K ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ (Q4 K a b c d) :=
  ⟨fun k τ z => by
    show rightActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
        (TowerColumn K a ((b + c) + d)) (k • τ) z
      = k • rightActionEnd K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
          (TowerColumn K a ((b + c) + d)) τ z
    rw [map_smul, LinearMap.smul_apply]⟩

/-- `QuadEnv`'s sop-side right `T_{a+b+c+d}`-action on `Q4`, pulled
back along the associativity cast from `Q4`'s own native
`T_{a+(b+c+d)}`-action (the `RouteRecast.lean` device:
`Module.compHom` along `(stdTowerCast _).toAlgEquiv.toRingHom.op`). -/
noncomputable instance instModuleRightRecast :
    Module ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q4 K a b c d) :=
  Module.compHom (Q4 K a b c d)
    (((stdTowerCast (K := K) (quadRightCast_eq a b c d)).toAlgEquiv.toRingHom).op)

theorem rightRecast_op_smul_def (τ : (stdTower (K := K) (a + b + c + d)).carrier)
    (z : Q4 K a b c d) :
    MulOpposite.op τ • z
      = MulOpposite.op ((stdTowerCast (K := K) (quadRightCast_eq a b c d)).toAlgEquiv τ) • z :=
  rfl

instance : IsScalarTower K ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q4 K a b c d) :=
  ⟨fun k τ z => by
    show MulOpposite.op ((stdTowerCast (K := K) (quadRightCast_eq a b c d)).toAlgEquiv
        (MulOpposite.unop (k • τ))) • z
      = k • (MulOpposite.op ((stdTowerCast (K := K) (quadRightCast_eq a b c d)).toAlgEquiv
          (MulOpposite.unop τ)) • z)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ z⟩

/-- **`Q4`'s combined action commutes with the recast right action**
(`phi3_comm_right`, transported along the recast via
`rightRecast_op_smul_def` and `rQ4_apply`). -/
instance : SMulCommClass (quadSource (K := K) a b c d).carrier
    ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ (Q4 K a b c d) :=
  ⟨fun w t z => by
    show (phi3 K a b c d) w
        (MulOpposite.op ((stdTowerCast (K := K) (quadRightCast_eq a b c d)).toAlgEquiv
          (MulOpposite.unop t)) • z)
      = MulOpposite.op ((stdTowerCast (K := K) (quadRightCast_eq a b c d)).toAlgEquiv
          (MulOpposite.unop t)) • (phi3 K a b c d) w z
    rw [rQ4_apply, rQ4_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
      phi3_comm_right]⟩

/-- `Q4`'s own native right `T_{a+(b+c+d)}`-action is graded
(`rightActionEnd_mem_relGrading`, mirroring `RouteCompat.lean`'s
`BL`/`BR` instances). -/
instance : GradedRightSMul (stdTower (K := K) (a + (b + c + d))).grading (grading K a b c d) where
  smul_mem _ _ _ _ hτ hw :=
    rightActionEnd_mem_relGrading (BR.grading K b c d) (TowerColumn.grading K a ((b + c) + d))
      hτ hw

/-- `Q4`'s own right action is graded, for `QuadEnv`'s sop-side tower
(the recast right coefficient action, mirroring `RouteCompat.lean`'s
`BR` recast instance). -/
instance : GradedRightSMul (stdTower (K := K) (a + b + c + d)).grading (grading K a b c d) where
  smul_mem _ _ _ _ hτ hw := by
    rw [rightRecast_op_smul_def]
    exact GradedRightSMul.smul_mem
      (stdTowerCast_mem_grading K (quadRightCast_eq a b c d) hτ) hw

/-- **`Q4` is a `QuadEnv K a b c d`-module**: the `quadSource`-action
(`phi1`–`phi3`, direct iteration in `quadSource`'s own order) and `Q4`'s
own right `T_{a+(b+c+d)}`-action (recast to `T_{a+b+c+d}`) assemble via
`Bimod.module`. -/
noncomputable instance instModuleQuadEnv : Module (QuadEnv K a b c d) (Q4 K a b c d) :=
  Bimod.module (quadSource (K := K) a b c d).grading (stdTower (K := K) (a + b + c + d)).grading
    (grading K a b c d)


/-! ### The four slot-embedding generators (M8a-8d′-iii-a″, item (b))

`Q4`'s `quadSource`-carrier action, restricted to a slot generator `x`
embedded through the three-fold `includeLeft`/`includeRight` chain
matching `quadSource`'s own bracket order, literally *is* the slot
action `fA`–`fD` (`aslot_apply`–`dslot_apply`) — a direct consequence
of `GradedTensorProduct.lift_tmul` (itself `rfl`) and `map_one` at each
of the (at most three) levels, no induction anywhere (unlike `Q1`'s
mirror facts, `QuadInterface.lean`, which need `RelTensor.hom_ext`
since `Q1`'s slot actions are built through the `TowerColumn`/`B_L`
intermediate layers rather than directly from `fA`–`fD`).  These need
`fA`–`fD`/`phi1`–`phi3` directly, hence must live in this file (they
are `private`); `quadSource_smul_def` first turns the `QuadEnv`-module
`•` into a plain `phi3`-application, and the intermediate levels are
taken as explicit parameters (mirroring `QuadInterface.lean`'s `Q1`
counterparts) rather than baked into the statement, since `rw`'s
motive-typechecking otherwise chokes on the `(quadSource …).carrier`
ascription once the argument is unfolded past the outermost `•` (a
`HSMul` instance argument, unlike a plain function argument, is frozen
at elaboration time and does not track through `rw`) — a single
slot-embedding term, built this way, serves both vertices in the
interface's `⊇` direction. -/

theorem quadSource_smul_def (w : (quadSource (K := K) a b c d).carrier) (z : Q4 K a b c d) :
    w • z = phi3 K a b c d w z := rfl

theorem aEmbed_smul
    (x₀ : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading) (x : (stdTower (K := K) a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (stdTower (K := K) a).grading (stdTower (K := K) b).grading x)
    (x₁ : (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) ᵍ⊗[K] (stdTower (K := K) c).grading)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) (stdTower (K := K) c).grading x₀)
    (x₂ : (quadSource (K := K) a b c d).carrier)
    (hx₂ : x₂ = GradedTensorProduct.includeLeft (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) (stdTower (K := K) c).grading) (stdTower (K := K) d).grading x₁)
    (z : Q4 K a b c d) :
    x₂ • z = x • z := by
  rw [quadSource_smul_def, aslot_apply]
  have h1 : phi1 K a b c d x₀ = fA K a b c d x := by
    rw [hx₀]
    show fA K a b c d x * fB K a b c d 1 = fA K a b c d x
    rw [map_one, mul_one]
  have h2 : phi2 K a b c d x₁ = fA K a b c d x := by
    rw [hx₁]
    show phi1 K a b c d x₀ * fC K a b c d 1 = fA K a b c d x
    rw [map_one, mul_one, h1]
  rw [hx₂]
  show (phi2 K a b c d x₁ * fD K a b c d 1) z = fA K a b c d x z
  rw [map_one, mul_one, h2]

theorem bEmbed_smul
    (y₀ : (stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading) (y : (stdTower (K := K) b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (stdTower (K := K) a).grading (stdTower (K := K) b).grading y)
    (y₁ : (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) ᵍ⊗[K] (stdTower (K := K) c).grading)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) (stdTower (K := K) c).grading y₀)
    (y₂ : (quadSource (K := K) a b c d).carrier)
    (hy₂ : y₂ = GradedTensorProduct.includeLeft (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) (stdTower (K := K) c).grading) (stdTower (K := K) d).grading y₁)
    (z : Q4 K a b c d) :
    y₂ • z = y • z := by
  rw [quadSource_smul_def, bslot_apply]
  have h1 : phi1 K a b c d y₀ = fB K a b c d y := by
    rw [hy₀]
    show fA K a b c d 1 * fB K a b c d y = fB K a b c d y
    rw [map_one, one_mul]
  have h2 : phi2 K a b c d y₁ = fB K a b c d y := by
    rw [hy₁]
    show phi1 K a b c d y₀ * fC K a b c d 1 = fB K a b c d y
    rw [map_one, mul_one, h1]
  rw [hy₂]
  show (phi2 K a b c d y₁ * fD K a b c d 1) z = fB K a b c d y z
  rw [map_one, mul_one, h2]

theorem cEmbed_smul
    (w₀ : (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) ᵍ⊗[K] (stdTower (K := K) c).grading) (w : (stdTower (K := K) c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) (stdTower (K := K) c).grading w)
    (w₁ : (quadSource (K := K) a b c d).carrier)
    (hw₁ : w₁ = GradedTensorProduct.includeLeft (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) (stdTower (K := K) c).grading) (stdTower (K := K) d).grading w₀)
    (z : Q4 K a b c d) :
    w₁ • z = w • z := by
  rw [quadSource_smul_def, cslot_apply]
  have h2 : phi2 K a b c d w₀ = fC K a b c d w := by
    rw [hw₀]
    show phi1 K a b c d 1 * fC K a b c d w = fC K a b c d w
    rw [map_one, one_mul]
  rw [hw₁]
  show (phi2 K a b c d w₀ * fD K a b c d 1) z = fC K a b c d w z
  rw [map_one, mul_one, h2]

theorem dEmbed_smul
    (t₀ : (quadSource (K := K) a b c d).carrier) (t : (stdTower (K := K) d).carrier)
    (ht₀ : t₀ = GradedTensorProduct.includeRight (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading) (stdTower (K := K) c).grading) (stdTower (K := K) d).grading t)
    (z : Q4 K a b c d) :
    t₀ • z = t • z := by
  rw [quadSource_smul_def, dslot_apply, ht₀]
  show (phi2 K a b c d 1 * fD K a b c d t) z = fD K a b c d t z
  rw [map_one, one_mul]

end Q4

end PentagonB

end Bimod

end Superfusion

/-
Superfusion / Bimod / QuadInterface

Milestone M8a-8d′-iii-a″ (roadmap v3): **the interface** —
`quadInterSpace = gradedHomF` at `QuadEnv` — the last piece of plumbing
between the tower pentagon (`QuadInterSpace.lean`'s six-condition
`quadInterSpace`) and the 8d′ general layer (`ParityBridge.lean`'s
`gradedHomF`, defined for any `[Module T M] [Module T N]` pair against
a submodule grading `𝒯` of `T`).

Four pieces, in increasing order of depth:

(a) **Envelope-action gradedness (general layer, `namespace Bimod`).**
    `actionHom_mem_tensorGrading`: `Bimod.Basic`'s `actionHom` shifts
    the module grading by the *tensor* grading of the envelope
    (`Superfusion.tensorGrading 𝒜 (SuperOp.grading ℬ)`, M7f-1a's
    grading making `𝒜 ᵍ⊗ ℬ` a graded algebra) — lifted from the
    tmul-generator fact `actionHom_tmul_smul_mem` (already landed in
    `Basic.lean`) via `Superfusion.tensorGrading_induction`.
    Instantiated at `QuadEnv`'s two module structures (`Q1`, `Q4`) as
    plain `SetLike.GradedSMul` instances, matching the established
    idiom (`rw [vadd_eq_add]; exact ...`).

(b) **Envelope generator evaluation (general layer).**  `actionHom`'s
    defining formula (`Basic.lean`'s `GradedTensorProduct.lift`)
    evaluated at the two pure generator families of the envelope: the
    "left" generators `x ᵍ⊗ (op 1)` (for *any* `x : A`, not only
    homogeneous — `actionHom_tmul_one_apply`) recover the bare `A`-module
    action, and the "right" generators `(1 : A) ᵍ⊗ b` (for any
    `b : SuperOp ℬ` — `actionHom_one_tmul_apply`) recover
    `rightActionHom`.  Both are one-line consequences of
    `actionHom_tmul_apply` plus the `map_one` of `rightActionHom`,
    since the mixed sign of `actionHom_tmul_apply_of_mem` degenerates
    at the (even) unit generator on either side.

    A companion general fact, needed to connect these envelope-level
    formulas to `Q1`'s/`Q4`'s own *slot* actions (built through several
    further layers of `gtensorLeftActionHom`/`GradedTensorProduct.lift`,
    `QuadEnvModule.lean`/`QuadEnvModule2.lean`): a `gtensorLeftActionHom`
    (`MiddleActionHom.lean`) collapses at the two slot-embedding
    generators `includeLeft`/`includeRight` to its two constituent maps
    (`gtensorLeftActionHom_includeLeft`/`_includeRight`), again for
    *any* (not necessarily homogeneous) generator — a direct consequence
    of `GradedTensorProduct.lift_tmul` (itself `rfl`) and `map_one`, no
    induction anywhere.  Chaining this fact through the two/three levels
    of each vertex's construction (using `RelTensor.hom_ext` to lift a
    generator-level `Module.End` identity to a genuine equality of
    endomorphisms, hence to a fact holding at *every* element, not only
    `mk`-generators) produces the eight slot-embedding bridges
    `Q1.aEmbed_smul_eq` .. `Q4.dEmbed_smul_eq`: the `QuadEnv` (or
    `quadSource`) action at a slot generator, embedded into the source
    tensor via the appropriate `includeLeft`/`includeRight` chain,
    literally IS the vertex's own registered slot action, on *every*
    element of the vertex (not merely spelled generators) — the
    generator evaluation this milestone's design note calls for.

(c)+(d) **The interface lemma**
    `mem_quadInterSpace_iff_gradedHomF`.  The `⊇` (restriction) direction
    (`gradedHomF → quadInterSpace`) evaluates a `QuadEnv`-super-equivariant
    `f` at the slot-embedding generators (via (b)) and the sop generators
    `1 ᵍ⊗ (op τ)` to recover the four slot super-equivariances and
    right-semilinearity; `homGrading` matches verbatim (same descended
    gradings on both sides).  See the session report for the status of
    the `⊆` (extension) direction.
-/
import Superfusion.Bimod.QuadEnvModule2
import Superfusion.Bimod.QuadInterSpace
import Superfusion.Bimod.ParityBridge

namespace Superfusion

namespace Bimod

open scoped TensorProduct

/-! ### (a) General layer: gradedness of the envelope action -/

section EnvelopeGraded

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
variable [IsScalarTower K A M] [IsScalarTower K Bᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul ℬ ℳ]

/-- **The envelope action is graded**: a homogeneous element of
`Envelope 𝒜 ℬ = 𝒜 ᵍ⊗ (SuperOp.grading ℬ)` of degree `i` (for
`Superfusion.tensorGrading`, M7f-1a's grading making `𝒜 ᵍ⊗ ℬ` a graded
algebra) shifts `actionHom`'s module grading by `i` — lifted from the
tmul-generator fact `actionHom_tmul_smul_mem` (`Basic.lean`) by
`Superfusion.tensorGrading_induction`, with the usual `← add_assoc`
index-association discipline. -/
theorem actionHom_mem_tensorGrading {i j : ZMod 2}
    {w : Envelope 𝒜 ℬ} (hw : w ∈ Superfusion.tensorGrading 𝒜 (SuperOp.grading ℬ) i)
    {m : M} (hm : m ∈ ℳ j) :
    actionHom 𝒜 ℬ ℳ w m ∈ ℳ (i + j) := by
  refine Superfusion.tensorGrading_induction 𝒜 (SuperOp.grading ℬ)
    (p := fun w' => actionHom 𝒜 ℬ ℳ w' m ∈ ℳ (i + j)) hw ?_ ?_ ?_ ?_
  · intro j₁ k₁ x y hjk hx hy
    have h := actionHom_tmul_smul_mem 𝒜 ℬ ℳ hx hy hm
    rwa [← add_assoc, hjk] at h
  · rw [map_zero, LinearMap.zero_apply]
    exact zero_mem _
  · intro w1 w2 h1 h2
    rw [map_add, LinearMap.add_apply]
    exact add_mem h1 h2
  · intro c w1 h1
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ c h1

end EnvelopeGraded

/-! ### (b) General layer: envelope generator evaluation -/

section EnvelopeGenerators

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
variable [IsScalarTower K A M] [IsScalarTower K Bᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul ℬ ℳ]

/-- **The envelope action at the "left" generator `x ᵍ⊗ (op 1)`, for
any `x : A`** (no homogeneity needed): it is exactly the bare `A`-action
— `signedRSMul ℬ ℳ 1 = 1` since `1` is even. -/
theorem actionHom_tmul_one_apply (x : A) (m : M) :
    actionHom 𝒜 ℬ ℳ (x ᵍ⊗ₜ[K] (1 : SuperOp ℬ)) m = x • m := by
  rw [actionHom_tmul_apply, ← rightActionHom_apply, map_one, Module.End.one_apply]

/-- **The envelope action at the "right" generator `(1 : A) ᵍ⊗ b`, for
any `b : SuperOp ℬ`** (no homogeneity needed): it is exactly
`rightActionHom`. -/
theorem actionHom_one_tmul_apply (b : SuperOp ℬ) (m : M) :
    actionHom 𝒜 ℬ ℳ ((1 : A) ᵍ⊗ₜ[K] b) m = rightActionHom ℬ ℳ b m := by
  rw [actionHom_tmul_apply, one_smul, rightActionHom_apply]

/-- `actionHom_tmul_one_apply`, restated at the `includeLeft`-spelled
generator (`x ᵍ⊗ (op 1) = GradedTensorProduct.includeLeft 𝒜 (SuperOp.grading
ℬ) x`) so that `rw` can match it directly against a term built through
`includeLeft` (as every slot-embedding chain below is), rather than
needing an intermediate unfold. -/
theorem actionHom_includeLeft_apply (x : A) (m : M) :
    actionHom 𝒜 ℬ ℳ (GradedTensorProduct.includeLeft 𝒜 (SuperOp.grading ℬ) x) m = x • m :=
  actionHom_tmul_one_apply 𝒜 ℬ ℳ x m

/-- `actionHom_one_tmul_apply`, restated at the `includeRight`-spelled
generator, for the same `rw`-matching reason. -/
theorem actionHom_includeRight_apply (b : SuperOp ℬ) (m : M) :
    actionHom 𝒜 ℬ ℳ (GradedTensorProduct.includeRight 𝒜 (SuperOp.grading ℬ) b) m
      = rightActionHom ℬ ℳ b m :=
  actionHom_one_tmul_apply 𝒜 ℬ ℳ b m

end EnvelopeGenerators

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-- The tensor grading of `QuadEnv`'s own envelope tensor
(`Superfusion.tensorGrading`, M7f-1a's grading making `𝒜 ᵍ⊗ ℬ` a graded
algebra) — the grading `superEquivariant`/`gradedHomF` quantify over
when `𝒯 := QuadEnv K a b c d`. -/
noncomputable abbrev quadEnvGrading : ZMod 2 → Submodule K (QuadEnv K a b c d) :=
  Superfusion.tensorGrading (quadSource (K := K) a b c d).grading
    (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading)

namespace Q1

/-- **(a) for `Q1`**: the `QuadEnv` action is graded —
`actionHom_mem_tensorGrading` instantiated at `Q1`'s own `QuadEnv`
-module structure (`instModuleQuadEnv`, `QuadEnvModule.lean`). -/
instance : SetLike.GradedSMul (quadEnvGrading K a b c d) (grading K a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact actionHom_mem_tensorGrading _ _ _ hw hz

end Q1

namespace Q4

/-- **(a) for `Q4`**: the `QuadEnv` action is graded —
`actionHom_mem_tensorGrading` instantiated at `Q4`'s own `QuadEnv`
-module structure (`instModuleQuadEnv`, `QuadEnvModule2.lean`). -/
instance : SetLike.GradedSMul (quadEnvGrading K a b c d) (grading K a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact actionHom_mem_tensorGrading _ _ _ hw hz

end Q4

/-- `SMulCommClass K (QuadEnv K a b c d) (Q1 K a b c d)`: for any
`Module.compHom`-built action of a `K`-algebra `T` (here `T := QuadEnv
K a b c d`, via `actionHom .toRingHom`), the resulting `T`-action is
automatically `K`-linear on each fixed `w`, since `actionHom 𝒜 ℬ ℳ w`
is *already* a `K`-linear map `M →ₗ[K] M` by construction — no further
hypothesis needed, `map_smul` of that bundled map is exactly the
`smul_comm` field. Needed for `gradedHomF`'s own `[SMulCommClass K T N]`
hypothesis (`N := Q1/Q4 K a b c d`). -/
instance : SMulCommClass K (QuadEnv K a b c d) (Q1 K a b c d) :=
  ⟨fun k w m => (map_smul (actionHom (quadSource (K := K) a b c d).grading
      (stdTower (K := K) (a + b + c + d)).grading (Q1.grading K a b c d) w) k m).symm⟩

instance : SMulCommClass K (QuadEnv K a b c d) (Q4 K a b c d) :=
  ⟨fun k w m => (map_smul (actionHom (quadSource (K := K) a b c d).grading
      (stdTower (K := K) (a + b + c + d)).grading (Q4.grading K a b c d) w) k m).symm⟩

/-! ### (b), continued: `Q1`'s eight slot-embedding bridges

`Q1`'s four slot actions (`QuadActions.lean`) are built through the
`TowerColumn`/`B_L` intermediate layers (`RouteBimod.lean`/
`TowerColumn.lean`), each one itself a `leftActionEnd`/`midAlgHom`
application whose *own* outer algebra is built via
`GradedTensorProduct.includeLeft`/`_includeRight` one level further
down (`TowerColumn`'s pulled-back slot actions, M8a-7c-2) — so
connecting `Q1`'s registered slot action to the envelope's
`includeLeft`-embedded slot generator needs the collapse fact of (b)
applied *twice* (once at `TowerColumn`'s own level, `B_L`'s own
`gtensorLeftActionHom`, M8a-8d′-iii-a) and once more at `Q1`'s own
`gtensorLeftActionHom` (M8a-8d′-iii-a) — each transition lifted from a
generator-level fact to a genuine equality of `Module.End`s via
`RelTensor.hom_ext`, landing a fact that holds at *every* element of
the vertex, not merely `mk`-generators.  The `d`-slot needs only the
single (`Q1`-level) transition, since `T_d` is `Q1`'s own direct middle
slot (no `TowerColumn`/`B_L` level involved).  Every intermediate
"elementwise smul = registered instance's function application" bridge
below is `rfl` (`Module.compHom`'s defining property) and is stated
*only* at the exact carrier spelling the registered instance search
needs — mixing spellings mid-proof defeats `rw`'s pattern matching
(the M8a-8d′-iii-a′ lesson). -/

namespace Q1

theorem aslot_apply (x : (stdTower (K := K) a).carrier) (z : Q1 K a b c d) :
    x • z = leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d) x z := rfl

theorem bslot_apply (y : (stdTower (K := K) b).carrier) (z : Q1 K a b c d) :
    y • z = leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d) y z := rfl

theorem cslot_apply (w : (stdTower (K := K) c).carrier) (z : Q1 K a b c d) :
    w • z = leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d) w z := rfl

theorem dslot_apply (t : (stdTower (K := K) d).carrier) (z : Q1 K a b c d) :
    t • z = midAlgHom (stdTower (K := K) (a + b + c)).grading (BL.grading K a b c)
      (stdTower (K := K) d).grading (TowerColumn.superCommSMul K (a + b + c) d) t z := rfl

theorem gtensorABCD_smul_def (w : (quadSource (K := K) a b c d).carrier) (m : Q1 K a b c d) :
    w • m = gtensorLeftActionHom (stdTower (K := K) (a + b + c)).grading (BL.grading K a b c)
      (stdTower (K := K) d).grading
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
      (TowerColumn.superCommSMul K (a + b + c) d) w m := rfl

end Q1

/-- `B_L`'s combined `((T_a ᵍ⊗ T_b) ᵍ⊗ T_c)`-action at the carrier
spelling (`BL.gtensorABCRaw_smul_def`, `QuadEnvModule.lean`, is stated
at the raw `ᵍ⊗` spelling instead — this bridge, `rfl`, matches the
spelling `Q1`'s own construction needs downstream). -/
theorem BL.gtensorABC_smul_def
    (w : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (m : BL K a b c) :
    w • m = gtensorLeftActionHom (stdTower (K := K) (a + b)).grading (TowerColumn.grading K a b)
      (stdTower (K := K) c).grading ((stdTower (K := K) a).gtensor (stdTower b)).grading
      (TowerColumn.superCommSMul K (a + b) c) w m := rfl

theorem BL.aslot_apply (x : (stdTower (K := K) a).carrier) (w : BL K a b c) :
    x • w = leftActionEnd K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c) x w := rfl

theorem BL.bslot_apply (y : (stdTower (K := K) b).carrier) (w : BL K a b c) :
    y • w = leftActionEnd K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) c) y w := rfl

theorem BL.cslot_apply (w' : (stdTower (K := K) c).carrier) (u : BL K a b c) :
    w' • u = midAlgHom (stdTower (K := K) (a + b)).grading (TowerColumn.grading K a b)
      (stdTower (K := K) c).grading (TowerColumn.superCommSMul K (a + b) c) w' u := rfl

/-- The `a`-slot generator, embedded via `TowerColumn`'s own
`includeLeft`, agrees with `TowerColumn`'s registered `a`-slot action
on every element (`TowerColumn.gtensor_smul_def`/`lslot_smul_def`,
both `rfl` to the same normal form). -/
theorem TowerColumn.aEmbed
    (x₀ : ((stdTower (K := K) a).gtensor (stdTower b)).carrier) (x : (stdTower (K := K) a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading x)
    (v : TowerColumn K a b) :
    x₀ • v = x • v := by
  rw [TowerColumn.gtensor_smul_def, hx₀, TowerColumn.lslot_smul_def]

theorem TowerColumn.bEmbed
    (y₀ : ((stdTower (K := K) a).gtensor (stdTower b)).carrier) (y : (stdTower (K := K) b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading y)
    (v : TowerColumn K a b) :
    y₀ • v = y • v := by
  rw [TowerColumn.gtensor_smul_def, hy₀, TowerColumn.rslot_smul_def]

theorem BL.aEmbed
    (x₀ : ((stdTower (K := K) a).gtensor (stdTower b)).carrier) (x : (stdTower (K := K) a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading x)
    (x₁ : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (stdTower (K := K) c).grading x₀)
    (w : BL K a b c) :
    x₁ • w = x • w := by
  have key : (leftActionEnd K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
        (TowerColumn K (a + b) c) x₀
      : Module.End K (BL K a b c))
      = (leftActionEnd K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
        (TowerColumn K (a + b) c) (B := (stdTower (K := K) a).carrier) x) := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, TowerColumn.aEmbed K a b x₀ x hx₀]
  rw [BL.gtensorABC_smul_def, hx₁, gtensorLeftActionHom_includeLeft, key, ← BL.aslot_apply]

theorem BL.bEmbed
    (y₀ : ((stdTower (K := K) a).gtensor (stdTower b)).carrier) (y : (stdTower (K := K) b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading y)
    (y₁ : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (stdTower (K := K) c).grading y₀)
    (w : BL K a b c) :
    y₁ • w = y • w := by
  have key : (leftActionEnd K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
        (TowerColumn K (a + b) c) y₀
      : Module.End K (BL K a b c))
      = (leftActionEnd K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
        (TowerColumn K (a + b) c) (B := (stdTower (K := K) b).carrier) y) := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, TowerColumn.bEmbed K a b y₀ y hy₀]
  rw [BL.gtensorABC_smul_def, hy₁, gtensorLeftActionHom_includeLeft, key, ← BL.bslot_apply]

theorem BL.cEmbed
    (w₀ : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (w' : (stdTower (K := K) c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (stdTower (K := K) c).grading w')
    (u : BL K a b c) :
    w₀ • u = w' • u := by
  rw [BL.gtensorABC_smul_def, hw₀, gtensorLeftActionHom_includeRight, ← BL.cslot_apply]

namespace Q1

/-- **The `a`-slot-embedding bridge**: the `quadSource`-carrier element
obtained by embedding `x : T_a` via the three-fold `includeLeft` chain
matching `quadSource`'s own bracket order acts on `Q1`, on *every*
element, exactly as `Q1`'s own registered `a`-slot action of `x`. -/
theorem aEmbed
    (x₀ : ((stdTower (K := K) a).gtensor (stdTower b)).carrier) (x : (stdTower (K := K) a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading x)
    (x₁ : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (stdTower (K := K) c).grading x₀)
    (x₂ : (quadSource (K := K) a b c d).carrier)
    (hx₂ : x₂ = GradedTensorProduct.includeLeft
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (stdTower (K := K) d).grading x₁)
    (z : Q1 K a b c d) :
    x₂ • z = x • z := by
  have key : (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
        (TowerColumn K (a + b + c) d) x₁
      : Module.End K (Q1 K a b c d))
      = (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
        (TowerColumn K (a + b + c) d) (B := (stdTower (K := K) a).carrier) x) := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, BL.aEmbed K a b c x₀ x hx₀ x₁ hx₁]
  rw [gtensorABCD_smul_def, hx₂, gtensorLeftActionHom_includeLeft, key, ← aslot_apply]

theorem bEmbed
    (y₀ : ((stdTower (K := K) a).gtensor (stdTower b)).carrier) (y : (stdTower (K := K) b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading y)
    (y₁ : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (stdTower (K := K) c).grading y₀)
    (y₂ : (quadSource (K := K) a b c d).carrier)
    (hy₂ : y₂ = GradedTensorProduct.includeLeft
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (stdTower (K := K) d).grading y₁)
    (z : Q1 K a b c d) :
    y₂ • z = y • z := by
  have key : (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
        (TowerColumn K (a + b + c) d) y₁
      : Module.End K (Q1 K a b c d))
      = (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
        (TowerColumn K (a + b + c) d) (B := (stdTower (K := K) b).carrier) y) := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, BL.bEmbed K a b c y₀ y hy₀ y₁ hy₁]
  rw [gtensorABCD_smul_def, hy₂, gtensorLeftActionHom_includeLeft, key, ← bslot_apply]

theorem cEmbed
    (w₀ : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (w' : (stdTower (K := K) c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (stdTower (K := K) c).grading w')
    (w₁ : (quadSource (K := K) a b c d).carrier)
    (hw₁ : w₁ = GradedTensorProduct.includeLeft
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (stdTower (K := K) d).grading w₀)
    (z : Q1 K a b c d) :
    w₁ • z = w' • z := by
  have key : (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
        (TowerColumn K (a + b + c) d) w₀
      : Module.End K (Q1 K a b c d))
      = (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
        (TowerColumn K (a + b + c) d) (B := (stdTower (K := K) c).carrier) w') := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, BL.cEmbed K a b c w₀ w' hw₀]
  rw [gtensorABCD_smul_def, hw₁, gtensorLeftActionHom_includeLeft, key, ← cslot_apply]

/-- **The `d`-slot-embedding bridge** — a single (`Q1`-level) collapse,
since `T_d` is `Q1`'s own direct middle slot, no `TowerColumn`/`B_L`
level involved. -/
theorem dEmbed
    (t₀ : (quadSource (K := K) a b c d).carrier) (t : (stdTower (K := K) d).carrier)
    (ht₀ : t₀ = GradedTensorProduct.includeRight
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (stdTower (K := K) d).grading t)
    (z : Q1 K a b c d) :
    t₀ • z = t • z := by
  rw [gtensorABCD_smul_def, ht₀, gtensorLeftActionHom_includeRight, ← dslot_apply]

end Q1

/-! ### (c) The interface, `⊇` direction: the four slot conditions

`Q1_quadEnv_smul_def`/`Q4_quadEnv_smul_def` unfold the `QuadEnv`-module
`•` on each vertex to `actionHom`, matching (b)'s
`actionHom_includeLeft_apply`; combined with the slot-embedding bridges
above and `Superfusion.includeLeft_mem_tensorGrading`/
`includeRight_mem_tensorGrading` (chained through the (at most) four
levels of `quadSource`'s own bracket, M7f-1a), a `QuadEnv`-super
-equivariant `f : Q1 → Q4` of degree `e`, evaluated at the envelope
element obtained by embedding a homogeneous slot generator through the
matching `includeLeft`/`includeRight` chain, is exactly `f`'s
super-equivariance for that slot's own action — the four conditions of
`quadInterSpace` beyond `homGrading` (which matches verbatim, since
`gradedHomF`'s and `quadInterSpace`'s `homGrading` component share the
same descended gradings `Q1.grading`/`Q4.grading`) and
`rightSemilinear` (not landed this round — see the session report: the
sop generator `1 ᵍ⊗ (op τ)`'s envelope action is `rightActionHom`,
Koszul-*signed* via `signedRSMul`, while `quadInterSpace`'s
`rightSemilinear` is the *unsigned* native right action; reconciling
the two needs the sign to cancel against `f`'s own degree-`e`
homogeneity, a genuine further argument not attempted here). -/

theorem Q1_quadEnv_smul_def (w : QuadEnv K a b c d) (m : Q1 K a b c d) :
    w • m = actionHom (quadSource (K := K) a b c d).grading
      (stdTower (K := K) (a + b + c + d)).grading (Q1.grading K a b c d) w m := rfl

theorem Q4_quadEnv_smul_def (w : QuadEnv K a b c d) (m : Q4 K a b c d) :
    w • m = actionHom (quadSource (K := K) a b c d).grading
      (stdTower (K := K) (a + b + c + d)).grading (Q4.grading K a b c d) w m := rfl

variable {K a b c d}

/-- **The `⊇` direction, `a`-slot**: a `QuadEnv`-super-equivariant `f`
of degree `e` is super-equivariant for the `a`-slot action, of the same
degree. -/
theorem superEquivariant_a_of_quadEnv {e : ZMod 2} (f : Q1 K a b c d →ₗ[K] Q4 K a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : QuadEnv K a b c d⦄,
      w ∈ quadEnvGrading K a b c d i → ∀ m : Q1 K a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) a).carrier⦄, x ∈ (stdTower (K := K) a).grading i →
      ∀ m : Q1 K a b c d, f (x • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • f m) := by
  intro i x hx m
  have hx0mem := Superfusion.includeLeft_mem_tensorGrading (stdTower (K := K) a).grading
    (stdTower (K := K) b).grading hx
  have hx1mem := Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading hx0mem
  set x₂ : (quadSource (K := K) a b c d).carrier :=
    GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading (stdTower (K := K) b).grading x))
    with hx2def
  have hx2mem : x₂ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading i := by
    rw [hx2def]
    exact Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading hx1mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      (quadSource (K := K) a b c d).grading
      (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) hx2mem
  have key := hequiv hwmem m
  rw [Q1_quadEnv_smul_def, actionHom_includeLeft_apply,
    Q1.aEmbed K a b c d
      (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading (stdTower (K := K) b).grading x)
      x rfl
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading (stdTower (K := K) b).grading x))
      rfl x₂ hx2def] at key
  rw [key, Q4_quadEnv_smul_def, actionHom_includeLeft_apply,
    Q4.aEmbed_smul K a b c d
      (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading (stdTower (K := K) b).grading x)
      x rfl
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading (stdTower (K := K) b).grading x))
      rfl x₂ hx2def]

/-- **The `⊇` direction, `b`-slot**. -/
theorem superEquivariant_b_of_quadEnv {e : ZMod 2} (f : Q1 K a b c d →ₗ[K] Q4 K a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : QuadEnv K a b c d⦄,
      w ∈ quadEnvGrading K a b c d i → ∀ m : Q1 K a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) b).carrier⦄, y ∈ (stdTower (K := K) b).grading i →
      ∀ m : Q1 K a b c d, f (y • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • f m) := by
  intro i y hy m
  have hy0mem := Superfusion.includeRight_mem_tensorGrading (stdTower (K := K) a).grading
    (stdTower (K := K) b).grading hy
  have hy1mem := Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading hy0mem
  set y₂ : (quadSource (K := K) a b c d).carrier :=
    GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeRight (stdTower (K := K) a).grading (stdTower (K := K) b).grading y))
    with hy2def
  have hy2mem : y₂ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading i := by
    rw [hy2def]
    exact Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading hy1mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      (quadSource (K := K) a b c d).grading
      (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) hy2mem
  have key := hequiv hwmem m
  rw [Q1_quadEnv_smul_def, actionHom_includeLeft_apply,
    Q1.bEmbed K a b c d
      (GradedTensorProduct.includeRight (stdTower (K := K) a).grading (stdTower (K := K) b).grading y)
      y rfl
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeRight (stdTower (K := K) a).grading (stdTower (K := K) b).grading y))
      rfl y₂ hy2def] at key
  rw [key, Q4_quadEnv_smul_def, actionHom_includeLeft_apply,
    Q4.bEmbed_smul K a b c d
      (GradedTensorProduct.includeRight (stdTower (K := K) a).grading (stdTower (K := K) b).grading y)
      y rfl
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeRight (stdTower (K := K) a).grading (stdTower (K := K) b).grading y))
      rfl y₂ hy2def]

/-- **The `⊇` direction, `c`-slot**. -/
theorem superEquivariant_c_of_quadEnv {e : ZMod 2} (f : Q1 K a b c d →ₗ[K] Q4 K a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : QuadEnv K a b c d⦄,
      w ∈ quadEnvGrading K a b c d i → ∀ m : Q1 K a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃w' : (stdTower (K := K) c).carrier⦄, w' ∈ (stdTower (K := K) c).grading i →
      ∀ m : Q1 K a b c d, f (w' • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w' • f m) := by
  intro i w' hw' m
  have hw0mem := Superfusion.includeRight_mem_tensorGrading
      (Superfusion.tensorGrading (stdTower (K := K) a).grading (stdTower (K := K) b).grading)
      (stdTower (K := K) c).grading hw'
  set w₁ : (quadSource (K := K) a b c d).carrier :=
    GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading
      (GradedTensorProduct.includeRight (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading w')
    with hw1def
  have hw1mem : w₁ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading i := by
    rw [hw1def]
    exact Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading hw0mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      (quadSource (K := K) a b c d).grading
      (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) hw1mem
  have key := hequiv hwmem m
  rw [Q1_quadEnv_smul_def, actionHom_includeLeft_apply,
    Q1.cEmbed K a b c d
      (GradedTensorProduct.includeRight (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading w')
      w' rfl w₁ hw1def] at key
  rw [key, Q4_quadEnv_smul_def, actionHom_includeLeft_apply,
    Q4.cEmbed_smul K a b c d
      (GradedTensorProduct.includeRight (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading w')
      w' rfl w₁ hw1def]

/-- **The `⊇` direction, `d`-slot** — a single (`Q1`/`Q4`-level)
collapse, since `T_d` is `quadSource`'s own outermost right factor. -/
theorem superEquivariant_d_of_quadEnv {e : ZMod 2} (f : Q1 K a b c d →ₗ[K] Q4 K a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : QuadEnv K a b c d⦄,
      w ∈ quadEnvGrading K a b c d i → ∀ m : Q1 K a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃t : (stdTower (K := K) d).carrier⦄, t ∈ (stdTower (K := K) d).grading i →
      ∀ m : Q1 K a b c d, f (t • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (t • f m) := by
  intro i t ht m
  set t₀ : (quadSource (K := K) a b c d).carrier :=
    GradedTensorProduct.includeRight
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading t
    with ht0def
  have ht0mem : t₀ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading i := by
    rw [ht0def]
    exact Superfusion.includeRight_mem_tensorGrading
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading ht
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      (quadSource (K := K) a b c d).grading
      (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) ht0mem
  have key := hequiv hwmem m
  rw [Q1_quadEnv_smul_def, actionHom_includeLeft_apply, Q1.dEmbed K a b c d t₀ t ht0def] at key
  rw [key, Q4_quadEnv_smul_def, actionHom_includeLeft_apply, Q4.dEmbed_smul K a b c d t₀ t ht0def]

/-- **The `⊇` direction, assembled**: a `f ∈ gradedHomF` (i.e.
`QuadEnv`-homogeneous of degree `e` and `QuadEnv`-super-equivariant of
degree `e`) satisfies `quadInterSpace`'s five non-`rightSemilinear`
conditions — `homGrading` (verbatim, same descended gradings) and the
four slot super-equivariances (`superEquivariant_a_of_quadEnv`–
`_d_of_quadEnv`).  `rightSemilinear` is not established this round
(see the design note above `Q1_quadEnv_smul_def`), so this is *not*
literally `f ∈ quadInterSpace K a b c d e` — the last piece of the `⊇`
direction of `mem_quadInterSpace_iff_gradedHomF`. -/
theorem quadInterSpace_five_conditions_of_mem_gradedHomF {e : ZMod 2}
    {f : Q1 K a b c d →ₗ[K] Q4 K a b c d}
    (hf : f ∈ gradedHomF (Q1.grading K a b c d) (quadEnvGrading K a b c d) (Q4.grading K a b c d) e) :
    f ∈ homGrading (Q1.grading K a b c d) (Q4.grading K a b c d) e
      ∧ f ∈ superEquivariant (stdTower (K := K) a).grading e
      ∧ f ∈ superEquivariant (stdTower (K := K) b).grading e
      ∧ f ∈ superEquivariant (stdTower (K := K) c).grading e
      ∧ f ∈ superEquivariant (stdTower (K := K) d).grading e := by
  rw [mem_gradedHomF_iff] at hf
  obtain ⟨hgrad, hequiv⟩ := hf
  rw [mem_superEquivariant] at hequiv
  exact ⟨hgrad, superEquivariant_a_of_quadEnv f hequiv, superEquivariant_b_of_quadEnv f hequiv,
    superEquivariant_c_of_quadEnv f hequiv, superEquivariant_d_of_quadEnv f hequiv⟩

end PentagonB

end Bimod

end Superfusion

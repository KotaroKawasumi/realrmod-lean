/-
Superfusion / Bimod / QuadInterface2

Milestone M8a-8d′-iii-a‴ (roadmap v3): **completing the interface** —
`mem_quadInterSpace_iff_gradedHomF`, finishing what `QuadInterface.lean`
left open (the sixth `rightSemilinear` condition of the `⊇` direction,
and the whole `⊆` direction).  Two general-layer resolutions:

(A) *Right-sign reconciliation* (`rightActionHom_equivariant_iff_of_mem`
    / `_iff_rightSemilinear`): the envelope's sop-generator action is
    SIGNED (`rightActionHom`/`signedRSMul`, `Basic.lean`), while
    `quadInterSpace`'s `rightSemilinear` is UNSIGNED.  For `f`
    homogeneous of degree `e`, at a homogeneous point `m ∈ ℳ i`
    (so `f m ∈ 𝒩 (i + e)`), the two Koszul signs of
    `signedRSMul_of_mem` (`sgn (j * i)` and `sgn (j * (i + e))`,
    `τ ∈ ℬ j`) combine with the equivariance sign `sgn (e * j)` to
    `sgn (j * i)` again (`e·j + j·(i+e) = j·i`, `decide`), so the
    Koszul sign present on BOTH sides cancels completely, leaving the
    two conditions equivalent.  Extended from a homogeneous point `m`
    to arbitrary `m` by `DirectSum.Decomposition.inductionOn`
    (linearity of every term in `m`).

(B) *Multiplicative and additive closure* (`superEquivariantAt_mul` /
    `superEquivariantAt_of_includeLeft_includeRight`): the
    `HomGrading.superEquivariant` sign convention is closed under
    products of homogeneous acting elements (`mul_smul` plus the sign
    identity `e·j₁ + e·j₂ = e·(j₁ + j₂)`) and under `K`-linear
    combinations within a FIXED degree (`smul_assoc`/`smul_comm`
    against a fixed `[IsScalarTower K T M] [IsScalarTower K T N]`).
    Combined with `tensorGrading_induction`'s "every homogeneous
    element is a `K`-linear combination of pure tensors" and the
    identity `x ᵍ⊗ₜ y = includeLeft x * includeRight y`
    (`GradedTensorProduct.tmul_one_mul_one_tmul`), equivariance at the
    two INCLUDED families (`includeLeft x`/`includeRight y`, for EVERY
    homogeneous `x`/`y`, not merely spelled generators) propagates to
    equivariance at EVERY element of `tensorGrading 𝒜 ℬ i`.  Applied
    four times — `quadSource`'s own three internal levels
    (`(A,B)`, `(AB,C)`, `(ABC,D)`, all landing at `T := quadSource.carrier`)
    then the outer sop-tensor split (`T := QuadEnv K a b c d`) — chained
    through `Q1.aEmbed`–`Q1.dEmbed`/`Q4.aEmbed_smul`–`Q4.dEmbed_smul`
    (`QuadInterface.lean`/`QuadEnvModule2.lean`) at the base cases, it
    builds `QuadEnv`-super-equivariance (the `⊆` direction's missing
    piece) from the six `quadInterSpace` conditions with NO further
    per-generator induction.

Deliverable: `mem_quadInterSpace_iff_gradedHomF`.  The dimension
arithmetic + discharge (M8a-8d′-iii-b) is deferred.
-/
import Superfusion.Bimod.QuadInterface

namespace Superfusion

namespace Bimod

open scoped TensorProduct

/-! ### (A) General layer: reconciling the signed sop-generator action
with the unsigned `rightSemilinear` condition -/

section RightGeneratorReconciliation

variable {K : Type*} [CommRing K]
variable {B : Type*} [Ring B] [Algebra K B]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [Module Bᵐᵒᵖ M] [IsScalarTower K Bᵐᵒᵖ M] [GradedRightSMul ℬ ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]
variable [Module Bᵐᵒᵖ N] [IsScalarTower K Bᵐᵒᵖ N] [GradedRightSMul ℬ 𝒩]

/-- The ZMod 2 sign identity behind the reconciliation:
`e·j + j·(i + e) = j·i`. -/
private theorem sgn_rightGenerator_cancel :
    ∀ e i j : ZMod 2, e * j + j * (i + e) = j * i := by decide

/-- Cancelling a `sgn`-scalar from both sides of an equation (the sign
squares to `1`). -/
private theorem sgn_smul_cancel {X : Type*} [AddCommGroup X] (n : ZMod 2) {x y : X}
    (h : ((sgn n : ℤˣ) : ℤ) • x = ((sgn n : ℤˣ) : ℤ) • y) : x = y := by
  have h2 : ((sgn n : ℤˣ) : ℤ) • (((sgn n : ℤˣ) : ℤ) • x)
      = ((sgn n : ℤˣ) : ℤ) • (((sgn n : ℤˣ) : ℤ) • y) := by rw [h]
  simpa only [smul_smul, ← Units.val_mul, sgn_mul_self', Units.val_one, one_smul] using h2

/-- **(A), homogeneous point**: for `f` homogeneous of degree `e`, a
homogeneous coefficient `τ ∈ ℬ j`, and a homogeneous point `m ∈ ℳ i`,
the SIGNED sop-generator equivariance
`f (rightActionHom (op τ) m) = sgn(e·j) • rightActionHom (op τ) (f m)`
is equivalent to the UNSIGNED `f (op τ • m) = op τ • f m` — the Koszul
sign of `signedRSMul_of_mem`, present on both sides once `m`'s and
`f m`'s own degrees (`i` and `i + e`) are substituted, cancels
completely (`sgn_rightGenerator_cancel`). -/
theorem rightActionHom_equivariant_iff_of_mem {i e j : ZMod 2}
    {f : M →ₗ[K] N} (hf : f ∈ homGrading ℳ 𝒩 e)
    {τ : B} (hτ : τ ∈ ℬ j) {m : M} (hm : m ∈ ℳ i) :
    f (rightActionHom ℬ ℳ (SuperOp.op ℬ τ) m)
        = ((sgn (e * j) : ℤˣ) : ℤ) • rightActionHom ℬ 𝒩 (SuperOp.op ℬ τ) (f m)
      ↔ f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
  have hfm : f m ∈ 𝒩 (i + e) := hf i m hm
  simp only [rightActionHom_apply, SuperOp.unop_op, signedRSMul_of_mem ℬ ℳ hτ hm,
    signedRSMul_of_mem ℬ 𝒩 hτ hfm, map_zsmul, smul_smul]
  have hs : ((sgn (j * i) : ℤˣ) : ℤ)
      = ((sgn (e * j) : ℤˣ) : ℤ) * ((sgn (j * (i + e)) : ℤˣ) : ℤ) := by
    rw [← sgn_rightGenerator_cancel e i j, sgn_add, Units.val_mul]
  rw [← hs]
  exact ⟨sgn_smul_cancel (j * i), fun h => by rw [h]⟩

/-- **(A), assembled**: sop-generator super-equivariance of a
degree-`e`-homogeneous `f` at a FIXED homogeneous `τ ∈ ℬ j`, over ALL
`m : M` (not merely homogeneous — extended from the pointwise fact
above by `DirectSum.Decomposition.inductionOn`, since every term is
`K`-linear in `m`), is equivalent to the unsigned `rightSemilinear`
-style condition at that same `τ`. -/
theorem rightActionHom_equivariant_iff_rightSemilinear {e j : ZMod 2}
    {f : M →ₗ[K] N} (hf : f ∈ homGrading ℳ 𝒩 e) {τ : B} (hτ : τ ∈ ℬ j) :
    (∀ m : M, f (rightActionHom ℬ ℳ (SuperOp.op ℬ τ) m)
        = ((sgn (e * j) : ℤˣ) : ℤ) • rightActionHom ℬ 𝒩 (SuperOp.op ℬ τ) (f m))
      ↔ ∀ m : M, f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
  constructor
  · intro hyp m
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | homogeneous m' =>
        exact (rightActionHom_equivariant_iff_of_mem ℬ ℳ 𝒩 hf hτ m'.2).mp (hyp m')
    | add m1 m2 h1 h2 => simp only [smul_add, map_add]; rw [h1, h2]
  · intro hyp m
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | homogeneous m' =>
        exact (rightActionHom_equivariant_iff_of_mem ℬ ℳ 𝒩 hf hτ m'.2).mpr (hyp m')
    | add m1 m2 h1 h2 => simp only [map_add, smul_add]; rw [h1, h2]

end RightGeneratorReconciliation

/-! ### (B) General layer: multiplicative and additive closure of
super-equivariance -/

section EquivariantClosure

variable {K : Type*} [CommRing K]

/-- **Product closure**: if `f` is equivariant (`HomGrading.superEquivariant`'s
sign convention, degree `e`) at two ring elements `w₁ ∈ 𝒯 j₁`/`w₂ ∈ 𝒯 j₂`
of a `[Module T M] [Module T N]` pair, it is equivariant at
`w₁ * w₂`, of degree `j₁ + j₂` (`mul_smul` plus the sign identity
`e·j₁ + e·j₂ = e·(j₁ + j₂)`). -/
theorem superEquivariantAt_mul {T M N : Type*} [Ring T]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [Module T M] [Module T N]
    {f : M →ₗ[K] N} {e j₁ j₂ : ZMod 2} {w₁ w₂ : T}
    (h1 : ∀ m : M, f (w₁ • m) = ((sgn (e * j₁) : ℤˣ) : ℤ) • (w₁ • f m))
    (h2 : ∀ m : M, f (w₂ • m) = ((sgn (e * j₂) : ℤˣ) : ℤ) • (w₂ • f m)) :
    ∀ m : M, f ((w₁ * w₂) • m)
      = ((sgn (e * (j₁ + j₂)) : ℤˣ) : ℤ) • ((w₁ * w₂) • f m) := by
  intro m
  calc f ((w₁ * w₂) • m) = f (w₁ • (w₂ • m)) := by rw [mul_smul]
    _ = ((sgn (e * j₁) : ℤˣ) : ℤ) • (w₁ • f (w₂ • m)) := h1 (w₂ • m)
    _ = ((sgn (e * j₁) : ℤˣ) : ℤ) •
          (w₁ • (((sgn (e * j₂) : ℤˣ) : ℤ) • (w₂ • f m))) := by rw [h2 m]
    _ = ((sgn (e * j₁) : ℤˣ) : ℤ) •
          (((sgn (e * j₂) : ℤˣ) : ℤ) • (w₁ • (w₂ • f m))) := by rw [smul_comm w₁]
    _ = (((sgn (e * j₁) : ℤˣ) : ℤ) * ((sgn (e * j₂) : ℤˣ) : ℤ)) • (w₁ • (w₂ • f m)) := by
        rw [smul_smul]
    _ = ((sgn (e * j₁ + e * j₂) : ℤˣ) : ℤ) • (w₁ • (w₂ • f m)) := by
        rw [← Units.val_mul, ← sgn_add]
    _ = ((sgn (e * (j₁ + j₂)) : ℤˣ) : ℤ) • (w₁ • (w₂ • f m)) := by rw [mul_add]
    _ = ((sgn (e * (j₁ + j₂)) : ℤˣ) : ℤ) • ((w₁ * w₂) • f m) := by rw [mul_smul]

/-- **The tmul-to-product identity**: the pure-tensor generator of a
graded tensor product is the product of its `includeLeft`/`includeRight`
embeds (`GradedTensorProduct.tmul_one_mul_one_tmul`, restated at the
`ᵍ⊗ₜ` spelling the closure lemma below needs). -/
private theorem tmul_eq_includeLeft_mul_includeRight
    {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ℬ : ZMod 2 → Submodule K B)
    [GradedAlgebra ℬ] (x : A) (y : B) :
    (x ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] ℬ)
      = GradedTensorProduct.includeLeft 𝒜 ℬ x * GradedTensorProduct.includeRight 𝒜 ℬ y := by
  show x ᵍ⊗ₜ[K] y = (x ᵍ⊗ₜ[K] (1 : B)) * ((1 : A) ᵍ⊗ₜ[K] y)
  rw [GradedTensorProduct.tmul_one_mul_one_tmul]

/-- **(B), assembled**: super-equivariance at the two `includeLeft`/
`includeRight` families (`hL`/`hR`, at EVERY homogeneous generator, not
merely spelled elements) extends, via `tensorGrading_induction`'s
"homogeneous element = `K`-linear combination of pure tensors" and the
product closure above, to super-equivariance at EVERY element of
`Superfusion.tensorGrading 𝒜 ℬ i`, for a FIXED ambient action
`[Module T M] [Module T N]` and an algebra embedding
`ι : 𝒜 ᵍ⊗[K] ℬ →ₐ[K] T`. -/
theorem superEquivariantAt_of_includeLeft_includeRight
    {A B T M N : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B] [Ring T] [Algebra K T]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
    (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [Module T M] [Module T N] [IsScalarTower K T M] [IsScalarTower K T N]
    (ι : (𝒜 ᵍ⊗[K] ℬ) →ₐ[K] T)
    {f : M →ₗ[K] N} {e : ZMod 2}
    (hL : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j → ∀ m : M,
      f (ι (GradedTensorProduct.includeLeft 𝒜 ℬ x) • m)
        = ((sgn (e * j) : ℤˣ) : ℤ) • (ι (GradedTensorProduct.includeLeft 𝒜 ℬ x) • f m))
    (hR : ∀ ⦃k : ZMod 2⦄ ⦃y : B⦄, y ∈ ℬ k → ∀ m : M,
      f (ι (GradedTensorProduct.includeRight 𝒜 ℬ y) • m)
        = ((sgn (e * k) : ℤˣ) : ℤ) • (ι (GradedTensorProduct.includeRight 𝒜 ℬ y) • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃w : 𝒜 ᵍ⊗[K] ℬ⦄, w ∈ Superfusion.tensorGrading 𝒜 ℬ i → ∀ m : M,
    f (ι w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (ι w • f m) := by
  intro i w hw m
  refine Superfusion.tensorGrading_induction 𝒜 ℬ
    (p := fun w' => ∀ m : M, f (ι w' • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (ι w' • f m))
    hw ?_ ?_ ?_ ?_ m
  · intro j k x y hjk hx hy m
    rw [tmul_eq_includeLeft_mul_includeRight 𝒜 ℬ x y, map_mul]
    have h := superEquivariantAt_mul (hL hx) (hR hy) m
    rwa [hjk] at h
  · intro m; simp
  · intro w1 w2 h1 h2 m
    simp only [map_add, add_smul, smul_add]
    rw [h1 m, h2 m]
  · intro c w1 h1 m
    simp only [map_smul, smul_assoc]
    rw [h1 m]
    exact smul_comm c _ _

end EquivariantClosure

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-! ### `K` is a scalar tower for `QuadEnv K a b c d` on `Q1`/`Q4`

Needed as the `[IsScalarTower K T M] [IsScalarTower K T N]` hypothesis
of `superEquivariantAt_of_includeLeft_includeRight` at the OUTER
(sop-tensor) level — `actionHom` is an `AlgHom`, hence `K`-linear, so
the `QuadEnv`-action it generates (`Q1_quadEnv_smul_def`/
`Q4_quadEnv_smul_def`) is automatically compatible with `K`-scalars. -/

instance : IsScalarTower K (QuadEnv K a b c d) (Q1 K a b c d) :=
  ⟨fun c w m => by simp only [Q1_quadEnv_smul_def, map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (QuadEnv K a b c d) (Q4 K a b c d) :=
  ⟨fun c w m => by simp only [Q4_quadEnv_smul_def, map_smul, LinearMap.smul_apply]⟩

/-! ### (A), instantiated: the sixth `quadInterSpace` condition -/

/-- The associativity recast between `Q1`'s outer right-coefficient
tower `T_{((a+b)+c)+d}` and `Q4`'s `T_{a+(b+c+d)}` — reproved locally
since `QuadInterSpace.lean`'s `quadRightCast_eq` is `private` (any two
proofs of the same equality are interchangeable, by proof
irrelevance). -/
private theorem quadRightCast_eq2 : a + b + c + d = a + (b + c + d) := by ring

/-- **The `⊇` direction, sixth condition**: a `QuadEnv`-super-equivariant
`f` of degree `e` satisfies `quadInterSpace`'s `rightSemilinear`
condition — the sop-generator instance of `hequiv`, converted via (A)'s
reconciliation (`rightActionHom_equivariant_iff_rightSemilinear`) at
each homogeneous `τ`, then extended to an arbitrary `t` by
`DirectSum.Decomposition.inductionOn` (linearity in `t`). -/
theorem rightSemilinear_of_quadEnv {e : ZMod 2} {f : Q1 K a b c d →ₗ[K] Q4 K a b c d}
    (hgrad : f ∈ homGrading (Q1.grading K a b c d) (Q4.grading K a b c d) e)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : QuadEnv K a b c d⦄,
      w ∈ quadEnvGrading K a b c d i → ∀ m : Q1 K a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    f ∈ rightSemilinear
        ((stdTowerCast (K := K) (quadRightCast_eq2 a b c d)).toAlgEquiv.toAlgHom.toRingHom) := by
  have hsop : ∀ ⦃j : ZMod 2⦄ ⦃τ : (stdTower (K := K) (a + b + c + d)).carrier⦄,
      τ ∈ (stdTower (K := K) (a + b + c + d)).grading j → ∀ m : Q1 K a b c d,
        f (rightActionHom (stdTower (K := K) (a + b + c + d)).grading (Q1.grading K a b c d)
            (SuperOp.op _ τ) m)
          = ((sgn (e * j) : ℤˣ) : ℤ) •
              rightActionHom (stdTower (K := K) (a + b + c + d)).grading (Q4.grading K a b c d)
                (SuperOp.op _ τ) (f m) := by
    intro j τ hτ m
    have hmem := Superfusion.includeRight_mem_tensorGrading (quadSource (K := K) a b c d).grading
      (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) hτ
    have key := hequiv hmem m
    rwa [Q1_quadEnv_smul_def, actionHom_includeRight_apply, Q4_quadEnv_smul_def,
      actionHom_includeRight_apply] at key
  have hunsigned : ∀ ⦃j : ZMod 2⦄ ⦃τ : (stdTower (K := K) (a + b + c + d)).carrier⦄,
      τ ∈ (stdTower (K := K) (a + b + c + d)).grading j → ∀ m : Q1 K a b c d,
        f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
    intro j τ hτ m
    exact (rightActionHom_equivariant_iff_rightSemilinear (stdTower (K := K) (a + b + c + d)).grading
      (Q1.grading K a b c d) (Q4.grading K a b c d) hgrad hτ).mp (hsop hτ) m
  rw [mem_rightSemilinear]
  intro t m
  show f (MulOpposite.op t • m)
    = MulOpposite.op ((stdTowerCast (K := K) (quadRightCast_eq2 a b c d)).toAlgEquiv t) • f m
  induction t using DirectSum.Decomposition.inductionOn (stdTower (K := K) (a + b + c + d)).grading with
  | zero => simp [map_zero, MulOpposite.op_zero, zero_smul]
  | homogeneous t' => exact hunsigned t'.2 m
  | add t1 t2 h1 h2 => simp only [MulOpposite.op_add, add_smul, map_add]; rw [h1, h2]

/-- **The `⊇` direction, assembled**: a `f ∈ gradedHomF` (i.e.
`QuadEnv`-homogeneous and `QuadEnv`-super-equivariant of degree `e`)
satisfies all six of `quadInterSpace`'s conditions. -/
theorem quadInterSpace_of_mem_gradedHomF {e : ZMod 2} {f : Q1 K a b c d →ₗ[K] Q4 K a b c d}
    (hf : f ∈ gradedHomF (Q1.grading K a b c d) (quadEnvGrading K a b c d) (Q4.grading K a b c d) e) :
    f ∈ quadInterSpace K a b c d e := by
  obtain ⟨hgrad, ha, hb, hc, hd⟩ := quadInterSpace_five_conditions_of_mem_gradedHomF hf
  rw [mem_gradedHomF_iff] at hf
  obtain ⟨_, hequiv⟩ := hf
  rw [mem_superEquivariant] at hequiv
  rw [mem_quadInterSpace_iff]
  exact ⟨hgrad, ha, hb, hc, hd, rightSemilinear_of_quadEnv K a b c d hgrad hequiv⟩

/-! ### (B), instantiated: `quadSource`'s three internal levels

Everything below uses the BUNDLED `.gtensor.grading`/`.gtensor.carrier`
spelling throughout — matching `Q1.aEmbed`–`Q1.dEmbed`'s own spelling
verbatim, and matching `quadSource`'s own definition (`(((T_a.gtensor
T_b).gtensor T_c).gtensor T_d)`) so that `T := (quadSource …).carrier`
(the ONLY spelling carrying `Q1`/`Q4`'s registered `Module`/
`IsScalarTower` instances) unifies against `𝒜 ᵍ⊗[K] ℬ` without an
instance mismatch (the M8a-8d′-iii-a′ lesson: mixing the bundled and
`Superfusion.tensorGrading`-unfolded spellings defeats typeclass
search, even though they are `rfl`-equal elementwise).
`Q4.aEmbed_smul`–`Q4.dEmbed_smul` (`QuadEnvModule2.lean`), by contrast,
are stated at the UNFOLDED spelling, so each is bridged to the bundled
one below (`Q4_aEmbed_bundled`–`Q4_dEmbed_bundled`) by a single
elementwise `rfl`. -/

private theorem Q4_aEmbed_bundled
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
    (z : Q4 K a b c d) :
    x₂ • z = x • z := by
  have hcol : x₂ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading (stdTower (K := K) b).grading x)) := by
    rw [hx₂, hx₁, hx₀]; rfl
  rw [hcol]
  exact Q4.aEmbed_smul K a b c d _ x rfl _ rfl _ rfl z

private theorem Q4_bEmbed_bundled
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
    (z : Q4 K a b c d) :
    y₂ • z = y • z := by
  have hcol : y₂ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading
      (GradedTensorProduct.includeLeft (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading
        (GradedTensorProduct.includeRight (stdTower (K := K) a).grading (stdTower (K := K) b).grading y)) := by
    rw [hy₂, hy₁, hy₀]; rfl
  rw [hcol]
  exact Q4.bEmbed_smul K a b c d _ y rfl _ rfl _ rfl z

private theorem Q4_cEmbed_bundled
    (w₀ : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).carrier)
    (w' : (stdTower (K := K) c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight ((stdTower (K := K) a).gtensor (stdTower b)).grading
        (stdTower (K := K) c).grading w')
    (w₁ : (quadSource (K := K) a b c d).carrier)
    (hw₁ : w₁ = GradedTensorProduct.includeLeft
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (stdTower (K := K) d).grading w₀)
    (z : Q4 K a b c d) :
    w₁ • z = w' • z := by
  have hcol : w₁ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading
      (GradedTensorProduct.includeRight (Superfusion.tensorGrading (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading) (stdTower (K := K) c).grading w') := by
    rw [hw₁, hw₀]; rfl
  rw [hcol]
  exact Q4.cEmbed_smul K a b c d _ w' rfl _ rfl z

private theorem Q4_dEmbed_bundled
    (t₀ : (quadSource (K := K) a b c d).carrier) (t : (stdTower (K := K) d).carrier)
    (ht₀ : t₀ = GradedTensorProduct.includeRight
        (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
        (stdTower (K := K) d).grading t)
    (z : Q4 K a b c d) :
    t₀ • z = t • z := by
  have hcol : t₀ = GradedTensorProduct.includeRight
      (Superfusion.tensorGrading (Superfusion.tensorGrading (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading) (stdTower (K := K) c).grading)
      (stdTower (K := K) d).grading t := by
    rw [ht₀]; rfl
  rw [hcol]
  exact Q4.dEmbed_smul K a b c d _ t rfl z

/-- The `(A,B) → (AB,C) → (ABC,D) = quadSource` embed, as a single
`AlgHom` (needed so `superEquivariantAt_of_includeLeft_includeRight`'s
`map_mul`/`map_add`/`map_smul` machinery applies to it directly). -/
private noncomputable def ιAB :
    ((stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading) →ₐ[K]
      (quadSource (K := K) a b c d).carrier :=
  (GradedTensorProduct.includeLeft
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
      (stdTower (K := K) d).grading).comp
    (GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
      (stdTower (K := K) c).grading)

/-- The `(AB,C) → (ABC,D) = quadSource` embed. -/
private noncomputable def ιABC :
    (((stdTower (K := K) a).gtensor (stdTower b)).grading ᵍ⊗[K] (stdTower (K := K) c).grading) →ₐ[K]
      (quadSource (K := K) a b c d).carrier :=
  GradedTensorProduct.includeLeft
    (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
    (stdTower (K := K) d).grading

/-- The identity, re-typed from the RAW `ABC.grading ᵍ⊗ D.grading` (whose
`Ring`/`Algebra` instances come from `GradedTensorProduct.instRing`/
`instAlgebra`, freshly synthesized against `[GradedAlgebra …]`) to
`quadSource.carrier` (whose `Ring`/`Algebra` instances come from
`SuperAlgebra.gtensor`'s own bundled fields) — the two instances are
`rfl`-equal (both ultimately reduce to the same `GradedTensorProduct`
construction) but NOT `instances`-transparently equal, so `AlgHom.id`
itself does not typecheck against the mismatched instance packaging;
built by hand instead, with `rfl` proofs for every field. -/
private noncomputable def ιABCD :
    ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading ᵍ⊗[K]
        (stdTower (K := K) d).grading) →ₐ[K]
      (quadSource (K := K) a b c d).carrier where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {K a b c d}

/-- **The `⊆` direction, `quadSource`-level equivariance**: the four
slot super-equivariances assemble, via `superEquivariantAt_of_includeLeft_includeRight`
applied at `quadSource`'s own three internal levels (`(A,B)`, `(AB,C)`,
`(ABC,D)`, all landing at `T := quadSource.carrier`), chained through
`Q1.aEmbed`–`Q1.dEmbed`/`Q4_aEmbed_bundled`–`Q4_dEmbed_bundled`, into
super-equivariance for `quadSource`'s OWN action on `Q1`/`Q4`, at EVERY
homogeneous element (not merely generators). -/
theorem quadSource_equivariant_of_slots {e : ZMod 2} {f : Q1 K a b c d →ₗ[K] Q4 K a b c d}
    (ha : f ∈ superEquivariant (stdTower (K := K) a).grading e)
    (hb : f ∈ superEquivariant (stdTower (K := K) b).grading e)
    (hc : f ∈ superEquivariant (stdTower (K := K) c).grading e)
    (hd : f ∈ superEquivariant (stdTower (K := K) d).grading e) :
    ∀ ⦃i : ZMod 2⦄ ⦃w : (quadSource (K := K) a b c d).carrier⦄,
      w ∈ (quadSource (K := K) a b c d).grading i → ∀ m : Q1 K a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m) := by
  rw [mem_superEquivariant] at ha hb hc hd
  have hAB := superEquivariantAt_of_includeLeft_includeRight
      (stdTower (K := K) a).grading (stdTower (K := K) b).grading (ιAB K a b c d)
      (f := f) (e := e)
      (fun j x hx m => by
        have hcol : ιAB K a b c d
            (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
              (stdTower (K := K) b).grading x)
          = GradedTensorProduct.includeLeft
              (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
              (stdTower (K := K) d).grading
              (GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
                  (stdTower (K := K) c).grading
                (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
                  (stdTower (K := K) b).grading x)) :=
          rfl
        rw [hcol, Q1.aEmbed K a b c d _ x rfl _ rfl _ rfl,
          Q4_aEmbed_bundled K a b c d _ x rfl _ rfl _ rfl]
        exact ha hx m)
      (fun k y hy m => by
        have hcol : ιAB K a b c d
            (GradedTensorProduct.includeRight (stdTower (K := K) a).grading
              (stdTower (K := K) b).grading y)
          = GradedTensorProduct.includeLeft
              (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
              (stdTower (K := K) d).grading
              (GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
                  (stdTower (K := K) c).grading
                (GradedTensorProduct.includeRight (stdTower (K := K) a).grading
                  (stdTower (K := K) b).grading y)) :=
          rfl
        rw [hcol, Q1.bEmbed K a b c d _ y rfl _ rfl _ rfl,
          Q4_bEmbed_bundled K a b c d _ y rfl _ rfl _ rfl]
        exact hb hy m)
  have hABC := superEquivariantAt_of_includeLeft_includeRight
      ((stdTower (K := K) a).gtensor (stdTower b)).grading (stdTower (K := K) c).grading
      (ιABC K a b c d) (f := f) (e := e)
      (fun j w hw m => by
        have hcol : ιABC K a b c d
            (GradedTensorProduct.includeLeft ((stdTower (K := K) a).gtensor (stdTower b)).grading
              (stdTower (K := K) c).grading w)
          = ιAB K a b c d w := rfl
        rw [hcol]
        exact hAB hw m)
      (fun k w' hw' m => by
        have hcol : ιABC K a b c d
            (GradedTensorProduct.includeRight ((stdTower (K := K) a).gtensor (stdTower b)).grading
              (stdTower (K := K) c).grading w')
          = GradedTensorProduct.includeLeft
              (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
              (stdTower (K := K) d).grading
              (GradedTensorProduct.includeRight ((stdTower (K := K) a).gtensor (stdTower b)).grading
                (stdTower (K := K) c).grading w') :=
          rfl
        rw [hcol, Q1.cEmbed K a b c d _ w' rfl _ rfl,
          Q4_cEmbed_bundled K a b c d _ w' rfl _ rfl]
        exact hc hw' m)
  have hABCD := superEquivariantAt_of_includeLeft_includeRight
      (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
      (stdTower (K := K) d).grading (ιABCD K a b c d)
      (f := f) (e := e)
      (fun j w hw m => by
        have hcol : (ιABCD K a b c d)
            (GradedTensorProduct.includeLeft
              (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
              (stdTower (K := K) d).grading w)
          = ιABC K a b c d w := rfl
        rw [hcol]
        exact hABC hw m)
      (fun k t ht m => by
        have hcol : (ιABCD K a b c d)
            (GradedTensorProduct.includeRight
              (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
              (stdTower (K := K) d).grading t)
          = GradedTensorProduct.includeRight
              (((stdTower (K := K) a).gtensor (stdTower b)).gtensor (stdTower c)).grading
              (stdTower (K := K) d).grading t :=
          rfl
        rw [hcol, Q1.dEmbed K a b c d _ t rfl, Q4_dEmbed_bundled K a b c d _ t rfl]
        exact hd ht m)
  intro i w hw m
  exact hABCD hw m

/-! ### (B), instantiated: the outer sop-tensor split -/

variable (K a b c d)

set_option maxHeartbeats 1000000 in
/-- **The `⊆` direction, assembled**: all six `quadInterSpace`
conditions (`homGrading`, the four slot super-equivariances, and
`rightSemilinear`) assemble into full `QuadEnv`-super-equivariance —
the `quadSource`-level equivariance of `quadSource_equivariant_of_slots`
supplies `hL` (via `Q1_quadEnv_smul_def`/`Q4_quadEnv_smul_def` +
`actionHom_includeLeft_apply`, since `QuadEnv`, unlike `quadSource`, is
a plain `abbrev` for the RAW graded tensor product, so `AlgHom.id`
typechecks against it directly with no instance mismatch); `hR` is the
sop-generator condition of (A), reconciled with `rightSemilinear` via
`rightRecast_op_smul_def` (`QuadEnvModule2.lean`).  (The `maxHeartbeats`
bump is needed for the `Q4.rightRecast_op_smul_def` rewrite, whose two
sides route through several layers of `Module.compHom`/`RingHom.op`.) -/
theorem quadEnv_equivariant_of_quadInterSpace
    {e : ZMod 2} {f : Q1 K a b c d →ₗ[K] Q4 K a b c d}
    (hgrad : f ∈ homGrading (Q1.grading K a b c d) (Q4.grading K a b c d) e)
    (ha : f ∈ superEquivariant (stdTower (K := K) a).grading e)
    (hb : f ∈ superEquivariant (stdTower (K := K) b).grading e)
    (hc : f ∈ superEquivariant (stdTower (K := K) c).grading e)
    (hd : f ∈ superEquivariant (stdTower (K := K) d).grading e)
    (hR : f ∈ rightSemilinear
        ((stdTowerCast (K := K) (quadRightCast_eq2 a b c d)).toAlgEquiv.toAlgHom.toRingHom)) :
    ∀ ⦃i : ZMod 2⦄ ⦃w : QuadEnv K a b c d⦄,
      w ∈ quadEnvGrading K a b c d i → ∀ m : Q1 K a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m) := by
  rw [mem_rightSemilinear] at hR
  have hslots := quadSource_equivariant_of_slots ha hb hc hd
  have hunsigned : ∀ ⦃j : ZMod 2⦄ ⦃τ : (stdTower (K := K) (a + b + c + d)).carrier⦄,
      τ ∈ (stdTower (K := K) (a + b + c + d)).grading j → ∀ m : Q1 K a b c d,
        f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
    intro j τ hτ m
    rw [Q4.rightRecast_op_smul_def]
    exact hR τ m
  exact superEquivariantAt_of_includeLeft_includeRight
    (quadSource (K := K) a b c d).grading (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading)
    (AlgHom.id K (QuadEnv K a b c d)) (f := f) (e := e)
    (fun j x hx m => by
      have hcol : (AlgHom.id K (QuadEnv K a b c d))
          (GradedTensorProduct.includeLeft (quadSource (K := K) a b c d).grading
            (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) x)
        = GradedTensorProduct.includeLeft (quadSource (K := K) a b c d).grading
            (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) x := rfl
      rw [hcol, Q1_quadEnv_smul_def, actionHom_includeLeft_apply,
        Q4_quadEnv_smul_def, actionHom_includeLeft_apply]
      exact hslots hx m)
    (fun k τ hτ m => by
      have hcol : (AlgHom.id K (QuadEnv K a b c d))
          (GradedTensorProduct.includeRight (quadSource (K := K) a b c d).grading
            (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) τ)
        = GradedTensorProduct.includeRight (quadSource (K := K) a b c d).grading
            (SuperOp.grading (stdTower (K := K) (a + b + c + d)).grading) τ := rfl
      rw [hcol, Q1_quadEnv_smul_def, actionHom_includeRight_apply,
        Q4_quadEnv_smul_def, actionHom_includeRight_apply]
      set τ' := SuperOp.unop (stdTower (K := K) (a + b + c + d)).grading τ with hτ'def
      have hτ'mem : τ' ∈ (stdTower (K := K) (a + b + c + d)).grading k := hτ
      rw [show τ = SuperOp.op (stdTower (K := K) (a + b + c + d)).grading τ'
          from (SuperOp.op_unop (stdTower (K := K) (a + b + c + d)).grading τ).symm]
      exact (rightActionHom_equivariant_iff_rightSemilinear
        (stdTower (K := K) (a + b + c + d)).grading (Q1.grading K a b c d) (Q4.grading K a b c d)
        hgrad hτ'mem).mpr (hunsigned hτ'mem) m)

/-! ### The interface, assembled -/

/-- **`mem_quadInterSpace_iff_gradedHomF`**: `quadInterSpace`'s six
conditions (`homGrading`, the four slot super-equivariances,
`rightSemilinear`) are EXACTLY `gradedHomF`'s two (`homGrading` and
`QuadEnv`-super-equivariance) — the interface completing this
milestone.  `⊇` is `quadInterSpace_of_mem_gradedHomF`; `⊆` assembles
`quadEnv_equivariant_of_quadInterSpace` (the four slots plus
`rightSemilinear` give full `QuadEnv`-equivariance) with the verbatim
`homGrading` match. -/
theorem mem_quadInterSpace_iff_gradedHomF {e : ZMod 2} {f : Q1 K a b c d →ₗ[K] Q4 K a b c d} :
    f ∈ quadInterSpace K a b c d e ↔
      f ∈ gradedHomF (Q1.grading K a b c d) (quadEnvGrading K a b c d) (Q4.grading K a b c d) e := by
  constructor
  · intro hf
    rw [mem_quadInterSpace_iff] at hf
    obtain ⟨hgrad, ha, hb, hc, hd, hR⟩ := hf
    rw [mem_gradedHomF_iff, mem_superEquivariant]
    exact ⟨hgrad, quadEnv_equivariant_of_quadInterSpace K a b c d hgrad ha hb hc hd hR⟩
  · exact quadInterSpace_of_mem_gradedHomF K a b c d

end PentagonB

end Bimod

end Superfusion

/-
Superfusion / Bimod / HomGrading

Milestone M8a-8a (general layer): **the pieces of the intertwiner
space** (§4.1: "homogeneous intertwiners, left super-equivariant,
right linear").  For `K`-modules `M`, `N`:

* `homGrading ℳ 𝒩 d` — the degree-`d` homogeneous maps
  (`f (ℳ i) ⊆ 𝒩 (i + d)`, the two-module `endGrading`);
* `superEquivariant 𝒯 d` — the maps super-equivariant of degree `d`
  for a graded `T`-action on both sides:
  `f (x • m) = (-1)^{d|x|} x • (f m)` on homogeneous `x`;
* `rightSemilinear ψ` — the maps intertwining right actions along an
  algebra map `ψ` (the coefficient identification; for `B_L → B_R`
  it is the associativity cast of the tower index).
* `homMask ℳ 𝒩 d` — the direct degree-`d` projection on maps between
  decomposed modules.  For strict right-linear maps over the same graded
  algebra, the projection is again strict right-linear.

Each is a `K`-submodule of `M →ₗ[K] N`; the paper's intertwiner space
is their intersection (`Intertwiner.lean`).
-/
import Superfusion.Bimod.GradedModule

namespace Superfusion

namespace Bimod

variable {K : Type*} [CommRing K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable {N : Type*} [AddCommGroup N] [Module K N]

/-! ### Homogeneous maps of a given degree -/

section HomGrading

variable (ℳ : ZMod 2 → Submodule K M) (𝒩 : ZMod 2 → Submodule K N)

/-- The degree-`d` homogeneous maps: `f (ℳ i) ⊆ 𝒩 (i + d)` (the
two-module `endGrading`). -/
def homGrading (d : ZMod 2) : Submodule K (M →ₗ[K] N) where
  carrier := {f | ∀ i : ZMod 2, ∀ m ∈ ℳ i, f m ∈ 𝒩 (i + d)}
  zero_mem' i m _ := by
    rw [LinearMap.zero_apply]
    exact zero_mem _
  add_mem' {f g} hf hg i m hm := by
    rw [LinearMap.add_apply]
    exact add_mem (hf i m hm) (hg i m hm)
  smul_mem' c f hf i m hm := by
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (hf i m hm)

theorem mem_homGrading {d : ZMod 2} {f : M →ₗ[K] N} :
    f ∈ homGrading ℳ 𝒩 d ↔ ∀ i : ZMod 2, ∀ m ∈ ℳ i, f m ∈ 𝒩 (i + d) :=
  Iff.rfl

end HomGrading

/-! ### Direct masks for two-module Hom gradings -/

section HomMask

variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]

private theorem zmod2_homMask_left_cancel :
    ∀ i j k : ZMod 2, k + i = k + j → i = j := by decide

/-- The degree-`d` mask on maps between two decomposed modules:
`f ↦ P_N(d) f P_M(0) + P_N(1+d) f P_M(1)`.

Unlike the parity-conjugation formula, this construction does not divide by
two. -/
noncomputable def homMask (d : ZMod 2) :
    (M →ₗ[K] N) →ₗ[K] (M →ₗ[K] N) where
  toFun f :=
    modProj 𝒩 (0 + d) ∘ₗ f ∘ₗ modProj ℳ 0 +
      modProj 𝒩 (1 + d) ∘ₗ f ∘ₗ modProj ℳ 1
  map_add' f g := by
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    abel
  map_smul' c f := by
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply,
      smul_add]

theorem homMask_apply (d : ZMod 2) (f : M →ₗ[K] N) (m : M) :
    homMask ℳ 𝒩 d f m =
      modProj 𝒩 (0 + d) (f (modProj ℳ 0 m)) +
        modProj 𝒩 (1 + d) (f (modProj ℳ 1 m)) :=
  rfl

/-- The degree mask has the requested degree. -/
theorem homMask_mem_homGrading (d : ZMod 2) (f : M →ₗ[K] N) :
    homMask ℳ 𝒩 d f ∈ homGrading ℳ 𝒩 d := by
  intro i m hm
  rw [homMask_apply]
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [modProj_of_mem ℳ hm,
      modProj_of_mem_ne ℳ hm (by decide), map_zero, map_zero, add_zero]
    exact modProj_mem 𝒩 (0 + d) _
  · rw [modProj_of_mem ℳ hm,
      modProj_of_mem_ne ℳ hm (by decide), map_zero, map_zero, zero_add]
    exact modProj_mem 𝒩 (1 + d) _

/-- The two degree masks add to the original map. -/
theorem homMask_zero_add_one (f : M →ₗ[K] N) :
    homMask ℳ 𝒩 0 f + homMask ℳ 𝒩 1 f = f := by
  apply LinearMap.ext
  intro m
  rw [LinearMap.add_apply, homMask_apply, homMask_apply]
  rw [show (0 : ZMod 2) + 0 = 0 from by decide,
    show (1 : ZMod 2) + 0 = 1 from by decide,
    show (0 : ZMod 2) + 1 = 1 from by decide,
    show (1 : ZMod 2) + 1 = 0 from by decide,
    add_add_add_comm, modProj_zero_add_modProj_one,
    add_comm (modProj 𝒩 1 (f (modProj ℳ 1 m)))
      (modProj 𝒩 0 (f (modProj ℳ 1 m))),
    modProj_zero_add_modProj_one, ← map_add,
    modProj_zero_add_modProj_one]

/-- The mask of a map already in its selected degree is the map itself. -/
theorem homMask_of_mem {d : ZMod 2} {f : M →ₗ[K] N}
    (hf : f ∈ homGrading ℳ 𝒩 d) :
    homMask ℳ 𝒩 d f = f := by
  apply LinearMap.ext
  intro m
  rw [homMask_apply]
  conv_rhs => rw [← modProj_zero_add_modProj_one ℳ m, map_add]
  rw [modProj_of_mem 𝒩
      (hf 0 _ (modProj_mem ℳ 0 m)),
    modProj_of_mem 𝒩
      (hf 1 _ (modProj_mem ℳ 1 m))]

/-- A mask of the other degree vanishes on a homogeneous map. -/
theorem homMask_of_mem_ne {d d' : ZMod 2} {f : M →ₗ[K] N}
    (hf : f ∈ homGrading ℳ 𝒩 d) (hdd' : d ≠ d') :
    homMask ℳ 𝒩 d' f = 0 := by
  apply LinearMap.ext
  intro m
  rw [homMask_apply,
    modProj_of_mem_ne 𝒩
      (hf 0 _ (modProj_mem ℳ 0 m))
      (fun h => hdd' (zmod2_homMask_left_cancel d d' 0 h)),
    modProj_of_mem_ne 𝒩
      (hf 1 _ (modProj_mem ℳ 1 m))
      (fun h => hdd' (zmod2_homMask_left_cancel d d' 1 h)),
    add_zero, LinearMap.zero_apply]

end HomMask

/-! ### Super-equivariance of a given degree -/

section Equivariant

variable {T : Type*} [Ring T] [Algebra K T]
variable (𝒯 : ZMod 2 → Submodule K T)
variable [Module T M] [Module T N]
variable [SMulCommClass K T N]

/-- The degree-`d` super-equivariant maps for a graded `T`-action:
`f (x • m) = (-1)^{d|x|} x • (f m)` on homogeneous `x` (§4.1 "left
super-equivariant"; the sign convention of super Skolem–Noether). -/
def superEquivariant (d : ZMod 2) : Submodule K (M →ₗ[K] N) where
  carrier := {f | ∀ ⦃i : ZMod 2⦄ ⦃x : T⦄, x ∈ 𝒯 i → ∀ m : M,
    f (x • m) = ((sgn (d * i) : ℤˣ) : ℤ) • (x • f m)}
  zero_mem' {i x} _ m := by
    rw [LinearMap.zero_apply, LinearMap.zero_apply, smul_zero, smul_zero]
  add_mem' {f g} hf hg i x hx m := by
    rw [LinearMap.add_apply, LinearMap.add_apply, hf hx m, hg hx m,
      smul_add, smul_add]
  smul_mem' c f hf i x hx m := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hf hx m, smul_comm c,
      smul_comm c x]

theorem mem_superEquivariant {d : ZMod 2} {f : M →ₗ[K] N} :
    f ∈ superEquivariant 𝒯 (M := M) (N := N) d ↔
      ∀ ⦃i : ZMod 2⦄ ⦃x : T⦄, x ∈ 𝒯 i → ∀ m : M,
        f (x • m) = ((sgn (d * i) : ℤˣ) : ℤ) • (x • f m) :=
  Iff.rfl

end Equivariant

/-! ### Right semilinearity along a coefficient identification -/

section RightSemilinear

variable {T T' : Type*} [Ring T] [Ring T']
variable [Module Tᵐᵒᵖ M] [Module T'ᵐᵒᵖ N] [SMulCommClass K T'ᵐᵒᵖ N]
variable (ψ : T →+* T')

/-- The maps intertwining the right actions along `ψ`:
`f (m · t) = (f m) · ψ t` (§4.1 "right linear"; `ψ` is the
identification of the two coefficient algebras). -/
def rightSemilinear : Submodule K (M →ₗ[K] N) where
  carrier := {f | ∀ (t : T) (m : M),
    f (MulOpposite.op t • m) = MulOpposite.op (ψ t) • f m}
  zero_mem' t m := by
    rw [LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]
  add_mem' {f g} hf hg t m := by
    rw [LinearMap.add_apply, LinearMap.add_apply, hf t m, hg t m, smul_add]
  smul_mem' c f hf t m := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hf t m, smul_comm c]

theorem mem_rightSemilinear {f : M →ₗ[K] N} :
    f ∈ rightSemilinear (M := M) (N := N) ψ ↔
      ∀ (t : T) (m : M),
        f (MulOpposite.op t • m) = MulOpposite.op (ψ t) • f m :=
  Iff.rfl

end RightSemilinear

/-! ### Direct Hom masks preserve strict right-linearity -/

section RightHomMask

variable {D : Type*} [Ring D] [Algebra K D]
variable (𝒟 : ZMod 2 → Submodule K D) [DirectSum.Decomposition 𝒟]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]
variable [Module Dᵐᵒᵖ M] [Module Dᵐᵒᵖ N] [SMulCommClass K Dᵐᵒᵖ N]
variable [GradedRightSMul 𝒟 ℳ] [GradedRightSMul 𝒟 𝒩]

omit [DirectSum.Decomposition 𝒟] in
/-- On a homogeneous coefficient, a direct Hom mask of a strict right-linear
map is again right-linear. -/
theorem homMask_op_smul_of_mem (d : ZMod 2) (f : M →ₗ[K] N)
    (hf : f ∈ rightSemilinear (M := M) (N := N) (RingHom.id D))
    {j : ZMod 2} {a : D} (ha : a ∈ 𝒟 j) (m : M) :
    homMask ℳ 𝒩 d f (MulOpposite.op a • m) =
      MulOpposite.op a • homMask ℳ 𝒩 d f m := by
  rw [homMask_apply, homMask_apply,
    modProj_op_smul_of_mem ℳ 𝒟 ha 0,
    modProj_op_smul_of_mem ℳ 𝒟 ha 1]
  have hf' : ∀ x : M,
      f (MulOpposite.op a • x) = MulOpposite.op a • f x := by
    intro x
    simpa using hf a x
  rw [hf', hf',
    modProj_op_smul_of_mem 𝒩 𝒟 ha (0 + d),
    modProj_op_smul_of_mem 𝒩 𝒟 ha (1 + d)]
  rcases zmod2_cases j with hj | hj <;> subst hj
  · simp only [add_zero, smul_add]
  · have h₁ : ∀ x : ZMod 2, 1 + x + 1 = 0 + x := by decide
    simp only [zero_add, show (1 : ZMod 2) + 1 = 0 from by decide,
      h₁, smul_add]
    rw [add_comm d 1]
    exact add_comm _ _

include 𝒟 in
/-- Direct degree masks preserve strict right-linearity over the same graded
coefficient algebra. -/
theorem homMask_mem_rightSemilinear (d : ZMod 2) (f : M →ₗ[K] N)
    (hf : f ∈ rightSemilinear (M := M) (N := N) (RingHom.id D)) :
    homMask ℳ 𝒩 d f ∈
      rightSemilinear (M := M) (N := N) (RingHom.id D) := by
  intro a m
  induction a using DirectSum.Decomposition.inductionOn 𝒟 with
  | zero =>
      simp only [MulOpposite.op_zero, zero_smul, map_zero]
  | add a b ha hb =>
      simpa only [MulOpposite.op_add, add_smul, map_add, smul_add] using
        congrArg₂ (· + ·) ha hb
  | homogeneous a =>
      simpa using homMask_op_smul_of_mem 𝒟 ℳ 𝒩 d f hf a.2 m

end RightHomMask

end Bimod

end Superfusion

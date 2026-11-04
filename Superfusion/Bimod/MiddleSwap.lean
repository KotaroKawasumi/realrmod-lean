/-
Superfusion / Bimod / MiddleSwap

Milestone M8a-8c′-1b-vi (roadmap v3): **the middle swap** —

  `midSwap : M ⊗[A] (N ⊗[B] P) ≃ₗ N ⊗[B] (M ⊗[A] P)`,
  `m ⊗ (n ⊗ p) ↦ (-1)^{|m||n|} n ⊗ (m ⊗ p)`,

for `M` right-`A`, `N` right-`B`, and `P` carrying two left actions
(by `A` and by `B`), each balancing one side directly and acting on
the other side through the Koszul-signed middle action — the gadget
that exposes the canonical `B_L(a,b,c{+}d)` inside the
`(ab)(cd)`-vertex for the last pentagon edge `E₅`.

The two outer `Module` structures are abstracted as instance
*variables*, constrained only by the generator sign laws (`MidSignLaw`)
of the signed middle action; for the `midAlgHom`-based structures of
the pentagon files these laws hold by `midEnd_mk_of_mem`.  As
everywhere in this project the sign has a closed bilinear form,

  `(n, p, m) ↦ n ⊗ (m ⊗ p) - 2 (odd n) ⊗ ((odd m) ⊗ p)`,

whose `B`-balancedness is the cancellation of the swap sign against
the middle-action sign (`(k+i)j + kj = ij`) and whose `A`-balancedness
is the mirror identity (`i(l+j) = li + ij`).  The construction is
literally symmetric in the `(A, M, ℳ)` and `(B, N, 𝒩)` data, so the
inverse is the same map at transposed parameters, and the round trip
is a closed-form computation (idempotency of the odd projections — no
sign chase, no induction).
-/
import Superfusion.Bimod.RelTensorGraded

namespace Superfusion

namespace Bimod

open scoped TensorProduct

/-! ### The sign-law hypothesis -/

section SignLaw

variable (K : Type*) [CommRing K]
variable (A : Type*) [Ring A] [Algebra K A]
variable (B : Type*) [Ring B]
variable (N : Type*) [AddCommGroup N] [Module K N] [Module Bᵐᵒᵖ N]
variable (P : Type*) [AddCommGroup P] [Module K P] [Module A P] [Module B P]
variable (𝒜 : ZMod 2 → Submodule K A) (𝒩 : ZMod 2 → Submodule K N)
variable [Module A (N ⊗[B;K] P)]

/-- The generator sign law of a Koszul-signed middle action: `A` acts
on `N ⊗[B] P` through `P`, with the Koszul sign against the parity of
the first slot — `x • (n ⊗ p) = (-1)^{|x||n|} n ⊗ (x • p)`.  For the
`midAlgHom`-based module structures this holds by `midEnd_mk_of_mem`;
here it is the *hypothesis* under which the middle swap is built, so
that the gadget applies to any spelling of those structures. -/
def MidSignLaw : Prop :=
  ∀ ⦃l i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 l → ∀ ⦃n : N⦄, n ∈ 𝒩 i → ∀ p : P,
    x • RelTensor.mk K B N P n p
      = ((sgn (l * i) : ℤˣ) : ℤ) • RelTensor.mk K B N P n (x • p)

end SignLaw

/-! ### The swap -/

section Swap

variable (K : Type*) [CommRing K]
variable (A : Type*) [Ring A] [Algebra K A]
variable (B : Type*) [Ring B] [Algebra K B]
variable (M : Type*) [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (N : Type*) [AddCommGroup N] [Module K N] [Module Bᵐᵒᵖ N]
variable (P : Type*) [AddCommGroup P] [Module K P] [Module A P] [Module B P]
variable (𝒜 : ZMod 2 → Submodule K A) [DirectSum.Decomposition 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [DirectSum.Decomposition ℬ]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]
variable [GradedRightSMul 𝒜 ℳ] [GradedRightSMul ℬ 𝒩]
variable [Module A (N ⊗[B;K] P)] [Module B (M ⊗[A;K] P)]

/-! #### The closed trilinear form -/

/-- The bundled trilinear map `(n, p, m) ↦ n ⊗ (m ⊗ p)`. -/
private noncomputable def swapBase :
    N →ₗ[K] P →ₗ[K] M →ₗ[K] (N ⊗[B;K] (M ⊗[A;K] P)) :=
  ((LinearMap.llcomp K M (M ⊗[A;K] P) (N ⊗[B;K] (M ⊗[A;K] P))).comp
    (RelTensor.mk K B N (M ⊗[A;K] P))).compl₂ (RelTensor.mk K A M P).flip

omit [Algebra K A] [Algebra K B] [Module B P] [Module A (N ⊗[B;K] P)] in
private theorem swapBase_apply (n : N) (p : P) (m : M) :
    swapBase K A B M N P n p m
      = RelTensor.mk K B N (M ⊗[A;K] P) n (RelTensor.mk K A M P m p) :=
  rfl

/-- The odd–odd correction `(n, p, m) ↦ (odd n) ⊗ ((odd m) ⊗ p)`. -/
private noncomputable def swapOdd :
    N →ₗ[K] P →ₗ[K] M →ₗ[K] (N ⊗[B;K] (M ⊗[A;K] P)) :=
  ((swapBase K A B M N P).comp (modProj 𝒩 1)).compr₂
    ((LinearMap.llcomp K M M (N ⊗[B;K] (M ⊗[A;K] P))).flip (modProj ℳ 1))

omit [Algebra K A] [Algebra K B] [Module B P] [Module A (N ⊗[B;K] P)] in
private theorem swapOdd_apply (n : N) (p : P) (m : M) :
    swapOdd K A B M N P ℳ 𝒩 n p m
      = RelTensor.mk K B N (M ⊗[A;K] P) (modProj 𝒩 1 n)
          (RelTensor.mk K A M P (modProj ℳ 1 m) p) :=
  rfl

/-- The middle swap in closed trilinear form:
`(n, p, m) ↦ n ⊗ (m ⊗ p) - 2 (odd n) ⊗ ((odd m) ⊗ p)`
(via `(-1)^{|m||n|} = 1 - 2·[both odd]`). -/
private noncomputable def swapTri :
    N →ₗ[K] P →ₗ[K] M →ₗ[K] (N ⊗[B;K] (M ⊗[A;K] P)) :=
  swapBase K A B M N P - (2 : ℤ) • swapOdd K A B M N P ℳ 𝒩

omit [Algebra K A] [Algebra K B] [Module B P] [Module A (N ⊗[B;K] P)] in
private theorem swapTri_apply (n : N) (p : P) (m : M) :
    swapTri K A B M N P ℳ 𝒩 n p m
      = RelTensor.mk K B N (M ⊗[A;K] P) n (RelTensor.mk K A M P m p)
        - (2 : ℤ) • RelTensor.mk K B N (M ⊗[A;K] P) (modProj 𝒩 1 n)
            (RelTensor.mk K A M P (modProj ℳ 1 m) p) :=
  rfl

omit [Algebra K A] [Algebra K B] [Module B P] [Module A (N ⊗[B;K] P)] in
/-- **The sign law of the closed form**: on homogeneous `n ∈ 𝒩 i`,
`m ∈ ℳ j` it is `(-1)^{ij} n ⊗ (m ⊗ p)`. -/
private theorem swapTri_of_mem {i j : ZMod 2} {n : N} {m : M}
    (hn : n ∈ 𝒩 i) (hm : m ∈ ℳ j) (p : P) :
    swapTri K A B M N P ℳ 𝒩 n p m
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K B N (M ⊗[A;K] P) n (RelTensor.mk K A M P m p) := by
  rw [swapTri_apply]
  rcases zmod2_cases i with hi | hi <;> rcases zmod2_cases j with hj | hj <;>
      subst hi <;> subst hj
  · rw [modProj_of_mem_ne 𝒩 hn (by decide), map_zero, LinearMap.zero_apply,
      smul_zero, sub_zero]
    simp
  · rw [modProj_of_mem_ne 𝒩 hn (by decide), map_zero, LinearMap.zero_apply,
      smul_zero, sub_zero]
    simp
  · rw [modProj_of_mem_ne ℳ hm (by decide), map_zero, LinearMap.zero_apply,
      map_zero, smul_zero, sub_zero]
    simp
  · rw [modProj_of_mem 𝒩 hn, modProj_of_mem ℳ hm,
      show (1 : ZMod 2) * 1 = 1 from by decide]
    simp only [sgn_one, units_sign_eq, Units.val_neg, Units.val_one,
      neg_smul, one_smul, two_smul]
    abel

/-! #### Balancedness over `B`: the sign cancellation -/

omit [Algebra K A] [Module A (N ⊗[B;K] P)] in
/-- The `B`-balancedness of the closed form: the swap sign against the
middle-action sign of the target, `(k+i)j + kj = ij`. -/
private theorem swapTri_balancedB (hB : MidSignLaw K B A M P ℬ ℳ) :
    RelTensor.IsBalanced B (swapTri K A B M N P ℳ 𝒩) := by
  intro y n p
  refine LinearMap.ext fun m => ?_
  induction y using DirectSum.Decomposition.inductionOn ℬ with
  | zero =>
      simp only [MulOpposite.op_zero, zero_smul, map_zero,
        LinearMap.zero_apply]
  | add y y' hy hy' =>
      simp only [MulOpposite.op_add, add_smul, map_add,
        LinearMap.add_apply, hy, hy']
  | homogeneous yb =>
      induction n using DirectSum.Decomposition.inductionOn 𝒩 with
      | zero =>
          simp only [smul_zero, map_zero, LinearMap.zero_apply]
      | add n n' hn hn' =>
          simp only [smul_add, map_add, LinearMap.add_apply, hn, hn']
      | homogeneous xn =>
          induction m using DirectSum.Decomposition.inductionOn ℳ with
          | zero => simp only [map_zero]
          | add m m' hm hm' => simp only [map_add, hm, hm']
          | homogeneous xm =>
              have sign_id : ∀ k i j : ZMod 2,
                  (k + i) * j + k * j = i * j := by decide
              rw [swapTri_of_mem K A B M N P ℳ 𝒩
                  (GradedRightSMul.smul_mem yb.2 xn.2) xm.2 p,
                swapTri_of_mem K A B M N P ℳ 𝒩 xn.2 xm.2 ((yb : B) • p),
                RelTensor.mk_op_smul, hB yb.2 xm.2, map_zsmul, smul_smul,
                ← Units.val_mul, ← sgn_add, sign_id]

/-! #### The lift ladder -/

private noncomputable def swapInner (hB : MidSignLaw K B A M P ℬ ℳ) :
    (N ⊗[B;K] P) →ₗ[K] M →ₗ[K] (N ⊗[B;K] (M ⊗[A;K] P)) :=
  RelTensor.lift (swapTri K A B M N P ℳ 𝒩)
    (swapTri_balancedB K A B M N P ℬ ℳ 𝒩 hB)

omit [Algebra K A] [Module A (N ⊗[B;K] P)] in
private theorem swapInner_mk (hB : MidSignLaw K B A M P ℬ ℳ)
    (n : N) (p : P) (m : M) :
    swapInner K A B M N P ℬ ℳ 𝒩 hB (RelTensor.mk K B N P n p) m
      = swapTri K A B M N P ℳ 𝒩 n p m := by
  show (RelTensor.lift (swapTri K A B M N P ℳ 𝒩)
      (swapTri_balancedB K A B M N P ℬ ℳ 𝒩 hB)
      (RelTensor.mk K B N P n p)) m = _
  rw [RelTensor.lift_mk]

/-- The `A`-balancedness of the flipped bilinear: the mirror sign
cancellation, `i(l+j) = li + ij`. -/
private theorem swapFlip_balancedA (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) :
    RelTensor.IsBalanced A (swapInner K A B M N P ℬ ℳ 𝒩 hB).flip := by
  intro x m w
  show swapInner K A B M N P ℬ ℳ 𝒩 hB w (MulOpposite.op x • m)
      = swapInner K A B M N P ℬ ℳ 𝒩 hB (x • w) m
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
      simp only [MulOpposite.op_zero, zero_smul, map_zero,
        LinearMap.zero_apply]
  | add x x' hx hx' =>
      simp only [MulOpposite.op_add, add_smul, map_add,
        LinearMap.add_apply, hx, hx']
  | homogeneous xa =>
      induction m using DirectSum.Decomposition.inductionOn ℳ with
      | zero =>
          simp only [smul_zero, map_zero]
      | add m m' hm hm' =>
          simp only [smul_add, map_add, hm, hm']
      | homogeneous xm =>
          induction w using RelTensor.induction_on with
          | zero =>
              simp only [map_zero, LinearMap.zero_apply, smul_zero]
          | add w w' hw hw' =>
              simp only [map_add, LinearMap.add_apply, smul_add, hw, hw']
          | mk n p =>
              induction n using DirectSum.Decomposition.inductionOn 𝒩 with
              | zero =>
                  simp only [map_zero, LinearMap.zero_apply, smul_zero]
              | add n n' hn hn' =>
                  simp only [map_add, LinearMap.add_apply, smul_add,
                    hn, hn']
              | homogeneous xn =>
                  have sign_id : ∀ l i j : ZMod 2,
                      l * i + i * j = i * (l + j) := by decide
                  rw [swapInner_mk K A B M N P ℬ ℳ 𝒩 hB,
                    swapTri_of_mem K A B M N P ℳ 𝒩 xn.2
                      (GradedRightSMul.smul_mem xa.2 xm.2) p,
                    RelTensor.mk_op_smul, hA xa.2 xn.2, map_zsmul,
                    LinearMap.smul_apply,
                    swapInner_mk K A B M N P ℬ ℳ 𝒩 hB,
                    swapTri_of_mem K A B M N P ℳ 𝒩 xn.2 xm.2
                      ((xa : A) • p),
                    smul_smul, ← Units.val_mul, ← sgn_add, sign_id]

/-! #### The swap -/

/-- **The middle swap**, as a linear map:
`m ⊗ (n ⊗ p) ↦ (-1)^{|m||n|} n ⊗ (m ⊗ p)`. -/
noncomputable def midSwapMap (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) :
    (M ⊗[A;K] (N ⊗[B;K] P)) →ₗ[K] (N ⊗[B;K] (M ⊗[A;K] P)) :=
  RelTensor.lift (swapInner K A B M N P ℬ ℳ 𝒩 hB).flip
    (swapFlip_balancedA K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB)

theorem midSwapMap_mk (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) (m : M) (w : N ⊗[B;K] P) :
    midSwapMap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB
        (RelTensor.mk K A M (N ⊗[B;K] P) m w)
      = swapInner K A B M N P ℬ ℳ 𝒩 hB w m := by
  show RelTensor.lift (swapInner K A B M N P ℬ ℳ 𝒩 hB).flip
      (swapFlip_balancedA K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB)
      (RelTensor.mk K A M (N ⊗[B;K] P) m w) = _
  rw [RelTensor.lift_mk]
  rfl

/-- The closed generator formula of the middle swap. -/
theorem midSwapMap_mk_mk (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) (m : M) (n : N) (p : P) :
    midSwapMap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB
        (RelTensor.mk K A M (N ⊗[B;K] P) m (RelTensor.mk K B N P n p))
      = RelTensor.mk K B N (M ⊗[A;K] P) n (RelTensor.mk K A M P m p)
        - (2 : ℤ) • RelTensor.mk K B N (M ⊗[A;K] P) (modProj 𝒩 1 n)
            (RelTensor.mk K A M P (modProj ℳ 1 m) p) := by
  rw [midSwapMap_mk K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB,
    swapInner_mk K A B M N P ℬ ℳ 𝒩 hB,
    swapTri_apply K A B M N P ℳ 𝒩]

/-- **The sign law of the middle swap**: on homogeneous `n ∈ 𝒩 i`,
`m ∈ ℳ j`, `m ⊗ (n ⊗ p) ↦ (-1)^{ij} n ⊗ (m ⊗ p)`. -/
theorem midSwapMap_mk_of_mem (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) {i j : ZMod 2} {n : N} {m : M}
    (hn : n ∈ 𝒩 i) (hm : m ∈ ℳ j) (p : P) :
    midSwapMap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB
        (RelTensor.mk K A M (N ⊗[B;K] P) m (RelTensor.mk K B N P n p))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K B N (M ⊗[A;K] P) n (RelTensor.mk K A M P m p) := by
  rw [midSwapMap_mk K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB,
    swapInner_mk K A B M N P ℬ ℳ 𝒩 hB,
    swapTri_of_mem K A B M N P ℳ 𝒩 hn hm p]

/-! #### The round trip -/

/-- The swap composed with its transposed-parameter mirror is the
identity: a closed-form computation via the idempotency of the odd
projections (`(-1)^{2|m||n|} = 1`, with no sign chase). -/
private theorem swap_comp_swap (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) :
    (midSwapMap K B A N M P ℬ 𝒜 𝒩 ℳ hB hA).comp
        (midSwapMap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB) = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  induction w using RelTensor.induction_on with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | mk n p =>
      rw [midSwapMap_mk_mk K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB, map_sub,
        map_zsmul, midSwapMap_mk_mk K B A N M P ℬ 𝒜 𝒩 ℳ hB hA,
        midSwapMap_mk_mk K B A N M P ℬ 𝒜 𝒩 ℳ hB hA,
        modProj_of_mem ℳ (modProj_mem ℳ 1 m),
        modProj_of_mem 𝒩 (modProj_mem 𝒩 1 n), smul_sub]
      abel

/-- **The middle swap** `M ⊗[A] (N ⊗[B] P) ≃ₗ N ⊗[B] (M ⊗[A] P)`,
`m ⊗ (n ⊗ p) ↦ (-1)^{|m||n|} n ⊗ (m ⊗ p)`: the inverse is the same
construction with the `(A, M, ℳ)` and `(B, N, 𝒩)` data transposed. -/
noncomputable def midSwap (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) :
    (M ⊗[A;K] (N ⊗[B;K] P)) ≃ₗ[K] (N ⊗[B;K] (M ⊗[A;K] P)) :=
  LinearEquiv.ofLinear (midSwapMap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB)
    (midSwapMap K B A N M P ℬ 𝒜 𝒩 ℳ hB hA)
    (swap_comp_swap K B A N M P ℬ 𝒜 𝒩 ℳ hB hA)
    (swap_comp_swap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB)

theorem midSwap_apply (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) (z : M ⊗[A;K] (N ⊗[B;K] P)) :
    midSwap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB z
      = midSwapMap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB z :=
  rfl

theorem midSwap_symm_apply (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) (z : N ⊗[B;K] (M ⊗[A;K] P)) :
    (midSwap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB).symm z
      = midSwapMap K B A N M P ℬ 𝒜 𝒩 ℳ hB hA z :=
  rfl

/-- The sign law of the middle swap, on homogeneous generators. -/
theorem midSwap_mk_of_mem (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) {i j : ZMod 2} {n : N} {m : M}
    (hn : n ∈ 𝒩 i) (hm : m ∈ ℳ j) (p : P) :
    midSwap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB
        (RelTensor.mk K A M (N ⊗[B;K] P) m (RelTensor.mk K B N P n p))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K B N (M ⊗[A;K] P) n (RelTensor.mk K A M P m p) := by
  rw [midSwap_apply K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB,
    midSwapMap_mk_of_mem K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB hn hm p]

/-- The sign law of the inverse middle swap. -/
theorem midSwap_symm_mk_of_mem (hA : MidSignLaw K A B N P 𝒜 𝒩)
    (hB : MidSignLaw K B A M P ℬ ℳ) {i j : ZMod 2} {n : N} {m : M}
    (hn : n ∈ 𝒩 i) (hm : m ∈ ℳ j) (p : P) :
    (midSwap K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB).symm
        (RelTensor.mk K B N (M ⊗[A;K] P) n (RelTensor.mk K A M P m p))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K A M (N ⊗[B;K] P) m (RelTensor.mk K B N P n p) := by
  rw [midSwap_symm_apply K A B M N P 𝒜 ℬ ℳ 𝒩 hA hB,
    midSwapMap_mk_of_mem K B A N M P ℬ 𝒜 𝒩 ℳ hB hA hm hn p,
    mul_comm j i]

end Swap

end Bimod

end Superfusion

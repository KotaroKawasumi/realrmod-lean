/-
Superfusion / Super / AdjoinOdd

Milestone M7a: the first concrete central simple superalgebras.

`AdjoinOdd ε = K ⊕ K·e` with `e` **odd** and `e² = ε` — the rank-one
Clifford superalgebra `K[e]/(e² − ε)`, realized explicitly on the module
`K × K` (so its dimension is `2` by construction, sidestepping the
missing basis/dimension theory for `CliffordAlgebra` in mathlib).

Main results (field base, `2` invertible, `ε ≠ 0`):

* `AdjoinOdd.isSuperCentral` — the supercenter is exactly `K·1`;
* `AdjoinOdd.isGradedSimple` — no nontrivial homogeneous two-sided ideals;
* `AdjoinOdd.isSuperAzumaya` — Wall's criterion holds, via
  `isSuperAzumaya_of_central_simple` (M4).

Over `ℝ`, `ε = ±1` gives the standard super division algebras `D₊₁`,
`D₋₁` of the paper (§2.2, §4), the generators of the Brauer–Wall group
`BW(ℝ) ≅ ℤ/8`; these are the corollaries
`isSuperAzumaya_one_real` / `isSuperAzumaya_neg_one_real`.

Note that `AdjoinOdd ε` is commutative as a plain ring but **not**
supercommutative: `e·e = ε` while the Koszul rule for an odd supercentral
element would force `e·e = −e·e`.  Its supercenter is `K·1`, strictly
smaller than its center — the sanity counterpoint to
`superCenter_evenGrading`.
-/
import Superfusion.Super.WallProof
import Mathlib.Data.Real.Basic

namespace Superfusion

section CommRingBase

variable {K : Type*} [CommRing K]

/-- `K ⊕ K·e` with `e` odd and `e² = ε`: the rank-one Clifford
superalgebra, as an explicit structure on `K × K`. -/
@[nolint unusedArguments]
def AdjoinOdd (ε : K) : Type _ :=
  letI := ε; K × K

namespace AdjoinOdd

variable (ε : K)

instance : AddCommGroup (AdjoinOdd ε) := inferInstanceAs (AddCommGroup (K × K))

instance : Module K (AdjoinOdd ε) := inferInstanceAs (Module K (K × K))

instance [Nontrivial K] : Nontrivial (AdjoinOdd ε) :=
  inferInstanceAs (Nontrivial (K × K))

instance : Module.Finite K (AdjoinOdd ε) :=
  inferInstanceAs (Module.Finite K (K × K))

/-- The element `a + b·e`. -/
def mk (a b : K) : AdjoinOdd ε := ((a, b) : K × K)

/-- The even coordinate (coefficient of `1`). -/
def ev : AdjoinOdd ε →ₗ[K] K := LinearMap.fst K K K

/-- The odd coordinate (coefficient of `e`). -/
def od : AdjoinOdd ε →ₗ[K] K := LinearMap.snd K K K

@[simp] theorem ev_mk (a b : K) : ev ε (mk ε a b) = a := rfl

@[simp] theorem od_mk (a b : K) : od ε (mk ε a b) = b := rfl

theorem ext {p q : AdjoinOdd ε} (h1 : ev ε p = ev ε q)
    (h2 : od ε p = od ε q) : p = q :=
  Prod.ext h1 h2

theorem mk_ev_od (p : AdjoinOdd ε) : mk ε (ev ε p) (od ε p) = p := rfl

instance : One (AdjoinOdd ε) := ⟨mk ε 1 0⟩

@[simp] theorem ev_one : ev ε (1 : AdjoinOdd ε) = 1 := rfl

@[simp] theorem od_one : od ε (1 : AdjoinOdd ε) = 0 := rfl

instance : Mul (AdjoinOdd ε) :=
  ⟨fun p q => mk ε (ev ε p * ev ε q + ε * (od ε p * od ε q))
    (ev ε p * od ε q + od ε p * ev ε q)⟩

@[simp] theorem ev_mul (p q : AdjoinOdd ε) :
    ev ε (p * q) = ev ε p * ev ε q + ε * (od ε p * od ε q) := rfl

@[simp] theorem od_mul (p q : AdjoinOdd ε) :
    od ε (p * q) = ev ε p * od ε q + od ε p * ev ε q := rfl

theorem mk_mul_mk (a b c d : K) :
    mk ε a b * mk ε c d = mk ε (a * c + ε * (b * d)) (a * d + b * c) :=
  ext ε (by simp) (by simp)

instance instMonoid : Monoid (AdjoinOdd ε) where
  one_mul p := ext ε (by simp) (by simp)
  mul_one p := ext ε (by simp) (by simp)
  mul_assoc p q r :=
    ext ε (by simp only [ev_mul, od_mul]; ring)
      (by simp only [ev_mul, od_mul]; ring)

instance instRing : Ring (AdjoinOdd ε) where
  left_distrib p q r :=
    ext ε (by simp only [ev_mul, map_add]; ring)
      (by simp only [od_mul, map_add]; ring)
  right_distrib p q r :=
    ext ε (by simp only [ev_mul, map_add]; ring)
      (by simp only [od_mul, map_add]; ring)
  zero_mul p := ext ε (by simp) (by simp)
  mul_zero p := ext ε (by simp) (by simp)

/-- `AdjoinOdd ε` is commutative as a plain ring (but not
supercommutative). -/
theorem mul_comm' (p q : AdjoinOdd ε) : p * q = q * p :=
  ext ε (by simp only [ev_mul]; ring) (by simp only [od_mul]; ring)

/-- The scalar inclusion `K →+* AdjoinOdd ε`. -/
def algebraMapAux : K →+* AdjoinOdd ε where
  toFun r := mk ε r 0
  map_one' := rfl
  map_mul' r s := ext ε (by simp) (by simp)
  map_zero' := rfl
  map_add' r s := ext ε (by simp) (by simp)

instance instAlgebra : Algebra K (AdjoinOdd ε) where
  algebraMap := algebraMapAux ε
  commutes' r p := mul_comm' ε _ _
  smul_def' r p :=
    ext ε (by simp [algebraMapAux, smul_eq_mul])
      (by simp [algebraMapAux, smul_eq_mul])

@[simp] theorem ev_algebraMap (r : K) :
    ev ε (algebraMap K (AdjoinOdd ε) r) = r := rfl

@[simp] theorem od_algebraMap (r : K) :
    od ε (algebraMap K (AdjoinOdd ε) r) = 0 := rfl

/-- The odd generator `e`. -/
def e : AdjoinOdd ε := mk ε 0 1

@[simp] theorem ev_e : ev ε (e ε) = 0 := rfl

@[simp] theorem od_e : od ε (e ε) = 1 := rfl

/-- The defining relation `e² = ε`. -/
theorem e_mul_e : e ε * e ε = algebraMap K (AdjoinOdd ε) ε :=
  ext ε (by simp) (by simp)

/-! ### The grading

`𝒜 0 = K·1` is the kernel of the odd coordinate, `𝒜 1 = K·e` the kernel
of the even coordinate. -/

/-- The `ZMod 2`-grading of `AdjoinOdd ε`. -/
def grading : ZMod 2 → Submodule K (AdjoinOdd ε) := fun i =>
  if i = 0 then LinearMap.ker (od ε) else LinearMap.ker (ev ε)

theorem mem_grading_zero {p : AdjoinOdd ε} :
    p ∈ grading ε 0 ↔ od ε p = 0 := by
  rw [grading, if_pos rfl, LinearMap.mem_ker]

theorem mem_grading_one {p : AdjoinOdd ε} :
    p ∈ grading ε 1 ↔ ev ε p = 0 := by
  rw [grading, if_neg (by decide), LinearMap.mem_ker]

theorem mk_mem_grading_zero (a : K) : mk ε a 0 ∈ grading ε 0 :=
  (mem_grading_zero ε).mpr rfl

theorem mk_mem_grading_one (b : K) : mk ε 0 b ∈ grading ε 1 :=
  (mem_grading_one ε).mpr rfl

theorem e_mem_grading_one : e ε ∈ grading ε 1 :=
  (mem_grading_one ε).mpr rfl

instance : SetLike.GradedMonoid (grading ε) where
  one_mem := (mem_grading_zero ε).mpr rfl
  mul_mem {i j} p q hp hq := by
    rcases zmod2_cases i with hi | hi <;> rcases zmod2_cases j with hj | hj <;>
      subst hi <;> subst hj
    · show p * q ∈ grading ε 0
      rw [mem_grading_zero] at hp hq ⊢
      simp [hp, hq]
    · show p * q ∈ grading ε 1
      rw [mem_grading_zero] at hp
      rw [mem_grading_one] at hq ⊢
      simp [hp, hq]
    · show p * q ∈ grading ε 1
      rw [mem_grading_one] at hp ⊢
      rw [mem_grading_zero] at hq
      simp [hp, hq]
    · show p * q ∈ grading ε 0
      rw [mem_grading_one] at hp hq
      rw [mem_grading_zero]
      simp [hp, hq]

/-- The pair `(a, b)` as an element of `AdjoinOdd ε`, `K`-linearly. -/
def ofPair : (K × K) ≃ₗ[K] AdjoinOdd ε := LinearEquiv.refl K (K × K)

/-- The projection onto the even layer. -/
def evenInto : AdjoinOdd ε →ₗ[K] grading ε 0 :=
  LinearMap.codRestrict (grading ε 0)
    ((ofPair ε).toLinearMap.comp ((LinearMap.inl K K K).comp (ev ε)))
    fun _ => (mem_grading_zero ε).mpr rfl

/-- The projection onto the odd layer. -/
def oddInto : AdjoinOdd ε →ₗ[K] grading ε 1 :=
  LinearMap.codRestrict (grading ε 1)
    ((ofPair ε).toLinearMap.comp ((LinearMap.inr K K K).comp (od ε)))
    fun _ => (mem_grading_one ε).mpr rfl

@[simp] theorem evenInto_coe (p : AdjoinOdd ε) :
    (evenInto ε p : AdjoinOdd ε) = mk ε (ev ε p) 0 := rfl

@[simp] theorem oddInto_coe (p : AdjoinOdd ε) :
    (oddInto ε p : AdjoinOdd ε) = mk ε 0 (od ε p) := rfl

instance : DirectSum.Decomposition (grading ε) where
  decompose' p :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(grading ε i)) 0 (evenInto ε p)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(grading ε i)) 1 (oddInto ε p)
  left_inv p := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of,
      evenInto_coe, oddInto_coe]
    exact ext ε (by simp) (by simp)
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        rw [map_zero]
        beta_reduce
        rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | of i b =>
        rcases zmod2_cases i with hi | hi <;> subst hi
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : evenInto ε (b : AdjoinOdd ε) = b :=
            Subtype.ext (ext ε (by simp)
              (by simp [(mem_grading_zero ε).mp b.2]))
          have h2 : oddInto ε (b : AdjoinOdd ε) = 0 :=
            Subtype.ext (ext ε (by simp)
              (by simp [(mem_grading_zero ε).mp b.2]))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : evenInto ε (b : AdjoinOdd ε) = 0 :=
            Subtype.ext (ext ε (by simp [(mem_grading_one ε).mp b.2])
              (by simp))
          have h2 : oddInto ε (b : AdjoinOdd ε) = b :=
            Subtype.ext (ext ε (by simp [(mem_grading_one ε).mp b.2])
              (by simp))
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-- `AdjoinOdd ε` is a superalgebra. -/
instance instGradedAlgebra : GradedAlgebra (grading ε) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

/-! ### Graded components, explicitly -/

theorem decompose_zero_coe (p : AdjoinOdd ε) :
    ((DirectSum.decompose (grading ε) p 0 : grading ε 0) : AdjoinOdd ε) =
      mk ε (ev ε p) 0 := by
  have hsplit : p = mk ε (ev ε p) 0 + mk ε 0 (od ε p) :=
    ext ε (by simp) (by simp)
  conv_lhs => rw [hsplit]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_same _ (mk_mem_grading_zero ε _),
    DirectSum.decompose_of_mem_ne _ (mk_mem_grading_one ε _)
      (by decide : (1 : ZMod 2) ≠ 0),
    add_zero]

theorem decompose_one_coe (p : AdjoinOdd ε) :
    ((DirectSum.decompose (grading ε) p 1 : grading ε 1) : AdjoinOdd ε) =
      mk ε 0 (od ε p) := by
  have hsplit : p = mk ε (ev ε p) 0 + mk ε 0 (od ε p) :=
    ext ε (by simp) (by simp)
  conv_lhs => rw [hsplit]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_ne _ (mk_mem_grading_zero ε _)
      (by decide : (0 : ZMod 2) ≠ 1),
    DirectSum.decompose_of_mem_same _ (mk_mem_grading_one ε _),
    zero_add]

end AdjoinOdd

end CommRingBase

/-! ### Central simplicity (field base) -/

namespace AdjoinOdd

section Field

variable {K : Type*} [Field K] (ε : K)

/-- For `ε ≠ 0` (and `2` invertible) the supercenter of `AdjoinOdd ε` is
exactly `K·1`: the odd generator fails the Koszul rule against itself. -/
theorem isSuperCentral [Invertible (2 : K)] (hε : ε ≠ 0) :
    IsSuperCentral (grading ε) := by
  constructor
  rw [superCenter, sup_le_iff]
  constructor
  · rintro z ⟨hz0, -⟩
    rw [mem_grading_zero] at hz0
    exact ⟨ev ε z, ext ε (by simp) (by simp [hz0])⟩
  · rintro z ⟨hz1, hzc⟩
    rw [mem_grading_one] at hz1
    have h := hzc.odd_anticomm (grading ε) (e_mem_grading_one ε)
    have hev := congrArg (ev ε) h
    simp only [ev_mul, ev_e, od_e, map_neg, hz1] at hev
    -- `hev : ε · od z = −(ε · od z)`, so `2 ε (od z) = 0`.
    have h2 : (2 : K) * (ε * od ε z) = 0 := by linear_combination hev
    have hz : od ε z = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (Invertible.ne_zero (2 : K))
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hε
        · exact h'
    have : z = 0 := ext ε (by simp [hz1]) (by simp [hz])
    rw [this]
    exact zero_mem _

/-- For `ε ≠ 0` the superalgebra `AdjoinOdd ε` is graded-simple: a
homogeneous two-sided ideal containing a nonzero homogeneous element
contains a unit. -/
theorem isGradedSimple (hε : ε ≠ 0) : IsGradedSimple (grading ε) := by
  constructor
  intro I hI
  rw [or_iff_not_imp_left]
  intro hne
  have hex : ∃ x, x ∈ I ∧ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine SetLike.ext fun y => ?_
    rw [TwoSidedIdeal.mem_bot (AdjoinOdd ε)]
    exact ⟨fun hy => hcon y hy, fun hy => hy ▸ I.zero_mem⟩
  obtain ⟨x, hxI, hx0⟩ := hex
  -- an even member with nonzero coordinate forces `I = ⊤`
  have keyEven : ∀ a : K, a ≠ 0 → mk ε a 0 ∈ I → I = ⊤ := by
    intro a ha hmem
    have heq : mk ε a⁻¹ 0 * mk ε a 0 = 1 :=
      ext ε (by simp [inv_mul_cancel₀ ha]) (by simp)
    have h1 : (1 : AdjoinOdd ε) ∈ I := by
      have := I.mul_mem_left (mk ε a⁻¹ 0) _ hmem
      rwa [heq] at this
    refine SetLike.ext fun y => ?_
    refine ⟨fun _ => TwoSidedIdeal.mem_top (AdjoinOdd ε), fun _ => ?_⟩
    have := I.mul_mem_left y _ h1
    rwa [mul_one] at this
  have h0 : mk ε (ev ε x) 0 ∈ I := by
    have := hI x hxI 0
    rwa [decompose_zero_coe] at this
  have h1 : mk ε 0 (od ε x) ∈ I := by
    have := hI x hxI 1
    rwa [decompose_one_coe] at this
  by_cases hev : ev ε x = 0
  · have hod : od ε x ≠ 0 := fun h =>
      hx0 (ext ε (by simp [hev]) (by simp [h]))
    have hmul : e ε * mk ε 0 (od ε x) = mk ε (ε * od ε x) 0 :=
      ext ε (by simp) (by simp)
    have hIe : mk ε (ε * od ε x) 0 ∈ I := by
      rw [← hmul]
      exact I.mul_mem_left _ _ h1
    exact keyEven _ (mul_ne_zero hε hod) hIe
  · exact keyEven _ hev h0

/-- **Wall's criterion for `AdjoinOdd ε`** (M7a): for `ε ≠ 0` the
rank-one Clifford superalgebra is super-Azumaya — the first concrete
model of the M1–M4 framework. -/
theorem isSuperAzumaya [Invertible (2 : K)] (hε : ε ≠ 0) :
    IsSuperAzumaya (grading ε) := by
  haveI := isSuperCentral ε hε
  haveI := isGradedSimple ε hε
  exact isSuperAzumaya_of_central_simple (grading ε)

end Field

section Real

/-- `D₊₁ = ℝ ⊕ ℝe`, `e² = 1`, is a central simple superalgebra: the
Brauer–Wall class `+1 ∈ BW(ℝ) ≅ ℤ/8` (§2.2). -/
theorem isSuperAzumaya_one_real : IsSuperAzumaya (grading (1 : ℝ)) := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact isSuperAzumaya (1 : ℝ) one_ne_zero

/-- `D₋₁ = ℝ ⊕ ℝe`, `e² = −1`, is a central simple superalgebra: the
Brauer–Wall class `−1 ∈ BW(ℝ) ≅ ℤ/8` (§2.2). -/
theorem isSuperAzumaya_neg_one_real :
    IsSuperAzumaya (grading (-1 : ℝ)) := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact isSuperAzumaya (-1 : ℝ) (neg_ne_zero.mpr one_ne_zero)

end Real

end AdjoinOdd

end Superfusion

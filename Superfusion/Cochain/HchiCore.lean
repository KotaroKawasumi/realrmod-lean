/-
Superfusion / Cochain / HchiCore

Scratch development of the degree-four cochain calculus needed by
`GaugeChi/HchiProto.lean`.
-/
import Superfusion.Cochain.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Superfusion

universe u v w

variable {G : Type u} [Group G]
variable {M : Type v} [CommGroup M]
variable {N : Type w} [CommGroup N]

/-! ## 1. Degree-four multiplicative cochain calculus -/

/-- Bridge: `dm₄` is the additive `d₄` transported along `Additive`. -/
theorem dm₄_eq_toMul_d₄ (f : G → G → G → G → M) (a b c d e : G) :
    dm₄ f a b c d e =
      Additive.toMul (d₄ (fun x y z w => Additive.ofMul (f x y z w)) a b c d e) := by
  simp only [dm₄, d₄, toMul_sub, toMul_add, div_eq_mul_inv]
  rfl

/-- `δδ = 1` in degree four: coboundaries of 3-cochains are 4-cocycles. -/
theorem dm₄_dm₃ (f : G → G → G → M) (a b c d e : G) : dm₄ (dm₃ f) a b c d e = 1 := by
  rw [dm₄_eq_toMul_d₄]
  have h : (fun x y z w => Additive.ofMul (dm₃ f x y z w)) =
      d₃ (fun x y z => Additive.ofMul (f x y z)) := by
    funext x y z w
    rw [dm₃_eq_toMul_d₃]
    simp
  rw [h, d₄_d₃]
  simp

/-- `dm₄` of a pointwise product. -/
theorem dm₄_mul (f g : G → G → G → G → M) (a b c d e : G) :
    dm₄ (fun x y z w => f x y z w * g x y z w) a b c d e
      = dm₄ f a b c d e * dm₄ g a b c d e := by
  simp only [dm₄, mul_inv]
  group
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- `dm₄` of a pointwise inverse. -/
theorem dm₄_inv (f : G → G → G → G → M) (a b c d e : G) :
    dm₄ (fun x y z w => (f x y z w)⁻¹) a b c d e = (dm₄ f a b c d e)⁻¹ := by
  simp only [dm₄, mul_inv, inv_inv]

/-- Monoid homomorphisms commute with `dm₄`. -/
theorem map_dm₄ (φ : M →* N) (f : G → G → G → G → M) (a b c d e : G) :
    φ (dm₄ f a b c d e) = dm₄ (fun x y z w => φ (f x y z w)) a b c d e := by
  simp [dm₄, map_mul, map_inv]

/-- Monoid homomorphisms commute with `dm₃` (companion of `map_dm₄`). -/
theorem map_dm₃' (φ : M →* N) (f : G → G → G → M) (a b c d : G) :
    φ (dm₃ f a b c d) = dm₃ (fun x y z => φ (f x y z)) a b c d := by
  simp [dm₃, map_mul, map_inv]

/-! ## 2. Averaging: degree-four cocycles over a finite group split off an
`|G|`-th power. -/

/-- **The averaging identity.**  For a 4-cocycle `f` on a finite group, the
"norm" 3-cochain `T(x,y,z) = ∏_g f(x,y,z,g)` has `δT = f^{|G|}`. -/
theorem dm₃_prod_eq_pow [Fintype G] (f : G → G → G → G → M)
    (hf : ∀ x y z w v, dm₄ f x y z w v = 1) (a b c d : G) :
    dm₃ (fun x y z => ∏ g : G, f x y z g) a b c d = f a b c d ^ Fintype.card G := by
  have hshift : (∏ g : G, f a b c (d * g)) = ∏ g : G, f a b c g :=
    Fintype.prod_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)
  have h1 : (∏ g : G, dm₄ f a b c d g) = 1 := by simp [hf]
  simp only [dm₄, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const,
    Finset.card_univ, hshift] at h1
  rw [dm₃]
  exact mul_inv_eq_one.mp h1

/-- **Vanishing of degree-four cohomology with uniquely `|G|`-divisible
coefficients.**  If the coefficient group admits a homomorphic `|G|`-th root,
every 4-cocycle is a coboundary. -/
theorem exists_dm₃_of_dm₄_eq_one [Fintype G] (rt : M →* M)
    (hrt : ∀ x : M, rt x ^ Fintype.card G = x)
    (f : G → G → G → G → M) (hf : ∀ x y z w v, dm₄ f x y z w v = 1) :
    ∃ γ : G → G → G → M, ∀ a b c d, f a b c d = dm₃ γ a b c d := by
  refine ⟨fun x y z => rt (∏ g : G, f x y z g), fun a b c d => ?_⟩
  rw [← map_dm₃' rt (fun x y z => ∏ g : G, f x y z g) a b c d,
    dm₃_prod_eq_pow f hf a b c d, map_pow, hrt]

/-! ## 3. The two coefficient groups: `Multiplicative ℝ` and `ℝˣ` -/

/-- Division by `n` as an endomorphism of `Multiplicative ℝ`. -/
noncomputable def realDivHom (n : ℕ) : Multiplicative ℝ →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x / n)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, add_div]
    rfl

theorem realDivHom_pow (n : ℕ) (hn : n ≠ 0) (x : Multiplicative ℝ) :
    realDivHom n x ^ n = x := by
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine Multiplicative.toAdd.injective ?_
  simp only [realDivHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_pow, toAdd_ofAdd,
    nsmul_eq_mul]
  field_simp

/-- `exp` as a homomorphism from the additive reals into `ℝˣ`. -/
noncomputable def expUnits : Multiplicative ℝ →* ℝˣ where
  toFun t := Units.mk0 (Real.exp (Multiplicative.toAdd t)) (Real.exp_ne_zero _)
  map_one' := by ext; simp
  map_mul' s t := by ext; simp [Real.exp_add]

@[simp] theorem expUnits_val (t : Multiplicative ℝ) :
    ((expUnits t : ℝˣ) : ℝ) = Real.exp (Multiplicative.toAdd t) := rfl

theorem expUnits_injective : Function.Injective (expUnits : Multiplicative ℝ → ℝˣ) := by
  intro s t h
  have : Real.exp (Multiplicative.toAdd s) = Real.exp (Multiplicative.toAdd t) := by
    simpa using congrArg (fun u : ℝˣ => (u : ℝ)) h
  exact Multiplicative.toAdd.injective (Real.exp_injective this)

/-- Every positive unit is an exponential. -/
theorem expUnits_surjective_on_pos {x : ℝˣ} (hx : 0 < (x : ℝ)) :
    expUnits (Multiplicative.ofAdd (Real.log (x : ℝ))) = x :=
  Units.ext (by simpa using Real.exp_log hx)

/-- **Positive-valued 4-cocycles are coboundaries** (no hypothesis on `|G|`:
the positive reals are uniquely divisible). -/
theorem exists_dm₃_of_pos [Fintype G] (r : G → G → G → G → ℝˣ)
    (hr : ∀ a b c d e, dm₄ r a b c d e = 1)
    (hpos : ∀ a b c d, 0 < ((r a b c d : ℝˣ) : ℝ)) :
    ∃ γ : G → G → G → ℝˣ, ∀ a b c d, r a b c d = dm₃ γ a b c d := by
  set f : G → G → G → G → Multiplicative ℝ :=
    fun a b c d => Multiplicative.ofAdd (Real.log ((r a b c d : ℝˣ) : ℝ)) with hfdef
  have hrf : ∀ a b c d, expUnits (f a b c d) = r a b c d := fun a b c d =>
    expUnits_surjective_on_pos (hpos a b c d)
  have hfc : ∀ a b c d e, dm₄ f a b c d e = 1 := by
    intro a b c d e
    refine expUnits_injective ?_
    rw [map_dm₄ expUnits f]
    simp only [hrf, map_one]
    exact hr a b c d e
  obtain ⟨γ, hγ⟩ := exists_dm₃_of_dm₄_eq_one (realDivHom (Fintype.card G))
    (fun x => realDivHom_pow _ Fintype.card_ne_zero x) f hfc
  refine ⟨fun x y z => expUnits (γ x y z), fun a b c d => ?_⟩
  rw [← map_dm₃' expUnits γ a b c d, ← hγ a b c d, hrf]

/-! ## 4. The sign character of `ℝˣ` -/

/-- The sign of a real unit, as a parity. -/
noncomputable def rsgn (x : ℝˣ) : ZMod 2 := if 0 < (x : ℝ) then 0 else 1

theorem rsgn_eq_zero_iff (x : ℝˣ) : rsgn x = 0 ↔ 0 < (x : ℝ) := by
  unfold rsgn
  split_ifs with h
  · simp [h]
  · exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

theorem rsgn_mul (x y : ℝˣ) : rsgn (x * y) = rsgn x + rsgn y := by
  have hx := x.ne_zero
  have hy := y.ne_zero
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy' <;>
    simp only [rsgn, Units.val_mul] <;>
    [ (rw [if_pos (mul_pos_of_neg_of_neg hx' hy'), if_neg (by linarith),
         if_neg (by linarith)]);
      (rw [if_neg (by nlinarith), if_neg (by linarith), if_pos hy']);
      (rw [if_neg (by nlinarith), if_pos hx', if_neg (by linarith)]);
      (rw [if_pos (mul_pos hx' hy'), if_pos hx', if_pos hy']) ] <;> decide

/-- `rsgn` as a homomorphism into `Multiplicative (ZMod 2)`. -/
noncomputable def rsgnHom : ℝˣ →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (rsgn x)
  map_one' := by simp [rsgn]
  map_mul' x y := by simp [rsgn_mul]

@[simp] theorem rsgn_sgn (i : ZMod 2) : rsgn (sgn i : ℝˣ) = i := by
  rcases zmod2_cases i with h | h <;> subst h <;>
    simp [rsgn, sgn, units_sign_eq]

theorem sgn_val_pos_iff (i : ZMod 2) : 0 < ((sgn i : ℝˣ) : ℝ) ↔ i = 0 := by
  rcases zmod2_cases i with h | h <;> subst h <;> simp [sgn, units_sign_eq]

/-- **The splitting lemma.**  A `ℝˣ`-valued 4-cocycle on a finite group whose
sign cochain is a coboundary is itself a coboundary. -/
theorem exists_dm₃_of_sign_coboundary [Fintype G] (r : G → G → G → G → ℝˣ)
    (hr : ∀ a b c d e, dm₄ r a b c d e = 1)
    (u : G → G → G → ZMod 2)
    (hu : ∀ a b c d, rsgn (r a b c d) = d₃ u a b c d) :
    ∃ γ : G → G → G → ℝˣ, ∀ a b c d, r a b c d = dm₃ γ a b c d := by
  set γ₁ : G → G → G → ℝˣ := fun x y z => (sgn (u x y z) : ℝˣ) with hγ₁
  have hdm : ∀ a b c d, dm₃ γ₁ a b c d = (sgn (d₃ u a b c d) : ℝˣ) := by
    intro a b c d
    simp only [hγ₁, dm₃, d₃, sgn_sub, sgn_add, sgn_inv]
  have hr'c : ∀ a b c d e,
      dm₄ (fun x y z w => r x y z w * (dm₃ γ₁ x y z w)⁻¹) a b c d e = 1 := by
    intro a b c d e
    rw [dm₄_mul, dm₄_inv, dm₄_dm₃, hr]
    simp
  have hr'pos : ∀ a b c d, 0 < ((r a b c d * (dm₃ γ₁ a b c d)⁻¹ : ℝˣ) : ℝ) := by
    intro a b c d
    rw [← rsgn_eq_zero_iff, rsgn_mul, hu a b c d, hdm]
    rw [sgn_inv, rsgn_sgn]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨γ₂, hγ₂⟩ :=
    exists_dm₃_of_pos (fun x y z w => r x y z w * (dm₃ γ₁ x y z w)⁻¹) hr'c hr'pos
  refine ⟨fun x y z => γ₂ x y z * γ₁ x y z, fun a b c d => ?_⟩
  have h2 := hγ₂ a b c d
  rw [dm₃_mul, ← h2]
  exact (inv_mul_cancel_right _ _).symm

/-! ## 5. `sgn`-cochains and the parity of a real cocycle -/

section SgnCochain

variable [GroupSign M]

/-- `dm₃` of a `sgn`-cochain is the `sgn` of `d₃`. -/
theorem dm₃_sgn (u : G → G → G → ZMod 2) (a b c d : G) :
    dm₃ (fun x y z => (sgn (u x y z) : M)) a b c d = sgn (d₃ u a b c d) := by
  simp only [dm₃, d₃, sgn_sub, sgn_add, sgn_inv]

/-- `dm₄` of a `sgn`-cochain is the `sgn` of `d₄`. -/
theorem dm₄_sgn (u : G → G → G → G → ZMod 2) (a b c d e : G) :
    dm₄ (fun x y z w => (sgn (u x y z w) : M)) a b c d e = sgn (d₄ u a b c d e) := by
  simp only [dm₄, d₄, sgn_sub, sgn_add, sgn_inv]

end SgnCochain

@[simp] theorem rsgn_one : rsgn (1 : ℝˣ) = 0 := by simp [rsgn]

@[simp] theorem rsgn_inv (x : ℝˣ) : rsgn x⁻¹ = rsgn x := by
  have h : rsgn x + rsgn x⁻¹ = 0 := by
    rw [← rsgn_mul, mul_inv_cancel, rsgn_one]
  have : ∀ p q : ZMod 2, p + q = 0 → q = p := by decide
  exact this _ _ h

private theorem zmod2_sub_eq_add' : ∀ p q : ZMod 2, p - q = p + q := by decide

/-- The parity cochain of a `ℝˣ`-valued 4-cocycle is an `F₂`-valued
4-cocycle. -/
theorem d₄_rsgn_eq_zero (r : G → G → G → G → ℝˣ)
    (hr : ∀ a b c d e, dm₄ r a b c d e = 1) (a b c d e : G) :
    d₄ (fun x y z w => rsgn (r x y z w)) a b c d e = 0 := by
  have h := congrArg rsgn (hr a b c d e)
  simp only [dm₄, rsgn_mul, rsgn_inv, rsgn_one] at h
  simpa only [d₄, zmod2_sub_eq_add'] using h

end Superfusion

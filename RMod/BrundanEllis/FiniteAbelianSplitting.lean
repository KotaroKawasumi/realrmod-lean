import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-! A finite abelian quotient splits when every cyclic generator has a lift
annihilated by the same order.  The final equivalence fixes the kernel pointwise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking

/-- A cyclic homomorphism specified by an element annihilated by n. -/
def cyclicLift {A : Type*} [CommGroup A] (n : ℕ) (a : A) (ha : a ^ n = 1) :
    Multiplicative (ZMod n) →* A :=
  (ZMod.lift n ⟨zmultiplesHom (Additive A) (Additive.ofMul a), by
    simpa using congrArg Additive.ofMul ha⟩).toMultiplicativeLeft

theorem cyclicLift_generator {A : Type*} [CommGroup A] (n : ℕ) (a : A) (ha : a ^ n = 1) :
    cyclicLift n a ha (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  let f : { f : ℤ →+ Additive A // f n = 0 } :=
    ⟨zmultiplesHom (Additive A) (Additive.ofMul a), by
      simpa using congrArg Additive.ofMul ha⟩
  change Additive.toMul (ZMod.lift n f (1 : ZMod n)) = a
  have hf : ZMod.lift n f (1 : ZMod n) = f.val 1 := by
    simpa only [Int.cast_one] using ZMod.lift_coe n f (1 : ℤ)
  rw [hf]
  simp [f]

/-- A homomorphism from a cyclic group is determined by its generator. -/
theorem cyclicHom_ext {A : Type*} [CommGroup A] (n : ℕ)
    (f g : Multiplicative (ZMod n) →* A)
    (h : f (Multiplicative.ofAdd (1 : ZMod n)) = g (Multiplicative.ofAdd (1 : ZMod n))) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  have hx : x = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
    apply Multiplicative.toAdd.injective
    simpa using hk.symm
  rw [hx, map_zpow, map_zpow, h]

/-- The finite abelian structure theorem assembles order-compatible cyclic lifts. -/
theorem exists_section_of_cyclic_lifts {A B : Type*} [CommGroup A] [CommGroup B] [Finite B]
    (f : A →* B)
    (h : ∀ b : B, ∀ n : ℕ, b ^ n = 1 → ∃ a : A, f a = b ∧ a ^ n = 1) :
    ∃ s : B →* A, Function.RightInverse s f := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite B
  let M := fun i : ι => Multiplicative (ZMod (n i))
  let j := fun i => MonoidHom.mulSingle M i
  let b := fun i => e.symm ((j i) (Multiplicative.ofAdd (1 : ZMod (n i))))
  have hb (i : ι) : b i ^ n i = 1 := by
    change (e.symm.toMonoidHom.comp (j i)) (Multiplicative.ofAdd (1 : ZMod (n i))) ^ n i = 1
    rw [← map_pow]
    have hz : Multiplicative.ofAdd (1 : ZMod (n i)) ^ n i = 1 := by
      apply Multiplicative.toAdd.injective
      simp
    rw [hz, map_one]
  choose a ha hp using fun i => h (b i) (n i) (hb i)
  let L := fun i => cyclicLift (n i) (a i) (hp i)
  have hL (i : ι) : f.comp (L i) = e.symm.toMonoidHom.comp (j i) := by
    apply cyclicHom_ext
    change f (cyclicLift (n i) (a i) (hp i) (Multiplicative.ofAdd (1 : ZMod (n i)))) = b i
    rw [cyclicLift_generator]
    exact ha i
  let S : (∀ i, M i) →* A := {
    toFun := fun x => ∏ i, L i (x i)
    map_one' := by simp
    map_mul' := by intro x y; simp [Finset.prod_mul_distrib] }
  refine ⟨S.comp e.toMonoidHom, ?_⟩
  intro x
  change f (∏ i, L i (e x i)) = x
  rw [map_prod]
  simp only [show ∀ i y, f (L i y) = e.symm (j i y) from
    fun i y => congrArg (fun F : M i →* B => F y) (hL i)]
  rw [← map_prod]
  simp only [j, MonoidHom.mulSingle_apply, Finset.univ_prod_mulSingle, e.symm_apply_apply]

/-- A section of a homomorphism of abelian groups gives the specified kernel decomposition. -/
def splitOfSection {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (s : B →* A) (hs : Function.RightInverse s f) : A ≃* (B × f.ker) where
  toFun a := (f a, ⟨a * (s (f a))⁻¹, by
    change f (a * (s (f a))⁻¹) = 1
    rw [map_mul, map_inv, hs (f a), mul_inv_cancel]⟩)
  invFun b := s b.1 * b.2
  left_inv a := by simp only [mul_comm (s (f a)), mul_assoc, inv_mul_cancel, mul_one]
  right_inv b := by
    rcases b with ⟨b, k⟩
    have hk : f (k : A) = 1 := k.property
    apply Prod.ext
    · change f (s b * (k : A)) = b
      rw [map_mul, hs b, hk, mul_one]
    · apply Subtype.ext
      change s b * (k : A) * (s (f (s b * (k : A))))⁻¹ = k
      rw [map_mul, hs b, hk, mul_one]
      rw [mul_comm (s b) (k : A), mul_inv_cancel_right]
  map_mul' a b := by
    apply Prod.ext
    · exact f.map_mul a b
    · apply Subtype.ext
      change a * b * (s (f (a * b)))⁻¹ =
        (a * (s (f a))⁻¹) * (b * (s (f b))⁻¹)
      simp only [map_mul, mul_inv_rev]
      ac_rfl

theorem splitOfSection_fst {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (s : B →* A) (hs : Function.RightInverse s f) (a : A) :
    (splitOfSection f s hs a).1 = f a := rfl

theorem splitOfSection_kernel {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (s : B →* A) (hs : Function.RightInverse s f) (a : f.ker) :
    splitOfSection f s hs (a : A) = (1, a) := by
  apply Prod.ext
  · exact a.property
  · apply Subtype.ext
    change (a : A) * (s (f a))⁻¹ = a
    rw [show f (a : A) = 1 from a.property, map_one, inv_one, mul_one]

end RMod.BrundanEllis.Stacking

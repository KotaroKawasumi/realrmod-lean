/-
Superfusion / Super / QuaternionObstruction

Milestone M7f-5b-2/5c: **the quaternion class is nontrivial and the
Bott period is exactly 8**.

There is no ℝ-algebra isomorphism `M_N(ℍ) ≅ M_M(ℝ)` (`N, M ≥ 1`):
pulling the real column module back along such an isomorphism gives
a simple module `V` over `L := M_N(ℍ)`; the quaternion column
module `W` is also simple, so by isotypicity of the simple artinian
ring `L` (the M5 product trick) there is an `L`-equivalence
`φ : V ≃ W`.  Conjugating by `φ`, every `L`-endomorphism of `W`
corresponds to an endomorphism of the REAL column module, which is
a real scalar (M7f-5b-1) — but right multiplication by the
quaternion `i` is an `L`-endomorphism of `W` that is not a real
scalar.  Contradiction.

Hence `[ℍ] ≠ 1` in `BW(ℝ)`, so `[D₁]⁴ = [ℍ] ≠ 1` (M7f-5a), and
with `[D₁]⁸ = 1` (M7f-4d) the order of `[D₁]` is **exactly 8**:
the classes `[D₀], …, [D₇]` are pairwise distinct — the
ℝ-specific half of `BW(ℝ) ≅ ℤ/8`.
-/
import Superfusion.Super.ColumnModule
import Superfusion.Super.QuaternionTower
import Superfusion.Super.BWGenerator
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix

namespace Superfusion

open Module
open Quaternion
open Matrix

/-! ### No isomorphism `M_N(ℍ) ≅ M_M(ℝ)` -/

section NoIso

variable {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable [Fintype m] [DecidableEq m] [Nonempty m]

/-- The quaternion unit `i`, named once so it is elaborated against
`ℍ[ℝ]` exactly once (an inline anonymous-constructor literal
`⟨0,1,0,0⟩` repeated at several call sites can be elaborated against
the underlying `QuaternionAlgebra` structure instead, producing
spurious type mismatches). -/
private def qIR : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- `ℝ`-scalars on `ℍ[ℝ]` commute with left multiplication by `ℍ[ℝ]`
itself: the `Algebra ℝ ℍ[ℝ]`-derived scalar tower, constructed by
hand since `ℍ[ℝ]` carries a second (defeq but not syntactically
equal) componentwise `SMul ℝ ℍ[ℝ]` instance that makes plain
typeclass search for `IsScalarTower ℝ ℍ[ℝ] ℍ[ℝ]` diverge into an
unrelated `RCLike`/`NormedField` instance chain. -/
theorem isScalarTower_real_quaternion : IsScalarTower ℝ ℍ[ℝ] ℍ[ℝ] where
  smul_assoc r a x := by
    ext <;> simp <;> ring

omit [DecidableEq n] [Nonempty n] in
/-- The real scalar tower on `Matrix n n ℍ[ℝ]` acting on itself,
built from `isScalarTower_real_quaternion` (again bypassing the
diamond-poisoned typeclass search). -/
theorem isScalarTower_real_matrix_quaternion :
    IsScalarTower ℝ (Matrix n n ℍ[ℝ]) (Matrix n n ℍ[ℝ]) :=
  @Matrix.Semiring.isScalarTower n ℝ ℍ[ℝ] _ _ _ _
    isScalarTower_real_quaternion

omit [Nonempty n] in
/-- The real scalar tower on `Matrix n n ℍ[ℝ]` acting on the
quaternion column module `n → ℍ[ℝ]` via `mulVec`. -/
theorem isScalarTower_real_matrix_quaternion_col :
    IsScalarTower ℝ (Matrix n n ℍ[ℝ]) (n → ℍ[ℝ]) where
  smul_assoc r A v := by
    show (r • A) *ᵥ v = r • (A *ᵥ v)
    funext i
    show (∑ j, (r • A) i j * v j) = r • (∑ j, A i j * v j)
    simp only [Matrix.smul_apply]
    rw [Finset.smul_sum]
    congr 1
    funext j
    exact isScalarTower_real_quaternion.smul_assoc r (A i j) (v j)

/-- **The Brauer obstruction** (M7f-5b): there is no ℝ-algebra
isomorphism between a quaternion matrix algebra and a real matrix
algebra. -/
theorem no_matrix_quaternion_iso_matrix_real
    (e : Matrix n n ℍ[ℝ] ≃ₐ[ℝ] Matrix m m ℝ) : False := by
  classical
  haveI := isScalarTower_real_quaternion
  haveI := isScalarTower_real_matrix_quaternion (n := n)
  haveI := isScalarTower_real_matrix_quaternion_col (n := n)
  -- V := the real column module, pulled back to an L-module along e
  letI instV : Module (Matrix n n ℍ[ℝ]) (m → ℝ) :=
    Module.compHom (m → ℝ) e.toAlgHom.toRingHom
  have hsmulV : ∀ (l : Matrix n n ℍ[ℝ]) (x : m → ℝ),
      l • x = e l • x := fun _ _ => rfl
  -- V is a simple L-module (transfer along e)
  haveI hVsimple : IsSimpleModule (Matrix n n ℍ[ℝ]) (m → ℝ) := by
    haveI hcol : IsSimpleModule (Matrix m m ℝ) (m → ℝ) :=
      isSimpleModule_column
    refine { toNontrivial := ?_, eq_bot_or_eq_top := fun S => ?_ }
    · refine ⟨⊥, ⊤, fun h => ?_⟩
      have h1 : (Pi.single (Classical.arbitrary m) 1 : m → ℝ) ∈
          (⊥ : Submodule (Matrix n n ℍ[ℝ]) (m → ℝ)) :=
        h ▸ Submodule.mem_top
      simp only [Submodule.mem_bot] at h1
      have h2 := congr_fun h1 (Classical.arbitrary m)
      rw [Pi.single_eq_same, Pi.zero_apply] at h2
      exact one_ne_zero h2
    · -- the same carrier is an R'-submodule
      let S' : Submodule (Matrix m m ℝ) (m → ℝ) :=
        { carrier := S
          add_mem' := S.add_mem
          zero_mem' := S.zero_mem
          smul_mem' := fun a x hx => by
            have ha : a • x = e (e.symm a) • x := by
              rw [AlgEquiv.apply_symm_apply]
            rw [ha, ← hsmulV]
            exact S.smul_mem _ hx }
      rcases hcol.eq_bot_or_eq_top S' with h | h
      · left
        rw [Submodule.eq_bot_iff]
        intro x hx
        have hx' : x ∈ S' := hx
        rw [h] at hx'
        exact (Submodule.mem_bot _).mp hx'
      · right
        rw [Submodule.eq_top_iff']
        intro x
        have hx' : x ∈ S' := h ▸ Submodule.mem_top
        exact hx'
  -- W := the quaternion column module, simple
  haveI hWsimple :
      IsSimpleModule (Matrix n n ℍ[ℝ]) (n → ℍ[ℝ]) :=
    isSimpleModule_column
  -- L is simple artinian
  haveI : IsArtinianRing (Matrix n n ℍ[ℝ]) :=
    IsArtinianRing.of_finite ℝ _
  -- the L-equivalence V ≃ W by isotypicity (the M5 product trick)
  obtain ⟨φ⟩ :
      Nonempty ((m → ℝ) ≃ₗ[Matrix n n ℍ[ℝ]] (n → ℍ[ℝ])) := by
    haveI h1 : IsSimpleModule (Matrix n n ℍ[ℝ])
        (Submodule.fst (Matrix n n ℍ[ℝ]) (m → ℝ) (n → ℍ[ℝ])) :=
      (Submodule.fstEquiv (Matrix n n ℍ[ℝ]) (m → ℝ)
        (n → ℍ[ℝ])).isSimpleModule_iff.mpr hVsimple
    haveI h2 : IsSimpleModule (Matrix n n ℍ[ℝ])
        (Submodule.snd (Matrix n n ℍ[ℝ]) (m → ℝ) (n → ℍ[ℝ])) :=
      (Submodule.sndEquiv (Matrix n n ℍ[ℝ]) (m → ℝ)
        (n → ℍ[ℝ])).isSimpleModule_iff.mpr hWsimple
    obtain ⟨eq⟩ := IsSimpleRing.isIsotypic
      (R := Matrix n n ℍ[ℝ]) ((m → ℝ) × (n → ℍ[ℝ]))
      (Submodule.snd (Matrix n n ℍ[ℝ]) (m → ℝ) (n → ℍ[ℝ]))
      (Submodule.fst (Matrix n n ℍ[ℝ]) (m → ℝ) (n → ℍ[ℝ]))
    exact ⟨((Submodule.fstEquiv (Matrix n n ℍ[ℝ]) (m → ℝ)
        (n → ℍ[ℝ])).symm.trans eq).trans
      (Submodule.sndEquiv (Matrix n n ℍ[ℝ]) (m → ℝ) (n → ℍ[ℝ]))⟩
  -- ℝ-scalars act through L on both sides, so φ is ℝ-linear
  have hRV : ∀ (c : ℝ) (x : m → ℝ),
      (algebraMap ℝ (Matrix n n ℍ[ℝ]) c) • x = c • x := by
    intro c x
    rw [hsmulV, AlgEquiv.commutes, algebraMap_smul]
  have hRW : ∀ (c : ℝ) (w : n → ℍ[ℝ]),
      (algebraMap ℝ (Matrix n n ℍ[ℝ]) c) • w = c • w :=
    fun c w => algebraMap_smul _ c w
  have hφR : ∀ (c : ℝ) (x : m → ℝ), φ (c • x) = c • φ x := by
    intro c x
    rw [← hRV, map_smul, hRW]
  -- right multiplication by the quaternion i, conjugated by φ,
  -- is an endomorphism of the real column module — hence scalar
  set ψ : Module.End (Matrix n n ℍ[ℝ]) (n → ℍ[ℝ]) :=
    rmulEnd ℍ[ℝ] n qIR with hψ
  set χL : (m → ℝ) →ₗ[Matrix n n ℍ[ℝ]] (m → ℝ) :=
    (φ.symm.toLinearMap.comp ψ).comp φ.toLinearMap with hχL
  have hχLapp : ∀ x : m → ℝ, χL x = φ.symm (ψ (φ x)) := fun x => rfl
  set χ : Module.End (Matrix m m ℝ) (m → ℝ) :=
    { toFun := χL
      map_add' := χL.map_add
      map_smul' := fun a x => by
        rw [RingHom.id_apply]
        have ha : ∀ y : m → ℝ, a • y = e (e.symm a) • y := fun y => by
          rw [AlgEquiv.apply_symm_apply]
        rw [ha x, ← hsmulV, map_smul, hsmulV, AlgEquiv.apply_symm_apply] }
    with hχ
  obtain ⟨c, hc⟩ := end_column_eq_smul_id ℝ m χ
  -- transport back: ψ is the real scalar c on W
  have hψc : ∀ w : n → ℍ[ℝ], ψ w = c • w := by
    intro w
    have h1 : χ (φ.symm w) = c • φ.symm w := by
      rw [hc]
      rfl
    have h2 : χ (φ.symm w) = φ.symm (ψ w) := by
      show χL (φ.symm w) = φ.symm (ψ w)
      rw [hχLapp, LinearEquiv.apply_symm_apply]
    have h3 : φ.symm (ψ w) = c • φ.symm w := by rw [← h2, h1]
    have h4 := congrArg φ h3
    rw [LinearEquiv.apply_symm_apply, hφR,
      LinearEquiv.apply_symm_apply] at h4
    exact h4
  -- evaluate at a basis vector: the quaternion i is a real scalar
  have hval := congr_fun (hψc (Pi.single (Classical.arbitrary n) 1))
    (Classical.arbitrary n)
  rw [hψ, rmulEnd_apply] at hval
  simp only [Pi.single_eq_same, one_mul, Pi.smul_apply] at hval
  -- compare imaginary parts: 1 = 0 in ℝ
  have himI := congrArg QuaternionAlgebra.imI hval
  have hqI : qIR.imI = (1 : ℝ) := rfl
  have hc1 : (c • (1 : ℍ[ℝ])).imI = (0 : ℝ) := by simp
  rw [hqI, hc1] at himI
  exact one_ne_zero himI

end NoIso

/-! ### The quaternion class is nontrivial in `BW(ℝ)` -/

/-- **`[ℍ] ≠ 1` in `BW(ℝ)`** (M7f-5b). -/
theorem not_isBWEquivalent_quaternion_base :
    ¬IsBWEquivalent (SuperAlgebra.quaternion ℝ) (SuperAlgebra.base ℝ) := by
  rintro ⟨p, q, r, s, hpq, hrs, ⟨f⟩⟩
  haveI hn : Nonempty (Fin p ⊕ Fin q) := by
    by_cases hp : p = 0
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, by omega⟩⟩
  haveI hm : Nonempty (Fin r ⊕ Fin s) := by
    by_cases hr : r = 0
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, by omega⟩⟩
  exact no_matrix_quaternion_iso_matrix_real f.toAlgEquiv

/-- `[D₁]⁴ ≠ 1`: the fourth floor is not BW-trivial (via M7f-5a). -/
theorem not_isBWEquivalent_tower_four_base :
    ¬IsBWEquivalent (divisionTower (1 : ℝ) 4) (SuperAlgebra.base ℝ) :=
  fun h => not_isBWEquivalent_quaternion_base
    ((isBWEquivalent_tower_four_quaternion ℝ).symm.trans h)

/-! ### The order of `[D₁]` is exactly 8 -/

section OrderEight

theorem bwGenReal_pow_four_ne_one : bwGenReal ^ 4 ≠ 1 := by
  intro h
  have hval : (Units.val bwGenReal : BWMonoid ℝ) ^ 4 = (1 : BWMonoid ℝ) :=
    (Units.val_pow_eq_pow_val bwGenReal 4).symm.trans
      ((congrArg Units.val h).trans (show Units.val (1 : BW ℝ) = 1 from rfl))
  rw [show (Units.val bwGenReal : BWMonoid ℝ)
      = BWMonoid.mk (divisionTower (1 : ℝ) 1) from rfl,
    ← mk_divisionTower_pow, BWMonoid.one_def] at hval
  exact not_isBWEquivalent_tower_four_base
    (BWMonoid.mk_eq_mk_iff.mp hval)

/-- **The order of `[D₁]` in `BW(ℝ)` is exactly 8** (M7f-5): the
Bott period is minimal. -/
theorem orderOf_bwGenReal : orderOf bwGenReal = 8 := by
  have hdvd : orderOf bwGenReal ∣ 8 := orderOf_bwGenReal_dvd_eight
  have hnot : ¬ orderOf bwGenReal ∣ 4 := fun h =>
    bwGenReal_pow_four_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  have hle : orderOf bwGenReal ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : orderOf bwGenReal <;>
    simp_all +decide

/-- **The eight tower classes are pairwise distinct** (thm:bw-group,
the ℝ-specific half): `⟨[D₁]⟩ ≅ ℤ/8` inside `BW(ℝ)`. -/
theorem divisionTower_bw_distinct {a b : ℕ} (ha : a < 8) (hb : b < 8)
    (h : IsBWEquivalent (divisionTower (1 : ℝ) a)
      (divisionTower (1 : ℝ) b)) :
    a = b := by
  have hmk : BWMonoid.mk (divisionTower (1 : ℝ) a)
      = BWMonoid.mk (divisionTower (1 : ℝ) b) :=
    BWMonoid.mk_eq_mk_iff.mpr h
  rw [mk_divisionTower_pow (1 : ℝ) a, mk_divisionTower_pow (1 : ℝ) b] at hmk
  have hu : bwGenReal ^ a = bwGenReal ^ b := by
    refine Units.ext ?_
    have hva : Units.val (bwGenReal ^ a)
        = (Units.val bwGenReal : BWMonoid ℝ) ^ a := Units.val_pow_eq_pow_val _ _
    have hvb : Units.val (bwGenReal ^ b)
        = (Units.val bwGenReal : BWMonoid ℝ) ^ b := Units.val_pow_eq_pow_val _ _
    rw [hva, hvb,
      show (Units.val bwGenReal : BWMonoid ℝ)
        = BWMonoid.mk (divisionTower (1 : ℝ) 1) from rfl]
    exact hmk
  have := pow_injOn_Iio_orderOf (x := bwGenReal)
    (by rwa [orderOf_bwGenReal]) (by rwa [orderOf_bwGenReal]) hu
  exact this

end OrderEight

end Superfusion

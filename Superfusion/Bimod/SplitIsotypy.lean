/-
Superfusion / Bimod / SplitIsotypy

Milestone M8a-8d′-ii (roadmap v3): **the ungraded endgame — split
isotypy**.  General layer: for a `K`-algebra `T` split by an
(ungraded) algebra isomorphism `e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K`
(`n ≠ 0`), `T` is a simple Artinian ring and, over any two simple
`T`-modules, `Hom_T` is at most `1`-dimensional; combined with the
dimension criterion "`finrank K M = n` forces `M ≅ SplitColumn e`",
any two finite-dimensional `T`-modules of `K`-dimension `n` have a
`1`-dimensional `T`-linear `Hom` space.  Chained with
`ParityBridge.lean`'s `gradedHomFSuccEquiv`, this discharges the
"total-dimension hypothesis" consumed by `parityConcentration` from
the (application-layer) fact that `F` splits and the two tower
endpoints have the same `K`-dimension.

1. **Uniqueness of the simple module.** `isSimpleModule_nonempty_linearEquiv`:
   over a simple Artinian ring `T`, any two simple `T`-modules are
   `T`-linearly isomorphic — `T`'s own isotypy
   (`IsSimpleRing.isIsotypic`), transported off the ring via
   `IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`
   (Wedderburn–Artin machinery, `Mathlib.RingTheory.SimpleModule.
   WedderburnArtin`).  **Split simple ring transfer**:
   `isSimpleRing_of_algEquiv_matrix`/`isArtinianRing_of_algEquiv_matrix`
   transfer `IsSimpleRing`/`IsArtinianRing` from `Matrix (Fin n) (Fin n)
   K` (simple since `K` is a division ring, Artinian since `K` is)
   across `e`, and `SplitColumn e := Fin n → K` (a fresh type,
   avoiding a `Module T` instance diamond across distinct splittings)
   carries the `T`-action `t • v = e t *ᵥ v` transported along `e` and
   `Matrix.mulVec`; it is simple by a direct one-matrix argument
   (`SplitColumn.isSimpleModule`, the *split* analogue of
   `ColumnSimple.lean`'s `columnBimodule_irreducible`: over a field
   every nonzero scalar is a unit, so no `IsSuperDivision` hypothesis
   or Koszul-sign bookkeeping is needed) and has `finrank K
   (SplitColumn e) = n` (`SplitColumn.finrank_eq`).

2. **The dimension criterion.** `linearEquiv_splitColumn_of_finrank_eq`:
   a finite-dimensional `T`-module `M` with `finrank K M = n` is
   `T`-linearly isomorphic to `SplitColumn e` — via
   `IsIsotypicOfType.linearEquiv_fun` (`M ≃ₗ[T] Fin k → SplitColumn e`
   for some multiplicity `k`, since every simple submodule of `M` is
   `≅ SplitColumn e` by part 1), the `K`-dimension count `n = k * n`
   already forces `k = 1` from `n ≠ 0` alone (no separate `Nontrivial
   M` hypothesis needed).  Corollary: `isSimpleModule_of_finrank_eq_split`
   transfers simplicity from `SplitColumn e`.

3. **The Hom bound.** `finrank_hom_eq_one`: for finite-dimensional
   `T`-modules `M`, `N` with `finrank K M = finrank K N = n`, the space
   of `T`-linear maps `M →ₗ[T] N` (a `K`-module via the ambient
   `SMulCommClass K T N`, automatic from `IsScalarTower K T N`) has
   `finrank K (M →ₗ[T] N) = 1` — both `M` and `N` are `≅ SplitColumn e`
   by part 2 (`equivArrowOfLinearEquiv`, transported `K`-linearly
   through the conjugation `f ↦ fN ∘ f ∘ fM⁻¹`), reducing to
   `Hom_T (SplitColumn e, SplitColumn e) ≅ K`
   (`SplitColumn.finrank_hom_self_eq_one`: `T` already acts through
   *all* of `Matrix (Fin n) (Fin n) K` via `e`, so a `T`-linear
   endomorphism commutes with every matrix unit, forcing it to be a
   scalar — a direct matrix-unit computation, the split analogue of
   Schur's lemma made concrete).  The route taken for the general
   "uniqueness of simples" fact (deliverable 2's alternative) is
   `IsSimpleRing.isIsotypic` off `Mathlib.RingTheory.SimpleModule.
   WedderburnArtin`, not the Morita/matrix-unit idempotent reduction
   (only the *endomorphism-ring* computation of part 3 uses matrix
   units directly).

4. **The bridge back to `gradedHomF`.** `equivSuperEquivariantZero`:
   for a `T`-grading `𝒯` with `[DirectSum.Decomposition 𝒯]`, the
   `K`-submodule `superEquivariant 𝒯 0` of `M →ₗ[K] N` (plain
   `T`-linearity on homogeneous elements, `mem_superEquivariant_zero_iff`)
   is `K`-linearly equivalent to the literal type `M →ₗ[T] N` (extending
   homogeneous-equivariance to full `T`-linearity by
   `DirectSum.Decomposition.inductionOn 𝒯`, the same induction principle
   `ParityBridge.lean` uses for `parityMap_parityMap`).  Composed with
   `ParityBridge.lean`'s `gradedHomFSuccEquiv` (which identifies
   `gradedHomF 𝒯 1` with `homGrading 1 ⊓ superEquivariant 𝒯 0`, a
   `homGrading`-degree-`1` submodule of the *same* ambient
   `superEquivariant 𝒯 0`) and `ChiAbs.lean`'s `homGrading`-directness,
   `gradedHomF_finrank_sum_le_one` assembles the **total-dimension
   hypothesis** `finrank (gradedHomF 0) + finrank (gradedHomF 1) ≤ 1`
   that `ParityBridge.lean`'s `parityConcentration` consumes, from
   `finrank_hom_eq_one`'s `finrank (M →ₗ[T] N) = 1`: `gradedHomF 0` and
   the reflected `gradedHomF 1` are disjoint `homGrading`-degree-`0`/`1`
   submodules of `superEquivariant 𝒯 0`, so their `finrank`s sum to at
   most `finrank (superEquivariant 𝒯 0) = finrank (M →ₗ[T] N) = 1`
   (`Submodule.finrank_add_finrank_le_of_disjoint`).
-/
import Superfusion.Bimod.ParityBridge
import Superfusion.Bimod.ChiAbs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

open scoped Matrix

namespace Superfusion

namespace Bimod

/-! ### Uniqueness of the simple module over a simple Artinian ring -/

section SimpleUnique

variable {T : Type*} [Ring T] [IsSimpleRing T] [IsArtinianRing T]

/-- **Uniqueness of the simple module.** Over a simple Artinian ring `T`, any two simple
`T`-modules are `T`-linearly isomorphic: both are isomorphic (as `T`-modules) to simple ideals of
`T` (`IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`), and all simple ideals of `T`
are isomorphic to each other (`IsSimpleRing.isIsotypic`, `T`'s own isotypy). -/
theorem isSimpleModule_nonempty_linearEquiv
    {S : Type*} [AddCommGroup S] [Module T S] [IsSimpleModule T S]
    {S' : Type*} [AddCommGroup S'] [Module T S'] [IsSimpleModule T S'] :
    Nonempty (S ≃ₗ[T] S') := by
  obtain ⟨I, ⟨eI⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule T S
  obtain ⟨I', ⟨eI'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule T S'
  haveI : IsSimpleModule T I := .congr eI.symm
  haveI : IsSimpleModule T I' := .congr eI'.symm
  obtain ⟨eII'⟩ := (IsSimpleRing.isIsotypic T T) I I'
  exact ⟨eI.trans (eII'.symm.trans eI'.symm)⟩

end SimpleUnique

/-! ### Split simple ring transfer -/

section SplitSimple

variable {K T : Type*} [Field K] [Ring T] [Algebra K T]
variable {n : ℕ}

/-- `T` is a simple ring when split by a matrix algebra isomorphism (`n ≠ 0`, so the matrix
index type is nonempty): transferred from `IsSimpleRing (Matrix (Fin n) (Fin n) K)` (a division
ring is simple, and the matrix ring over a simple ring is simple) along `e.symm`. -/
theorem isSimpleRing_of_algEquiv_matrix (e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K) (hn : n ≠ 0) :
    IsSimpleRing T := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  haveI : IsSimpleRing (Matrix (Fin n) (Fin n) K) := IsSimpleRing.matrix (Fin n) K
  exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv ‹_›

/-- `T` is an Artinian ring when split by a matrix algebra isomorphism: transferred from
`IsArtinianRing (Matrix (Fin n) (Fin n) K)` (a field is Artinian, and the matrix ring over an
Artinian ring is Artinian) along `e.symm`. -/
theorem isArtinianRing_of_algEquiv_matrix (e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    IsArtinianRing T :=
  RingEquiv.isArtinianRing e.symm.toRingEquiv

end SplitSimple

/-! ### The split column module -/

section SplitColumnDef

variable {K T : Type*} [Field K] [Ring T] [Algebra K T]
variable {n : ℕ}

/-- **The split column module** attached to an (ungraded) splitting `e : T ≃ₐ[K] Matrix (Fin n)
(Fin n) K`: the type `Fin n → K`, kept as a fresh type synonym (rather than registering a `Module
T (Fin n → K)` instance directly) to avoid a `Module T`-instance diamond across distinct
splittings `e`. -/
def SplitColumn (_e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K) : Type _ := Fin n → K

namespace SplitColumn

variable (e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K)

instance : AddCommGroup (SplitColumn e) := Pi.addCommGroup

instance : Module K (SplitColumn e) := Pi.module _ _ _

/-- **Forget the `SplitColumn e` wrapper**: the identity map `SplitColumn e → Fin n → K`, given an
explicit (concrete) `Fin n → K` return type so that any `+`/`•` computed on the result is resolved
using the ordinary `Fin n → K` instances — plain type *ascription* of a bound variable already of
type `SplitColumn e` does not achieve this (typeclass search for `+`/`•` uses the operand's
syntactic/inferred type, which an ascription does not change for an existing free variable), so a
genuine function is needed. -/
def toFun (v : SplitColumn e) : Fin n → K := v

/-- **Wrap a column vector**: the identity map `Fin n → K → SplitColumn e`, the inverse of
`toFun` (see `toFun`'s docstring for why a genuine function, rather than an ascription, is
needed). -/
def ofFun (v : Fin n → K) : SplitColumn e := v

@[simp] theorem toFun_ofFun (v : Fin n → K) : toFun e (ofFun e v) = v := rfl

@[simp] theorem ofFun_toFun (v : SplitColumn e) : ofFun e (toFun e v) = v := rfl

@[simp] theorem toFun_add (v w : SplitColumn e) : toFun e (v + w) = toFun e v + toFun e w := rfl

@[simp] theorem toFun_zero : toFun e (0 : SplitColumn e) = 0 := rfl

@[simp] theorem toFun_smul (c : K) (v : SplitColumn e) : toFun e (c • v) = c • toFun e v := rfl

@[simp] theorem ofFun_add (v w : Fin n → K) : ofFun e (v + w) = ofFun e v + ofFun e w := rfl

@[simp] theorem ofFun_zero : ofFun e (0 : Fin n → K) = 0 := rfl

@[simp] theorem ofFun_smul (c : K) (v : Fin n → K) : ofFun e (c • v) = c • ofFun e v := rfl

/-- **The `T`-action on the split column module**, transported along `e` via `Matrix.mulVec`:
`t • v = ofFun e (e t *ᵥ toFun e v)`.  (`rw`'s automatic closing tactic does not unfold the
semireducible `toFun`/`ofFun`, so each field ends in an explicit application of one of the `rfl`
lemmas above rather than relying on that.) -/
noncomputable instance : Module T (SplitColumn e) where
  smul t v := ofFun e ((e t) *ᵥ toFun e v)
  one_smul v := by
    show ofFun e ((e 1) *ᵥ toFun e v) = v
    rw [map_one, Matrix.one_mulVec]
    exact ofFun_toFun e v
  mul_smul t t' v := by
    show ofFun e ((e (t * t')) *ᵥ toFun e v)
      = ofFun e ((e t) *ᵥ toFun e (ofFun e ((e t') *ᵥ toFun e v)))
    rw [map_mul, ← Matrix.mulVec_mulVec, toFun_ofFun]
  smul_zero t := by
    show ofFun e ((e t) *ᵥ (0 : Fin n → K)) = 0
    rw [Matrix.mulVec_zero]
    exact ofFun_zero e
  smul_add t v w := by
    show ofFun e ((e t) *ᵥ (toFun e v + toFun e w))
      = ofFun e ((e t) *ᵥ toFun e v) + ofFun e ((e t) *ᵥ toFun e w)
    rw [Matrix.mulVec_add]
    exact ofFun_add e _ _
  add_smul t t' v := by
    show ofFun e ((e (t + t')) *ᵥ toFun e v)
      = ofFun e ((e t) *ᵥ toFun e v) + ofFun e ((e t') *ᵥ toFun e v)
    rw [map_add, Matrix.add_mulVec]
    exact ofFun_add e _ _
  zero_smul v := by
    show ofFun e ((e (0 : T)) *ᵥ toFun e v) = 0
    rw [map_zero, Matrix.zero_mulVec]
    exact ofFun_zero e

theorem smul_def (t : T) (v : SplitColumn e) : t • v = ofFun e ((e t) *ᵥ toFun e v) := rfl

instance : IsScalarTower K T (SplitColumn e) where
  smul_assoc c t v := by
    show ofFun e ((e (c • t)) *ᵥ toFun e v) = c • ofFun e ((e t) *ᵥ toFun e v)
    rw [map_smul, Matrix.smul_mulVec]
    exact ofFun_smul e c _

/-- The split column module has `K`-dimension `n`. -/
theorem finrank_eq : Module.finrank K (SplitColumn e) = n := by
  show Module.finrank K (Fin n → K) = n
  exact Module.finrank_fin_fun (R := K)

/-- **The split column module is simple.** Over a field every nonzero scalar is a unit, so given
a nonzero `x`, a component `x k₀ ≠ 0`, and any target `z`, the single matrix with column `k₀`
equal to `z / x k₀` (and all other columns `0`) sends `x` to `z` — the split (field, no grading)
analogue of `ColumnSimple.lean`'s `column_reach`/`columnBimodule_irreducible`. -/
theorem isSimpleModule (hn : n ≠ 0) : IsSimpleModule T (SplitColumn e) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨?_, fun x hx z => ?_⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    exact Function.nontrivial
  · obtain ⟨k₀, hk₀⟩ : ∃ k₀, toFun e x k₀ ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      rw [← ofFun_toFun e x, show toFun e x = 0 from funext h]
      exact ofFun_zero e
    refine ⟨e.symm (Matrix.of fun j k => if k = k₀ then toFun e z j / toFun e x k₀ else 0), ?_⟩
    show ofFun e ((e (e.symm _)) *ᵥ toFun e x) = z
    rw [AlgEquiv.apply_symm_apply]
    have hval : (Matrix.of fun j k => if k = k₀ then toFun e z j / toFun e x k₀ else 0)
        *ᵥ toFun e x = toFun e z := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [show (fun k => (if k = k₀ then toFun e z j / toFun e x k₀ else 0) * toFun e x k)
          = fun k => if k = k₀ then (toFun e z j / toFun e x k₀) * toFun e x k else 0 from by
          funext k
          by_cases hk : k = k₀ <;> simp [hk]]
      rw [Finset.sum_ite_eq' Finset.univ k₀
        (fun k => (toFun e z j / toFun e x k₀) * toFun e x k)]
      simp [div_mul_cancel₀ (toFun e z j) hk₀]
    rw [hval]
    exact ofFun_toFun e z

end SplitColumn

end SplitColumnDef

/-! ### The dimension criterion -/

section DimensionCriterion

variable {K T : Type*} [Field K] [Ring T] [Algebra K T]
variable {n : ℕ} (e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K) (hn : n ≠ 0)
variable {M : Type*} [AddCommGroup M] [Module K M] [Module T M] [IsScalarTower K T M]
variable [Module.Finite K M]

include hn e in
/-- **The dimension criterion**: a finite-dimensional `T`-module `M` with `finrank K M = n` is
`T`-linearly isomorphic to the split column module.  (Every simple submodule of `M` is `≅
SplitColumn e` by `isSimpleModule_nonempty_linearEquiv`, so `M` is isotypic of that type; the
`K`-dimension count `n = k * n` against the multiplicity `k` from
`IsIsotypicOfType.linearEquiv_fun` already forces `k = 1` from `n ≠ 0` alone.) -/
theorem linearEquiv_splitColumn_of_finrank_eq (hM : Module.finrank K M = n) :
    Nonempty (M ≃ₗ[T] SplitColumn e) := by
  haveI := isSimpleRing_of_algEquiv_matrix e hn
  haveI := isArtinianRing_of_algEquiv_matrix e
  haveI : Module.Finite T M := .of_restrictScalars_finite K T M
  haveI : Module.Finite K (SplitColumn e) := inferInstanceAs (Module.Finite K (Fin n → K))
  haveI : Module.Free K (SplitColumn e) := inferInstanceAs (Module.Free K (Fin n → K))
  haveI := SplitColumn.isSimpleModule e hn
  have hiso : IsIsotypicOfType T M (SplitColumn e) :=
    fun _ _ => isSimpleModule_nonempty_linearEquiv
  obtain ⟨k, ⟨f⟩⟩ := hiso.linearEquiv_fun
  have hK : Module.finrank K M = k * Module.finrank K (SplitColumn e) := by
    rw [(f.restrictScalars K).finrank_eq, Module.finrank_pi_fintype K, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hM, SplitColumn.finrank_eq] at hK
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hk1 : k = 1 := Nat.eq_of_mul_eq_mul_right hn_pos (by rw [one_mul]; exact hK.symm)
  subst hk1
  exact ⟨f.trans (LinearEquiv.funUnique (Fin 1) T (SplitColumn e))⟩

include hn e in
/-- **Corollary of the dimension criterion**: a finite-dimensional `T`-module `M` with `finrank K
M = n` is simple (transferring simplicity from `SplitColumn e` along
`linearEquiv_splitColumn_of_finrank_eq`). -/
theorem isSimpleModule_of_finrank_eq_split (hM : Module.finrank K M = n) :
    IsSimpleModule T M := by
  haveI := SplitColumn.isSimpleModule e hn
  obtain ⟨f⟩ := linearEquiv_splitColumn_of_finrank_eq e hn hM
  exact IsSimpleModule.congr f

end DimensionCriterion

/-! ### The Hom bound -/

section HomBound

variable {K T : Type*} [Field K] [Ring T] [Algebra K T]
variable {n : ℕ} (e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K) (hn : n ≠ 0)

include hn in
/-- **Schur, split case**: the `T`-linear endomorphisms of the split column module have
`K`-dimension `1`.  Transporting a `T`-linear `f` along `toFun`/`ofFun` gives a `K`-linear `g` on
`Fin n → K` that commutes with the action of *every* matrix (since `T` acts through all of `Matrix
(Fin n) (Fin n) K` via `e`); the matrix-unit relation `M *ᵥ x = x j • Pi.single i 1` (for `M` the
`(i, j)` matrix unit) then forces `g (Pi.single i 1) = c • Pi.single i 1` for every `i`, with `c :=
g (Pi.single i₀ 1) i₀` at the fixed index `i₀` from `n ≠ 0` — and, by linearity of `g` against the
standard basis `Pi.single i 1`, `g v = c • v` for every `v`. -/
theorem SplitColumn.finrank_hom_self_eq_one :
    Module.finrank K (SplitColumn e →ₗ[T] SplitColumn e) = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  set i₀ : Fin n := Classical.arbitrary (Fin n) with hi₀
  -- the matrix-unit relation, entirely in `Fin n → K`
  have hunit : ∀ (i j : Fin n) (x : Fin n → K),
      (Matrix.of fun a b => if a = i ∧ b = j then (1 : K) else 0) *ᵥ x
        = x j • Pi.single i (1 : K) := by
    intro i j x
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    by_cases ha : a = i
    · subst ha
      rw [show (fun b => (if a = a ∧ b = j then (1 : K) else 0) * x b)
          = fun b => if b = j then x b else 0 from by
          funext b; by_cases hb : b = j <;> simp [hb]]
      rw [Finset.sum_ite_eq' Finset.univ j x]
      simp
    · rw [show (fun b => (if a = i ∧ b = j then (1 : K) else 0) * x b) = fun _ => (0 : K) from by
        funext b; simp [ha]]
      simp [Ne.symm ha]
  refine finrank_eq_one (LinearMap.id : SplitColumn e →ₗ[T] SplitColumn e) ?_ ?_
  · intro h
    have h1 : (SplitColumn.ofFun e (Pi.single i₀ (1 : K)) : SplitColumn e) = 0 :=
      LinearMap.congr_fun h _
    have h2 : (Pi.single i₀ (1 : K) : Fin n → K) = 0 := by
      have h1' := congrArg (SplitColumn.toFun e) h1
      simp at h1'
    simpa using congrFun h2 i₀
  · intro f
    -- transport `f` to a `K`-linear map `g` on `Fin n → K` commuting with every matrix
    let g : (Fin n → K) →ₗ[K] (Fin n → K) :=
      { toFun := fun x => SplitColumn.toFun e (f (SplitColumn.ofFun e x))
        map_add' := fun x y => by
          show SplitColumn.toFun e (f (SplitColumn.ofFun e (x + y)))
            = SplitColumn.toFun e (f (SplitColumn.ofFun e x))
              + SplitColumn.toFun e (f (SplitColumn.ofFun e y))
          rw [show (SplitColumn.ofFun e (x + y) : SplitColumn e)
              = SplitColumn.ofFun e x + SplitColumn.ofFun e y from rfl, map_add]
          exact SplitColumn.toFun_add e _ _
        map_smul' := fun c x => by
          show SplitColumn.toFun e (f (SplitColumn.ofFun e (c • x)))
            = c • SplitColumn.toFun e (f (SplitColumn.ofFun e x))
          rw [show (SplitColumn.ofFun e (c • x) : SplitColumn e) = c • SplitColumn.ofFun e x
              from rfl, LinearMap.map_smul_of_tower f]
          exact SplitColumn.toFun_smul e c _ }
    have hgmat : ∀ (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K), g (M *ᵥ x) = M *ᵥ g x := by
      intro M x
      show SplitColumn.toFun e (f (SplitColumn.ofFun e (M *ᵥ x)))
        = M *ᵥ SplitColumn.toFun e (f (SplitColumn.ofFun e x))
      have hsmul : (e.symm M) • (SplitColumn.ofFun e x) = SplitColumn.ofFun e (M *ᵥ x) := by
        show SplitColumn.ofFun e ((e (e.symm M)) *ᵥ SplitColumn.toFun e (SplitColumn.ofFun e x))
          = SplitColumn.ofFun e (M *ᵥ x)
        rw [AlgEquiv.apply_symm_apply, SplitColumn.toFun_ofFun]
      rw [← hsmul, f.map_smul]
      show SplitColumn.toFun e ((e.symm M) • f (SplitColumn.ofFun e x))
        = M *ᵥ SplitColumn.toFun e (f (SplitColumn.ofFun e x))
      rw [SplitColumn.smul_def, AlgEquiv.apply_symm_apply, SplitColumn.toFun_ofFun]
    set c : K := g (Pi.single i₀ (1 : K)) i₀ with hc
    have hcol : ∀ i : Fin n, g (Pi.single i (1 : K)) = c • Pi.single i (1 : K) := by
      intro i
      have hx : (Pi.single i₀ (1 : K) : Fin n → K) i₀ • Pi.single i (1 : K)
          = Pi.single i (1 : K) := by simp
      calc g (Pi.single i (1 : K))
          = g ((Matrix.of fun a b => if a = i ∧ b = i₀ then (1 : K) else 0)
              *ᵥ Pi.single i₀ (1 : K)) := by rw [hunit i i₀ (Pi.single i₀ (1 : K)), hx]
        _ = (Matrix.of fun a b => if a = i ∧ b = i₀ then (1 : K) else 0) *ᵥ g (Pi.single i₀ (1 : K))
            := hgmat _ _
        _ = (g (Pi.single i₀ (1 : K)) : Fin n → K) i₀ • Pi.single i (1 : K) :=
            hunit i i₀ (g (Pi.single i₀ (1 : K)))
        _ = c • Pi.single i (1 : K) := by rw [hc]
    have hx_eq : ∀ x : Fin n → K, x = ∑ i, x i • Pi.single i (1 : K) := fun x => by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    have key : ∀ x : Fin n → K, g x = c • x := fun x => by
      have hterm : ∀ i : Fin n,
          g (x i • Pi.single i (1 : K)) = c • (x i • Pi.single i (1 : K)) := by
        intro i
        rw [g.map_smul, hcol, smul_smul, smul_smul, mul_comm]
      conv_lhs => rw [hx_eq x]
      rw [map_sum, Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.smul_sum, ← hx_eq x]
    refine ⟨c, ?_⟩
    ext v
    show (c • v : SplitColumn e) = f v
    rw [← SplitColumn.ofFun_toFun e (c • v), ← SplitColumn.ofFun_toFun e (f v)]
    congr 1
    show c • SplitColumn.toFun e v = SplitColumn.toFun e (f v)
    exact (key (SplitColumn.toFun e v)).symm

/-- **The Hom-space conjugation equivalence**: given `T`-linear isomorphisms `M ≃ₗ[T] M'` and `N
≃ₗ[T] N'`, the `T`-linear `Hom`-spaces `M →ₗ[T] N` and `M' →ₗ[T] N'` are `K`-linearly equivalent
via `f ↦ fN ∘ f ∘ fM⁻¹`. -/
noncomputable def equivArrowOfLinearEquiv
    {M M' N N' : Type*} [AddCommGroup M] [Module K M] [Module T M] [IsScalarTower K T M]
    [AddCommGroup M'] [Module K M'] [Module T M'] [IsScalarTower K T M']
    [AddCommGroup N] [Module K N] [Module T N] [IsScalarTower K T N]
    [AddCommGroup N'] [Module K N'] [Module T N'] [IsScalarTower K T N']
    (fM : M ≃ₗ[T] M') (fN : N ≃ₗ[T] N') :
    (M →ₗ[T] N) ≃ₗ[K] (M' →ₗ[T] N') :=
  LinearEquiv.ofLinear
    { toFun := fun f => fN.toLinearMap ∘ₗ f ∘ₗ fM.symm.toLinearMap
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c f => by
        ext x
        show fN (c • f (fM.symm x)) = c • fN (f (fM.symm x))
        exact LinearMapClass.map_smul_of_tower fN c (f (fM.symm x)) }
    { toFun := fun g => fN.symm.toLinearMap ∘ₗ g ∘ₗ fM.toLinearMap
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c g => by
        ext x
        show fN.symm (c • g (fM x)) = c • fN.symm (g (fM x))
        exact LinearMapClass.map_smul_of_tower fN.symm c (g (fM x)) }
    (by ext f x; simp)
    (by ext g x; simp)

include e hn in
/-- **The Hom bound**: for finite-dimensional `T`-modules `M`, `N` of `K`-dimension `n` (both
forced `T`-linearly isomorphic to `SplitColumn e` by `linearEquiv_splitColumn_of_finrank_eq`), the
space of `T`-linear maps `M →ₗ[T] N` has `K`-dimension exactly `1`. -/
theorem finrank_hom_eq_one
    {M N : Type*} [AddCommGroup M] [Module K M] [Module T M] [IsScalarTower K T M]
    [Module.Finite K M] [AddCommGroup N] [Module K N] [Module T N] [IsScalarTower K T N]
    [Module.Finite K N]
    (hM : Module.finrank K M = n) (hN : Module.finrank K N = n) :
    Module.finrank K (M →ₗ[T] N) = 1 := by
  obtain ⟨fM⟩ := linearEquiv_splitColumn_of_finrank_eq e hn hM
  obtain ⟨fN⟩ := linearEquiv_splitColumn_of_finrank_eq e hn hN
  rw [(equivArrowOfLinearEquiv fM fN).finrank_eq, SplitColumn.finrank_hom_self_eq_one e hn]

include e hn in
/-- The `≤ 1` corollary of `finrank_hom_eq_one`. -/
theorem finrank_hom_le_one
    {M N : Type*} [AddCommGroup M] [Module K M] [Module T M] [IsScalarTower K T M]
    [Module.Finite K M] [AddCommGroup N] [Module K N] [Module T N] [IsScalarTower K T N]
    [Module.Finite K N]
    (hM : Module.finrank K M = n) (hN : Module.finrank K N = n) :
    Module.finrank K (M →ₗ[T] N) ≤ 1 :=
  (finrank_hom_eq_one e hn hM hN).le

end HomBound

/-! ### The bridge back to `gradedHomF` -/

section Bridge

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable {N : Type*} [AddCommGroup N] [Module K N]
variable {T : Type*} [Ring T] [Algebra K T]
variable (𝒯 : ZMod 2 → Submodule K T) [DirectSum.Decomposition 𝒯]
variable [Module T M] [Module T N] [IsScalarTower K T M] [IsScalarTower K T N]

omit [DirectSum.Decomposition 𝒯] in
/-- Any `T`-linear map, viewed (via `IsScalarTower K T M/N`) as a `K`-linear map, is
super-equivariant of degree `0` (plainly `T`-linear, `mem_superEquivariant_zero_iff`, not just on
homogeneous elements of `𝒯`). -/
theorem restrictScalars_mem_superEquivariant_zero (g : M →ₗ[T] N) :
    g.restrictScalars K ∈ superEquivariant 𝒯 (M := M) (N := N) 0 := by
  rw [mem_superEquivariant_zero_iff]
  intro i x _ m
  exact g.map_smul x m

/-- Conversely, a `K`-linear map that is super-equivariant of degree `0` (plainly `T`-linear on
homogeneous elements of `𝒯`, `mem_superEquivariant_zero_iff`) extends to a genuine `T`-linear map,
by `DirectSum.Decomposition.inductionOn 𝒯` (the same induction principle `ParityBridge.lean` uses
for `parityMap_parityMap`). -/
noncomputable def toTLinearOfMemSuperEquivariantZero (f : M →ₗ[K] N)
    (hf : f ∈ superEquivariant 𝒯 (M := M) (N := N) 0) : M →ₗ[T] N where
  toFun := f
  map_add' := f.map_add
  map_smul' t m := by
    induction t using DirectSum.Decomposition.inductionOn 𝒯 with
    | zero => simp
    | @homogeneous i x =>
        simp only [RingHom.id_apply]
        exact (mem_superEquivariant_zero_iff 𝒯).mp hf x.2 m
    | add t t' ht ht' =>
        simp only [RingHom.id_apply] at ht ht' ⊢
        rw [add_smul, map_add, ht, ht', add_smul]

/-- **The bridge between plain super-equivariance and literal `T`-linearity**: the degree-`0`
super-equivariant `K`-submodule of `M →ₗ[K] N` is `K`-linearly equivalent to the literal `T`-linear
maps `M →ₗ[T] N`. -/
noncomputable def equivSuperEquivariantZero :
    ↥(superEquivariant 𝒯 (M := M) (N := N) 0) ≃ₗ[K] (M →ₗ[T] N) :=
  LinearEquiv.ofLinear
    { toFun := fun f => toTLinearOfMemSuperEquivariantZero 𝒯 f.1 f.2
      map_add' := fun f g => by ext m; simp [toTLinearOfMemSuperEquivariantZero]
      map_smul' := fun c f => by ext m; simp [toTLinearOfMemSuperEquivariantZero] }
    { toFun := fun g =>
        ⟨g.restrictScalars K, restrictScalars_mem_superEquivariant_zero 𝒯 g⟩
      map_add' := fun f g => by apply Subtype.ext; ext m; simp
      map_smul' := fun c f => by apply Subtype.ext; ext m; simp }
    (by ext g m; simp [toTLinearOfMemSuperEquivariantZero])
    (by ext f m; simp [toTLinearOfMemSuperEquivariantZero])

theorem finrank_superEquivariant_zero_eq :
    Module.finrank K ↥(superEquivariant 𝒯 (M := M) (N := N) 0) = Module.finrank K (M →ₗ[T] N) :=
  (equivSuperEquivariantZero 𝒯).finrank_eq

end Bridge

/-! ### Assembling the total-dimension hypothesis -/

section Assemble

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K M] (ℳ : ZMod 2 → Submodule K M)
  [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] (𝒩 : ZMod 2 → Submodule K N)
  [DirectSum.Decomposition 𝒩]
variable {T : Type*} [Ring T] [Algebra K T]
variable (𝒯 : ZMod 2 → Submodule K T) [DirectSum.Decomposition 𝒯]
variable [Module T M] [Module T N] [IsScalarTower K T M] [IsScalarTower K T N]
variable [SetLike.GradedSMul 𝒯 ℳ]
variable [Module.Finite K M] [Module.Finite K N]

omit [SetLike.GradedSMul 𝒯 ℳ] in
/-- **A submodule sandwiched, disjointly, between two others**: the `finrank`-additivity of a
disjoint pair `A`, `B` sitting inside a common ambient submodule `C` (of a `K`-vector space `V`)
bounds `finrank A + finrank B` by `finrank C` — the general submodule-lattice fact underlying
`gradedHomF_finrank_sum_le_one`. -/
private theorem finrank_add_finrank_le_of_disjoint_of_le {V : Type*} [AddCommGroup V] [Module K V]
    {A B C : Submodule K V} [Module.Finite K ↥A] [Module.Finite K ↥B] [Module.Finite K ↥C]
    (hAC : A ≤ C) (hBC : B ≤ C) (hdisj : Disjoint A B) :
    Module.finrank K ↥A + Module.finrank K ↥B ≤ Module.finrank K ↥C := by
  have heq : Module.finrank K ↥(A ⊔ B) = Module.finrank K ↥A + Module.finrank K ↥B := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    omega
  rw [← heq]
  exact Submodule.finrank_mono (sup_le hAC hBC)

/-- **The total-dimension hypothesis for `parityConcentration`**: under a splitting `e` and the
matching `K`-dimension hypotheses `finrank K M = finrank K N = n`, `finrank (gradedHomF 𝒯 0) +
finrank (gradedHomF 𝒯 1) ≤ 1`.  `gradedHomF ℳ 𝒯 𝒩 0` and (via `finrank_gradedHomF_eq`, reflecting
`gradedHomF ℳ 𝒯 𝒩 1` into its unsigned `homGrading`-degree-`1` companion) `gradedHomF ℳ 𝒯 𝒩 1` sit
as *disjoint* `homGrading`-degree-`0`/`1` submodules of the same ambient `superEquivariant 𝒯 0`
(`homGrading_eq_zero_of_ne`), whose `K`-dimension is `1` by `finrank_hom_eq_one` — so their
`finrank`s sum to at most `1` (`finrank_add_finrank_le_of_disjoint_of_le`). -/
theorem gradedHomF_finrank_sum_le_one
    {n : ℕ} (e : T ≃ₐ[K] Matrix (Fin n) (Fin n) K) (hn : n ≠ 0)
    (hM : Module.finrank K M = n) (hN : Module.finrank K N = n) :
    Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 0) + Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 1) ≤ 1 := by
  have hC : Module.finrank K ↥(superEquivariant 𝒯 (M := M) (N := N) 0) ≤ 1 := by
    rw [finrank_superEquivariant_zero_eq 𝒯]
    exact finrank_hom_le_one e hn hM hN
  have hAC : gradedHomF ℳ 𝒯 𝒩 0 ≤ superEquivariant 𝒯 (M := M) (N := N) 0 :=
    fun f hf => ((mem_gradedHomF_iff ℳ 𝒯 𝒩).mp hf).2
  have hBC : (homGrading ℳ 𝒩 1 ⊓ superEquivariant 𝒯 (M := M) (N := N) 0)
      ≤ superEquivariant 𝒯 (M := M) (N := N) 0 := inf_le_right
  have hdisj : Disjoint (gradedHomF ℳ 𝒯 𝒩 0)
      (homGrading ℳ 𝒩 1 ⊓ superEquivariant 𝒯 (M := M) (N := N) 0) := by
    rw [Submodule.disjoint_def]
    intro f hfA hfB
    obtain ⟨hf0, _⟩ := (mem_gradedHomF_iff ℳ 𝒯 𝒩).mp hfA
    obtain ⟨hf1, _⟩ := Submodule.mem_inf.mp hfB
    exact PentagonB.homGrading_eq_zero_of_ne K ℳ 𝒩 (by decide) hf0 hf1
  have hbound := finrank_add_finrank_le_of_disjoint_of_le hAC hBC hdisj
  have hB_eq : Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 1)
      = Module.finrank K ↥(homGrading ℳ 𝒩 1 ⊓ superEquivariant 𝒯 (M := M) (N := N) 0) := by
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [finrank_gradedHomF_eq ℳ 𝒯 𝒩 1, h11]
  rw [hB_eq]
  exact hbound.trans hC

end Assemble

end Bimod

end Superfusion

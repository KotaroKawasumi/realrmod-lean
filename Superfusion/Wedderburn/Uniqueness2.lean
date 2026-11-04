/-
Superfusion / Wedderburn / Uniqueness2

Milestone M10-8b of the graded Wedderburn arc (docs/wedderburn-design.md, "Extension:
M10-8..."): **assembling `wedderburn_uniqueness`** from the two landed halves of M10-8a
(`Wedderburn/Uniqueness.lean`: `endIdealEquivOfMinimal` — the transport equivalence between
the endomorphism algebras of two minimal homogeneous left ideals of the *same* graded-simple
algebra — and `endColumnEquivOp` — the column ideal's endomorphism algebra is `Dᵐᵒᵖ`). This
file supplies the missing middle piece — transporting a minimal homogeneous left ideal (and its
endomorphism algebra) *across* a graded isomorphism of two different algebras — and the final
assembly.

**Deliverable 1 (`idealMap`/`idealRestrict`/`endIdealConj`).** For an algebra equivalence
`φ : A ≃ₐ[K] B`, `idealMap φ I` is the pushforward of a left ideal `I ≤ A` along `φ` (the
set-image `φ '' I`, closed under `B`'s left multiplication by `φ`-equivariance); it is
homogeneous when `I` is (`isHomogeneous_idealMap`), and graded-simple when `I` is
(`isGradedSimpleIdeal_idealMap`, via `idealMap φ.symm` back-transport and the
`idealMap_idealMap_symm` round-trip identity). The restriction of `φ` to a bijection
`↥I ≃ ↥(idealMap φ I)` (`idealRestrict`) is `φ`-*semilinear* (`idealRestrict_smul`); conjugating
by it gives a genuine `K`-algebra equivalence `Module.End A ↥I ≃ₐ[K] Module.End B ↥(idealMap φ
I)` (`endIdealConj`, hand-built directly — forward/backward maps, `map_add'`/`map_smul'`
component-wise — per the CRITICAL FRAGILITY note recorded by the M10-8a builder: generic
bijective-transport lemmas interacting with `AlgEquiv.ofBijective`-style construction trigger
deterministic timeouts in this mathlib version). Since `idealRestrict` shifts *no* degree
(unlike M10-8a's `rightMultEquiv`, which shifts by `deg y`), the grading transport
(`endIdealConj_map_grading`) needs no shift-cancellation bookkeeping, only the concrete
decompose-splitting argument the fragility note asks for (`idealRestrict_mem_idealGrading` both
directions).

**Deliverable 2 (`SuperAlgebra.mop`/`SuperAlgEquiv.mopCongr`/`SuperAlgEquiv.mopMop`).** The
plain multiplicative opposite of a bundled `SuperAlgebra`, using mathlib's `AlgEquiv.op`
(`Algebra/Algebra/Opposite.lean`) for the congruence and `AlgEquiv.opOp` for the canonical
double-opposite identification `P ≅ (Pᵐᵒᵖ)ᵐᵒᵖ`; the grading-transport proofs are the concrete
`induction x using MulOpposite.rec'` / `unop_op` computations (`mopCongr_map_grading`,
`mopMop_map_grading`), not the generic bijective-transport lemma composed with these bundled
equivalences (same fragility avoidance as Deliverable 1).

**Deliverable 3 (`wedderburn_uniqueness`).** Fix a column index `j₀` on each side; the column
ideal `columnIdeal j₀` (M10-8a Part 2) is a minimal homogeneous left ideal of `D.matrixSuper p
q`. Transport it along the given graded isomorphism `e` (Deliverable 1) to a minimal
homogeneous left ideal of `D'.matrixSuper p' q'`; chain `endIdealEquivOfMinimal` (M10-8a) with
the column ideal of `D'.matrixSuper p' q'` itself. Recover `D`/`D'` from their respective
column-ideal endomorphism algebras via `endColumnEquivOp` (M10-8a Part 2) and
`SuperAlgEquiv.mopMop`/`mopCongr` (Deliverable 2): `D ≅ (Dᵐᵒᵖ)ᵐᵒᵖ ≅ (End_A(col_D))ᵐᵒᵖ ≅
(End_B(col_{D'}))ᵐᵒᵖ ≅ (D'ᵐᵒᵖ)ᵐᵒᵖ ≅ D'`. A recorded elaboration lesson (folded-type
reducibility): `(D.matrixSuper p q).grading` and `matrixGradingA (sumParity p q) D.grading`
are definitionally equal but instance search does not reliably identify them across a single
function application once one side's implicit ring/algebra instances are fixed from the other's
bundled `SuperAlgebra` fields; the fix (matching the M10-7/M10-8a precedent) is a *single*
`let`-bound (not `have`-bound, to keep it transparent) bridge `φ := e.toAlgEquiv` re-typed at
the unfolded `Matrix ... ≃ₐ[K] Matrix ...` level, after which the entire proof works with the
unfolded `matrixGradingA` presentation throughout, and a bare `haveI := endIdealGradedAlgebra …`
(no restated type ascription — the ascription itself was the trigger for a metavariable-stuck
elaboration failure, discovered by direct experiment) to register each derived `GradedAlgebra`
instance.

**Deliverable 4 (`superAlgEquiv_of_bwMk_eq`).** The BW-class corollary for central super
division algebras. Route taken: **not** the Azumaya route sketched in the milestone brief
(`isSuperAzumaya_of_central_simple` + `isSuperAzumaya_sumParity` + `isSuperAzumaya_tensorGrading`
+ `matrixSuperGtensor`/unitor transfer) — that plumbing needs `M_{p|q}(D) ≅ M_{p|q}(K) ᵍ⊗ D`
transported through several bundled equivalences and did not look shorter than a direct proof of
the one missing fact. Instead, a **direct matrix-ascent lemma**
(`isGradedSimple_matrixSuper_of_isSuperDivision`): if `D` itself is a super division algebra,
`D.matrixSuper p q` (`p + q ≠ 0`) is graded-simple — the mirror image of the already-landed
descent direction (`isGradedSimple_of_matrixSuper`, `Wedderburn/BWEqualsDBW.lean`): a nonzero
homogeneous two-sided ideal has a homogeneous component with a nonzero (hence unit, by
`IsSuperDivision`) entry `X i₁ j₁`; matrix-unit sweeps `single a i₁ 1 * X * single j₁ b 1 =
single a b (X i₁ j₁)` populate the ideal with `single a b w` for every `a, b`, and then
`single a a (Y a b * w⁻¹) * single a b w = single a b (Y a b)` for every `a, b` recovers an
arbitrary target matrix `Y` as a sum of ideal members. This lemma needs no centrality at all,
so `superAlgEquiv_of_bwMk_eq`'s route is: unfold `mk D = mk D'` to `IsBWEquivalent D D'`
(`BWMonoid.mk_eq_mk_iff`), discharge `wedderburn_uniqueness`'s `[IsGradedSimple (D.matrixSuper p
q).grading]` hypothesis directly from `hdiv`, and apply `wedderburn_uniqueness`. The `[IsSuperCentral
_]`/`[IsGradedSimple _]` hypotheses on `D`, `D'` in the corollary's signature (matching `DBW`'s
six-field witness bundle, `Gauge/DBW.lean`) are therefore carried but not used by this specific
proof.
-/
import Superfusion.Wedderburn.Uniqueness
import Superfusion.Wedderburn.BWEqualsDBW

namespace Superfusion

/-! ### Deliverable 1: transporting a minimal homogeneous left ideal across an algebra
equivalence -/

section IdealMap

variable {K : Type*} [Field K] {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- **The pushforward of a left ideal along an algebra equivalence**: `φ '' I`, a left ideal of
`B` (closed under `B`'s left multiplication by `φ`-equivariance:
`b * φ a = φ (φ⁻¹ b) * φ a = φ (φ⁻¹ b * a)`, and `φ⁻¹ b * a ∈ I` since `I` is a left ideal). -/
def idealMap (φ : A ≃ₐ[K] B) (I : Submodule A A) : Submodule B B where
  carrier := φ '' I
  zero_mem' := ⟨0, I.zero_mem, map_zero φ⟩
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    exact ⟨a + a', I.add_mem ha ha', map_add φ a a'⟩
  smul_mem' b x hx := by
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨φ.symm b * a, I.smul_mem (φ.symm b) ha, ?_⟩
    show φ (φ.symm b * a) = b * φ a
    rw [map_mul, φ.apply_symm_apply]

theorem idealMap_apply_mem (φ : A ≃ₐ[K] B) {I : Submodule A A} {a : A} (ha : a ∈ I) :
    φ a ∈ idealMap φ I := ⟨a, ha, rfl⟩

theorem mem_idealMap {φ : A ≃ₐ[K] B} {I : Submodule A A} {y : B} :
    y ∈ idealMap φ I ↔ ∃ a ∈ I, φ a = y := Iff.rfl

theorem idealMap_bot (φ : A ≃ₐ[K] B) : idealMap φ (⊥ : Submodule A A) = ⊥ := by
  refine SetLike.ext fun x => ?_
  simp only [idealMap, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_image, SetLike.mem_coe, Submodule.mem_bot]
  constructor
  · rintro ⟨a, rfl, rfl⟩; rw [map_zero]
  · rintro rfl; exact ⟨0, rfl, map_zero φ⟩

theorem idealMap_ne_bot (φ : A ≃ₐ[K] B) {I : Submodule A A} (hIne : I ≠ ⊥) :
    idealMap φ I ≠ ⊥ := by
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIne
  intro h
  apply ha0
  apply φ.injective
  have hmem : φ a ∈ idealMap φ I := idealMap_apply_mem φ haI
  rw [h, Submodule.mem_bot] at hmem
  rw [hmem, map_zero]

theorem idealMap_symm_idealMap (φ : A ≃ₐ[K] B) (I : Submodule A A) :
    idealMap φ.symm (idealMap φ I) = I := by
  refine le_antisymm ?_ ?_
  · rintro a ⟨b, ⟨a', ha', rfl⟩, rfl⟩
    rwa [φ.symm_apply_apply]
  · intro a ha
    exact ⟨φ a, idealMap_apply_mem φ ha, φ.symm_apply_apply a⟩

/-- The round-trip identity carrying `idealMap`'s minimality transport: pushing forward then
pulling back (along the symmetric equivalence) recovers the original submodule. -/
theorem idealMap_idealMap_symm (φ : A ≃ₐ[K] B) (J : Submodule B B) :
    idealMap φ (idealMap φ.symm J) = J := by
  have h := idealMap_symm_idealMap φ.symm J
  rwa [AlgEquiv.symm_symm] at h

theorem isHomogeneous_idealMap {𝒜 : ZMod 2 → Submodule K A} {ℬ : ZMod 2 → Submodule K B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)
    {I : Submodule A A} (hI : I.IsHomogeneous 𝒜) :
    (idealMap φ I).IsHomogeneous ℬ := by
  intro i y hy
  obtain ⟨a, ha, rfl⟩ := hy
  rw [decompose_map 𝒜 ℬ φ hφ a i]
  exact idealMap_apply_mem φ (hI i ha)

theorem map_grading_symm_of_map_grading {𝒜 : ZMod 2 → Submodule K A} {ℬ : ZMod 2 → Submodule K B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)
    (i : ZMod 2) : (ℬ i).map φ.symm.toLinearMap = 𝒜 i := by
  rw [← hφ i, ← Submodule.map_comp]
  rw [show φ.symm.toLinearMap.comp φ.toLinearMap = LinearMap.id from by ext x; simp]
  exact Submodule.map_id _

/-- **`idealMap` preserves graded simplicity** (Deliverable 1, minimality half): the pullback
`idealMap φ.symm J` of a homogeneous `J ≤ idealMap φ I` is a homogeneous ideal `≤ I`; simplicity
of `I` forces it to `⊥` or `I`, transporting forward (via `idealMap_idealMap_symm`) to `J = ⊥`
or `J = idealMap φ I`. -/
theorem isGradedSimpleIdeal_idealMap {𝒜 : ZMod 2 → Submodule K A} {ℬ : ZMod 2 → Submodule K B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)
    {I : Submodule A A} (hsimple : IsGradedSimpleIdeal 𝒜 I) :
    IsGradedSimpleIdeal ℬ (idealMap φ I) := by
  intro J hJhom hJle
  have hφ' := map_grading_symm_of_map_grading φ hφ
  have hJ'hom : (idealMap φ.symm J).IsHomogeneous 𝒜 := isHomogeneous_idealMap φ.symm hφ' hJhom
  have hJ'le : idealMap φ.symm J ≤ I := by
    rintro x ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hab⟩ := hJle hb
    rw [← hab, φ.symm_apply_apply]
    exact ha
  rcases hsimple (idealMap φ.symm J) hJ'hom hJ'le with h | h
  · left
    rw [← idealMap_idealMap_symm φ J, h, idealMap_bot]
  · right
    rw [← idealMap_idealMap_symm φ J, h]

/-! #### The restriction of `φ` to a `φ`-semilinear bijection `↥I ≃ ↥(idealMap φ I)` -/

/-- The restriction of `φ` to `↥I ≃ ↥(idealMap φ I)`, as a plain bijection (not yet a linear
map — see `idealRestrict_smul` for its `φ`-semilinearity). -/
def idealRestrict (φ : A ≃ₐ[K] B) (I : Submodule A A) : ↥I ≃ ↥(idealMap φ I) where
  toFun x := ⟨φ (x : A), idealMap_apply_mem φ x.2⟩
  invFun y := ⟨φ.symm (y : B), by
    obtain ⟨a, ha, hay⟩ := y.2
    rw [← hay, φ.symm_apply_apply]
    exact ha⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

theorem idealRestrict_apply (φ : A ≃ₐ[K] B) (I : Submodule A A) (x : ↥I) :
    ((idealRestrict φ I x : ↥(idealMap φ I)) : B) = φ (x : A) := rfl

theorem idealRestrict_symm_apply (φ : A ≃ₐ[K] B) (I : Submodule A A) (y : ↥(idealMap φ I)) :
    (((idealRestrict φ I).symm y : ↥I) : A) = φ.symm (y : B) := rfl

theorem idealRestrict_smul (φ : A ≃ₐ[K] B) (I : Submodule A A) (a : A) (x : ↥I) :
    idealRestrict φ I (a • x) = φ a • idealRestrict φ I x := by
  apply Subtype.ext
  show φ ((a • x : ↥I) : A) = ((φ a • idealRestrict φ I x : ↥(idealMap φ I)) : B)
  rw [Submodule.coe_smul, smul_eq_mul, Submodule.coe_smul, smul_eq_mul, idealRestrict_apply,
    map_mul]

theorem idealRestrict_symm_smul (φ : A ≃ₐ[K] B) (I : Submodule A A) (b : B)
    (y : ↥(idealMap φ I)) :
    (idealRestrict φ I).symm (b • y) = φ.symm b • (idealRestrict φ I).symm y := by
  apply Subtype.ext
  show φ.symm ((b • y : ↥(idealMap φ I)) : B) = ((φ.symm b • (idealRestrict φ I).symm y : ↥I) : A)
  rw [Submodule.coe_smul, smul_eq_mul, Submodule.coe_smul, smul_eq_mul, idealRestrict_symm_apply,
    map_mul]

theorem idealRestrict_add (φ : A ≃ₐ[K] B) (I : Submodule A A) (u v : ↥I) :
    idealRestrict φ I (u + v) = idealRestrict φ I u + idealRestrict φ I v := by
  apply Subtype.ext
  show φ ((u + v : ↥I) : A) = ((idealRestrict φ I u + idealRestrict φ I v : ↥(idealMap φ I)) : B)
  rw [Submodule.coe_add, Submodule.coe_add, idealRestrict_apply, idealRestrict_apply, map_add]

theorem idealRestrict_symm_add (φ : A ≃ₐ[K] B) (I : Submodule A A)
    (u v : ↥(idealMap φ I)) :
    (idealRestrict φ I).symm (u + v)
      = (idealRestrict φ I).symm u + (idealRestrict φ I).symm v := by
  apply Subtype.ext
  show φ.symm ((u + v : ↥(idealMap φ I)) : B)
    = (((idealRestrict φ I).symm u + (idealRestrict φ I).symm v : ↥I) : A)
  rw [Submodule.coe_add, Submodule.coe_add, idealRestrict_symm_apply, idealRestrict_symm_apply,
    map_add]

theorem idealRestrict_zero (φ : A ≃ₐ[K] B) (I : Submodule A A) :
    idealRestrict φ I 0 = 0 := by
  apply Subtype.ext
  show φ ((0 : ↥I) : A) = ((0 : ↥(idealMap φ I)) : B)
  rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_zero]

/-! #### `endIdealConj`: conjugation by `idealRestrict` as a `K`-algebra equivalence -/

/-- Conjugation of `f : Module.End A ↥I` by `idealRestrict φ I`, as a `B`-linear map (using
`idealRestrict`'s `φ`-semilinearity on both sides to cancel `φ`, leaving `B`-linearity). -/
def endConjFun (φ : A ≃ₐ[K] B) (I : Submodule A A) (f : Module.End A ↥I) :
    Module.End B ↥(idealMap φ I) where
  toFun y := idealRestrict φ I (f ((idealRestrict φ I).symm y))
  map_add' y y' := by rw [idealRestrict_symm_add, map_add, idealRestrict_add]
  map_smul' b y := by
    show idealRestrict φ I (f ((idealRestrict φ I).symm (b • y)))
      = b • idealRestrict φ I (f ((idealRestrict φ I).symm y))
    rw [idealRestrict_symm_smul, map_smul, idealRestrict_smul, φ.apply_symm_apply]

theorem endConjFun_apply (φ : A ≃ₐ[K] B) (I : Submodule A A) (f : Module.End A ↥I)
    (y : ↥(idealMap φ I)) :
    endConjFun φ I f y = idealRestrict φ I (f ((idealRestrict φ I).symm y)) := rfl

/-- The mirror-image conjugation, in the reverse direction; the two-sided inverse of
`endConjFun` (`endConjFunInv_endConjFun`/`endConjFun_endConjFunInv`). -/
def endConjFunInv (φ : A ≃ₐ[K] B) (I : Submodule A A) (g : Module.End B ↥(idealMap φ I)) :
    Module.End A ↥I where
  toFun x := (idealRestrict φ I).symm (g (idealRestrict φ I x))
  map_add' x x' := by rw [idealRestrict_add, map_add, idealRestrict_symm_add]
  map_smul' a x := by
    show (idealRestrict φ I).symm (g (idealRestrict φ I (a • x)))
      = a • (idealRestrict φ I).symm (g (idealRestrict φ I x))
    rw [idealRestrict_smul, map_smul, idealRestrict_symm_smul, φ.symm_apply_apply]

theorem endConjFunInv_apply (φ : A ≃ₐ[K] B) (I : Submodule A A)
    (g : Module.End B ↥(idealMap φ I)) (x : ↥I) :
    endConjFunInv φ I g x = (idealRestrict φ I).symm (g (idealRestrict φ I x)) := rfl

theorem endConjFunInv_endConjFun (φ : A ≃ₐ[K] B) (I : Submodule A A) (f : Module.End A ↥I) :
    endConjFunInv φ I (endConjFun φ I f) = f := by
  refine LinearMap.ext fun x => ?_
  rw [endConjFunInv_apply, endConjFun_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem endConjFun_endConjFunInv (φ : A ≃ₐ[K] B) (I : Submodule A A)
    (g : Module.End B ↥(idealMap φ I)) :
    endConjFun φ I (endConjFunInv φ I g) = g := by
  refine LinearMap.ext fun y => ?_
  rw [endConjFun_apply, endConjFunInv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem endConjFun_one (φ : A ≃ₐ[K] B) (I : Submodule A A) :
    endConjFun φ I 1 = 1 := by
  refine LinearMap.ext fun y => ?_
  rw [endConjFun_apply]
  show idealRestrict φ I ((idealRestrict φ I).symm y) = y
  rw [Equiv.apply_symm_apply]

theorem endConjFun_mul (φ : A ≃ₐ[K] B) (I : Submodule A A) (f g : Module.End A ↥I) :
    endConjFun φ I (f * g) = endConjFun φ I f * endConjFun φ I g := by
  refine LinearMap.ext fun y => ?_
  rw [endConjFun_apply]
  show idealRestrict φ I (f (g ((idealRestrict φ I).symm y)))
    = endConjFun φ I f (endConjFun φ I g y)
  rw [endConjFun_apply, endConjFun_apply, Equiv.symm_apply_apply]

theorem endConjFun_zero (φ : A ≃ₐ[K] B) (I : Submodule A A) :
    endConjFun φ I 0 = 0 := by
  refine LinearMap.ext fun y => ?_
  rw [endConjFun_apply]
  show idealRestrict φ I 0 = 0
  exact idealRestrict_zero φ I

theorem endConjFun_add (φ : A ≃ₐ[K] B) (I : Submodule A A) (f g : Module.End A ↥I) :
    endConjFun φ I (f + g) = endConjFun φ I f + endConjFun φ I g := by
  refine LinearMap.ext fun y => ?_
  rw [endConjFun_apply]
  show idealRestrict φ I (f ((idealRestrict φ I).symm y) + g ((idealRestrict φ I).symm y))
    = endConjFun φ I f y + endConjFun φ I g y
  rw [idealRestrict_add, endConjFun_apply, endConjFun_apply]

theorem endConjFun_algebraMap (φ : A ≃ₐ[K] B) (I : Submodule A A) (c : K) :
    endConjFun φ I (algebraMap K (Module.End A ↥I) c)
      = algebraMap K (Module.End B ↥(idealMap φ I)) c := by
  refine LinearMap.ext fun y => ?_
  rw [endConjFun_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
  show idealRestrict φ I (c • (idealRestrict φ I).symm y) = c • y
  have hc : ((algebraMap K A c) • (idealRestrict φ I).symm y) = c • (idealRestrict φ I).symm y :=
    by rw [algebraMap_smul]
  rw [← hc, idealRestrict_smul, φ.commutes, algebraMap_smul, Equiv.apply_symm_apply]

/-- **`endIdealConj`** (Deliverable 1, the assembled theorem): conjugation by `idealRestrict φ
I` is a `K`-algebra equivalence `Module.End A ↥I ≃ₐ[K] Module.End B ↥(idealMap φ I)` — built by
hand (explicit forward/backward maps and their `left_inv`/`right_inv`/`map_mul'`/`map_add'`/
`commutes'`), per the fragility note in the file docstring. -/
def endIdealConj (φ : A ≃ₐ[K] B) (I : Submodule A A) :
    Module.End A ↥I ≃ₐ[K] Module.End B ↥(idealMap φ I) where
  toFun f := endConjFun φ I f
  invFun g := endConjFunInv φ I g
  left_inv f := endConjFunInv_endConjFun φ I f
  right_inv g := endConjFun_endConjFunInv φ I g
  map_mul' f g := endConjFun_mul φ I f g
  map_add' f g := endConjFun_add φ I f g
  commutes' c := endConjFun_algebraMap φ I c

/-! #### Grading transport for `idealRestrict`/`endIdealConj`

`idealRestrict` shifts *no* degree (`idealRestrict_mem_idealGrading`: degree-`j` stays
degree-`j`, unlike M10-8a's `rightMultEquiv`, which shifts by `deg y`), so the End-grading
transport (`endIdealConj_map_grading`) needs no shift-cancellation computation. -/

theorem idealRestrict_mem_idealGrading {𝒜 : ZMod 2 → Submodule K A} {ℬ : ZMod 2 → Submodule K B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)
    {I : Submodule A A} {j : ZMod 2} {x : ↥I} (hx : x ∈ idealGrading 𝒜 I j) :
    idealRestrict φ I x ∈ idealGrading ℬ (idealMap φ I) j := by
  rw [mem_idealGrading_iff] at hx ⊢
  rw [idealRestrict_apply]
  exact (mem_iff_map_mem 𝒜 ℬ φ hφ).mp hx

theorem idealRestrict_symm_mem_idealGrading {𝒜 : ZMod 2 → Submodule K A}
    {ℬ : ZMod 2 → Submodule K B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : A ≃ₐ[K] B)
    (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i) {I : Submodule A A} {j : ZMod 2}
    {y : ↥(idealMap φ I)} (hy : y ∈ idealGrading ℬ (idealMap φ I) j) :
    (idealRestrict φ I).symm y ∈ idealGrading 𝒜 I j := by
  rw [mem_idealGrading_iff] at hy ⊢
  rw [idealRestrict_symm_apply]
  exact (mem_iff_map_mem ℬ 𝒜 φ.symm (map_grading_symm_of_map_grading φ hφ)).mp hy

theorem endConjFun_mem_endIdealGrading {𝒜 : ZMod 2 → Submodule K A} {ℬ : ZMod 2 → Submodule K B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)
    {I : Submodule A A} (hI : I.IsHomogeneous 𝒜) (hJ : (idealMap φ I).IsHomogeneous ℬ)
    {d : ZMod 2} {f : Module.End A ↥I} (hf : f ∈ endIdealGrading 𝒜 hI d) :
    endConjFun φ I f ∈ endIdealGrading ℬ hJ d := by
  intro j y hy
  rw [endConjFun_apply]
  exact idealRestrict_mem_idealGrading φ hφ (hf j _ (idealRestrict_symm_mem_idealGrading φ hφ hy))

/-- **`endIdealConj` respects the gradings, degree for degree** (Deliverable 1's final
theorem). -/
theorem endIdealConj_map_grading {𝒜 : ZMod 2 → Submodule K A} {ℬ : ZMod 2 → Submodule K B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)
    {I : Submodule A A} (hI : I.IsHomogeneous 𝒜) (hJ : (idealMap φ I).IsHomogeneous ℬ)
    (d : ZMod 2) :
    (endIdealGrading 𝒜 hI d).map (endIdealConj φ I).toLinearMap = endIdealGrading ℬ hJ d := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨f, hf, rfl⟩
    exact endConjFun_mem_endIdealGrading φ hφ hI hJ hf
  · intro g hg
    refine ⟨endConjFunInv φ I g, ?_, endConjFun_endConjFunInv φ I g⟩
    intro j x hx
    have hx' : idealRestrict φ I x ∈ idealGrading ℬ (idealMap φ I) j :=
      idealRestrict_mem_idealGrading φ hφ hx
    have hgx : g (idealRestrict φ I x) ∈ idealGrading ℬ (idealMap φ I) (j + d) := hg j _ hx'
    exact idealRestrict_symm_mem_idealGrading φ hφ hgx

end IdealMap

/-! ### Deliverable 2: `ᵐᵒᵖ` congruence at the bundled `SuperAlgebra` level

Mathlib's `AlgEquiv.op`/`AlgEquiv.opOp` (`Algebra/Algebra/Opposite.lean`) supply the underlying
`AlgEquiv` machinery; the only new content is the grading transport. -/

section OpBundled

variable {K : Type*} [Field K]

/-- The plain multiplicative opposite of a bundled superalgebra (not the *super*-opposite
`SuperAlgebra.sop` — no Koszul sign enters, matching design decision 2 of
`docs/wedderburn-design.md`: `Eᵐᵒᵖ`, not `E^sop`). -/
noncomputable def SuperAlgebra.mop (P : SuperAlgebra K) : SuperAlgebra K where
  carrier := P.carrierᵐᵒᵖ
  grading := opGrading P.grading

/-- **`AlgEquiv.op` respects the gradings** (Deliverable 2a): proved directly via
`induction x using MulOpposite.rec'` (not the generic bijective-transport lemma composed with a
bundled equivalence — same fragility avoidance as Deliverable 1). -/
theorem mopCongr_map_grading {P Q : SuperAlgebra K} (e : SuperAlgEquiv P Q) (i : ZMod 2) :
    (opGrading P.grading i).map (AlgEquiv.op e.toAlgEquiv).toLinearMap = opGrading Q.grading i :=
  by
  refine map_grading_of_bijective (opGrading P.grading) (opGrading Q.grading)
    (AlgEquiv.op e.toAlgEquiv).toAlgHom ?_ (AlgEquiv.op e.toAlgEquiv).bijective i
  intro d x hx
  induction x using MulOpposite.rec' with
  | h a =>
    rw [mem_opGrading_iff, MulOpposite.unop_op] at hx
    show MulOpposite.unop ((AlgEquiv.op e.toAlgEquiv) (MulOpposite.op a)) ∈ Q.grading d
    show e.toAlgEquiv a ∈ Q.grading d
    exact (mem_iff_map_mem P.grading Q.grading e.toAlgEquiv e.map_grading).mp hx

/-- **`SuperAlgEquiv.mopCongr`**: a graded isomorphism `P ≅ Q` induces `Pᵐᵒᵖ ≅ Qᵐᵒᵖ`. -/
noncomputable def SuperAlgEquiv.mopCongr {P Q : SuperAlgebra K} (e : SuperAlgEquiv P Q) :
    SuperAlgEquiv P.mop Q.mop :=
  ⟨AlgEquiv.op e.toAlgEquiv, mopCongr_map_grading e⟩

/-- **`AlgEquiv.opOp` respects the gradings** (Deliverable 2b): the double-opposite
identification is grading-preserving. -/
theorem mopMop_map_grading (P : SuperAlgebra K) (i : ZMod 2) :
    (P.grading i).map (AlgEquiv.opOp K P.carrier).toLinearMap
      = opGrading (opGrading P.grading) i := by
  refine map_grading_of_bijective P.grading (opGrading (opGrading P.grading))
    (AlgEquiv.opOp K P.carrier).toAlgHom ?_ (AlgEquiv.opOp K P.carrier).bijective i
  intro d x hx
  rw [mem_opGrading_iff, mem_opGrading_iff]
  show MulOpposite.unop (MulOpposite.unop ((AlgEquiv.opOp K P.carrier) x)) ∈ P.grading d
  rw [AlgEquiv.opOp_apply, MulOpposite.unop_op, MulOpposite.unop_op]
  exact hx

/-- **`SuperAlgEquiv.mopMop`**: `P ≅ (Pᵐᵒᵖ)ᵐᵒᵖ`, graded. -/
noncomputable def SuperAlgEquiv.mopMop (P : SuperAlgebra K) : SuperAlgEquiv P P.mop.mop :=
  ⟨AlgEquiv.opOp K P.carrier, mopMop_map_grading P⟩

end OpBundled

/-! ### Deliverable 4a: the direct matrix-ascent lemma

`IsSuperDivision D.grading ⇒ IsGradedSimple (D.matrixSuper p q).grading` (`p + q ≠ 0`), the
mirror image of `isGradedSimple_of_matrixSuper` (`Wedderburn/BWEqualsDBW.lean`). Needs no
centrality; landed here (rather than routing through the Azumaya machinery, see the file
docstring) since it directly discharges `wedderburn_uniqueness`'s `IsGradedSimple` hypothesis for
`superAlgEquiv_of_bwMk_eq`. -/

section MatrixAscent

/-- The matrix-unit sweep identity `single a i₁ 1 * X * single j₁ b 1 = single a b (X i₁ j₁)`,
the entrywise engine of the ascent lemma below. -/
theorem single_mul_apply_of_ne_matrixAscent {D : Type*} [Ring D]
    {n : Type*} [Fintype n] [DecidableEq n] (a i1 j1 b : n) (X : Matrix n n D) :
    Matrix.single a i1 (1 : D) * X * Matrix.single j1 b (1 : D) = Matrix.single a b (X i1 j1) := by
  rw [mul_assoc]
  ext r c
  rcases eq_or_ne r a with hr | hr
  · rcases eq_or_ne c b with hc | hc
    · subst hr; subst hc
      simp
    · subst hr
      rw [Matrix.single_apply_of_col_ne _ _ hc.symm, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [show (X * Matrix.single j1 b (1 : D)) l c = 0 from
        Matrix.mul_single_apply_of_ne (c := (1 : D)) (i := j1) (j := b) (a := l) (b := c)
          (hbj := hc) (M := X),
        mul_zero]
  · rw [show (Matrix.single a i1 (1 : D) * (X * Matrix.single j1 b (1 : D))) r c = 0
      from Matrix.single_mul_apply_of_ne (c := (1 : D)) (i := a) (j := i1) (a := r) (b := c)
        (h := hr) (M := X * Matrix.single j1 b (1 : D)),
      Matrix.single_apply_of_row_ne hr.symm]

/-- Every matrix is the (finite) sum of its single-entry decomposition. -/
theorem matrix_eq_sum_single {D : Type*} [Ring D]
    {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n D) :
    Y = ∑ a : n, ∑ b : n, Matrix.single a b (Y a b) := by
  ext r c
  rw [Matrix.sum_apply,
    Finset.sum_eq_single r (fun a _ ha => by
      rw [Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro b _
      exact Matrix.single_apply_of_row_ne ha b c (Y a b))
      (fun h => absurd (Finset.mem_univ r) h),
    Matrix.sum_apply,
    Finset.sum_eq_single c (fun b _ hb => Matrix.single_apply_of_col_ne r r hb (Y r b))
      (fun h => absurd (Finset.mem_univ c) h),
    Matrix.single_apply_same]

/-- **The direct matrix-ascent lemma** (Deliverable 4a): a super *division* algebra's matrix
stabilization is graded-simple. A nonzero homogeneous two-sided ideal `J` has a homogeneous
component `X` with a nonzero entry `w := X i₁ j₁` (a unit, by `IsSuperDivision`); the sweep
`single a i₁ 1 * X * single j₁ b 1 = single a b w ∈ J` populates every matrix-unit slot
(`hallw`), and `single a a (Y a b * w⁻¹) * single a b w = single a b (Y a b) ∈ J` for arbitrary
`a, b` recovers every entry of an arbitrary target `Y`, giving `Y ∈ J` (`matrix_eq_sum_single`),
i.e. `J = ⊤`. -/
theorem isGradedSimple_matrixSuper_of_isSuperDivision {K : Type*} [Field K] (D : SuperAlgebra K)
    (p q : ℕ) (_hpq : p + q ≠ 0) (hdiv : Bimod.IsSuperDivision D.grading) :
    IsGradedSimple (D.matrixSuper p q).grading := by
  show IsGradedSimple (matrixGradingA (sumParity p q) D.grading)
  haveI hne : Nonempty (Fin p ⊕ Fin q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, Nat.pos_of_ne_zero fun hq => _hpq (by rw [hp, hq])⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  constructor
  intro J hJ
  by_cases hJbot : J = ⊥
  · exact Or.inl hJbot
  refine Or.inr ?_
  have hlt : (⊥ : TwoSidedIdeal (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier)) < J :=
    bot_lt_iff_ne_bot.mpr hJbot
  obtain ⟨-, v, hvJ, hv0'⟩ := SetLike.lt_iff_le_and_exists.mp hlt
  have hv0 : v ≠ 0 := fun h => hv0' (by rw [h]; exact TwoSidedIdeal.zero_mem _)
  have hcomp : ∃ d : ZMod 2, (DirectSum.decompose (matrixGradingA (sumParity p q) D.grading) v d :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0
    have h0 := hcon 0
    have h1 := hcon 1
    rw [← evenPart_apply] at h0
    rw [← oddPart_apply] at h1
    rw [← evenPart_add_oddPart (matrixGradingA (sumParity p q) D.grading) v, h0, h1, add_zero]
  obtain ⟨d, hd⟩ := hcomp
  set X := (DirectSum.decompose (matrixGradingA (sumParity p q) D.grading) v d :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier) with hXdef
  have hXJ : X ∈ J := by rw [hXdef]; exact hJ v hvJ d
  have hXmem : X ∈ matrixGradingA (sumParity p q) D.grading d := SetLike.coe_mem _
  obtain ⟨i1, j1, hij1⟩ : ∃ i1 j1, X i1 j1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hd
    ext r k
    exact hcon r k
  have hXentry : X i1 j1 ∈ D.grading (d + sumParity p q i1 + sumParity p q j1) := hXmem i1 j1
  obtain ⟨u, hu⟩ := hdiv hXentry hij1
  have hallw : ∀ a b, Matrix.single a b (X i1 j1) ∈ J := by
    intro a b
    rw [← single_mul_apply_of_ne_matrixAscent a i1 j1 b X]
    exact J.mul_mem_right _ _ (J.mul_mem_left _ _ hXJ)
  have hallY : ∀ (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier) a b,
      Matrix.single a b (Y a b) ∈ J := by
    intro Y a b
    have hmem :
        Matrix.single a a (Y a b * ((u⁻¹ : D.carrierˣ) : D.carrier)) * Matrix.single a b (X i1 j1)
          ∈ J := J.mul_mem_left _ _ (hallw a b)
    have heq2 :
        Matrix.single a a (Y a b * ((u⁻¹ : D.carrierˣ) : D.carrier)) * Matrix.single a b (X i1 j1)
          = Matrix.single a b (Y a b) := by
      rw [Matrix.single_mul_single_same]
      congr 1
      rw [mul_assoc, ← hu, Units.inv_mul, mul_one]
    rwa [heq2] at hmem
  ext y
  simp only [TwoSidedIdeal.mem_top, iff_true]
  rw [matrix_eq_sum_single y]
  exact sum_mem fun a _ => sum_mem fun b _ => hallY y a b

end MatrixAscent

/-! ### Deliverable 3: `wedderburn_uniqueness` -/

section WedderburnUniqueness

universe u
variable {K : Type u} [Field K]

/-- **`wedderburn_uniqueness`** (M10-8, the summit of this file): the super division algebra
recovered from a graded-simple matrix stabilization by `graded_wedderburn`
(`Wedderburn/MatrixRealization.lean`) is unique up to graded isomorphism. -/
theorem wedderburn_uniqueness (D D' : SuperAlgebra.{u,u} K)
    (hdiv : Bimod.IsSuperDivision D.grading) (hdiv' : Bimod.IsSuperDivision D'.grading)
    [FiniteDimensional K D.carrier] [Nontrivial D.carrier]
    [FiniteDimensional K D'.carrier] [Nontrivial D'.carrier]
    {p q p' q' : ℕ} (hpq : p + q ≠ 0) (hpq' : p' + q' ≠ 0)
    [IsGradedSimple (D.matrixSuper p q).grading]
    (e : SuperAlgEquiv (D.matrixSuper p q) (D'.matrixSuper p' q')) :
    Nonempty (SuperAlgEquiv D D') := by
  haveI hjne : Nonempty (Fin p ⊕ Fin q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  haveI hj'ne : Nonempty (Fin p' ⊕ Fin q') := by
    rcases Nat.eq_zero_or_pos p' with hp' | hp'
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp'⟩⟩
  obtain ⟨j₀⟩ := hjne
  obtain ⟨j₀'⟩ := hj'ne
  -- Bridge the `.matrixSuper`-folded hypotheses into their unfolded (`matrixGradingA`) form,
  -- once, so that all subsequent instance search stays unfolded (avoiding the folded-type
  -- reducibility trap at the `matrixSuper` boundary — see the file docstring): `φ` is
  -- `let`-bound (not `have`-bound) so that its definitional unfolding to `e.toAlgEquiv` stays
  -- available to the elaborator.
  let φ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier ≃ₐ[K]
      Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') D'.carrier := e.toAlgEquiv
  have hφ : ∀ i, (matrixGradingA (sumParity p q) D.grading i).map φ.toLinearMap
      = matrixGradingA (sumParity p' q') D'.grading i := e.map_grading
  haveI hSA : IsGradedSimple (matrixGradingA (sumParity p q) D.grading) :=
    ‹IsGradedSimple (D.matrixSuper p q).grading›
  haveI hSA' : IsGradedSimple (matrixGradingA (sumParity p' q') D'.grading) :=
    isGradedSimple_of_equiv (matrixGradingA (sumParity p q) D.grading)
      (matrixGradingA (sumParity p' q') D'.grading) φ hφ
  have hIhom : (columnIdeal (D := D.carrier) j₀).IsHomogeneous
      (matrixGradingA (sumParity p q) D.grading) :=
    isHomogeneous_columnIdeal (𝒟 := D.grading) (π := sumParity p q) j₀
  have hIne : (columnIdeal (D := D.carrier) j₀) ≠ ⊥ := columnIdeal_ne_bot (D := D.carrier) j₀
  have hIsimple : IsGradedSimpleIdeal (matrixGradingA (sumParity p q) D.grading)
      (columnIdeal (D := D.carrier) j₀) :=
    isGradedSimpleIdeal_columnIdeal (𝒟 := D.grading) (π := sumParity p q) hdiv j₀
  have hI'hom : (columnIdeal (D := D'.carrier) j₀').IsHomogeneous
      (matrixGradingA (sumParity p' q') D'.grading) :=
    isHomogeneous_columnIdeal (𝒟 := D'.grading) (π := sumParity p' q') j₀'
  have hI'ne : (columnIdeal (D := D'.carrier) j₀') ≠ ⊥ := columnIdeal_ne_bot (D := D'.carrier) j₀'
  have hI'simple : IsGradedSimpleIdeal (matrixGradingA (sumParity p' q') D'.grading)
      (columnIdeal (D := D'.carrier) j₀') :=
    isGradedSimpleIdeal_columnIdeal (𝒟 := D'.grading) (π := sumParity p' q') hdiv' j₀'
  -- Transport the column ideal of `D` along `e` into a minimal homogeneous left ideal of
  -- `D'.matrixSuper p' q'`.
  have hJhom : (idealMap φ (columnIdeal (D := D.carrier) j₀)).IsHomogeneous
      (matrixGradingA (sumParity p' q') D'.grading) :=
    isHomogeneous_idealMap φ hφ hIhom
  have hJne : (idealMap φ (columnIdeal (D := D.carrier) j₀)) ≠ ⊥ :=
    idealMap_ne_bot φ hIne
  have hJsimple : IsGradedSimpleIdeal (matrixGradingA (sumParity p' q') D'.grading)
      (idealMap φ (columnIdeal (D := D.carrier) j₀)) :=
    isGradedSimpleIdeal_idealMap φ hφ hIsimple
  -- The three `SuperAlgebra`-bundled endomorphism algebras (the `GradedAlgebra` instances are
  -- registered via bare `haveI := …`, with no restated type ascription — see the file
  -- docstring's elaboration lesson).
  haveI hEalgI := endIdealGradedAlgebra (matrixGradingA (sumParity p q) D.grading) hIhom
  haveI hEalgJ := endIdealGradedAlgebra (matrixGradingA (sumParity p' q') D'.grading) hJhom
  haveI hEalgI' := endIdealGradedAlgebra (matrixGradingA (sumParity p' q') D'.grading) hI'hom
  set EndID : SuperAlgebra K :=
    ⟨Module.End (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier)
        ↥(columnIdeal (D := D.carrier) j₀),
      endIdealGrading (matrixGradingA (sumParity p q) D.grading) hIhom⟩ with hEndIDdef
  set EndJ : SuperAlgebra K :=
    ⟨Module.End (Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') D'.carrier)
        ↥(idealMap φ (columnIdeal (D := D.carrier) j₀)),
      endIdealGrading (matrixGradingA (sumParity p' q') D'.grading) hJhom⟩ with hEndJdef
  set EndID' : SuperAlgebra K :=
    ⟨Module.End (Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') D'.carrier)
        ↥(columnIdeal (D := D'.carrier) j₀'),
      endIdealGrading (matrixGradingA (sumParity p' q') D'.grading) hI'hom⟩ with hEndID'def
  set Dop : SuperAlgebra K := D.mop with hDopdef
  set D'op : SuperAlgebra K := D'.mop with hD'opdef
  -- `EndID ≅ EndJ` (Deliverable 1) then `EndJ ≅ EndID'` (M10-8a's `endIdealEquivOfMinimal`,
  -- both minimal homogeneous left ideals of `D'.matrixSuper p' q'`).
  have e1 : SuperAlgEquiv EndID EndJ :=
    ⟨endIdealConj φ (columnIdeal (D := D.carrier) j₀),
      endIdealConj_map_grading φ hφ hIhom hJhom⟩
  have e2 : SuperAlgEquiv EndJ EndID' :=
    ⟨endIdealEquivOfMinimal (matrixGradingA (sumParity p' q') D'.grading) hJhom hI'hom hJsimple
        hI'simple hJne hI'ne,
      endIdealEquivOfMinimal_map_grading (matrixGradingA (sumParity p' q') D'.grading) hJhom
        hI'hom hJsimple hI'simple hJne hI'ne⟩
  have e12 : SuperAlgEquiv EndID EndID' := e1.trans e2
  -- Recover `D`/`D'` from their respective column-ideal endomorphism algebras
  -- (M10-8a's `endColumnEquivOp`).
  have colEquivD : SuperAlgEquiv EndID Dop :=
    ⟨endColumnEquivOp (D := D.carrier) j₀,
      fun d => endColumnEquivOp_map_grading (D := D.carrier) (π := sumParity p q)
        (𝒟 := D.grading) (j₀ := j₀) hIhom d⟩
  have colEquivD' : SuperAlgEquiv EndID' D'op :=
    ⟨endColumnEquivOp (D := D'.carrier) j₀',
      fun d => endColumnEquivOp_map_grading (D := D'.carrier) (π := sumParity p' q')
        (𝒟 := D'.grading) (j₀ := j₀') hI'hom d⟩
  -- `D ≅ (Dᵐᵒᵖ)ᵐᵒᵖ ≅ (End_A(col_D))ᵐᵒᵖ ≅ (End_B(col_{D'}))ᵐᵒᵖ ≅ (D'ᵐᵒᵖ)ᵐᵒᵖ ≅ D'`.
  exact ⟨(SuperAlgEquiv.mopMop D).trans ((SuperAlgEquiv.mopCongr colEquivD.symm).trans
    ((SuperAlgEquiv.mopCongr e12).trans
      ((SuperAlgEquiv.mopCongr colEquivD').trans (SuperAlgEquiv.mopMop D').symm)))⟩

end WedderburnUniqueness

/-! ### Deliverable 4: the BW-class corollary for central super division algebras -/

section BWCorollary

universe v
variable {K : Type v} [Field K]

/-- **`superAlgEquiv_of_bwMk_eq`** (M10-8, deliverable 4): two central super division algebras
representing the same Brauer–Wall class are graded-isomorphic. Unfolds `mk D = mk D'` to
`IsBWEquivalent D D'` (`BWMonoid.mk_eq_mk_iff`) and discharges `wedderburn_uniqueness`'s
`[IsGradedSimple (D.matrixSuper p q).grading]` hypothesis directly from `hdiv` via the direct
matrix-ascent lemma (`isGradedSimple_matrixSuper_of_isSuperDivision`, Deliverable 4a) — see the
file docstring for why this route was chosen over the Azumaya-tensor-transfer route sketched in
the milestone brief. The `[IsSuperCentral _]`/`[IsGradedSimple _]` hypotheses (matching `DBW`'s
six-field witness bundle, `Gauge/DBW.lean`) are carried in the signature but not needed by this
particular proof. -/
theorem superAlgEquiv_of_bwMk_eq (D D' : SuperAlgebra.{v,v} K)
    [IsSuperCentral D.grading] [IsGradedSimple D.grading]
    [FiniteDimensional K D.carrier] [Nontrivial D.carrier]
    (hdiv : Bimod.IsSuperDivision D.grading)
    [IsSuperCentral D'.grading] [IsGradedSimple D'.grading]
    [FiniteDimensional K D'.carrier] [Nontrivial D'.carrier]
    (hdiv' : Bimod.IsSuperDivision D'.grading)
    (hmk : BWMonoid.mk D = BWMonoid.mk D') :
    Nonempty (SuperAlgEquiv D D') := by
  have hIBE : IsBWEquivalent D D' := BWMonoid.mk_eq_mk_iff.mp hmk
  obtain ⟨p, q, p', q', hpq, hpq', ⟨e⟩⟩ := hIBE
  haveI : IsGradedSimple (D.matrixSuper p q).grading :=
    isGradedSimple_matrixSuper_of_isSuperDivision D p q hpq hdiv
  exact wedderburn_uniqueness D D' hdiv hdiv' hpq hpq' e

end BWCorollary

end Superfusion

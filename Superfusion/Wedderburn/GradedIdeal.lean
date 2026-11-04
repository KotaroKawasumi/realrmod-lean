/-
Superfusion / Wedderburn / GradedIdeal

Milestone M10-1 of the graded Wedderburn arc (docs/wedderburn-design.md):
the ideal-theoretic scaffolding feeding Step 1 ("minimal graded left
ideal") and Step 3 ("faithfulness via the annihilator") of the four-step
proof of the graded Wedderburn theorem.

**Homogeneous left ideals** (Deliverable 1).  A left ideal of a
superalgebra `A` is just an `A`-submodule of the left-regular module `A`,
`p : Submodule A A`; it is *homogeneous* if it contains the graded
components of each of its elements.  Mathlib already has exactly this
notion, `Submodule.IsHomogeneous p ℳ` (`Mathlib/RingTheory/GradedAlgebra/
Homogeneous/Submodule.lean`), instantiated with the module grading
`ℳ := 𝒜` acting on `A` by itself: the `VAdd (ZMod 2) (ZMod 2)` and
`SetLike.GradedSMul 𝒜 𝒜` obligations both discharge automatically (the
former from `Add`, the latter from `GradedAlgebra 𝒜`'s
`SetLike.GradedMonoid` structure).  This is the same instantiation the
M8a bimodule track already exercises (`Bimod/GradedModule.lean`'s
`isHomogeneous_span`), so we reuse it verbatim rather than defining a
parallel local predicate — the upstream-friendly choice (principle B).
The *same* mathlib definition, with the base ring specialized to `K`
instead of `A`, is exactly the right notion of "homogeneous `K`-subspace"
used in Deliverable 2.

**The parity automorphism** (Deliverable 2).  `Super.parityInvolution`
already builds `J : A ≃ₐ[K] A`, `a₀ + a₁ ↦ a₀ - a₁`, with `J² = id`; we
reuse it under the name `parityAut` fixed by the design record, adding
only the one fact that file does not need: a `J`-stable `K`-subspace is
homogeneous (`isGraded_of_parityAut_stable`), the input to Step 3's
semisimplicity-via-the-`ε`-trick argument.

**Minimal homogeneous left ideal** (Deliverable 3).  Existence, by
well-ordering the (nonempty, since `⊤` qualifies) set of `K`-dimensions
of nonzero homogeneous left ideals and taking a minimizer: any
homogeneous sub-ideal strictly smaller than the minimizer would have
strictly smaller `K`-dimension, contradicting minimality unless it is
`⊥`.  `I ≠ ⊥` upgrades for free to `Nontrivial ↥I`
(`nontrivial_of_ne_bot`), the form later rounds need.

**Subtype glue** (added after the design review that produced this
file's addendum).  The degree-`j` layer of a homogeneous left ideal `I`,
viewed inside the subtype `↥I` rather than inside `A`, and the
`DirectSum.Decomposition` this gives `↥I` — mirroring
`Bimod/GradedModule.lean`'s `quotGrading`/`quotDecomposition`
construction, but for a *sub*object rather than a quotient
(`Bimod.modProj 𝒜 j`, restricted to `I` via `LinearMap.restrict`, using
homogeneity for the invariance proof, in place of `quotProj`'s
`Submodule.liftQ`).  The `Module A ↥I` and `IsScalarTower K A ↥I`
instances need no construction: mathlib finds them automatically from
the ordinary submodule instances, and `↥I` and `↥(I.restrictScalars K)`
carry definitionally equal `K`-module structures
(`finrank_ideal_eq_finrank_restrictScalars`), so the `finrank` arithmetic
of Deliverable 3 transfers to `↥I` without further work.  No `Module
(Module.End …) …` instance is introduced here; that is later-round
territory.

**Annihilator homogeneity and faithfulness** (Deliverable 4).  The
annihilator of a left ideal `I` is automatically a *two-sided* ideal
(the left-ideal property of `I` — `A • I ⊆ I` — is exactly what is
needed to push a right multiplication through); we build it directly as
a `TwoSidedIdeal A` (`Super/Basic.lean`'s interface), rather than routing
through `Module.annihilator`'s one-sided `Ideal` type, so it plugs
straight into `TwoSidedIdeal.IsHomogeneous`/`IsGradedSimple`.
Homogeneity of `I` forces homogeneity of its annihilator (an element
annihilating a homogeneous `n` has each graded component individually
annihilating `n`, by the same complementary-grade argument as
`RegularSchur.lean`'s `parts_eq_of_add_eq`); graded simplicity of `A`
then forces the annihilator of any nonzero homogeneous `I` to be `⊥`.
-/
import Superfusion.Super.ParityInvolution
import Superfusion.Bimod.GradedModule
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Superfusion

/-! ### Deliverable 1: homogeneous left ideals -/

section HomogeneousLeftIdeal

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- `⊥` is (trivially) a homogeneous left ideal. -/
theorem isHomogeneous_bot : (⊥ : Submodule A A).IsHomogeneous 𝒜 := by
  intro i x hx
  rw [Submodule.mem_bot] at hx
  subst hx
  rw [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  exact Submodule.zero_mem _

/-- `⊤` is (trivially) a homogeneous left ideal. -/
theorem isHomogeneous_top : (⊤ : Submodule A A).IsHomogeneous 𝒜 :=
  fun _ _ _ => Submodule.mem_top

/-- Explicit component-membership form of homogeneity for a left ideal,
in the exact shape of `Super/Basic.lean`'s `TwoSidedIdeal.IsHomogeneous`
(the raw mathlib predicate has the same content behind a strict-implicit
binder; this is the directly-callable, explicit-argument restatement): a
homogeneous `p` contains the graded components of each of its
elements. -/
theorem isHomogeneous_decompose_mem {p : Submodule A A} (hp : p.IsHomogeneous 𝒜)
    {j : ZMod 2} {m : A} (hm : m ∈ p) : ((DirectSum.decompose 𝒜 m j : 𝒜 j) : A) ∈ p :=
  hp j hm

/-- The even projection, in `decompose`-form (the `evenPart` analogue of
`SuperOpposite.lean`'s `oddPart_apply`, absent from `RegularSchur.lean`
since that file never needs it explicitly). -/
theorem evenPart_apply (a : A) : evenPart 𝒜 a = (DirectSum.decompose 𝒜 a 0 : A) := rfl

end HomogeneousLeftIdeal

/-! ### Deliverable 2: the parity automorphism -/

section ParityAut

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- The parity automorphism `a₀ + a₁ ↦ a₀ - a₁`: the design record's
`ε` (docs/wedderburn-design.md, Step 3).  This is exactly
`Super.parityInvolution`, reused verbatim under the name fixed by the
design record; this file adds only the one extra fact that
`ParityInvolution.lean`'s M4 development does not need,
`isGraded_of_parityAut_stable`. -/
noncomputable def parityAut : A ≃ₐ[K] A := parityInvolution 𝒜

theorem parityAut_eq_parityInvolution (a : A) :
    parityAut 𝒜 a = parityInvolution 𝒜 a := rfl

theorem parityAut_apply (a : A) : parityAut 𝒜 a = evenPart 𝒜 a - oddPart 𝒜 a :=
  parityInvolution_apply 𝒜 a

theorem parityAut_apply_of_mem_even {a : A} (ha : a ∈ 𝒜 0) : parityAut 𝒜 a = a := by
  rw [parityAut_apply, evenPart_of_mem_zero 𝒜 ha, oddPart_of_mem_zero 𝒜 ha, sub_zero]

theorem parityAut_apply_of_mem_odd {a : A} (ha : a ∈ 𝒜 1) : parityAut 𝒜 a = -a := by
  rw [parityAut_apply, evenPart_of_mem_one 𝒜 ha, oddPart_of_mem_one 𝒜 ha, zero_sub]

/-- `ε² = id`. -/
theorem parityAut_parityAut (a : A) : parityAut 𝒜 (parityAut 𝒜 a) = a := by
  rw [parityAut_eq_parityInvolution, parityAut_eq_parityInvolution]
  exact parityMap_parityMap 𝒜 a

/-- **Key lemma** (Step 3 of the design record): a `K`-subspace stable
under the parity automorphism is homogeneous.  Its even part is
`⅟2•(w+εw)`, its odd part `⅟2•(w-εw)`
(`evenPart_eq_of_invertible`/`oddPart_eq_of_invertible`, from
`ParityInvolution.lean`), both manifestly in `W` once `w` and `εw` both
are. -/
theorem isGraded_of_parityAut_stable [Invertible (2 : K)] {W : Submodule K A}
    (hW : ∀ w ∈ W, parityAut 𝒜 w ∈ W) : W.IsHomogeneous 𝒜 := by
  have hW' : ∀ w ∈ W, parityInvolution 𝒜 w ∈ W := fun w hw => by
    have h := hW w hw
    rwa [parityAut_eq_parityInvolution] at h
  intro i x hx
  rcases zmod2_cases i with hi | hi <;> subst hi
  · show evenPart 𝒜 x ∈ W
    rw [evenPart_eq_of_invertible 𝒜 x]
    exact W.smul_mem _ (W.add_mem hx (hW' x hx))
  · show oddPart 𝒜 x ∈ W
    rw [oddPart_eq_of_invertible 𝒜 x]
    exact W.smul_mem _ (W.sub_mem hx (hW' x hx))

/-- The `A`-submodule corollary needed downstream: a parity-stable left
ideal is homogeneous, by restricting scalars to `K` and applying the
subspace version. -/
theorem isHomogeneous_of_parityAut_stable [Invertible (2 : K)] {p : Submodule A A}
    (hp : ∀ w ∈ p, parityAut 𝒜 w ∈ p) : p.IsHomogeneous 𝒜 := by
  intro i x hx
  have hx' : x ∈ p.restrictScalars K := hx
  have hp' : ∀ w ∈ p.restrictScalars K, parityAut 𝒜 w ∈ p.restrictScalars K :=
    fun w hw => hp w hw
  exact isGraded_of_parityAut_stable 𝒜 hp' i hx'

end ParityAut

/-! ### Deliverable 3: a minimal nonzero homogeneous left ideal -/

section Nontrivial

variable {A : Type*} [Ring A]

/-- A nonzero left ideal, viewed as a subtype, is nontrivial — the form
later rounds (which build a `Module`/`Basis` theory on `↥I`) actually
need `I ≠ ⊥` in. -/
theorem nontrivial_of_ne_bot {I : Submodule A A} (h : I ≠ ⊥) : Nontrivial ↥I :=
  Submodule.nontrivial_iff_ne_bot.mpr h

end Nontrivial

section MinimalIdeal

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable [Nontrivial A] [FiniteDimensional K A]

open Module

/-- **Existence of a minimal nonzero homogeneous left ideal** (Step 1 of
the design record's four-step proof): among the nonzero homogeneous left
ideals of `A` — a nonempty set of `K`-dimensions, since `⊤` qualifies
(`Nontrivial A` forces `⊤ ≠ ⊥`) — pick one of least `K`-dimension.  Any
homogeneous sub-ideal strictly smaller than it would have strictly
smaller `K`-dimension (`Submodule.finrank_lt_finrank_of_lt`, applied
after `restrictScalars K`), contradicting minimality unless it is `⊥`. -/
theorem exists_minimal_homogeneous_leftIdeal :
    ∃ I : Submodule A A, I.IsHomogeneous 𝒜 ∧ I ≠ ⊥ ∧
      ∀ J : Submodule A A, J.IsHomogeneous 𝒜 → J ≤ I → J = ⊥ ∨ J = I := by
  classical
  have hex : ∃ n : ℕ, ∃ I : Submodule A A, I.IsHomogeneous 𝒜 ∧ I ≠ ⊥ ∧
      finrank K (I.restrictScalars K) = n :=
    ⟨_, ⊤, isHomogeneous_top 𝒜, bot_ne_top.symm, rfl⟩
  obtain ⟨I, hIhom, hIbot, hIrank⟩ := Nat.find_spec hex
  refine ⟨I, hIhom, hIbot, ?_⟩
  intro J hJhom hJle
  by_contra hcon
  push Not at hcon
  obtain ⟨hJbot, hJneI⟩ := hcon
  have hJltI : J < I := lt_of_le_of_ne hJle hJneI
  have hJltI' : J.restrictScalars K < I.restrictScalars K := by
    rwa [Submodule.restrictScalars_lt]
  have hrk : finrank K (J.restrictScalars K) < finrank K (I.restrictScalars K) :=
    Submodule.finrank_lt_finrank_of_lt hJltI'
  have hJmem : ∃ I : Submodule A A, I.IsHomogeneous 𝒜 ∧ I ≠ ⊥ ∧
      finrank K (I.restrictScalars K) = finrank K (J.restrictScalars K) :=
    ⟨J, hJhom, hJbot, rfl⟩
  exact Nat.find_min hex (hIrank ▸ hrk) hJmem

end MinimalIdeal

/-! ### Subtype glue: the induced grading on `↥I`

For a homogeneous left ideal `I`, the subtype `↥I` inherits both the
ordinary `A`-module structure of a submodule (`Submodule.instModule`,
found automatically) and, compatibly (`IsScalarTower K A ↥I`, again
automatic from mathlib's `Submodule.restrictScalars.isScalarTower`
together with the standard `IsScalarTower K A A` instance of an
algebra), a `ZMod 2`-grading pulled back from `𝒜` along the inclusion
`↥I ↪ A`.  This mirrors `Bimod/GradedModule.lean`'s
`quotGrading`/`quotDecomposition` construction for a *sub*object rather
than a quotient: `Bimod.modProj 𝒜 j`, restricted to `I` (using
homogeneity for the invariance proof, `LinearMap.restrict`) in place of
`quotProj`'s `Submodule.liftQ`. -/

section IdealSubtype

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (I : Submodule A A)

/-- The degree-`j` layer of `I`, as a `K`-submodule of the subtype `↥I`:
the pullback of `𝒜 j` along the inclusion `↥I ↪ A`. -/
def idealGrading (j : ZMod 2) : Submodule K ↥I :=
  (𝒜 j).comap (I.restrictScalars K).subtype

omit [GradedAlgebra 𝒜] in
theorem mem_idealGrading_iff {j : ZMod 2} {x : ↥I} :
    x ∈ idealGrading 𝒜 I j ↔ (x : A) ∈ 𝒜 j :=
  Submodule.mem_comap

/-- `↥I` carries the same `K`-vector space structure whether it is
reached via the `A`-submodule instance or via `I.restrictScalars K`:
this is the bridge letting the `finrank` computations of
`exists_minimal_homogeneous_leftIdeal` (stated for `I.restrictScalars K`)
transfer to statements about `↥I` (the shape later rounds want). -/
theorem finrank_ideal_eq_finrank_restrictScalars :
    Module.finrank K ↥I = Module.finrank K (I.restrictScalars K) := rfl

variable {I}

/-- `Bimod.modProj 𝒜 j`, restricted to (both the domain and the
codomain) `↥I`: the degree-`j` grade projection of `A`, corestricted
using homogeneity of `I`. -/
noncomputable def idealProjAmbient (hI : I.IsHomogeneous 𝒜) (j : ZMod 2) :
    ↥I →ₗ[K] ↥I :=
  (Bimod.modProj 𝒜 j).restrict (p := I.restrictScalars K) (q := I.restrictScalars K)
    (fun x hx => by rw [Bimod.modProj_apply]; exact hI j hx)

theorem idealProjAmbient_coe (hI : I.IsHomogeneous 𝒜) (j : ZMod 2) (x : ↥I) :
    (idealProjAmbient 𝒜 hI j x : A) = Bimod.modProj 𝒜 j (x : A) := rfl

theorem idealProjAmbient_mem (hI : I.IsHomogeneous 𝒜) (j : ZMod 2) (x : ↥I) :
    idealProjAmbient 𝒜 hI j x ∈ idealGrading 𝒜 I j := by
  rw [mem_idealGrading_iff, idealProjAmbient_coe, Bimod.modProj_apply]
  exact Submodule.coe_mem _

theorem idealProjAmbient_of_mem (hI : I.IsHomogeneous 𝒜) {j : ZMod 2} {x : ↥I}
    (hx : x ∈ idealGrading 𝒜 I j) : idealProjAmbient 𝒜 hI j x = x := by
  apply Subtype.ext
  rw [idealProjAmbient_coe, Bimod.modProj_of_mem 𝒜 ((mem_idealGrading_iff 𝒜 I).mp hx)]

theorem idealProjAmbient_of_mem_ne (hI : I.IsHomogeneous 𝒜) {j j' : ZMod 2} {x : ↥I}
    (hx : x ∈ idealGrading 𝒜 I j) (hjj' : j ≠ j') : idealProjAmbient 𝒜 hI j' x = 0 := by
  apply Subtype.ext
  rw [idealProjAmbient_coe,
    Bimod.modProj_of_mem_ne 𝒜 ((mem_idealGrading_iff 𝒜 I).mp hx) hjj']
  rfl

theorem idealProjAmbient_zero_add_idealProjAmbient_one (hI : I.IsHomogeneous 𝒜) (x : ↥I) :
    idealProjAmbient 𝒜 hI 0 x + idealProjAmbient 𝒜 hI 1 x = x := by
  apply Subtype.ext
  rw [Submodule.coe_add, idealProjAmbient_coe, idealProjAmbient_coe,
    Bimod.modProj_zero_add_modProj_one]

/-- The degree-`j` descent, corestricted to the layer. -/
noncomputable def idealProjInto (hI : I.IsHomogeneous 𝒜) (j : ZMod 2) :
    ↥I →ₗ[K] idealGrading 𝒜 I j :=
  LinearMap.codRestrict (idealGrading 𝒜 I j) (idealProjAmbient 𝒜 hI j)
    (idealProjAmbient_mem 𝒜 hI j)

/-- **The subtype `↥I` of a homogeneous left ideal is `ZMod 2`-decomposed**
by `idealGrading` — the sub-object analogue of
`Bimod.quotDecomposition`.  An `abbrev` (the homogeneity is a hypothesis,
so this cannot be an instance), to be activated with `letI` at use
sites. -/
noncomputable abbrev idealDecomposition (hI : I.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (idealGrading 𝒜 I) where
  decompose' z :=
    DirectSum.lof K (ZMod 2) (fun j => ↥(idealGrading 𝒜 I j)) 0
        (idealProjInto 𝒜 hI 0 z)
      + DirectSum.lof K (ZMod 2) (fun j => ↥(idealGrading 𝒜 I j)) 1
        (idealProjInto 𝒜 hI 1 z)
  left_inv z := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact idealProjAmbient_zero_add_idealProjAmbient_one 𝒜 hI z
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        rw [map_zero]
        beta_reduce
        rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | of j b =>
        rcases zmod2_cases j with hj | hj <;> subst hj
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : idealProjInto 𝒜 hI 0 (b : ↥I) = b :=
            Subtype.ext (idealProjAmbient_of_mem 𝒜 hI b.2)
          have h2 : idealProjInto 𝒜 hI 1 (b : ↥I) = 0 :=
            Subtype.ext (idealProjAmbient_of_mem_ne 𝒜 hI b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : idealProjInto 𝒜 hI 0 (b : ↥I) = 0 :=
            Subtype.ext (idealProjAmbient_of_mem_ne 𝒜 hI b.2 (by decide))
          have h2 : idealProjInto 𝒜 hI 1 (b : ↥I) = b :=
            Subtype.ext (idealProjAmbient_of_mem 𝒜 hI b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

end IdealSubtype

/-! ### Deliverable 4: the annihilator, and faithfulness -/

section Annihilator

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- The annihilator of a left ideal `I`, `{a | ∀ m ∈ I, a * m = 0}`,
built directly as a `TwoSidedIdeal A` (rather than through mathlib's
one-sided `Module.annihilator`, so it plugs straight into
`TwoSidedIdeal.IsHomogeneous`/`IsGradedSimple`).  It is automatically
*two-sided*: closure under premultiplication is free, and closure under
postmultiplication uses only that `I` is a left ideal, `y * m ∈ I` for
`m ∈ I`. -/
def leftIdealAnnihilator (I : Submodule A A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a : A | ∀ m ∈ I, a * m = 0}
    (fun m _ => zero_mul m)
    (fun {x y} hx hy m hm => by rw [add_mul, hx m hm, hy m hm, add_zero])
    (fun {x} hx m hm => by rw [neg_mul, hx m hm, neg_zero])
    (fun {x y} hy m hm => by rw [mul_assoc, hy m hm, mul_zero])
    (fun {x y} hx m hm => by
      rw [mul_assoc]
      have hmem : y * m ∈ I := by simpa using I.smul_mem y hm
      exact hx _ hmem)

theorem mem_leftIdealAnnihilator_iff {I : Submodule A A} {a : A} :
    a ∈ leftIdealAnnihilator I ↔ ∀ m ∈ I, a * m = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

/-- Two elements of complementary grades summing to `0` both vanish (a
restatement of `RegularSchur.lean`'s `parts_eq_of_add_eq` with the
right-hand side `0 + 0`). -/
private theorem eq_zero_of_split {x0 x1 : A} (h0 : x0 ∈ 𝒜 0) (h1 : x1 ∈ 𝒜 1)
    (hsum : x0 + x1 = 0) : x0 = 0 ∧ x1 = 0 :=
  parts_eq_of_add_eq 𝒜 h0 (zero_mem (𝒜 0)) h1 (zero_mem (𝒜 1)) (by rw [hsum, zero_add])

/-- **Homogeneity of the annihilator**: if `I` is a homogeneous left
ideal, its annihilator is a homogeneous two-sided ideal.  The argument
(docs/wedderburn-design.md, Step 3): an `a` annihilating `I` annihilates
each homogeneous component `n` of each `m ∈ I` (homogeneity of `I` puts
those components back into `I`); splitting `a` into its own two
components, `a * n = 0` forces each `a_i * n = 0` individually, since the
two summands land in complementary grades
(`RegularSchur.lean`'s `parts_eq_of_add_eq`). -/
theorem isHomogeneous_leftIdealAnnihilator {I : Submodule A A} (hI : I.IsHomogeneous 𝒜) :
    TwoSidedIdeal.IsHomogeneous 𝒜 (leftIdealAnnihilator I) := by
  have key : ∀ a : A, (∀ m ∈ I, a * m = 0) → ∀ j : ZMod 2, ∀ n ∈ I, n ∈ 𝒜 j →
      evenPart 𝒜 a * n = 0 ∧ oddPart 𝒜 a * n = 0 := by
    intro a ha j n hnI hnj
    have han : a * n = 0 := ha n hnI
    have hsplit : evenPart 𝒜 a * n + oddPart 𝒜 a * n = 0 := by
      rw [← add_mul, evenPart_add_oddPart, han]
    rcases zmod2_cases j with hj | hj <;> subst hj
    · have h0 : evenPart 𝒜 a * n ∈ 𝒜 0 := by
        have h := SetLike.mul_mem_graded (evenPart_mem 𝒜 a) hnj
        rwa [zero_add] at h
      have h1 : oddPart 𝒜 a * n ∈ 𝒜 1 := by
        have h := SetLike.mul_mem_graded (oddPart_mem 𝒜 a) hnj
        rwa [show (1 : ZMod 2) + 0 = 1 from by decide] at h
      exact eq_zero_of_split 𝒜 h0 h1 hsplit
    · have h0 : oddPart 𝒜 a * n ∈ 𝒜 0 := by
        have h := SetLike.mul_mem_graded (oddPart_mem 𝒜 a) hnj
        rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
      have h1 : evenPart 𝒜 a * n ∈ 𝒜 1 := by
        have h := SetLike.mul_mem_graded (evenPart_mem 𝒜 a) hnj
        rwa [show (0 : ZMod 2) + 1 = 1 from by decide] at h
      have hsplit' : oddPart 𝒜 a * n + evenPart 𝒜 a * n = 0 := by rw [add_comm]; exact hsplit
      have h01 := eq_zero_of_split 𝒜 h0 h1 hsplit'
      exact ⟨h01.2, h01.1⟩
  have full : ∀ a : A, (∀ m ∈ I, a * m = 0) → ∀ m ∈ I,
      evenPart 𝒜 a * m = 0 ∧ oddPart 𝒜 a * m = 0 := by
    intro a ha m hm
    have h0 := key a ha 0 (evenPart 𝒜 m) (hI 0 hm) (evenPart_mem 𝒜 m)
    have h1 := key a ha 1 (oddPart 𝒜 m) (hI 1 hm) (oddPart_mem 𝒜 m)
    refine ⟨?_, ?_⟩
    · calc evenPart 𝒜 a * m
          = evenPart 𝒜 a * evenPart 𝒜 m + evenPart 𝒜 a * oddPart 𝒜 m := by
            rw [← mul_add, evenPart_add_oddPart]
        _ = 0 := by rw [h0.1, h1.1, add_zero]
    · calc oddPart 𝒜 a * m
          = oddPart 𝒜 a * evenPart 𝒜 m + oddPart 𝒜 a * oddPart 𝒜 m := by
            rw [← mul_add, evenPart_add_oddPart]
        _ = 0 := by rw [h0.2, h1.2, add_zero]
  intro a ha i
  rw [mem_leftIdealAnnihilator_iff] at ha ⊢
  rcases zmod2_cases i with hi | hi <;> subst hi <;> intro m hm
  · rw [← evenPart_apply]
    exact (full a ha m hm).1
  · rw [← oddPart_apply]
    exact (full a ha m hm).2

/-- **Faithfulness** (Step 3 of the design record): if `A` is graded-
simple, the annihilator of any nonzero homogeneous left ideal `I` is
trivial.  The annihilator is a homogeneous two-sided ideal, hence `⊥` or
`⊤` by graded simplicity; it is not `⊤`, since `1` acts as the identity
on the nonzero `I`. -/
theorem leftIdealAnnihilator_eq_bot [IsGradedSimple 𝒜] {I : Submodule A A}
    (hI : I.IsHomogeneous 𝒜) (hIbot : I ≠ ⊥) : leftIdealAnnihilator I = ⊥ := by
  have hhom := isHomogeneous_leftIdealAnnihilator 𝒜 hI
  rcases IsGradedSimple.eq_bot_or_eq_top (leftIdealAnnihilator I) hhom with h | h
  · exact h
  · exfalso
    apply hIbot
    rw [Submodule.eq_bot_iff]
    intro m hm
    have h1 : (1 : A) ∈ leftIdealAnnihilator I := h ▸ TwoSidedIdeal.mem_top A
    have h2 := mem_leftIdealAnnihilator_iff.mp h1 m hm
    rwa [one_mul] at h2

end Annihilator

end Superfusion

/-
Superfusion / Wedderburn / Density

Milestone M10-3 of the graded Wedderburn arc (docs/wedderburn-design.md):
**density**, Step 3 of the four-step proof.  For the minimal homogeneous
left ideal `I` of a graded-simple finite-dimensional superalgebra `A`,
with `E := Module.End A ↥I` (a super division algebra by M10-2), the
representation `ρ : A → Module.End E ↥I` (left multiplication, viewed as
`E`-linear since `E` already commutes with the `A`-action by definition)
is an injective, surjective, *graded* algebra homomorphism.

**The density input is mathlib's Jacobson density corollary**
(`Module.Finite.toModuleEnd_moduleEnd_surjective`,
`Mathlib/RingTheory/SimpleModule/Basic.lean:588`) — this file is an
upstream-friendly wrapper around that theorem, not a re-derivation of
Jacobson density itself: all the work here is (a) upgrading the raw
`RingHom` `Module.toModuleEnd` to an `AlgHom` over `K`, (b) connecting its
kernel to M10-1's `leftIdealAnnihilator`, (c) assembling the finiteness
hypothesis from `FiniteDimensional K A`, and (d) proving `ρ` is graded
against `densityEndGrading`.

**Deliverable 1 — the representation.**  `densityRep : A →ₐ[K] Module.End
(Module.End A ↥I) ↥I` is `AlgHom.mk'` applied to mathlib's
`Module.toModuleEnd (Module.End A ↥I) (S := A) ↥I`; the `K`-linearity
obligation reduces, after unfolding both sides to their action on a test
vector `y : ↥I`, to `smul_assoc : (c • x) • y = c • (x • y)` for the tower
`K → A → ↥I`.  *Instance discipline*: the codomain's `Algebra K (Module.End
(Module.End A ↥I) ↥I)` structure is found by the same route as M10-2's
`Algebra K (Module.End A ↥I)` — `Module.End.instAlgebra` at `R := K`,
`S := Module.End A ↥I`, `M := ↥I` — whose three hypotheses are again
mathlib global instances (`Module.End.apply_smulCommClass'`,
`Module.End.apply_isScalarTower`), so no repo-local `Module`/`Algebra`
instance is declared here.

**Deliverable 2 — injectivity.**  `ρ a = 0` unfolds (via
`DFunLike.congr_fun` and the subtype-coercion form of the `↥I`-action) to
`∀ m ∈ I, a * m = 0`, exactly M10-1's `mem_leftIdealAnnihilator_iff`; under
`IsGradedSimple 𝒜` and `I ≠ ⊥`, M10-1's `leftIdealAnnihilator_eq_bot`
collapses this to `a = 0`.

**Deliverable 3 — finiteness and surjectivity.**  `Module.Finite
(Module.End A ↥I) ↥I` is assembled from `Module.Finite K ↥I` (a submodule
of the finite-dimensional `A`) via
`Module.Finite.of_restrictScalars_finite K (Module.End A ↥I) ↥I`, needing
only the tower instances already in scope.  Surjectivity of `ρ` is then
mathlib's `Module.Finite.toModuleEnd_moduleEnd_surjective` under
`IsSemisimpleModule A ↥I` (M10-2's `isSemisimpleModule_of_minimal`,
the "ε-trick"); it transports from the underlying `RingHom` to `ρ`
*definitionally* since `AlgHom.mk'` does not change the coercion to a
function.

**Deliverable 4 — the `E`-graded structure on the codomain and
gradedness of `ρ`.**  `densityEndGrading d` is the `endIdealGrading`-shaped
submodule of `Module.End (Module.End A ↥I) ↥I` (an `E`-linear map is in
particular `K`-linear via the `K → E → ↥I` tower, so this is well-formed
as a `K`-submodule): degree-`d` maps shift every `idealGrading` layer by
`d`.  `densityRep_mem_grading` shows `ρ(𝒜 d) ⊆` degree `d`, by the same
grade-shift computation as M10-1's annihilator homogeneity.  Only
**directness** of the two-piece decomposition is proved as a general fact
(`densityEndGrading_directness`, `grading 0 ⊓ grading 1 = ⊥`, since a `g`
in both sends every homogeneous layer into `idealGrading j ⊓ idealGrading
(j+1) = 0` and `↥I` is spanned by its homogeneous layers); **spanning**
(`densityEndGrading_spanning`) is deduced from surjectivity of `ρ`
together with the additive splitting `a = evenPart a + oddPart a`.
Combining directness, spanning, and injectivity gives the two-sided
equality `densityRep_grading_eq : Submodule.map ρ.toLinearMap (𝒜 d) =
densityEndGrading d`.

**What M10-4 should consume.**  The `Nonempty (A ≃ₐ[K] Module.End
(Module.End A ↥I) ↥I)`-style bundled statement is *not* built here (per
the design record, a heavy bundle is deferred to the matrix-realization
round); M10-4 should instead assemble its own graded `AlgEquiv` directly
from `densityRep_bijective` (an `AlgEquiv.ofBijective`) together with
`densityRep_grading_eq` (which supplies, for each `d`, the exact image of
`𝒜 d` under that equivalence — the data a `GradedAlgHom`/graded-equiv
transport lemma would need) and `densityEndGrading_directness` (for the
`SetLike.GradedMonoid`/`Decomposition` obligations on the codomain, once
M10-4 fixes a basis and transports the grading across the matrix
identification).
-/
import Superfusion.Wedderburn.GradedSchur

namespace Superfusion

/-! ### Deliverable 1: the representation `ρ` -/

section DensityRep

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable {I : Submodule A A}

/-- **The density representation** `ρ : A → Module.End (Module.End A ↥I)
↥I`: left multiplication by `a`, viewed as an `E`-linear endomorphism of
`↥I` for `E := Module.End A ↥I` (well-defined for *any* submodule `I`,
with no homogeneity hypothesis — the grading enters only in Deliverable
4).  Built from mathlib's `Module.toModuleEnd` `RingHom`, upgraded to a
`K`-algebra map via `AlgHom.mk'` and `smul_assoc` for the `K → A → ↥I`
tower. -/
noncomputable def densityRep : A →ₐ[K] Module.End (Module.End A ↥I) ↥I :=
  AlgHom.mk' (Module.toModuleEnd (Module.End A ↥I) (S := A) ↥I) fun c x => by
    apply LinearMap.ext
    intro y
    show (c • x) • y = c • ((Module.toModuleEnd (Module.End A ↥I) (S := A) ↥I) x y)
    rw [smul_assoc]
    rfl

theorem densityRep_apply (a : A) (m : ↥I) : densityRep (K := K) (I := I) a m = a • m := rfl

end DensityRep

/-! ### Deliverable 2: injectivity -/

section Injectivity

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

/-- `ρ a = 0` iff `a` annihilates `I` (M10-1's `leftIdealAnnihilator`):
unfold `ρ a = 0` at a test vector `⟨m, hm⟩ : ↥I` in one direction, and
rebuild the `A`-linear map `y ↦ a • y` (already zero on each coordinate)
in the other. -/
theorem densityRep_eq_zero_iff (a : A) :
    densityRep (K := K) (I := I) a = 0 ↔ a ∈ leftIdealAnnihilator I := by
  rw [mem_leftIdealAnnihilator_iff]
  constructor
  · intro h m hm
    have h2 : (a • (⟨m, hm⟩ : ↥I) : ↥I) = (0 : ↥I) :=
      DFunLike.congr_fun h (⟨m, hm⟩ : ↥I)
    have h3 := congrArg Subtype.val h2
    simpa using h3
  · intro h
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    show a * (y : A) = (0 : A)
    exact h y.1 y.2

/-- **Injectivity of `ρ`** (Deliverable 2): under graded simplicity of
`A` and `I ≠ ⊥`, M10-1's `leftIdealAnnihilator_eq_bot` collapses the
kernel of `ρ` to `0`. -/
theorem densityRep_injective [IsGradedSimple 𝒜] (hI : I.IsHomogeneous 𝒜) (hne : I ≠ ⊥) :
    Function.Injective (densityRep (K := K) (A := A) (I := I)) := by
  intro a b hab
  have hz : densityRep (K := K) (I := I) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [densityRep_eq_zero_iff, leftIdealAnnihilator_eq_bot 𝒜 hI hne, TwoSidedIdeal.mem_bot] at hz
  exact sub_eq_zero.mp hz

end Injectivity

/-! ### Deliverable 3: finiteness and surjectivity -/

section Density

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

/-- **Surjectivity of `ρ`** (Deliverable 3): mathlib's Jacobson density
corollary `Module.Finite.toModuleEnd_moduleEnd_surjective`, applied to
`R := A`, `M := ↥I`, under `IsSemisimpleModule A ↥I` (the "ε-trick",
M10-2's `isSemisimpleModule_of_minimal`) and `Module.Finite (Module.End
A ↥I) ↥I` (assembled from `Module.Finite K ↥I`, a submodule of the
finite-dimensional `A`, via `Module.Finite.of_restrictScalars_finite`).
Transports to `ρ` definitionally, since `AlgHom.mk'` preserves the
underlying function. -/
theorem densityRep_surjective (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hne : I ≠ ⊥) [FiniteDimensional K A] [Invertible (2 : K)] :
    Function.Surjective (densityRep (K := K) (A := A) (I := I)) := by
  haveI : IsSemisimpleModule A ↥I := isSemisimpleModule_of_minimal 𝒜 hI hsimple hne
  haveI : FiniteDimensional K ↥I := FiniteDimensional.finiteDimensional_submodule
    (I.restrictScalars K)
  haveI : Module.Finite (Module.End A ↥I) ↥I :=
    Module.Finite.of_restrictScalars_finite K (Module.End A ↥I) ↥I
  intro g
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := ↥I) g
  exact ⟨a, ha⟩

/-- **Bijectivity of `ρ`** (Deliverables 2+3 combined). -/
theorem densityRep_bijective [IsGradedSimple 𝒜] (hI : I.IsHomogeneous 𝒜)
    (hsimple : IsGradedSimpleIdeal 𝒜 I) (hne : I ≠ ⊥)
    [FiniteDimensional K A] [Invertible (2 : K)] :
    Function.Bijective (densityRep (K := K) (A := A) (I := I)) :=
  ⟨densityRep_injective 𝒜 hI hne, densityRep_surjective 𝒜 hI hsimple hne⟩

end Density

/-! ### Deliverable 4: the `E`-graded structure and gradedness of `ρ` -/

section Grading

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

/-- The parity grading on `Module.End (Module.End A ↥I) ↥I`, relative to
`I`'s own grading `idealGrading 𝒜 I`: degree-`d` maps shift every layer by
`d` (the `densityRep`-side analogue of M10-2's `endIdealGrading`; an
`E`-linear endomorphism of `↥I`, `E := Module.End A ↥I`, is in particular
`K`-linear via the `K → E → ↥I` tower, so this is a well-formed
`K`-submodule).  The parameter `_hI` is carried purely for API-naming
uniformity, mirroring `endIdealGrading`. -/
def densityEndGrading (_hI : I.IsHomogeneous 𝒜) (d : ZMod 2) :
    Submodule K (Module.End (Module.End A ↥I) ↥I) where
  carrier := {g | ∀ (j : ZMod 2) (x : ↥I), x ∈ idealGrading 𝒜 I j →
    g x ∈ idealGrading 𝒜 I (j + d)}
  zero_mem' := fun j x _ => by
    rw [LinearMap.zero_apply]
    exact zero_mem _
  add_mem' {f g} hf hg := fun j x hx => by
    rw [LinearMap.add_apply]
    exact add_mem (hf j x hx) (hg j x hx)
  smul_mem' c f hf := fun j x hx => by
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (hf j x hx)

theorem mem_densityEndGrading {hI : I.IsHomogeneous 𝒜} {d : ZMod 2}
    {g : Module.End (Module.End A ↥I) ↥I} :
    g ∈ densityEndGrading 𝒜 hI d ↔
      ∀ (j : ZMod 2) (x : ↥I), x ∈ idealGrading 𝒜 I j → g x ∈ idealGrading 𝒜 I (j + d) :=
  Iff.rfl

/-- **`ρ` is graded** (Deliverable 4): left multiplication by a
homogeneous `a` of degree `d` shifts every `idealGrading` layer by `d`
(the same computation as M10-1's `modProj_smul_of_mem`/M10-2's
`idealProjAmbient_smul_of_mem`, restated in coordinate-free form via
`SetLike.mul_mem_graded`). -/
theorem densityRep_mem_grading (hI : I.IsHomogeneous 𝒜) {d : ZMod 2} {a : A} (ha : a ∈ 𝒜 d) :
    densityRep (K := K) (I := I) a ∈ densityEndGrading 𝒜 hI d := by
  intro j x hx
  have hx' : (x : A) ∈ 𝒜 j := (mem_idealGrading_iff 𝒜 I).mp hx
  have h := SetLike.mul_mem_graded ha hx'
  rw [add_comm d j] at h
  show (a • x : A) ∈ 𝒜 (j + d)
  rwa [smul_eq_mul]

private theorem zmod2_density_ne_add_one : ∀ j : ZMod 2, j + 1 ≠ j := by decide

/-- **Directness** of the two-piece decomposition (Deliverable 4): a `g`
lying in both `densityEndGrading 0` and `densityEndGrading 1` sends every
homogeneous layer of `↥I` into `idealGrading j ⊓ idealGrading (j+1) = 0`
(via M10-1's `idealProjAmbient_of_mem`/`_of_mem_ne`), and `↥I` is spanned
by its two homogeneous layers
(`idealProjAmbient_zero_add_idealProjAmbient_one`), so `g = 0`. -/
theorem densityEndGrading_directness (hI : I.IsHomogeneous 𝒜) :
    densityEndGrading 𝒜 hI 0 ⊓ densityEndGrading 𝒜 hI 1 = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Submodule.mem_bot]
  have hzero : ∀ (j : ZMod 2) (y : ↥I), y ∈ idealGrading 𝒜 I j → g y = 0 := by
    intro j y hy
    have h0 : g y ∈ idealGrading 𝒜 I (j + 0) := hg.1 j y hy
    have h1 : g y ∈ idealGrading 𝒜 I (j + 1) := hg.2 j y hy
    rw [add_zero] at h0
    have e0 := idealProjAmbient_of_mem 𝒜 hI h0
    have e1 := idealProjAmbient_of_mem_ne 𝒜 hI h1 (zmod2_density_ne_add_one j)
    rw [e1] at e0
    exact e0.symm
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  conv_lhs => rw [← idealProjAmbient_zero_add_idealProjAmbient_one 𝒜 hI x]
  rw [map_add, hzero 0 _ (idealProjAmbient_mem 𝒜 hI 0 x),
    hzero 1 _ (idealProjAmbient_mem 𝒜 hI 1 x), add_zero]

/-- **Spanning** of the two-piece decomposition (Deliverable 4): every
`g` is `ρ(evenPart a) + ρ(oddPart a)` for a preimage `a` of `g` under the
surjective `ρ`, and each summand lies in the matching grade by
`densityRep_mem_grading`. -/
theorem densityEndGrading_spanning (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hne : I ≠ ⊥) [FiniteDimensional K A] [Invertible (2 : K)]
    (g : Module.End (Module.End A ↥I) ↥I) :
    ∃ g0 ∈ densityEndGrading 𝒜 hI 0, ∃ g1 ∈ densityEndGrading 𝒜 hI 1, g = g0 + g1 := by
  obtain ⟨a, rfl⟩ := densityRep_surjective 𝒜 hI hsimple hne g
  refine ⟨densityRep (K := K) (I := I) (evenPart 𝒜 a), densityRep_mem_grading 𝒜 hI (evenPart_mem 𝒜 a),
    densityRep (K := K) (I := I) (oddPart 𝒜 a), densityRep_mem_grading 𝒜 hI (oddPart_mem 𝒜 a), ?_⟩
  rw [← map_add, evenPart_add_oddPart]

/-- **`ρ(𝒜 d) = densityEndGrading d`** (Deliverable 4, the referee route):
`⊆` is `densityRep_mem_grading`; for `⊇`, split a preimage `a` of
`g ∈ densityEndGrading d` into its degree-`d` and degree-`(d+1)` parts —
`ρ` of the degree-`(d+1)` part then lies in `densityEndGrading d ⊓
densityEndGrading (d+1) = densityEndGrading 0 ⊓ densityEndGrading 1 = ⊥`
(directness), hence vanishes, hence (by injectivity) that part of `a`
itself vanishes, leaving `g = ρ` of the degree-`d` part. -/
theorem densityRep_grading_eq [IsGradedSimple 𝒜] (hI : I.IsHomogeneous 𝒜)
    (hsimple : IsGradedSimpleIdeal 𝒜 I) (hne : I ≠ ⊥)
    [FiniteDimensional K A] [Invertible (2 : K)] (d : ZMod 2) :
    Submodule.map (densityRep (K := K) (A := A) (I := I)).toLinearMap (𝒜 d) =
      densityEndGrading 𝒜 hI d := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact densityRep_mem_grading 𝒜 hI ha
  · intro g hg
    obtain ⟨a, rfl⟩ := densityRep_surjective 𝒜 hI hsimple hne g
    rcases zmod2_cases d with hd | hd <;> subst hd
    · have hmap : densityRep (K := K) (I := I) (evenPart 𝒜 a) + densityRep (K := K) (I := I) (oddPart 𝒜 a) =
          densityRep (K := K) (I := I) a := by
        rw [← map_add, evenPart_add_oddPart]
      have heven_mem : densityRep (K := K) (I := I) (evenPart 𝒜 a) ∈ densityEndGrading 𝒜 hI 0 :=
        densityRep_mem_grading 𝒜 hI (evenPart_mem 𝒜 a)
      have hodd_mem1 : densityRep (K := K) (I := I) (oddPart 𝒜 a) ∈ densityEndGrading 𝒜 hI 1 :=
        densityRep_mem_grading 𝒜 hI (oddPart_mem 𝒜 a)
      have hodd_mem0 : densityRep (K := K) (I := I) (oddPart 𝒜 a) ∈ densityEndGrading 𝒜 hI 0 := by
        have heq : densityRep (K := K) (I := I) (oddPart 𝒜 a) =
            densityRep (K := K) (I := I) a - densityRep (K := K) (I := I) (evenPart 𝒜 a) := by
          rw [eq_sub_iff_add_eq, add_comm]
          exact hmap
        rw [heq]
        exact (densityEndGrading 𝒜 hI 0).sub_mem hg heven_mem
      have hodd_zero : densityRep (K := K) (I := I) (oddPart 𝒜 a) = 0 := by
        have hmem : densityRep (K := K) (I := I) (oddPart 𝒜 a) ∈
            densityEndGrading 𝒜 hI 0 ⊓ densityEndGrading 𝒜 hI 1 := ⟨hodd_mem0, hodd_mem1⟩
        rwa [densityEndGrading_directness 𝒜 hI, Submodule.mem_bot] at hmem
      have ha_odd_zero : oddPart 𝒜 a = 0 := by
        apply densityRep_injective 𝒜 hI hne
        rw [hodd_zero, map_zero]
      refine ⟨evenPart 𝒜 a, evenPart_mem 𝒜 a, ?_⟩
      have heq := evenPart_add_oddPart 𝒜 a
      rw [ha_odd_zero, add_zero] at heq
      rw [heq]
      rfl
    · have hmap : densityRep (K := K) (I := I) (oddPart 𝒜 a) + densityRep (K := K) (I := I) (evenPart 𝒜 a) =
          densityRep (K := K) (I := I) a := by
        rw [← map_add, add_comm, evenPart_add_oddPart]
      have hodd_mem : densityRep (K := K) (I := I) (oddPart 𝒜 a) ∈ densityEndGrading 𝒜 hI 1 :=
        densityRep_mem_grading 𝒜 hI (oddPart_mem 𝒜 a)
      have heven_mem0 : densityRep (K := K) (I := I) (evenPart 𝒜 a) ∈ densityEndGrading 𝒜 hI 0 :=
        densityRep_mem_grading 𝒜 hI (evenPart_mem 𝒜 a)
      have heven_mem1 : densityRep (K := K) (I := I) (evenPart 𝒜 a) ∈ densityEndGrading 𝒜 hI 1 := by
        have heq : densityRep (K := K) (I := I) (evenPart 𝒜 a) =
            densityRep (K := K) (I := I) a - densityRep (K := K) (I := I) (oddPart 𝒜 a) := by
          rw [eq_sub_iff_add_eq, add_comm]
          exact hmap
        rw [heq]
        exact (densityEndGrading 𝒜 hI 1).sub_mem hg hodd_mem
      have heven_zero : densityRep (K := K) (I := I) (evenPart 𝒜 a) = 0 := by
        have hmem : densityRep (K := K) (I := I) (evenPart 𝒜 a) ∈
            densityEndGrading 𝒜 hI 0 ⊓ densityEndGrading 𝒜 hI 1 := ⟨heven_mem0, heven_mem1⟩
        rwa [densityEndGrading_directness 𝒜 hI, Submodule.mem_bot] at hmem
      have ha_even_zero : evenPart 𝒜 a = 0 := by
        apply densityRep_injective 𝒜 hI hne
        rw [heven_zero, map_zero]
      refine ⟨oddPart 𝒜 a, oddPart_mem 𝒜 a, ?_⟩
      have heq := evenPart_add_oddPart 𝒜 a
      rw [ha_even_zero, zero_add] at heq
      rw [heq]
      rfl

end Grading

end Superfusion

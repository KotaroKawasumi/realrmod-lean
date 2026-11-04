/-
Superfusion / Wedderburn / GradedSchur

Milestone M10-2 of the graded Wedderburn arc (docs/wedderburn-design.md):
**graded Schur's lemma** for the endomorphism algebra of a minimal
homogeneous left ideal, Step 2 of the four-step proof, together with the
ungraded semisimplicity of that ideal (Step 3's opening bullet, the
"ε-trick").

**The End grading** (Deliverable 1).  For a homogeneous left ideal `I`
(`hI : I.IsHomogeneous 𝒜`), `E := Module.End A ↥I` is graded by
`endIdealGrading hI i = {f | ∀ j, f (idealGrading I j) ⊆ idealGrading I
(j+i)}` — the M10-1 subtype-glue analogue of `Super/GradedEnd.lean`'s
`endGrading`, relative to `I`'s own grading (`idealGrading`) rather than
`A`'s.  *Instance discipline*: `Algebra K (Module.End A ↥I)` is found
entirely from mathlib's `Module.End.instAlgebra` (`Algebra/Algebra/
Basic.lean`), instantiated at `R := K`, `S := A`, `M := ↥I`; its three
hypotheses — `Module K ↥I`, `SMulCommClass A K ↥I`,
`IsScalarTower K A ↥I` — are each *already* global mathlib instances on
a submodule of a `K`-algebra (`Submodule.instModule`,
`IsScalarTower.to_smulCommClass'`, `Submodule.restrictScalars.
isScalarTower` respectively), so no repo-local `Module`/`Algebra`
instance is declared here at all.

**Masks preserve `A`-linearity** (Deliverable 2).  The degree-`i` mask
of `f`, built from the *`K`-linear* grade projections `idealProjAmbient`
(M10-1), is a priori only `K`-linear; the content of this deliverable is
that when `f` itself is `A`-linear, so is its mask — because left
multiplication by a homogeneous `a` shifts every grade component by
exactly `deg a` (`idealProjAmbient_smul_of_mem`, proved once at the
ambient level `A` via `modProj_smul_of_mem` and transported to `↥I` by
the `idealProjAmbient_coe` bridge), so extracting a grade component
commutes with the (unsigned, plain) module action.  Splitting a general
`a` into `evenPart a + oddPart a` upgrades the homogeneous case to all of
`A`.

**Decomposition and graded algebra structure** (Deliverable 3) follow
`GradedEnd.lean`'s mask-projection argument verbatim, with
`idealProjAmbient` in place of `gradeProj` and `endIdealMask` in place of
`endMask`.

**Graded Schur** (Deliverable 4).  A nonzero homogeneous `f` of degree
`i` has kernel and range whose *ambient images* in `A` (pushed forward
along the injective `A`-linear inclusion `I.subtype`) are homogeneous
left ideals `≤ I` — homogeneity following from the same grade-shift
argument, since `f` shifts every `idealGrading` layer by `i`.  Graded
simplicity of `I` (the hypothesis `IsGradedSimpleIdeal`, produced by
M10-1's `exists_minimal_homogeneous_leftIdeal`) forces each pushed-
forward submodule to be `⊥` or `I`; nonzero-ness of `f` rules out
`ker f = ⊤` and `range f = ⊥`, leaving `f` bijective
(`Module.End.isUnit_iff`), i.e. a unit.  Hence
`endIdeal_isSuperDivision : Bimod.IsSuperDivision (endIdealGrading hI)`.

**Ungraded semisimplicity of `I`** (Deliverable 5, the "ε-trick" of Step
3).  A minimal *ungraded* nonzero `A`-submodule `S ≤ ↥I` exists by the
same finite-dimensional well-ordering argument as M10-1's minimal
homogeneous ideal (`exists_minimal_submodule`, dropping the homogeneity
constraint); it is simple (`isSimpleModule_iff_isAtom`).  The parity
automorphism `ε` restricts to a `K`-linear involution of `↥I`
(`parityAutIdeal`, well-defined because `I` is homogeneous hence
`ε`-stable), which is *`ε`-semilinear* for the `A`-action
(`parityAutIdeal_smul`: `ε(a·x) = ε(a)·ε(x)`) — enough to push `S`
forward to a genuine `A`-submodule `εIdealSubmodule hI S`, again simple
(an atom, by the same "twist is a monotone involution" argument).  Their
sum `S ⊔ ε(S)` is `ε`-stable, hence (pushed to `A`) homogeneous by
M10-1's `isHomogeneous_of_parityAut_stable`; graded simplicity of `I`
then forces `S ⊔ ε(S) = I` (as `↥I`'s `⊤`, via the `Submodule.map`
injectivity of `I.subtype`).  `IsSemisimpleModule.sup` of the two simples
gives semisimplicity of `↥⊤ ≅ ↥I`
(`isSemisimpleModule_of_minimal`).  *Mathlib bridge*: the
`sSup`-of-simples characterization lives in
`Mathlib/RingTheory/SimpleModule/Basic.lean`; the constructor actually
used here is the more economical
`IsSemisimpleModule.sup {p q} (_ : IsSemisimpleModule R p)
(_ : IsSemisimpleModule R q) : IsSemisimpleModule R ↥(p ⊔ q)` (rather
than `IsSemisimpleModule.of_sSup_simples_eq_top`, which would need the
*whole* set of simple submodules, not just the two constructed here).
-/
import Superfusion.Wedderburn.GradedIdeal
import Superfusion.Gauge.SuperDivisionBasic
import Mathlib.RingTheory.SimpleModule.Basic

namespace Superfusion

section GradedSchur

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

/-! ### Graded-module simplicity of a homogeneous left ideal

The clean local name for the property produced by M10-1's
`exists_minimal_homogeneous_leftIdeal`: every homogeneous left ideal
`≤ I` is `⊥` or `I`. -/

/-- `I` is **graded-simple as a graded left ideal**: the only homogeneous
left ideals `≤ I` are `⊥` and `I`.  (Exactly the third conjunct produced
by `exists_minimal_homogeneous_leftIdeal`, named for reuse.) -/
def IsGradedSimpleIdeal (I : Submodule A A) : Prop :=
  ∀ J : Submodule A A, J.IsHomogeneous 𝒜 → J ≤ I → J = ⊥ ∨ J = I

/-! ### Deliverable 1: the End grading -/

/-- The parity grading on `E = Module.End A ↥I`, relative to `I`'s own
grading `idealGrading 𝒜 I`: degree-`i` maps shift every grade by `i`
(the M10-1 subtype-glue analogue of `Super/GradedEnd.lean`'s
`endGrading`).  The parameter `hI` is carried purely for API-naming
uniformity with the rest of the file (`endIdealMask`, the `Decomposition`
instance, …), which genuinely need it; the raw membership condition does
not. -/
def endIdealGrading (_hI : I.IsHomogeneous 𝒜) (i : ZMod 2) :
    Submodule K (Module.End A ↥I) where
  carrier := {f | ∀ (j : ZMod 2) (x : ↥I), x ∈ idealGrading 𝒜 I j →
    f x ∈ idealGrading 𝒜 I (j + i)}
  zero_mem' := fun j x _ => by
    rw [LinearMap.zero_apply]
    exact zero_mem _
  add_mem' {f g} hf hg := fun j x hx => by
    rw [LinearMap.add_apply]
    exact add_mem (hf j x hx) (hg j x hx)
  smul_mem' c f hf := fun j x hx => by
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (hf j x hx)

theorem mem_endIdealGrading {hI : I.IsHomogeneous 𝒜} {i : ZMod 2}
    {f : Module.End A ↥I} :
    f ∈ endIdealGrading 𝒜 hI i ↔
      ∀ (j : ZMod 2) (x : ↥I), x ∈ idealGrading 𝒜 I j →
        f x ∈ idealGrading 𝒜 I (j + i) :=
  Iff.rfl

/-! ### Deliverable 2: masks preserve `A`-linearity -/

private theorem zmod2_schur_ne_add_one : ∀ d : ZMod 2, d ≠ d + 1 := by decide

private theorem zmod2_schur_ne_add_one' : ∀ i : ZMod 2, i ≠ 1 + i := by decide

private theorem zmod2_schur_eq_or_eq_add_one :
    ∀ i j : ZMod 2, j = i ∨ j = 1 + i := by decide

private theorem zmod2_schur_shift1 : ∀ i : ZMod 2, (1 + i) + 1 = 0 + i := by decide

private theorem zmod2_schur_shift2 : ∀ i : ZMod 2, (0 + i) + 1 = 1 + i := by decide

private theorem zmod2_schur_one : ∀ i i' : ZMod 2, i ≠ i' → 1 + i ≠ 1 + i' := by decide

/-- **The grade-shift identity at the ambient level**: left multiplication
by a homogeneous `a` of degree `d` shifts the degree-`j` component to
degree `j + d` (docs/wedderburn-design.md, Step 2's unsigned
computation). -/
theorem modProj_smul_of_mem {d : ZMod 2} {a : A} (ha : a ∈ 𝒜 d)
    (j : ZMod 2) (y : A) :
    Bimod.modProj 𝒜 (j + d) (a * y) = a * Bimod.modProj 𝒜 j y := by
  have hy := Bimod.modProj_zero_add_modProj_one 𝒜 y
  have hsplit : a * y = a * Bimod.modProj 𝒜 0 y + a * Bimod.modProj 𝒜 1 y := by
    rw [← mul_add, hy]
  have h0 : a * Bimod.modProj 𝒜 0 y ∈ 𝒜 d := by
    have h := SetLike.mul_mem_graded ha (Bimod.modProj_mem 𝒜 0 y)
    rwa [add_zero] at h
  have h1 : a * Bimod.modProj 𝒜 1 y ∈ 𝒜 (d + 1) :=
    SetLike.mul_mem_graded ha (Bimod.modProj_mem 𝒜 1 y)
  rw [hsplit]
  rcases zmod2_cases j with hj | hj <;> subst hj
  · rw [zero_add, map_add, Bimod.modProj_of_mem 𝒜 h0,
      Bimod.modProj_of_mem_ne 𝒜 h1 (zmod2_schur_ne_add_one d).symm, add_zero]
  · rw [show (1 : ZMod 2) + d = d + 1 from add_comm 1 d, map_add,
      Bimod.modProj_of_mem_ne 𝒜 h0 (zmod2_schur_ne_add_one d),
      Bimod.modProj_of_mem 𝒜 h1, zero_add]

/-- The `↥I`-level transport of `modProj_smul_of_mem` along the
`idealProjAmbient_coe` bridge. -/
theorem idealProjAmbient_smul_of_mem (hI : I.IsHomogeneous 𝒜) {d : ZMod 2}
    {a : A} (ha : a ∈ 𝒜 d) (j : ZMod 2) (x : ↥I) :
    idealProjAmbient 𝒜 hI (j + d) (a • x) = a • idealProjAmbient 𝒜 hI j x := by
  apply Subtype.ext
  show (idealProjAmbient 𝒜 hI (j + d) (a • x) : A)
      = ((a • idealProjAmbient 𝒜 hI j x : ↥I) : A)
  rw [idealProjAmbient_coe, Submodule.coe_smul, smul_eq_mul,
    Submodule.coe_smul, smul_eq_mul, modProj_smul_of_mem 𝒜 ha, idealProjAmbient_coe]

variable {𝒜} in
/-- If `u ∈ idealGrading I j`, `v ∈ idealGrading I j'` with `j ≠ j'`,
then `u` is the degree-`j` grade component of `u + v` (the M10-2
"extraction" lemma, subsuming both the kernel-vanishing and
range-homogeneity arguments of Deliverable 4). -/
theorem idealProjAmbient_add_of_mem_ne (hI : I.IsHomogeneous 𝒜) {u v : ↥I}
    {j j' : ZMod 2} (hu : u ∈ idealGrading 𝒜 I j) (hv : v ∈ idealGrading 𝒜 I j')
    (hjj' : j ≠ j') : idealProjAmbient 𝒜 hI j (u + v) = u := by
  rw [map_add, idealProjAmbient_of_mem 𝒜 hI hu,
    idealProjAmbient_of_mem_ne 𝒜 hI hv (Ne.symm hjj'), add_zero]

variable {𝒜} in
/-- The companion "second-summand" extraction. -/
theorem idealProjAmbient_add_of_mem_ne' (hI : I.IsHomogeneous 𝒜) {u v : ↥I}
    {j j' : ZMod 2} (hu : u ∈ idealGrading 𝒜 I j) (hv : v ∈ idealGrading 𝒜 I j')
    (hjj' : j ≠ j') : idealProjAmbient 𝒜 hI j' (u + v) = v := by
  rw [add_comm]
  exact idealProjAmbient_add_of_mem_ne hI hv hu hjj'.symm

variable {𝒜} in
/-- The raw (uncorestricted) degree-`i` mask function on
`Module.End A ↥I`: `idealProjAmbient`-conjugation of `f`, mirroring
`GradedEnd.lean`'s `endMask`. -/
noncomputable def endIdealMaskFun (hI : I.IsHomogeneous 𝒜) (i : ZMod 2)
    (f : Module.End A ↥I) : ↥I → ↥I :=
  fun x => idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 x))
    + idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 x))

variable {𝒜} in
theorem endIdealMaskFun_add (hI : I.IsHomogeneous 𝒜) (i : ZMod 2) (f : Module.End A ↥I)
    (x y : ↥I) :
    endIdealMaskFun hI i f (x + y) = endIdealMaskFun hI i f x + endIdealMaskFun hI i f y := by
  simp only [endIdealMaskFun, map_add]
  abel

variable {𝒜} in
theorem endIdealMaskFun_add_fun (hI : I.IsHomogeneous 𝒜) (i : ZMod 2)
    (f g : Module.End A ↥I) (x : ↥I) :
    endIdealMaskFun hI i (f + g) x = endIdealMaskFun hI i f x + endIdealMaskFun hI i g x := by
  simp only [endIdealMaskFun, LinearMap.add_apply, map_add]
  abel

variable {𝒜} in
theorem endIdealMaskFun_smul_fun (hI : I.IsHomogeneous 𝒜) (i : ZMod 2) (c : K)
    (f : Module.End A ↥I) (x : ↥I) :
    endIdealMaskFun hI i (c • f) x = c • endIdealMaskFun hI i f x := by
  simp only [endIdealMaskFun, LinearMap.smul_apply, map_smul, smul_add]

variable {𝒜} in
theorem endIdealMaskFun_smul (hI : I.IsHomogeneous 𝒜) (i : ZMod 2) (f : Module.End A ↥I)
    (a : A) (x : ↥I) :
    endIdealMaskFun hI i f (a • x) = a • endIdealMaskFun hI i f x := by
  have hsplit : a = evenPart 𝒜 a + oddPart 𝒜 a := (evenPart_add_oddPart 𝒜 a).symm
  have key : ∀ {d : ZMod 2} {b : A}, b ∈ 𝒜 d →
      endIdealMaskFun hI i f (b • x) = b • endIdealMaskFun hI i f x := by
    intro d b hb
    rcases zmod2_cases d with hd | hd <;> subst hd
    · have e0 : idealProjAmbient 𝒜 hI 0 (b • x) = b • idealProjAmbient 𝒜 hI 0 x := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb 0 x
        rwa [add_zero] at h
      have e1 : idealProjAmbient 𝒜 hI 1 (b • x) = b • idealProjAmbient 𝒜 hI 1 x := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb 1 x
        rwa [add_zero] at h
      have e2 : idealProjAmbient 𝒜 hI (0 + i) (b • f (idealProjAmbient 𝒜 hI 0 x))
          = b • idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 x)) := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb (0 + i) (f (idealProjAmbient 𝒜 hI 0 x))
        rwa [add_zero] at h
      have e3 : idealProjAmbient 𝒜 hI (1 + i) (b • f (idealProjAmbient 𝒜 hI 1 x))
          = b • idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 x)) := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb (1 + i) (f (idealProjAmbient 𝒜 hI 1 x))
        rwa [add_zero] at h
      show idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 (b • x)))
          + idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 (b • x)))
        = b • (idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 x))
          + idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 x)))
      rw [e0, e1, f.map_smul, f.map_smul, e2, e3, smul_add]
    · have e0 : idealProjAmbient 𝒜 hI 0 (b • x) = b • idealProjAmbient 𝒜 hI 1 x := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb 1 x
        rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
      have e1 : idealProjAmbient 𝒜 hI 1 (b • x) = b • idealProjAmbient 𝒜 hI 0 x := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb 0 x
        rwa [zero_add] at h
      have e2 : idealProjAmbient 𝒜 hI (0 + i) (b • f (idealProjAmbient 𝒜 hI 1 x))
          = b • idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 x)) := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb (1 + i) (f (idealProjAmbient 𝒜 hI 1 x))
        rwa [zmod2_schur_shift1] at h
      have e3 : idealProjAmbient 𝒜 hI (1 + i) (b • f (idealProjAmbient 𝒜 hI 0 x))
          = b • idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 x)) := by
        have h := idealProjAmbient_smul_of_mem 𝒜 hI hb (0 + i) (f (idealProjAmbient 𝒜 hI 0 x))
        rwa [zmod2_schur_shift2] at h
      show idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 (b • x)))
          + idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 (b • x)))
        = b • (idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 x))
          + idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 x)))
      rw [e0, e1, f.map_smul, f.map_smul, e2, e3, ← smul_add, add_comm]
  calc endIdealMaskFun hI i f (a • x)
      = endIdealMaskFun hI i f ((evenPart 𝒜 a + oddPart 𝒜 a) • x) := by rw [← hsplit]
    _ = endIdealMaskFun hI i f (evenPart 𝒜 a • x) + endIdealMaskFun hI i f (oddPart 𝒜 a • x) := by
        rw [add_smul, endIdealMaskFun_add]
    _ = evenPart 𝒜 a • endIdealMaskFun hI i f x + oddPart 𝒜 a • endIdealMaskFun hI i f x :=
        congrArg₂ (· + ·) (key (evenPart_mem 𝒜 a)) (key (oddPart_mem 𝒜 a))
    _ = a • endIdealMaskFun hI i f x := by rw [← add_smul, ← hsplit]

variable {𝒜} in
/-- The degree-`i` mask, bundled as an `A`-linear map (the content of
Deliverable 2: masking a genuinely `A`-linear `f` again produces an
`A`-linear map, not merely a `K`-linear one). -/
noncomputable def endIdealMaskLM (hI : I.IsHomogeneous 𝒜) (i : ZMod 2)
    (f : Module.End A ↥I) : Module.End A ↥I where
  toFun := endIdealMaskFun hI i f
  map_add' := endIdealMaskFun_add hI i f
  map_smul' a x := endIdealMaskFun_smul hI i f a x

/-- The degree-`i` mask, as a `K`-linear self-map of `E = Module.End A ↥I`. -/
noncomputable def endIdealMask (hI : I.IsHomogeneous 𝒜) (i : ZMod 2) :
    Module.End A ↥I →ₗ[K] Module.End A ↥I where
  toFun f := endIdealMaskLM hI i f
  map_add' f g := LinearMap.ext fun x => by
    rw [LinearMap.add_apply]
    exact endIdealMaskFun_add_fun hI i f g x
  map_smul' c f := LinearMap.ext fun x => by
    rw [LinearMap.smul_apply]
    exact endIdealMaskFun_smul_fun hI i c f x

theorem endIdealMask_apply (hI : I.IsHomogeneous 𝒜) (i : ZMod 2) (f : Module.End A ↥I)
    (x : ↥I) :
    endIdealMask 𝒜 hI i f x
      = idealProjAmbient 𝒜 hI (0 + i) (f (idealProjAmbient 𝒜 hI 0 x))
        + idealProjAmbient 𝒜 hI (1 + i) (f (idealProjAmbient 𝒜 hI 1 x)) := rfl

theorem endIdealMask_mem (hI : I.IsHomogeneous 𝒜) (i : ZMod 2) (f : Module.End A ↥I) :
    endIdealMask 𝒜 hI i f ∈ endIdealGrading 𝒜 hI i := by
  intro j x hx
  rw [endIdealMask_apply]
  rcases zmod2_cases j with hj | hj <;> subst hj
  · rw [idealProjAmbient_of_mem 𝒜 hI hx, idealProjAmbient_of_mem_ne 𝒜 hI hx (by decide),
      map_zero, map_zero, add_zero]
    exact idealProjAmbient_mem 𝒜 hI (0 + i) _
  · rw [idealProjAmbient_of_mem 𝒜 hI hx, idealProjAmbient_of_mem_ne 𝒜 hI hx (by decide),
      map_zero, map_zero, zero_add]
    exact idealProjAmbient_mem 𝒜 hI (1 + i) _

theorem endIdealMask_of_mem {hI : I.IsHomogeneous 𝒜} {i : ZMod 2} {f : Module.End A ↥I}
    (hf : f ∈ endIdealGrading 𝒜 hI i) : endIdealMask 𝒜 hI i f = f := by
  refine LinearMap.ext fun x => ?_
  rw [endIdealMask_apply]
  conv_rhs => rw [← idealProjAmbient_zero_add_idealProjAmbient_one 𝒜 hI x, map_add]
  rw [idealProjAmbient_of_mem 𝒜 hI (hf 0 _ (idealProjAmbient_mem 𝒜 hI 0 x)),
    idealProjAmbient_of_mem 𝒜 hI (hf 1 _ (idealProjAmbient_mem 𝒜 hI 1 x))]

theorem endIdealMask_of_mem_ne {hI : I.IsHomogeneous 𝒜} {i i' : ZMod 2} {f : Module.End A ↥I}
    (hf : f ∈ endIdealGrading 𝒜 hI i) (hii' : i ≠ i') :
    endIdealMask 𝒜 hI i' f = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [endIdealMask_apply,
    idealProjAmbient_of_mem_ne 𝒜 hI (hf 0 _ (idealProjAmbient_mem 𝒜 hI 0 x))
      (fun h => hii' (by rwa [zero_add, zero_add] at h)),
    idealProjAmbient_of_mem_ne 𝒜 hI (hf 1 _ (idealProjAmbient_mem 𝒜 hI 1 x))
      (zmod2_schur_one i i' hii'),
    add_zero, LinearMap.zero_apply]

theorem endIdealMask_zero_add_endIdealMask_one (hI : I.IsHomogeneous 𝒜) (f : Module.End A ↥I) :
    endIdealMask 𝒜 hI 0 f + endIdealMask 𝒜 hI 1 f = f := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.add_apply, endIdealMask_apply, endIdealMask_apply]
  rw [show (0 : ZMod 2) + 0 = 0 from by decide,
    show (1 : ZMod 2) + 0 = 1 from by decide,
    show (0 : ZMod 2) + 1 = 1 from by decide,
    show (1 : ZMod 2) + 1 = 0 from by decide]
  rw [add_add_add_comm, idealProjAmbient_zero_add_idealProjAmbient_one,
    add_comm (idealProjAmbient 𝒜 hI 1 (f (idealProjAmbient 𝒜 hI 1 x)))
      (idealProjAmbient 𝒜 hI 0 (f (idealProjAmbient 𝒜 hI 1 x))),
    idealProjAmbient_zero_add_idealProjAmbient_one, ← map_add,
    idealProjAmbient_zero_add_idealProjAmbient_one]

/-- The degree-`i` mask, corestricted to the layer. -/
noncomputable def endIdealMaskInto (hI : I.IsHomogeneous 𝒜) (i : ZMod 2) :
    Module.End A ↥I →ₗ[K] endIdealGrading 𝒜 hI i :=
  LinearMap.codRestrict (endIdealGrading 𝒜 hI i) (endIdealMask 𝒜 hI i)
    (endIdealMask_mem 𝒜 hI i)

/-! ### Deliverable 3: decomposition and graded algebra structure -/

/-- **`E = Module.End A ↥I` is `ZMod 2`-decomposed** by `endIdealGrading`
— the M10-2 analogue of `GradedEnd.lean`'s anonymous `Decomposition`
instance.  Not an `instance` (the homogeneity `hI` is a hypothesis, not
found by typeclass search); activate with `letI` at use sites. -/
noncomputable abbrev endIdealDecomposition (hI : I.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (endIdealGrading 𝒜 hI) where
  decompose' f :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(endIdealGrading 𝒜 hI i)) 0
        (endIdealMaskInto 𝒜 hI 0 f)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(endIdealGrading 𝒜 hI i)) 1
        (endIdealMaskInto 𝒜 hI 1 f)
  left_inv f := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact endIdealMask_zero_add_endIdealMask_one 𝒜 hI f
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
          have h1 : endIdealMaskInto 𝒜 hI 0 (b : Module.End A ↥I) = b :=
            Subtype.ext (endIdealMask_of_mem 𝒜 b.2)
          have h2 : endIdealMaskInto 𝒜 hI 1 (b : Module.End A ↥I) = 0 :=
            Subtype.ext (endIdealMask_of_mem_ne 𝒜 b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : endIdealMaskInto 𝒜 hI 0 (b : Module.End A ↥I) = 0 :=
            Subtype.ext (endIdealMask_of_mem_ne 𝒜 b.2 (by decide))
          have h2 : endIdealMaskInto 𝒜 hI 1 (b : Module.End A ↥I) = b :=
            Subtype.ext (endIdealMask_of_mem 𝒜 b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

private theorem zmod2_schur_mul : ∀ k j i : ZMod 2, (k + j) + i = k + (i + j) := by decide

/-- **The `GradedMonoid` structure**: composition adds degrees, the
identity is degree `0`.  Independent of `hI` (the degree-shift statement
for `1` and `f * g` never needs `I`'s homogeneity, only the layer
membership `idealGrading`). -/
instance (hI : I.IsHomogeneous 𝒜) : SetLike.GradedMonoid (endIdealGrading 𝒜 hI) where
  one_mem := fun j x hx => by
    rw [show ((1 : Module.End A ↥I) x) = x from rfl]
    rwa [show j + (0 : ZMod 2) = j from by rw [add_zero]]
  mul_mem {i j} f g hf hg := fun k x hx => by
    rw [show ((f * g) x) = f (g x) from rfl]
    have h := hf (k + j) (g x) (hg k x hx)
    rwa [zmod2_schur_mul] at h

/-- **The endomorphism algebra of a homogeneous minimal left ideal is a
graded algebra** (M10-2, Deliverable 3). -/
noncomputable abbrev endIdealGradedAlgebra (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (endIdealGrading 𝒜 hI) where
  toGradedMonoid := inferInstance
  toDecomposition := endIdealDecomposition 𝒜 hI

/-! ### Deliverable 4: graded Schur -/

/-- The pushed-forward kernel of a graded endomorphism is a homogeneous
left ideal `≤ I`. -/
theorem isHomogeneous_ker_map (hI : I.IsHomogeneous 𝒜) {i : ZMod 2} {f : Module.End A ↥I}
    (hf : f ∈ endIdealGrading 𝒜 hI i) :
    ((LinearMap.ker f).map I.subtype).IsHomogeneous 𝒜 := by
  intro j x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hfy : f y = 0 := hy
  have hsplit : f (idealProjAmbient 𝒜 hI 0 y) + f (idealProjAmbient 𝒜 hI 1 y) = 0 := by
    rw [← map_add, idealProjAmbient_zero_add_idealProjAmbient_one, hfy]
  have hmem0 : f (idealProjAmbient 𝒜 hI 0 y) ∈ idealGrading 𝒜 I i := by
    have h := hf 0 _ (idealProjAmbient_mem 𝒜 hI 0 y)
    rwa [zero_add] at h
  have hmem1 : f (idealProjAmbient 𝒜 hI 1 y) ∈ idealGrading 𝒜 I (1 + i) :=
    hf 1 _ (idealProjAmbient_mem 𝒜 hI 1 y)
  have hy0 : f (idealProjAmbient 𝒜 hI 0 y) = 0 := by
    have h := idealProjAmbient_add_of_mem_ne hI hmem0 hmem1 (zmod2_schur_ne_add_one' i)
    rw [hsplit, map_zero] at h
    exact h.symm
  have hy1 : f (idealProjAmbient 𝒜 hI 1 y) = 0 := by
    have h := hsplit
    rwa [hy0, zero_add] at h
  show (DirectSum.decompose 𝒜 (y : A) j : A) ∈ (LinearMap.ker f).map I.subtype
  rw [show (DirectSum.decompose 𝒜 (y : A) j : A) = Bimod.modProj 𝒜 j (y : A) from rfl,
    ← idealProjAmbient_coe 𝒜 hI j y]
  rcases zmod2_cases j with hj | hj <;> subst hj
  · exact ⟨idealProjAmbient 𝒜 hI 0 y, hy0, rfl⟩
  · exact ⟨idealProjAmbient 𝒜 hI 1 y, hy1, rfl⟩

/-- The pushed-forward range of a graded endomorphism is a homogeneous
left ideal `≤ I`. -/
theorem isHomogeneous_range_map (hI : I.IsHomogeneous 𝒜) {i : ZMod 2} {f : Module.End A ↥I}
    (hf : f ∈ endIdealGrading 𝒜 hI i) :
    ((LinearMap.range f).map I.subtype).IsHomogeneous 𝒜 := by
  intro j x hx
  obtain ⟨z, ⟨y, rfl⟩, rfl⟩ := hx
  have hmem0 : f (idealProjAmbient 𝒜 hI 0 y) ∈ idealGrading 𝒜 I i := by
    have h := hf 0 _ (idealProjAmbient_mem 𝒜 hI 0 y)
    rwa [zero_add] at h
  have hmem1 : f (idealProjAmbient 𝒜 hI 1 y) ∈ idealGrading 𝒜 I (1 + i) :=
    hf 1 _ (idealProjAmbient_mem 𝒜 hI 1 y)
  have hsplit : f (idealProjAmbient 𝒜 hI 0 y) + f (idealProjAmbient 𝒜 hI 1 y) = f y := by
    rw [← map_add, idealProjAmbient_zero_add_idealProjAmbient_one]
  show (DirectSum.decompose 𝒜 (f y : A) j : A) ∈ (LinearMap.range f).map I.subtype
  rw [show (DirectSum.decompose 𝒜 (f y : A) j : A) = Bimod.modProj 𝒜 j (f y : A) from rfl,
    ← idealProjAmbient_coe 𝒜 hI j (f y), ← hsplit]
  rcases zmod2_schur_eq_or_eq_add_one i j with hj | hj
  · rw [hj, idealProjAmbient_add_of_mem_ne hI hmem0 hmem1 (zmod2_schur_ne_add_one' i)]
    exact ⟨f (idealProjAmbient 𝒜 hI 0 y), ⟨idealProjAmbient 𝒜 hI 0 y, rfl⟩, rfl⟩
  · rw [hj, idealProjAmbient_add_of_mem_ne' hI hmem0 hmem1 (zmod2_schur_ne_add_one' i)]
    exact ⟨f (idealProjAmbient 𝒜 hI 1 y), ⟨idealProjAmbient 𝒜 hI 1 y, rfl⟩, rfl⟩

/-- **Graded Schur**: every nonzero homogeneous endomorphism of the
graded-simple ideal `I` is a unit. -/
theorem endIdeal_isUnit_of_mem_ne_zero (hI : I.IsHomogeneous 𝒜)
    (hsimple : IsGradedSimpleIdeal 𝒜 I) {i : ZMod 2} {f : Module.End A ↥I}
    (hf : f ∈ endIdealGrading 𝒜 hI i) (hf0 : f ≠ 0) : IsUnit f := by
  rw [Module.End.isUnit_iff]
  constructor
  · rw [← LinearMap.ker_eq_bot]
    have hhom := isHomogeneous_ker_map 𝒜 hI hf
    have hle : (LinearMap.ker f).map I.subtype ≤ I := Submodule.map_subtype_le I _
    rcases hsimple _ hhom hle with h | h
    · have h' : (LinearMap.ker f).map I.subtype = (⊥ : Submodule A ↥I).map I.subtype := by
        rw [h, Submodule.map_bot]
      exact (Submodule.map_injective_of_injective (Submodule.injective_subtype I)) h'
    · exfalso
      apply hf0
      have h' : (LinearMap.ker f).map I.subtype = (⊤ : Submodule A ↥I).map I.subtype := by
        rw [h, Submodule.map_subtype_top]
      have htop : LinearMap.ker f = ⊤ :=
        (Submodule.map_injective_of_injective (Submodule.injective_subtype I)) h'
      rwa [LinearMap.ker_eq_top] at htop
  · rw [← LinearMap.range_eq_top]
    have hhom := isHomogeneous_range_map 𝒜 hI hf
    have hle : (LinearMap.range f).map I.subtype ≤ I := Submodule.map_subtype_le I _
    rcases hsimple _ hhom hle with h | h
    · exfalso
      apply hf0
      have h' : (LinearMap.range f).map I.subtype = (⊥ : Submodule A ↥I).map I.subtype := by
        rw [h, Submodule.map_bot]
      have hbot : LinearMap.range f = ⊥ :=
        (Submodule.map_injective_of_injective (Submodule.injective_subtype I)) h'
      rwa [LinearMap.range_eq_bot] at hbot
    · have h' : (LinearMap.range f).map I.subtype = (⊤ : Submodule A ↥I).map I.subtype := by
        rw [h, Submodule.map_subtype_top]
      exact (Submodule.map_injective_of_injective (Submodule.injective_subtype I)) h'

/-- **`E = Module.End A ↥I` is a super division algebra**
(docs/wedderburn-design.md, Step 2). -/
theorem endIdeal_isSuperDivision (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I) :
    Bimod.IsSuperDivision (endIdealGrading 𝒜 hI) :=
  fun _ _ hf hf0 => endIdeal_isUnit_of_mem_ne_zero 𝒜 hI hsimple hf hf0

end GradedSchur

/-! ### Deliverable 5: ungraded semisimplicity of `I` (the ε-trick) -/

section Semisimple

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

open Module

/-- **A minimal nonzero `A`-submodule of a finite-dimensional nonzero
module exists** — the ungraded (no homogeneity constraint) counterpart
of M10-1's `exists_minimal_homogeneous_leftIdeal`, proved by the same
`finrank` well-ordering argument. -/
theorem exists_minimal_submodule {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [FiniteDimensional K M] [Nontrivial M] :
    ∃ S : Submodule A M, S ≠ ⊥ ∧ ∀ T : Submodule A M, T ≤ S → T = ⊥ ∨ T = S := by
  classical
  have hex : ∃ n : ℕ, ∃ S : Submodule A M, S ≠ ⊥ ∧
      finrank K (S.restrictScalars K) = n :=
    ⟨_, ⊤, bot_ne_top.symm, rfl⟩
  obtain ⟨S, hSbot, hSrank⟩ := Nat.find_spec hex
  refine ⟨S, hSbot, ?_⟩
  intro T hTle
  by_contra hcon
  push Not at hcon
  obtain ⟨hTbot, hTneS⟩ := hcon
  have hTltS : T < S := lt_of_le_of_ne hTle hTneS
  have hTltS' : T.restrictScalars K < S.restrictScalars K := by
    rwa [Submodule.restrictScalars_lt]
  have hrk : finrank K (T.restrictScalars K) < finrank K (S.restrictScalars K) :=
    Submodule.finrank_lt_finrank_of_lt hTltS'
  have hTmem : ∃ S' : Submodule A M, S' ≠ ⊥ ∧
      finrank K (S'.restrictScalars K) = finrank K (T.restrictScalars K) :=
    ⟨T, hTbot, rfl⟩
  exact Nat.find_min hex (hSrank ▸ hrk) hTmem

variable {𝒜} in
/-- `ε` maps a homogeneous left ideal into itself. -/
theorem parityAut_mem_of_mem (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) :
    parityAut 𝒜 a ∈ I := by
  rw [parityAut_apply, evenPart_apply, oddPart_apply]
  exact I.sub_mem (hI 0 ha) (hI 1 ha)

variable {𝒜} in
/-- **The restriction of `ε` to `↥I`**, a `K`-linear involution (well
defined because `I` is homogeneous). -/
noncomputable def parityAutIdeal (hI : I.IsHomogeneous 𝒜) : ↥I →ₗ[K] ↥I :=
  (parityAut 𝒜).toLinearMap.restrict (p := I.restrictScalars K) (q := I.restrictScalars K)
    (fun _x hx => parityAut_mem_of_mem hI hx)

variable {𝒜} in
theorem parityAutIdeal_coe (hI : I.IsHomogeneous 𝒜) (x : ↥I) :
    (parityAutIdeal hI x : A) = parityAut 𝒜 (x : A) := rfl

variable {𝒜} in
theorem parityAutIdeal_parityAutIdeal (hI : I.IsHomogeneous 𝒜) (x : ↥I) :
    parityAutIdeal hI (parityAutIdeal hI x) = x := by
  apply Subtype.ext
  rw [parityAutIdeal_coe, parityAutIdeal_coe, parityAut_parityAut]

variable {𝒜} in
/-- **`ε`-semilinearity of `parityAutIdeal`** for the `A`-action:
`ε(a • x) = ε(a) • ε(x)`.  The key computation letting `ε` push an
`A`-submodule of `↥I` to another `A`-submodule (not merely a
`K`-subspace). -/
theorem parityAutIdeal_smul (hI : I.IsHomogeneous 𝒜) (a : A) (x : ↥I) :
    parityAutIdeal hI (a • x) = parityAut 𝒜 a • parityAutIdeal hI x := by
  apply Subtype.ext
  rw [parityAutIdeal_coe, Submodule.coe_smul, smul_eq_mul, Submodule.coe_smul, smul_eq_mul,
    parityAutIdeal_coe, map_mul]

variable {𝒜} in
/-- **The `ε`-twist of an `A`-submodule of `↥I`**: the image of `S`
under `parityAutIdeal`, made into a genuine `A`-submodule via
`parityAutIdeal_smul` (docs/wedderburn-design.md, Step 3). -/
noncomputable def εIdealSubmodule (hI : I.IsHomogeneous 𝒜) (S : Submodule A ↥I) :
    Submodule A ↥I where
  carrier := parityAutIdeal hI '' S
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s + t, S.add_mem hs ht, map_add _ _ _⟩
  zero_mem' := ⟨0, S.zero_mem, map_zero _⟩
  smul_mem' a := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨parityAut 𝒜 a • s, S.smul_mem _ hs, ?_⟩
    rw [parityAutIdeal_smul, parityAut_parityAut]

variable {𝒜} in
theorem mem_εIdealSubmodule_iff (hI : I.IsHomogeneous 𝒜) {S : Submodule A ↥I} {x : ↥I} :
    x ∈ εIdealSubmodule hI S ↔ ∃ s ∈ S, parityAutIdeal hI s = x :=
  Iff.rfl

variable {𝒜} in
theorem εIdealSubmodule_εIdealSubmodule (hI : I.IsHomogeneous 𝒜) (S : Submodule A ↥I) :
    εIdealSubmodule hI (εIdealSubmodule hI S) = S := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rwa [parityAutIdeal_parityAutIdeal]
  · intro s hs
    exact ⟨parityAutIdeal hI s, ⟨s, hs, rfl⟩, parityAutIdeal_parityAutIdeal hI s⟩

variable {𝒜} in
theorem εIdealSubmodule_bot (hI : I.IsHomogeneous 𝒜) :
    εIdealSubmodule hI (⊥ : Submodule A ↥I) = ⊥ := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_bot] at hs
    simp [hs]
  · exact bot_le

variable {𝒜} in
theorem εIdealSubmodule_mono (hI : I.IsHomogeneous 𝒜) {S T : Submodule A ↥I} (hST : S ≤ T) :
    εIdealSubmodule hI S ≤ εIdealSubmodule hI T := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, hST hs, rfl⟩

variable {𝒜} in
theorem εIdealSubmodule_sup (hI : I.IsHomogeneous 𝒜) (S T : Submodule A ↥I) :
    εIdealSubmodule hI (S ⊔ T) = εIdealSubmodule hI S ⊔ εIdealSubmodule hI T := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.mem_sup.mpr ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
  · apply sup_le
    · exact εIdealSubmodule_mono hI le_sup_left
    · exact εIdealSubmodule_mono hI le_sup_right

variable {𝒜} in
/-- **The `ε`-twist of a simple submodule is simple**: `εIdealSubmodule`
is a monotone involution on `Submodule A ↥I`, hence carries atoms to
atoms. -/
theorem isAtom_εIdealSubmodule (hI : I.IsHomogeneous 𝒜) {S : Submodule A ↥I}
    (hS : IsAtom S) : IsAtom (εIdealSubmodule hI S) := by
  constructor
  · intro h
    apply hS.1
    have := congrArg (εIdealSubmodule hI) h
    rwa [εIdealSubmodule_εIdealSubmodule, εIdealSubmodule_bot] at this
  · intro T hT
    have hTle : εIdealSubmodule hI T ≤ S := by
      have := εIdealSubmodule_mono hI hT.le
      rwa [εIdealSubmodule_εIdealSubmodule] at this
    have hTne : εIdealSubmodule hI T ≠ S := by
      intro h
      apply hT.ne
      have := congrArg (εIdealSubmodule hI) h
      rwa [εIdealSubmodule_εIdealSubmodule] at this
    have hbot := hS.2 _ (lt_of_le_of_ne hTle hTne)
    have := congrArg (εIdealSubmodule hI) hbot
    rwa [εIdealSubmodule_εIdealSubmodule, εIdealSubmodule_bot] at this

/-- **Ungraded semisimplicity of a minimal graded ideal**
(docs/wedderburn-design.md, Step 3's opening bullet, the "ε-trick"): a
minimal ungraded submodule `S ≤ ↥I` together with its `ε`-twist span
`↥I`, and both are simple, so `IsSemisimpleModule.sup` finishes. -/
theorem isSemisimpleModule_of_minimal (hI : I.IsHomogeneous 𝒜)
    (hsimple : IsGradedSimpleIdeal 𝒜 I) [Invertible (2 : K)] [FiniteDimensional K A]
    (hne : I ≠ ⊥) : IsSemisimpleModule A ↥I := by
  haveI : Nontrivial ↥I := nontrivial_of_ne_bot hne
  haveI : FiniteDimensional K ↥I := FiniteDimensional.finiteDimensional_submodule
    (I.restrictScalars K)
  obtain ⟨S, hSbot, hSmin⟩ := exists_minimal_submodule (A := A) (K := K) (M := ↥I)
  have hSatom : IsAtom S := ⟨hSbot, fun T hT => (hSmin T hT.le).resolve_right (ne_of_lt hT)⟩
  have hEatom : IsAtom (εIdealSubmodule hI S) := isAtom_εIdealSubmodule hI hSatom
  haveI hSsimple : IsSimpleModule A ↥S := isSimpleModule_iff_isAtom.mpr hSatom
  haveI hEsimple : IsSimpleModule A ↥(εIdealSubmodule hI S) :=
    isSimpleModule_iff_isAtom.mpr hEatom
  haveI hSup : IsSemisimpleModule A ↥(S ⊔ εIdealSubmodule hI S) :=
    IsSemisimpleModule.sup inferInstance inferInstance
  have hTtop : S ⊔ εIdealSubmodule hI S = ⊤ := by
    have hTε : εIdealSubmodule hI (S ⊔ εIdealSubmodule hI S) = S ⊔ εIdealSubmodule hI S := by
      rw [εIdealSubmodule_sup, εIdealSubmodule_εIdealSubmodule, sup_comm]
    have hTstable : ∀ w ∈ (S ⊔ εIdealSubmodule hI S).map I.subtype,
        parityAut 𝒜 w ∈ (S ⊔ εIdealSubmodule hI S).map I.subtype := by
      rintro w ⟨x, hx, rfl⟩
      refine ⟨parityAutIdeal hI x, ?_, parityAutIdeal_coe hI x⟩
      rw [← hTε]
      exact ⟨x, hx, rfl⟩
    have hhom := isHomogeneous_of_parityAut_stable 𝒜 hTstable
    have hle : (S ⊔ εIdealSubmodule hI S).map I.subtype ≤ I := Submodule.map_subtype_le I _
    have hSne : S ⊔ εIdealSubmodule hI S ≠ ⊥ := by
      intro h
      exact hSbot (le_bot_iff.mp (h ▸ le_sup_left))
    have hne' : (S ⊔ εIdealSubmodule hI S).map I.subtype ≠ ⊥ := by
      intro h
      apply hSne
      have h' : (S ⊔ εIdealSubmodule hI S).map I.subtype
          = (⊥ : Submodule A ↥I).map I.subtype := by rw [h, Submodule.map_bot]
      exact (Submodule.map_injective_of_injective (Submodule.injective_subtype I)) h'
    rcases hsimple _ hhom hle with h | h
    · exact absurd h hne'
    · have h' : (S ⊔ εIdealSubmodule hI S).map I.subtype
          = (⊤ : Submodule A ↥I).map I.subtype := by rw [h, Submodule.map_subtype_top]
      exact (Submodule.map_injective_of_injective (Submodule.injective_subtype I)) h'
  rw [hTtop] at hSup
  exact IsSemisimpleModule.congr Submodule.topEquiv.symm

end Semisimple

end Superfusion

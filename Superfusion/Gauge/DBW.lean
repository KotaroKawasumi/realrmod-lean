/-
Superfusion / Gauge / DBW

Milestone M9-5 of the intrinsic gauge track: **`DBW(K)` and the gauge class
map** — connecting the abstract `DivisionFusionGauge` skeleton to the landed
Brauer–Wall group `BW K` (`Superfusion.Super.BWGroup`).

**Contents.**

* A gap-filling preliminary: the super-opposite construction preserves
  supercentrality and graded simplicity (`IsSuperCentral.sop`,
  `IsGradedSimple.sop`).  These are general `ZMod 2`-graded-ring facts, not
  specific to division algebras; the M7f Brauer–Wall layer never needed them
  (`BW.ofAzumaya`'s inverse law only needs `IsSuperAzumaya P.grading`, not
  `IsSuperAzumaya P.sop.grading`), so they were not previously proved.  They
  are needed here because `DBW(K)`'s membership predicate asks for an
  *explicit* central-simple representative, and the natural representative of
  a class's inverse is the super-opposite of a representative of the class.
* `DivisionFusionGauge.bwClass : G → BW K`, the Brauer–Wall class of each
  skeleton floor `D_a`, built as a unit of the class monoid via
  `BW.ofAzumaya` (Wall's criterion, `isSuperAzumaya_of_central_simple`,
  supplies the Azumaya hypothesis from `Γ`'s own `central`/`gradedSimple`
  fields).
* Homomorphy of the class map (`bwClass_add`, from the fusion isomorphism
  `Γ.fuse` witnessing Brauer–Wall equivalence after matrix stabilization) and
  its corollary `bwClass_zero` (a *consequence* of homomorphy plus group
  cancellation — `D_0` is not assumed to represent the trivial class), bundled
  as `bwClassHom : G →+ Additive (BW K)`.
* `DBW K : Set (BW K)`, the division-representable classes, with
  `DBW.one_mem` and `DBW.inv_mem` (via `IsSuperDivision.sop` and the
  `[P]⁻¹ = [P^sop]` theorem), and the *open* product-closure statement
  `DBW.MulClosed` (the mini-Wedderburn target, deliberately left unproved).
* `DivisionFusionGauge.IsCanonical`, a light definitional placeholder
  recording what a gauge with `G = DBW K` realizing exactly the division
  classes, faithfully, should look like.

Design record: docs/super-track-design.md (M9 sections).
-/
import Superfusion.Gauge.FusionGauge
import Superfusion.Super.BWGroup
import Superfusion.Super.WallProof

namespace Superfusion

/-! ### The super-opposite preserves supercentrality and graded simplicity

A general `ZMod 2`-graded-ring fact (not special to super division algebras):
the super-opposite construction of `Superfusion.Super.SuperOpposite`
preserves `IsSuperCentral` and `IsGradedSimple`.  Route: the same underlying
`K`-module and homogeneous pieces (`SuperOp.grading 𝒜 = 𝒜` definitionally),
with the signed swap `op a ∙ op b = ±op(b*a)` (`SuperOp.op_mul_op_of_mem`) on
homogeneous elements for supercentrality, and the general (non-homogeneous)
multiplication formula `mulMap p q = q*p - 2•(oddPart q * oddPart p)`
(`SuperOp.mulMap_apply`) together with ideal-absorption of the odd component
for graded simplicity. -/

section SopTransfer

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {𝒜 : ZMod 2 → Submodule K A} [GradedAlgebra 𝒜]

/-- The signed-central-swap identity, transported across `op`: for
`a ∈ 𝒜 i`, `b ∈ 𝒜 j`, the `SuperOp`-central-swap equation at `(op a, op b)`
is equivalent to the `𝒜`-central-swap equation at `(a, b)`. -/
private theorem isSupercentral_sop_congr {i j : ZMod 2} {a b : A}
    (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    SuperOp.op 𝒜 a * SuperOp.op 𝒜 b =
        ((sgn (i * j) : ℤˣ) : ℤ) • (SuperOp.op 𝒜 b * SuperOp.op 𝒜 a) ↔
      a * b = ((sgn (i * j) : ℤˣ) : ℤ) • (b * a) := by
  rw [SuperOp.op_mul_op_of_mem 𝒜 ha hb, SuperOp.op_mul_op_of_mem 𝒜 hb ha, smul_smul,
    show ((sgn (i * j) : ℤˣ) : ℤ) * ((sgn (j * i) : ℤˣ) : ℤ) = 1 from by
      rw [mul_comm j i, ← Units.val_mul, sgn_mul_self', Units.val_one],
    one_smul]
  constructor
  · intro h
    have h2 := congrArg (SuperOp.unop 𝒜) h
    rwa [map_zsmul, SuperOp.unop_op, SuperOp.unop_op, eq_comm] at h2
  · intro h
    have h2 := congrArg (SuperOp.op 𝒜) h
    rwa [map_zsmul, eq_comm] at h2

private theorem isSupercentral_sop_iff {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) :
    IsSupercentral (SuperOp.grading 𝒜) i (SuperOp.op 𝒜 a) ↔ IsSupercentral 𝒜 i a := by
  constructor
  · intro H j b hb
    have hb' : SuperOp.op 𝒜 b ∈ SuperOp.grading 𝒜 j := (SuperOp.mem_grading_iff 𝒜 j _).mpr hb
    exact (isSupercentral_sop_congr ha hb).mp (H j (SuperOp.op 𝒜 b) hb')
  · intro H j y hy
    obtain ⟨b, hb, rfl⟩ : ∃ b, b ∈ 𝒜 j ∧ SuperOp.op 𝒜 b = y :=
      ⟨SuperOp.unop 𝒜 y, (SuperOp.mem_grading_iff 𝒜 j y).mp hy, SuperOp.op_unop 𝒜 y⟩
    exact (isSupercentral_sop_congr ha hb).mpr (H j b hb)

/-- **The super-opposite preserves supercentrality.** -/
theorem IsSuperCentral.sop (h : IsSuperCentral 𝒜) : IsSuperCentral (SuperOp.grading 𝒜) where
  superCenter_le_one := by
    have key : ∀ i : ZMod 2, superCenterGrade (SuperOp.grading 𝒜) i ≤ 1 := by
      rintro i y ⟨hy, hyc⟩
      have hy' : SuperOp.unop 𝒜 y ∈ 𝒜 i := (SuperOp.mem_grading_iff 𝒜 i y).mp hy
      have hop : SuperOp.op 𝒜 (SuperOp.unop 𝒜 y) = y := SuperOp.op_unop 𝒜 y
      have hyc' : IsSupercentral (SuperOp.grading 𝒜) i (SuperOp.op 𝒜 (SuperOp.unop 𝒜 y)) :=
        hop ▸ hyc
      have hc : IsSupercentral 𝒜 i (SuperOp.unop 𝒜 y) := (isSupercentral_sop_iff hy').mp hyc'
      have h1 : SuperOp.unop 𝒜 y ∈ (1 : Submodule K A) :=
        mem_one_of_isSupercentral (𝒜 := 𝒜) hy' hc
      rw [← hop]
      obtain ⟨c, hc1⟩ := Submodule.mem_one.mp h1
      exact Submodule.mem_one.mpr ⟨c, by rw [← hc1]; rfl⟩
    calc superCenter (SuperOp.grading 𝒜)
        = superCenterGrade (SuperOp.grading 𝒜) 0 ⊔ superCenterGrade (SuperOp.grading 𝒜) 1 := rfl
      _ ≤ 1 := sup_le (key 0) (key 1)

/-- The odd component commutes with `op`, across the definitional identification
`SuperOp.grading 𝒜 = 𝒜` and `SuperOp.op 𝒜 = LinearEquiv.refl K A` (reinterpreted at the
type synonym). -/
private theorem oddPart_op_eq (a : A) :
    oddPart (SuperOp.grading 𝒜) (SuperOp.op 𝒜 a) = SuperOp.op 𝒜 (oddPart 𝒜 a) := rfl

/-- The general (non-homogeneous) product identity underlying `SuperOp`'s multiplication,
transported through `op`. -/
private theorem op_mul_op_eq (p q : A) :
    SuperOp.op 𝒜 p * SuperOp.op 𝒜 q =
      SuperOp.op 𝒜 (q * p) - (2 : ℤ) • SuperOp.op 𝒜 (oddPart 𝒜 q * oddPart 𝒜 p) := by
  rw [SuperOp.mul_def, SuperOp.unop_op, SuperOp.unop_op, SuperOp.mulMap_apply, map_sub, map_zsmul]

/-- The odd-odd product `op(oddPart p) ∙ op(oddPart q)` collapses to the (negated) `op` of the
plain product, by idempotence of `oddPart` on already-odd elements. -/
private theorem op_oddPart_mul_op_oddPart (p q : A) :
    SuperOp.op 𝒜 (oddPart 𝒜 p) * SuperOp.op 𝒜 (oddPart 𝒜 q) =
      -SuperOp.op 𝒜 (oddPart 𝒜 q * oddPart 𝒜 p) := by
  have h := op_mul_op_eq (𝒜 := 𝒜) (oddPart 𝒜 p) (oddPart 𝒜 q)
  rw [oddPart_of_mem_one 𝒜 (oddPart_mem 𝒜 q), oddPart_of_mem_one 𝒜 (oddPart_mem 𝒜 p)] at h
  rw [h, two_smul]
  abel

variable {I' : TwoSidedIdeal (SuperOp 𝒜)}

private theorem oddPart_cross_mem_right (a a' : A) (h : SuperOp.op 𝒜 (oddPart 𝒜 a') ∈ I') :
    SuperOp.op 𝒜 (oddPart 𝒜 a * oddPart 𝒜 a') ∈ I' := by
  have hp : SuperOp.op 𝒜 (oddPart 𝒜 a') * SuperOp.op 𝒜 (oddPart 𝒜 a) ∈ I' := I'.mul_mem_right _ _ h
  rw [op_oddPart_mul_op_oddPart] at hp
  exact neg_mem_iff.mp hp

private theorem oddPart_cross_mem_left (a a' : A) (h : SuperOp.op 𝒜 (oddPart 𝒜 a) ∈ I') :
    SuperOp.op 𝒜 (oddPart 𝒜 a * oddPart 𝒜 a') ∈ I' := by
  have hp : SuperOp.op 𝒜 (oddPart 𝒜 a') * SuperOp.op 𝒜 (oddPart 𝒜 a) ∈ I' := I'.mul_mem_left _ _ h
  rw [op_oddPart_mul_op_oddPart] at hp
  exact neg_mem_iff.mp hp

/-- **The super-opposite preserves graded simplicity.** -/
theorem IsGradedSimple.sop (h : IsGradedSimple 𝒜) : IsGradedSimple (SuperOp.grading 𝒜) where
  eq_bot_or_eq_top I' hI' := by
    have hodd : ∀ b : A, SuperOp.op 𝒜 b ∈ I' → SuperOp.op 𝒜 (oddPart 𝒜 b) ∈ I' := by
      intro b hb
      have hmem := hI' (SuperOp.op 𝒜 b) hb 1
      rwa [← oddPart_apply, oddPart_op_eq] at hmem
    -- pull `I'` back to a homogeneous two-sided ideal `Ψ` of `A`
    let carrier : Set A := {a | SuperOp.op 𝒜 a ∈ I'}
    have hmul_left : ∀ {a a' : A}, a' ∈ carrier → a * a' ∈ carrier := by
      intro a a' ha'
      show SuperOp.op 𝒜 (a * a') ∈ I'
      have e := op_mul_op_eq (𝒜 := 𝒜) a' a
      have h1 : SuperOp.op 𝒜 a' * SuperOp.op 𝒜 a ∈ I' := I'.mul_mem_right _ _ ha'
      have h2 : SuperOp.op 𝒜 (oddPart 𝒜 a * oddPart 𝒜 a') ∈ I' :=
        oddPart_cross_mem_right a a' (hodd a' ha')
      have hrw : SuperOp.op 𝒜 (a * a') = SuperOp.op 𝒜 a' * SuperOp.op 𝒜 a
          + (2 : ℤ) • SuperOp.op 𝒜 (oddPart 𝒜 a * oddPart 𝒜 a') := by
        rw [e]; abel
      rw [hrw]
      exact I'.add_mem h1 (I'.zsmul_mem 2 h2)
    have hmul_right : ∀ {a a' : A}, a ∈ carrier → a * a' ∈ carrier := by
      intro a a' ha
      show SuperOp.op 𝒜 (a * a') ∈ I'
      have e := op_mul_op_eq (𝒜 := 𝒜) a' a
      have h1 : SuperOp.op 𝒜 a' * SuperOp.op 𝒜 a ∈ I' := I'.mul_mem_left _ _ ha
      have h2 : SuperOp.op 𝒜 (oddPart 𝒜 a * oddPart 𝒜 a') ∈ I' :=
        oddPart_cross_mem_left a a' (hodd a ha)
      have hrw : SuperOp.op 𝒜 (a * a') = SuperOp.op 𝒜 a' * SuperOp.op 𝒜 a
          + (2 : ℤ) • SuperOp.op 𝒜 (oddPart 𝒜 a * oddPart 𝒜 a') := by
        rw [e]; abel
      rw [hrw]
      exact I'.add_mem h1 (I'.zsmul_mem 2 h2)
    let Ψ : TwoSidedIdeal A := TwoSidedIdeal.mk' carrier
      (by show SuperOp.op 𝒜 0 ∈ I'; rw [map_zero]; exact I'.zero_mem)
      (fun {a a'} ha ha' => by
        show SuperOp.op 𝒜 (a + a') ∈ I'; rw [map_add]; exact I'.add_mem ha ha')
      (fun {a} ha => by show SuperOp.op 𝒜 (-a) ∈ I'; rw [map_neg]; exact I'.neg_mem ha)
      (fun {a a'} ha' => hmul_left ha') (fun {a a'} ha => hmul_right ha)
    have hΨhom : TwoSidedIdeal.IsHomogeneous 𝒜 Ψ := by
      intro a ha i
      rw [TwoSidedIdeal.mem_mk'] at ha
      rw [TwoSidedIdeal.mem_mk']
      rcases zmod2_cases i with hi | hi <;> subst hi
      · show SuperOp.op 𝒜 (evenPart 𝒜 a) ∈ I'
        have hev : SuperOp.op 𝒜 (evenPart 𝒜 a) = SuperOp.op 𝒜 a - SuperOp.op 𝒜 (oddPart 𝒜 a) := by
          rw [← map_sub]; congr 1
          rw [eq_sub_iff_add_eq]; exact evenPart_add_oddPart 𝒜 a
        rw [hev]
        exact I'.sub_mem ha (hodd a ha)
      · show SuperOp.op 𝒜 (oddPart 𝒜 a) ∈ I'
        exact hodd a ha
    have hcorr : ∀ z : SuperOp 𝒜, SuperOp.unop 𝒜 z ∈ Ψ ↔ z ∈ I' := by
      intro z
      rw [TwoSidedIdeal.mem_mk']
      show SuperOp.op 𝒜 (SuperOp.unop 𝒜 z) ∈ I' ↔ z ∈ I'
      rw [SuperOp.op_unop]
    rcases h.eq_bot_or_eq_top Ψ hΨhom with hb | ht
    · left
      ext z
      rw [← hcorr z, hb, TwoSidedIdeal.mem_bot, TwoSidedIdeal.mem_bot, (SuperOp.unop 𝒜).map_eq_zero_iff]
    · right
      ext z
      simp [← hcorr z, ht, TwoSidedIdeal.mem_top]

end SopTransfer

/-! ### The Brauer–Wall class map -/

section ClassMap

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)] {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

/-- Each skeleton floor is finite-dimensional (registered as an instance so that class-monoid
statements about `Γ.D a`, in particular `BWMonoid.mk (Γ.D a)`, elaborate without manual `haveI`
bookkeeping at every use site). -/
instance DivisionFusionGauge.instFiniteDimensionalD (a : G) :
    FiniteDimensional K (Γ.D a).carrier := Γ.findim a

instance DivisionFusionGauge.instNontrivialD (a : G) : Nontrivial (Γ.D a).carrier := Γ.nontriv a

instance DivisionFusionGauge.instIsSuperCentralD (a : G) : IsSuperCentral (Γ.D a).grading :=
  Γ.central a

instance DivisionFusionGauge.instIsGradedSimpleD (a : G) : IsGradedSimple (Γ.D a).grading :=
  Γ.gradedSimple a

/-- **Wall's criterion** supplies the Azumaya hypothesis from `Γ`'s own `central`/`gradedSimple`
fields. -/
instance DivisionFusionGauge.instIsSuperAzumayaD (a : G) : IsSuperAzumaya (Γ.D a).grading :=
  isSuperAzumaya_of_central_simple (Γ.D a).grading

/-- **The Brauer–Wall class of a skeleton floor** `D_a`: a unit of the Brauer–Wall class monoid
`BW K`, via `BW.ofAzumaya`. -/
noncomputable def DivisionFusionGauge.bwClass (a : G) : BW K :=
  BW.ofAzumaya (Γ.D a)

@[simp] theorem DivisionFusionGauge.bwClass_val (a : G) :
    (Γ.bwClass a).val = BWMonoid.mk (Γ.D a) := rfl

/-- **Homomorphy of the class map**: the fusion isomorphism `Γ.fuse a b`, a graded isomorphism
onto a matrix stabilization of `D_{a+b}`, is *exactly* a witness of Brauer–Wall equivalence
between `D_a ᵍ⊗ D_b` and `D_{a+b}` (`IsBWEquivalent.of_matrixSuper`); this transports to equality
of classes in the monoid (`BWMonoid.mk_eq_mk_iff`), then lifts to the unit group by comparing
`.val` (`Units.ext`). -/
theorem DivisionFusionGauge.bwClass_add (a b : G) :
    Γ.bwClass (a + b) = Γ.bwClass a * Γ.bwClass b := by
  have goal_val : (Γ.bwClass (a + b)).val = (Γ.bwClass a * Γ.bwClass b).val := by
    show BWMonoid.mk (Γ.D (a + b)) = (Γ.bwClass a).val * (Γ.bwClass b).val
    rw [Γ.bwClass_val, Γ.bwClass_val, BWMonoid.mk_mul]
    exact (BWMonoid.mk_eq_mk_iff).mpr
      (IsBWEquivalent.of_matrixSuper (Γ.size_pos a b) (Γ.fuse a b)).symm
  exact Units.ext goal_val

/-- **The class map sends `0` to the trivial class** — a *corollary* of homomorphy plus group
cancellation, not an assumption: `Γ.bwClass 0 = Γ.bwClass 0 * Γ.bwClass 0` (from `bwClass_add 0 0`
and `0 + 0 = 0`) forces `Γ.bwClass 0 = 1` in the group `BW K`.  Note `D_0` is *not* assumed to be
the base algebra; this is a genuine consequence. -/
theorem DivisionFusionGauge.bwClass_zero : Γ.bwClass 0 = 1 := by
  have h := Γ.bwClass_add 0 0
  rw [add_zero] at h
  have h2 : Γ.bwClass 0 * 1 = Γ.bwClass 0 * Γ.bwClass 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

/-- **The bundled class map**, as an additive-to-multiplicative homomorphism: `G` is additive
(matching `DivisionFusionGauge`'s convention, mirroring `stdTower`/`stdFuse`'s native `ZMod 8`
indexing), while `BW K` is multiplicative, so the cleanest bundling routes through `Additive (BW
K)` on the codomain rather than wrapping the domain in `Multiplicative`. -/
noncomputable def DivisionFusionGauge.bwClassHom : G →+ Additive (BW K) where
  toFun a := Additive.ofMul (Γ.bwClass a)
  map_zero' := by
    show Additive.ofMul (Γ.bwClass 0) = 0
    rw [Γ.bwClass_zero]; rfl
  map_add' a b := by
    show Additive.ofMul (Γ.bwClass (a + b)) = Additive.ofMul (Γ.bwClass a) + Additive.ofMul (Γ.bwClass b)
    rw [Γ.bwClass_add]; rfl

end ClassMap

/-! ### `DBW(K)`: the division-representable classes -/

section DBWDef

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- **`DBW(K)`**: the Brauer–Wall classes representable by an *explicit* central-simple,
finite-dimensional, nontrivial super *division* algebra (§2.2's division algebras) — matching
`DivisionFusionGauge`'s own per-object hypotheses.  Membership packages a witness `D` together
with the equality of its class (`BWMonoid.mk D`, the class monoid element) with `x.val`. -/
def DBW : Set (BW K) :=
  {x | ∃ (D : SuperAlgebra.{u, u} K) (_ : IsSuperCentral D.grading) (_ : IsGradedSimple D.grading)
      (hf : FiniteDimensional K D.carrier) (hn : Nontrivial D.carrier),
      Bimod.IsSuperDivision D.grading ∧ haveI := hf; haveI := hn; BWMonoid.mk D = x.val}

variable {K}

omit [Invertible (2 : K)] in
/-- **`DBW.one_mem`**: the base algebra `K` (purely even) is a super division representative of
the trivial class. -/
theorem DBW.one_mem : (1 : BW K) ∈ DBW K :=
  ⟨SuperAlgebra.base K, base_isSuperCentral, base_isGradedSimple, inferInstance, inferInstance,
    Bimod.IsSuperDivision.base, rfl⟩

/-- **`DBW.inv_mem`**: the super-opposite of a division representative of `x` is a division
representative of `x⁻¹` — via `IsSuperDivision.sop`, `IsSuperCentral.sop`, `IsGradedSimple.sop`
(the sop-transfer lemmas above) for the per-object hypotheses, and the Brauer–Wall inverse law
`[P]⁻¹ = [P^sop]` (`BW.ofAzumaya_inv`) for the class equality. -/
theorem DBW.inv_mem {x : BW K} (hx : x ∈ DBW K) : x⁻¹ ∈ DBW K := by
  obtain ⟨D, hc, hs, hf, hn, hdiv, hval⟩ := hx
  haveI := hc
  haveI := hs
  haveI := hf
  haveI := hn
  haveI : IsSuperAzumaya D.grading := isSuperAzumaya_of_central_simple D.grading
  have hux : BW.ofAzumaya D = x := Units.ext (by rw [BW.ofAzumaya_val]; exact hval)
  refine ⟨D.sop, hc.sop, hs.sop, inferInstance, inferInstance, hdiv.sop, ?_⟩
  rw [← hux]
  exact (BW.ofAzumaya_inv D).symm

/-- **The open mini-Wedderburn target**: product-closure of `DBW(K)` — the class of a
graded-tensor-product of two central-simple *division* algebras is again division-representable.
This is the substantial content of the mini-Wedderburn theorem (a graded-tensor-product of two
super division algebras, while typically no longer itself a division algebra, decomposes as a
matrix algebra over one — the intrinsic-gauge-track analogue of "division ⊗ division = matrix
over division"), and is **deliberately left unproved** here: `DBW(K)` is a group exactly when this
holds, which is not established by this milestone. -/
def DBW.MulClosed (K : Type u) [Field K] [Invertible (2 : K)] : Prop :=
  ∀ x y, x ∈ DBW K → y ∈ DBW K → x * y ∈ DBW K

/-- **`IsCanonical`**: the intended shape of the eventual "`DBWGauge`" specialization, recorded
here as a light `Prop`-valued predicate rather than a new structure (building an honest
`DivisionFusionGauge K (DBW K)` needs a group structure on `DBW K` as an *index set*, which is
exactly `DBW.MulClosed` plus `DBW.one_mem`/`DBW.inv_mem` packaged into a `Subgroup`-like closure —
future work for a `DBWGauge` milestone once mini-Wedderburn lands): a gauge `Γ : DivisionFusionGauge
K G` is **canonical** when its class map is *injective* (distinct skeleton floors have distinct
Brauer–Wall classes) and its range is *exactly* `DBW K` (every division-representable class is hit,
and only those are). -/
def DivisionFusionGauge.IsCanonical {G : Type v} [AddGroup G] (Γ : DivisionFusionGauge K G) : Prop :=
  Function.Injective Γ.bwClass ∧ Set.range Γ.bwClass = DBW K

end DBWDef

end Superfusion

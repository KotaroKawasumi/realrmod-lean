/-
Superfusion / Wedderburn / BWGauge

Milestone M10-9 (`docs/wedderburn-design.md`, "Extension: M10-9 the tautological BW gauge"):
**the tautological division fusion gauge `Γ_BW` on `BW(K)`**. With `BW K = DBW K` landed
(`Superfusion.Wedderburn.BWEqualsDBW`, `exists_division_of_unit`) and Wedderburn uniqueness
landed (`Superfusion.Wedderburn.Uniqueness2`, `superAlgEquiv_of_bwMk_eq`), *every* Brauer–Wall
class of *every* field `K` (with `2` invertible) has a canonical super division representative,
chosen once and for all by `Classical.choice`, and the fusion isomorphisms of `graded_wedderburn`
applied to the graded tensor product of two representatives assemble into an honest term of the
abstract skeleton `DivisionFusionGauge K (Additive (BW K))`
(`Superfusion.Gauge.FusionGauge`, M9-2) — the skeletal data `(BW(K), D_a, φ_{a,b})` the paper's
superbicategory skeleton needs, for a *general* field.

**Contents.**

* `bwRep : Additive (BW K) → SuperAlgebra K`, the chosen division representative of a class
  (`exists_division_of_unit`, `Exists.choose`-extracted *once* per class so that all six witness
  fields cohere with a single underlying choice), and its six field lemmas
  (`bwRep_isSuperCentral`, `bwRep_isGradedSimple`, `bwRep_isSuperDivision`,
  `bwRep_finiteDimensional`, `bwRep_nontrivial`, `bwRep_mk`), plus matching global instances.
* The fusion data: a private bundle `bwGtensorWedderburn` (mirroring
  `Wedderburn/DBWGroup.lean`'s `exists_division_of_gtensor`, but keeping the produced
  `SuperAlgEquiv` instead of discarding it for a bare class equation) realizing
  `D_a ᵍ⊗ D_b ≅ M_{p|q}(D₃)` for a fresh super division algebra `D₃`; a class chase
  (`bwD3_mk_eq`) identifies `[D₃] = [D_a] * [D_b] = [D_{a+b}]`; Wedderburn uniqueness
  (`superAlgEquiv_of_bwMk_eq`) then supplies `D₃ ≅ D_{a+b}`, and composing with the
  `matrixSuper` congruence gives `bwFuse a b : D_a ᵍ⊗ D_b ≅ M_{σ(a,b)}(D_{a+b})`
  (`bwSize a b := (p, q)`). All the (D₃, p, q, equivalence) data for a fixed `(a, b)` comes from
  a *single* application of `bwGtensorWedderburn a b`, threaded through every downstream
  accessor, so the witnesses cohere.
* `bwGauge : DivisionFusionGauge K (Additive (BW K))`, the assembly.
* **Tautological canonicality**: `bwGauge_bwClass : bwGauge.bwClass a = Additive.toMul a` — the
  class map is (definitionally, up to `Additive`/`Multiplicative` bookkeeping) the identity —
  and its two corollaries, `bwGauge_isCanonical : bwGauge.IsCanonical` (`DivisionFusionGauge.
  IsCanonical`'s injectivity-plus-range-equals-`DBW`interface, both immediate: injectivity from
  `Additive.toMul` being an equivalence, range-equals-`DBW K` from `DBW_eq_univ`) and
  `bwGauge_bwClassHom : bwGauge.bwClassHom = AddMonoidHom.id _` (the class-map homomorphism is
  the identity homomorphism on `Additive (BW K)`).
* **The parity**: `bwParity := bwGauge.gaugeParity`, `Additive (BW K) → Additive (BW K) →
  Additive (BW K) → ZMod 2`. `DivisionFusionGauge.gaugeParity` (`Superfusion.Gauge.GaugePentagon`,
  M9-3b) needs no hypotheses on `Γ` beyond `Γ : DivisionFusionGauge K G` itself (its own
  Skolem–Noether existence proof derives everything it needs from `Γ`'s per-object fields at the
  composite index), so it instantiates directly at `bwGauge` with no structural mismatch — the
  headline mathematical content: **for every field `K` with `2` invertible, there is a
  pentagon-parity cochain `p : BW(K)³ → ℤ/2`.**

The (p, χ) *definition* itself (as the paper's cocycle data on the skeleton) lives in the
bimodule layer (parallel session); `bwGauge` is the computation device and existence witness of
the skeletal data this milestone was asked to produce.
-/
import Superfusion.Wedderburn.Uniqueness2
import Superfusion.Gauge.GaugePentagon

namespace Superfusion

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-! ### The representative choice `bwRep` -/

section Rep

/-- **The tautological representative choice** (M10-9, deliverable 1): the division
representative of a Brauer–Wall class `Additive.toMul a : BW K`, chosen once via
`exists_division_of_unit` (`Superfusion.Wedderburn.BWEqualsDBW`) — a single `Exists.choose`
extraction so that all six witness fields below refer to the *same* underlying choice. -/
noncomputable def bwRep (a : Additive (BW.{u} K)) : SuperAlgebra.{u, u} K :=
  (exists_division_of_unit (Additive.toMul a)).choose

theorem bwRep_isSuperCentral (a : Additive (BW.{u} K)) :
    IsSuperCentral (bwRep a).grading :=
  (exists_division_of_unit (Additive.toMul a)).choose_spec.choose

theorem bwRep_isGradedSimple (a : Additive (BW.{u} K)) :
    IsGradedSimple (bwRep a).grading :=
  (exists_division_of_unit (Additive.toMul a)).choose_spec.choose_spec.choose

theorem bwRep_finiteDimensional (a : Additive (BW.{u} K)) :
    FiniteDimensional K (bwRep a).carrier :=
  (exists_division_of_unit (Additive.toMul a)).choose_spec.choose_spec.choose_spec.choose

theorem bwRep_nontrivial (a : Additive (BW.{u} K)) :
    Nontrivial (bwRep a).carrier :=
  (exists_division_of_unit (Additive.toMul a)).choose_spec.choose_spec.choose_spec.choose_spec.choose

theorem bwRep_isSuperDivision (a : Additive (BW.{u} K)) :
    Bimod.IsSuperDivision (bwRep a).grading :=
  (exists_division_of_unit (Additive.toMul a)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- **The class equation of the representative choice**: `[bwRep a] = Additive.toMul a`. -/
theorem bwRep_mk (a : Additive (BW.{u} K)) :
    haveI := bwRep_finiteDimensional a
    haveI := bwRep_nontrivial a
    BWMonoid.mk (bwRep a) = (Additive.toMul a).val :=
  (exists_division_of_unit (Additive.toMul a)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2

instance bwRep_instFiniteDimensional (a : Additive (BW.{u} K)) :
    FiniteDimensional K (bwRep a).carrier := bwRep_finiteDimensional a

instance bwRep_instNontrivial (a : Additive (BW.{u} K)) :
    Nontrivial (bwRep a).carrier := bwRep_nontrivial a

instance bwRep_instIsSuperCentral (a : Additive (BW.{u} K)) :
    IsSuperCentral (bwRep a).grading := bwRep_isSuperCentral a

instance bwRep_instIsGradedSimple (a : Additive (BW.{u} K)) :
    IsGradedSimple (bwRep a).grading := bwRep_isGradedSimple a

end Rep

/-! ### The fusion data -/

section Fuse

/-- **The gtensor-Wedderburn bundle** (M10-9, deliverable 2, private): the mirror of
`Wedderburn/DBWGroup.lean`'s `exists_division_of_gtensor`, but keeping the produced `SuperAlgEquiv`
`(bwRep a) ᵍ⊗ (bwRep b) ≅ M_{p|q}(D₃)` instead of discarding it for a bare class equation — that
equivalence is exactly what `bwFuse` needs. Azumaya closure (`isSuperAzumaya_of_central_simple`
on each factor, `isSuperAzumaya_tensorGrading` for the tensor) gives graded simplicity of the
tensor (`isGradedSimple_of_isSuperAzumaya`), unlocking `graded_wedderburn`; centrality of `D₃`
descends from the tensor via the P-twist (`isSuperCentral_of_equiv` then
`isSuperCentral_of_matrixSuper`), exactly as in `exists_division_of_gtensor`. -/
private theorem bwGtensorWedderburn (a b : Additive (BW.{u} K)) :
    ∃ (D₃ : SuperAlgebra.{u, u} K) (p q : ℕ),
      p + q ≠ 0 ∧ IsSuperCentral D₃.grading ∧ IsGradedSimple D₃.grading ∧
      FiniteDimensional K D₃.carrier ∧ Nontrivial D₃.carrier ∧
      Bimod.IsSuperDivision D₃.grading ∧
      Nonempty (SuperAlgEquiv ((bwRep a).gtensor (bwRep b)) (D₃.matrixSuper p q)) := by
  haveI hA1 : IsSuperAzumaya (bwRep a).grading :=
    isSuperAzumaya_of_central_simple (bwRep a).grading
  haveI hA2 : IsSuperAzumaya (bwRep b).grading :=
    isSuperAzumaya_of_central_simple (bwRep b).grading
  haveI hAtensor : IsSuperAzumaya ((bwRep a).gtensor (bwRep b)).grading :=
    isSuperAzumaya_tensorGrading (bwRep a).grading (bwRep b).grading
  haveI hAcentral : IsSuperCentral ((bwRep a).gtensor (bwRep b)).grading :=
    isSuperCentral_of_isSuperAzumaya ((bwRep a).gtensor (bwRep b)).grading
  haveI hAsimple : IsGradedSimple ((bwRep a).gtensor (bwRep b)).grading :=
    isGradedSimple_of_isSuperAzumaya ((bwRep a).gtensor (bwRep b)).grading
  obtain ⟨D₃, p, q, hpq, hdiv3, hfin3, hnontriv3, ⟨θ⟩⟩ :=
    graded_wedderburn ((bwRep a).gtensor (bwRep b))
  haveI := hfin3
  haveI := hnontriv3
  have hsimple3 : IsGradedSimple D₃.grading := IsSuperDivision.isGradedSimple hdiv3
  haveI hcentralMatrix : IsSuperCentral (D₃.matrixSuper p q).grading :=
    isSuperCentral_of_equiv ((bwRep a).gtensor (bwRep b)).grading (D₃.matrixSuper p q).grading
      θ.toAlgEquiv θ.map_grading
  have hcentral3 : IsSuperCentral D₃.grading := isSuperCentral_of_matrixSuper D₃ p q hpq
  exact ⟨D₃, p, q, hpq, hcentral3, hsimple3, hfin3, hnontriv3, hdiv3, ⟨θ⟩⟩

private noncomputable def bwD3 (a b : Additive (BW.{u} K)) : SuperAlgebra.{u, u} K :=
  (bwGtensorWedderburn a b).choose

private noncomputable def bwP (a b : Additive (BW.{u} K)) : ℕ :=
  (bwGtensorWedderburn a b).choose_spec.choose

private noncomputable def bwQ (a b : Additive (BW.{u} K)) : ℕ :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose

private theorem bwPQ_ne_zero (a b : Additive (BW.{u} K)) : bwP a b + bwQ a b ≠ 0 :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose_spec.1

private theorem bwD3_isSuperCentral (a b : Additive (BW.{u} K)) :
    IsSuperCentral (bwD3 a b).grading :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose_spec.2.1

private theorem bwD3_isGradedSimple (a b : Additive (BW.{u} K)) :
    IsGradedSimple (bwD3 a b).grading :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose_spec.2.2.1

private theorem bwD3_finiteDimensional (a b : Additive (BW.{u} K)) :
    FiniteDimensional K (bwD3 a b).carrier :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose_spec.2.2.2.1

private theorem bwD3_nontrivial (a b : Additive (BW.{u} K)) :
    Nontrivial (bwD3 a b).carrier :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose_spec.2.2.2.2.1

private theorem bwD3_isSuperDivision (a b : Additive (BW.{u} K)) :
    Bimod.IsSuperDivision (bwD3 a b).grading :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose_spec.2.2.2.2.2.1

private theorem bwD3_equiv (a b : Additive (BW.{u} K)) :
    Nonempty
      (SuperAlgEquiv ((bwRep a).gtensor (bwRep b)) ((bwD3 a b).matrixSuper (bwP a b) (bwQ a b))) :=
  (bwGtensorWedderburn a b).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2

private instance bwD3_instFiniteDimensional (a b : Additive (BW.{u} K)) :
    FiniteDimensional K (bwD3 a b).carrier := bwD3_finiteDimensional a b

private instance bwD3_instNontrivial (a b : Additive (BW.{u} K)) :
    Nontrivial (bwD3 a b).carrier := bwD3_nontrivial a b

private instance bwD3_instIsSuperCentral (a b : Additive (BW.{u} K)) :
    IsSuperCentral (bwD3 a b).grading := bwD3_isSuperCentral a b

private instance bwD3_instIsGradedSimple (a b : Additive (BW.{u} K)) :
    IsGradedSimple (bwD3 a b).grading := bwD3_isGradedSimple a b

/-- **The class chase**: `[D₃] = [bwRep a] ᵍ⊗ [bwRep b] = [bwRep (a+b)]`, at the `BWMonoid`
level. Route: `bwD3_equiv`'s witness gives `[D₃] = [(bwRep a) ᵍ⊗ (bwRep b)]`
(`IsBWEquivalent.of_matrixSuper`); `BWMonoid.mk_mul` splits the tensor class; `bwRep_mk` reads
each factor's class as `(Additive.toMul _).val`; `(toMul a).val * (toMul b).val = (toMul
(a+b)).val` is a *definitional* fact (`Additive.add`/`Units.mul` unfold to exactly this), proved
by `rfl` directly rather than by `rw`ing the generic `toMul_add`/`Units.val_mul` lemmas — the
latter trips the documented `BW K := (BWMonoid K)ˣ` semireducible-`def` diamond (`rw`'s
"instances"-transparency pattern matching resynthesizes a `Mul (BW K)` instance that is
defeq-but-not-syntactically-equal to the one already present in the goal). -/
private theorem bwD3_mk_eq (a b : Additive (BW.{u} K)) :
    BWMonoid.mk (bwD3 a b) = BWMonoid.mk (bwRep (a + b)) := by
  obtain ⟨θ⟩ := bwD3_equiv a b
  have h1 : BWMonoid.mk (bwD3 a b) = BWMonoid.mk ((bwRep a).gtensor (bwRep b)) :=
    BWMonoid.mk_eq_mk_iff.mpr (IsBWEquivalent.of_matrixSuper (bwPQ_ne_zero a b) θ).symm
  have h4 : (Additive.toMul a).val * (Additive.toMul b).val = (Additive.toMul (a + b)).val := rfl
  rw [h1, ← BWMonoid.mk_mul (bwRep a) (bwRep b), bwRep_mk a, bwRep_mk b, h4, ← bwRep_mk (a + b)]

/-- **Wedderburn uniqueness identifies `D₃` with `bwRep (a+b)`** (M10-8b,
`superAlgEquiv_of_bwMk_eq`), via the class chase `bwD3_mk_eq`. -/
private theorem bwD3_uniqueness_equiv (a b : Additive (BW.{u} K)) :
    Nonempty (SuperAlgEquiv (bwD3 a b) (bwRep (a + b))) :=
  superAlgEquiv_of_bwMk_eq (bwD3 a b) (bwRep (a + b))
    (bwD3_isSuperDivision a b) (bwRep_isSuperDivision (a + b)) (bwD3_mk_eq a b)

/-- **The fusion sizes** `σ(a,b) = (p, q)` (M10-9, deliverable 2): the sizes produced by
`bwGtensorWedderburn`. -/
noncomputable def bwSize (a b : Additive (BW.{u} K)) : ℕ × ℕ := (bwP a b, bwQ a b)

/-- **The fusion isomorphisms** `φ_{a,b}` (M10-9, deliverable 2): `bwGtensorWedderburn`'s
`(bwRep a) ᵍ⊗ (bwRep b) ≅ M_{p|q}(D₃)` composed with the `matrixSuper` congruence of the
Wedderburn-uniqueness isomorphism `D₃ ≅ bwRep (a+b)`. -/
noncomputable def bwFuse (a b : Additive (BW.{u} K)) :
    SuperAlgEquiv ((bwRep a).gtensor (bwRep b))
      ((bwRep (a + b)).matrixSuper (bwSize a b).1 (bwSize a b).2) :=
  (Classical.choice (bwD3_equiv a b)).trans
    ((Classical.choice (bwD3_uniqueness_equiv a b)).matrixSuper (bwP a b) (bwQ a b))

end Fuse

/-! ### The gauge -/

/-- **`bwGauge`, the tautological division fusion gauge on `BW(K)`** (M10-9): for every field
`K` with `2` invertible, the skeletal data `(BW(K), D_a, φ_{a,b})` of the paper's
superbicategory skeleton, realized as an honest term of `DivisionFusionGauge K (Additive (BW
K))`, assembled from `bwRep`/`bwSize`/`bwFuse`. -/
noncomputable def bwGauge : DivisionFusionGauge K (Additive (BW.{u} K)) where
  D := bwRep
  central := bwRep_isSuperCentral
  gradedSimple := bwRep_isGradedSimple
  division := bwRep_isSuperDivision
  nontriv := bwRep_nontrivial
  findim := bwRep_finiteDimensional
  size := bwSize
  fuse := bwFuse

/-! ### Tautological canonicality -/

/-- **Tautological canonicality** (M10-9, deliverable 4): `bwGauge`'s class map is (up to the
`Additive`/`Multiplicative` bookkeeping) the identity. -/
theorem bwGauge_bwClass (a : Additive (BW.{u} K)) :
    (bwGauge (K := K)).bwClass a = Additive.toMul a := by
  apply Units.ext
  rw [DivisionFusionGauge.bwClass_val]
  exact bwRep_mk a

/-- **`bwGauge` is canonical**: its class map is injective (immediate, `Additive.toMul` is an
equivalence) with range exactly `DBW K` (immediate from `DBW_eq_univ`, `BW K = DBW K`,
`Superfusion.Wedderburn.BWEqualsDBW`). -/
theorem bwGauge_isCanonical : (bwGauge (K := K)).IsCanonical := by
  refine ⟨fun a a' h => Additive.toMul.injective ?_, ?_⟩
  · rw [← bwGauge_bwClass, ← bwGauge_bwClass]
    exact h
  · rw [show (bwGauge (K := K)).bwClass = Additive.toMul from funext bwGauge_bwClass,
      Additive.toMul.range_eq_univ, DBW_eq_univ]

theorem bwGauge_bwClassHom_apply (a : Additive (BW.{u} K)) :
    (bwGauge (K := K)).bwClassHom a = a := by
  show Additive.ofMul ((bwGauge (K := K)).bwClass a) = a
  rw [bwGauge_bwClass]
  exact ofMul_toMul a

/-- **The class-map homomorphism is the identity**: `bwGauge.bwClassHom = id`, a cheap corollary
of `bwGauge_bwClass`. -/
theorem bwGauge_bwClassHom :
    (bwGauge (K := K)).bwClassHom = AddMonoidHom.id (Additive (BW.{u} K)) :=
  AddMonoidHom.ext bwGauge_bwClassHom_apply

/-! ### The parity -/

/-- **The gauge-level pentagon-parity cochain on `BW(K)`** (M10-9, deliverable 5): for every
field `K` with `2` invertible, there is a genuine function `p : BW(K)³ → ℤ/2`
(`Superfusion.Gauge.GaugePentagon`'s `gaugeParity`, M9-3b) measuring the pentagon-failure of the
tautological gauge `bwGauge` — `DivisionFusionGauge.gaugeParity` needs no hypotheses on the
gauge beyond being a `DivisionFusionGauge` (its own Skolem–Noether existence proof derives
everything from `Γ`'s per-object fields at the composite index), so it instantiates directly.
The `(p, χ)` cocycle *definition* itself lives in the bimodule layer (parallel session); this is
the computation device and existence witness of the skeletal `p`-data. -/
noncomputable def bwParity :
    Additive (BW.{u} K) → Additive (BW.{u} K) → Additive (BW.{u} K) → ZMod 2 :=
  (bwGauge (K := K)).gaugeParity

/-- **`bwParity`'s defining equation**: it is exactly `bwGauge.gaugeParity`. -/
theorem bwParity_eq (a b c : Additive (BW.{u} K)) :
    bwParity a b c = (bwGauge (K := K)).gaugeParity a b c := rfl

end Superfusion

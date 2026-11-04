/-
Superfusion / Wedderburn / BWEqualsDBW

Milestone M10-7 (arc extension): **`BW(K) = DBW(K)`** — every invertible Brauer–Wall class is
division-representable. This closes the open item recorded in `DBWGroup.lean`'s module
docstring: `DBW.MulClosed` (M10-6) shows the *product* of two division-representable classes is
division-representable, but says nothing about an *arbitrary* unit's representative, which
`Quotient.exists_rep` hands back with no control beyond finite-dimensionality and nontriviality.

**The route.** Given a unit `u : BW K`, unfold `u.val`, `u.inv` to arbitrary representatives
`P`, `Q` (`BWMonoid.exists_rep`); `u.val_inv` unwinds (via `BWMonoid.mk_mul`/`one_def`/
`mk_eq_mk_iff`) to `IsBWEquivalent (P ᵍ⊗ Q) (base K)`, i.e. a graded isomorphism after matrix
stabilization on both sides. The trivial class's own stabilization `M_{r|s}(K)` is central and
graded-simple (`isSuperCentral_matrix`/`isGradedSimple_matrix`, M7d-1, transported off
`evenGrading K K` via `matrixGradingA_evenGrading`); transport this along the graded isomorphism
onto `M_{p|q}(P ᵍ⊗ Q)` (`isSuperCentral_of_equiv`/`isGradedSimple_of_equiv`,
`isSuperCentral_and_isGradedSimple_of_bwEquivalent_base`), then descend the matrix stabilization
(`isSuperCentral_of_matrixSuper`, already landed; `isGradedSimple_of_matrixSuper`, new: an
entrywise two-sided ideal argument, mirroring the P-twist file's style) to get `P ᵍ⊗ Q` itself
central and graded-simple.

The genuinely new content is descending *further*, from the tensor product `P ᵍ⊗ Q` to the
single factor `P`:

* **Graded simplicity** (`isGradedSimple_of_gtensor`): a homogeneous two-sided ideal `J` of `P`
  gives rise to a homogeneous two-sided ideal `J ᵍ⊗ Q` of `P ᵍ⊗ Q` — realized concretely as
  `tensorIdealSubmodule`, the image of `J ⊗[K] Q` under the (flat-module, hence injective)
  inclusion map `TensorProduct.map J.subtype id`, landing inside the plain tensor product and
  then folded across `GradedTensorProduct.of` (`tensorIota`, `tensorIdealSubmodule`). Its
  dimension is `finrank J * finrank Q` (`finrank_tensorIdealSubmodule`), giving `J ᵍ⊗ Q = ⊥ ↔
  J = ⊥` and `= ⊤ ↔ J = ⊤` (`tensorIdealSubmodule_eq_bot_iff`/`_eq_top_iff`) — the properness and
  nonzero-ness directions of the correspondence. Two-sided-ideal closure
  (`tmul_mul_tensorIdealSubmodule_mem`/`tensorIdealSubmodule_mul_tmul_mem`, extended off pure
  tensors to arbitrary elements by `mul_tensorIdealSubmodule_mem`/`tensorIdealSubmodule_mul_mem`)
  is a direct Koszul-sign computation via `tmul_coe_mul_coe_tmul`, splitting the *other* tensor
  factor into its even/odd parts so the multiplication formula's homogeneity hypotheses are met.
  Homogeneity of the ideal (`tensorIdealSubmodule_isHomogeneous`) is the same computation via
  `tensorMask_tmul`, using homogeneity of `J`. Graded simplicity of `P ᵍ⊗ Q` then forces
  `J ᵍ⊗ Q ∈ {⊥, ⊤}`, hence (by the dimension count) `J ∈ {⊥, ⊤}`.
* **Supercentrality** (`isSuperCentral_of_gtensor`): a homogeneous supercentral `z ∈ P` gives
  `z ᵍ⊗ 1`, homogeneous supercentral in `P ᵍ⊗ Q` (`tmul_one_supercentral`, a direct
  `tmul_coe_mul_coe_tmul` sign computation, `tmul_one_supercentral_tmul`); supercentrality of
  `P ᵍ⊗ Q` forces `z ᵍ⊗ 1` to be a scalar, and `a ↦ a ᵍ⊗ 1` is injective (`tmul_one_injective`,
  via `Algebra.TensorProduct.includeLeft_injective` — a field's `algebraMap` into a nontrivial
  algebra is always injective, `FaithfulSMul.algebraMap_injective`), so `z` itself is a scalar.

Assembling: `P` central, graded-simple, finite-dimensional, nontrivial ⇒ `graded_wedderburn`
realizes it as `M_{p|q}(D)`, `D` a super division algebra; centrality of `D` descends from `P`
via the P-twist exactly as in M10-6's `exists_division_of_gtensor` (`exists_division_of_unit`).
This exhibits `D` as a division representative of `u.val`'s class, i.e. `u ∈ DBW K`
(`DBW_eq_univ`, `DBWSubgroup_eq_top`).

**The headline corollary.** Composing `zmod8_mulEquiv_DBWReal : Multiplicative (ZMod 8) ≃*
DBWRealSubgroup` (`Gauge/DBWRealGroup.lean`, the completed real classification) with the subgroup
identification `DBWRealSubgroup = DBWSubgroup ℝ = ⊤` (`DBWSubgroup_real_eq`, `DBWSubgroup_eq_top`)
and `Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G` gives the paper's **`BW(ℝ) ≅ ℤ/8`**
(`bw_real_equiv_zmod8`).
-/
import Superfusion.Wedderburn.DBWGroup
import Mathlib.RingTheory.Flat.Basic

namespace Superfusion

open TensorProduct GradedTensorProduct Module

/-! ### Deliverable 1: entrywise descent of graded simplicity across matrix stabilization

The converse companion to `isSuperCentral_of_matrixSuper` (the P-twist descent, `Wedderburn/
AzumayaConverse.lean`): graded simplicity of `M_{p|q}(D)` descends to graded simplicity of `D`,
provided `p + q ≠ 0`. The matrix-with-entries-in-`J` set is a homogeneous two-sided ideal of the
matrix superalgebra (entrywise membership; homogeneity via `matrixMaskA`, `decompose_
matrixGradingA_zero_coe`/`_one_coe`), read back out at a fixed diagonal index. -/

section MatrixDescent

variable {K : Type*} [Field K]

/-- **Graded simplicity descends across matrix stabilization** (M10-7, deliverable 1): dual to
`isSuperCentral_of_matrixSuper`. A homogeneous two-sided ideal `J` of `D` gives the entrywise
ideal `{M | ∀ a b, M a b ∈ J}` of `M_{p|q}(D)`, homogeneous by `matrixMaskA`; graded simplicity of
the matrix algebra forces it to `⊥` (read off the `(a₀,a₀)` entry of a diagonal witness) or `⊤`
(read off the `(a₀,a₀)` entry of `1`), giving `J = ⊥` or `J = ⊤`. -/
theorem isGradedSimple_of_matrixSuper (D : SuperAlgebra K) (p q : ℕ) (hpq : p + q ≠ 0)
    [IsGradedSimple (D.matrixSuper p q).grading] : IsGradedSimple D.grading := by
  haveI hIGS : IsGradedSimple (matrixGradingA (sumParity p q) D.grading) :=
    ‹IsGradedSimple (D.matrixSuper p q).grading›
  haveI hne : Nonempty (Fin p ⊕ Fin q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  obtain ⟨a0⟩ := hne
  constructor
  intro J hJ
  set Jmat : TwoSidedIdeal (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier) :=
    TwoSidedIdeal.mk' {M | ∀ a b, M a b ∈ J}
      (fun a b => by simp)
      (fun {M N} hM hN a b => by rw [Matrix.add_apply]; exact J.add_mem (hM a b) (hN a b))
      (fun {M} hM a b => by rw [Matrix.neg_apply]; exact J.neg_mem (hM a b))
      (fun {M N} hN a b => by
        rw [Matrix.mul_apply]
        exact sum_mem fun c _ => J.mul_mem_left (M a c) (N c b) (hN c b))
      (fun {M N} hM a b => by
        rw [Matrix.mul_apply]
        exact sum_mem fun c _ => J.mul_mem_right (M a c) (N c b) (hM a c))
    with hJmatdef
  have hJmatHom : TwoSidedIdeal.IsHomogeneous (matrixGradingA (sumParity p q) D.grading) Jmat := by
    intro M hM i
    have hMmem : ∀ a b, M a b ∈ J := (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp hM
    rcases zmod2_cases i with hi | hi <;> subst hi
    · rw [decompose_matrixGradingA_zero_coe, TwoSidedIdeal.mem_mk']
      intro a b
      rw [matrixMaskA_apply]
      exact hJ (M a b) (hMmem a b) _
    · rw [decompose_matrixGradingA_one_coe, TwoSidedIdeal.mem_mk']
      intro a b
      rw [matrixMaskA_apply]
      exact hJ (M a b) (hMmem a b) _
  rcases IsGradedSimple.eq_bot_or_eq_top Jmat hJmatHom with hbot | htop
  · left
    ext x
    rw [TwoSidedIdeal.mem_bot]
    constructor
    · intro hx
      have hM : (Matrix.diagonal (fun _ => x) :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier) ∈ Jmat := by
        rw [TwoSidedIdeal.mem_mk']
        intro a b
        by_cases hab : a = b
        · subst hab; rw [Matrix.diagonal_apply_eq]; exact hx
        · rw [Matrix.diagonal_apply_ne _ hab]; exact J.zero_mem
      rw [hbot, TwoSidedIdeal.mem_bot] at hM
      have hentry := congrFun (congrFun hM a0) a0
      rwa [Matrix.diagonal_apply_eq, Matrix.zero_apply] at hentry
    · rintro rfl; exact J.zero_mem
  · right
    ext x
    simp only [TwoSidedIdeal.mem_top, iff_true]
    have h1 : (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier) ∈ Jmat := by
      rw [htop]; exact TwoSidedIdeal.mem_top _
    have h1' := (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp h1 a0 a0
    rw [Matrix.one_apply_eq] at h1'
    have hx1 := J.mul_mem_left x 1 h1'
    rwa [mul_one] at hx1

end MatrixDescent

/-! ### Deliverable 2: the tensor ideal `J ᵍ⊗ Q` inside `P ᵍ⊗ Q`

For a homogeneous two-sided ideal `J` of `P`, `J ᵍ⊗ Q` is realized as a `K`-submodule of the
graded tensor product `P ᵍ⊗ Q` (kept at the *folded* type `P.grading ᵍ⊗[K] Q.grading` throughout,
never `(P.gtensor Q).carrier`, to avoid the semireducible-`def` instance mismatches that
`SuperAlgebra.gtensor`/`.matrixSuper` otherwise trigger): the image of the injective map
`J ⊗[K] Q → P ⊗[K] Q` (injective since every module over a field is flat,
`TensorProduct.map_injective_of_flat_flat`), folded across `GradedTensorProduct.of`. Its
dimension is `finrank J * finrank Q` (`finrank_tensorIdealSubmodule`), and it equals the span of
`{j ᵍ⊗ q | j ∈ J}` (`tensorIdealSubmodule_eq_span`, via `TensorProduct.range_map_eq_span_tmul`). -/

section TensorIdeal

universe u
variable {K : Type u} [Field K]
variable (P Q : SuperAlgebra.{u,u} K)

/-- A `TwoSidedIdeal` of `P.carrier`, viewed as a `K`-submodule (automatic since a two-sided
ideal absorbs multiplication by `algebraMap K P.carrier c`). -/
def idealToSubmodule (J : TwoSidedIdeal P.carrier) : Submodule K P.carrier where
  carrier := J
  zero_mem' := J.zero_mem
  add_mem' := J.add_mem
  smul_mem' c x hx := by
    rw [Algebra.smul_def]
    exact J.mul_mem_left _ _ hx

theorem mem_idealToSubmodule {J : TwoSidedIdeal P.carrier} {x : P.carrier} :
    x ∈ idealToSubmodule P J ↔ x ∈ J := Iff.rfl

variable {P Q}

/-- The inclusion `J ⊗[K] Q → P ⊗[K] Q` underlying the tensor ideal. -/
noncomputable def tensorIota (J : TwoSidedIdeal P.carrier) :
    (idealToSubmodule P J) ⊗[K] Q.carrier →ₗ[K] P.carrier ⊗[K] Q.carrier :=
  TensorProduct.map (idealToSubmodule P J).subtype (LinearMap.id : Q.carrier →ₗ[K] Q.carrier)

theorem tensorIota_injective (J : TwoSidedIdeal P.carrier) :
    Function.Injective (tensorIota (P := P) (Q := Q) J) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _)
    Function.injective_id

/-- **The tensor ideal `J ᵍ⊗ Q`** (M10-7, deliverable 2): the image of `J ⊗[K] Q` inside
`P ᵍ⊗[K] Q`, folded across `GradedTensorProduct.of`. -/
noncomputable def tensorIdealSubmodule (J : TwoSidedIdeal P.carrier) :
    Submodule K (P.grading ᵍ⊗[K] Q.grading) :=
  Submodule.map (GradedTensorProduct.of K P.grading Q.grading).toLinearMap
    (LinearMap.range (tensorIota (Q := Q) J))

theorem tensorIdealSubmodule_eq_span (J : TwoSidedIdeal P.carrier) :
    tensorIdealSubmodule (Q := Q) J
      = Submodule.span K
        {z : P.grading ᵍ⊗[K] Q.grading | ∃ (j : P.carrier) (_ : j ∈ J) (q : Q.carrier),
          z = (j ᵍ⊗ₜ[K] q : P.grading ᵍ⊗[K] Q.grading)} := by
  rw [tensorIdealSubmodule, tensorIota,
    TensorProduct.range_map_eq_span_tmul, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨j, q, rfl⟩, rfl⟩
    exact ⟨(j : P.carrier), j.2, q, rfl⟩
  · rintro ⟨j, hj, q, rfl⟩
    exact ⟨(⟨j, hj⟩ : idealToSubmodule P J) ⊗ₜ[K] q, ⟨⟨j, hj⟩, q, rfl⟩, rfl⟩

/-- **`finrank (J ᵍ⊗ Q) = finrank J * finrank Q`** (M10-7, deliverable 2): the dimension count
carrying the properness and nonzero-ness directions of the ideal correspondence. -/
theorem finrank_tensorIdealSubmodule [FiniteDimensional K P.carrier]
    [FiniteDimensional K Q.carrier] (J : TwoSidedIdeal P.carrier) :
    finrank K (tensorIdealSubmodule (Q := Q) J)
      = finrank K (idealToSubmodule P J) * finrank K Q.carrier := by
  rw [tensorIdealSubmodule, LinearEquiv.finrank_map_eq]
  rw [(LinearEquiv.ofInjective (tensorIota (Q := Q) J) (tensorIota_injective J)).finrank_eq.symm]
  exact Module.finrank_tensorProduct

private theorem gen_mem_tensorIdealSubmodule (J : TwoSidedIdeal P.carrier)
    (j : P.carrier) (hj : j ∈ J) (q : Q.carrier) :
    (j ᵍ⊗ₜ[K] q : P.grading ᵍ⊗[K] Q.grading) ∈ tensorIdealSubmodule (Q := Q) J := by
  rw [tensorIdealSubmodule_eq_span]
  exact Submodule.subset_span ⟨j, hj, q, rfl⟩

/-- Left-multiplication by an arbitrary pure tensor stays inside the tensor ideal: the "touching"
factors (the second slot of the left tensor, the first slot of the ideal generator) are split
into even/odd parts so `tmul_coe_mul_coe_tmul`'s homogeneity hypotheses are met, landing each of
the four cross terms back in `J ᵍ⊗ Q` via left-ideal absorption. -/
theorem tmul_mul_tensorIdealSubmodule_mem {J : TwoSidedIdeal P.carrier}
    (hJ : TwoSidedIdeal.IsHomogeneous P.grading J)
    (a : P.carrier) (b : Q.carrier) (j : P.carrier) (hj : j ∈ J) (q : Q.carrier) :
    ((a ᵍ⊗ₜ[K] b : P.grading ᵍ⊗[K] Q.grading) * (j ᵍ⊗ₜ[K] q))
      ∈ tensorIdealSubmodule (Q := Q) J := by
  have hb : b = evenPart Q.grading b + oddPart Q.grading b :=
    (evenPart_add_oddPart Q.grading b).symm
  have hj' : j = evenPart P.grading j + oddPart P.grading j :=
    (evenPart_add_oddPart P.grading j).symm
  have hj0 : evenPart P.grading j ∈ J := hJ j hj 0
  have hj1 : oddPart P.grading j ∈ J := hJ j hj 1
  have hb0 : evenPart Q.grading b ∈ Q.grading 0 := evenPart_mem Q.grading b
  have hb1 : oddPart Q.grading b ∈ Q.grading 1 := oddPart_mem Q.grading b
  have hje0 : evenPart P.grading j ∈ P.grading 0 := evenPart_mem P.grading j
  have hje1 : oddPart P.grading j ∈ P.grading 1 := oddPart_mem P.grading j
  rw [hb, hj', gtmul_add, add_gtmul, mul_add, add_mul, add_mul]
  have e00 := tmul_coe_mul_coe_tmul P.grading Q.grading a
    (⟨evenPart Q.grading b, hb0⟩ : Q.grading 0) (⟨evenPart P.grading j, hje0⟩ : P.grading 0) q
  have e01 := tmul_coe_mul_coe_tmul P.grading Q.grading a
    (⟨evenPart Q.grading b, hb0⟩ : Q.grading 0) (⟨oddPart P.grading j, hje1⟩ : P.grading 1) q
  have e10 := tmul_coe_mul_coe_tmul P.grading Q.grading a
    (⟨oddPart Q.grading b, hb1⟩ : Q.grading 1) (⟨evenPart P.grading j, hje0⟩ : P.grading 0) q
  have e11 := tmul_coe_mul_coe_tmul P.grading Q.grading a
    (⟨oddPart Q.grading b, hb1⟩ : Q.grading 1) (⟨oddPart P.grading j, hje1⟩ : P.grading 1) q
  simp only at e00 e01 e10 e11
  rw [e00, e01, e10, e11]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_) <;>
    · rw [Units.smul_def]
      refine zsmul_mem ?_ _
      first
      | exact gen_mem_tensorIdealSubmodule J _ (J.mul_mem_left a _ hj0) _
      | exact gen_mem_tensorIdealSubmodule J _ (J.mul_mem_left a _ hj1) _

/-- Right-multiplication by an arbitrary pure tensor stays inside the tensor ideal, the mirror of
`tmul_mul_tensorIdealSubmodule_mem`: right-ideal absorption absorbs the ideal generator `j`
directly (no homogeneity of `j` needed), so only the *other* two factors need splitting. -/
theorem tensorIdealSubmodule_mul_tmul_mem {J : TwoSidedIdeal P.carrier}
    (j : P.carrier) (hj : j ∈ J) (q : Q.carrier) (a : P.carrier) (b : Q.carrier) :
    ((j ᵍ⊗ₜ[K] q : P.grading ᵍ⊗[K] Q.grading) * (a ᵍ⊗ₜ[K] b))
      ∈ tensorIdealSubmodule (Q := Q) J := by
  have hq : q = evenPart Q.grading q + oddPart Q.grading q :=
    (evenPart_add_oddPart Q.grading q).symm
  have ha : a = evenPart P.grading a + oddPart P.grading a :=
    (evenPart_add_oddPart P.grading a).symm
  have hqe0 : evenPart Q.grading q ∈ Q.grading 0 := evenPart_mem Q.grading q
  have hqe1 : oddPart Q.grading q ∈ Q.grading 1 := oddPart_mem Q.grading q
  have hae0 : evenPart P.grading a ∈ P.grading 0 := evenPart_mem P.grading a
  have hae1 : oddPart P.grading a ∈ P.grading 1 := oddPart_mem P.grading a
  rw [hq, ha, gtmul_add, add_gtmul, mul_add, add_mul, add_mul]
  have e00 := tmul_coe_mul_coe_tmul P.grading Q.grading j
    (⟨evenPart Q.grading q, hqe0⟩ : Q.grading 0) (⟨evenPart P.grading a, hae0⟩ : P.grading 0) b
  have e01 := tmul_coe_mul_coe_tmul P.grading Q.grading j
    (⟨evenPart Q.grading q, hqe0⟩ : Q.grading 0) (⟨oddPart P.grading a, hae1⟩ : P.grading 1) b
  have e10 := tmul_coe_mul_coe_tmul P.grading Q.grading j
    (⟨oddPart Q.grading q, hqe1⟩ : Q.grading 1) (⟨evenPart P.grading a, hae0⟩ : P.grading 0) b
  have e11 := tmul_coe_mul_coe_tmul P.grading Q.grading j
    (⟨oddPart Q.grading q, hqe1⟩ : Q.grading 1) (⟨oddPart P.grading a, hae1⟩ : P.grading 1) b
  simp only at e00 e01 e10 e11
  rw [e00, e01, e10, e11]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_) <;>
    · rw [Units.smul_def]
      refine zsmul_mem ?_ _
      exact gen_mem_tensorIdealSubmodule J _ (J.mul_mem_right j _ hj) _

end TensorIdeal

/-! ### Deliverable 3: two-sided-ideal closure, homogeneity, and the bot/top correspondence -/

section TensorIdealClosure

universe u
variable {K : Type u} [Field K]
variable {P Q : SuperAlgebra.{u,u} K}

/-- A safe induction principle for `P.grading ᵍ⊗[K] Q.grading`, staying at the folded type
throughout (avoiding the `GradedTensorProduct`/underlying-tensor-product type mismatch that a
direct `induction x using TensorProduct.induction_on` triggers on a `𝒜 ᵍ⊗[K] ℬ`-typed variable,
since the folded type carries a different `Mul`). -/
private theorem gtensor_induction {p : (P.grading ᵍ⊗[K] Q.grading) → Prop}
    (x : P.grading ᵍ⊗[K] Q.grading)
    (tmul : ∀ (a : P.carrier) (b : Q.carrier), p (a ᵍ⊗ₜ[K] b))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) : p x := by
  have key : ∀ t : P.carrier ⊗[K] Q.carrier,
      p (GradedTensorProduct.of K P.grading Q.grading t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact zero
    | tmul a b => exact tmul a b
    | add u v hu hv =>
        rw [map_add]
        exact add _ _ hu hv
  have h := key ((GradedTensorProduct.of K P.grading Q.grading).symm x)
  rwa [GradedTensorProduct.symm_of_of] at h

theorem mul_tensorIdealSubmodule_mem {J : TwoSidedIdeal P.carrier}
    (hJ : TwoSidedIdeal.IsHomogeneous P.grading J)
    (x : P.grading ᵍ⊗[K] Q.grading) {y : P.grading ᵍ⊗[K] Q.grading}
    (hy : y ∈ tensorIdealSubmodule (Q := Q) J) :
    x * y ∈ tensorIdealSubmodule (Q := Q) J := by
  rw [tensorIdealSubmodule_eq_span] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, q, rfl⟩ := hz
    refine gtensor_induction (p := fun x => x * (j ᵍ⊗ₜ[K] q) ∈ tensorIdealSubmodule (Q := Q) J)
      x ?_ ?_ ?_
    · intro a b; exact tmul_mul_tensorIdealSubmodule_mem hJ a b j hj q
    · rw [zero_mul]; exact Submodule.zero_mem _
    · intro u v hu hv; rw [add_mul]; exact Submodule.add_mem _ hu hv
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
    rw [mul_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
    rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu

theorem tensorIdealSubmodule_mul_mem {J : TwoSidedIdeal P.carrier}
    {y : P.grading ᵍ⊗[K] Q.grading} (hy : y ∈ tensorIdealSubmodule (Q := Q) J)
    (x : P.grading ᵍ⊗[K] Q.grading) :
    y * x ∈ tensorIdealSubmodule (Q := Q) J := by
  rw [tensorIdealSubmodule_eq_span] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, q, rfl⟩ := hz
    refine gtensor_induction (p := fun x => (j ᵍ⊗ₜ[K] q) * x ∈ tensorIdealSubmodule (Q := Q) J)
      x ?_ ?_ ?_
    · intro a b; exact tensorIdealSubmodule_mul_tmul_mem j hj q a b
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro u v hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
    rw [add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu

/-- The `i`-th graded component of `P.grading ᵍ⊗[K] Q.grading`, as computed by `DirectSum.decompose`,
is exactly `tensorMask P.grading Q.grading i` — the `TensorGrading.lean` masking construction. -/
private theorem decompose_tensorGrading_zero_coe (x : P.grading ᵍ⊗[K] Q.grading) :
    (DirectSum.decompose (tensorGrading P.grading Q.grading) x 0 :
        P.grading ᵍ⊗[K] Q.grading) = tensorMask P.grading Q.grading 0 x := by
  conv_lhs => rw [← tensorMask_zero_add_tensorMask_one P.grading Q.grading x]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_same _ (tensorMask_mem P.grading Q.grading 0 x),
    DirectSum.decompose_of_mem_ne _ (tensorMask_mem P.grading Q.grading 1 x)
      (by decide : (1 : ZMod 2) ≠ 0), add_zero]

private theorem decompose_tensorGrading_one_coe (x : P.grading ᵍ⊗[K] Q.grading) :
    (DirectSum.decompose (tensorGrading P.grading Q.grading) x 1 :
        P.grading ᵍ⊗[K] Q.grading) = tensorMask P.grading Q.grading 1 x := by
  conv_lhs => rw [← tensorMask_zero_add_tensorMask_one P.grading Q.grading x]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_ne _ (tensorMask_mem P.grading Q.grading 0 x)
      (by decide : (0 : ZMod 2) ≠ 1),
    DirectSum.decompose_of_mem_same _ (tensorMask_mem P.grading Q.grading 1 x), zero_add]

private theorem decompose_tensorGrading_coe (i : ZMod 2) (x : P.grading ᵍ⊗[K] Q.grading) :
    ((DirectSum.decompose (tensorGrading P.grading Q.grading) x i :
        tensorGrading P.grading Q.grading i) : P.grading ᵍ⊗[K] Q.grading)
      = tensorMask P.grading Q.grading i x := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact decompose_tensorGrading_zero_coe x
  · exact decompose_tensorGrading_one_coe x

/-- **The tensor ideal is homogeneous** (M10-7, deliverable 3): on a generator `j ᵍ⊗ q`,
`tensorMask_tmul` splits the degree-`i` component into `(gradeProj 0 j) ᵍ⊗ (gradeProj i q) +
(gradeProj 1 j) ᵍ⊗ (gradeProj (i+1) q)`, each summand a fresh generator since `J`'s own
homogeneity puts `gradeProj 0 j`, `gradeProj 1 j` back in `J`. -/
theorem tensorIdealSubmodule_isHomogeneous {J : TwoSidedIdeal P.carrier}
    (hJ : TwoSidedIdeal.IsHomogeneous P.grading J) {x : P.grading ᵍ⊗[K] Q.grading}
    (hx : x ∈ tensorIdealSubmodule (Q := Q) J) (i : ZMod 2) :
    tensorMask P.grading Q.grading i x ∈ tensorIdealSubmodule (Q := Q) J := by
  rw [tensorIdealSubmodule_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨j, hj, q, rfl⟩ := hz
      rw [tensorMask_tmul]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.subset_span
          ⟨gradeProj P.grading 0 j, hJ j hj 0, gradeProj Q.grading i q, rfl⟩
      · exact Submodule.subset_span
          ⟨gradeProj P.grading 1 j, hJ j hj 1, gradeProj Q.grading (i + 1) q, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu

theorem idealToSubmodule_eq_bot_iff (J : TwoSidedIdeal P.carrier) :
    idealToSubmodule P J = ⊥ ↔ J = ⊥ := by
  constructor
  · intro h
    refine TwoSidedIdeal.ext fun x => ?_
    rw [TwoSidedIdeal.mem_bot]
    constructor
    · intro hx
      have hx' : x ∈ idealToSubmodule P J := hx
      rwa [h, Submodule.mem_bot] at hx'
    · rintro rfl
      exact J.zero_mem
  · intro h
    refine Submodule.ext fun x => ?_
    rw [Submodule.mem_bot, mem_idealToSubmodule, h, TwoSidedIdeal.mem_bot]

theorem idealToSubmodule_eq_top_iff (J : TwoSidedIdeal P.carrier) :
    idealToSubmodule P J = ⊤ ↔ J = ⊤ := by
  constructor
  · intro h
    refine TwoSidedIdeal.ext fun x => ⟨fun _ => TwoSidedIdeal.mem_top _, fun _ => ?_⟩
    have hx' : x ∈ idealToSubmodule P J := h ▸ Submodule.mem_top
    exact hx'
  · intro h
    refine Submodule.ext fun x => ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    rw [mem_idealToSubmodule, h]
    exact TwoSidedIdeal.mem_top _

end TensorIdealClosure

section TensorIdealDimension

universe u
variable {K : Type u} [Field K]
variable {P Q : SuperAlgebra.{u,u} K}
variable [FiniteDimensional K P.carrier] [FiniteDimensional K Q.carrier] [Nontrivial Q.carrier]

omit [Nontrivial Q.carrier] in
private theorem finrank_gtensor_eq :
    finrank K (P.grading ᵍ⊗[K] Q.grading) = finrank K P.carrier * finrank K Q.carrier := by
  rw [← (GradedTensorProduct.of K P.grading Q.grading).finrank_eq]
  exact Module.finrank_tensorProduct

private theorem finrank_Q_pos : 0 < finrank K Q.carrier := Module.finrank_pos

/-- **`J ᵍ⊗ Q = ⊥ ↔ J = ⊥`** (M10-7, deliverable 3): the nonzero-ness direction of the ideal
correspondence, via the dimension count `finrank_tensorIdealSubmodule` and `finrank Q ≠ 0`. -/
theorem tensorIdealSubmodule_eq_bot_iff (J : TwoSidedIdeal P.carrier) :
    tensorIdealSubmodule (Q := Q) J = ⊥ ↔ J = ⊥ := by
  haveI : Module.Finite K (P.grading ᵍ⊗[K] Q.grading) := finite_gtensor P.grading Q.grading
  rw [← idealToSubmodule_eq_bot_iff (P := P) J, ← Submodule.finrank_eq_zero (R := K),
    ← Submodule.finrank_eq_zero (R := K), finrank_tensorIdealSubmodule, mul_eq_zero]
  have hQpos : finrank K Q.carrier ≠ 0 := finrank_Q_pos.ne'
  constructor
  · rintro (h0 | h0)
    · exact h0
    · exact absurd h0 hQpos
  · intro h0
    exact Or.inl h0

/-- **`J ᵍ⊗ Q = ⊤ ↔ J = ⊤`** (M10-7, deliverable 3): the properness direction, again via the
dimension count. -/
theorem tensorIdealSubmodule_eq_top_iff (J : TwoSidedIdeal P.carrier) :
    tensorIdealSubmodule (Q := Q) J = ⊤ ↔ J = ⊤ := by
  haveI : Module.Finite K (P.grading ᵍ⊗[K] Q.grading) := finite_gtensor P.grading Q.grading
  rw [← idealToSubmodule_eq_top_iff (P := P) J]
  constructor
  · intro h
    have hfr : finrank K (tensorIdealSubmodule (Q := Q) J)
        = finrank K (P.grading ᵍ⊗[K] Q.grading) := by rw [h, finrank_top]
    rw [finrank_tensorIdealSubmodule, finrank_gtensor_eq] at hfr
    have hcancel := mul_right_cancel₀ finrank_Q_pos.ne' hfr
    exact Submodule.eq_top_of_finrank_eq (by rw [hcancel])
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_tensorIdealSubmodule, h, finrank_top, finrank_gtensor_eq]

end TensorIdealDimension

/-! ### Deliverable 4: supercentrality descends from `P ᵍ⊗ Q` to `P` -/

section CentralDescent

universe u
variable {K : Type u} [Field K]
variable {P Q : SuperAlgebra.{u,u} K}

/-- **`a ↦ a ᵍ⊗ 1` is injective** whenever `Q` is nontrivial: a field's `algebraMap` into any
nontrivial algebra is injective (`FaithfulSMul.algebraMap_injective`), so
`Algebra.TensorProduct.includeLeft` is injective on the underlying (plain) tensor product, which
shares its additive/module structure with the graded tensor product via `GradedTensorProduct.of`. -/
theorem tmul_one_injective [Nontrivial Q.carrier] :
    Function.Injective
      (fun a : P.carrier => (a ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading)) := by
  intro a a' h
  have h' : (a : P.carrier) ⊗ₜ[K] (1 : Q.carrier) = a' ⊗ₜ[K] (1 : Q.carrier) :=
    (GradedTensorProduct.of K P.grading Q.grading).injective h
  exact Algebra.TensorProduct.includeLeft_injective
    (R := K) (S := K) (FaithfulSMul.algebraMap_injective K Q.carrier) h'

private theorem zsmul_gtensor (n : ℤ) (x : P.carrier) (y : Q.carrier) :
    ((n • x) ᵍ⊗ₜ[K] y : P.grading ᵍ⊗[K] Q.grading) = n • (x ᵍ⊗ₜ[K] y) := by
  rw [show (((n • x) ᵍ⊗ₜ[K] y : P.grading ᵍ⊗[K] Q.grading))
      = GradedTensorProduct.of K P.grading Q.grading ((n • x) ⊗ₜ[K] y) from rfl,
    show ((n • x) ⊗ₜ[K] y : P.carrier ⊗[K] Q.carrier) = n • (x ⊗ₜ[K] y) from
      (TensorProduct.smul_tmul' _ _ _).symm,
    map_zsmul]

private theorem zmod2_centrality_sign (iz j1 j2 : ZMod 2) :
    iz * j1 = iz * (j1 + j2) + j2 * iz := by decide +revert

/-- The Koszul-sign computation carrying `z ᵍ⊗ 1`'s supercommutation with a bi-homogeneous
generator `a ᵍ⊗ b` of `P ᵍ⊗ Q`, from `z`'s own supercentrality in `P`. -/
private theorem tmul_one_supercentral_tmul {z : P.carrier} {iz : ZMod 2} (hz : z ∈ P.grading iz)
    (hzc : IsSupercentral P.grading iz z) {j1 j2 : ZMod 2}
    (a : P.carrier) (ha : a ∈ P.grading j1) (b : Q.carrier) (hb : b ∈ Q.grading j2) :
    ((z ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading) * (a ᵍ⊗ₜ[K] b))
      = ((sgn (iz * (j1 + j2)) : ℤˣ) : ℤ) • ((a ᵍ⊗ₜ[K] b) * (z ᵍ⊗ₜ[K] (1 : Q.carrier))) := by
  have hL := tmul_coe_mul_coe_tmul P.grading Q.grading z
    (⟨(1 : Q.carrier), SetLike.one_mem_graded Q.grading⟩ : Q.grading 0) (⟨a, ha⟩ : P.grading j1) b
  have hR := tmul_coe_mul_coe_tmul P.grading Q.grading a
    (⟨b, hb⟩ : Q.grading j2) (⟨z, hz⟩ : P.grading iz) (1 : Q.carrier)
  simp only [zero_mul, uzpow_zero, one_smul, one_mul] at hL
  simp only [mul_one] at hR
  rw [← sgn_eq_neg_one_uzpow, Units.smul_def] at hR
  rw [hL, hR, hzc j1 a ha, zsmul_gtensor, smul_smul, ← Units.val_mul, ← sgn_add,
    zmod2_centrality_sign iz j1 j2]

private theorem tmul_one_supercentral {z : P.carrier} {iz : ZMod 2} (hz : z ∈ P.grading iz)
    (hzc : IsSupercentral P.grading iz z) :
    IsSupercentral (tensorGrading P.grading Q.grading) iz
      (z ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading) := by
  intro j w hw
  refine tensorGrading_induction P.grading Q.grading hw
    (p := fun w => (z ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading) * w
      = ((sgn (iz * j) : ℤˣ) : ℤ) • (w * (z ᵍ⊗ₜ[K] (1 : Q.carrier))))
    ?_ ?_ ?_ ?_
  · intro j1 j2 a b hjk ha hb
    rw [← hjk]
    exact tmul_one_supercentral_tmul hz hzc a ha b hb
  · simp
  · intro u v hu hv
    simp only [mul_add, add_mul, hu, hv, smul_add]
  · intro c u hu
    rw [mul_smul_comm, hu, smul_comm, smul_mul_assoc]

/-- **Supercentrality descends from `P ᵍ⊗ Q` to `P`** (M10-7, deliverable 4): a homogeneous
supercentral `z ∈ P` gives `z ᵍ⊗ 1`, homogeneous supercentral in `P ᵍ⊗ Q`
(`tmul_one_supercentral`); supercentrality of `P ᵍ⊗ Q` forces it to be a scalar
`algebraMap c ᵍ⊗ 1`, and injectivity of `a ↦ a ᵍ⊗ 1` (`tmul_one_injective`) reads off
`z = algebraMap c`. -/
theorem isSuperCentral_of_gtensor [FiniteDimensional K P.carrier] [FiniteDimensional K Q.carrier]
    [Nontrivial P.carrier] [Nontrivial Q.carrier]
    [IsSuperCentral (tensorGrading P.grading Q.grading)] : IsSuperCentral P.grading := by
  constructor
  have layer : ∀ iz : ZMod 2, superCenterGrade P.grading iz ≤ (1 : Submodule K P.carrier) := by
    rintro iz z ⟨hz, hzc⟩
    have hz'c : IsSupercentral (tensorGrading P.grading Q.grading) iz
        (z ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading) :=
      tmul_one_supercentral hz hzc
    have hz'mem : (z ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading)
        ∈ tensorGrading P.grading Q.grading iz := by
      have h := tmul_mem_tensorGrading P.grading Q.grading hz (SetLike.one_mem_graded Q.grading)
      rwa [add_zero] at h
    have hone : (z ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading)
        ∈ (1 : Submodule K (P.grading ᵍ⊗[K] Q.grading)) :=
      mem_one_of_isSupercentral (𝒜 := tensorGrading P.grading Q.grading) hz'mem hz'c
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hone
    have halg : (algebraMap K P.carrier c ᵍ⊗ₜ[K] (1 : Q.carrier) : P.grading ᵍ⊗[K] Q.grading)
        = z ᵍ⊗ₜ[K] (1 : Q.carrier) := by
      rw [← hc]
      exact (GradedTensorProduct.algebraMap_def P.grading Q.grading c).symm
    have hzc' := tmul_one_injective halg
    exact Submodule.mem_one.mpr ⟨c, hzc'⟩
  rw [superCenter, sup_le_iff]
  exact ⟨layer 0, layer 1⟩

end CentralDescent

/-! ### Deliverable 5: graded simplicity descends from `P ᵍ⊗ Q` to `P` -/

section SimpleDescent

universe u
variable {K : Type u} [Field K]
variable {P Q : SuperAlgebra.{u,u} K}

/-- **Graded simplicity descends from `P ᵍ⊗ Q` to `P`** (M10-7, deliverable 5): a homogeneous
two-sided ideal `J` of `P` gives the tensor ideal `Jideal := J ᵍ⊗ Q` of `P ᵍ⊗ Q`
(`tensorIdealSubmodule`, wrapped as a `TwoSidedIdeal` via `mul_tensorIdealSubmodule_mem`/
`tensorIdealSubmodule_mul_mem`, homogeneous via `tensorIdealSubmodule_isHomogeneous`); graded
simplicity of `P ᵍ⊗ Q` forces `Jideal ∈ {⊥, ⊤}`, and the dimension correspondence
(`tensorIdealSubmodule_eq_bot_iff`/`_eq_top_iff`) reads this back as `J ∈ {⊥, ⊤}`. -/
theorem isGradedSimple_of_gtensor [FiniteDimensional K P.carrier] [FiniteDimensional K Q.carrier]
    [Nontrivial Q.carrier]
    [IsGradedSimple (tensorGrading P.grading Q.grading)] : IsGradedSimple P.grading := by
  constructor
  intro J hJ
  set Jideal : TwoSidedIdeal (P.grading ᵍ⊗[K] Q.grading) :=
    TwoSidedIdeal.mk' (tensorIdealSubmodule (Q := Q) J : Set _)
      (Submodule.zero_mem _)
      (fun {_ _} hx hy => Submodule.add_mem _ hx hy)
      (fun {_} hx => Submodule.neg_mem _ hx)
      (fun {x y} hy => mul_tensorIdealSubmodule_mem hJ x hy)
      (fun {x y} hx => tensorIdealSubmodule_mul_mem hx y)
    with hJidealdef
  have hJidealHom : TwoSidedIdeal.IsHomogeneous (tensorGrading P.grading Q.grading) Jideal := by
    intro x hx i
    rw [TwoSidedIdeal.mem_mk'] at hx ⊢
    rw [decompose_tensorGrading_coe]
    exact tensorIdealSubmodule_isHomogeneous hJ hx i
  have hJidealCarrier : (Jideal : Set (P.grading ᵍ⊗[K] Q.grading))
      = (tensorIdealSubmodule (Q := Q) J : Set (P.grading ᵍ⊗[K] Q.grading)) :=
    TwoSidedIdeal.coe_mk' _ _ _ _ _ _
  rcases IsGradedSimple.eq_bot_or_eq_top Jideal hJidealHom with hbot | htop
  · left
    have hSub : tensorIdealSubmodule (Q := Q) J = ⊥ := by
      apply Submodule.ext
      intro x
      rw [Submodule.mem_bot, ← SetLike.mem_coe, ← hJidealCarrier, SetLike.mem_coe,
        hbot, TwoSidedIdeal.mem_bot]
    exact (tensorIdealSubmodule_eq_bot_iff J).mp hSub
  · right
    have hSub : tensorIdealSubmodule (Q := Q) J = ⊤ := by
      refine Submodule.ext fun x => ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
      rw [← SetLike.mem_coe, ← hJidealCarrier, SetLike.mem_coe, htop]
      exact TwoSidedIdeal.mem_top _
    exact (tensorIdealSubmodule_eq_top_iff J).mp hSub

end SimpleDescent

/-! ### Deliverable 6: an algebra `BW`-equivalent to the base is central and graded-simple -/

section BaseEquivalent

universe u
variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- **`IsBWEquivalent A (base K)` gives `A` central + graded-simple** (M10-7, deliverable 6): the
trivial class's own stabilization `M_{r|s}(K)` is central and graded-simple (`isSuperCentral_
matrix`/`isGradedSimple_matrix`, M7d-1, transported off `evenGrading K K` via `matrixGradingA_
evenGrading`); transport along the witnessing graded isomorphism `θ.symm` onto `M_{p|q}(A)`
(`isSuperCentral_of_equiv`/`isGradedSimple_of_equiv`), then descend the matrix stabilization
(`isSuperCentral_of_matrixSuper`, the P-twist; `isGradedSimple_of_matrixSuper`, deliverable 1). -/
theorem isSuperCentral_and_isGradedSimple_of_bwEquivalent_base {A : SuperAlgebra.{u,u} K}
    (h : IsBWEquivalent A (SuperAlgebra.base K)) :
    IsSuperCentral A.grading ∧ IsGradedSimple A.grading := by
  obtain ⟨p, q, r, s, hpq, hrs, ⟨θ⟩⟩ := h
  haveI hrsNE : Nonempty (Fin r ⊕ Fin s) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hr⟩⟩
  have heq : matrixGradingA (sumParity r s) (evenGrading K K) = matrixGrading (sumParity r s) K :=
    matrixGradingA_evenGrading _
  haveI hCmat0 : IsSuperCentral (matrixGrading (sumParity r s) K) := isSuperCentral_matrix _ K
  haveI hSmat0 : IsGradedSimple (matrixGrading (sumParity r s) K) := isGradedSimple_matrix _ K
  haveI hCmatA : IsSuperCentral (matrixGradingA (sumParity r s) (evenGrading K K)) := by
    constructor
    rw [heq]
    exact IsSuperCentral.superCenter_le_one (𝒜 := matrixGrading (sumParity r s) K)
  haveI hSmatA : IsGradedSimple (matrixGradingA (sumParity r s) (evenGrading K K)) :=
    isGradedSimple_of_equiv (matrixGrading (sumParity r s) K)
      (matrixGradingA (sumParity r s) (evenGrading K K))
      AlgEquiv.refl
      (fun i => by
        show (matrixGrading (sumParity r s) K i).map (LinearMap.id)
          = matrixGradingA (sumParity r s) (evenGrading K K) i
        rw [Submodule.map_id]
        exact (congrFun heq i).symm)
  haveI hCbase : IsSuperCentral ((SuperAlgebra.base K).matrixSuper r s).grading := hCmatA
  haveI hSbase : IsGradedSimple ((SuperAlgebra.base K).matrixSuper r s).grading := hSmatA
  haveI hCA : IsSuperCentral (A.matrixSuper p q).grading :=
    isSuperCentral_of_equiv ((SuperAlgebra.base K).matrixSuper r s).grading
      (A.matrixSuper p q).grading θ.symm.toAlgEquiv θ.symm.map_grading
  haveI hSA : IsGradedSimple (A.matrixSuper p q).grading :=
    isGradedSimple_of_equiv ((SuperAlgebra.base K).matrixSuper r s).grading
      (A.matrixSuper p q).grading θ.symm.toAlgEquiv θ.symm.map_grading
  exact ⟨isSuperCentral_of_matrixSuper A p q hpq, isGradedSimple_of_matrixSuper A p q hpq⟩

end BaseEquivalent

/-! ### Deliverable 7: the final assembly — `BW(K) = DBW(K)` -/

section FinalAssembly

universe u
variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- Every element of the class monoid `BWMonoid K` has an explicit central-simple representative
(`Quotient.exists_rep`, repackaged with the two instance fields split out). -/
theorem BWMonoid.exists_rep (x : BWMonoid.{u} K) :
    ∃ (P : SuperAlgebra.{u,u} K) (hf : FiniteDimensional K P.carrier) (hn : Nontrivial P.carrier),
      haveI := hf; haveI := hn; x = BWMonoid.mk P := by
  obtain ⟨P, hP⟩ := Quotient.exists_rep x
  refine ⟨P.1, P.2.1, P.2.2, ?_⟩
  haveI := P.2.1
  haveI := P.2.2
  rw [← hP]
  rfl

/-- **Every unit of `BW K` has a division representative** (M10-7, deliverable 7): unfold `u.val`,
`u.inv` to arbitrary representatives `P`, `Q`; `u.val_inv` unwinds to `IsBWEquivalent (P ᵍ⊗ Q)
(base K)`, giving `P ᵍ⊗ Q` central and graded-simple
(`isSuperCentral_and_isGradedSimple_of_bwEquivalent_base`), hence (deliverables 4–5) `P` itself
central and graded-simple. `graded_wedderburn` realizes `P ≅ M_{p|q}(D)`, `D` a super division
algebra; centrality of `D` descends from `P` via the P-twist exactly as in M10-6's
`exists_division_of_gtensor`. -/
theorem exists_division_of_unit (u : BW.{u} K) :
    ∃ (D : SuperAlgebra.{u, u} K) (_ : IsSuperCentral D.grading) (_ : IsGradedSimple D.grading)
      (hf : FiniteDimensional K D.carrier) (hn : Nontrivial D.carrier),
      Bimod.IsSuperDivision D.grading ∧
        haveI := hf; haveI := hn; BWMonoid.mk D = u.val := by
  obtain ⟨P, hPf, hPn, hPeq⟩ := BWMonoid.exists_rep u.val
  obtain ⟨Q, hQf, hQn, hQeq⟩ := BWMonoid.exists_rep u.inv
  haveI := hPf
  haveI := hPn
  haveI := hQf
  haveI := hQn
  have hIBE : IsBWEquivalent (P.gtensor Q) (SuperAlgebra.base K) := by
    have h1 := u.val_inv
    rw [hPeq, hQeq, BWMonoid.mk_mul, BWMonoid.one_def] at h1
    exact BWMonoid.mk_eq_mk_iff.mp h1
  obtain ⟨hCT, hST⟩ := isSuperCentral_and_isGradedSimple_of_bwEquivalent_base hIBE
  haveI hCT' : IsSuperCentral (tensorGrading P.grading Q.grading) := hCT
  haveI hST' : IsGradedSimple (tensorGrading P.grading Q.grading) := hST
  haveI hCP : IsSuperCentral P.grading := isSuperCentral_of_gtensor (Q := Q)
  haveI hSP : IsGradedSimple P.grading := isGradedSimple_of_gtensor (Q := Q)
  obtain ⟨D, p, q, hpq, hdiv, hfin, hnontriv, ⟨θ⟩⟩ := graded_wedderburn P
  haveI := hfin
  haveI := hnontriv
  have hSD : IsGradedSimple D.grading := IsSuperDivision.isGradedSimple hdiv
  haveI hcentralMatrix : IsSuperCentral (D.matrixSuper p q).grading :=
    isSuperCentral_of_equiv P.grading (D.matrixSuper p q).grading θ.toAlgEquiv θ.map_grading
  have hCD : IsSuperCentral D.grading := isSuperCentral_of_matrixSuper D p q hpq
  refine ⟨D, hCD, hSD, hfin, hnontriv, hdiv, ?_⟩
  rw [hPeq]
  exact BWMonoid.mk_eq_mk_iff.mpr (IsBWEquivalent.of_matrixSuper hpq θ).symm

/-- **`DBW K = BW K`**, as sets (M10-7): every unit has a division representative. -/
theorem DBW_eq_univ : DBW.{u} K = Set.univ := by
  ext u
  simp only [Set.mem_univ, iff_true]
  exact exists_division_of_unit u

/-- **`DBWSubgroup K = ⊤`** (M10-7, the headline of this file): `DBW(K)` is *every* Brauer–Wall
class, for every field `K` with `2` invertible. -/
theorem DBWSubgroup_eq_top : DBWSubgroup.{u} K = ⊤ := by
  refine Subgroup.ext fun u => ⟨fun _ => Subgroup.mem_top u, fun _ => ?_⟩
  show u ∈ DBW K
  rw [DBW_eq_univ]
  trivial

end FinalAssembly

/-! ### The headline corollary: `BW(ℝ) ≅ ℤ/8` -/

/-- **The paper's `BW(ℝ) ≅ ℤ/8`**: composing `zmod8_mulEquiv_DBWReal` (the completed real
classification, `Gauge/DBWRealGroup.lean`) with the subgroup identification `DBWRealSubgroup =
DBWSubgroup ℝ = ⊤` (`DBWSubgroup_real_eq`, `DBWSubgroup_eq_top`) and `Subgroup.topEquiv`. -/
noncomputable def bw_real_equiv_zmod8 : Multiplicative (ZMod 8) ≃* BW ℝ :=
  zmod8_mulEquiv_DBWReal.trans
    ((MulEquiv.subgroupCongr (DBWSubgroup_real_eq.symm.trans DBWSubgroup_eq_top)).trans
      Subgroup.topEquiv)

end Superfusion

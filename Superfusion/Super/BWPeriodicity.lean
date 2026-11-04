/-
Superfusion / Super / BWPeriodicity

Milestones M7d-4b-3 and M7e-1: **Brauer–Wall mod-8 periodicity** —

  `D_ε^{⊗̂ (n+8)} ≅ M_{8|8}(D_ε^{⊗̂ n})`   for every `n` and `ε = ±1`,
  over any field `K` with `2` invertible  (`bw_mod8`, `bw_mod8_neg`).

The eighth-power shift of the division tower is exactly one `M_{8|8}`
matrix stabilization: the index of the standard super division
algebras matters only mod `8` up to Brauer–Wall equivalence
(`IsBWEquivalent`, defined by graded isomorphism after matrix
stabilization, mirroring mathlib's `IsBrauerEquivalent`).  Over `ℝ`
both signs combine to shift the paper's `D_n` (`n : ℤ`) by eight in
either direction (`DReal_bw_mod8`, `DReal_bw_mod8_neg`).  This is the
*upper-bound* half of `BW(ℝ) ≅ ℤ/8`; that `8` is the exact period
(the classes of `D₀, …, D₇` are pairwise distinct) is a separate,
genuinely `ℝ`-specific statement, not formalized here.

Assembly: graded isomorphisms are bundled as `SuperAlgEquiv`
(refl/symm/trans); the odd double is functorial in graded equivalences
(`OddDouble.congr`, by the universal property with an explicit
entrywise inverse); the base case is the Bott certificate
(`bottSuper`/`bottSuperNeg`, bridged by `matrixGradingA_evenGrading`),
and the induction step (`towerMatrixEquivOfBott`, generic in `ε` and
the base case) is the commutation
`OddDouble (M_{8|8}(A)) ≅ M_{8|8}(OddDouble A)` of M7d-4b-2.
-/
import Superfusion.Super.OddDoubleMatrix
import Superfusion.Super.BottCertificate

namespace Superfusion

/-! ### Functoriality of the odd double in graded equivalences -/

namespace OddDouble

section Congr

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (ε : K)
variable (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)

include hφ in
theorem congrHom_hconj (a : A) :
    gen ℬ ε * ((inl ℬ ε).comp φ.toAlgHom) a
      = ((inl ℬ ε).comp φ.toAlgHom) (parityMap 𝒜 a) * gen ℬ ε := by
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  rw [gen_mul_inl, parityMap_map 𝒜 ℬ φ hφ]

/-- The forward map `OddDouble 𝒜 ε → OddDouble ℬ ε` induced by a graded
equivalence, from the universal property. -/
noncomputable def congrHom : OddDouble 𝒜 ε →ₐ[K] OddDouble ℬ ε :=
  lift 𝒜 ε ((inl ℬ ε).comp φ.toAlgHom) (gen ℬ ε) (gen_mul_gen ℬ ε)
    (congrHom_hconj 𝒜 ℬ ε φ hφ)

include hφ in
theorem congrHom_mk (a b : A) :
    congrHom 𝒜 ℬ ε φ hφ (mk 𝒜 ε a b) = mk ℬ ε (φ a) (φ b) := by
  rw [congrHom, lift_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  rw [inl_mul_gen]
  exact ext ℬ ε (by simp) (by simp)

include hφ in
theorem congrHom_bijective :
    Function.Bijective (congrHom 𝒜 ℬ ε φ hφ) := by
  have hR : Function.LeftInverse
      (fun x => mk 𝒜 ε (φ.symm (p1 ℬ ε x)) (φ.symm (p2 ℬ ε x)))
      (congrHom 𝒜 ℬ ε φ hφ) := by
    intro x
    have hx : x = mk 𝒜 ε (p1 𝒜 ε x) (p2 𝒜 ε x) := (mk_p1_p2 𝒜 ε x).symm
    show mk 𝒜 ε (φ.symm (p1 ℬ ε (congrHom 𝒜 ℬ ε φ hφ x)))
        (φ.symm (p2 ℬ ε (congrHom 𝒜 ℬ ε φ hφ x))) = x
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    rw [congrHom_mk, p1_mk, p2_mk, AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply]
  have hL : Function.RightInverse
      (fun x => mk 𝒜 ε (φ.symm (p1 ℬ ε x)) (φ.symm (p2 ℬ ε x)))
      (congrHom 𝒜 ℬ ε φ hφ) := by
    intro P
    rw [congrHom_mk, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    exact mk_p1_p2 ℬ ε P
  exact ⟨hR.injective, hL.surjective⟩

include hφ in
theorem congrHom_isHomogeneous :
    IsHomogeneousHom (grading 𝒜 ε) (grading ℬ ε)
      (congrHom 𝒜 ℬ ε φ hφ) := by
  refine lift_isHomogeneous 𝒜 ε ((inl ℬ ε).comp φ.toAlgHom) (gen ℬ ε)
    (gen_mul_gen ℬ ε) (congrHom_hconj 𝒜 ℬ ε φ hφ) (grading ℬ ε) ?_
    (gen_mem_grading ℬ ε)
  intro j x hx
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  exact inl_mem_grading ℬ ε ((mem_iff_map_mem 𝒜 ℬ φ hφ).mp hx)

include hφ in
theorem congrHom_map_grading (i : ZMod 2) :
    ((grading 𝒜 ε) i).map (congrHom 𝒜 ℬ ε φ hφ).toLinearMap
      = grading ℬ ε i :=
  map_grading_of_bijective (grading 𝒜 ε) (grading ℬ ε)
    (congrHom 𝒜 ℬ ε φ hφ) (congrHom_isHomogeneous 𝒜 ℬ ε φ hφ)
    (congrHom_bijective 𝒜 ℬ ε φ hφ) i

/-- The odd double is functorial in graded equivalences. -/
noncomputable def congr : OddDouble 𝒜 ε ≃ₐ[K] OddDouble ℬ ε :=
  AlgEquiv.ofBijective (congrHom 𝒜 ℬ ε φ hφ)
    (congrHom_bijective 𝒜 ℬ ε φ hφ)

end Congr

end OddDouble

/-! ### Graded isomorphisms of bundled superalgebras -/

section Bundled

variable {K : Type*} [CommRing K]

/-- A graded isomorphism of bundled superalgebras. -/
structure SuperAlgEquiv (P Q : SuperAlgebra K) where
  /-- The underlying algebra equivalence. -/
  toAlgEquiv : P.carrier ≃ₐ[K] Q.carrier
  map_grading : ∀ i,
    (P.grading i).map toAlgEquiv.toLinearMap = Q.grading i

namespace SuperAlgEquiv

variable {P Q R : SuperAlgebra K}

/-- Identity. -/
def refl (P : SuperAlgebra K) : SuperAlgEquiv P P :=
  ⟨AlgEquiv.refl, fun _ => Submodule.map_id _⟩

/-- Inverse. -/
def symm (e : SuperAlgEquiv P Q) : SuperAlgEquiv Q P :=
  ⟨e.toAlgEquiv.symm, fun i => by
    rw [← e.map_grading i, ← Submodule.map_comp]
    have h : e.toAlgEquiv.symm.toLinearMap.comp e.toAlgEquiv.toLinearMap
        = LinearMap.id := by
      ext x
      simp
    rw [h, Submodule.map_id]⟩

/-- Composition. -/
def trans (e : SuperAlgEquiv P Q) (f : SuperAlgEquiv Q R) :
    SuperAlgEquiv P R :=
  ⟨e.toAlgEquiv.trans f.toAlgEquiv, fun i => by
    rw [← f.map_grading i, ← e.map_grading i, ← Submodule.map_comp]
    rfl⟩

end SuperAlgEquiv

/-! ### Bundled constructions -/

/-- The `M_{p|q}` matrix stabilization of a bundled superalgebra. -/
noncomputable def SuperAlgebra.matrixSuper (P : SuperAlgebra K)
    (p q : ℕ) : SuperAlgebra K where
  carrier := Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier
  grading := matrixGradingA (sumParity p q) P.grading

/-- Functoriality of the odd double, bundled. -/
noncomputable def OddDouble.congrSuper {P Q : SuperAlgebra K} (ε : K)
    (e : SuperAlgEquiv P Q) :
    SuperAlgEquiv (P.oddDouble ε) (Q.oddDouble ε) :=
  ⟨OddDouble.congr P.grading Q.grading ε e.toAlgEquiv e.map_grading,
    OddDouble.congrHom_map_grading P.grading Q.grading ε e.toAlgEquiv
      e.map_grading⟩

/-- The commutation of M7d-4b-2, bundled. -/
noncomputable def OddDouble.matrixSuperCommute (P : SuperAlgebra K)
    (p q : ℕ) (ε : K) :
    SuperAlgEquiv ((P.matrixSuper p q).oddDouble ε)
      ((P.oddDouble ε).matrixSuper p q) :=
  ⟨OddDouble.oddDoubleMatrixEquiv (sumParity p q) P.grading ε,
    OddDouble.oddDoubleMatrixEquiv_map_grading (sumParity p q) P.grading ε⟩

/-- The inductive shift, generic in `ε` and the base case: if the
eighth floor of the `ε`-tower trivializes to `M_{8|8}(K)`, then every
floor shifts by eight up to one `M_{8|8}` stabilization (the induction
step is the commutation of the odd double with matrix stabilization,
M7d-4b-2). -/
noncomputable def towerMatrixEquivOfBott (ε : K)
    (bott : SuperAlgEquiv (divisionTower ε 8)
      ((SuperAlgebra.base K).matrixSuper 8 8)) :
    ∀ n : ℕ, SuperAlgEquiv (divisionTower ε (n + 8))
      ((divisionTower ε n).matrixSuper 8 8)
  | 0 => bott
  | n + 1 =>
      (OddDouble.congrSuper ε (towerMatrixEquivOfBott ε bott n)).trans
        (OddDouble.matrixSuperCommute (divisionTower ε n) 8 8 ε)

/-! ### Brauer–Wall equivalence -/

/-- Brauer–Wall equivalence of bundled superalgebras: graded
isomorphism after matrix stabilization (mirroring mathlib's
`IsBrauerEquivalent`, including its nonemptiness conditions — without
`p + q ≠ 0` the index type of `M_{0|0}` is empty, the stabilization is
the zero ring, and the relation would degenerate to the total
relation). -/
def IsBWEquivalent (P Q : SuperAlgebra K) : Prop :=
  ∃ p q r s : ℕ, p + q ≠ 0 ∧ r + s ≠ 0 ∧
    Nonempty (SuperAlgEquiv (P.matrixSuper p q) (Q.matrixSuper r s))

theorem IsBWEquivalent.refl (P : SuperAlgebra K) : IsBWEquivalent P P :=
  ⟨1, 0, 1, 0, one_ne_zero, one_ne_zero, ⟨SuperAlgEquiv.refl _⟩⟩

theorem IsBWEquivalent.symm {P Q : SuperAlgebra K}
    (h : IsBWEquivalent P Q) : IsBWEquivalent Q P := by
  obtain ⟨p, q, r, s, hpq, hrs, ⟨e⟩⟩ := h
  exact ⟨r, s, p, q, hrs, hpq, ⟨e.symm⟩⟩

end Bundled

/-! ### Mod-8 periodicity over a field with `2` invertible -/

section Mod8

variable (K : Type*) [Field K] [Invertible (2 : K)]

/-- The Bott certificate, bundled: `D₁^{⊗̂8} ≅ M_{8|8}(K)` as bundled
superalgebras (the target grading is bridged by
`matrixGradingA_evenGrading`). -/
noncomputable def bottSuper :
    SuperAlgEquiv (divisionTower (1 : K) 8)
      ((SuperAlgebra.base K).matrixSuper 8 8) :=
  ⟨(Bott.bottEquiv K :
      (divisionTower (1 : K) 8).carrier ≃ₐ[K]
        ((SuperAlgebra.base K).matrixSuper 8 8).carrier),
    fun i => by
      show ((divisionTower (1 : K) 8).grading i).map
          (Bott.bottEquiv K).toLinearMap
        = matrixGradingA (sumParity 8 8) (SuperAlgebra.base K).grading i
      rw [show matrixGradingA (sumParity 8 8) (SuperAlgebra.base K).grading
          = matrixGrading (sumParity 8 8) K from
        matrixGradingA_evenGrading (sumParity 8 8)]
      exact Bott.bottHom_map_grading K i⟩

/-- The `ε = -1` Bott certificate, bundled: `D₋₁^{⊗̂8} ≅ M_{8|8}(K)`. -/
noncomputable def bottSuperNeg :
    SuperAlgEquiv (divisionTower (-1 : K) 8)
      ((SuperAlgebra.base K).matrixSuper 8 8) :=
  ⟨(Bott.bottEquivNeg K :
      (divisionTower (-1 : K) 8).carrier ≃ₐ[K]
        ((SuperAlgebra.base K).matrixSuper 8 8).carrier),
    fun i => by
      show ((divisionTower (-1 : K) 8).grading i).map
          (Bott.bottEquivNeg K).toLinearMap
        = matrixGradingA (sumParity 8 8) (SuperAlgebra.base K).grading i
      rw [show matrixGradingA (sumParity 8 8) (SuperAlgebra.base K).grading
          = matrixGrading (sumParity 8 8) K from
        matrixGradingA_evenGrading (sumParity 8 8)]
      exact Bott.bottHomNeg_map_grading K i⟩

/-- The inductive shift: the `(n+8)`-th floor of the `ε = +1` tower is
the `M_{8|8}` stabilization of the `n`-th floor, as graded algebras. -/
noncomputable def towerMatrixEquiv (n : ℕ) :
    SuperAlgEquiv (divisionTower (1 : K) (n + 8))
      ((divisionTower (1 : K) n).matrixSuper 8 8) :=
  towerMatrixEquivOfBott (1 : K) (bottSuper K) n

/-- The inductive shift for the `ε = -1` tower. -/
noncomputable def towerMatrixEquivNeg (n : ℕ) :
    SuperAlgEquiv (divisionTower (-1 : K) (n + 8))
      ((divisionTower (-1 : K) n).matrixSuper 8 8) :=
  towerMatrixEquivOfBott (-1 : K) (bottSuperNeg K) n

/-- **Brauer–Wall mod-8 periodicity** (M7d-4b-3, M7e-1):
`D₁^{⊗̂(n+8)} ≅ M_{8|8}(D₁^{⊗̂ n})` as graded algebras for every `n`,
over any field with `2` invertible — the index of the standard super
division algebras matters only mod `8` up to matrix stabilization.
Standard axioms only. -/
theorem bw_mod8 (n : ℕ) :
    Nonempty (SuperAlgEquiv (divisionTower (1 : K) (n + 8))
      ((divisionTower (1 : K) n).matrixSuper 8 8)) :=
  ⟨towerMatrixEquiv K n⟩

/-- **Brauer–Wall mod-8 periodicity**, `ε = -1` (M7e-1). -/
theorem bw_mod8_neg (n : ℕ) :
    Nonempty (SuperAlgEquiv (divisionTower (-1 : K) (n + 8))
      ((divisionTower (-1 : K) n).matrixSuper 8 8)) :=
  ⟨towerMatrixEquivNeg K n⟩

end Mod8

/-! ### The paper's `D_n` over `ℝ`: both directions -/

/-- Mod-8 periodicity for the paper's standard super division algebras,
positive direction: `D_{n+8} ≅ M_{8|8}(D_n)` for `0 ≤ n`. -/
theorem DReal_bw_mod8 (n : ℤ) (hn : 0 ≤ n) :
    Nonempty (SuperAlgEquiv (DReal (n + 8)) ((DReal n).matrixSuper 8 8)) := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have h1 : DReal (n + 8) = divisionTower (1 : ℝ) (n.natAbs + 8) := by
    unfold DReal
    rw [if_pos (by omega : (0 : ℤ) ≤ n + 8)]
    congr 1
    omega
  have h2 : DReal n = divisionTower (1 : ℝ) n.natAbs := by
    unfold DReal
    rw [if_pos hn]
  rw [h1, h2]
  exact bw_mod8 ℝ n.natAbs

/-- Mod-8 periodicity for the paper's standard super division algebras,
negative direction: `D_{n-8} ≅ M_{8|8}(D_n)` for `n ≤ 0`. -/
theorem DReal_bw_mod8_neg (n : ℤ) (hn : n ≤ 0) :
    Nonempty (SuperAlgEquiv (DReal (n - 8)) ((DReal n).matrixSuper 8 8)) := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have h1 : DReal (n - 8) = divisionTower (-1 : ℝ) (n.natAbs + 8) := by
    unfold DReal
    rw [if_neg (by omega : ¬ (0 : ℤ) ≤ n - 8)]
    congr 1
    omega
  have h2 : DReal n = divisionTower (-1 : ℝ) n.natAbs := by
    unfold DReal
    rcases eq_or_lt_of_le hn with h0 | hneg
    · rw [h0, if_pos le_rfl]
      rfl
    · rw [if_neg (by omega)]
  rw [h1, h2]
  exact bw_mod8_neg ℝ n.natAbs

end Superfusion

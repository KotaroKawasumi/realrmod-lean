/-
Superfusion / Gauge / RealFuse3

Milestone M9-4b-ii-3: **the quaternion row/column of the 64 real fusion
isomorphisms**: the thirteen pairs `(4, b)`/`(a, 4)` (plus `(4, 4)`)
involving `realRep 4 = quatEvenSuper` (purely even `ℍ`).

The key structural simplification, spelled out fully once (`quatFuse`,
Stage 0): since `realRep 4` is *purely even* (`evenGrading ℝ ℍ[ℝ]`), the
Koszul sign `(-1)^{ji}` in the anticommutation hypothesis of
`GradedTensorProduct.lift` is *always* `1` when the first tensor factor is
`realRep 4` — the only nonzero grade of `ℍ` is `0`, and `(-1)^{j·0} = 1` for
every `j`.  So building an algebra map out of `(realRep 4).gtensor B` from
two homogeneous pieces reduces to building an ordinary (ungraded) algebra
map out of the honest tensor product `ℍ ⊗[ℝ] B`, i.e. **two commuting
algebra homs out of `ℍ` and `B`** — no sign bookkeeping anywhere.

Stage 1 (`realFuse_four_four`, the priority case `(4,4)`): rather than
re-deriving this by hand, we reuse the already-landed general machinery
for **Wall's isomorphism** (`Superfusion.Super.GradedEndMatrix`):
for a nontrivial finite-dimensional central-simple superalgebra `P`,
`P ᵍ⊗ P.sop ≅ P.gEnd ≅ M_{p|q}(K)` with `p = dim P₀`, `q = dim P₁`
(`wallSuperEquiv`, `endMatrixSuper`).  Since `ℍ` is purely even, its
super-opposite `ℍ.sop` has *no* Koszul sign either, and is literally the
ordinary opposite algebra `ℍᵐᵒᵖ` — already identified with `ℍ` itself by
mathlib's quaternion conjugation (`Quaternion.starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ`).
Chaining `ℍ ≅ ℍ.sop` (via `starAe`, wrapped through `SuperOp`) with
`wallSuperEquiv` and `endMatrixSuper` gives `ℍ ᵍ⊗ ℍ ≅ M_{4|0}(ℝ)` with no
new bijectivity argument at all — central simplicity (already landed in
`Superfusion.Gauge.RealReps`) does all the work.

Stages 2 (`(4,7)`/`(7,4)`) and 3 (`(4,1)`/`(1,4)`) build the two odd-target
pairs directly from Stage 0's commuting-pair recipe: the even part of
`Cl_{0,3}`/`Cl_{3,0}` is `ℍ` (Table 1), and the volume element `ω` is a
*central* odd square-one/minus-one element, giving the second (odd)
factor's image for free.

Design record: docs/paper-tables-extract.md, docs/super-track-design.md.
-/
import Superfusion.Gauge.RealFuse2
import Superfusion.Super.GradedEndMatrix
import Superfusion.Super.GradedEndMatrixExplicit
import Superfusion.Super.CliffordRankOne
import Mathlib.Algebra.QuaternionBasis

namespace Superfusion

open TensorProduct
open GradedTensorProduct
open Quaternion

/-! ### Stage 0: the purely-even super-opposite of the quaternions -/

section EvenSop

/-- **The purely-even super-opposite has no Koszul sign**: for `ℍ`
(purely even), `SuperOp (evenGrading ℝ ℍ)` is literally the ordinary
opposite algebra, already identified with `ℍ` by mathlib's quaternion
conjugation `Quaternion.starAe`. -/
noncomputable def quatSopEquiv :
    ℍ[ℝ] ≃ₐ[ℝ] SuperOp (evenGrading ℝ ℍ[ℝ]) where
  toFun x := SuperOp.op (evenGrading ℝ ℍ[ℝ]) (Quaternion.starAe x).unop
  invFun y := Quaternion.starAe.symm (MulOpposite.op (SuperOp.unop (evenGrading ℝ ℍ[ℝ]) y))
  left_inv x := by
    simp only [SuperOp.unop_op, MulOpposite.op_unop, AlgEquiv.symm_apply_apply]
  right_inv y := by
    simp only [AlgEquiv.apply_symm_apply, MulOpposite.unop_op, SuperOp.op_unop]
  map_mul' x y := by
    show SuperOp.op _ (Quaternion.starAe (x * y)).unop
        = SuperOp.op _ (Quaternion.starAe x).unop * SuperOp.op _ (Quaternion.starAe y).unop
    rw [map_mul, MulOpposite.unop_mul, SuperOp.mul_def, SuperOp.unop_op, SuperOp.unop_op,
      SuperOp.mulMap_apply,
      oddPart_of_mem_zero (evenGrading ℝ ℍ[ℝ]) (mem_evenGrading_zero ℝ ℍ[ℝ] _),
      oddPart_of_mem_zero (evenGrading ℝ ℍ[ℝ]) (mem_evenGrading_zero ℝ ℍ[ℝ] _), mul_zero,
      zsmul_zero, sub_zero]
  map_add' x y := by
    show SuperOp.op _ (Quaternion.starAe (x + y)).unop
        = SuperOp.op _ (Quaternion.starAe x).unop + SuperOp.op _ (Quaternion.starAe y).unop
    rw [map_add, MulOpposite.unop_add, map_add]
  commutes' r := by
    show SuperOp.op (evenGrading ℝ ℍ[ℝ]) (Quaternion.starAe (algebraMap ℝ ℍ[ℝ] r)).unop
        = algebraMap ℝ (SuperOp (evenGrading ℝ ℍ[ℝ])) r
    rw [AlgEquiv.commutes]
    rfl

/-- The bundled graded equivalence `quatEvenSuper ≅ quatEvenSuper.sop`. -/
noncomputable def quatSopSuperEquiv : SuperAlgEquiv quatEvenSuper quatEvenSuper.sop :=
  ⟨quatSopEquiv, fun i => by
    rcases zmod2_cases i with hi | hi <;> subst hi
    · show (evenGrading ℝ ℍ[ℝ] 0).map quatSopEquiv.toLinearMap = evenGrading ℝ ℍ[ℝ] 0
      rw [evenGrading_zero, Submodule.map_top, LinearMap.range_eq_top.mpr quatSopEquiv.surjective]
      rfl
    · show (evenGrading ℝ ℍ[ℝ] 1).map quatSopEquiv.toLinearMap = evenGrading ℝ ℍ[ℝ] 1
      rw [evenGrading_one, Submodule.map_bot]
      rfl⟩

end EvenSop

/-! ### Stage 1: `(4, 4)` -/

section FourFour

/-- **`quatEvenSuper` is super-Azumaya**: central and graded-simple
(`Superfusion.Gauge.RealReps`), so Wall's map is bijective. -/
noncomputable instance quatEvenSuper_isSuperAzumaya : IsSuperAzumaya quatEvenSuper.grading := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  haveI : IsGradedSimple quatEvenSuper.grading := quatEvenSuper_isGradedSimple
  haveI : IsSuperCentral quatEvenSuper.grading := quatEvenSuper_isSuperCentral
  exact isSuperAzumaya_of_central_simple quatEvenSuper.grading

/-- The two dimensions of the purely-even quaternion grading: `4` even,
`0` odd. -/
theorem quatEvenSuper_grading_finrank :
    Module.finrank ℝ (quatEvenSuper.grading 0) = 4
      ∧ Module.finrank ℝ (quatEvenSuper.grading 1) = 0 := by
  constructor
  · show Module.finrank ℝ (evenGrading ℝ ℍ[ℝ] 0) = 4
    rw [evenGrading_zero, finrank_top]
    exact quatEvenSuper_finrank
  · show Module.finrank ℝ (evenGrading ℝ ℍ[ℝ] 1) = 0
    rw [evenGrading_one, finrank_bot]

/-- The explicit quaternion basis `1, i, j, k` of the even part
`quatEvenSuper.grading 0 = ⊤`, replacing the choice-produced `finBasis`
in the matrix frame of the `(4,4)` branch. -/
noncomputable def quatEvenBasisZero : Module.Basis (Fin 4) ℝ (quatEvenSuper.grading 0) :=
  ((QuaternionAlgebra.basisOneIJK _ _ _ : Module.Basis (Fin 4) ℝ ℍ[ℝ]).map
      (Submodule.topEquiv (M := ℍ[ℝ])).symm).map
    (LinearEquiv.ofEq ⊤ (quatEvenSuper.grading 0)
      (show (⊤ : Submodule ℝ ℍ[ℝ]) = quatEvenSuper.grading 0 from
        (evenGrading_zero ℝ ℍ[ℝ]).symm))

/-- The empty basis of the (trivial) odd part `quatEvenSuper.grading 1 = ⊥`. -/
noncomputable def quatEvenBasisOne : Module.Basis (Fin 0) ℝ (quatEvenSuper.grading 1) :=
  (Module.Basis.empty _ : Module.Basis (Fin 0) ℝ (⊥ : Submodule ℝ ℍ[ℝ])).map
    (LinearEquiv.ofEq ⊥ (quatEvenSuper.grading 1)
      (show (⊥ : Submodule ℝ ℍ[ℝ]) = quatEvenSuper.grading 1 from
        (evenGrading_one ℝ ℍ[ℝ]).symm))

/-- **`(4, 4) ↦ 0`**: `ℍ ᵍ⊗ ℍ ≅ M_{4|0}(ℝ)`, via `quatSopSuperEquiv`
(the sign-free `ℍ ≅ ℍ.sop`), Wall's isomorphism `ℍ ᵍ⊗ ℍ.sop ≅ End(ℍ)`,
and the endomorphism-is-a-matrix-superalgebra equivalence **along the
explicit quaternion basis `1, i, j, k`** (`endMatrixSuperOf`,
`quatEvenBasisZero`) — the matrix frame of this branch is pinned to
explicit basis vectors, with no `finBasis` choice anywhere.  No new
bijectivity argument: central simplicity does all the work.
Table 2 cross-check: `(4,4) ↦ D_0`, `4|0` — **matches**. -/
noncomputable def realFuse_four_four :
    SuperAlgEquiv ((realRep 4).gtensor (realRep 4)) ((realRep (4 + 4)).matrixSuper 4 0) :=
  ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr quatSopSuperEquiv).trans <|
    (wallSuperEquiv quatEvenSuper).trans <|
      endMatrixSuperOf quatEvenSuper quatEvenBasisZero quatEvenBasisOne

end FourFour

/-! ### Bridge: `A ᵍ⊗ (division-tower floor 1) ≅ A.oddDouble`

`Superfusion.Super.OddDoubleTensor.equivGradedTensor` already identifies
`A ᵍ⊗ D_ε ≅ A.oddDouble ε` for the *explicit* rank-one model `D_ε =
AdjoinOdd ε` (M7c-3).  `realRep 1`/`realRep 7` are instead built from the
*tower* model `divisionTower ε 1` (an iterated `OddDouble` of the base
field).  Both are the same abstract superalgebra; the bridge
(`divisionTowerOneEquivAdjoinOdd`) is the evident `e ↦ gen` identification,
bijective by graded simplicity + a dimension count (`2 = 2`), exactly the
`OddDouble.lift`/`hypFusePhi` idiom of `Superfusion.Gauge.RealFuse2`. -/

section OddDoubleBridge

variable {K : Type*} [CommRing K]

/-- The bundled rank-one Clifford superalgebra `D_ε = K[e]/(e^2 = ε)`. -/
noncomputable def adjoinOddSuper (ε : K) : SuperAlgebra K where
  carrier := AdjoinOdd ε
  grading := AdjoinOdd.grading ε

private theorem oddDoubleGtensorEquiv_isHomogeneous (P : SuperAlgebra K) (ε : K) :
    IsHomogeneousHom (tensorGrading P.grading (AdjoinOdd.grading ε))
      (OddDouble.grading P.grading ε) (OddDouble.equivGradedTensor P.grading ε).toAlgHom := by
  intro i z hz
  refine tensorGrading_induction P.grading (AdjoinOdd.grading ε) hz
    (p := fun w => (OddDouble.equivGradedTensor P.grading ε) w
      ∈ OddDouble.grading P.grading ε i) ?_ ?_ ?_ ?_
  · intro j k x y hjk hx hy
    rw [← hjk]
    exact OddDouble.equivGradedTensor_tmul_mem P.grading ε hx hy
  · rw [map_zero]; exact zero_mem _
  · intro u v hu hv; rw [map_add]; exact add_mem hu hv
  · intro c u hu; rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- **M7c-3, bundled**: `A ᵍ⊗ D_ε ≅ A.oddDouble ε`, for any superalgebra
`A` and any `ε`. -/
noncomputable def oddDoubleGtensorEquiv (P : SuperAlgebra K) (ε : K) :
    SuperAlgEquiv (P.gtensor (adjoinOddSuper ε)) (P.oddDouble ε) :=
  ⟨OddDouble.equivGradedTensor P.grading ε, fun i =>
    map_grading_of_bijective (tensorGrading P.grading (AdjoinOdd.grading ε))
      (OddDouble.grading P.grading ε) (OddDouble.equivGradedTensor P.grading ε).toAlgHom
      (oddDoubleGtensorEquiv_isHomogeneous P ε)
      (OddDouble.equivGradedTensor P.grading ε).bijective i⟩

variable (ε : ℝ)

private theorem adjoinOdd_ofId_isHomogeneous :
    IsHomogeneousHom (evenGrading ℝ ℝ) (AdjoinOdd.grading ε)
      (Algebra.ofId ℝ (AdjoinOdd ε)) := by
  intro i x hx
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [Algebra.ofId_apply]
    exact algebraMap_mem_grade_zero (AdjoinOdd.grading ε) x
  · rw [evenGrading_one, Submodule.mem_bot] at hx
    subst hx
    rw [map_zero]
    exact zero_mem _

private theorem adjoinOdd_hconj (a : ℝ) :
    AdjoinOdd.e ε * (Algebra.ofId ℝ (AdjoinOdd ε)) a
      = (Algebra.ofId ℝ (AdjoinOdd ε)) (parityMap (evenGrading ℝ ℝ) a) * AdjoinOdd.e ε := by
  rw [parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top, Algebra.ofId_apply]
  exact (Algebra.commutes a (AdjoinOdd.e ε)).symm

/-- `Cl_{0,1}`/`Cl_{1,0}` (tower model, floor `1`) sent to `D_ε` (rank-one
model), `gen ↦ e`. -/
private noncomputable def divisionTowerOneToAdjoinOddHom :
    (divisionTower ε 1).carrier →ₐ[ℝ] AdjoinOdd ε :=
  OddDouble.lift (evenGrading ℝ ℝ) ε (Algebra.ofId ℝ (AdjoinOdd ε)) (AdjoinOdd.e ε)
    (AdjoinOdd.e_mul_e ε) (adjoinOdd_hconj ε)

private theorem divisionTowerOneToAdjoinOddHom_isHomogeneous :
    IsHomogeneousHom (divisionTower ε 1).grading (AdjoinOdd.grading ε)
      (divisionTowerOneToAdjoinOddHom ε) :=
  OddDouble.lift_isHomogeneous (evenGrading ℝ ℝ) ε (Algebra.ofId ℝ (AdjoinOdd ε)) (AdjoinOdd.e ε)
    (AdjoinOdd.e_mul_e ε) (adjoinOdd_hconj ε) (AdjoinOdd.grading ε) (adjoinOdd_ofId_isHomogeneous ε)
    (AdjoinOdd.e_mem_grading_one ε)

private theorem divisionTowerOneToAdjoinOddHom_bijective (hε : ε ≠ 0) :
    Function.Bijective (divisionTowerOneToAdjoinOddHom ε) := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  haveI : IsGradedSimple (divisionTower ε 1).grading := divisionTower_isGradedSimple hε 1
  haveI : Nontrivial (AdjoinOdd ε) := inferInstance
  have hinj : Function.Injective (divisionTowerOneToAdjoinOddHom ε) :=
    injective_of_isGradedSimple (divisionTower ε 1).grading (AdjoinOdd.grading ε)
      (divisionTowerOneToAdjoinOddHom ε) (divisionTowerOneToAdjoinOddHom_isHomogeneous ε)
  have hdim : Module.finrank ℝ (divisionTower ε 1).carrier
      = Module.finrank ℝ (AdjoinOdd ε) := by
    rw [divisionTower_finrank, AdjoinOdd.finrank_adjoinOdd, pow_one]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (divisionTowerOneToAdjoinOddHom ε).toLinearMap) hdim).mp hinj⟩

/-- **The bridge**: `Cl_{0,1}`/`Cl_{1,0}` (tower model) `≅ D_ε` (rank-one
explicit model). -/
noncomputable def divisionTowerOneEquivAdjoinOdd (hε : ε ≠ 0) :
    SuperAlgEquiv (divisionTower ε 1) (adjoinOddSuper ε) :=
  ⟨AlgEquiv.ofBijective (divisionTowerOneToAdjoinOddHom ε)
      (divisionTowerOneToAdjoinOddHom_bijective ε hε),
    map_grading_of_bijective (divisionTower ε 1).grading (AdjoinOdd.grading ε)
      (divisionTowerOneToAdjoinOddHom ε) (divisionTowerOneToAdjoinOddHom_isHomogeneous ε)
      (divisionTowerOneToAdjoinOddHom_bijective ε hε)⟩

/-- **Combined bridge**: `A ᵍ⊗ (divisionTower ε 1) ≅ A.oddDouble ε`, for
any real superalgebra `A` and any `ε ≠ 0`. -/
noncomputable def oddDoubleGtensorDivisionOneEquiv (P : SuperAlgebra ℝ) (hε : ε ≠ 0) :
    SuperAlgEquiv (P.gtensor (divisionTower ε 1)) (P.oddDouble ε) :=
  ((SuperAlgEquiv.refl P).gtensorCongr (divisionTowerOneEquivAdjoinOdd ε hε)).trans
    (oddDoubleGtensorEquiv P ε)

end OddDoubleBridge

/-! ### Generic helpers for a `QuaternionAlgebra.Basis`

For an algebra hom `q.liftHom : ℍ[R,c₁,c₂,c₃] → A` built from a
`QuaternionAlgebra.Basis`, an element commuting with the two generators
`q.i`, `q.j`, or lying in the degree-`0` piece of a grading containing
`q.i`, `q.j`, automatically does so with (resp. contains) the image of
*every* quaternion — from the explicit formula
`q.lift x = algebraMap x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k`. -/

section QuatBasisHelpers

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {c₁ c₂ c₃ : R}
  (q : QuaternionAlgebra.Basis A c₁ c₂ c₃)

theorem quatBasis_mem_grading_zero {B : ZMod 2 → Submodule R A} [GradedAlgebra B]
    (hi : q.i ∈ B 0) (hj : q.j ∈ B 0) (x : QuaternionAlgebra R c₁ c₂ c₃) :
    q.liftHom x ∈ B 0 := by
  show algebraMap R A x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k ∈ B 0
  have hk : q.k ∈ B 0 := by
    rw [← q.i_mul_j]
    simpa using SetLike.mul_mem_graded hi hj
  exact add_mem (add_mem (add_mem (algebraMap_mem_grade_zero B x.re)
    (Submodule.smul_mem _ _ hi)) (Submodule.smul_mem _ _ hj)) (Submodule.smul_mem _ _ hk)

theorem quatBasis_commute {z : A} (hi : Commute z q.i) (hj : Commute z q.j)
    (x : QuaternionAlgebra R c₁ c₂ c₃) : Commute z (q.liftHom x) := by
  show Commute z (algebraMap R A x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k)
  have hk : Commute z q.k := by rw [← q.i_mul_j]; exact hi.mul_right hj
  have h1 : Commute z (algebraMap R A x.re) := Algebra.commute_algebraMap_right x.re z
  have h2 : Commute z (x.imI • q.i) := by
    rw [Algebra.smul_def]; exact (Algebra.commute_algebraMap_right x.imI z).mul_right hi
  have h3 : Commute z (x.imJ • q.j) := by
    rw [Algebra.smul_def]; exact (Algebra.commute_algebraMap_right x.imJ z).mul_right hj
  have h4 : Commute z (x.imK • q.k) := by
    rw [Algebra.smul_def]; exact (Algebra.commute_algebraMap_right x.imK z).mul_right hk
  exact ((h1.add_right h2).add_right h3).add_right h4

end QuatBasisHelpers

/-! ### The odd-target quaternion/Clifford core

For `ε = ±1`, three explicit anticommuting odd generators `g₁, g₂, g₃`
of `divisionTower ε 3` (embedded, via `OddDouble.inl`, from the tower's
own floors `1`, `2`, `3`): the even products `I = g₁g₂`, `J = g₂g₃` obey
the quaternion relations (`ℍ[R,-1,0,-1]`), and the volume element
`ω = g₁g₂g₃` is odd, squares to `-ε`, and — via `quatBasis_commute` —
**commutes with the whole image of `ℍ`** (the "central volume element"
fact of the file docstring), giving the second (odd) factor's image for
free. -/

section AlgHomHelpers

/-- Pushing a square-to-scalar identity through an algebra hom. -/
private theorem alghom_sq_algebraMap {K B C : Type*} [CommRing K] [Ring B] [Ring C] [Algebra K B]
    [Algebra K C] (f : B →ₐ[K] C) {x : B} {ε : K} (hx : x * x = algebraMap K B ε) :
    f x * f x = algebraMap K C ε := by
  rw [← map_mul, hx, AlgHom.commutes]

/-- Pushing an anticommutation identity through an algebra hom. -/
private theorem alghom_anti {K B C : Type*} [CommRing K] [Ring B] [Ring C] [Algebra K B]
    [Algebra K C] (f : B →ₐ[K] C) {x y : B} (hxy : x * y = -(y * x)) :
    f x * f y = -(f y * f x) := by
  rw [← map_mul, hxy, map_neg, map_mul]

/-- Flipping the two sides of an anticommutation identity. -/
private theorem flip_neg {G : Type*} [SubtractionMonoid G] {a b : G} (h : a = -b) : b = -a := by
  rw [h, neg_neg]

/-- `gen` anticommutes with `inl` of an odd element (the defining relation
of `OddDouble`, in commutator form). -/
private theorem gen_anti_inl_of_odd {K B : Type*} [CommRing K] [Ring B] [Algebra K B]
    (𝒜 : ZMod 2 → Submodule K B) [GradedAlgebra 𝒜] (ε : K) {x : B} (hx : x ∈ 𝒜 1) :
    OddDouble.gen 𝒜 ε * OddDouble.inl 𝒜 ε x = -(OddDouble.inl 𝒜 ε x * OddDouble.gen 𝒜 ε) := by
  rw [OddDouble.gen_mul_inl, parityMap_of_mem_one 𝒜 hx, map_neg, neg_mul]

end AlgHomHelpers

/-! ### Three abstract anticommuting square-root generators

The pure ring-theoretic content of the "quaternion relations from three
Clifford generators, and their central volume element" fact, isolated
from all `OddDouble`/tower bookkeeping: given `a, b, c` in a real algebra
with `a² = b² = c² = ε` and pairwise anticommuting, the even products
`I = ab`, `J = bc` satisfy the quaternion relations `[R,-1,0,-1]`
(`gammaPair_sq`, `gammaTriple_JI`), and the volume element `ω = abc`
**commutes with `a`, `b`, `c`** (`gammaTriple_omega_mul_a/b`, plus the
even-odd commutation `gammaTriple_c_comm_ab`), squaring to `-ε`
(`gammaTriple_omega_sq`). -/

section GammaTriple

variable {A : Type*} [Ring A] [Algebra ℝ A] {a b c : A} {ε : ℝ}

/-- The square of a product of two anticommuting square-root-`ε`
elements. -/
theorem gammaPair_sq (ha : a * a = algebraMap ℝ A ε) (hb : b * b = algebraMap ℝ A ε)
    (hab : a * b = -(b * a)) : (a * b) * (a * b) = algebraMap ℝ A (-(ε * ε)) := by
  rw [show a * b * (a * b) = a * (b * a * b) from by rw [mul_assoc, mul_assoc],
    flip_neg hab, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, mul_assoc, ha, hb, ← map_mul,
    map_neg]

omit [Algebra ℝ A] in
/-- The mixed product `(bc)(ab) = -(ab)(bc)` of two overlapping even
products of anticommuting generators. -/
theorem gammaTriple_JI (hab : a * b = -(b * a)) (hac : a * c = -(c * a))
    (hbc : b * c = -(c * b)) : (b * c) * (a * b) = -((a * b) * (b * c)) := by
  have h1 : (b * c) * (a * b) = b * ((c * a) * b) := by rw [mul_assoc, mul_assoc]
  have h2 : b * ((c * a) * b) = -(b * ((a * c) * b)) := by rw [flip_neg hac, neg_mul, mul_neg]
  have h3 : b * ((a * c) * b) = -(b * (a * (b * c))) := by
    rw [mul_assoc, flip_neg hbc, mul_neg, mul_neg]
  rw [h1, h2, h3, neg_neg, ← mul_assoc, flip_neg hab, neg_mul]

omit [Algebra ℝ A] in
/-- The even product `ab` commutes with `c` (odd-with-even, no sign). -/
theorem gammaTriple_c_comm_ab (hac : a * c = -(c * a)) (hbc : b * c = -(c * b)) :
    c * (a * b) = a * b * c := by
  have h1 : c * (a * b) = (c * a) * b := (mul_assoc c a b).symm
  have h2 : (c * a) * b = -((a * c) * b) := by rw [flip_neg hac, neg_mul]
  have h3 : (a * c) * b = a * (c * b) := mul_assoc a c b
  have h4 : c * b = -(b * c) := flip_neg hbc
  have h5 : a * (-(b * c)) = -(a * (b * c)) := mul_neg a (b * c)
  have h6 : a * (b * c) = a * b * c := (mul_assoc a b c).symm
  rw [h1, h2, h3, h4, h5, h6, neg_neg]

/-- The volume element `abc` squares to `-ε`. -/
theorem gammaTriple_omega_sq (hc : c * c = algebraMap ℝ A ε)
    (hI : (a * b) * (a * b) = algebraMap ℝ A (-1)) (hcomm : c * (a * b) = a * b * c) :
    (a * b * c) * (a * b * c) = algebraMap ℝ A (-ε) := by
  calc a * b * c * (a * b * c) = a * b * (c * (a * b * c)) := mul_assoc (a * b) c (a * b * c)
    _ = a * b * ((c * (a * b)) * c) := congrArg (a * b * ·) (mul_assoc c (a * b) c).symm
    _ = a * b * ((a * b * c) * c) := by rw [hcomm]
    _ = a * b * ((a * b) * (c * c)) := congrArg (a * b * ·) (mul_assoc (a * b) c c)
    _ = (a * b) * (a * b) * (c * c) := (mul_assoc (a * b) (a * b) (c * c)).symm
    _ = algebraMap ℝ A (-1) * algebraMap ℝ A ε := by rw [hI, hc]
    _ = algebraMap ℝ A (-ε) := by rw [← map_mul, neg_mul, one_mul]

/-- `ω · a = ε • (bc)`. -/
theorem gammaTriple_omega_mul_a (ha : a * a = algebraMap ℝ A ε) (hab : a * b = -(b * a))
    (hac : a * c = -(c * a)) : (a * b * c) * a = algebraMap ℝ A ε * (b * c) := by
  have h1 : (a * b * c) * a = (a * b) * (c * a) := mul_assoc (a * b) c a
  have h2 : (a * b) * (c * a) = -((a * b) * (a * c)) := by rw [flip_neg hac, mul_neg]
  have h3a : (a * b) * (a * c) = a * (b * (a * c)) := mul_assoc a b (a * c)
  have h3b : b * (a * c) = (b * a) * c := (mul_assoc b a c).symm
  have h3c : (b * a) * c = -((a * b) * c) := by rw [flip_neg hab, neg_mul]
  have h3d : a * (-((a * b) * c)) = -(a * ((a * b) * c)) := mul_neg a ((a * b) * c)
  have h3e : a * ((a * b) * c) = (a * (a * b)) * c := (mul_assoc a (a * b) c).symm
  have h3f : a * (a * b) = (a * a) * b := (mul_assoc a a b).symm
  have h3g : ((a * a) * b) * c = (a * a) * (b * c) := mul_assoc (a * a) b c
  have h3 : (a * b) * (a * c) = -((a * a) * (b * c)) := by
    rw [h3a, h3b, h3c, h3d, h3e, h3f, h3g]
  rw [h1, h2, h3, neg_neg, ha]

/-- `a · ω = ε • (bc)`. -/
theorem gammaTriple_a_mul_omega (ha : a * a = algebraMap ℝ A ε) :
    a * (a * b * c) = algebraMap ℝ A ε * (b * c) := by
  rw [show a * (a * b * c) = a * (a * b) * c from (mul_assoc a (a * b) c).symm,
    show a * (a * b) = (a * a) * b from (mul_assoc a a b).symm, ha, mul_assoc]

/-- `ω · b = -(ε • (ac))`. -/
theorem gammaTriple_omega_mul_b (hb : b * b = algebraMap ℝ A ε) (hbc : b * c = -(c * b)) :
    (a * b * c) * b = -(algebraMap ℝ A ε * (a * c)) := by
  have h1 : (a * b * c) * b = (a * b) * (c * b) := mul_assoc (a * b) c b
  have h2 : (a * b) * (c * b) = -((a * b) * (b * c)) := by rw [flip_neg hbc, mul_neg]
  have h3a : (a * b) * (b * c) = a * (b * (b * c)) := mul_assoc a b (b * c)
  have h3b : b * (b * c) = (b * b) * c := (mul_assoc b b c).symm
  have h3c : a * ((b * b) * c) = a * (algebraMap ℝ A ε * c) := by rw [hb]
  have h3d : a * (algebraMap ℝ A ε * c) = (a * algebraMap ℝ A ε) * c :=
    (mul_assoc a (algebraMap ℝ A ε) c).symm
  have h3e : a * algebraMap ℝ A ε = algebraMap ℝ A ε * a := (Algebra.commutes ε a).symm
  have h3f : (algebraMap ℝ A ε * a) * c = algebraMap ℝ A ε * (a * c) :=
    mul_assoc (algebraMap ℝ A ε) a c
  have h3 : (a * b) * (b * c) = algebraMap ℝ A ε * (a * c) := by
    rw [h3a, h3b, h3c, h3d, h3e, h3f]
  rw [h1, h2, h3]

/-- `b · ω = -(ε • (ac))`. -/
theorem gammaTriple_b_mul_omega (hb : b * b = algebraMap ℝ A ε) (hab : a * b = -(b * a)) :
    b * (a * b * c) = -(algebraMap ℝ A ε * (a * c)) := by
  have h1 : b * (a * b * c) = (b * (a * b)) * c := (mul_assoc b (a * b) c).symm
  have h2 : b * (a * b) = (b * a) * b := (mul_assoc b a b).symm
  have h3 : (b * a) * b = -((a * b) * b) := by rw [flip_neg hab, neg_mul]
  have h4 : (a * b) * b = a * (b * b) := mul_assoc a b b
  have h5 : a * (b * b) = a * algebraMap ℝ A ε := by rw [hb]
  have h6 : a * algebraMap ℝ A ε = algebraMap ℝ A ε * a := (Algebra.commutes ε a).symm
  have h7 : ((b * a) * b) * c = -(algebraMap ℝ A ε * (a * c)) := by
    rw [h3, h4, h5, h6, neg_mul, mul_assoc]
  rw [h1, h2, h7]

/-- `ω · c = ε • (ab)`. -/
theorem gammaTriple_omega_mul_c (hc : c * c = algebraMap ℝ A ε) :
    (a * b * c) * c = algebraMap ℝ A ε * (a * b) := by
  rw [mul_assoc, hc, ← Algebra.commutes]

omit [Algebra ℝ A] in
/-- `c · ω = ω · c`, from the even-odd commutation `c*(ab) = abc`. -/
theorem gammaTriple_c_mul_omega (hcomm : c * (a * b) = a * b * c) :
    c * (a * b * c) = (a * b * c) * c :=
  ((mul_assoc c (a * b) c).symm).trans (congrArg (· * c) hcomm)

end GammaTriple

section QuatCliffordCore

variable (ε : ℝ)

/-- The tower's own floor-`1` generator, embedded up to floor `3`. -/
noncomputable def cliffG1 : (divisionTower ε 3).carrier :=
  OddDouble.inl (divisionTower ε 2).grading ε
    (OddDouble.inl (divisionTower ε 1).grading ε (OddDouble.gen (evenGrading ℝ ℝ) ε))

/-- The tower's own floor-`2` generator, embedded up to floor `3`. -/
noncomputable def cliffG2 : (divisionTower ε 3).carrier :=
  OddDouble.inl (divisionTower ε 2).grading ε (OddDouble.gen (divisionTower ε 1).grading ε)

/-- The tower's own floor-`3` generator. -/
noncomputable def cliffG3 : (divisionTower ε 3).carrier :=
  OddDouble.gen (divisionTower ε 2).grading ε

/-- The auxiliary floor-`2` element underlying `cliffG1`. -/
private noncomputable def cliffH12 : (divisionTower ε 2).carrier :=
  OddDouble.inl (divisionTower ε 1).grading ε (OddDouble.gen (evenGrading ℝ ℝ) ε)

private theorem cliffG1_eq_inl_cliffH12 :
    cliffG1 ε = OddDouble.inl (divisionTower ε 2).grading ε (cliffH12 ε) := rfl

private theorem gen0_mem_one : OddDouble.gen (evenGrading ℝ ℝ) ε ∈ (divisionTower ε 1).grading 1 :=
  OddDouble.gen_mem_grading (evenGrading ℝ ℝ) ε

private theorem gen1_mem_one :
    OddDouble.gen (divisionTower ε 1).grading ε ∈ (divisionTower ε 2).grading 1 :=
  OddDouble.gen_mem_grading (divisionTower ε 1).grading ε

private theorem cliffH12_mem_one : cliffH12 ε ∈ (divisionTower ε 2).grading 1 :=
  OddDouble.inl_mem_grading (divisionTower ε 1).grading ε (gen0_mem_one ε)

theorem cliffG1_mem_odd : cliffG1 ε ∈ (divisionTower ε 3).grading 1 :=
  OddDouble.inl_mem_grading (divisionTower ε 2).grading ε (cliffH12_mem_one ε)

theorem cliffG2_mem_odd : cliffG2 ε ∈ (divisionTower ε 3).grading 1 :=
  OddDouble.inl_mem_grading (divisionTower ε 2).grading ε (gen1_mem_one ε)

theorem cliffG3_mem_odd : cliffG3 ε ∈ (divisionTower ε 3).grading 1 :=
  OddDouble.gen_mem_grading (divisionTower ε 2).grading ε

/-- `g₃ · g₃ = ε`. -/
theorem cliffG3_sq : cliffG3 ε * cliffG3 ε = algebraMap ℝ (divisionTower ε 3).carrier ε :=
  OddDouble.gen_mul_gen (divisionTower ε 2).grading ε

/-- `g₂ · g₂ = ε`. -/
theorem cliffG2_sq : cliffG2 ε * cliffG2 ε = algebraMap ℝ (divisionTower ε 3).carrier ε :=
  alghom_sq_algebraMap (OddDouble.inl (divisionTower ε 2).grading ε)
    (OddDouble.gen_mul_gen (divisionTower ε 1).grading ε)

/-- `g₁ · g₁ = ε`. -/
theorem cliffG1_sq : cliffG1 ε * cliffG1 ε = algebraMap ℝ (divisionTower ε 3).carrier ε := by
  rw [cliffG1_eq_inl_cliffH12]
  exact alghom_sq_algebraMap (OddDouble.inl (divisionTower ε 2).grading ε)
    (alghom_sq_algebraMap (OddDouble.inl (divisionTower ε 1).grading ε)
      (OddDouble.gen_mul_gen (evenGrading ℝ ℝ) ε))

/-- `g₃ · g₂ = -(g₂ · g₃)`. -/
theorem cliffG3_mul_cliffG2 : cliffG3 ε * cliffG2 ε = -(cliffG2 ε * cliffG3 ε) :=
  gen_anti_inl_of_odd (divisionTower ε 2).grading ε (gen1_mem_one ε)

/-- `g₃ · g₁ = -(g₁ · g₃)`. -/
theorem cliffG3_mul_cliffG1 : cliffG3 ε * cliffG1 ε = -(cliffG1 ε * cliffG3 ε) := by
  rw [cliffG1_eq_inl_cliffH12]
  exact gen_anti_inl_of_odd (divisionTower ε 2).grading ε (cliffH12_mem_one ε)

/-- `g₁ · g₂ = -(g₂ · g₁)`. -/
theorem cliffG1_mul_cliffG2 : cliffG1 ε * cliffG2 ε = -(cliffG2 ε * cliffG1 ε) := by
  rw [cliffG1_eq_inl_cliffH12]
  exact alghom_anti (OddDouble.inl (divisionTower ε 2).grading ε)
    (flip_neg (gen_anti_inl_of_odd (divisionTower ε 1).grading ε (gen0_mem_one ε)))

/-! #### The even products `I = g₁g₂`, `J = g₂g₃`, and the volume element `ω = g₁g₂g₃` -/

/-- `I = g₁g₂`, the first quaternion generator. -/
noncomputable def cliffI : (divisionTower ε 3).carrier := cliffG1 ε * cliffG2 ε

/-- `J = g₂g₃`, the second quaternion generator. -/
noncomputable def cliffJ : (divisionTower ε 3).carrier := cliffG2 ε * cliffG3 ε

/-- `ω = g₁g₂g₃`, the volume element. -/
noncomputable def cliffOmega : (divisionTower ε 3).carrier := cliffG1 ε * cliffG2 ε * cliffG3 ε

theorem cliffI_mem_even : cliffI ε ∈ (divisionTower ε 3).grading 0 := by
  have h := SetLike.mul_mem_graded (cliffG1_mem_odd ε) (cliffG2_mem_odd ε)
  rwa [show (1 + 1 : ZMod 2) = 0 from by decide] at h

theorem cliffJ_mem_even : cliffJ ε ∈ (divisionTower ε 3).grading 0 := by
  have h := SetLike.mul_mem_graded (cliffG2_mem_odd ε) (cliffG3_mem_odd ε)
  rwa [show (1 + 1 : ZMod 2) = 0 from by decide] at h

theorem cliffOmega_mem_odd : cliffOmega ε ∈ (divisionTower ε 3).grading 1 := by
  have h := SetLike.mul_mem_graded (cliffI_mem_even ε) (cliffG3_mem_odd ε)
  rwa [zero_add] at h

variable (hε2 : ε * ε = 1)

include hε2 in
/-- `I² = -1`. -/
theorem cliffI_sq : cliffI ε * cliffI ε = algebraMap ℝ (divisionTower ε 3).carrier (-1) := by
  show cliffG1 ε * cliffG2 ε * (cliffG1 ε * cliffG2 ε) = algebraMap ℝ (divisionTower ε 3).carrier (-1)
  rw [gammaPair_sq (cliffG1_sq ε) (cliffG2_sq ε) (cliffG1_mul_cliffG2 ε), hε2]

include hε2 in
/-- `J² = -1`. -/
theorem cliffJ_sq : cliffJ ε * cliffJ ε = algebraMap ℝ (divisionTower ε 3).carrier (-1) := by
  show cliffG2 ε * cliffG3 ε * (cliffG2 ε * cliffG3 ε) = algebraMap ℝ (divisionTower ε 3).carrier (-1)
  rw [gammaPair_sq (cliffG2_sq ε) (cliffG3_sq ε) (flip_neg (cliffG3_mul_cliffG2 ε)), hε2]

/-- `JI = -(IJ)`: the third quaternion relation. -/
theorem cliffJ_mul_cliffI : cliffJ ε * cliffI ε = -(cliffI ε * cliffJ ε) :=
  gammaTriple_JI (cliffG1_mul_cliffG2 ε) (flip_neg (cliffG3_mul_cliffG1 ε))
    (flip_neg (cliffG3_mul_cliffG2 ε))

/-- `g₃ · I = ω`: the even-odd commutation. -/
theorem cliffG3_comm_cliffI : cliffG3 ε * cliffI ε = cliffOmega ε :=
  gammaTriple_c_comm_ab (flip_neg (cliffG3_mul_cliffG1 ε)) (flip_neg (cliffG3_mul_cliffG2 ε))

include hε2 in
/-- `ω² = -ε`. -/
theorem cliffOmega_sq :
    cliffOmega ε * cliffOmega ε = algebraMap ℝ (divisionTower ε 3).carrier (-ε) :=
  gammaTriple_omega_sq (cliffG3_sq ε) (cliffI_sq ε hε2) (cliffG3_comm_cliffI ε)

/-- **`ω` commutes with `g₁`**. -/
theorem cliffOmega_commute_cliffG1 : Commute (cliffOmega ε) (cliffG1 ε) :=
  (gammaTriple_omega_mul_a (cliffG1_sq ε) (cliffG1_mul_cliffG2 ε)
      (flip_neg (cliffG3_mul_cliffG1 ε))).trans
    (gammaTriple_a_mul_omega (cliffG1_sq ε)).symm

/-- **`ω` commutes with `g₂`**. -/
theorem cliffOmega_commute_cliffG2 : Commute (cliffOmega ε) (cliffG2 ε) :=
  (gammaTriple_omega_mul_b (cliffG2_sq ε) (flip_neg (cliffG3_mul_cliffG2 ε))).trans
    (gammaTriple_b_mul_omega (cliffG2_sq ε) (cliffG1_mul_cliffG2 ε)).symm

/-- **`ω` commutes with `g₃`**. -/
theorem cliffOmega_commute_cliffG3 : Commute (cliffOmega ε) (cliffG3 ε) :=
  (gammaTriple_c_mul_omega (cliffG3_comm_cliffI ε)).symm

/-- **`ω` commutes with `I`**. -/
theorem cliffOmega_commute_cliffI : Commute (cliffOmega ε) (cliffI ε) :=
  (cliffOmega_commute_cliffG1 ε).mul_right (cliffOmega_commute_cliffG2 ε)

/-- **`ω` commutes with `J`**. -/
theorem cliffOmega_commute_cliffJ : Commute (cliffOmega ε) (cliffJ ε) :=
  (cliffOmega_commute_cliffG2 ε).mul_right (cliffOmega_commute_cliffG3 ε)

/-! #### The quaternion basis `ℍ[R,-1,0,-1] → divisionTower ε 3`, `i ↦ I`, `j ↦ J` -/

include hε2 in
/-- The quaternion relations `[R,-1,0,-1]` on `I, J`. -/
noncomputable def cliffQuatBasis :
    QuaternionAlgebra.Basis (divisionTower ε 3).carrier (-1 : ℝ) 0 (-1 : ℝ) where
  i := cliffI ε
  j := cliffJ ε
  k := cliffI ε * cliffJ ε
  i_mul_i := by rw [cliffI_sq ε hε2, Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]
  j_mul_j := by rw [cliffJ_sq ε hε2, Algebra.algebraMap_eq_smul_one]
  i_mul_j := rfl
  j_mul_i := by rw [zero_smul, zero_sub]; exact cliffJ_mul_cliffI ε

include hε2 in
/-- **The quaternion embedding** `ℍ → Cl_{0,3}`/`Cl_{3,0}`, `i ↦ g₁g₂`,
`j ↦ g₂g₃`. -/
noncomputable def cliffPhi : ℍ[ℝ] →ₐ[ℝ] (divisionTower ε 3).carrier := (cliffQuatBasis ε hε2).liftHom

include hε2 in
theorem cliffPhi_isHomogeneous :
    IsHomogeneousHom (evenGrading ℝ ℍ[ℝ]) (divisionTower ε 3).grading (cliffPhi ε hε2) := by
  intro i x hx
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact quatBasis_mem_grading_zero (cliffQuatBasis ε hε2) (cliffI_mem_even ε) (cliffJ_mem_even ε) x
  · rw [evenGrading_one, Submodule.mem_bot] at hx
    subst hx
    rw [map_zero]
    exact zero_mem _

include hε2 in
/-- **`ω` commutes with the whole image of `ℍ`** — the "central volume
element" fact of the file docstring. -/
theorem cliffOmega_commute_cliffPhi (x : ℍ[ℝ]) : Commute (cliffOmega ε) (cliffPhi ε hε2 x) :=
  quatBasis_commute (cliffQuatBasis ε hε2) (cliffOmega_commute_cliffI ε) (cliffOmega_commute_cliffJ ε) x

include hε2 in
private theorem cliffTheta_hconj (x : ℍ[ℝ]) :
    cliffOmega ε * cliffPhi ε hε2 x
      = cliffPhi ε hε2 (parityMap quatEvenSuper.grading x) * cliffOmega ε := by
  show cliffOmega ε * cliffPhi ε hε2 x
      = cliffPhi ε hε2 (parityMap (evenGrading ℝ ℍ[ℝ]) x) * cliffOmega ε
  rw [parityMap_of_mem_zero (evenGrading ℝ ℍ[ℝ]) Submodule.mem_top]
  exact cliffOmega_commute_cliffPhi ε hε2 x

include hε2 in
/-- **The pair fusion map** `ℍ ˆ⊗ Cl_{0,1}/Cl_{1,0} → Cl_{0,3}/Cl_{3,0}`,
via `OddDouble.lift` on the purely-even `quatEvenSuper.oddDouble (-ε)`. -/
noncomputable def cliffTheta :
    (quatEvenSuper.oddDouble (-ε)).carrier →ₐ[ℝ] (divisionTower ε 3).carrier :=
  OddDouble.lift quatEvenSuper.grading (-ε) (cliffPhi ε hε2) (cliffOmega ε) (cliffOmega_sq ε hε2)
    (cliffTheta_hconj ε hε2)

include hε2 in
theorem cliffTheta_isHomogeneous :
    IsHomogeneousHom (OddDouble.grading quatEvenSuper.grading (-ε)) (divisionTower ε 3).grading
      (cliffTheta ε hε2) :=
  OddDouble.lift_isHomogeneous quatEvenSuper.grading (-ε) (cliffPhi ε hε2) (cliffOmega ε)
    (cliffOmega_sq ε hε2) (cliffTheta_hconj ε hε2) (divisionTower ε 3).grading
    (cliffPhi_isHomogeneous ε hε2) (cliffOmega_mem_odd ε)

include hε2 in
theorem cliffTheta_bijective : Function.Bijective (cliffTheta ε hε2) := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hεne : ε ≠ 0 := fun h => by rw [h, mul_zero] at hε2; exact zero_ne_one hε2
  have hnegεne : (-ε) ≠ 0 := neg_ne_zero.mpr hεne
  haveI : IsGradedSimple quatEvenSuper.grading := quatEvenSuper_isGradedSimple
  haveI : IsGradedSimple (OddDouble.grading quatEvenSuper.grading (-ε)) :=
    OddDouble.isGradedSimple quatEvenSuper.grading (-ε) hnegεne
  haveI : Nontrivial (divisionTower ε 3).carrier := divisionTower_nontrivial ε 3
  have hinj : Function.Injective (cliffTheta ε hε2) :=
    injective_of_isGradedSimple (OddDouble.grading quatEvenSuper.grading (-ε))
      (divisionTower ε 3).grading (cliffTheta ε hε2) (cliffTheta_isHomogeneous ε hε2)
  haveI : FiniteDimensional ℝ (quatEvenSuper.oddDouble (-ε)).carrier := by
    show FiniteDimensional ℝ (OddDouble quatEvenSuper.grading (-ε))
    infer_instance
  have hdim : Module.finrank ℝ (quatEvenSuper.oddDouble (-ε)).carrier
      = Module.finrank ℝ (divisionTower ε 3).carrier := by
    show Module.finrank ℝ (ℍ[ℝ] × ℍ[ℝ]) = Module.finrank ℝ (divisionTower ε 3).carrier
    rw [Module.finrank_prod, Quaternion.finrank_eq_four, divisionTower_finrank]
    norm_num
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (cliffTheta ε hε2).toLinearMap) hdim).mp hinj⟩

include hε2 in
/-- **The bundled pair fusion**: `ℍ.oddDouble(-ε) ≅ Cl_{0,3}/Cl_{3,0}` (the
target floor `3` of the `ε`-tower). -/
noncomputable def cliffThetaEquiv :
    SuperAlgEquiv (quatEvenSuper.oddDouble (-ε)) (divisionTower ε 3) :=
  ⟨AlgEquiv.ofBijective (cliffTheta ε hε2) (cliffTheta_bijective ε hε2),
    map_grading_of_bijective (OddDouble.grading quatEvenSuper.grading (-ε)) (divisionTower ε 3).grading
      (cliffTheta ε hε2) (cliffTheta_isHomogeneous ε hε2) (cliffTheta_bijective ε hε2)⟩

end QuatCliffordCore

/-! ### `(4, 7)` and `(4, 1)`, and their transposes -/

section QuatOddPairs

/-- Transport `A.oddDouble` along an equality of `ε`'s (a plain value
equality, not a `defeq` — needed since `ℝ`'s `Neg` is not
kernel-reducible). -/
noncomputable def oddDouble_congr_eps {P : SuperAlgebra ℝ} {ε ε' : ℝ} (h : ε = ε') :
    SuperAlgEquiv (P.oddDouble ε) (P.oddDouble ε') := by
  subst h; exact SuperAlgEquiv.refl _

/-- **`(4, 7) ↦ 3`**: `ℍ ᵍ⊗ Cl_{1,0} ≅ M_{1|0}(Cl_{0,3})`. `Cl_{0,3}`'s even
part is `ℍ` and its volume element `ω` (odd, central, `ω² = 1`) supplies
the `Cl_{1,0}` factor. Table 2 cross-check: `(4,7) ↦ D_3`, `1|0` —
**matches**. -/
noncomputable def realFuse_four_seven :
    SuperAlgEquiv ((realRep 4).gtensor (realRep 7)) ((realRep (4 + 7)).matrixSuper 1 0) :=
  (oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper one_ne_zero).trans <|
    (oddDouble_congr_eps (show (1 : ℝ) = -(-1 : ℝ) from by norm_num)).trans <|
      (cliffThetaEquiv (-1 : ℝ) (show (-1 : ℝ) * (-1 : ℝ) = 1 from by norm_num)).trans
        (matrixSuperOne (divisionTower (-1 : ℝ) 3)).symm

/-- **`(4, 1) ↦ 5`**: `ℍ ᵍ⊗ Cl_{0,1} ≅ M_{1|0}(Cl_{3,0})`. Same
construction, `ε = 1` (`Cl_{3,0}`'s volume element `ω² = -1`). Table 2
cross-check: `(4,1) ↦ D_5`, `1|0` — **matches**. -/
noncomputable def realFuse_four_one :
    SuperAlgEquiv ((realRep 4).gtensor (realRep 1)) ((realRep (4 + 1)).matrixSuper 1 0) :=
  (oddDoubleGtensorDivisionOneEquiv (-1 : ℝ) quatEvenSuper (by norm_num)).trans <|
    (cliffThetaEquiv (1 : ℝ) (show (1 : ℝ) * (1 : ℝ) = 1 from by norm_num)).trans
      (matrixSuperOne (divisionTower (1 : ℝ) 3)).symm

/-- **`(7, 4) ↦ 3`**, for free from the Koszul braiding. -/
noncomputable def realFuse_seven_four :
    SuperAlgEquiv ((realRep 7).gtensor (realRep 4)) ((realRep (7 + 4)).matrixSuper 1 0) :=
  realFuse_transpose realFuse_four_seven

/-- **`(1, 4) ↦ 5`**, for free from the Koszul braiding. -/
noncomputable def realFuse_one_four :
    SuperAlgEquiv ((realRep 1).gtensor (realRep 4)) ((realRep (1 + 4)).matrixSuper 1 0) :=
  realFuse_transpose realFuse_four_one

end QuatOddPairs

end Superfusion

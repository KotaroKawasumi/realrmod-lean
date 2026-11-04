/-
Superfusion / Gauge / RealFuseSpecWrap2

M15 semantic-bridge GROUP C (continued): the `ε = -1` **wrap pairs**,
i.e. the branches of `RealFuse4` whose Clifford floors sum past the Bott
floor `4` and therefore route through the *composite* floor-`4`
certificate `divisionTowerNegFourQuatSuper` (`RealFuse4:213`) rather
than through the field-generic gamma-matrix certificate
`towerFourQuatSuper` that `RealFuseSpecWrap` uses.

**Landed here**

* `realFuseMatrix_1_3 : realFuseMatrix 1 3 = !![…]` (16 × 16),
* `realFuseMatrix_2_2 : realFuseMatrix 2 2 = !![…]` (16 × 16),
* `realFuseMatrix_3_1 : realFuseMatrix 3 1 = !![…]` — the Koszul
  transpose of `(1,3)`, discharged from the forward spec through
  `RealFuseSpecTranspose.realFuseMatrix_3_1_of_forward`.

**The machinery gap that this file closes.**  The previous wave stopped
at the `ε = -1` wraps because `divisionTowerNegFourQuatSuper` is built
*by reduction* out of three inverse-direction pieces, and no evaluation
lemmas existed for them.  All of that is now generic and reusable:

1. `negE` (this file) names the inner peel
   `Cl_{0,3} ≅ ℍ ᵍ⊗ Cl_{1,0}` exactly as it is spelled inside the
   certificate, and `negE_of_left` / `negE_of_right` turn a *forward*
   `cliffThetaEquiv` value on an `OddDouble.mk` into a `negE` value on a
   tensor.  Both inverses (`cliffThetaEquiv.symm`,
   `oddDoubleGtensorDivisionOneEquiv.symm`) are crossed with
   `AlgEquiv.symm_apply_eq` only (`ct_symm`, `od_symm`); no inverse
   formula is ever unfolded.  `nEv_0 … nEv_7` are the eight values on
   the floor-`3` tower frame.
2. `absorbTail_apply`: the certificate's tail
   `ℍ ᵍ⊗ M_{1|1}(ℝ) → M_{1|1}(ℍ ᵍ⊗ ℝ) → M_{1|1}(ℍ)` is *entrywise
   scalar multiplication*, `q ᵍ⊗ M ↦ (M r s) • q`.  Every Koszul sign in
   `matrixSuperGtensorRight` dies against the evenness of `ℍ`; the
   supporting fact is `comm_even_tmul` — the braiding is sign-free when
   the **left** factor is even, for an *arbitrary* (not necessarily
   homogeneous) right factor, proved by splitting the right factor into
   `evenPart + oddPart`.
3. `hcv_11 / hcv_1g / hcv_g1 / hcv_gg`: the four values of
   `gtensorComm ; hypFuse` on the generator tensors of
   `Cl_{1,0} ᵍ⊗ Cl_{0,1}`.  Exactly one of the four (`hcv_gg`) carries a
   Koszul sign — it is the *only* sign in the whole certificate.
4. `negCert_of`: the assembly.  From a `negE` value `w ↦ q ᵍ⊗ u` and a
   hyperbolic value for `(u, v)`, entry `(r, s)` of
   `divisionTowerNegFourQuatSuper (towerFuse (-1) 3 1 (w ᵍ⊗ v))` is
   `M r s • q`.  `cert_11 / cert_g1 / cert_1g / cert_gg` package the four
   shapes as `diaM` / `offM` literals, and `nqv4_0 … nqv4_15` /
   `nqc4_0 … nqc4_15` are the sixteen certificate values, first as
   `M_{1|1}(ℍ)` monomials and then in the target frame
   `matrixSuperBasis quatBasis 1 1`.  These sixteen are the `ε = -1`
   mirror of `RealFuseSpecWrap`'s `qv4_*` / `qc4_*` and are what the
   remaining wrap branches need.

**Instance-diamond notes** (these dominated the debugging time):

* The three carrier gaps `(P.oddDouble ε).carrier` vs `OddDouble …`,
  `(divisionTower ε 1).carrier` vs `OddDouble (base ℝ).grading ε`, and
  `(P.gtensor Q).carrier` vs `𝒜 ᵍ⊗[ℝ] ℬ` are definitional but *not*
  instance-transparent, so any `Neg`/`SMul`/`One` written at one of them
  is invisible to `rw`/`map_neg`/`map_smul` at the other.  Three cures,
  in order of preference: (i) prefer the *bundled-typed* constant
  (`q1 ε`, never `OddDouble.gen (base ℝ).grading ε`) — this alone fixed
  `hcv_gg`; (ii) keep every quaternion sign as a **literal** of `ℍ[ℝ]`
  (`n1`, `nqi`, `nqj`, `nqk` from `RealFuseSpecWrap`) so that `map_neg`
  only ever sees `ℍ[ℝ]`'s own `Neg` — this is what makes `ctf_1 … ctf_5`
  one-liners; (iii) finish with `exact` / `refine … (map_neg _ _) …`
  (default transparency) instead of `rw`.
* `SuperAlgEquiv.gtensorCongr_tmul` and `gtensorAssoc_tmul` state their
  tensors inside `show … from` wrappers (`have this := …; this`), which
  block `rw` when chained.  The fix is to restate each step at one
  uniform, hand-written spelling by `have sᵢ : … := hᵢ` (a defeq check)
  before rewriting into the `rfl`-proved composite equation — see
  `negCert_of`.
* Private declarations of the sibling spec files are reached with
  Mathlib's `open private … from …`; nothing is copied, and no
  `RealFuseSpec*` file is edited.

**Not landed** (needs the matrix-ampliation tail): `(2,3)`, `(3,3)`,
`(5,5)`, `(5,6)`.  Each of the four is
`towerFuse ; towerFuse.symm ; (certificate ᵍ⊗ id) ; matrixSuperGtensor ;
(inner fuse).matrixSuper ; matrixSuperComp`, and everything up to and
including `(certificate ᵍ⊗ id)` is already available above
(`nqv4_*`, resp. `RealFuseSpecWrap`'s `qv4_*` for the two `ε = +1`
cases).  What is still missing is only the *tail*: the generic
single-entry lemmas are provided here
(`single_mem_matrixGradingA'`, `msg_single'`, `matrixSuperMap_single'`,
`matrixSuperComp_single'`), so what remains for each branch is (a) the
`ℍ ᵍ⊗ Cl_{0,1}` / `ℍ ᵍ⊗ Cl_{0,2}` value dictionary of the inner fuse
(`realFuse_four_one` / `realFuse_four_two`, whose generator values are
already `private` in `RealFuseSpecQuat` as `fuse41_tmul_one/gen`),
(b) resolving `msg_single'`'s column sign `sgn (sumParity 1 1 s * |b|)`
at the four concrete `(s, |b|)` — best folded into the quaternion
literal rather than carried as a `ℤˣ`-scalar — and (c) the
`collapseIndexEquiv 1 1 p q` index table.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7).
-/
import Superfusion.Gauge.RealFuseSpecWrap
import Superfusion.Gauge.RealFuseSpecQuat
import Superfusion.Gauge.RealFuseSpecPeel
import Superfusion.Gauge.RealFuseSpecTranspose

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Superfusion

open Module TensorProduct GradedTensorProduct Quaternion

open private q1 q1_def mem_q1 tb1_0 tb1_1
  tb3_0 tb3_1 tb3_2 tb3_3 tb3_4 tb3_5 tb3_6 tb3_7
  tb4_0 tb4_1 tb4_2 tb4_3 tb4_4 tb4_5 tb4_6 tb4_7
  tb4_8 tb4_9 tb4_10 tb4_11 tb4_12 tb4_13 tb4_14 tb4_15
  qF1 qF2 qF3 qF4 qF5 qF6 qF7
  prodF3F7 prodF6F7 prodF5F7
  cliffPhi_e0 cliffPhi_e1 cliffPhi_e2 cliffPhi_e3
  cliffOmega_val cliffThetaEquiv_mk_left cliffThetaEquiv_mk_right
  oddDoubleGDOne_tmul_one oddDoubleGDOne_tmul_gen oddDouble_congr_eps_mk
  mkA_neg mkB_neg smul_mkA smul_mkB
  towerFuse_basis toMatrix_of_coord matrixSuperBasis_repr
  quatBasis_zero quatBasis_one quatBasis_two quatBasis_three
  from Superfusion.Gauge.RealFuseSpecQuat

open private qi qj qk n1 nqi nqj nqk offM diaM diaM_one
  quatBasis_0 quatBasis_1 quatBasis_2 quatBasis_3
  neg_one_q neg_qi neg_qj neg_qk
  dstQ_0 dstQ_1 dstQ_2 dstQ_3 dstQ_4 dstQ_5 dstQ_6 dstQ_7
  dstQ_8 dstQ_9 dstQ_10 dstQ_11 dstQ_12 dstQ_13 dstQ_14 dstQ_15
  smul_dstQ sb_p_0 sb_p_1 sb_p_2 sb_p_3 sb_m_0 sb_m_1 sb_m_2 sb_m_3
  from Superfusion.Gauge.RealFuseSpecWrap

open private fuse41_tmul_one fuse41_tmul_gen fuse_h11
  from Superfusion.Gauge.RealFuseSpecQuat

open private hypE' hypF' hypE'_mul_hypF' hypFuse_val_one_one
  hypFuse_val_one_gen hypFuse_val_gen_one hypFuse_val_gen_gen
  from Superfusion.Gauge.RealFuseSpecPeel

/-! ### Generic helpers -/

/-- `SuperAlgEquiv.refl` acts as the identity (definitional). -/
private theorem superRefl_apply (P : SuperAlgebra ℝ) (x : P.carrier) :
    (SuperAlgEquiv.refl P).toAlgEquiv x = x := rfl

/-- Scalars pull out of the right slot of `ᵍ⊗ₜ`. -/
private theorem gtmul_smul_right {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A)
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (x : A) (c : ℝ) (y : B) :
    (x ᵍ⊗ₜ[ℝ] (c • y) : 𝒜 ᵍ⊗[ℝ] ℬ) = c • (x ᵍ⊗ₜ[ℝ] y : 𝒜 ᵍ⊗[ℝ] ℬ) := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ (x ⊗ₜ[ℝ] (c • y)) = _
  rw [TensorProduct.tmul_smul, map_smul]

/-- **The braiding is sign-free when the left factor is even** — for an
arbitrary (not necessarily homogeneous) right factor, by splitting it
into its even and odd parts. -/
private theorem comm_even_tmul (P Q : SuperAlgebra ℝ) {x : P.carrier}
    (hx : x ∈ P.grading 0) (y : Q.carrier) :
    (gtensorComm P Q).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y)
      = GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ y x := by
  obtain ⟨a, ha, b, hb, rfl⟩ :
      ∃ a, a ∈ Q.grading 0 ∧ ∃ b, b ∈ Q.grading 1 ∧ a + b = y :=
    ⟨evenPart Q.grading y, evenPart_mem _ _, oddPart Q.grading y,
      oddPart_mem _ _, evenPart_add_oddPart _ _⟩
  have h0 := gtensorComm_tmul_of_mem P Q hx ha
  have h1 := gtensorComm_tmul_of_mem P Q hx hb
  rw [mul_zero, uzpow_zero, one_smul] at h0 h1
  have hs : GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x
        (a + b)
      = (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x a
          : (P.gtensor Q).carrier)
        + GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x b :=
    gtmul_add P.grading Q.grading x a b
  have hs' : GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ
        (a + b) x
      = (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ a x
          : (Q.gtensor P).carrier)
        + GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ b x :=
    add_gtmul Q.grading P.grading a b x
  calc (gtensorComm P Q).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x (a + b))
      = (gtensorComm P Q).toAlgEquiv
          ((GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x a
              : (P.gtensor Q).carrier)
            + GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x b)
        := by rw [hs]
    _ = (gtensorComm P Q).toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x a)
          + (gtensorComm P Q).toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x b)
        := map_add _ _ _
    _ = (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ a x
            : (Q.gtensor P).carrier)
          + GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ b x
        := by rw [h0, h1]; rfl
    _ = _ := hs'.symm

/-- The right unitor on `x ᵍ⊗ t` for a scalar `t`. -/
private theorem unitorRight_tmul (P : SuperAlgebra ℝ) (x : P.carrier)
    (t : ℝ) :
    (gtensorUnitorRight P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ x t) = t • x := by
  have h1 : (gtensorUnitorRight P).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := P.grading)
        (ℬ := (SuperAlgebra.base ℝ).grading) ℝ x (1 : ℝ)) = x := by
    have h := gunitorRightHom_tmul P.grading x (1 : ℝ)
    rw [map_one, mul_one] at h
    exact h
  have ht : GradedTensorProduct.tmul (𝒜 := P.grading)
        (ℬ := (SuperAlgebra.base ℝ).grading) ℝ x t
      = (t • GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ x (1 : ℝ) :
          (P.gtensor (SuperAlgebra.base ℝ)).carrier) := by
    rw [← gtmul_smul_right]
    congr 1
    show t = t * (1 : ℝ)
    rw [mul_one]
  calc (gtensorUnitorRight P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (SuperAlgebra.base ℝ).grading) ℝ x t)
      = (gtensorUnitorRight P).toAlgEquiv
          (t • GradedTensorProduct.tmul (𝒜 := P.grading)
            (ℬ := (SuperAlgebra.base ℝ).grading) ℝ x (1 : ℝ) :
            (P.gtensor (SuperAlgebra.base ℝ)).carrier) := by rw [ht]
    _ = t • (gtensorUnitorRight P).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := P.grading)
            (ℬ := (SuperAlgebra.base ℝ).grading) ℝ x (1 : ℝ)) := map_smul _ _ _
    _ = t • x := by rw [h1]

/-! ### The absorb tail of the `ε = -1` certificate

`ℍ ᵍ⊗ M_{1|1}(ℝ) ≅ M_{1|1}(ℍ ᵍ⊗ ℝ) ≅ M_{1|1}(ℍ)`: entrywise scalar
multiplication.  Every Koszul sign in `matrixSuperGtensorRight` is
killed by the evenness of the quaternion factor. -/

/-- The middle map of `matrixSuperGtensorRight`, on a pure tensor with
an **even** right factor: no column twist. -/
private theorem msgt_tmul_even (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)
    {q : quatEvenSuper.carrier} (hq : q ∈ quatEvenSuper.grading 0)
    (r s : Fin 1 ⊕ Fin 1) :
    (matrixSuperGtensor (SuperAlgebra.base ℝ) quatEvenSuper 1 1).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading)
          (ℬ := quatEvenSuper.grading) ℝ M q) r s
      = GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := quatEvenSuper.grading) ℝ (M r s) q := by
  have h := matrixTensorSuperHom_apply_of_mem (sumParity 1 1)
    (SuperAlgebra.base ℝ).grading quatEvenSuper.grading M hq r s
  rw [mul_zero, sgn_zero, Units.val_one, one_smul] at h
  exact h

/-- **The absorb tail**, entrywise: `q ᵍ⊗ M ↦ (M r s) • q`. -/
private theorem absorbTail_apply {q : quatEvenSuper.carrier}
    (hq : q ∈ quatEvenSuper.grading 0)
    (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (r s : Fin 1 ⊕ Fin 1) :
    ((matrixSuperGtensorRight quatEvenSuper (SuperAlgebra.base ℝ) 1 1).trans
          ((gtensorUnitorRight quatEvenSuper).matrixSuper 1 1)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ q M) r s
      = (M r s) • q := by
  have hA := comm_even_tmul quatEvenSuper
    ((SuperAlgebra.base ℝ).matrixSuper 1 1) hq M
  have hB := msgt_tmul_even M hq r s
  have hC := gtensorComm_tmul_of_mem (SuperAlgebra.base ℝ) quatEvenSuper
    (mem_evenGrading_zero ℝ ℝ (M r s)) hq
  rw [mul_zero, uzpow_zero, one_smul] at hC
  have hD := unitorRight_tmul quatEvenSuper q (M r s)
  have e1 : ((matrixSuperGtensorRight quatEvenSuper (SuperAlgebra.base ℝ) 1 1).trans
          ((gtensorUnitorRight quatEvenSuper).matrixSuper 1 1)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ q M) r s
      = (gtensorUnitorRight quatEvenSuper).toAlgEquiv
          ((gtensorComm (SuperAlgebra.base ℝ) quatEvenSuper).toAlgEquiv
            ((matrixSuperGtensor (SuperAlgebra.base ℝ) quatEvenSuper 1 1).toAlgEquiv
              ((gtensorComm quatEvenSuper
                  ((SuperAlgebra.base ℝ).matrixSuper 1 1)).toAlgEquiv
                (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
                  (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ q M))
              r s)) := rfl
  rw [hA, hB, hC, hD] at e1
  exact e1

/-! ### The two halves of the composite certificate

`divisionTowerNegFourQuatSuper` is
`(towerFuse (-1) 3 1).symm ; (negE ᵍ⊗ id) ; assoc ; (id ᵍ⊗ (comm ; hypFuse))
 ; absorbTail`.  Only `negE` (the inverse of the odd-double/`cliffTheta`
identification of `Cl_{0,3}` with `ℍ ᵍ⊗ Cl_{1,0}`) and the four
`comm ; hypFuse` values have to be pinned; everything else is generic. -/

private theorem negOneSq : (-1 : ℝ) * (-1 : ℝ) = 1 := by norm_num

/-- The `ε = -1` peel: `Cl_{0,3} ≅ ℍ ᵍ⊗ Cl_{1,0}`, as spelled inside
`divisionTowerNegFourQuatSuper`. -/
private noncomputable def negE :
    SuperAlgEquiv (divisionTower (-1 : ℝ) 3)
      (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 1)) :=
  ((cliffThetaEquiv (-1 : ℝ) negOneSq).symm.trans
      (oddDouble_congr_eps (show (-(-1 : ℝ)) = 1 from by norm_num))).trans
    (oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper one_ne_zero).symm

/-- `cliffThetaEquiv`'s inverse from a forward value. -/
private theorem ct_symm {x : (quatEvenSuper.oddDouble (-(-1 : ℝ))).carrier}
    {y : (divisionTower (-1 : ℝ) 3).carrier}
    (h : (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv x = y) :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).symm.toAlgEquiv y = x := by
  show ((cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv).symm y = x
  rw [AlgEquiv.symm_apply_eq]
  exact h.symm

/-- `oddDoubleGtensorDivisionOneEquiv`'s inverse from a forward value. -/
private theorem od_symm
    {x : (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 1)).carrier}
    {y : (quatEvenSuper.oddDouble (1 : ℝ)).carrier}
    (h : (oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper
        one_ne_zero).toAlgEquiv x = y) :
    (oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper
        one_ne_zero).symm.toAlgEquiv y = x := by
  show ((oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper
      one_ne_zero).toAlgEquiv).symm y = x
  rw [AlgEquiv.symm_apply_eq]
  exact h.symm

/-- The generic shape of a `negE` value: from a forward `cliffTheta`
value on a left/right `OddDouble.mk`, read off the tensor. -/
private theorem negE_of_left {x : quatEvenSuper.carrier}
    {y : (divisionTower (-1 : ℝ) 3).carrier}
    (h : (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
      (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) x 0) = y) :
    negE.toAlgEquiv y
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x
          (1 : (divisionTower (1 : ℝ) 1).carrier) := by
  have h1 := ct_symm h
  have h2 := oddDouble_congr_eps_mk (P := quatEvenSuper)
    (show (-(-1 : ℝ)) = 1 from by norm_num) x 0
  have h3 := od_symm (oddDoubleGDOne_tmul_one quatEvenSuper (1 : ℝ) one_ne_zero x)
  have e1 : negE.toAlgEquiv y
      = (oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper
            one_ne_zero).symm.toAlgEquiv
          ((oddDouble_congr_eps (show (-(-1 : ℝ)) = 1 from by norm_num)).toAlgEquiv
            ((cliffThetaEquiv (-1 : ℝ) negOneSq).symm.toAlgEquiv y)) := rfl
  rw [h1, h2, h3] at e1
  exact e1

private theorem negE_of_right {x : quatEvenSuper.carrier}
    {y : (divisionTower (-1 : ℝ) 3).carrier}
    (h : (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
      (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) 0 x) = y) :
    negE.toAlgEquiv y
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ x (q1 (1 : ℝ)) := by
  have h1 := ct_symm h
  have h2 := oddDouble_congr_eps_mk (P := quatEvenSuper)
    (show (-(-1 : ℝ)) = 1 from by norm_num) 0 x
  have h3 := od_symm (oddDoubleGDOne_tmul_gen quatEvenSuper (1 : ℝ) one_ne_zero x)
  have e1 : negE.toAlgEquiv y
      = (oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper
            one_ne_zero).symm.toAlgEquiv
          ((oddDouble_congr_eps (show (-(-1 : ℝ)) = 1 from by norm_num)).toAlgEquiv
            ((cliffThetaEquiv (-1 : ℝ) negOneSq).symm.toAlgEquiv y)) := rfl
  rw [h1, h2, h3] at e1
  exact e1

/-! ### The eight `negE` values on the floor-`3` tower frame -/

/-- `ct x := cliffThetaEquiv (-1) _` applied to the `OddDouble` frame,
with the quaternion entries written as the literals of
`RealFuseSpecWrap` (so that no `Neg` of the *bundled* carrier ever
appears — `map_neg` only ever sees `ℍ[ℝ]`'s own `Neg`). -/
private theorem ctf_0 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) (1 : ℍ[ℝ]) 0)
      = towerBasis (-1 : ℝ) 3 0 := by
  rw [cliffThetaEquiv_mk_left, map_one, tb3_0]

private theorem ctf_3 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) qi 0)
      = towerBasis (-1 : ℝ) 3 3 := by
  rw [cliffThetaEquiv_mk_left, ← quatBasis_1, cliffPhi_e1, tb3_3]

private theorem ctf_6 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) qj 0)
      = towerBasis (-1 : ℝ) 3 6 := by
  rw [cliffThetaEquiv_mk_left, ← quatBasis_2, cliffPhi_e2, tb3_6]

private theorem ctf_5 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) nqk 0)
      = towerBasis (-1 : ℝ) 3 5 := by
  rw [cliffThetaEquiv_mk_left, ← neg_qk, ← quatBasis_3, map_neg, cliffPhi_e3,
    tb3_5, neg_one_smul, neg_neg]

private theorem ctf_7 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) 0 (1 : ℍ[ℝ]))
      = towerBasis (-1 : ℝ) 3 7 := by
  rw [cliffThetaEquiv_mk_right, map_one, one_mul, cliffOmega_val, tb3_7]

private theorem ctf_1 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) 0 nqj)
      = towerBasis (-1 : ℝ) 3 1 := by
  rw [cliffThetaEquiv_mk_right, ← neg_qj, ← quatBasis_2, map_neg, cliffPhi_e2,
    cliffOmega_val, neg_mul, prodF6F7 (-1 : ℝ) negOneSq, neg_neg, tb3_1]

private theorem ctf_4 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) 0 nqi)
      = towerBasis (-1 : ℝ) 3 4 := by
  rw [cliffThetaEquiv_mk_right, ← neg_qi, ← quatBasis_1, map_neg, cliffPhi_e1,
    cliffOmega_val, neg_mul, prodF3F7 (-1 : ℝ) negOneSq, neg_neg, tb3_4]

private theorem ctf_2 :
    (cliffThetaEquiv (-1 : ℝ) negOneSq).toAlgEquiv
        (OddDouble.mk quatEvenSuper.grading (-(-1 : ℝ)) 0 nqk)
      = towerBasis (-1 : ℝ) 3 2 := by
  rw [cliffThetaEquiv_mk_right, ← neg_qk, ← quatBasis_3, map_neg, cliffPhi_e3,
    cliffOmega_val, neg_mul, smul_mul_assoc, prodF5F7 (-1 : ℝ) negOneSq,
    neg_one_smul, neg_neg, tb3_2]

private theorem nEv_0 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 0)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (1 : ℍ[ℝ])
        (1 : (divisionTower (1 : ℝ) 1).carrier) := negE_of_left ctf_0

private theorem nEv_3 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 3)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ qi
        (1 : (divisionTower (1 : ℝ) 1).carrier) := negE_of_left ctf_3

private theorem nEv_6 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 6)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ qj
        (1 : (divisionTower (1 : ℝ) 1).carrier) := negE_of_left ctf_6

private theorem nEv_5 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 5)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ nqk
        (1 : (divisionTower (1 : ℝ) 1).carrier) := negE_of_left ctf_5

private theorem nEv_7 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 7)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (1 : ℍ[ℝ])
        (q1 (1 : ℝ)) := negE_of_right ctf_7

private theorem nEv_1 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 1)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ nqj
        (q1 (1 : ℝ)) := negE_of_right ctf_1

private theorem nEv_4 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 4)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ nqi
        (q1 (1 : ℝ)) := negE_of_right ctf_4

private theorem nEv_2 : negE.toAlgEquiv (towerBasis (-1 : ℝ) 3 2)
    = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ nqk
        (q1 (1 : ℝ)) := negE_of_right ctf_2

/-! ### The hyperbolic half: `comm ; hypFuse` on the four generator
tensors -/

private theorem mem_one_dt (ε : ℝ) :
    (1 : (divisionTower ε 1).carrier) ∈ (divisionTower ε 1).grading 0 :=
  SetLike.one_mem_graded _

/-- `u = 1`, `v = 1`. -/
private theorem hcv_11 :
    hypFuse.toAlgEquiv
        ((gtensorComm (divisionTower (1 : ℝ) 1)
            (divisionTower (-1 : ℝ) 1)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
            (1 : (divisionTower (1 : ℝ) 1).carrier)
            (1 : (divisionTower (-1 : ℝ) 1).carrier)))
      = (1 : ((SuperAlgebra.base ℝ).matrixSuper 1 1).carrier) := by
  have hc := gtensorComm_tmul_of_mem (divisionTower (1 : ℝ) 1)
    (divisionTower (-1 : ℝ) 1) (mem_one_dt 1) (mem_one_dt (-1))
  rw [mul_zero, uzpow_zero, one_smul] at hc
  rw [hc]
  exact hypFuse_val_one_one

/-- `u = 1`, `v = gen`. -/
private theorem hcv_1g :
    hypFuse.toAlgEquiv
        ((gtensorComm (divisionTower (1 : ℝ) 1)
            (divisionTower (-1 : ℝ) 1)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
            (1 : (divisionTower (1 : ℝ) 1).carrier) (q1 (-1 : ℝ))))
      = hypE' := by
  have hc := gtensorComm_tmul_of_mem (divisionTower (1 : ℝ) 1)
    (divisionTower (-1 : ℝ) 1) (mem_one_dt 1) (mem_q1 (-1 : ℝ))
  rw [mul_zero, uzpow_zero, one_smul] at hc
  rw [hc]
  exact hypFuse_val_gen_one

/-- `u = gen`, `v = 1`. -/
private theorem hcv_g1 :
    hypFuse.toAlgEquiv
        ((gtensorComm (divisionTower (1 : ℝ) 1)
            (divisionTower (-1 : ℝ) 1)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (q1 (1 : ℝ))
            (1 : (divisionTower (-1 : ℝ) 1).carrier)))
      = hypF' := by
  have hc := gtensorComm_tmul_of_mem (divisionTower (1 : ℝ) 1)
    (divisionTower (-1 : ℝ) 1) (mem_q1 (1 : ℝ)) (mem_one_dt (-1))
  rw [zero_mul, uzpow_zero, one_smul] at hc
  rw [hc]
  exact hypFuse_val_one_gen

/-- `u = gen`, `v = gen`: the only Koszul sign of the whole certificate. -/
private theorem hcv_gg :
    hypFuse.toAlgEquiv
        ((gtensorComm (divisionTower (1 : ℝ) 1)
            (divisionTower (-1 : ℝ) 1)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (q1 (1 : ℝ))
            (q1 (-1 : ℝ))))
      = -(hypE' * hypF') := by
  have hc := gtensorComm_tmul_of_mem (divisionTower (1 : ℝ) 1)
    (divisionTower (-1 : ℝ) 1) (mem_q1 (1 : ℝ)) (mem_q1 (-1 : ℝ))
  rw [mul_one, uzpow_one, Units.smul_def, Units.val_neg, Units.val_one,
    neg_smul, one_smul] at hc
  rw [hc]
  refine Eq.trans (map_neg _ _) ?_
  exact congrArg (fun z => -z) hypFuse_val_gen_gen

/-! ### The certificate, assembled -/

/-- **The `ε = -1` floor-`4` certificate, evaluated**: from a `negE`
value `w ↦ q ᵍ⊗ u` and the hyperbolic value of `(u, v)`, the entry
`(r, s)` of the image of `towerFuse (-1) 3 1 (w ᵍ⊗ v)` is `M r s • q`.
All Koszul signs of the tail vanish (`q` is even); the only sign of the
whole certificate is the one inside `hcv_gg`. -/
private theorem negCert_of {q : quatEvenSuper.carrier}
    (hq : q ∈ quatEvenSuper.grading 0)
    {w : (divisionTower (-1 : ℝ) 3).carrier}
    {u : (divisionTower (1 : ℝ) 1).carrier}
    (v : (divisionTower (-1 : ℝ) 1).carrier)
    {M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ}
    (hw : negE.toAlgEquiv w
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ q u)
    (hM : hypFuse.toAlgEquiv
        ((gtensorComm (divisionTower (1 : ℝ) 1)
            (divisionTower (-1 : ℝ) 1)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ u v)) = M)
    (r s : Fin 1 ⊕ Fin 1) :
    divisionTowerNegFourQuatSuper.toAlgEquiv
        ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w v)) r s
      = M r s • q := by
  have hcancel : (towerFuse (-1 : ℝ) 3 1).symm.toAlgEquiv
      ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w v))
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w v :=
    AlgEquiv.symm_apply_apply _ _
  have hB := SuperAlgEquiv.gtensorCongr_tmul negE
    (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1)) w v
  rw [hw, superRefl_apply] at hB
  have hC := gtensorAssoc_tmul quatEvenSuper (divisionTower (1 : ℝ) 1)
    (divisionTower (-1 : ℝ) 1) q u v
  have hD := SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl quatEvenSuper)
    ((gtensorComm (divisionTower (1 : ℝ) 1)
      (divisionTower (-1 : ℝ) 1)).trans hypFuse) q
    (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
      (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ u v)
  have hDt : ((gtensorComm (divisionTower (1 : ℝ) 1)
        (divisionTower (-1 : ℝ) 1)).trans hypFuse).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
        (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ u v) = M := hM
  rw [superRefl_apply, hDt] at hD
  -- restate the three steps at a single, uniform spelling so that they chain
  have s1 : (negE.gtensorCongr
        (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w v)
      = GradedTensorProduct.tmul
          (𝒜 := (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 1)).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ q u) v := hB
  have s2 : (gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 1)
        (divisionTower (-1 : ℝ) 1)).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 1)).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ q u) v)
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((divisionTower (1 : ℝ) 1).gtensor
            (divisionTower (-1 : ℝ) 1)).grading) ℝ q
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ u v) := hC
  have s3 : ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
        ((gtensorComm (divisionTower (1 : ℝ) 1)
          (divisionTower (-1 : ℝ) 1)).trans hypFuse)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((divisionTower (1 : ℝ) 1).gtensor
            (divisionTower (-1 : ℝ) 1)).grading) ℝ q
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ u v))
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((SuperAlgebra.base ℝ).matrixSuper 1 1).grading) ℝ q M := hD
  have e1 : divisionTowerNegFourQuatSuper.toAlgEquiv
        ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w v))
      = ((matrixSuperGtensorRight quatEvenSuper (SuperAlgebra.base ℝ) 1 1).trans
            ((gtensorUnitorRight quatEvenSuper).matrixSuper 1 1)).toAlgEquiv
          (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
              ((gtensorComm (divisionTower (1 : ℝ) 1)
                (divisionTower (-1 : ℝ) 1)).trans hypFuse)).toAlgEquiv
            ((gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 1)
                (divisionTower (-1 : ℝ) 1)).toAlgEquiv
              ((negE.gtensorCongr
                  (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
                ((towerFuse (-1 : ℝ) 3 1).symm.toAlgEquiv
                  ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
                    (GradedTensorProduct.tmul
                      (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
                      (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w v)))))) :=
    rfl
  rw [hcancel, s1, s2, s3] at e1
  rw [e1]
  exact absorbTail_apply hq M r s


/-! ### Matrix shapes and the sixteen certificate values -/

/-- The quaternions are purely even. -/
private theorem hq_all (q : ℍ[ℝ]) : q ∈ quatEvenSuper.grading 0 := by
  show q ∈ (evenGrading ℝ ℍ[ℝ]) 0
  exact mem_evenGrading_zero ℝ ℍ[ℝ] q

private theorem mk_dia {N : (quatEvenSuper.matrixSuper 1 1).carrier} {a b : ℍ[ℝ]}
    (h00 : N (Sum.inl 0) (Sum.inl 0) = a)
    (h01 : N (Sum.inl 0) (Sum.inr 0) = 0)
    (h10 : N (Sum.inr 0) (Sum.inl 0) = 0)
    (h11 : N (Sum.inr 0) (Sum.inr 0) = b) :
    N = diaM a b := by
  refine Matrix.ext fun r c => ?_
  have h1 : ∀ x : Fin 1, x = 0 := fun x => Subsingleton.elim x 0
  rcases r with r | r <;> rcases c with c | c <;> rw [h1 r, h1 c] <;>
    simp [diaM, h00, h01, h10, h11] <;> try rfl

private theorem mk_off {N : (quatEvenSuper.matrixSuper 1 1).carrier} {a b : ℍ[ℝ]}
    (h00 : N (Sum.inl 0) (Sum.inl 0) = 0)
    (h01 : N (Sum.inl 0) (Sum.inr 0) = a)
    (h10 : N (Sum.inr 0) (Sum.inl 0) = b)
    (h11 : N (Sum.inr 0) (Sum.inr 0) = 0) :
    N = offM a b := by
  refine Matrix.ext fun r c => ?_
  have h1 : ∀ x : Fin 1, x = 0 := fun x => Subsingleton.elim x 0
  rcases r with r | r <;> rcases c with c | c <;> rw [h1 r, h1 c] <;>
    simp [offM, h00, h01, h10, h11] <;> try rfl

private theorem neg_n1 : -n1 = (1 : ℍ[ℝ]) := by rw [← neg_one_q, neg_neg]
private theorem neg_nqi : -nqi = qi := by rw [← neg_qi, neg_neg]
private theorem neg_nqj : -nqj = qj := by rw [← neg_qj, neg_neg]
private theorem neg_nqk : -nqk = qk := by rw [← neg_qk, neg_neg]

/-- The identity of `M_{1|1}(ℝ)`, restated at the bare matrix type so
that `Matrix.one_apply` is usable. -/
private theorem hcv_11' :
    hypFuse.toAlgEquiv
        ((gtensorComm (divisionTower (1 : ℝ) 1)
            (divisionTower (-1 : ℝ) 1)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
            (1 : (divisionTower (1 : ℝ) 1).carrier)
            (1 : (divisionTower (-1 : ℝ) 1).carrier)))
      = (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) := hcv_11

private theorem eI_ll :
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (Sum.inl 0) (Sum.inl 0)
      = (1 : ℝ) := by simp
private theorem eI_lr :
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (Sum.inl 0) (Sum.inr 0)
      = (0 : ℝ) := by simp
private theorem eI_rl :
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (Sum.inr 0) (Sum.inl 0)
      = (0 : ℝ) := by simp
private theorem eI_rr :
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (Sum.inr 0) (Sum.inr 0)
      = (1 : ℝ) := by simp

private theorem eE_ll : hypE' (Sum.inl 0) (Sum.inl 0) = (0 : ℝ) := by
  simp [hypE']
private theorem eE_lr : hypE' (Sum.inl 0) (Sum.inr 0) = (1 : ℝ) := by
  simp [hypE']
private theorem eE_rl : hypE' (Sum.inr 0) (Sum.inl 0) = (-1 : ℝ) := by
  simp [hypE']
private theorem eE_rr : hypE' (Sum.inr 0) (Sum.inr 0) = (0 : ℝ) := by
  simp [hypE']

private theorem eF_ll : hypF' (Sum.inl 0) (Sum.inl 0) = (0 : ℝ) := by
  simp [hypF']
private theorem eF_lr : hypF' (Sum.inl 0) (Sum.inr 0) = (1 : ℝ) := by
  simp [hypF']
private theorem eF_rl : hypF' (Sum.inr 0) (Sum.inl 0) = (1 : ℝ) := by
  simp [hypF']
private theorem eF_rr : hypF' (Sum.inr 0) (Sum.inr 0) = (0 : ℝ) := by
  simp [hypF']

private theorem eG_ll : (-(hypE' * hypF')) (Sum.inl 0) (Sum.inl 0) = (-1 : ℝ) := by
  rw [hypE'_mul_hypF']; simp
private theorem eG_lr : (-(hypE' * hypF')) (Sum.inl 0) (Sum.inr 0) = (0 : ℝ) := by
  rw [hypE'_mul_hypF']; simp
private theorem eG_rl : (-(hypE' * hypF')) (Sum.inr 0) (Sum.inl 0) = (0 : ℝ) := by
  rw [hypE'_mul_hypF']; simp
private theorem eG_rr : (-(hypE' * hypF')) (Sum.inr 0) (Sum.inr 0) = (1 : ℝ) := by
  rw [hypE'_mul_hypF']; simp

/-- `u = 1`, `v = 1`: the diagonal shape. -/
private theorem cert_11 {q : ℍ[ℝ]} {w : (divisionTower (-1 : ℝ) 3).carrier}
    (hw : negE.toAlgEquiv w
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ q
          (1 : (divisionTower (1 : ℝ) 1).carrier)) :
    divisionTowerNegFourQuatSuper.toAlgEquiv
        ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w
            (1 : (divisionTower (-1 : ℝ) 1).carrier)))
      = diaM q q := by
  refine mk_dia ?_ ?_ ?_ ?_
  · rw [negCert_of (hq_all q) _ hw hcv_11', eI_ll]; exact one_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_11', eI_lr]; exact zero_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_11', eI_rl]; exact zero_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_11', eI_rr]; exact one_smul ℝ q

/-- `u = gen`, `v = 1`: the antidiagonal shape, sign-free. -/
private theorem cert_g1 {q : ℍ[ℝ]} {w : (divisionTower (-1 : ℝ) 3).carrier}
    (hw : negE.toAlgEquiv w
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ q (q1 (1 : ℝ))) :
    divisionTowerNegFourQuatSuper.toAlgEquiv
        ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w
            (1 : (divisionTower (-1 : ℝ) 1).carrier)))
      = offM q q := by
  refine mk_off ?_ ?_ ?_ ?_
  · rw [negCert_of (hq_all q) _ hw hcv_g1, eF_ll]; exact zero_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_g1, eF_lr]; exact one_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_g1, eF_rl]; exact one_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_g1, eF_rr]; exact zero_smul ℝ q

/-- `u = 1`, `v = gen`: the antidiagonal shape with a lower sign. -/
private theorem cert_1g {q : ℍ[ℝ]} {w : (divisionTower (-1 : ℝ) 3).carrier}
    (hw : negE.toAlgEquiv w
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ q
          (1 : (divisionTower (1 : ℝ) 1).carrier)) :
    divisionTowerNegFourQuatSuper.toAlgEquiv
        ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w (q1 (-1 : ℝ))))
      = offM q (-q) := by
  refine mk_off ?_ ?_ ?_ ?_
  · rw [negCert_of (hq_all q) _ hw hcv_1g, eE_ll]; exact zero_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_1g, eE_lr]; exact one_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_1g, eE_rl]; exact neg_one_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_1g, eE_rr]; exact zero_smul ℝ q

/-- `u = gen`, `v = gen`: the diagonal shape with an upper sign (this is
where the single Koszul sign of the certificate lands). -/
private theorem cert_gg {q : ℍ[ℝ]} {w : (divisionTower (-1 : ℝ) 3).carrier}
    (hw : negE.toAlgEquiv w
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ q (q1 (1 : ℝ))) :
    divisionTowerNegFourQuatSuper.toAlgEquiv
        ((towerFuse (-1 : ℝ) 3 1).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ w (q1 (-1 : ℝ))))
      = diaM (-q) q := by
  refine mk_dia ?_ ?_ ?_ ?_
  · rw [negCert_of (hq_all q) _ hw hcv_gg, eG_ll]; exact neg_one_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_gg, eG_lr]; exact zero_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_gg, eG_rl]; exact zero_smul ℝ q
  · rw [negCert_of (hq_all q) _ hw hcv_gg, eG_rr]; exact one_smul ℝ q

/-! ### The source dictionary at floor `4` and the sixteen values -/

private theorem hs_0 : towerBasis (-1 : ℝ) 4 0
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 0)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 0 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_1 : towerBasis (-1 : ℝ) 4 1
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 1)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 1 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_2 : towerBasis (-1 : ℝ) 4 2
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 2)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 2 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_3 : towerBasis (-1 : ℝ) 4 3
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 3)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 3 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_4 : towerBasis (-1 : ℝ) 4 4
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 4)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 4 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_5 : towerBasis (-1 : ℝ) 4 5
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 5)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 5 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_6 : towerBasis (-1 : ℝ) 4 6
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 6)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 6 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_7 : towerBasis (-1 : ℝ) 4 7
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 7)
          (1 : (divisionTower (-1 : ℝ) 1).carrier)) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 7 0
  rw [tb1_0 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_8 : towerBasis (-1 : ℝ) 4 8
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 0)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 0 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_9 : towerBasis (-1 : ℝ) 4 9
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 1)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 1 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_10 : towerBasis (-1 : ℝ) 4 10
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 2)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 2 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_11 : towerBasis (-1 : ℝ) 4 11
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 3)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 3 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_12 : towerBasis (-1 : ℝ) 4 12
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 4)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 4 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_13 : towerBasis (-1 : ℝ) 4 13
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 5)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 5 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_14 : towerBasis (-1 : ℝ) 4 14
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 6)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 6 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem hs_15 : towerBasis (-1 : ℝ) 4 15
    = (towerFuse (-1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (towerBasis (-1 : ℝ) 3 7)
          (q1 (-1 : ℝ))) := by
  have h := towerFuse_basis (-1 : ℝ) 3 1 7 1
  rw [tb1_1 (-1 : ℝ)] at h
  exact h.symm

private theorem nqv4_0 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 0)
      = diaM 1 1 := by
  rw [hs_0]
  exact cert_11 nEv_0

private theorem nqv4_1 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 1)
      = offM nqj nqj := by
  rw [hs_1]
  exact cert_g1 nEv_1

private theorem nqv4_2 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 2)
      = offM nqk nqk := by
  rw [hs_2]
  exact cert_g1 nEv_2

private theorem nqv4_3 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 3)
      = diaM qi qi := by
  rw [hs_3]
  exact cert_11 nEv_3

private theorem nqv4_4 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 4)
      = offM nqi nqi := by
  rw [hs_4]
  exact cert_g1 nEv_4

private theorem nqv4_5 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 5)
      = diaM nqk nqk := by
  rw [hs_5]
  exact cert_11 nEv_5

private theorem nqv4_6 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 6)
      = diaM qj qj := by
  rw [hs_6]
  exact cert_11 nEv_6

private theorem nqv4_7 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 7)
      = offM 1 1 := by
  rw [hs_7]
  exact cert_g1 nEv_7

private theorem nqv4_8 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 8)
      = offM 1 n1 := by
  rw [hs_8]
  rw [← neg_one_q]
  exact cert_1g nEv_0

private theorem nqv4_9 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 9)
      = diaM qj nqj := by
  rw [hs_9]
  rw [← neg_nqj]
  exact cert_gg nEv_1

private theorem nqv4_10 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 10)
      = diaM qk nqk := by
  rw [hs_10]
  rw [← neg_nqk]
  exact cert_gg nEv_2

private theorem nqv4_11 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 11)
      = offM qi nqi := by
  rw [hs_11]
  rw [← neg_qi]
  exact cert_1g nEv_3

private theorem nqv4_12 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 12)
      = diaM qi nqi := by
  rw [hs_12]
  rw [← neg_nqi]
  exact cert_gg nEv_4

private theorem nqv4_13 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 13)
      = offM nqk qk := by
  rw [hs_13]
  rw [← neg_nqk]
  exact cert_1g nEv_5

private theorem nqv4_14 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 14)
      = offM qj nqj := by
  rw [hs_14]
  rw [← neg_qj]
  exact cert_1g nEv_6

private theorem nqv4_15 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 15)
      = diaM n1 1 := by
  rw [hs_15]
  rw [← neg_one_q]
  exact cert_gg nEv_7

/-! ### The certificate values in target-frame coordinates -/

private theorem nqc4_0 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 0)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  rw [smul_dstQ (1 : ℝ) dstQ_0, smul_dstQ (1 : ℝ) dstQ_12, sb_p_0]
  exact nqv4_0

private theorem nqc4_1 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 1)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_6, smul_dstQ (-1 : ℝ) dstQ_10, sb_m_2]
  exact nqv4_1

private theorem nqc4_2 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 2)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_7, smul_dstQ (-1 : ℝ) dstQ_11, sb_m_3]
  exact nqv4_2

private theorem nqc4_3 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 3)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  rw [smul_dstQ (1 : ℝ) dstQ_1, smul_dstQ (1 : ℝ) dstQ_13, sb_p_1]
  exact nqv4_3

private theorem nqc4_4 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 4)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_5, smul_dstQ (-1 : ℝ) dstQ_9, sb_m_1]
  exact nqv4_4

private theorem nqc4_5 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 5)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_3, smul_dstQ (-1 : ℝ) dstQ_15, sb_m_3]
  exact nqv4_5

private theorem nqc4_6 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 6)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  rw [smul_dstQ (1 : ℝ) dstQ_2, smul_dstQ (1 : ℝ) dstQ_14, sb_p_2]
  exact nqv4_6

private theorem nqc4_7 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 7)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  rw [smul_dstQ (1 : ℝ) dstQ_4, smul_dstQ (1 : ℝ) dstQ_8, sb_p_0]
  exact nqv4_7

private theorem nqc4_8 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 8)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  rw [smul_dstQ (1 : ℝ) dstQ_4, smul_dstQ (-1 : ℝ) dstQ_8, sb_p_0, sb_m_0]
  exact nqv4_8

private theorem nqc4_9 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 9)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  rw [smul_dstQ (1 : ℝ) dstQ_2, smul_dstQ (-1 : ℝ) dstQ_14, sb_p_2, sb_m_2]
  exact nqv4_9

private theorem nqc4_10 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 10)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  rw [smul_dstQ (1 : ℝ) dstQ_3, smul_dstQ (-1 : ℝ) dstQ_15, sb_p_3, sb_m_3]
  exact nqv4_10

private theorem nqc4_11 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 11)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  rw [smul_dstQ (1 : ℝ) dstQ_5, smul_dstQ (-1 : ℝ) dstQ_9, sb_p_1, sb_m_1]
  exact nqv4_11

private theorem nqc4_12 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 12)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  rw [smul_dstQ (1 : ℝ) dstQ_1, smul_dstQ (-1 : ℝ) dstQ_13, sb_p_1, sb_m_1]
  exact nqv4_12

private theorem nqc4_13 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 13)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_7, smul_dstQ (1 : ℝ) dstQ_11, sb_m_3, sb_p_3]
  exact nqv4_13

private theorem nqc4_14 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 14)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  rw [smul_dstQ (1 : ℝ) dstQ_6, smul_dstQ (-1 : ℝ) dstQ_10, sb_p_2, sb_m_2]
  exact nqv4_14

private theorem nqc4_15 :
    divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 15)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_0, smul_dstQ (1 : ℝ) dstQ_12, sb_m_0, sb_p_0]
  exact nqv4_15

/-! ### The matrix-ampliation tail (for the `(2,3)` / `(3,3)` wraps)

`M_{1|1}(ℍ) ᵍ⊗ Cl_{0,b} ≅ M_{1|1}(ℍ ᵍ⊗ Cl_{0,b}) ≅ M_{1|1}(M_{p|q}(D))
≅ M_{…}(D)`.  Generic, and stated on single-entry matrices — the only
sign is `matrixSuperGtensor`'s column twist, which is folded into the
quaternion literal rather than carried as a `ℤˣ`-scalar. -/

private theorem zmod2_fold : ∀ x y j : ZMod 2, x + y + j + x + y = j := by
  decide

/-- A single-entry matrix with homogeneous entry is homogeneous. -/
private theorem single_mem_matrixGradingA' {n' : Type*} [Fintype n']
    [DecidableEq n'] (π : n' → ZMod 2) {A : Type*} [Ring A] [Algebra ℝ A]
    (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] {jd : ZMod 2} {d : A}
    (hd : d ∈ 𝒜 jd) (r s : n') :
    Matrix.single r s d ∈ matrixGradingA π 𝒜 (π r + π s + jd) := by
  intro a b
  by_cases hab : r = a ∧ s = b
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.single_apply_same,
      show π r + π s + jd + π r + π s = jd from zmod2_fold (π r) (π s) jd]
    exact hd
  · rw [Matrix.single_apply_of_ne (h := hab)]
    exact zero_mem _

/-- `matrixSuperGtensor` on a single-entry matrix tensor a homogeneous
element: the column sign appears. -/
private theorem msg_single' (Q P : SuperAlgebra ℝ) (p' q' : ℕ)
    (u v : Fin p' ⊕ Fin q') (x : Q.carrier) {jb : ZMod 2} {b : P.carrier}
    (hb : b ∈ P.grading jb) :
    (matrixSuperGtensor Q P p' q').toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity p' q') Q.grading)
          (ℬ := P.grading) ℝ (Matrix.single u v x) b)
      = ((sgn (sumParity p' q' v * jb) : ℤˣ) : ℤ) •
          Matrix.single u v
            (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ
              x b) := by
  refine Matrix.ext fun a c => ?_
  show matrixTensorSuperHom (sumParity p' q') Q.grading P.grading
      (GradedTensorProduct.tmul
        (𝒜 := matrixGradingA (sumParity p' q') Q.grading)
        (ℬ := P.grading) ℝ (Matrix.single u v x) b) a c
    = (((sgn (sumParity p' q' v * jb) : ℤˣ) : ℤ) •
        Matrix.single u v
          (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := P.grading) ℝ
            x b)) a c
  rw [matrixTensorSuperHom_apply_of_mem (sumParity p' q') Q.grading
    P.grading (Matrix.single u v x) hb a c, Matrix.smul_apply]
  by_cases hac : u = a ∧ v = c
  · obtain ⟨rfl, rfl⟩ := hac
    rw [Matrix.single_apply_same, Matrix.single_apply_same]
  · rw [Matrix.single_apply_of_ne (h := hac),
      Matrix.single_apply_of_ne (h := hac), zero_gtmul, smul_zero,
      smul_zero]

/-- Entrywise functoriality on a single-entry matrix. -/
private theorem matrixSuperMap_single' {P Q : SuperAlgebra ℝ}
    (e : SuperAlgEquiv P Q) (p' q' : ℕ) (r s : Fin p' ⊕ Fin q')
    (z : P.carrier) :
    (e.matrixSuper p' q').toAlgEquiv (Matrix.single r s z)
      = Matrix.single r s (e.toAlgEquiv z) := by
  show e.toAlgEquiv.mapMatrix (Matrix.single r s z) = _
  rw [AlgEquiv.mapMatrix_apply, Matrix.map_single]

/-- `matrixSuperComp` on a nested single-entry matrix. -/
private theorem matrixSuperComp_single' (P : SuperAlgebra ℝ)
    (p' q' p q : ℕ) (u v : Fin p' ⊕ Fin q') (r s : Fin p ⊕ Fin q)
    (z : P.carrier) :
    (matrixSuperComp P p' q' p q).toAlgEquiv
        (Matrix.single u v (Matrix.single r s z))
      = Matrix.single (collapseIndexEquiv p' q' p q (u, r))
          (collapseIndexEquiv p' q' p q (v, s)) z := by
  show Matrix.reindexAlgEquiv ℝ _ (collapseIndexEquiv p' q' p q)
      ((Matrix.compAlgEquiv _ _ _ ℝ)
        (Matrix.single u v (Matrix.single r s z)))
    = _
  rw [Matrix.compAlgEquiv_apply, Matrix.comp_single_single]
  simp [Matrix.reindex_apply]

/-! ### The `(1,3)` branch -/

private theorem col13_0 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 0
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 0))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 0]
  exact nqc4_0

private theorem col13_1 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 1
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 1))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 1]
  exact nqc4_2

private theorem col13_2 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 2)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 2
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 2))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 2]
  exact nqc4_4

private theorem col13_3 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 3)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 3
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 3))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 3]
  exact nqc4_6

private theorem col13_4 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 4)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 4) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 4
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 4))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 4]
  exact nqc4_8

private theorem col13_5 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 5)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 5) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 5
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 5))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 5]
  exact nqc4_10

private theorem col13_6 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 6)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 6) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 6
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 6))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 6]
  exact nqc4_12

private theorem col13_7 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 7)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 7) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 0 7
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 0)
          (towerBasis (-1 : ℝ) 3 7))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 0 7]
  exact nqc4_14

private theorem col13_8 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 8)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 8
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 0
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 0))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 0]
  exact nqc4_1

private theorem col13_9 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 9)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 9
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 1
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 1))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 1]
  exact nqc4_3

private theorem col13_10 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 10)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 10
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 2
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 2))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 2]
  exact nqc4_5

private theorem col13_11 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 11)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 11
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 3
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 3))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 3]
  exact nqc4_7

private theorem col13_12 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 12)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 12
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 4) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 4
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 4))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 4]
  exact nqc4_9

private theorem col13_13 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 13)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 13
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 5) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 5
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 5))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 5]
  exact nqc4_11

private theorem col13_14 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 14)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 14
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 6) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 6
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 6))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 6]
  exact nqc4_13

private theorem col13_15 :
    ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 15)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 1)
        (B := divisionTower (-1 : ℝ) 3)
        (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 15
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 7) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) 1 7
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 1 3).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
          (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ (towerBasis (-1 : ℝ) 1 1)
          (towerBasis (-1 : ℝ) 3 7))) = _
  rw [towerFuse_basis (-1 : ℝ) 1 3 1 7]
  exact nqc4_15

set_option maxRecDepth 40000 in
/-- **Deliverable `(1,3)`**: the `ε = -1` wrap through the Bott floor,
via the composite certificate `divisionTowerNegFourQuatSuper`. -/
theorem realFuseMatrix_1_3 :
    realFuseMatrix 1 3
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
           0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
           0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
           0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
           0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] := by
  have hcol : ∀ c : Fin 16,
      ((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) c)
        = (![1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, -1, -1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![0, 7, 5, 2, 4, 3, 1, 6, 6, 1, 3, 4, 2, 5, 7, 0] c)
          + (![1, -1, -1, 1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, 1, 1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![12, 11, 9, 14, 8, 15, 13, 10, 10, 13, 15, 8, 14, 9, 11, 12] c) := by
    intro c
    fin_cases c
    · exact col13_0
    · exact col13_1
    · exact col13_2
    · exact col13_3
    · exact col13_4
    · exact col13_5
    · exact col13_6
    · exact col13_7
    · exact col13_8
    · exact col13_9
    · exact col13_10
    · exact col13_11
    · exact col13_12
    · exact col13_13
    · exact col13_14
    · exact col13_15
  have key : ∀ i j : Fin 16,
      ((matrixSuperBasis quatBasis 1 1).repr
          (((towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper).toAlgEquiv
            (gtensorBasis (A := divisionTower (-1 : ℝ) 1) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 1) (towerBasis (-1 : ℝ) 3) j))) i
        = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
             0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
             0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
             0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
             0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
             0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
             0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
             1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
             0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
             0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    rw [hcol j, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, Basis.repr_self_apply,
      Basis.repr_self_apply, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  refine Matrix.ext fun i j => ?_
  rw [realFuseMatrix_apply]
  exact key i j

/-! ### The `(2,2)` branch -/

private theorem col22_0 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 0)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 0 0
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 0))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 0 0]
  exact nqc4_0

private theorem col22_1 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 1)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 0 1
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 1))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 0 1]
  exact nqc4_4

private theorem col22_2 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 2)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 0 2
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 2))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 0 2]
  exact nqc4_8

private theorem col22_3 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 3)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 0 3
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 0)
          (towerBasis (-1 : ℝ) 2 3))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 0 3]
  exact nqc4_12

private theorem col22_4 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 4)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 1 0
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 0))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 1 0]
  exact nqc4_1

private theorem col22_5 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 5)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 1 1
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 1))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 1 1]
  exact nqc4_5

private theorem col22_6 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 6)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 1 2
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 2))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 1 2]
  exact nqc4_9

private theorem col22_7 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 7)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 1 3
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 1)
          (towerBasis (-1 : ℝ) 2 3))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 1 3]
  exact nqc4_13

private theorem col22_8 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 8)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 8
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 2 0
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 0))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 2 0]
  exact nqc4_2

private theorem col22_9 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 9)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 9
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 2 1
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 1))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 2 1]
  exact nqc4_6

private theorem col22_10 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 10)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 10
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 2 2
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 2))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 2 2]
  exact nqc4_10

private theorem col22_11 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 11)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 11
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 2 3
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 2)
          (towerBasis (-1 : ℝ) 2 3))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 2 3]
  exact nqc4_14

private theorem col22_12 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 12)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 12
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 0) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 3 0
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 0))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 3 0]
  exact nqc4_3

private theorem col22_13 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 13)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 13
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 1) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 3 1
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 1))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 3 1]
  exact nqc4_7

private theorem col22_14 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 14)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 14
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 2) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 3 2
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 2))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 3 2]
  exact nqc4_11

private theorem col22_15 :
    ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 15)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (-1 : ℝ) 2)
        (B := divisionTower (-1 : ℝ) 2)
        (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 15
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 3) :=
    gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) 3 3
  rw [hsrc]
  show divisionTowerNegFourQuatSuper.toAlgEquiv
      ((towerFuse (-1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 2).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (towerBasis (-1 : ℝ) 2 3)
          (towerBasis (-1 : ℝ) 2 3))) = _
  rw [towerFuse_basis (-1 : ℝ) 2 2 3 3]
  exact nqc4_15

set_option maxRecDepth 40000 in
/-- **Deliverable `(2,2)`**: the `ε = -1` wrap through the Bott floor,
via the composite certificate `divisionTowerNegFourQuatSuper`. -/
theorem realFuseMatrix_2_2 :
    realFuseMatrix 2 2
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
           0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
           0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
           0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] := by
  have hcol : ∀ c : Fin 16,
      ((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
          (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) c)
        = (![1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, 1, 1, 1, -1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![0, 5, 4, 1, 6, 3, 2, 7, 7, 2, 3, 6, 1, 4, 5, 0] c)
          + (![1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![12, 9, 8, 13, 10, 15, 14, 11, 11, 14, 15, 10, 13, 8, 9, 12] c) := by
    intro c
    fin_cases c
    · exact col22_0
    · exact col22_1
    · exact col22_2
    · exact col22_3
    · exact col22_4
    · exact col22_5
    · exact col22_6
    · exact col22_7
    · exact col22_8
    · exact col22_9
    · exact col22_10
    · exact col22_11
    · exact col22_12
    · exact col22_13
    · exact col22_14
    · exact col22_15
  have key : ∀ i j : Fin 16,
      ((matrixSuperBasis quatBasis 1 1).repr
          (((towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper).toAlgEquiv
            (gtensorBasis (A := divisionTower (-1 : ℝ) 2) (B := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1 : ℝ) 2) (towerBasis (-1 : ℝ) 2) j))) i
        = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
             0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
             0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
             0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
             0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
             0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
             1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
             0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
             0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    rw [hcol j, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, Basis.repr_self_apply,
      Basis.repr_self_apply, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  refine Matrix.ext fun i j => ?_
  rw [realFuseMatrix_apply]
  exact key i j

/-- **Deliverable `(3,1)`**: the Koszul transpose of `(1,3)`, discharged
from the forward spec by `RealFuseSpecTranspose`'s conditional theorem. -/
theorem realFuseMatrix_3_1 :
    realFuseMatrix 3 1
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
           0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
           0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] :=
  realFuseMatrix_3_1_of_forward realFuseMatrix_1_3

end Superfusion

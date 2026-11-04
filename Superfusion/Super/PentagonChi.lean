/-
Superfusion / Super / PentagonChi

Milestone M7d-5b-4-iii(c), part 8'': **the pentagon comparison scalar
χ(a,b,c,d)** and the parity cocycle identity `δp = 0`.

All five pentagon edges (`edgeT12, edgeT24, alignedEdgeT45, edgeT13,
edgeT35`) are landed.  Composing them along the two `K₅` paths from
vertex 1 (`quadRoute1`) to vertex 5 (`alignedRoute5`) —

  `pathA := edgeT35 * edgeT13`            (via vertex 3, `quadRoute3`)
  `pathB := alignedEdgeT45 * (edgeT24 * edgeT12)`
                                            (via vertices 2 and 4)

— produces two homogeneous invertible intertwiners of the SAME pair
`(quadRoute1, alignedRoute5)`, of a priori different parities.  Since
the pentagon frame is central simple over the (central simple)
quadruple-tensor source, super Skolem–Noether (M6/M7d-5a) applies at
this pair: the twisted bimodule is irreducible, so its supercenter is
one-dimensional and concentrated in a single parity `i`.  Both `pathA`
and `pathB`, read as homogeneous intertwiners, land in this
supercenter (the REVERSE of `intertwines_of_mem_superCenterBimod`,
proved here since `SuperCenterBimod.lean` records only the forward
direction) — forcing both of their parities to equal `i`, hence to
equal EACH OTHER: `p(a+b,c,d) + p(a,b,c+d) = p(a,b,c) + p(a,b+c,d) +
p(b,c,d)`, the cocycle identity `δp = 0`.

The same one-dimensionality gives the scalar χ: `pathB` spans the
one-dimensional supercenter (it is nonzero there), so `pathA = χ •
pathB` for a unique `χ ∈ K^×`.
-/
import Superfusion.Super.PentagonEdge35Close

namespace Superfusion

open Module

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

section Frame

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-! ### The reverse supercenter-bimodule lemma

`SuperCenterBimod.lean` records only `intertwines_of_mem_superCenterBimod`
(supercenter membership ⟹ intertwining).  We need the converse: a
homogeneous intertwiner of `(φ, φ')` lies in the supercenter of the
twisted bimodule.  Proved by `DirectSum.Decomposition.inductionOn`,
reducing to the homogeneous case where the twisted actions unfold
(`Twisted.smul_def` / `Twisted.op_smul_def`) to exactly the
intertwining hypothesis via `signedRSMul_of_mem`. -/

section Reverse

variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable (φ φ' : A →ₐ[K] B)
variable (hφ : IsHomogeneousHom 𝒜 ℬ φ) (hφ' : IsHomogeneousHom 𝒜 ℬ φ')

omit [Invertible (2 : K)] in
/-- **The reverse of `intertwines_of_mem_superCenterBimod`**: a
homogeneous element `t` of parity `k` satisfying the intertwining
relation for ALL homogeneous `b` lies in the supercenter of the
twisted bimodule. -/
theorem mem_superCenterBimod_of_intertwines {t : B} {k : ZMod 2}
    (htk : t ∈ ℬ k)
    (hint : ∀ ⦃j : ZMod 2⦄ ⦃b : A⦄, b ∈ 𝒜 j →
      φ' b * t = ((sgn (j * k) : ℤˣ) : ℤ) • (t * φ b)) :
    Twisted.of 𝒜 ℬ φ φ' hφ hφ' t ∈
      superCenterBimod 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ') := by
  rw [mem_superCenterBimod]
  intro b
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
      show (0 : A) • Twisted.of 𝒜 ℬ φ φ' hφ hφ' t
        = signedRSMul 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')
          (0 : A) (Twisted.of 𝒜 ℬ φ φ' hφ hφ' t)
      rw [zero_smul, map_zero, LinearMap.zero_apply]
  | @homogeneous j b =>
      show b.1 • Twisted.of 𝒜 ℬ φ φ' hφ hφ' t
        = signedRSMul 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')
          b.1 (Twisted.of 𝒜 ℬ φ φ' hφ hφ' t)
      rw [Twisted.smul_def,
        signedRSMul_of_mem 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ') b.2
          (show Twisted.of 𝒜 ℬ φ φ' hφ hφ' t ∈
            Twisted.grading 𝒜 ℬ φ φ' hφ hφ' k from htk),
        show (MulOpposite.op b.1 : Aᵐᵒᵖ) •
            Twisted.of 𝒜 ℬ φ φ' hφ hφ' t
          = Twisted.of 𝒜 ℬ φ φ' hφ hφ' (t * φ b.1) from
          Twisted.op_smul_def 𝒜 ℬ φ φ' hφ hφ' b.1 t,
        hint b.2]
      rfl
  | add u u' hu hu' =>
      show (u + u') • Twisted.of 𝒜 ℬ φ φ' hφ hφ' t
        = signedRSMul 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')
          (u + u') (Twisted.of 𝒜 ℬ φ φ' hφ hφ' t)
      rw [add_smul, map_add, LinearMap.add_apply, hu, hu']

end Reverse

/-! ### The pentagon frame's central simplicity

The frame at the top of the K₅ pentagon (`quadRoute1`'s target,
shared by all five vertices after alignment) is central simple, and
so — transferred along `quadRoute1` — is the quadruple-tensor
source.  This mirrors `pentagonT_exists`'s transfer at the triple
level (`PentagonParity.lean`). -/

section CentralSimple

/-- The pentagon frame's matrix size is nonzero (a 4096-case kernel
`decide`, mirroring `sizeL_ne_zero`). -/
theorem extSize_quad_ne_zero : ∀ a b c d : ZMod 8,
    (extSize (sizeL a b c) (a + b + c) d).1
      + (extSize (sizeL a b c) (a + b + c) d).2 ≠ 0 := by
  decide

variable (a b c d : ZMod 8)

/-- The quadruple-tensor source, bundled.  An `abbrev` (not a plain
`def`) so that it unfolds transparently during elaboration and
typeclass search — needed since its `.carrier` must unify on the
nose with the (unfolded) domains of `quadRoute1`, `alignedRoute5`,
etc. -/
noncomputable abbrev quadSource (a b c d : ZMod 8) : SuperAlgebra K :=
  ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
    (stdTower c)).gtensor (stdTower d))

/-- The pentagon frame, bundled (an `abbrev`, for the same reason as
`quadSource`). -/
noncomputable abbrev quadFrame (a b c d : ZMod 8) : SuperAlgebra K :=
  (stdTower (K := K) (a + b + c + d)).matrixSuper
    (extSize (sizeL a b c) (a + b + c) d).1
    (extSize (sizeL a b c) (a + b + c) d).2

instance quadFrame_nonempty :
    Nonempty (Fin (extSize (sizeL a b c) (a + b + c) d).1
      ⊕ Fin (extSize (sizeL a b c) (a + b + c) d).2) := by
  have h := extSize_quad_ne_zero a b c d
  by_cases h1 : (extSize (sizeL a b c) (a + b + c) d).1 = 0
  · exact ⟨Sum.inr ⟨0, by omega⟩⟩
  · exact ⟨Sum.inl ⟨0, by omega⟩⟩

instance quadFrame_finiteDimensional :
    FiniteDimensional K (quadFrame (K := K) a b c d).carrier :=
  inferInstanceAs (Module.Finite K
    (Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier))

instance quadFrame_nontrivial :
    Nontrivial (quadFrame (K := K) a b c d).carrier :=
  inferInstanceAs (Nontrivial
    (Matrix _ _ (stdTower (K := K) (a + b + c + d)).carrier))

instance quadFrame_isSuperCentral :
    IsSuperCentral (quadFrame (K := K) a b c d).grading :=
  matrixSuper_isSuperCentral (stdTower (a + b + c + d)) _ _
    (stdTower_isSuperCentral (a + b + c + d))

instance quadFrame_isGradedSimple :
    IsGradedSimple (quadFrame (K := K) a b c d).grading :=
  matrixSuper_isGradedSimple (stdTower (a + b + c + d)) _ _
    (stdTower_isGradedSimple (a + b + c + d))

instance quadSource_finiteDimensional :
    FiniteDimensional K (quadSource (K := K) a b c d).carrier :=
  Module.Finite.equiv (quadRoute1 (K := K) a b c d).toAlgEquiv.symm.toLinearEquiv

instance quadSource_nontrivial :
    Nontrivial (quadSource (K := K) a b c d).carrier :=
  (quadRoute1 (K := K) a b c d).toAlgEquiv.symm.injective.nontrivial

instance quadSource_isSuperCentral :
    IsSuperCentral (quadSource (K := K) a b c d).grading :=
  isSuperCentral_of_equiv (quadFrame (K := K) a b c d).grading
    (quadSource (K := K) a b c d).grading
    (quadRoute1 (K := K) a b c d).toAlgEquiv.symm
    (quadRoute1 (K := K) a b c d).symm.map_grading

instance quadSource_isGradedSimple :
    IsGradedSimple (quadSource (K := K) a b c d).grading :=
  isGradedSimple_of_equiv (quadFrame (K := K) a b c d).grading
    (quadSource (K := K) a b c d).grading
    (quadRoute1 (K := K) a b c d).toAlgEquiv.symm
    (quadRoute1 (K := K) a b c d).symm.map_grading

end CentralSimple

/-! ### The two path composites -/

section Paths

/-- **Path A** of the K₅ pentagon: vertex 1 → vertex 3 → vertex 5,
via `quadRoute3` and the edges `edgeT13`, `edgeT35`.  Stated with the
literal (unfolded) frame type — not `(quadFrame ...).carrier` — to
keep the defining equation and the membership/unit proofs below from
having to unify through the `quadFrame` abbreviation, which is
expensive at this depth. -/
noncomputable def pathA (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  edgeT35 a b c d * edgeT13 a b c d

/-- **Path B** of the K₅ pentagon: vertex 1 → vertex 2 → vertex 4 →
vertex 5, via `quadRoute2`, `alignedRoute4`, and the edges `edgeT12`,
`edgeT24`, `alignedEdgeT45` (same literal-type convention as
`pathA`). -/
noncomputable def pathB (a b c d : ZMod 8) :
    ((stdTower (K := K) (a + b + c + d)).matrixSuper
      (extSize (sizeL a b c) (a + b + c) d).1
      (extSize (sizeL a b c) (a + b + c) d).2).carrier :=
  alignedEdgeT45 a b c d * (edgeT24 a b c d * edgeT12 a b c d)

variable (a b c d : ZMod 8)

/-- **Path A intertwines `(quadRoute1, alignedRoute5)`**, with parity
`p(a+b,c,d) + p(a,b,c+d)` — one application of `intertwines_comp`
(`φ₁ = quadRoute1`, `φ₂ = quadRoute3`, `φ₃ = alignedRoute5`,
`t₁ = edgeT13`, `t₂ = edgeT35`). -/
theorem pathA_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (alignedRoute5 a b c d).toAlgEquiv w * pathA a b c d
        = ((sgn (j * (pentagonParity (K := K) (a + b) c d
              + pentagonParity (K := K) a b (c + d))) : ℤˣ) : ℤ) •
          (pathA a b c d * (quadRoute1 a b c d).toAlgEquiv w) :=
  intertwines_comp
    (((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).grading)
    (quadRoute1 a b c d).toAlgEquiv.toAlgHom
    (quadRoute3 a b c d).toAlgEquiv.toAlgHom
    (alignedRoute5 a b c d).toAlgEquiv.toAlgHom
    (edgeT13_intertwines a b c d) (edgeT35_intertwines a b c d)

/-- **Path B intertwines `(quadRoute1, alignedRoute5)`**, with parity
`p(a,b,c) + p(a,b+c,d) + p(b,c,d)` — two applications of
`intertwines_comp`: first `quadRoute1 → quadRoute2 → alignedRoute4`
(`t₁ = edgeT12`, `t₂ = edgeT24`), then `quadRoute1 → alignedRoute4 →
alignedRoute5` (`t₁ = edgeT24 * edgeT12`, `t₂ = alignedEdgeT45`). -/
theorem pathB_intertwines (a b c d : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃w : ((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).carrier⦄,
      w ∈ ((((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).gtensor (stdTower d)).grading j →
      (alignedRoute5 a b c d).toAlgEquiv w * pathB a b c d
        = ((sgn (j * (pentagonParity (K := K) a b c
              + pentagonParity (K := K) a (b + c) d
              + pentagonParity (K := K) b c d)) : ℤˣ) : ℤ) •
          (pathB a b c d * (quadRoute1 a b c d).toAlgEquiv w) := by
  have step1 := intertwines_comp
    (((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).grading)
    (quadRoute1 a b c d).toAlgEquiv.toAlgHom
    (quadRoute2 a b c d).toAlgEquiv.toAlgHom
    (alignedRoute4 a b c d).toAlgEquiv.toAlgHom
    (edgeT12_intertwines a b c d) (edgeT24_intertwines a b c d)
  have step2 := intertwines_comp
    (((((stdTower (K := K) a).gtensor (stdTower b)).gtensor
      (stdTower c)).gtensor (stdTower d)).grading)
    (quadRoute1 a b c d).toAlgEquiv.toAlgHom
    (alignedRoute4 a b c d).toAlgEquiv.toAlgHom
    (alignedRoute5 a b c d).toAlgEquiv.toAlgHom
    step1 (alignedEdgeT45_intertwines a b c d)
  exact step2

end Paths

/-! ### Homogeneity and invertibility of the paths -/

section PathMem

variable (a b c d : ZMod 8)

theorem pathA_mem (a b c d : ZMod 8) :
    pathA (K := K) a b c d
      ∈ ((stdTower (K := K) (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) (a + b) c d
          + pentagonParity (K := K) a b (c + d)) := by
  rw [pathA, show pentagonParity (K := K) (a + b) c d
        + pentagonParity (K := K) a b (c + d)
      = pentagonParity (K := K) a b (c + d)
        + pentagonParity (K := K) (a + b) c d from add_comm _ _]
  exact SetLike.mul_mem_graded (edgeT35_mem a b c d) (edgeT13_mem a b c d)

omit [Invertible (2 : K)] in
/-- Transport a graded membership along an equality of parities,
with the grading held abstract (the explicit statement keeps the
elaborator from building a motive over the deep concrete type). -/
private theorem mem_grading_of_eq {B : Type*} [AddCommGroup B]
    [Module K B] (𝒜 : ZMod 2 → Submodule K B) {q q' : ZMod 2}
    (h : q = q') {x : B} (hx : x ∈ 𝒜 q) : x ∈ 𝒜 q' := h ▸ hx

set_option maxHeartbeats 16000000 in
theorem pathB_mem (a b c d : ZMod 8) :
    pathB (K := K) a b c d
      ∈ ((stdTower (K := K) (a + b + c + d)).matrixSuper
          (extSize (sizeL a b c) (a + b + c) d).1
          (extSize (sizeL a b c) (a + b + c) d).2).grading
        (pentagonParity (K := K) a b c
          + pentagonParity (K := K) a (b + c) d
          + pentagonParity (K := K) b c d) := by
  have hinner := SetLike.mul_mem_graded (edgeT24_mem (K := K) a b c d)
    (edgeT12_mem a b c d)
  have houter := SetLike.mul_mem_graded (alignedEdgeT45_mem a b c d) hinner
  have hidx : pentagonParity (K := K) b c d
        + (pentagonParity (K := K) a (b + c) d
          + pentagonParity (K := K) a b c)
      = pentagonParity (K := K) a b c
        + pentagonParity (K := K) a (b + c) d
        + pentagonParity (K := K) b c d := by ring
  rw [pathB]
  exact mem_grading_of_eq _ hidx houter

theorem pathA_isUnit (a b c d : ZMod 8) :
    IsUnit (pathA (K := K) a b c d) :=
  (edgeT35_isUnit a b c d).mul (edgeT13_isUnit a b c d)

theorem pathB_isUnit (a b c d : ZMod 8) :
    IsUnit (pathB (K := K) a b c d) :=
  (alignedEdgeT45_isUnit a b c d).mul
    ((edgeT24_isUnit a b c d).mul (edgeT12_isUnit a b c d))

theorem pathA_ne_zero (a b c d : ZMod 8) :
    pathA (K := K) a b c d ≠ 0 :=
  (pathA_isUnit a b c d).ne_zero

theorem pathB_ne_zero (a b c d : ZMod 8) :
    pathB (K := K) a b c d ≠ 0 :=
  (pathB_isUnit a b c d).ne_zero

end PathMem

/-! ### The supercenter bridge

We package the two homogeneous maps `φ := quadRoute1`, `φ' :=
alignedRoute5` and their twisted bimodule once, as reusable
abbreviations, to avoid restating the six-argument `Twisted`/
`superCenterBimod` expressions at every step. -/

section Bridge

variable (a b c d : ZMod 8)

/-- The homogeneous-map witness for `quadRoute1`. -/
theorem quadRoute1_hom (a b c d : ZMod 8) :
    IsHomogeneousHom (quadSource (K := K) a b c d).grading
      (quadFrame (K := K) a b c d).grading
      (quadRoute1 a b c d).toAlgEquiv.toAlgHom :=
  isHomogeneousHom_of_map_grading _ (quadRoute1 a b c d).map_grading

/-- The homogeneous-map witness for `alignedRoute5`. -/
theorem alignedRoute5_hom (a b c d : ZMod 8) :
    IsHomogeneousHom (quadSource (K := K) a b c d).grading
      (quadFrame (K := K) a b c d).grading
      (alignedRoute5 a b c d).toAlgEquiv.toAlgHom :=
  isHomogeneousHom_of_map_grading _ (alignedRoute5 a b c d).map_grading

/-- The twisted bimodule at the pentagon frame, for the pair
`(quadRoute1, alignedRoute5)`. -/
noncomputable abbrev quadTwisted (a b c d : ZMod 8) : Type u :=
  Twisted (quadSource (K := K) a b c d).grading
    (quadFrame (K := K) a b c d).grading
    (quadRoute1 a b c d).toAlgEquiv.toAlgHom
    (alignedRoute5 a b c d).toAlgEquiv.toAlgHom
    (quadRoute1_hom a b c d) (alignedRoute5_hom a b c d)

/-- The grading of the pentagon-frame twisted bimodule (defeq to
`(quadFrame ...).grading`). -/
noncomputable abbrev quadTwistedGrading (a b c d : ZMod 8) :
    ZMod 2 → Submodule K (quadTwisted (K := K) a b c d) :=
  Twisted.grading (quadSource (K := K) a b c d).grading
    (quadFrame (K := K) a b c d).grading
    (quadRoute1 a b c d).toAlgEquiv.toAlgHom
    (alignedRoute5 a b c d).toAlgEquiv.toAlgHom
    (quadRoute1_hom a b c d) (alignedRoute5_hom a b c d)

/-- The interpretation map into the twisted bimodule. -/
noncomputable abbrev quadOf (a b c d : ZMod 8) :
    (quadFrame (K := K) a b c d).carrier ≃ₗ[K] quadTwisted (K := K) a b c d :=
  Twisted.of (quadSource (K := K) a b c d).grading
    (quadFrame (K := K) a b c d).grading
    (quadRoute1 a b c d).toAlgEquiv.toAlgHom
    (alignedRoute5 a b c d).toAlgEquiv.toAlgHom
    (quadRoute1_hom a b c d) (alignedRoute5_hom a b c d)

/-- The supercenter of the pentagon-frame twisted bimodule. -/
noncomputable abbrev quadSC (a b c d : ZMod 8) :
    Submodule K (quadTwisted (K := K) a b c d) :=
  superCenterBimod (quadSource (K := K) a b c d).grading
    (quadTwistedGrading (K := K) a b c d)

/-- **Path A lies in the supercenter of the twisted bimodule**
`(quadRoute1, alignedRoute5)`. -/
theorem pathA_mem_superCenterBimod (a b c d : ZMod 8) :
    quadOf (K := K) a b c d (pathA a b c d) ∈ quadSC (K := K) a b c d :=
  mem_superCenterBimod_of_intertwines _ _ _ _ _ _ (pathA_mem a b c d)
    (pathA_intertwines a b c d)

/-- **Path B lies in the supercenter of the twisted bimodule**
`(quadRoute1, alignedRoute5)`. -/
theorem pathB_mem_superCenterBimod (a b c d : ZMod 8) :
    quadOf (K := K) a b c d (pathB a b c d) ∈ quadSC (K := K) a b c d :=
  mem_superCenterBimod_of_intertwines _ _ _ _ _ _ (pathB_mem a b c d)
    (pathB_intertwines a b c d)

end Bridge

/-! ### Uniqueness of the Skolem–Noether element at the pentagon frame -/

section Unique

variable (a b c d : ZMod 8)

/-- The irreducibility of the twisted bimodule at the pentagon frame. -/
theorem quad_isSimpleSuperBimod_twisted (a b c d : ZMod 8) :
    IsSimpleSuperBimod (quadSource (K := K) a b c d).grading
      (quadTwistedGrading (K := K) a b c d) :=
  isSimpleSuperBimod_twisted_of_surjective _ _ _ _ _ _
    (quadRoute1 a b c d).toAlgEquiv.surjective
    (alignedRoute5 a b c d).toAlgEquiv.surjective

/-- **The Skolem–Noether uniqueness statement at the pentagon
frame**: the space of homogeneous intertwiners of `(quadRoute1,
alignedRoute5)` is one-dimensional and concentrated in a single
parity. -/
theorem quad_superSkolemNoether_unique (a b c d : ZMod 8) :
    Module.finrank K (quadSC (K := K) a b c d) = 1 ∧
      ∃ i : ZMod 2,
        quadSC (K := K) a b c d ≤ quadTwistedGrading (K := K) a b c d i :=
  superSkolemNoether_unique _ _ _ _ _ _
    (quad_isSimpleSuperBimod_twisted a b c d)

end Unique

/-! ### The pentagon comparison scalar χ -/

section Chi

variable (a b c d : ZMod 8)

/-- The auxiliary existence statement powering `pentagonChi`: some
scalar carries `pathB`'s image to `pathA`'s image in the
one-dimensional supercenter, extracted by
`exists_smul_eq_of_finrank_eq_one` applied to `pathB`'s (nonzero)
image. -/
private theorem pentagonChi_exists (a b c d : ZMod 8) :
    ∃ c' : K, c' • pathB (K := K) a b c d = pathA (K := K) a b c d := by
  classical
  obtain ⟨hdim, -⟩ := quad_superSkolemNoether_unique (K := K) a b c d
  have hBmem := pathB_mem_superCenterBimod (K := K) a b c d
  have hAmem := pathA_mem_superCenterBimod (K := K) a b c d
  set vB : quadSC (K := K) a b c d := ⟨_, hBmem⟩ with hvB
  set vA : quadSC (K := K) a b c d := ⟨_, hAmem⟩ with hvA
  have hvB0 : vB ≠ 0 := by
    intro h
    exact pathB_ne_zero a b c d
      ((quadOf (K := K) a b c d).injective
        (show quadOf (K := K) a b c d (pathB a b c d) = 0 from
          congrArg Subtype.val h))
  obtain ⟨c', hc'⟩ := exists_smul_eq_of_finrank_eq_one hdim hvB0 vA
  refine ⟨c', ?_⟩
  have hcoe : c' • quadOf (K := K) a b c d (pathB a b c d)
      = quadOf (K := K) a b c d (pathA a b c d) :=
    congrArg Subtype.val hc'
  refine (quadOf (K := K) a b c d).injective ?_
  rw [map_smul]
  exact hcoe

/-- **The pentagon comparison scalar** `χ(a,b,c,d)`: the unique
scalar with `pathA = χ • pathB`, extracted from the one-dimensional
supercenter (path B is a nonzero vector there, so it spans, by
`exists_smul_eq_of_finrank_eq_one`). -/
noncomputable def pentagonChi (a b c d : ZMod 8) : K :=
  (pentagonChi_exists a b c d).choose

theorem pentagonChi_spec (a b c d : ZMod 8) :
    pathA (K := K) a b c d
      = pentagonChi (K := K) a b c d • pathB (K := K) a b c d :=
  (pentagonChi_exists a b c d).choose_spec.symm

theorem pentagonChi_ne_zero (a b c d : ZMod 8) :
    pentagonChi (K := K) a b c d ≠ 0 := by
  intro h
  apply pathA_ne_zero (K := K) a b c d
  rw [pentagonChi_spec a b c d, h, zero_smul]

theorem pentagonChi_unique (a b c d : ZMod 8) (c' : K)
    (h : pathA (K := K) a b c d = c' • pathB (K := K) a b c d) :
    c' = pentagonChi (K := K) a b c d := by
  have hb := pentagonChi_spec (K := K) a b c d
  rw [hb] at h
  exact smul_left_injective K (pathB_ne_zero a b c d) h.symm

end Chi

/-! ### The parity cocycle identity -/

section Cocycle

omit [Invertible (2 : K)] in
/-- Two graded components of a nonzero element must have the same
parity: elements of `ℬ q ∩ ℬ i` other than `0` force `q = i`
(`ZMod 2` has only two elements, so this reduces to
`eq_zero_of_mem_zero_of_mem_one_mod`). -/
private theorem eq_of_ne_zero_mem_two_grades {B : Type*} [AddCommGroup B]
    [Module K B] (ℬ : ZMod 2 → Submodule K B) [DirectSum.Decomposition ℬ]
    {m : B} (hm0 : m ≠ 0) {q i : ZMod 2} (hq : m ∈ ℬ q) (hi : m ∈ ℬ i) :
    q = i := by
  by_contra hne
  apply hm0
  rcases zmod2_cases q with rfl | rfl <;> rcases zmod2_cases i with rfl | rfl
  · exact absurd rfl hne
  · exact eq_zero_of_mem_zero_of_mem_one_mod ℬ hq hi
  · exact eq_zero_of_mem_zero_of_mem_one_mod ℬ hi hq
  · exact absurd rfl hne

/-- **The parity cocycle identity** `δp = 0`: both `pathA` and
`pathB` are nonzero homogeneous intertwiners of `(quadRoute1,
alignedRoute5)`, hence both lie in the one-dimensional supercenter
concentrated in a single parity `i` — forcing their (a priori
different) parities to coincide with `i`, hence with each other. -/
theorem pentagonParity_cocycle (a b c d : ZMod 8) :
    pentagonParity (K := K) (a + b) c d + pentagonParity (K := K) a b (c + d)
      = pentagonParity (K := K) a b c + pentagonParity (K := K) a (b + c) d
        + pentagonParity (K := K) b c d := by
  obtain ⟨-, i, hconc⟩ := quad_superSkolemNoether_unique (K := K) a b c d
  have hiA : quadOf (K := K) a b c d (pathA a b c d) ∈
      quadTwistedGrading (K := K) a b c d i :=
    hconc (pathA_mem_superCenterBimod a b c d)
  have hiB : quadOf (K := K) a b c d (pathB a b c d) ∈
      quadTwistedGrading (K := K) a b c d i :=
    hconc (pathB_mem_superCenterBimod a b c d)
  have hqA : quadOf (K := K) a b c d (pathA a b c d) ∈
      quadTwistedGrading (K := K) a b c d
        (pentagonParity (K := K) (a + b) c d
          + pentagonParity (K := K) a b (c + d)) :=
    pathA_mem (K := K) a b c d
  have hqB : quadOf (K := K) a b c d (pathB a b c d) ∈
      quadTwistedGrading (K := K) a b c d
        (pentagonParity (K := K) a b c + pentagonParity (K := K) a (b + c) d
          + pentagonParity (K := K) b c d) :=
    pathB_mem (K := K) a b c d
  have hA0 : quadOf (K := K) a b c d (pathA a b c d) ≠ 0 := fun h =>
    pathA_ne_zero a b c d
      ((quadOf (K := K) a b c d).injective
        (h.trans (map_zero (quadOf (K := K) a b c d)).symm))
  have hB0 : quadOf (K := K) a b c d (pathB a b c d) ≠ 0 := fun h =>
    pathB_ne_zero a b c d
      ((quadOf (K := K) a b c d).injective
        (h.trans (map_zero (quadOf (K := K) a b c d)).symm))
  have heqA := eq_of_ne_zero_mem_two_grades
    (quadFrame (K := K) a b c d).grading hA0 hqA hiA
  have heqB := eq_of_ne_zero_mem_two_grades
    (quadFrame (K := K) a b c d).grading hB0 hqB hiB
  rw [heqA, heqB]

end Cocycle

end Frame

end Superfusion

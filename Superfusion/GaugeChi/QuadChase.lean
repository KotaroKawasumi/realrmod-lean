/-
Superfusion / GaugeChi / QuadChase

**The generic layer of the four-sign evaluation.**  See
`docs/quad-bridge-design.md`.

Nothing here mentions `realGauge`: this file supplies the tools with which a
single pentagon quadruple can be evaluated at EXPLICIT connectors,

0. `gq4Collapse` / `gq4Coord` — the column presentation of `GQ4`, and the
   separating functional it produces;
1. the *unit basis column* calculus (`fsingle`): `Pi.single r 1` generators
   make `gblColumnEquiv` / `gbrColumnEquiv` into standard basis columns, so a
   connector `gtOfT T` may be read off a generator with NO fusion-spec data;
2. `famTop` / `famBot` and `chiOfFamily_pos_of_separating` — the pentagon
   scalar's sign, read off ONE generator and ONE functional;
3. the sign-free specializations of the three signed pentagon edges;
4. `ConnectorFamily.scale` — rescaling a family by a nowhere-zero SCALAR
   function.  This is what removes the last structural obstacle: an explicit
   connector may be installed at finitely many triples of an existing family
   *without any dependent dispatch over the label group*, because only a
   scalar (not a linear map between label-dependent types) is being chosen.
-/
import Superfusion.GaugeChi.ConnectorRescale
import Superfusion.GaugeChi.TDictGauge

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod ConnectorFamily

universe u v

/-! ## 0. `GQ4` as a column, and the separating functional -/

section Collapse

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-- **`GQ4` collapses to a column of `F_{a,b+c+d}`'s**: transport the right
factor's column dictionary `gbrColumnEquiv` through the outer `RelTensor`
(`mapEquivLeft`), then apply the free-column collapse.  The mirror of
`ChiTower.gq1Collapse` on the other pentagon end. -/
noncomputable def gq4Collapse (hsz : Γ.gaugeSizeR b c d = Γ.gaugeSizeL b c d) :
    GQ4 K Γ a b c d ≃ₗ[K]
      ((Fin (Γ.gaugeSizeL b c d).1 ⊕ Fin (Γ.gaugeSizeL b c d).2)
        → FusionColumn (Γ.fuse a (b + c + d))) :=
  (PentagonB.RelTensor.mapEquivLeft K (gbrColumnEquiv K Γ b c d hsz)
      (gbrColumnEquiv_rightEquiv K Γ b c d hsz)).trans RelTensor.freeCollapse

/-- **`gq4Collapse` on generators.** -/
theorem gq4Collapse_mk (hsz : Γ.gaugeSizeR b c d = Γ.gaugeSizeL b c d)
    (m : GBR Γ b c d) (v : FusionColumn (Γ.fuse a (b + c + d))) :
    gq4Collapse K Γ a b c d hsz
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m v)
      = fun x => gbrColumnEquiv K Γ b c d hsz m x • v := by
  show RelTensor.freeCollapse
      (PentagonB.RelTensor.mapEquivLeft K (gbrColumnEquiv K Γ b c d hsz)
        (gbrColumnEquiv_rightEquiv K Γ b c d hsz)
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m v)) = _
  rw [show PentagonB.RelTensor.mapEquivLeft K (gbrColumnEquiv K Γ b c d hsz)
        (gbrColumnEquiv_rightEquiv K Γ b c d hsz)
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m v)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.gaugeRouteR' b c d))
          (FusionColumn (Γ.fuse a (b + c + d))) (gbrColumnEquiv K Γ b c d hsz m) v from
      RelTensor.map_mk _ _ (gbrColumnEquiv_rightEquiv K Γ b c d hsz) (fun _ _ => rfl) m v]
  exact RelTensor.freeCollapse_mk _ v

end Collapse

/-! ## 2. The unit basis column calculus

A `FusionColumn` is literally a function `Fin p ⊕ Fin q → B.carrier`, so it
has single-entry columns.  The point of this section is that **the column
dictionaries send single-entry generators to single-entry columns**, with no
fusion-isomorphism data entering: the only property of the balancing action
used is `one_smul`.  This is what makes a quadruple chase cheap. -/

section Single

variable {K : Type u} [CommRing K]
variable {P B : SuperAlgebra K} {p q : ℕ}

/-- **The single-entry fusion column** `r ↦ ξ`. -/
noncomputable def fsingle (φ : SuperAlgEquiv P (B.matrixSuper p q))
    (r : Fin p ⊕ Fin q) (ξ : B.carrier) : FusionColumn φ :=
  (Pi.single r ξ : (Fin p ⊕ Fin q) → B.carrier)

theorem fsingle_apply (φ : SuperAlgEquiv P (B.matrixSuper p q))
    (r : Fin p ⊕ Fin q) (ξ : B.carrier) (x : Fin p ⊕ Fin q) :
    (fsingle φ r ξ : (Fin p ⊕ Fin q) → B.carrier) x = if x = r then ξ else 0 :=
  Pi.single_apply r ξ x

theorem fsingle_self (φ : SuperAlgEquiv P (B.matrixSuper p q))
    (r : Fin p ⊕ Fin q) (ξ : B.carrier) :
    (fsingle φ r ξ : (Fin p ⊕ Fin q) → B.carrier) r = ξ := by
  rw [fsingle_apply, if_pos rfl]

/-- A single-entry column is homogeneous as soon as its entry is. -/
theorem fsingle_mem_grading (φ : SuperAlgEquiv P (B.matrixSuper p q))
    {i : ZMod 2} {r : Fin p ⊕ Fin q} {ξ : B.carrier}
    (hξ : ξ ∈ B.grading (i + sumParity p q r)) :
    fsingle φ r ξ ∈ FusionColumn.grading φ i :=
  Bimod.single_mem_columnGrading (sumParity p q) B.grading hξ

/-- The unit basis column at an EVEN index is even. -/
theorem fsingle_one_mem_grading (φ : SuperAlgEquiv P (B.matrixSuper p q))
    {r : Fin p ⊕ Fin q} (hr : sumParity p q r = 0) :
    fsingle φ r 1 ∈ FusionColumn.grading φ 0 :=
  fsingle_mem_grading φ (by rw [hr, add_zero]; exact SetLike.one_mem_graded B.grading)

end Single

section Dict

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

attribute [local instance 500] leftModule rightModule

/-- **The left column dictionary on a unit generator**: the image of
`GBL.mk (fsingle l 1) (fsingle r ξ)` is the single-entry column at the
collapsed index `gblIndexEquiv (l, r)`. -/
theorem gblColumnEquiv_fsingle
    (l : Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
    (r : Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
    (ξ : (Γ.D (a + b + c)).carrier) :
    gblColumnEquiv K Γ a b c
        (GBL.mk Γ a b c (fsingle (Γ.fuse a b) l 1) (fsingle (Γ.fuse (a + b) c) r ξ))
      = fsingle (Γ.gaugeRouteL a b c) (gblIndexEquiv K Γ a b c (l, r)) ξ := by
  funext x
  rw [gblColumnEquiv_mk, fsingle_apply]
  by_cases h1 : ((gblIndexEquiv K Γ a b c).symm x).1 = l
  · rw [if_pos h1, one_smul, fsingle_apply, fsingle_apply]
    by_cases h2 : ((gblIndexEquiv K Γ a b c).symm x).2 = r
    · rw [if_pos h2, if_pos (by rw [← Equiv.symm_apply_eq, ← h1, ← h2])]
    · rw [if_neg h2, if_neg fun hx => h2 (by rw [hx, Equiv.symm_apply_apply])]
  · rw [if_neg h1, zero_smul, fsingle_apply,
      if_neg fun hx => h1 (by rw [hx, Equiv.symm_apply_apply])]
    rfl

/-- **The right column dictionary on a unit generator.** -/
theorem gbrColumnEquiv_fsingle (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (l : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
    (r : Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
    (ξ : (Γ.D (a + (b + c))).carrier) :
    gbrColumnEquiv K Γ a b c hsz
        (GBR.mk Γ a b c (fsingle (Γ.fuse b c) l 1) (fsingle (Γ.fuse a (b + c)) r ξ))
      = fsingle (Γ.gaugeRouteR' a b c) (gbrIndexEquiv K Γ a b c hsz (l, r))
          ((Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv ξ) := by
  funext x
  rw [gbrColumnEquiv_mk, fsingle_apply]
  by_cases h1 : ((gbrIndexEquiv K Γ a b c hsz).symm x).1 = l
  · rw [if_pos h1, one_smul, fsingle_apply, fsingle_apply]
    by_cases h2 : ((gbrIndexEquiv K Γ a b c hsz).symm x).2 = r
    · rw [if_pos h2, if_pos (by rw [← Equiv.symm_apply_eq, ← h1, ← h2])]
    · rw [if_neg h2, if_neg fun hx => h2 (by rw [hx, Equiv.symm_apply_apply]), map_zero]
  · rw [if_neg h1, zero_smul]
    show (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
        (0 : (Γ.D (a + (b + c))).carrier) = _
    rw [map_zero, fsingle_apply,
      if_neg fun hx => h1 (by rw [hx, Equiv.symm_apply_apply])]

/-- **The generator formula for `gtOfT`**: if the matrix applied to `m`'s
column is `n`'s column, then `gtOfT T m = n` (the same statement as
`QuadBridgeProto.gtOfT_eq_of_columnEquiv`, restated here so that this file
stays out of the certificate import cone). -/
theorem gtOfT_eq_of_column (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier)
    (m : GBL Γ a b c) (n : GBR Γ a b c)
    (h : gmulVecMap K Γ a b c T (gblColumnEquiv K Γ a b c m)
      = gbrColumnEquiv K Γ a b c hsz n) :
    gtOfT K Γ a b c hsz T m = n := by
  rw [gtOfT_apply, h, LinearEquiv.symm_apply_apply]

/-- **An explicit connector on a unit generator**: only the matrix column at
the collapsed index is ever read.  `gtOfT T` sends
`GBL.mk (fsingle l 1) (fsingle r ξ)` to any `n : GBR` whose column is
`y ↦ T y X · ξ`, `X = gblIndexEquiv (l, r)`. -/
theorem gtOfT_fsingle (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier)
    (l : Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
    (r : Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
    (ξ : (Γ.D (a + b + c)).carrier) (n : GBR Γ a b c)
    (h : ∀ y, T y (gblIndexEquiv K Γ a b c (l, r)) * ξ
      = (gbrColumnEquiv K Γ a b c hsz n : Fin (Γ.gaugeSizeL a b c).1 ⊕
          Fin (Γ.gaugeSizeL a b c).2 → (Γ.D (a + b + c)).carrier) y) :
    gtOfT K Γ a b c hsz T
        (GBL.mk Γ a b c (fsingle (Γ.fuse a b) l 1) (fsingle (Γ.fuse (a + b) c) r ξ)) = n := by
  refine gtOfT_eq_of_column K Γ a b c hsz T _ n ?_
  rw [gblColumnEquiv_fsingle]
  funext y
  rw [gmulVecMap_apply]
  show Matrix.mulVec T (Pi.single (gblIndexEquiv K Γ a b c (l, r)) ξ :
    Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2 →
      (Γ.D (a + b + c)).carrier) y = _
  rw [Matrix.mulVec_single]
  exact h y

/-- **A UNIT connector on a unit generator.**  When the frozen matrix is the
identity in the Lean frame — which is the case at six of the seven triples the
detector touches — the whole connector application collapses to ONE index
identity between the two collapse bijections. -/
theorem gtOfT_one_fsingle (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier)
    (hT : ∀ y x, T y x = if y = x then 1 else 0)
    (l : Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
    (r : Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
    (p : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
    (q : Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
    (ξ : (Γ.D (a + (b + c))).carrier)
    (hidx : gbrIndexEquiv K Γ a b c hsz (p, q) = gblIndexEquiv K Γ a b c (l, r)) :
    gtOfT K Γ a b c hsz T
        (GBL.mk Γ a b c (fsingle (Γ.fuse a b) l 1)
          (fsingle (Γ.fuse (a + b) c) r
            ((Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv ξ)))
      = GBR.mk Γ a b c (fsingle (Γ.fuse b c) p 1) (fsingle (Γ.fuse a (b + c)) q ξ) := by
  refine gtOfT_fsingle K Γ a b c hsz T l r _ _ fun y => ?_
  rw [gbrColumnEquiv_fsingle, hidx, hT, fsingle_apply]
  by_cases h : y = gblIndexEquiv K Γ a b c (l, r)
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

/-- `gtOfT_one_fsingle` with unit coefficient — the form every one of the six
identity slots is used in. -/
theorem gtOfT_one_fsingle_one (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier)
    (hT : ∀ y x, T y x = if y = x then 1 else 0)
    (l : Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
    (r : Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
    (p : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
    (q : Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
    (hidx : gbrIndexEquiv K Γ a b c hsz (p, q) = gblIndexEquiv K Γ a b c (l, r)) :
    gtOfT K Γ a b c hsz T
        (GBL.mk Γ a b c (fsingle (Γ.fuse a b) l 1) (fsingle (Γ.fuse (a + b) c) r 1))
      = GBR.mk Γ a b c (fsingle (Γ.fuse b c) p 1) (fsingle (Γ.fuse a (b + c)) q 1) := by
  have h := gtOfT_one_fsingle K Γ a b c hsz T hT l r p q 1 hidx
  rwa [map_one] at h

end Dict

/-! ### Index casts at a self-equality

At the concrete labels the detector touches, `a + b + c` and `a + (b + c)` are
*definitionally* the same element of `ZMod 8`, so the three associativity
recasts of the pentagon are the identity; these are the `rfl`-lemmas that say
so. -/

section SelfCast

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

theorem gaugeCast_self {x : G} (h : x = x) (ξ : (Γ.D x).carrier) :
    (Γ.gaugeCast h).toAlgEquiv ξ = ξ := rfl

theorem gColumnCastFst_self (d : G) {x : G} (h : x = x)
    (w : FusionColumn (Γ.fuse x d)) : gColumnCastFst K Γ d h w = w := rfl

theorem fusionColumnCast_self (a : G) {x : G} (h : x = x)
    (w : FusionColumn (Γ.fuse a x)) : fusionColumnCast K Γ a h w = w := rfl

end SelfCast

/-! ## 3. The coordinate functional on `GQ4` -/

section Coord

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-- **One coordinate of `GQ4`**, through `gq4Collapse`: pick a composite
frame index `P`, an outer column index `s`, and a `K`-functional `μ` on the
total coefficient algebra. -/
noncomputable def gq4Coord (hsz : Γ.gaugeSizeR b c d = Γ.gaugeSizeL b c d)
    (Pidx : Fin (Γ.gaugeSizeL b c d).1 ⊕ Fin (Γ.gaugeSizeL b c d).2)
    (s : Fin (Γ.size a (b + c + d)).1 ⊕ Fin (Γ.size a (b + c + d)).2)
    (μ : (Γ.D (a + (b + c + d))).carrier →ₗ[K] K) :
    GQ4 K Γ a b c d →ₗ[K] K :=
  μ ∘ₗ ((LinearMap.proj (R := K)
        (φ := fun _ : Fin (Γ.size a (b + c + d)).1 ⊕ Fin (Γ.size a (b + c + d)).2 =>
          (Γ.D (a + (b + c + d))).carrier) s) ∘ₗ
      ((LinearMap.proj (R := K)
          (φ := fun _ : Fin (Γ.gaugeSizeL b c d).1 ⊕ Fin (Γ.gaugeSizeL b c d).2 =>
            FusionColumn (Γ.fuse a (b + c + d))) Pidx) ∘ₗ
        (gq4Collapse K Γ a b c d hsz).toLinearMap))

theorem gq4Coord_apply (hsz : Γ.gaugeSizeR b c d = Γ.gaugeSizeL b c d)
    (Pidx : Fin (Γ.gaugeSizeL b c d).1 ⊕ Fin (Γ.gaugeSizeL b c d).2)
    (s : Fin (Γ.size a (b + c + d)).1 ⊕ Fin (Γ.size a (b + c + d)).2)
    (μ : (Γ.D (a + (b + c + d))).carrier →ₗ[K] K) (z : GQ4 K Γ a b c d) :
    gq4Coord K Γ a b c d hsz Pidx s μ z
      = μ ((gq4Collapse K Γ a b c d hsz z Pidx :
          Fin (Γ.size a (b + c + d)).1 ⊕ Fin (Γ.size a (b + c + d)).2 →
            (Γ.D (a + (b + c + d))).carrier) s) := rfl

/-- **The coordinate functional at a unit generator of `GQ4`.** -/
theorem gq4Coord_mk_fsingle (hsz : Γ.gaugeSizeR b c d = Γ.gaugeSizeL b c d)
    (Pidx : Fin (Γ.gaugeSizeL b c d).1 ⊕ Fin (Γ.gaugeSizeL b c d).2)
    (s : Fin (Γ.size a (b + c + d)).1 ⊕ Fin (Γ.size a (b + c + d)).2)
    (μ : (Γ.D (a + (b + c + d))).carrier →ₗ[K] K)
    (m : GBR Γ b c d) (v : FusionColumn (Γ.fuse a (b + c + d))) :
    gq4Coord K Γ a b c d hsz Pidx s μ
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m v)
      = μ (((gbrColumnEquiv K Γ b c d hsz m :
          Fin (Γ.gaugeSizeL b c d).1 ⊕ Fin (Γ.gaugeSizeL b c d).2 →
            (Γ.D (b + c + d)).carrier) Pidx • v :
          Fin (Γ.size a (b + c + d)).1 ⊕ Fin (Γ.size a (b + c + d)).2 →
            (Γ.D (a + (b + c + d))).carrier) s) := by
  rw [gq4Coord_apply, gq4Collapse_mk]

end Coord

/-! ## 3b. The Koszul signs vanish at even column indices -/

section EvenEdges

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-- `GE2` at an even first slot: no sign. -/
theorem GE2_mk_of_even (e : ZMod 2)
    (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) 0)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBR.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (GQ3Inner K Γ a b c d) u
          (t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v w)) := by
  have hsgn : ((sgn (e * (0 : ZMod 2)) : ℤˣ) : ℤ) = 1 := by rw [mul_zero, sgn_zero]; rfl
  rw [GE2_mk_of_mem K Γ a b c d e t₂ ht₂ hu v w, hsgn, one_smul]

/-- `GE4` at an even first slot: no sign. -/
theorem GE4_mk_of_even (e : ZMod 2)
    (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))
    {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) 0)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (GBR Γ (a + b) c d) u (t₄ (GBL.mk Γ (a + b) c d v w)) := by
  have hsgn : ((sgn (e * (0 : ZMod 2)) : ℤˣ) : ℤ) = 1 := by rw [mul_zero, sgn_zero]; rfl
  rw [GE4_mk_of_mem K Γ a b c d e t₄ ht₄ hu v w, hsgn, one_smul]

/-- `GE5` at an even `F_{c,d}` slot: no sign. -/
theorem GE5_mk_of_even (e : ZMod 2)
    (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))
    {j : ZMod 2} {v : FusionColumn (Γ.fuse c d)} {u : FusionColumn (Γ.fuse a b)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse c d) 0)
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (GBR Γ (a + b) c d) u (GBR.mk Γ (a + b) c d v w))
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBR Γ a b (c + d)) v (t₅ (GBL.mk Γ a b (c + d) u w)) := by
  have hsgn : ((sgn ((0 : ZMod 2) * (e + j)) : ℤˣ) : ℤ) = 1 := by rw [zero_mul, sgn_zero]; rfl
  rw [GE5_mk_of_mem K Γ a b c d e t₅ ht₅ hv hu w, hsgn]
  exact one_smul ℤ _

end EvenEdges

/-! ## 4. The two route composites of a family, named -/

section Routes

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-- **The top route at a family's data** — `GE3 ∘ GE2 ∘ GE1` with the family's
own connectors at the three top slots `(a,b,c)`, `(a,b+c,d)`, `(b,c,d)`; the
middle one enters through the `gq2rCast` recast (`gt2Canon`). -/
noncomputable def famTop (C : ConnectorFamily K Γ) (a b c d : G) :
    GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d :=
  gTopRoute K Γ a b c d (C.T a b c) (C.right_equivariance a b c)
    (gParity K Γ a (b + c) d)
    (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
    (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
      (C.mem_gParity a (b + c) d))
    (C.T b c d) (C.right_equivariance b c d)

/-- **The bottom route at a family's data** — `gq4Close ∘ GE5 ∘ GE4` with the
family's connectors at the two bottom slots `(a+b,c,d)`, `(a,b,c+d)`. -/
noncomputable def famBot (C : ConnectorFamily K Γ) (a b c d : G) :
    GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d :=
  gBotRoute K Γ a b c d
    (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
    (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d)

/-- **The defining pentagon equation, in the named routes** — this is
`chiOfFamily_spec`, verbatim. -/
theorem famTop_eq_smul_famBot (C : ConnectorFamily K Γ) (a b c d : G) :
    famTop K Γ C a b c d = chiOfFamily K Γ C a b c d • famBot K Γ C a b c d :=
  chiOfFamily_spec K Γ C

/-- The pentagon equation evaluated at a single vector. -/
theorem famTop_apply (C : ConnectorFamily K Γ) (a b c d : G) (v : GQ1 K Γ a b c d) :
    famTop K Γ C a b c d v = chiOfFamily K Γ C a b c d • famBot K Γ C a b c d v := by
  rw [famTop_eq_smul_famBot, LinearMap.smul_apply]

/-- **The bottom route at a family is never zero** (`gBotRoute` is bijective
for invertible connectors, and `GQ1` is nontrivial). -/
theorem famBot_ne_zero (C : ConnectorFamily K Γ) (a b c d : G) :
    famBot K Γ C a b c d ≠ 0 :=
  gBotRoute_family_ne_zero K Γ C

/-- **The pentagon scalar from one generator and one functional.** -/
theorem chiOfFamily_eq_of_separating (C : ConnectorFamily K Γ) {a b c d : G} (cc : K)
    (v : GQ1 K Γ a b c d) (φ : GQ4 K Γ a b c d →ₗ[K] K)
    (hne : φ (famBot K Γ C a b c d v) ≠ 0)
    (h : φ (famTop K Γ C a b c d v) = cc * φ (famBot K Γ C a b c d v)) :
    chiOfFamily K Γ C a b c d = cc := by
  rw [famTop_apply, map_smul, smul_eq_mul] at h
  exact mul_right_cancel₀ hne h

/-- The same from a vector identity at one generator. -/
theorem chiOfFamily_eq_of_apply (C : ConnectorFamily K Γ) {a b c d : G} (cc : K)
    (v : GQ1 K Γ a b c d) (φ : GQ4 K Γ a b c d →ₗ[K] K)
    (hne : φ (famBot K Γ C a b c d v) ≠ 0)
    (h : famTop K Γ C a b c d v = cc • famBot K Γ C a b c d v) :
    chiOfFamily K Γ C a b c d = cc :=
  chiOfFamily_eq_of_separating K Γ C cc v φ hne (by rw [h, map_smul, smul_eq_mul])

/-- The strongest (and most expensive) input — a full identity of the two
route composites. -/
theorem chiOfFamily_eq_of_routes (C : ConnectorFamily K Γ) {a b c d : G} (cc : K)
    (h : famTop K Γ C a b c d = cc • famBot K Γ C a b c d) :
    chiOfFamily K Γ C a b c d = cc := by
  have hbot := famBot_ne_zero K Γ C a b c d
  have hspec := famTop_eq_smul_famBot K Γ C a b c d
  have hz : (cc - chiOfFamily K Γ C a b c d) • famBot K Γ C a b c d = 0 := by
    rw [sub_smul, ← h, ← hspec, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 hbot

/-! ### The two routes at a generator

The whole pentagon chase, packaged once: given the three (resp. two) values
of the family's connectors on the generators that actually occur, the route
composite is read off with no further work.  Every Koszul sign is discharged
by the evenness hypotheses (`GE2`/`GE4`/`GE5_mk_of_even`). -/

/-- **The top route at a generator.** -/
theorem famTop_mk (C : ConnectorFamily K Γ) (a b c d : G)
    (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c))
    (w : FusionColumn (Γ.fuse (a + b + c) d))
    {u₁ : FusionColumn (Γ.fuse b c)} {v₁ : FusionColumn (Γ.fuse a (b + c))}
    (h₁ : C.T a b c (GBL.mk Γ a b c u v) = GBR.mk Γ a b c u₁ v₁)
    (hu₁ : u₁ ∈ FusionColumn.grading (Γ.fuse b c) 0)
    {u₂ : FusionColumn (Γ.fuse (b + c) d)} {v₂ : FusionColumn (Γ.fuse a (b + c + d))}
    (h₂ : C.T a (b + c) d
        (GBL.mk Γ a (b + c) d v₁ (gColumnCastFst K Γ d (add_assoc a b c) w))
      = GBR.mk Γ a (b + c) d u₂ v₂)
    {u₃ : FusionColumn (Γ.fuse c d)} {v₃ : FusionColumn (Γ.fuse b (c + d))}
    (h₃ : C.T b c d (GBL.mk Γ b c d u₁ u₂) = GBR.mk Γ b c d u₃ v₃) :
    famTop K Γ C a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d u₃ v₃) v₂ := by
  show GE3 K Γ a b c d (C.T b c d) (C.right_equivariance b c d)
      (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
        (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
          (C.mem_gParity a (b + c) d))
        (GE1 K Γ a b c d (C.T a b c) (C.right_equivariance a b c)
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w))) = _
  rw [GE1_mk, h₁, GE2_mk_of_even K Γ a b c d _ _ _ hu₁]
  show GE3 K Γ a b c d (C.T b c d) (C.right_equivariance b c d)
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (GQ3Inner K Γ a b c d) u₁
        ((gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w))) = _
  rw [show (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w)
      = GBR.mk Γ a (b + c) d u₂ v₂ from by
      rw [show (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w)
        = gt2Canon K Γ a b c d (C.equiv a (b + c) d)
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
              (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w) from rfl,
        gt2Canon_mk]
      exact h₂]
  show GE3 K Γ a b c d (C.T b c d) (C.right_equivariance b c d)
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (GQ3Inner K Γ a b c d) u₁
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (FusionColumn (Γ.fuse a (b + c + d))) u₂ v₂)) = _
  rw [GE3_mk, h₃]

/-- **The bottom route at a generator.** -/
theorem famBot_mk (C : ConnectorFamily K Γ) (a b c d : G)
    (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c))
    (w : FusionColumn (Γ.fuse (a + b + c) d))
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) 0)
    {u₄ : FusionColumn (Γ.fuse c d)} {v₄ : FusionColumn (Γ.fuse (a + b) (c + d))}
    (h₄ : C.T (a + b) c d (GBL.mk Γ (a + b) c d v w) = GBR.mk Γ (a + b) c d u₄ v₄)
    (hu₄ : u₄ ∈ FusionColumn.grading (Γ.fuse c d) 0)
    {u₅ : FusionColumn (Γ.fuse b (c + d))} {v₅ : FusionColumn (Γ.fuse a (b + (c + d)))}
    (h₅ : C.T a b (c + d) (GBL.mk Γ a b (c + d) u v₄) = GBR.mk Γ a b (c + d) u₅ v₅) :
    famBot K Γ C a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d u₄ u₅)
          (fusionColumnCast K Γ a (add_assoc b c d).symm v₅) := by
  show (gq4Close K Γ a b c d).toLinearMap
      (GE5 K Γ a b c d (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d)
        (GE4 K Γ a b c d (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w))) = _
  rw [GE4_mk_of_even K Γ a b c d _ _ _ hu, h₄,
    GE5_mk_of_even K Γ a b c d _ _ _ hu₄ hu, h₅]
  exact gq4Close_mk K Γ a b c d u₄ u₅ v₅

end Routes

/-! ## 5. Only the SIGN is ever needed -/

section Sign

variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge ℝ G)

attribute [local instance 500] leftModule rightModule

/-- **The pentagon scalar is positive** as soon as the two route values at one
generator have the same (nonzero) sign. -/
theorem chiOfFamily_pos_of_separating (C : ConnectorFamily ℝ Γ) {a b c d : G}
    (v : GQ1 ℝ Γ a b c d) (φ : GQ4 ℝ Γ a b c d →ₗ[ℝ] ℝ)
    (h : 0 < φ (famTop ℝ Γ C a b c d v) * φ (famBot ℝ Γ C a b c d v)) :
    0 < chiOfFamily ℝ Γ C a b c d := by
  have hteq : φ (famTop ℝ Γ C a b c d v)
      = chiOfFamily ℝ Γ C a b c d * φ (famBot ℝ Γ C a b c d v) := by
    rw [famTop_apply, map_smul, smul_eq_mul]
  rw [hteq] at h
  nlinarith [h, mul_self_nonneg (φ (famBot ℝ Γ C a b c d v))]

end Sign

/-! ## 7. Rescaling a connector family by a scalar function

**The device that makes an explicit evaluation possible at all.**  A
`ConnectorFamily` assigns to every triple a map between *label-dependent*
types, so replacing finitely many of its members by explicit certificates
would require a dependent dispatch over the whole label group.  Multiplying
by a nowhere-zero SCALAR function needs no such thing — and, since the
intertwiner line at each triple is one-dimensional, scalars are enough to
reach ANY prescribed nonzero member. -/

section Scale

variable {K : Type u} [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable {Γ : DivisionFusionGauge K G}

attribute [local instance 500] leftModule rightModule

/-- **A connector family rescaled by a nowhere-zero scalar function.** -/
noncomputable def ConnectorFamily.scale (C : ConnectorFamily K Γ)
    (k : G → G → G → K) (hk : ∀ x y z, k x y z ≠ 0) : ConnectorFamily K Γ where
  T x y z := k x y z • C.T x y z
  parity := C.parity
  mem x y z := Submodule.smul_mem _ _ (C.mem x y z)
  ne_zero x y z := smul_ne_zero (hk x y z) (C.ne_zero x y z)

@[simp] theorem ConnectorFamily.scale_T (C : ConnectorFamily K Γ)
    (k : G → G → G → K) (hk : ∀ x y z, k x y z ≠ 0) (x y z : G) :
    (C.scale k hk).T x y z = k x y z • C.T x y z := rfl

/-- **Reaching a prescribed member by a scalar.**  If `E` is a nonzero member
of the intertwiner line at `(x,y,z)`, the unique scalar taking `C.T x y z` to
`E` exists and is nonzero. -/
theorem exists_scale_eq (C : ConnectorFamily K Γ) {x y z : G}
    {E : GBL Γ x y z →ₗ[K] GBR Γ x y z}
    (hE : E ∈ gInterSpace K Γ x y z (gParity K Γ x y z)) (hEne : E ≠ 0) :
    ∃ k : K, k ≠ 0 ∧ k • C.T x y z = E := by
  obtain ⟨κ, hκ⟩ := gInterSpace_spanning K Γ (C.mem_gParity x y z) hE hEne
  have hκ0 : κ ≠ 0 := by
    intro h0
    exact C.ne_zero x y z (by rw [hκ, h0, zero_smul])
  refine ⟨κ⁻¹, inv_ne_zero hκ0, ?_⟩
  rw [hκ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

/-- The family member as a linear map, at a family produced by `scale`
(a `rfl`-lemma making the pentagon routes readable). -/
theorem ConnectorFamily.equiv_apply (C : ConnectorFamily K Γ) (x y z : G)
    (m : GBL Γ x y z) : C.equiv x y z m = C.T x y z m := rfl

end Scale

end GaugeChi

end Superfusion

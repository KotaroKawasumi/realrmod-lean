/-
Superfusion / GaugeChi / RouteBridgeNative

**The EXCEPTIONAL bridge**: the native-device analogue of
`GaugeChi/RouteBridgeProto.lean`'s six slot-coefficient lemmas, valid at the
12 triples `(x,4,4)` / `(4,4,x)` where `hsz` fails.

`RouteBridgeProto` is the aligned template: it carries a frozen connector to
`gParity` through `TDictGauge`'s `gtOfT`, which needs
`hsz : gaugeSizeR = gaugeSizeL`.  At `(x,4,4)` and `(4,4,x)` that hypothesis
is FALSE (`gaugeSizeL = (2,2)` but `gaugeSizeR = (4,0)`), so the whole aligned
chain is unavailable.  `TDictGaugeNative` supplies the `hsz`-free device;
`CoeffCheckerRect` supplies the rectangular arithmetic.  What was missing is
the layer in between — the semantic bridge at the NATIVE frame.  This file is
that layer.

## What changes, relative to `RouteBridgeProto`

Exactly three things, and all three are local:

1. **`gaugeSizeCastEquiv` disappears.**  The aligned right-route indices
   `ro`/`ri` read the right frame through `(gaugeSizeCastEquiv hsz).symm`;
   the native ones (`roN`/`riN` below) read it through
   `gbrNativeIndexEquiv` alone, at the right route's OWN index type
   `Fin σR.1 ⊕ Fin σR.2`.
2. **The unprimed entry lemmas.**  `RouteMatrixProto`'s
   `routeR'_{a,b,c}Slot_entry` are replaced by `routeRNative_{a,b,c}Slot_entry`
   (§1), which repackage `TDictGauge`'s `routeR_aslot_entry` /
   `routeR_bslot_entry` / `routeR_cslot_entry` at the three slot embeddings
   with `includeLeft`/`includeRight` rewritten to elementary tensors — the
   same repackaging `RouteMatrixProto` §6 does, minus the frame cast.
3. **The `gaugeCast` κ moves from the right route to the left route.**  In
   the aligned device `gaugeRouteR'` post-composes with
   `κ⁻¹ = gaugeCast (add_assoc a b c).symm`, so the right coefficient lemmas
   land on `castBasis`.  In the native device `gaugeRouteR` needs no cast at
   all (it already lives in `D_{a+(b+c)}`), while the left route is read as
   `gaugeRouteLNative = gaugeRouteL ⬝ gaugeMatrixCast (add_assoc a b c)`, so
   the LEFT coefficient lemmas land on `castBasisN`.  This is forced by
   `gmulVecMapNative`, which applies κ to the incoming column.

Everything else — `realFuse_comboL/comboR_entry`, `fuseRow`/`fuseCol`,
`IsFuseZ`, `cond_zsmul_sum`, `lo`/`li`, and the six *left*-route
factorizations — is imported from `RouteBridgeProto` unchanged.

## Contents

* §1 `routeRNative_{a,b,c}Slot_entry` — gauge-generic, `hsz`-free.
* §2 `routeRNative_{a,b,c}Slot_coeff` and `routeLNative_{a,b,c}Slot_coeff` —
  the six slot route matrices as integer coefficient arrays, at `realGauge`.
* §3 the rectangular glue: `matOfCoeff₂_intertwine` /
  `realMatOfCoeff₂_intertwine` (the function-level sibling of
  `CoeffCheckerRect.checkMatEq_sound_submatrix₂`, which is the same statement
  driven by a `List` certificate through two equivalences),
  `matOfCoeff₂_mem_nativeGrading`, `matOfCoeff₂_ne_zero`, and the packaged
  consumer `gtOfTNative_mem_interSpace_of_realRepBasis`.
* §4 the fully worked exceptional triple `(1,4,4)`, ending in
  `gParity ℝ realGauge 1 4 4 = 0`.

## The triple `(1,4,4)`

`gaugeSizeR = (4,0)`, `gaugeSizeL = (2,2)` — genuinely different index types,
equal totals (`σ = 4`); `dim D_{1+(4+4)} = dim D_1 = 2`; certgen parity `0`;
transported pivot `(0,2)` with sign `+1`; `permL = permR = id`.  The connector
literal, its parity and its pivot are read from
`Data/certificates/real_lean_frame_transport.json` (record `1,4,4`,
`bridge = "exceptional"`), whose `T_lean` is already in Lean frame order.

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.CoeffCheckerRect
import Superfusion.Gauge.RealFuseSpecQuat
import Superfusion.Gauge.RealFuseSpecQuat3

namespace Superfusion

namespace GaugeChi

open Module GradedTensorProduct

universe u v

/-! ### 1. The three native right-route entry lemmas

`RouteMatrixProto` §6 packaged `TDictGauge`'s three `gaugeRouteR` entry
chases at the slot embeddings *and* at the aligned frame, by composing with
`routeR'_entry`.  Here they are packaged at the slot embeddings only: the
frame stays native, so no `hsz` and no `gaugeCast` occur. -/

section NativeSlotEntries

open Bimod

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

attribute [local instance 500] leftModule rightModule

/-- **Native right route at an `a`-slot generator** — the Koszul slot: the
entry vanishes off the `Γ.size b c` block diagonal and carries the sign
`(−1)^{π(r₁)·|x|}`.  The `hsz`-free analogue of `routeR'_aSlot_entry`. -/
theorem routeRNative_aSlot_entry {d : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading d)
    (i j : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    routeRMat K Γ a b c (aSlot K Γ a b c x) i j
      = if ((gbrNativeIndexEquiv K Γ a b c).symm i).1
            = ((gbrNativeIndexEquiv K Γ a b c).symm j).1 then
          ((sgn (sumParity (Γ.size b c).1 (Γ.size b c).2
              ((gbrNativeIndexEquiv K Γ a b c).symm i).1 * d) : ℤˣ) : ℤ) •
            (Γ.fuse a (b + c)).toAlgEquiv
              (GradedTensorProduct.tmul (𝒜 := (Γ.D a).grading)
                (ℬ := (Γ.D (b + c)).grading) K x (1 : (Γ.D (b + c)).carrier))
              ((gbrNativeIndexEquiv K Γ a b c).symm i).2
              ((gbrNativeIndexEquiv K Γ a b c).symm j).2
        else 0 := by
  show (Γ.gaugeRouteR a b c).toAlgEquiv
      (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)) i j = _
  rw [routeR_aslot_entry K Γ a b c hx, GradedTensorProduct.includeLeft_apply]

/-- **Native right route at a `b`-slot generator.** -/
theorem routeRNative_bSlot_entry (y : (Γ.D b).carrier)
    (i j : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    routeRMat K Γ a b c (bSlot K Γ a b c y) i j
      = (Γ.fuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (Γ.D a).grading)
            (ℬ := (Γ.D (b + c)).grading) K (1 : (Γ.D a).carrier)
            ((Γ.fuse b c).toAlgEquiv
              (GradedTensorProduct.tmul (𝒜 := (Γ.D b).grading) (ℬ := (Γ.D c).grading) K
                y (1 : (Γ.D c).carrier))
              ((gbrNativeIndexEquiv K Γ a b c).symm i).1
              ((gbrNativeIndexEquiv K Γ a b c).symm j).1))
          ((gbrNativeIndexEquiv K Γ a b c).symm i).2
          ((gbrNativeIndexEquiv K Γ a b c).symm j).2 := by
  show (Γ.gaugeRouteR a b c).toAlgEquiv
      (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)) i j = _
  rw [routeR_bslot_entry K Γ a b c, GradedTensorProduct.includeRight_apply,
    GradedTensorProduct.includeLeft_apply]

/-- **Native right route at a `c`-slot generator.** -/
theorem routeRNative_cSlot_entry (z : (Γ.D c).carrier)
    (i j : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    routeRMat K Γ a b c (cSlot K Γ a b c z) i j
      = (Γ.fuse a (b + c)).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (Γ.D a).grading)
            (ℬ := (Γ.D (b + c)).grading) K (1 : (Γ.D a).carrier)
            ((Γ.fuse b c).toAlgEquiv
              (GradedTensorProduct.tmul (𝒜 := (Γ.D b).grading) (ℬ := (Γ.D c).grading) K
                (1 : (Γ.D b).carrier) z)
              ((gbrNativeIndexEquiv K Γ a b c).symm i).1
              ((gbrNativeIndexEquiv K Γ a b c).symm j).1))
          ((gbrNativeIndexEquiv K Γ a b c).symm i).2
          ((gbrNativeIndexEquiv K Γ a b c).symm j).2 := by
  show (Γ.gaugeRouteR a b c).toAlgEquiv
      (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading z) i j = _
  rw [routeR_cslot_entry K Γ a b c, GradedTensorProduct.includeRight_apply,
    GradedTensorProduct.includeRight_apply]

end NativeSlotEntries

/-! ### 2. The six slot route matrices at the native frame, as integer
coefficient arrays

Same shape as `RouteBridgeProto` §4, with the three changes listed in the
module header.  Like their aligned siblings these are `realGauge`-generic and
**triple-independent**: a rollout writes them once. -/

section NativeRouteSlots

variable (a b c : ZMod 8)

/-- Outer block index of the NATIVE right composite frame — no `hsz`, no
`gaugeSizeCastEquiv`.  Compare `RouteBridgeProto.ro`. -/
noncomputable abbrev roN
    (I : Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2) :
    Fin (realSize b c).1 ⊕ Fin (realSize b c).2 :=
  ((gbrNativeIndexEquiv ℝ realGauge a b c).symm I).1

/-- Inner block index of the NATIVE right composite frame. -/
noncomputable abbrev riN
    (I : Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2) :
    Fin (realSize a (b + c)).1 ⊕ Fin (realSize a (b + c)).2 :=
  ((gbrNativeIndexEquiv ℝ realGauge a b c).symm I).2

/-- The associativity coefficient cast, applied to the LEFT tower's basis.
In the aligned device (`RouteBridgeProto.castBasis`) the cast sits on the
RIGHT route and points the other way; here it is
`κ = gaugeCast (add_assoc a b c) : D_{(a+b)+c} ≅ D_{a+(b+c)}`, because
`gmulVecMapNative` applies κ to the incoming (left) column. -/
noncomputable abbrev castBasisN (g : Fin (realRepDim (a + b + c).val)) :
    (realGauge.D (a + (b + c))).carrier :=
  (realGauge.gaugeCast (add_assoc a b c)).toAlgEquiv (realRepBasis (a + b + c) g)

/-- **Native right route at an `a`-slot generator, in coefficient form** —
the Koszul slot.  No coefficient cast: `gaugeRouteR` already lands in
`D_{a+(b+c)}`. -/
theorem routeRNative_aSlot_coeff
    {BZ : Fin (((realSize a (b + c)).1 + (realSize a (b + c)).2)
        * ((realSize a (b + c)).1 + (realSize a (b + c)).2) * realRepDim (a + (b + c)).val)
      → Fin (realRepDim a.val * realRepDim (b + c).val) → ℤ}
    (hB : IsFuseZ a (b + c) BZ)
    (i : Fin (realRepDim a.val))
    (jbc : Fin (realRepDim (b + c).val)) (hjbc : (jbc : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2) :
    routeRMat ℝ realGauge a b c (aSlot ℝ realGauge a b c (realRepBasis a i)) I J
      = ∑ g, ((if roN a b c I = roN a b c J then
              ((sgn (sumParity (realSize b c).1 (realSize b c).2 (roN a b c I)
                  * realRepBasisParity a i) : ℤˣ) : ℤ)
                * BZ (fuseRow a (b + c) (riN a b c I) (riN a b c J) g)
                    (fuseCol a (b + c) i jbc)
            else 0 : ℤ) : ℝ)
          • realRepBasis (a + (b + c)) g := by
  refine (routeRNative_aSlot_entry ℝ realGauge a b c (realRepBasis_mem a i) I J).trans ?_
  refine (congrArg (fun w : (realRep (a + (b + c))).carrier =>
      if roN a b c I = roN a b c J then
        ((sgn (sumParity (realSize b c).1 (realSize b c).2 (roN a b c I)
            * realRepBasisParity a i) : ℤˣ) : ℤ) • w else 0)
    (realFuse_basisL_entry a (b + c) i jbc hjbc (riN a b c I) (riN a b c J))).trans ?_
  refine (cond_zsmul_sum _ _ _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ =>
    congrArg (fun w : ℝ => w • realRepBasis (a + (b + c)) g) ?_
  by_cases h : roN a b c I = roN a b c J
  · rw [if_pos h, if_pos h, hB]
    push_cast
    ring
  · rw [if_neg h, if_neg h, Int.cast_zero]

/-- **Native right route at a `b`-slot generator, in coefficient form.** -/
theorem routeRNative_bSlot_coeff
    {AZ : Fin (((realSize b c).1 + (realSize b c).2) * ((realSize b c).1 + (realSize b c).2)
      * realRepDim (b + c).val) → Fin (realRepDim b.val * realRepDim c.val) → ℤ}
    (hA : IsFuseZ b c AZ)
    {BZ : Fin (((realSize a (b + c)).1 + (realSize a (b + c)).2)
        * ((realSize a (b + c)).1 + (realSize a (b + c)).2) * realRepDim (a + (b + c)).val)
      → Fin (realRepDim a.val * realRepDim (b + c).val) → ℤ}
    (hB : IsFuseZ a (b + c) BZ)
    (j : Fin (realRepDim b.val))
    (jc : Fin (realRepDim c.val)) (hjc : (jc : ℕ) = 0)
    (ia : Fin (realRepDim a.val)) (hia : (ia : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2) :
    routeRMat ℝ realGauge a b c (bSlot ℝ realGauge a b c (realRepBasis b j)) I J
      = ∑ g, ((∑ e, AZ (fuseRow b c (roN a b c I) (roN a b c J) e) (fuseCol b c j jc)
              * BZ (fuseRow a (b + c) (riN a b c I) (riN a b c J) g)
                  (fuseCol a (b + c) ia e) : ℤ) : ℝ)
          • realRepBasis (a + (b + c)) g := by
  refine (routeRNative_bSlot_entry ℝ realGauge a b c (realRepBasis b j) I J).trans ?_
  refine (congrArg (fun u : (realRep (b + c)).carrier =>
      (realFuse a (b + c)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading)
          (ℬ := (realRep (b + c)).grading) ℝ 1 u) (riN a b c I) (riN a b c J))
    (realFuse_basisL_entry b c j jc hjc (roN a b c I) (roN a b c J))).trans ?_
  refine (realFuse_comboR_one_entry a (b + c) ia hia _ _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ =>
    congrArg (fun w : ℝ => w • realRepBasis (a + (b + c)) g) ?_
  simp only [hA, hB]
  push_cast
  ring

/-- **Native right route at a `c`-slot generator, in coefficient form.** -/
theorem routeRNative_cSlot_coeff
    {AZ : Fin (((realSize b c).1 + (realSize b c).2) * ((realSize b c).1 + (realSize b c).2)
      * realRepDim (b + c).val) → Fin (realRepDim b.val * realRepDim c.val) → ℤ}
    (hA : IsFuseZ b c AZ)
    {BZ : Fin (((realSize a (b + c)).1 + (realSize a (b + c)).2)
        * ((realSize a (b + c)).1 + (realSize a (b + c)).2) * realRepDim (a + (b + c)).val)
      → Fin (realRepDim a.val * realRepDim (b + c).val) → ℤ}
    (hB : IsFuseZ a (b + c) BZ)
    (ib : Fin (realRepDim b.val)) (hib : (ib : ℕ) = 0)
    (l : Fin (realRepDim c.val))
    (ia : Fin (realRepDim a.val)) (hia : (ia : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2) :
    routeRMat ℝ realGauge a b c (cSlot ℝ realGauge a b c (realRepBasis c l)) I J
      = ∑ g, ((∑ e, AZ (fuseRow b c (roN a b c I) (roN a b c J) e) (fuseCol b c ib l)
              * BZ (fuseRow a (b + c) (riN a b c I) (riN a b c J) g)
                  (fuseCol a (b + c) ia e) : ℤ) : ℝ)
          • realRepBasis (a + (b + c)) g := by
  refine (routeRNative_cSlot_entry ℝ realGauge a b c (realRepBasis c l) I J).trans ?_
  refine (congrArg (fun u : (realRep (b + c)).carrier =>
      (realFuse a (b + c)).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep a).grading)
          (ℬ := (realRep (b + c)).grading) ℝ 1 u) (riN a b c I) (riN a b c J))
    (realFuse_basisR_entry b c ib hib l (roN a b c I) (roN a b c J))).trans ?_
  refine (realFuse_comboR_one_entry a (b + c) ia hia _ _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ =>
    congrArg (fun w : ℝ => w • realRepBasis (a + (b + c)) g) ?_
  simp only [hA, hB]
  push_cast
  ring

/-- **Recast left route at an `a`-slot generator, in coefficient form.**  The
coefficient array is `RouteBridgeProto.routeL_aSlot_coeff`'s verbatim; only
the basis it multiplies changes, from `realRepBasis (a+b+c)` to its κ-image
`castBasisN`. -/
theorem routeLNative_aSlot_coeff
    {AZ : Fin (((realSize a b).1 + (realSize a b).2) * ((realSize a b).1 + (realSize a b).2)
      * realRepDim (a + b).val) → Fin (realRepDim a.val * realRepDim b.val) → ℤ}
    (hA : IsFuseZ a b AZ)
    {BZ : Fin (((realSize (a + b) c).1 + (realSize (a + b) c).2)
        * ((realSize (a + b) c).1 + (realSize (a + b) c).2) * realRepDim (a + b + c).val)
      → Fin (realRepDim (a + b).val * realRepDim c.val) → ℤ}
    (hB : IsFuseZ (a + b) c BZ)
    (i : Fin (realRepDim a.val))
    (jb : Fin (realRepDim b.val)) (hjb : (jb : ℕ) = 0)
    (jc : Fin (realRepDim c.val)) (hjc : (jc : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    routeLNativeMat ℝ realGauge a b c (aSlot ℝ realGauge a b c (realRepBasis a i)) I J
      = ∑ g, ((∑ e, AZ (fuseRow a b (lo a b c I) (lo a b c J) e) (fuseCol a b i jb)
              * BZ (fuseRow (a + b) c (li a b c I) (li a b c J) g)
                  (fuseCol (a + b) c e jc) : ℤ) : ℝ)
          • castBasisN a b c g := by
  refine (gaugeRouteLNative_entry ℝ realGauge a b c _ I J).trans ?_
  refine (congrArg (realGauge.gaugeCast (add_assoc a b c)).toAlgEquiv
    (routeL_aSlot_coeff a b c hA hB i jb hjb jc hjc I J)).trans ?_
  exact algEquiv_sum_smul _ _ _

/-- **Recast left route at a `b`-slot generator, in coefficient form.** -/
theorem routeLNative_bSlot_coeff
    {AZ : Fin (((realSize a b).1 + (realSize a b).2) * ((realSize a b).1 + (realSize a b).2)
      * realRepDim (a + b).val) → Fin (realRepDim a.val * realRepDim b.val) → ℤ}
    (hA : IsFuseZ a b AZ)
    {BZ : Fin (((realSize (a + b) c).1 + (realSize (a + b) c).2)
        * ((realSize (a + b) c).1 + (realSize (a + b) c).2) * realRepDim (a + b + c).val)
      → Fin (realRepDim (a + b).val * realRepDim c.val) → ℤ}
    (hB : IsFuseZ (a + b) c BZ)
    (ia : Fin (realRepDim a.val)) (hia : (ia : ℕ) = 0)
    (j : Fin (realRepDim b.val))
    (jc : Fin (realRepDim c.val)) (hjc : (jc : ℕ) = 0)
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    routeLNativeMat ℝ realGauge a b c (bSlot ℝ realGauge a b c (realRepBasis b j)) I J
      = ∑ g, ((∑ e, AZ (fuseRow a b (lo a b c I) (lo a b c J) e) (fuseCol a b ia j)
              * BZ (fuseRow (a + b) c (li a b c I) (li a b c J) g)
                  (fuseCol (a + b) c e jc) : ℤ) : ℝ)
          • castBasisN a b c g := by
  refine (gaugeRouteLNative_entry ℝ realGauge a b c _ I J).trans ?_
  refine (congrArg (realGauge.gaugeCast (add_assoc a b c)).toAlgEquiv
    (routeL_bSlot_coeff a b c hA hB ia hia j jc hjc I J)).trans ?_
  exact algEquiv_sum_smul _ _ _

/-- **Recast left route at a `c`-slot generator, in coefficient form** — the
Koszul slot on the left. -/
theorem routeLNative_cSlot_coeff
    {BZ : Fin (((realSize (a + b) c).1 + (realSize (a + b) c).2)
        * ((realSize (a + b) c).1 + (realSize (a + b) c).2) * realRepDim (a + b + c).val)
      → Fin (realRepDim (a + b).val * realRepDim c.val) → ℤ}
    (hB : IsFuseZ (a + b) c BZ)
    (iab : Fin (realRepDim (a + b).val)) (hiab : (iab : ℕ) = 0)
    (l : Fin (realRepDim c.val))
    (I J : Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2) :
    routeLNativeMat ℝ realGauge a b c (cSlot ℝ realGauge a b c (realRepBasis c l)) I J
      = ∑ g, ((if lo a b c I = lo a b c J then
              ((sgn (sumParity (realSize a b).1 (realSize a b).2 (lo a b c I)
                  * realRepBasisParity c l) : ℤˣ) : ℤ)
                * BZ (fuseRow (a + b) c (li a b c I) (li a b c J) g)
                    (fuseCol (a + b) c iab l)
            else 0 : ℤ) : ℝ)
          • castBasisN a b c g := by
  refine (gaugeRouteLNative_entry ℝ realGauge a b c _ I J).trans ?_
  refine (congrArg (realGauge.gaugeCast (add_assoc a b c)).toAlgEquiv
    (routeL_cSlot_coeff a b c hB iab hiab l I J)).trans ?_
  exact algEquiv_sum_smul _ _ _

end NativeRouteSlots

/-! ### 3. The rectangular glue

`RouteBridgeProto` §5 consumes the coefficient form through three square
devices: `matOfCoeff_intertwine`, `matOfCoeff_mem_matrixGrading` and
`matOfCoeff_ne_zero`.  All three are square in an essential way — the first
because `matOfCoeff_mul` contracts one index type with itself, the second
because `matrixSuper`'s grading has ONE parity mask.  Here they are restated
over `CoeffCheckerRect`'s `matOfCoeff₂`, against `TDictGaugeNative`'s
`nativeGrading`.

`matOfCoeff₂_intertwine` is the function-level sibling of
`CoeffCheckerRect.checkMatEq_sound_submatrix₂`: same conclusion at the same
three shapes, but driven by a pointwise `convCoeff₂` identity (one `decide`)
rather than by a `List` certificate through two frame equivalences.  The
`List` route is what a 512-point rollout will emit; the pointwise route is
what a hand-carried triple uses, and it keeps the certificate free of any
`Equiv` evaluation beyond the ones already inside the route arrays. -/

section RectGlue

/-- **The rectangular certificate consumer**: a checked integer convolution
identity gives the matrix identity `X · T = c • (T · Y)` at the three shapes
`ιR × ιR`, `ιR × ιL`, `ιL × ιL`.  Rectangular analogue of
`RouteBridgeProto.matOfCoeff_intertwine`. -/
theorem matOfCoeff₂_intertwine {P : Type*} [Ring P] [Algebra ℝ P] {k : ℕ}
    {ιR ιL : Type*} [Fintype ιR] [Fintype ιL] (bP : Basis (Fin k) ℝ P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : ℝ) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X : ιR → ιR → Fin k → ℤ) (T : ιR → ιL → Fin k → ℤ)
    (Y : ιL → ιL → Fin k → ℤ)
    (h : ∀ r t g, convCoeff₂ sg co X T r t g = c * convCoeff₂ sg co T Y r t g) :
    matOfCoeff₂ bP X * matOfCoeff₂ bP T = c • (matOfCoeff₂ bP T * matOfCoeff₂ bP Y) := by
  rw [matOfCoeff₂_mul hmul hco hco', matOfCoeff₂_mul hmul hco hco', matOfCoeff₂_zsmul]
  exact congrArg (matOfCoeff₂ bP) (funext fun r => funext fun t => funext fun g => h r t g)

/-- The `realGauge` instance of `matOfCoeff₂_intertwine`. -/
theorem realMatOfCoeff₂_intertwine (m : ZMod 8) {ιR ιL : Type*}
    [Fintype ιR] [Fintype ιL] (c : ℤ)
    (X : ιR → ιR → Fin (realRepDim m.val) → ℤ)
    (T : ιR → ιL → Fin (realRepDim m.val) → ℤ)
    (Y : ιL → ιL → Fin (realRepDim m.val) → ℤ)
    (h : ∀ r t g, convCoeff₂ (realRepMulSign m) (realRepMulIdx m) X T r t g
      = c * convCoeff₂ (realRepMulSign m) (realRepMulIdx m) T Y r t g) :
    matOfCoeff₂ (realRepBasis m) X * matOfCoeff₂ (realRepBasis m) T
      = c • (matOfCoeff₂ (realRepBasis m) T * matOfCoeff₂ (realRepBasis m) Y) :=
  matOfCoeff₂_intertwine (realRepBasis m) (realRepBasis_mul m)
    (realRepMulIdx_involutive m) (realRepMulIdx_involutive m) c X T Y h

/-- **The rectangular grading of a native connector**: every basis index
carrying a nonzero coefficient must have the parity prescribed by the TWO
masks of `nativeGrading`.  Rectangular analogue of
`RouteBridgeProto.matOfCoeff_mem_matrixGrading`. -/
theorem matOfCoeff₂_mem_nativeGrading (a b c : ZMod 8)
    (x : (Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2)
      → (Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2)
      → Fin (realRepDim (a + (b + c)).val) → ℤ) (e : ZMod 2)
    (h : ∀ r s g, x r s g = 0 ∨ realRepBasisParity (a + (b + c)) g
      = e + sumParity (realGauge.gaugeSizeR a b c).1 (realGauge.gaugeSizeR a b c).2 r
        + sumParity (realGauge.gaugeSizeL a b c).1 (realGauge.gaugeSizeL a b c).2 s) :
    matOfCoeff₂ (realRepBasis (a + (b + c))) x ∈ nativeGrading ℝ realGauge a b c e := by
  intro r s
  show (∑ g, ((x r s g : ℤ) : ℝ) • realRepBasis (a + (b + c)) g)
    ∈ (realRep (a + (b + c))).grading
        (e + sumParity (realGauge.gaugeSizeR a b c).1 (realGauge.gaugeSizeR a b c).2 r
          + sumParity (realGauge.gaugeSizeL a b c).1 (realGauge.gaugeSizeL a b c).2 s)
  refine Submodule.sum_mem _ fun g _ => ?_
  rcases h r s g with h0 | hp
  · rw [h0, Int.cast_zero, zero_smul]
    exact zero_mem _
  · exact Submodule.smul_mem _ _ (hp ▸ realRepBasis_mem (a + (b + c)) g)

/-- A rectangular coefficient matrix with a nonzero coefficient is nonzero —
the hypothesis of `gtOfTNative_ne_zero`. -/
theorem matOfCoeff₂_ne_zero (m : ZMod 8) {ιR ιL : Type*}
    (x : ιR → ιL → Fin (realRepDim m.val) → ℤ) (r : ιR) (s : ιL)
    (g : Fin (realRepDim m.val)) (h : x r s g ≠ 0) :
    matOfCoeff₂ (realRepBasis m) x ≠ 0 := by
  intro h0
  refine h ?_
  have hz : matOfCoeff₂ (realRepBasis m) x
      = matOfCoeff₂ (realRepBasis m)
          (fun (_ : ιR) (_ : ιL) (_ : Fin (realRepDim m.val)) => (0 : ℤ)) := by
    rw [h0]
    refine (Matrix.ext fun r' s' => ?_).symm
    show ∑ g', ((0 : ℤ) : ℝ) • realRepBasis m g' = 0
    exact Finset.sum_eq_zero fun g' _ => by rw [Int.cast_zero, zero_smul]
  exact congrFun (congrFun (congrFun (matOfCoeff₂_injective (realRepBasis m) hz) r) s) g

/-- **The `realGauge` consumer at the native frame**: the `hsz`-FREE
drop-in for `RouteMatrixProto.gtOfT_mem_interSpace_of_realRepBasis`.  A
rectangular connector of the right degree whose native intertwining identity
holds at the `dim D_a + dim D_b + dim D_c` canonical basis vectors of the
three slots lands in `gInterSpace`. -/
theorem gtOfTNative_mem_interSpace_of_realRepBasis (a b c : ZMod 8)
    {T : NativeT ℝ realGauge a b c} {e : ZMod 2}
    (hT : T ∈ nativeGrading ℝ realGauge a b c e)
    (hAint : ∀ i, routeRMat ℝ realGauge a b c
          (aSlot ℝ realGauge a b c (realRepBasis a i)) * T
        = ((sgn (realRepBasisParity a i * e) : ℤˣ) : ℤ) •
            (T * routeLNativeMat ℝ realGauge a b c
              (aSlot ℝ realGauge a b c (realRepBasis a i))))
    (hBint : ∀ i, routeRMat ℝ realGauge a b c
          (bSlot ℝ realGauge a b c (realRepBasis b i)) * T
        = ((sgn (realRepBasisParity b i * e) : ℤˣ) : ℤ) •
            (T * routeLNativeMat ℝ realGauge a b c
              (bSlot ℝ realGauge a b c (realRepBasis b i))))
    (hCint : ∀ i, routeRMat ℝ realGauge a b c
          (cSlot ℝ realGauge a b c (realRepBasis c i)) * T
        = ((sgn (realRepBasisParity c i * e) : ℤˣ) : ℤ) •
            (T * routeLNativeMat ℝ realGauge a b c
              (cSlot ℝ realGauge a b c (realRepBasis c i)))) :
    gtOfTNative ℝ realGauge a b c T ∈ gInterSpace ℝ realGauge a b c e :=
  gtOfTNative_mem_interSpace_of_slot_generators ℝ realGauge a b c hT
    (realRepBasis a) (realRepBasisParity a)
    (realRepBasis b) (realRepBasisParity b)
    (realRepBasis c) (realRepBasisParity c)
    (realRepBasis_mem a) (realRepBasis_mem b) (realRepBasis_mem c)
    (adjoin_realRepBasis_eq_top a) (adjoin_realRepBasis_eq_top b)
    (adjoin_realRepBasis_eq_top c) hAint hBint hCint

end RectGlue

/-! ### 4. The exceptional triple `(1,4,4)`

`gaugeSizeR 1 4 4 = (4,0)`, `gaugeSizeL 1 4 4 = (2,2)` — the two frames are
different *types*, with equal totals `σ = 4`; `hsz` is false, so nothing in
`RouteBridgeProto` applies.  `dim D_{1+(4+4)} = dim D_1 = 2`.  The frozen
connector is record `1,4,4` of
`Data/certificates/real_lean_frame_transport.json` (`bridge =
"exceptional"`, `permL = permR = id`, `parity = 0`, transported pivot
`(0,2)`, pivot sign `+1`), read off its `T_lean` block in Lean frame order.

Four fusion corners are involved and all four are nontrivial as a package:
`realFuse 1 4` and `realFuse 5 4` on the left route, `realFuse 4 4`
(Wall's `ℍ ᵍ⊗ ℍ ≅ M_{4|0}(ℝ)`, the very isomorphism that makes `hsz` fail)
and `realFuse 1 0` on the right. -/

section Triple_144

open Module

/-! #### The integer shadows of the four fusion corners -/

/-- The integer sibling of `Superfusion.fuseDecode`, the base-3 value-code
decoder of the packed `RealFuseSpec*` literals. -/
def fuseDecodeZ : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | _ => 0

theorem fuseDecode_eq_fuseDecodeZ (n : ℕ) :
    fuseDecode n = ((fuseDecodeZ n : ℤ) : ℝ) := by
  match n with
  | 0 => norm_num [fuseDecode, fuseDecodeZ]
  | 1 => norm_num [fuseDecode, fuseDecodeZ]
  | 2 => norm_num [fuseDecode, fuseDecodeZ]
  | (_ + 3) =>
    show (0 : ℝ) = ((0 : ℤ) : ℝ)
    norm_num

/-- Integer shadow of the frozen `realFuseMatrix 1 4` literal. -/
def fuseZ_1_4 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0]]
  f.val col.val

theorem hfuseZ_1_4 : IsFuseZ 1 4 fuseZ_1_4 := by
  intro f col
  rw [realFuseMatrix_1_4]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_1_4, matGet] <;> rfl

/-- Integer shadow of the frozen `realFuseMatrix 4 4` literal (Wall's
isomorphism `ℍ ᵍ⊗ ℍ ≅ M_{4|0}(ℝ)`). -/
def fuseZ_4_4 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0],
    [0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1],
    [0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    [0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    [0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0],
    [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1]]
  f.val col.val

set_option maxHeartbeats 4000000 in
theorem hfuseZ_4_4 : IsFuseZ 4 4 fuseZ_4_4 := by
  intro f col
  rw [realFuseMatrix_4_4]
  fin_cases f <;> fin_cases col <;> norm_num [fuseZ_4_4, matGet] <;> rfl

/-- Integer shadow of the frozen `realFuseMatrix 5 4` literal — a `32 × 32`
matrix, carried through the SAME base-3 packing the real literal uses
(`fuseRows_5_4`), so no `256`-fold case split is ever performed. -/
def fuseZ_5_4 : Fin 32 → Fin 32 → ℤ :=
  fun i j => fuseDecodeZ (fuseRows_5_4 i / 3 ^ (j : ℕ) % 3)

theorem hfuseZ_5_4 : IsFuseZ 5 4 fuseZ_5_4 := by
  intro f col
  rw [realFuseMatrix_5_4]
  exact fuseDecode_eq_fuseDecodeZ _


/-! #### The certificate

Every line below is `scripts/certgen`-style generated: the connector literal,
its grading, its pivot, ten slot-generator certificates (2 for `D_1`, 4 for
each `D_4`), the three slot families and the assembly.  Each certificate is
two `Matrix.ext` applications of §2 and one `decide`. -/

/-- **The frozen connector** at `(1,4,4)`, as an integer coefficient array
over `D_{1+(4+4)} = D_1`: rows indexed by the RIGHT frame `Fin 4 ⊕ Fin 0`,
columns by the LEFT frame `Fin 2 ⊕ Fin 2`.  Pre-transported into Lean frame
order by `scripts/certgen` (`permL = permR = id` here), so no permutation, no
`Equiv` and no index-bound proof is ever evaluated inside a check. -/
noncomputable def Tc144 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun r s g => coeffGet [[[0, 0], [1, 0], [0, 0], [0, 0]], [[0, 0], [0, 0], [0, 0], [0, 1]], [[-1, 0], [0, 0], [0, 0], [0, 0]], [[0, 0], [0, 0], [0, 1], [0, 0]]] (sumPos r) (sumPos s) g.val

/-- **The connector** as a rectangular matrix over `D_1`. -/
noncomputable def T144 : NativeT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) :=
  matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Tc144

/-- **The rectangular grading hypothesis** — the connector is homogeneous of
degree `0` for the TWO frame masks `(4,0)` and `(2,2)`. -/
theorem hT144 : T144 ∈ nativeGrading ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) 0 :=
  matOfCoeff₂_mem_nativeGrading (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) Tc144 0 (by decide)

/-- The connector is nonzero — witnessed at its TRANSPORTED pivot
`(row 0, col 2)` of the free-coordinate manifest, i.e. frame row
`0`, frame column `1`, basis index `0`, value
`1`. -/
theorem T144_ne_zero : T144 ≠ 0 :=
  matOfCoeff₂_ne_zero ((1 : ZMod 8) + (4 + 4)) Tc144 (Sum.inl ⟨0, by decide⟩)
    (Sum.inl ⟨1, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa144_0 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    if roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I = roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J then
      ((sgn (sumParity (realSize (4 : ZMod 8) (4 : ZMod 8)).1 (realSize (4 : ZMod 8) (4 : ZMod 8)).2 (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim ((4 : ZMod 8) + 4).val)))
    else 0

/-- Recast-left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya144_0 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((1 : ZMod 8) + 4).val),
      fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- **The native intertwining certificate at the `a`-slot generator `0`.** -/
theorem hinta144_0 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xa144_0 :=
    Matrix.ext fun I J => routeRNative_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim ((4 : ZMod 8) + 4).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Ya144_0 :=
    Matrix.ext fun I J => routeLNative_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xa144_0 Tc144 Ya144_0 (by decide)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa144_1 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    if roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I = roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J then
      ((sgn (sumParity (realSize (4 : ZMod 8) (4 : ZMod 8)).1 (realSize (4 : ZMod 8) (4 : ZMod 8)).2 (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim ((4 : ZMod 8) + 4).val)))
    else 0

/-- Recast-left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya144_1 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((1 : ZMod 8) + 4).val),
      fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- **The native intertwining certificate at the `a`-slot generator `1`.** -/
theorem hinta144_1 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xa144_1 :=
    Matrix.ext fun I J => routeRNative_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_0 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim ((4 : ZMod 8) + 4).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Ya144_1 :=
    Matrix.ext fun I J => routeLNative_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 hfuseZ_5_4 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xa144_1 Tc144 Ya144_1 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb144_0 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb144_0 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((1 : ZMod 8) + 4).val),
      fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- **The native intertwining certificate at the `b`-slot generator `0`.** -/
theorem hintb144_0 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xb144_0 :=
    Matrix.ext fun I J => routeRNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yb144_0 :=
    Matrix.ext fun I J => routeLNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xb144_0 Tc144 Yb144_0 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb144_1 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb144_1 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((1 : ZMod 8) + 4).val),
      fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- **The native intertwining certificate at the `b`-slot generator `1`.** -/
theorem hintb144_1 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xb144_1 :=
    Matrix.ext fun I J => routeRNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yb144_1 :=
    Matrix.ext fun I J => routeLNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xb144_1 Tc144 Yb144_1 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb144_2 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb144_2 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((1 : ZMod 8) + 4).val),
      fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- **The native intertwining certificate at the `b`-slot generator `2`.** -/
theorem hintb144_2 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xb144_2 :=
    Matrix.ext fun I J => routeRNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yb144_2 :=
    Matrix.ext fun I J => routeLNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xb144_2 Tc144 Yb144_2 (by decide)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb144_3 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb144_3 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((1 : ZMod 8) + 4).val),
      fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- **The native intertwining certificate at the `b`-slot generator `3`.** -/
theorem hintb144_3 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xb144_3 :=
    Matrix.ext fun I J => routeRNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yb144_3 :=
    Matrix.ext fun I J => routeLNative_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xb144_3 Tc144 Yb144_3 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc144_0 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc144_0 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    if lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I = lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- **The native intertwining certificate at the `c`-slot generator `0`.** -/
theorem hintc144_0 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xc144_0 :=
    Matrix.ext fun I J => routeRNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yc144_0 :=
    Matrix.ext fun I J => routeLNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xc144_0 Tc144 Yc144_0 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc144_1 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc144_1 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    if lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I = lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- **The native intertwining certificate at the `c`-slot generator `1`.** -/
theorem hintc144_1 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xc144_1 :=
    Matrix.ext fun I J => routeRNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yc144_1 :=
    Matrix.ext fun I J => routeLNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xc144_1 Tc144 Yc144_1 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc144_2 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc144_2 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    if lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I = lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- **The native intertwining certificate at the `c`-slot generator `2`.** -/
theorem hintc144_2 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xc144_2 :=
    Matrix.ext fun I J => routeRNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yc144_2 :=
    Matrix.ext fun I J => routeLNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xc144_2 Tc144 Yc144_2 (by decide)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc144_3 : (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → (Fin (realGauge.gaugeSizeR 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeR 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    ∑ ee : Fin (realRepDim ((4 : ZMod 8) + 4).val),
      fuseZ_4_4 (fuseRow (4 : ZMod 8) (4 : ZMod 8) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (roN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 4) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (riN (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Recast-left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc144_3 : (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → (Fin (realGauge.gaugeSizeL 1 4 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 4).2) → Fin (realRepDim ((1 : ZMod 8) + (4 + 4)).val) → ℤ :=
  fun I J g =>
    if lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I = lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((1 : ZMod 8) + 4) (4 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) J) g)
            (fuseCol ((1 : ZMod 8) + 4) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- **The native intertwining certificate at the `c`-slot generator `3`.** -/
theorem hintc144_3 :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) • (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX : routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Xc144_3 :=
    Matrix.ext fun I J => routeRNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff₂ (realRepBasis ((1 : ZMod 8) + (4 + 4))) Yc144_3 :=
    Matrix.ext fun I J => routeLNative_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim ((1 : ZMod 8) + 4).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  rw [hX, hY]
  exact realMatOfCoeff₂_intertwine ((1 : ZMod 8) + (4 + 4)) ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * (0 : ZMod 2)) : ℤˣ) : ℤ) Xc144_3 Tc144 Yc144_3 (by decide)

/-- **The `a`-slot intertwining family.** -/
theorem hAint144 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T144
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * (0 : ZMod 2)) : ℤˣ) : ℤ) •
          (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]
    exact hinta144_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]
    exact hinta144_1

/-- **The `b`-slot intertwining family.** -/
theorem hBint144 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * (0 : ZMod 2)) : ℤˣ) : ℤ) •
          (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]
    exact hintb144_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]
    exact hintb144_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]
    exact hintb144_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]
    exact hintb144_3

/-- **The `c`-slot intertwining family.** -/
theorem hCint144 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    routeRMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T144
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * (0 : ZMod 2)) : ℤˣ) : ℤ) •
          (T144 * routeLNativeMat ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]
    exact hintc144_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]
    exact hintc144_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]
    exact hintc144_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]
    exact hintc144_3

/-! #### Conclusion -/

/-- `gtOfTNative T ∈ gInterSpace` at this exceptional triple — through the
`hsz`-FREE device, which is the only one available here. -/
theorem gtOfTNative144_mem_gInterSpace :
    gtOfTNative ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) T144
      ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) 0 :=
  gtOfTNative_mem_interSpace_of_realRepBasis (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) hT144 hAint144 hBint144 hCint144

theorem gtOfTNative144_ne_zero : gtOfTNative ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) T144 ≠ 0 :=
  gtOfTNative_ne_zero ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) T144_ne_zero

theorem gInterSpace144_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfTNative144_mem_gInterSpace, gtOfTNative144_ne_zero⟩

/-- **The canonical parity at the exceptional triple `(1,4,4)`**, matching the
frozen certgen table (`parity = 0` in the transport manifest). -/
theorem gParity144 : gParity ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (4 : ZMod 8) gInterSpace144_ne_bot).symm

end Triple_144

#print axioms routeRNative_aSlot_coeff
#print axioms routeLNative_cSlot_coeff
#print axioms matOfCoeff₂_intertwine
#print axioms gtOfTNative_mem_interSpace_of_realRepBasis
#print axioms gParity144

end GaugeChi

end Superfusion

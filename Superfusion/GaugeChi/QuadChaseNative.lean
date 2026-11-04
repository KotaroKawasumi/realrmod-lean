/-
Superfusion / GaugeChi / QuadChaseNative

Native-frame coordinate tools for the fourfold pentagon chase.

`QuadChase.gq4Collapse` uses the aligned right dictionary and therefore
requires `gaugeSizeR = gaugeSizeL`.  The twelve exceptional real triples are
genuinely rectangular.  Here the target vertex is first returned, through
`gq4Recast.symm`, to its natural right-associated coefficient tower; the
hypothesis-free native right dictionary can then be collapsed without any
frame-size equality.

The remaining lemmas are the native rectangular analogues of the unit-column
calculus in `QuadChase`: a `GBR` generator is a standard native column, and a
native connector matrix can consequently be evaluated on one standard source
column.
-/
import Superfusion.GaugeChi.QuadChase
import Superfusion.GaugeChi.TDictGaugeNative

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

/-! ## The native-frame collapse of the fourth pentagon vertex -/

section NativeCollapse

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-- **`GQ4` in its natural native right frame.**

The stored fourth vertex is balanced over `D_{(b+c)+d}`, whereas
`gbrNativeColumnEquiv` uses the natural coefficient algebra
`D_{b+(c+d)}`.  The public recast equivalence performs exactly this change
of coefficient tower.  After it, the native `GBR` dictionary is genuinely
right-equivariant and the usual free-column collapse applies. -/
noncomputable def gq4CollapseNative :
    GQ4 K Γ a b c d ≃ₗ[K]
      ((Fin (Γ.gaugeSizeR b c d).1 ⊕ Fin (Γ.gaugeSizeR b c d).2) →
        FusionColumn (Γ.fuse a (b + (c + d)))) :=
  (gq4Recast K Γ a b c d).symm.trans
    ((PentagonB.RelTensor.mapEquivLeft K
        (gbrNativeColumnEquiv K Γ b c d)
        (gbrNativeColumnEquiv_rightEquiv K Γ b c d)).trans
      RelTensor.freeCollapse)

/-- `gq4CollapseNative` on a generator already written in the natural
coefficient presentation `GQ4l`. -/
theorem gq4CollapseNative_recast_mk
    (m : GBR Γ b c d)
    (v : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4CollapseNative K Γ a b c d
        (gq4Recast K Γ a b c d
          (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
            (FusionColumn (Γ.fuse a (b + (c + d)))) m v))
      = fun x => gbrNativeColumnEquiv K Γ b c d m x • v := by
  show RelTensor.freeCollapse
      (PentagonB.RelTensor.mapEquivLeft K
        (gbrNativeColumnEquiv K Γ b c d)
        (gbrNativeColumnEquiv_rightEquiv K Γ b c d)
        ((gq4Recast K Γ a b c d).symm
          (gq4Recast K Γ a b c d
            (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
              (FusionColumn (Γ.fuse a (b + (c + d)))) m v)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rw [show PentagonB.RelTensor.mapEquivLeft K
        (gbrNativeColumnEquiv K Γ b c d)
        (gbrNativeColumnEquiv_rightEquiv K Γ b c d)
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + (c + d)))) m v)
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.gaugeRouteR b c d))
          (FusionColumn (Γ.fuse a (b + (c + d))))
          (gbrNativeColumnEquiv K Γ b c d m) v from
      RelTensor.map_mk _ _
        (gbrNativeColumnEquiv_rightEquiv K Γ b c d)
        (fun _ _ => rfl) m v]
  exact RelTensor.freeCollapse_mk _ v

/-- `gq4CollapseNative` on a generator in the stored `GQ4` presentation.
The outer fusion column is transported back to its natural right-associated
label before the coefficient is read. -/
theorem gq4CollapseNative_mk
    (m : GBR Γ b c d)
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    gq4CollapseNative K Γ a b c d
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m w)
      = fun x => gbrNativeColumnEquiv K Γ b c d m x •
          (fusionColumnCast K Γ a (add_assoc b c d).symm).symm w := by
  let v : FusionColumn (Γ.fuse a (b + (c + d))) :=
    (fusionColumnCast K Γ a (add_assoc b c d).symm).symm w
  have hrec :
      RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m w
        = gq4Recast K Γ a b c d
            (RelTensor.mk K (Γ.D (b + (c + d))).carrier (GBR Γ b c d)
              (FusionColumn (Γ.fuse a (b + (c + d)))) m v) := by
    rw [gq4Recast_mk]
    change RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) m w =
      RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
        (FusionColumn (Γ.fuse a (b + c + d))) m
          (fusionColumnCast K Γ a (add_assoc b c d).symm
            ((fusionColumnCast K Γ a (add_assoc b c d).symm).symm w))
    rw [LinearEquiv.apply_symm_apply]
  rw [hrec, gq4CollapseNative_recast_mk]

end NativeCollapse

/-! ## Native unit-column dictionary calculus -/

section NativeDict

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

attribute [local instance 500] leftModule rightModule

/-- **The native right dictionary on a unit generator.**  No coefficient
cast occurs: both sides live in the natural `D_{a+(b+c)}` tower. -/
theorem gbrNativeColumnEquiv_fsingle
    (l : Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
    (r : Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)
    (ξ : (Γ.D (a + (b + c))).carrier) :
    gbrNativeColumnEquiv K Γ a b c
        (GBR.mk Γ a b c (fsingle (Γ.fuse b c) l 1)
          (fsingle (Γ.fuse a (b + c)) r ξ))
      = fsingle (Γ.gaugeRouteR a b c)
          (gbrNativeIndexEquiv K Γ a b c (l, r)) ξ := by
  funext x
  rw [gbrNativeColumnEquiv_mk, fsingle_apply]
  by_cases h1 : ((gbrNativeIndexEquiv K Γ a b c).symm x).1 = l
  · rw [if_pos h1, one_smul, fsingle_apply, fsingle_apply]
    by_cases h2 : ((gbrNativeIndexEquiv K Γ a b c).symm x).2 = r
    · rw [if_pos h2,
        if_pos (by rw [← Equiv.symm_apply_eq, ← h1, ← h2])]
    · rw [if_neg h2,
        if_neg fun hx => h2 (by rw [hx, Equiv.symm_apply_apply])]
  · rw [if_neg h1, zero_smul, fsingle_apply,
      if_neg fun hx => h1 (by rw [hx, Equiv.symm_apply_apply])]
    rfl

/-- If native matrix multiplication carries the source dictionary column to
the target dictionary column, then `gtOfTNative` carries the corresponding
semantic generator to that target. -/
theorem gtOfTNative_eq_of_column
    (T : NativeT K Γ a b c) (m : GBL Γ a b c) (n : GBR Γ a b c)
    (h : gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m)
      = gbrNativeColumnEquiv K Γ a b c n) :
    gtOfTNative K Γ a b c T m = n := by
  rw [gtOfTNative_apply, h, LinearEquiv.symm_apply_apply]

/-- **A native rectangular connector on a unit generator.**

The input coefficient is first transported by the associativity cast built
into `gmulVecMapNative`; the matrix then reads only the single source-frame
column selected by `gblIndexEquiv`. -/
theorem gtOfTNative_fsingle
    (T : NativeT K Γ a b c)
    (l : Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
    (r : Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
    (ξ : (Γ.D (a + b + c)).carrier) (n : GBR Γ a b c)
    (h : ∀ y,
      T y (gblIndexEquiv K Γ a b c (l, r)) *
          (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv ξ
        = (gbrNativeColumnEquiv K Γ a b c n :
            Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 →
              (Γ.D (a + (b + c))).carrier) y) :
    gtOfTNative K Γ a b c T
        (GBL.mk Γ a b c (fsingle (Γ.fuse a b) l 1)
          (fsingle (Γ.fuse (a + b) c) r ξ)) = n := by
  refine gtOfTNative_eq_of_column K Γ a b c T _ n ?_
  rw [gblColumnEquiv_fsingle, gmulVecMapNative_apply]
  let X := gblIndexEquiv K Γ a b c (l, r)
  let κξ := (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv ξ
  have hsingle :
      (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
        ((fsingle (Γ.gaugeRouteL a b c) X ξ :
          Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2 →
            (Γ.D (a + b + c)).carrier) s))
        = (Pi.single X κξ :
            Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2 →
              (Γ.D (a + (b + c))).carrier) := by
    funext s
    rw [fsingle_apply, Pi.single_apply]
    by_cases hs : s = X
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs, map_zero]
  rw [hsingle]
  funext y
  rw [Matrix.mulVec_single]
  exact h y

end NativeDict

/-! ## The two family routes on homogeneous generators, with signs -/

section SignedRoutes

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-- **The top route on a homogeneous generator, with its Koszul sign.**

Only the first `F_{b,c}` factor exposed after the first connector crosses the
degree-`gParity(a,b+c,d)` second connector.  Thus the complete top-route sign
is `(-1)^{gParity(a,b+c,d) j₁}`. -/
theorem famTop_mk_signed (C : ConnectorFamily K Γ) (a b c d : G)
    (u : FusionColumn (Γ.fuse a b))
    (v : FusionColumn (Γ.fuse (a + b) c))
    (w : FusionColumn (Γ.fuse (a + b + c) d))
    {j₁ : ZMod 2}
    {u₁ : FusionColumn (Γ.fuse b c)}
    {v₁ : FusionColumn (Γ.fuse a (b + c))}
    (h₁ : C.T a b c (GBL.mk Γ a b c u v) = GBR.mk Γ a b c u₁ v₁)
    (hu₁ : u₁ ∈ FusionColumn.grading (Γ.fuse b c) j₁)
    {u₂ : FusionColumn (Γ.fuse (b + c) d)}
    {v₂ : FusionColumn (Γ.fuse a (b + c + d))}
    (h₂ : C.T a (b + c) d
        (GBL.mk Γ a (b + c) d v₁
          (gColumnCastFst K Γ d (add_assoc a b c) w))
      = GBR.mk Γ a (b + c) d u₂ v₂)
    {u₃ : FusionColumn (Γ.fuse c d)}
    {v₃ : FusionColumn (Γ.fuse b (c + d))}
    (h₃ : C.T b c d (GBL.mk Γ b c d u₁ u₂)
      = GBR.mk Γ b c d u₃ v₃) :
    famTop K Γ C a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d))
          (GBL.mk Γ a b c u v) w)
      = ((((sgn (gParity K Γ a (b + c) d * j₁) : ℤˣ) : ℤ) : K)) •
          RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
            (FusionColumn (Γ.fuse a (b + c + d)))
            (GBR.mk Γ b c d u₃ v₃) v₂ := by
  let source : GQ1 K Γ a b c d :=
    RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w
  let middle : GQ3 K Γ a b c d :=
    RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (GQ3Inner K Γ a b c d) u₁
      ((gt2Canon K Γ a b c d
        (C.equiv a (b + c) d)).toLinearMap
          (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w))
  let target : GQ4 K Γ a b c d :=
    RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d u₃ v₃) v₂
  let ε : K := (((sgn (gParity K Γ a (b + c) d * j₁) : ℤˣ) : ℤ) : K)
  have hprefix :
      GE2 K Γ a b c d (gParity K Γ a (b + c) d)
          (gt2Canon K Γ a b c d
            (C.equiv a (b + c) d)).toLinearMap
          (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d)
            (gParity K Γ a (b + c) d)
            (C.mem_gParity a (b + c) d))
          (GE1 K Γ a b c d (C.T a b c)
            (C.right_equivariance a b c) source)
        = ε • middle := by
    dsimp only [source, middle, ε]
    rw [GE1_mk, h₁, GE2_mk_of_mem K Γ a b c d _ _ _ hu₁,
      ← Int.cast_smul_eq_zsmul K]
    rfl
  have hcanon :
      (gt2Canon K Γ a b c d
        (C.equiv a (b + c) d)).toLinearMap
          (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w)
        = GBR.mk Γ a (b + c) d u₂ v₂ := by
    rw [show (gt2Canon K Γ a b c d
        (C.equiv a (b + c) d)).toLinearMap
        (RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c)))
          (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w)
      = gt2Canon K Γ a b c d (C.equiv a (b + c) d)
          (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v₁ w) from rfl,
      gt2Canon_mk]
    exact h₂
  have hsuffix :
      GE3 K Γ a b c d (C.T b c d) (C.right_equivariance b c d)
          middle = target := by
    dsimp only [middle, target]
    rw [hcanon]
    show GE3 K Γ a b c d (C.T b c d) (C.right_equivariance b c d)
        (RelTensor.mk K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) u₁
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse (b + c) d))
            (FusionColumn (Γ.fuse a (b + c + d))) u₂ v₂))
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d)))
          (GBR.mk Γ b c d u₃ v₃) v₂
    rw [GE3_mk, h₃]
  change famTop K Γ C a b c d source = ε • target
  calc
    famTop K Γ C a b c d source =
        GE3 K Γ a b c d (C.T b c d) (C.right_equivariance b c d)
          (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
            (gt2Canon K Γ a b c d
              (C.equiv a (b + c) d)).toLinearMap
            (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d)
              (gParity K Γ a (b + c) d)
              (C.mem_gParity a (b + c) d))
            (GE1 K Γ a b c d (C.T a b c)
              (C.right_equivariance a b c) source)) := rfl
    _ = GE3 K Γ a b c d (C.T b c d)
        (C.right_equivariance b c d) (ε • middle) :=
      congrArg (GE3 K Γ a b c d (C.T b c d)
        (C.right_equivariance b c d)) hprefix
    _ = ε • GE3 K Γ a b c d (C.T b c d)
        (C.right_equivariance b c d) middle :=
      (GE3 K Γ a b c d (C.T b c d)
        (C.right_equivariance b c d)).map_smul ε middle
    _ = ε • target := congrArg (fun z => ε • z) hsuffix

/-- **The bottom route on homogeneous generators, with both Koszul signs.**

The fourth edge contributes `(-1)^{e₄ j}`.  After it, the fifth edge
contributes `(-1)^{i (e₅+j)}`.  The displayed exponent is their sum in
`ZMod 2`; the final coefficient recast is sign-free. -/
theorem famBot_mk_signed (C : ConnectorFamily K Γ) (a b c d : G)
    {j : ZMod 2}
    (u : FusionColumn (Γ.fuse a b))
    (v : FusionColumn (Γ.fuse (a + b) c))
    (w : FusionColumn (Γ.fuse (a + b + c) d))
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    {i : ZMod 2}
    {u₄ : FusionColumn (Γ.fuse c d)}
    {v₄ : FusionColumn (Γ.fuse (a + b) (c + d))}
    (h₄ : C.T (a + b) c d (GBL.mk Γ (a + b) c d v w)
      = GBR.mk Γ (a + b) c d u₄ v₄)
    (hu₄ : u₄ ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u₅ : FusionColumn (Γ.fuse b (c + d))}
    {v₅ : FusionColumn (Γ.fuse a (b + (c + d)))}
    (h₅ : C.T a b (c + d) (GBL.mk Γ a b (c + d) u v₄)
      = GBR.mk Γ a b (c + d) u₅ v₅) :
    famBot K Γ C a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d))
          (GBL.mk Γ a b c u v) w)
      = ((((sgn
          (gParity K Γ (a + b) c d * j +
            i * (gParity K Γ a b (c + d) + j)) : ℤˣ) : ℤ) : K)) •
          RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
            (FusionColumn (Γ.fuse a (b + c + d)))
            (GBR.mk Γ b c d u₄ u₅)
            (fusionColumnCast K Γ a (add_assoc b c d).symm v₅) := by
  let source : GQ1 K Γ a b c d :=
    RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w
  let middle₅ : GQ5 K Γ a b c d :=
    RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (GBR Γ (a + b) c d) u (GBR.mk Γ (a + b) c d u₄ v₄)
  let middle₄ : GQ4r K Γ a b c d :=
    RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GBR Γ a b (c + d)) u₄ (GBR.mk Γ a b (c + d) u₅ v₅)
  let target : GQ4 K Γ a b c d :=
    RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d u₄ u₅)
      (fusionColumnCast K Γ a (add_assoc b c d).symm v₅)
  let ε₄ : K :=
    (((sgn (gParity K Γ (a + b) c d * j) : ℤˣ) : ℤ) : K)
  let ε₅ : K :=
    (((sgn (i * (gParity K Γ a b (c + d) + j)) : ℤˣ) : ℤ) : K)
  have hfour :
      GE4 K Γ a b c d (gParity K Γ (a + b) c d)
          (C.T (a + b) c d) (C.slotFour a b c d) source
        = ε₄ • middle₅ := by
    dsimp only [source, middle₅, ε₄]
    rw [GE4_mk_of_mem K Γ a b c d _ _ _ hu, h₄,
      ← Int.cast_smul_eq_zsmul K]
    rfl
  have hfive :
      GE5 K Γ a b c d (gParity K Γ a b (c + d))
          (C.T a b (c + d)) (C.slotFive a b c d) middle₅
        = ε₅ • middle₄ := by
    dsimp only [middle₅, middle₄, ε₅]
    rw [GE5_mk_of_mem K Γ a b c d _ _ _ hu₄ hu, h₅,
      ← Int.cast_smul_eq_zsmul K]
    rfl
  have hclose :
      (gq4Close K Γ a b c d).toLinearMap middle₄ = target := by
    dsimp only [middle₄, target]
    exact gq4Close_mk K Γ a b c d u₄ u₅ v₅
  change famBot K Γ C a b c d source =
    ((((sgn
      (gParity K Γ (a + b) c d * j +
        i * (gParity K Γ a b (c + d) + j)) : ℤˣ) : ℤ) : K)) • target
  calc
    famBot K Γ C a b c d source =
        (gq4Close K Γ a b c d).toLinearMap
          (GE5 K Γ a b c d (gParity K Γ a b (c + d))
            (C.T a b (c + d)) (C.slotFive a b c d)
            (GE4 K Γ a b c d (gParity K Γ (a + b) c d)
              (C.T (a + b) c d) (C.slotFour a b c d) source)) := rfl
    _ = (gq4Close K Γ a b c d).toLinearMap
        (GE5 K Γ a b c d (gParity K Γ a b (c + d))
          (C.T a b (c + d)) (C.slotFive a b c d)
          (ε₄ • middle₅)) :=
      congrArg (fun z => (gq4Close K Γ a b c d).toLinearMap
        (GE5 K Γ a b c d (gParity K Γ a b (c + d))
          (C.T a b (c + d)) (C.slotFive a b c d) z)) hfour
    _ = (gq4Close K Γ a b c d).toLinearMap
        (ε₄ • GE5 K Γ a b c d (gParity K Γ a b (c + d))
          (C.T a b (c + d)) (C.slotFive a b c d) middle₅) :=
      congrArg (gq4Close K Γ a b c d).toLinearMap
        ((GE5 K Γ a b c d (gParity K Γ a b (c + d))
          (C.T a b (c + d)) (C.slotFive a b c d)).map_smul ε₄ middle₅)
    _ = (gq4Close K Γ a b c d).toLinearMap
        (ε₄ • (ε₅ • middle₄)) :=
      congrArg (fun z => (gq4Close K Γ a b c d).toLinearMap
        (ε₄ • z)) hfive
    _ = ε₄ • (ε₅ • (gq4Close K Γ a b c d).toLinearMap middle₄) := by
      rw [map_smul, map_smul]
    _ = ε₄ • (ε₅ • target) :=
      congrArg (fun z => ε₄ • (ε₅ • z)) hclose
    _ = ((((sgn
        (gParity K Γ (a + b) c d * j +
          i * (gParity K Γ a b (c + d) + j)) : ℤˣ) : ℤ) : K)) • target := by
      dsimp only [ε₄, ε₅]
      rw [smul_smul, ← Int.cast_mul, ← Units.val_mul, ← sgn_add]

end SignedRoutes

/-! ## One native coordinate of the fourth vertex -/

section NativeCoord

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-- One coordinate of `GQ4` in its natural rectangular right frame. -/
noncomputable def gq4NativeCoord
    (Pidx : Fin (Γ.gaugeSizeR b c d).1 ⊕ Fin (Γ.gaugeSizeR b c d).2)
    (s : Fin (Γ.size a (b + (c + d))).1 ⊕
      Fin (Γ.size a (b + (c + d))).2)
    (μ : (Γ.D (a + (b + (c + d)))).carrier →ₗ[K] K) :
    GQ4 K Γ a b c d →ₗ[K] K :=
  μ ∘ₗ ((LinearMap.proj (R := K)
        (φ := fun _ : Fin (Γ.size a (b + (c + d))).1 ⊕
            Fin (Γ.size a (b + (c + d))).2 =>
          (Γ.D (a + (b + (c + d)))).carrier) s) ∘ₗ
      ((LinearMap.proj (R := K)
          (φ := fun _ : Fin (Γ.gaugeSizeR b c d).1 ⊕
              Fin (Γ.gaugeSizeR b c d).2 =>
            FusionColumn (Γ.fuse a (b + (c + d)))) Pidx) ∘ₗ
        (gq4CollapseNative K Γ a b c d).toLinearMap))

theorem gq4NativeCoord_apply
    (Pidx : Fin (Γ.gaugeSizeR b c d).1 ⊕ Fin (Γ.gaugeSizeR b c d).2)
    (s : Fin (Γ.size a (b + (c + d))).1 ⊕
      Fin (Γ.size a (b + (c + d))).2)
    (μ : (Γ.D (a + (b + (c + d)))).carrier →ₗ[K] K)
    (z : GQ4 K Γ a b c d) :
    gq4NativeCoord K Γ a b c d Pidx s μ z =
      μ ((gq4CollapseNative K Γ a b c d z Pidx :
        Fin (Γ.size a (b + (c + d))).1 ⊕
          Fin (Γ.size a (b + (c + d))).2 →
            (Γ.D (a + (b + (c + d)))).carrier) s) :=
  rfl

/-- Coordinate evaluation on a stored `GQ4` generator. -/
theorem gq4NativeCoord_mk
    (Pidx : Fin (Γ.gaugeSizeR b c d).1 ⊕ Fin (Γ.gaugeSizeR b c d).2)
    (s : Fin (Γ.size a (b + (c + d))).1 ⊕
      Fin (Γ.size a (b + (c + d))).2)
    (μ : (Γ.D (a + (b + (c + d)))).carrier →ₗ[K] K)
    (m : GBR Γ b c d) (w : FusionColumn (Γ.fuse a (b + c + d))) :
    gq4NativeCoord K Γ a b c d Pidx s μ
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) m w)
      = μ (((gbrNativeColumnEquiv K Γ b c d m :
          Fin (Γ.gaugeSizeR b c d).1 ⊕ Fin (Γ.gaugeSizeR b c d).2 →
            (Γ.D (b + (c + d))).carrier) Pidx •
          (fusionColumnCast K Γ a (add_assoc b c d).symm).symm w :
            Fin (Γ.size a (b + (c + d))).1 ⊕
              Fin (Γ.size a (b + (c + d))).2 →
                (Γ.D (a + (b + (c + d)))).carrier) s) := by
  rw [gq4NativeCoord_apply, gq4CollapseNative_mk]

end NativeCoord

end GaugeChi

end Superfusion

/-
Superfusion / GaugeChi / QuintNontrivial

Milestone M13-3a of the abstract `(p, χ)` arc (the K₅ chain): **`Nontrivial
(V1 K Γ a b c d e)`**, for every `a b c d e : G` — the genuinely new content
`Quint.lean`'s file docstring (referee correction 4) flags as deferred: a
`D_{a+b+c+d}`-EQUIVARIANT collapse of `GQ1`'s own `gq1Collapse`
(`GaugeChi.ChiTower`), transported through `V1`'s FIRST slot, composed with
a plain "coordinate-evaluation" separating functional against `V1`'s SECOND
slot `FusionColumn (Γ.fuse (a+b+c+d) e)`.

**The route actually used** (equivariant collapse, first slot):

1. **`FusionColumn (Γ.fuse x y)` is nontrivial** for any `x y : G`: it is
   literally `(Fin p ⊕ Fin q) → (Γ.D (x+y)).carrier` with `(p, q) =
   Γ.size x y`; `Γ.size_pos` (`Gauge.FusionGauge`) gives `p + q ≠ 0`, hence
   `Fin p ⊕ Fin q` is nonempty, and `Γ.nontriv (x+y)` gives the value type
   nontrivial — `Function.const`'s injectivity (needing exactly the
   nonempty index) transports nontriviality onto the column.
2. **`gq1Collapse`'s own right `D_{a+b+c+d}`-action-equivariance**: a
   pointwise-in-the-index-coordinate fact, assembled from three
   commutations — `RelTensor.map_comm_rightActionEnd` (new, general: a
   right-`A`-equivariant first-slot map commutes with the OUTER right
   `C`-action, sign-free, `RelTensor.induction_on`), instantiated at
   `gblFirstCollapse`/`gblFirstCollapse_rightEquiv`; `RelTensor.freeCollapse
   _rightActionEnd` (`Bimod.ChiTower`, already general); and the
   `piProdCollapse`-commutes-with-a-pointwise-action triviality (`rfl`,
   literal currying).
3. **The separating functional**: `proj := eval at a fixed coordinate ∘
   gq1Collapse`, a `K`-linear, right-`D_{a+b+c+d}`-equivariant map `GQ1 →
   D_{a+b+c+d}` (from 2). `f m n := proj(m) • n` (via `Algebra.lsmul`,
   `OuterActions.lean`'s own combinator) is `IsBalanced` (the balancing
   check reduces to `proj`'s equivariance plus `Module`'s own `mul_smul`
   axiom — no further hypothesis on `N`'s action shape is needed, so the
   "matrix, not free" character of `N`'s slot action the referee correction
   flags is a genuine non-issue for this argument). Choosing `m₀` with
   `proj m₀ = 1` (via `gq1Collapse`'s surjectivity, `Pi.single`) and `n₀ ≠
   0` (from 1) gives `RelTensor.lift f hbal (mk m₀ n₀) = n₀ ≠ 0`, hence
   `mk m₀ n₀ ≠ 0` in `V1`.

The corollary `V1_exists_ne_zero` is stated alongside for direct
consumption if `Nontrivial` itself isn't the preferred spelling downstream.
-/
import Superfusion.GaugeChi.Quint
import Superfusion.GaugeChi.ChiTower

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

/-! ### `FusionColumn (Γ.fuse x y)` is nontrivial -/

private theorem finSum_nonempty {p q : ℕ} (h : p + q ≠ 0) : Nonempty (Fin p ⊕ Fin q) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · exact ⟨Sum.inr ⟨0, by omega⟩⟩
  · exact ⟨Sum.inl ⟨0, hp⟩⟩

/-- **`FusionColumn (Γ.fuse x y)` is nontrivial**: it is literally `(Fin p ⊕
Fin q) → (Γ.D (x+y)).carrier` with `(p, q) = Γ.size x y`; `Γ.size_pos`
supplies `p + q ≠ 0` (hence the index nonempty), and `Γ.nontriv (x+y)`
supplies the value type nontrivial — `Function.const`'s injectivity (given
the nonempty index) transports nontriviality onto the column. -/
theorem fusionColumn_nontrivial (x y : G) :
    Nontrivial (FusionColumn (Γ.fuse x y)) := by
  haveI := Γ.nontriv (x + y)
  haveI : Nonempty (Fin (Γ.size x y).1 ⊕ Fin (Γ.size x y).2) :=
    finSum_nonempty (Γ.size_pos x y)
  show Nontrivial ((Fin (Γ.size x y).1 ⊕ Fin (Γ.size x y).2) → (Γ.D (x + y)).carrier)
  exact Function.Injective.nontrivial
    (f := Function.const (Fin (Γ.size x y).1 ⊕ Fin (Γ.size x y).2)) Function.const_injective

/-! ### `PentagonB.RelTensor.mapEquivLeft`'s first slot commutes with the
outer right `C`-action -/

section MapEquivLeftCommRightActionEnd

variable {A : Type*} [Ring A]
variable {M M' : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module K M'] [Module Aᵐᵒᵖ M']
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {C : Type*} [Ring C] [Algebra K C] [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N]
  [IsScalarTower K Cᵐᵒᵖ N]

omit [Invertible (2 : K)] in
/-- **`mapEquivLeft`'s generator formula**, bridging its `LinearEquiv`
application to the underlying `RelTensor.map` it is built from
(`PentagonB.RelTensor.mapEquivLeft`'s own definition unfolds to `RelTensor.
map φ.toLinearMap id hφ _`, so its action on `mk m n` is `map_mk`'s
formula). -/
private theorem mapEquivLeft_mk
    (φ : M ≃ₗ[K] M')
    (hφ : ∀ (a : A) (m : M), φ (MulOpposite.op a • m) = MulOpposite.op a • φ m)
    (m : M) (n : N) :
    PentagonB.RelTensor.mapEquivLeft K φ hφ (RelTensor.mk K A M N m n)
      = RelTensor.mk K A M' N (φ m) n := by
  show RelTensor.map φ.toLinearMap (LinearMap.id : N →ₗ[K] N) hφ (fun _ _ => rfl)
      (RelTensor.mk K A M N m n) = _
  rw [RelTensor.map_mk]
  rfl

omit [Invertible (2 : K)] in
/-- **`mapEquivLeft`'s first slot commutes with the outer right `C`-action**:
for `φ` right-`A`-equivariant, pushing `φ` through `rightActionEnd`'s
`C`-action in either order agrees — a direct `RelTensor.induction_on` fact
(both sides literal equalities of generators, sign-free since `map`'s own
construction never signs). -/
private theorem mapEquivLeft_comm_rightActionEnd
    (φ : M ≃ₗ[K] M')
    (hφ : ∀ (a : A) (m : M), φ (MulOpposite.op a • m) = MulOpposite.op a • φ m)
    (c : Cᵐᵒᵖ) (x : M ⊗[A;K] N) :
    PentagonB.RelTensor.mapEquivLeft K φ hφ (rightActionEnd K A M N c x)
      = rightActionEnd K A M' N c (PentagonB.RelTensor.mapEquivLeft K φ hφ x) := by
  induction x using RelTensor.induction_on with
  | zero => simp
  | mk m n => rw [rightActionEnd_mk, mapEquivLeft_mk, mapEquivLeft_mk, rightActionEnd_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

end MapEquivLeftCommRightActionEnd

/-! ### `gq1Collapse`'s own right `D_{a+b+c+d}`-action-equivariance -/

section GQ1CollapseEquivariance

variable (a b c d : G)

/-- **`GBL Γ a b c`'s own collapse, then `freeCollapse`, as ONE named
`LinearEquiv`** (top-level `def`, mirroring `GaugeChi.ChiTower.gq1Collapse`'s
own first `.trans` step verbatim): building the intermediate composite as
its OWN top-level `def` (with an EXPLICIT, `FusionColumn`-spelled codomain)
lets `piProdCollapse`'s later composition unify against this ALREADY-FIXED
type by plain defeq, rather than propagating `piProdCollapse`'s own raw
`Idx3 → D` target down into `RelTensor.freeCollapse`'s implicit second
factor BEFORE it can be read off `mapEquivLeft`'s actual codomain
`FusionColumn (Γ.fuse (a+b+c) d)` (an instance-resolution ordering trap that
a single mega `have`/`show` re-deriving the whole `.trans` chain at once
hits). -/
private noncomputable def gq1W :
    GQ1 K Γ a b c d ≃ₗ[K]
      ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
          (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)
        → FusionColumn (Γ.fuse (a + b + c) d)) :=
  (PentagonB.RelTensor.mapEquivLeft K (gblFirstCollapse K Γ a b c)
      (gblFirstCollapse_rightEquiv K Γ a b c)).trans RelTensor.freeCollapse

private theorem gq1W_apply (z : GQ1 K Γ a b c d) :
    gq1W K Γ a b c d z
      = RelTensor.freeCollapse
          (PentagonB.RelTensor.mapEquivLeft K (gblFirstCollapse K Γ a b c)
            (gblFirstCollapse_rightEquiv K Γ a b c) z) := rfl

/-- **A local re-derivation of `gq1Collapse`'s own defining composite**
(`gq1W` composed with the final currying), as a top-level `def`; `gq1Collapse
_eq_local` (`rfl`) bridges it to the imported `gq1Collapse`. -/
private noncomputable def gq1CollapseLocal :
    GQ1 K Γ a b c d ≃ₗ[K]
      (((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
          (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)) ×
        (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2)
        → (Γ.D (a + b + c + d)).carrier) :=
  (gq1W K Γ a b c d).trans
    (piProdCollapse K ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
        (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2))
      (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2)
      (Γ.D (a + b + c + d)).carrier)

private theorem gq1CollapseLocal_apply (z : GQ1 K Γ a b c d) :
    gq1CollapseLocal K Γ a b c d z
      = piProdCollapse K ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
            (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2))
          (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2)
          (Γ.D (a + b + c + d)).carrier (gq1W K Γ a b c d z) := rfl

private theorem gq1Collapse_eq_local :
    gq1Collapse K Γ a b c d = gq1CollapseLocal K Γ a b c d := rfl

private theorem gq1Collapse_rightActionEnd
    (τ : ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ) (m : GQ1 K Γ a b c d) :
    gq1Collapse K Γ a b c d (τ • m)
      = fun p => τ • gq1Collapse K Γ a b c d m p := by
  rw [GQ1.right_smul_apply K Γ a b c d τ m]
  funext p
  rw [gq1Collapse_eq_local, gq1CollapseLocal_apply, gq1CollapseLocal_apply]
  rw [gq1W_apply, gq1W_apply, mapEquivLeft_comm_rightActionEnd,
    RelTensor.freeCollapse_rightActionEnd]
  rfl

end GQ1CollapseEquivariance

/-! ### The separating functional and the discharge -/

section Discharge

variable (a b c d e : G)

private noncomputable abbrev QIdx : Type _ :=
  ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
      (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)) ×
    (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2)

private theorem qidx_nonempty : Nonempty (QIdx K Γ a b c d) := by
  haveI : Nonempty (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) := finSum_nonempty (Γ.size_pos a b)
  haveI : Nonempty (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2) :=
    finSum_nonempty (Γ.size_pos (a + b) c)
  haveI : Nonempty (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2) :=
    finSum_nonempty (Γ.size_pos (a + b + c) d)
  infer_instance

/-- **The `K`-linear coordinate-evaluation functional**: `GQ1 → D_{a+b+c+d}`,
`m ↦ gq1Collapse m p₀` for a fixed `p₀`. -/
private noncomputable def gq1Proj (p₀ : QIdx K Γ a b c d) :
    GQ1 K Γ a b c d →ₗ[K] (Γ.D (a + b + c + d)).carrier :=
  (LinearMap.proj p₀).comp (gq1Collapse K Γ a b c d).toLinearMap

private theorem gq1Proj_apply (p₀ : QIdx K Γ a b c d) (m : GQ1 K Γ a b c d) :
    gq1Proj K Γ a b c d p₀ m = gq1Collapse K Γ a b c d m p₀ := rfl

/-- **`gq1Proj` is right-`D_{a+b+c+d}`-equivariant.** -/
private theorem gq1Proj_rightSmul (p₀ : QIdx K Γ a b c d)
    (τ : ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ) (m : GQ1 K Γ a b c d) :
    gq1Proj K Γ a b c d p₀ (τ • m) = τ • gq1Proj K Γ a b c d p₀ m := by
  rw [gq1Proj_apply, gq1Proj_apply, gq1Collapse_rightActionEnd K Γ a b c d τ m]

/-- **`gq1Proj` hits `1` at some point `m₀`**: `gq1Collapse`'s own
surjectivity (`Pi.single p₀ 1`, transported back along `.symm`). -/
private theorem gq1Proj_exists_eq_one (p₀ : QIdx K Γ a b c d) :
    ∃ m₀ : GQ1 K Γ a b c d, gq1Proj K Γ a b c d p₀ m₀ = 1 := by
  classical
  refine ⟨(gq1Collapse K Γ a b c d).symm (Pi.single p₀ (1 : (Γ.D (a + b + c + d)).carrier)), ?_⟩
  rw [gq1Proj_apply, LinearEquiv.apply_symm_apply, Pi.single_eq_same]

/-- **`Nontrivial (V1 K Γ a b c d e)`** (M13-3a). -/
theorem quintNontrivial : Nontrivial (V1 K Γ a b c d e) := by
  classical
  obtain ⟨p₀⟩ := qidx_nonempty K Γ a b c d
  obtain ⟨m₀, hm₀⟩ := gq1Proj_exists_eq_one K Γ a b c d p₀
  haveI := fusionColumn_nontrivial K Γ (a + b + c + d) e
  obtain ⟨n₀, hn₀⟩ := exists_ne (0 : FusionColumn (Γ.fuse (a + b + c + d) e))
  set f : GQ1 K Γ a b c d →ₗ[K] FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K]
      FusionColumn (Γ.fuse (a + b + c + d) e) :=
    (Algebra.lsmul K K (FusionColumn (Γ.fuse (a + b + c + d) e))).toLinearMap.comp
      (gq1Proj K Γ a b c d p₀) with hf
  have hbal : RelTensor.IsBalanced (Γ.D (a + b + c + d)).carrier f := by
    intro x m n
    show f (MulOpposite.op x • m) n = f m (x • n)
    rw [hf]
    show (Algebra.lsmul K K (FusionColumn (Γ.fuse (a + b + c + d) e))
        (gq1Proj K Γ a b c d p₀ (MulOpposite.op x • m))) n
      = (Algebra.lsmul K K (FusionColumn (Γ.fuse (a + b + c + d) e))
          (gq1Proj K Γ a b c d p₀ m)) (x • n)
    rw [gq1Proj_rightSmul, op_smul_eq_mul, Algebra.lsmul_apply, Algebra.lsmul_apply,
      mul_smul]
  have hval : RelTensor.lift f hbal
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m₀ n₀) = n₀ := by
    rw [RelTensor.lift_mk]
    show (Algebra.lsmul K K (FusionColumn (Γ.fuse (a + b + c + d) e))
        (gq1Proj K Γ a b c d p₀ m₀)) n₀ = n₀
    rw [hm₀, Algebra.lsmul_apply, one_smul]
  have hmk_ne :
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m₀ n₀ : V1 K Γ a b c d e) ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hval
    exact hn₀ hval.symm
  exact ⟨_, 0, hmk_ne⟩

/-- **`V1` has a nonzero element** (corollary of `quintNontrivial`, for
direct consumption if the `Nontrivial` spelling isn't what the assembly
wants). -/
theorem V1_exists_ne_zero : ∃ x : V1 K Γ a b c d e, x ≠ 0 := by
  haveI := quintNontrivial K Γ a b c d e
  exact exists_ne 0

end Discharge

end GaugeChi

end Superfusion

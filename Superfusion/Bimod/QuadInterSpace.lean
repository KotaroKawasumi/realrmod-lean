/-
Superfusion / Bimod / QuadInterSpace

Milestone M8a-8c′-2c (roadmap v3): **the quadruple intertwiner space**
`Hom(Q1, Q4)` — the stage on which `χ_abs` will be defined
(`E3 ∘ E2 ∘ E1 = χ · (q4Close ∘ E5 ∘ E4)`).  For each parity `e`, the
degree-`e` quadruple intertwiners are the `K`-linear maps `Q1 → Q4`
that are

* homogeneous of degree `e` for the descended gradings (`Q1.grading`,
  `Q4.grading`, M8a-8c′-2a″);
* super-equivariant of degree `e` for each of the *four* slot actions
  of `T_a`, `T_b`, `T_c`, `T_d` (`f (x • m) = (-1)^{e|x|} x • f m` on
  homogeneous `x` — "left super-equivariant", HomGrading.lean's
  `superEquivariant`);
* right-linear along the associativity identification
  `T_{((a+b)+c)+d} ≅ T_{a+(b+c+d)}` of the outer coefficient towers
  (`stdTowerCast`, `Intertwiner.lean`'s cast device) — exactly `Q1`'s
  and `Q4`'s own outer right-coefficient towers (`QuadActions.lean`).

`quadInterSpace K a b c d e` is the intersection of the six submodules
of the general layer (`HomGrading.lean`), assembled exactly as
`Intertwiner.lean`'s triple-level `interSpace`.

This file also records the two route composites

* `topRoute t₁ t₂ t₃ = E3 t₃ ∘ E2 t₂ ∘ E1 t₁ : Q1 → Q4` (the
  left-associated `((ab)c)d`-bracketing path),
* `botRoute t₄ t₅ = q4Close ∘ E5 t₅ ∘ E4 t₄ : Q1 → Q4` (the
  `a(b(cd))`-associated path),

for the hypothesis bundles `E1`–`E5` each already require.  **Their
membership in `quadInterSpace` is deferred**: every edge from `E2`
onward folds its own associator (`q2Assoc`, `q3Assoc`'s inverse,
`q1Assoc`, `q5Swap`) into its generator formula, so its transport laws
(`EdgeEquiv2.lean`–`EdgeEquivClose.lean`) are established only in the
"generator-∀" style sanctioned by the 2026-07-19 method note: for a
generator with a *specific internal factor homogeneous* (e.g. `E2`'s
`u ∈ TowerColumn.grading K b c j`), never for an arbitrary element of
the vertex.  `HomGrading.lean`'s `superEquivariant`/`homGrading`/
`rightSemilinear`, by contrast, quantify over *all* `m : M` — bridging
the two requires new "general layer" Decomposition-induction theorems
for `RelTensor.assoc` (mirroring `MapEquivariance.lean`'s
`map_comp_leftActionEnd`/`map_comp_midEnd` for `RelTensor.map`, or
`SignedMapEquivariance.lean`'s for `smap`), which `RelTensorAssoc.lean`
explicitly defers ("Gradedness and outer-action equivariance of the
associator are deferred to the milestone that needs them") and which
`EdgeEquiv2.lean` explicitly declines to build ("the WARNING-sanctioned
alternative to a full `z : Q2`-universal statement").  Landing that
general layer for `q2Assoc`, `q3Assoc`, `q1Assoc`, `q5Swap` (four more
files comparable in scope to `MapEquivariance.lean`/
`SignedMapEquivariance.lean`) is out of scope for this file; see the
session report for the composite generator-level sign laws as far as
they were traced by hand.
-/
import Superfusion.Bimod.Intertwiner
import Superfusion.Bimod.EdgeEquivClose

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-! ### Scalars commute with the slot and right actions -/

namespace Q1

instance : SMulCommClass K (stdTower (K := K) a).carrier (Q1 K a b c d) :=
  ⟨fun k x w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d) x) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) b).carrier (Q1 K a b c d) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d) y) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) c).carrier (Q1 K a b c d) :=
  ⟨fun k z w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d) z) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) d).carrier (Q1 K a b c d) :=
  ⟨fun k τ w => (LinearMap.map_smul
    (midEnd (stdTower (K := K) (a + b + c)).grading
      (BL.grading K a b c) (stdTower (K := K) d).grading
      (TowerColumn.superCommSMul K (a + b + c) d) τ) k w).symm⟩

instance : SMulCommClass K ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ
    (Q1 K a b c d) :=
  ⟨fun k τ w => (LinearMap.map_smul
    (rightActionEnd K (stdTower (K := K) (a + b + c)).carrier
      (BL K a b c) (TowerColumn K (a + b + c) d) τ) k w).symm⟩

end Q1

namespace Q4

instance : SMulCommClass K (stdTower (K := K) b).carrier (Q4 K a b c d) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d)) y) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) c).carrier (Q4 K a b c d) :=
  ⟨fun k z w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d)) z) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) d).carrier (Q4 K a b c d) :=
  ⟨fun k t w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d)) t) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) a).carrier (Q4 K a b c d) :=
  ⟨fun k x w => (LinearMap.map_smul
    (midEnd (stdTower (K := K) (b + c + d)).grading
      (BR.grading K b c d) (stdTower (K := K) a).grading
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (b + c + d)).grading
        (TowerColumn.superCommSMul K a ((b + c) + d))) x) k w).symm⟩

instance : SMulCommClass K
    ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ (Q4 K a b c d) :=
  ⟨fun k τ w => (LinearMap.map_smul
    (rightActionEnd K (stdTower (K := K) (b + c + d)).carrier
      (BR K b c d) (TowerColumn K a ((b + c) + d)) τ) k w).symm⟩

end Q4

/-! ### The quadruple intertwiner space -/

/-- The associativity recast of the total coefficient algebra between
`Q1`'s outer right-coefficient tower `T_{((a+b)+c)+d}` and `Q4`'s
`T_{a+(b+c+d)}` (matching `EdgeEquiv2.lean`'s `right_recast_eq` and
`EdgeEquiv4.lean`'s `right_recast_eq`, composed). -/
private theorem quadRightCast_eq : a + b + c + d = a + (b + c + d) := by
  ring

/-- **The degree-`e` quadruple intertwiner space** `Hom_e(Q1, Q4)`:
homogeneous of degree `e`, super-equivariant for the four slot
actions, right-linear along the associativity identification of the
outer coefficient towers. -/
noncomputable def quadInterSpace (e : ZMod 2) :
    Submodule K (Q1 K a b c d →ₗ[K] Q4 K a b c d) :=
  homGrading (Q1.grading K a b c d) (Q4.grading K a b c d) e
    ⊓ superEquivariant (stdTower (K := K) a).grading e
    ⊓ superEquivariant (stdTower (K := K) b).grading e
    ⊓ superEquivariant (stdTower (K := K) c).grading e
    ⊓ superEquivariant (stdTower (K := K) d).grading e
    ⊓ rightSemilinear
        ((stdTowerCast (K := K)
          (quadRightCast_eq a b c d)).toAlgEquiv.toAlgHom.toRingHom)

/-- Membership unfolded: the six conditions above. -/
theorem mem_quadInterSpace_iff {e : ZMod 2}
    {f : Q1 K a b c d →ₗ[K] Q4 K a b c d} :
    f ∈ quadInterSpace K a b c d e ↔
      f ∈ homGrading (Q1.grading K a b c d) (Q4.grading K a b c d) e
      ∧ f ∈ superEquivariant (stdTower (K := K) a).grading e
      ∧ f ∈ superEquivariant (stdTower (K := K) b).grading e
      ∧ f ∈ superEquivariant (stdTower (K := K) c).grading e
      ∧ f ∈ superEquivariant (stdTower (K := K) d).grading e
      ∧ f ∈ rightSemilinear
          ((stdTowerCast (K := K)
            (quadRightCast_eq a b c d)).toAlgEquiv.toAlgHom.toRingHom) := by
  show f ∈ (_ ⊓ _ ⊓ _ ⊓ _ ⊓ _ ⊓ _ : Submodule K _) ↔ _
  simp only [Submodule.mem_inf]
  tauto

/-! ### The two route composites -/

/-- **The top route** `E3 ∘ E2 ∘ E1 : Q1 → Q4`, the composite along the
left-associated `((ab)c)d`-bracketing pentagon path, for `t₁` right-
equivariant, `t₂` a spelled generator of parity `e₂` super-equivariant
for the `(b+c)`-slot, and `t₃` right-equivariant (exactly the
hypothesis bundles `E1`, `E2`, `E3` themselves require). -/
noncomputable def topRoute
    (t₁ : BL K a b c →ₗ[K] BR K a b c)
    (ht₁ : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier)
      (m : BL K a b c),
      t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
    (e₂ : ZMod 2) (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
      y ∈ (stdTower (K := K) (b + c)).grading i →
      ∀ n : Q2rInner K a b c d,
        t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
    (t₃ : BL K b c d →ₗ[K] BR K b c d)
    (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier)
      (m : BL K b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m) :
    Q1 K a b c d →ₗ[K] Q4 K a b c d :=
  E3 K a b c d t₃ ht₃ ∘ₗ E2 K a b c d e₂ t₂ ht₂ ∘ₗ E1 K a b c d t₁ ht₁

/-- **The bottom route** `q4Close ∘ E5 ∘ E4 : Q1 → Q4`, the composite
along the `a(b(cd))`-associated pentagon path, for `t₄` a spelled
generator of parity `e₄` super-equivariant for the `(a+b)`-slot, and
`t₅` a spelled generator of parity `e₅` super-equivariant for the
`(c+d)`-slot (exactly the hypothesis bundles `E4`, `E5` themselves
require; `q4Close` needs no intertwiner data at all). -/
noncomputable def botRoute
    (e₄ : ZMod 2) (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i →
      ∀ n : BL K (a + b) c d,
        t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
    (e₅ : ZMod 2) (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i →
      ∀ n : BL K a b (c + d),
        t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n)) :
    Q1 K a b c d →ₗ[K] Q4 K a b c d :=
  (q4Close K a b c d).toLinearMap ∘ₗ
    E5 K a b c d e₅ t₅ ht₅ ∘ₗ E4 K a b c d e₄ t₄ ht₄

end PentagonB

end Bimod

end Superfusion

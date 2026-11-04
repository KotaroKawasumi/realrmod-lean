/-
Superfusion / GaugeChi / PentagonMembership

Milestone M12-4 of the abstract `(p, χ)` arc (continued): **the quadruple
intertwiner space** `gQuadInterSpace Γ a b c d e = Hom_e(GQ1, GQ4)` and the
two route composites `gTopRoute`, `gBotRoute` — the Γ-mirror of
`Superfusion.Bimod.QuadInterSpace`.

For each parity `e`, the degree-`e` quadruple intertwiners are the
`K`-linear maps `GQ1 → GQ4` that are homogeneous of degree `e` for the
descended gradings, super-equivariant of degree `e` for each of the four
slot actions of `D_a`, `D_b`, `D_c`, `D_d`, and right-linear along the
associativity identification `D_{((a+b)+c)+d} ≅ D_{a+(b+c+d)}` of the outer
coefficient towers (`Γ.gaugeCast`) — exactly `GQ1`'s and `GQ4`'s own outer
right-coefficient towers (`GaugeChi.PentagonActions`).

`gTopRoute t₁ t₂ t₃ = GE3 t₃ ∘ GE2 t₂ ∘ GE1 t₁ : GQ1 → GQ4` (the
left-associated `((ab)c)d`-bracketing path) and
`gBotRoute t₄ t₅ = gq4Close ∘ GE5 t₅ ∘ GE4 t₄ : GQ1 → GQ4` (the
`a(b(cd))`-associated path) are recorded for the hypothesis bundles `GE1`–
`GE5` each already require.
-/
import Superfusion.GaugeChi.PentagonEdgeEquiv

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-! ### Scalars commute with the slot and right actions -/

namespace GQ1

instance : SMulCommClass K (Γ.D a).carrier (GQ1 K Γ a b c d) :=
  ⟨fun k x w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (a + b + c)).carrier
      (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) x) k w).symm⟩

instance : SMulCommClass K (Γ.D b).carrier (GQ1 K Γ a b c d) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (a + b + c)).carrier
      (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) y) k w).symm⟩

instance : SMulCommClass K (Γ.D c).carrier (GQ1 K Γ a b c d) :=
  ⟨fun k z w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (a + b + c)).carrier
      (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) z) k w).symm⟩

instance : SMulCommClass K (Γ.D d).carrier (GQ1 K Γ a b c d) :=
  ⟨fun k τ w => (LinearMap.map_smul
    (midEnd (Γ.D (a + b + c)).grading
      (GBL.grading Γ a b c) (Γ.D d).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) τ) k w).symm⟩

instance : SMulCommClass K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ1 K Γ a b c d) :=
  ⟨fun k τ w => (LinearMap.map_smul
    (rightActionEnd K (Γ.D (a + b + c)).carrier
      (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) τ) k w).symm⟩

end GQ1

namespace GQ4

instance : SMulCommClass K (Γ.D b).carrier (GQ4 K Γ a b c d) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (b + c + d)).carrier
      (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))) y) k w).symm⟩

instance : SMulCommClass K (Γ.D c).carrier (GQ4 K Γ a b c d) :=
  ⟨fun k z w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (b + c + d)).carrier
      (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))) z) k w).symm⟩

instance : SMulCommClass K (Γ.D d).carrier (GQ4 K Γ a b c d) :=
  ⟨fun k t w => (LinearMap.map_smul
    (leftActionEnd K (Γ.D (b + c + d)).carrier
      (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))) t) k w).symm⟩

instance : SMulCommClass K (Γ.D a).carrier (GQ4 K Γ a b c d) :=
  ⟨fun k x w => (LinearMap.map_smul
    (midEnd (Γ.D (b + c + d)).grading
      (GBR.grading Γ b c d) (Γ.D a).grading
      (superCommSMul_symm (Γ.D a).grading (Γ.D (b + c + d)).grading
        (FusionColumn.superCommSMul (Γ.fuse a (b + c + d)))) x) k w).symm⟩

instance : SMulCommClass K
    ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ (GQ4 K Γ a b c d) :=
  ⟨fun k τ w => (LinearMap.map_smul
    (rightActionEnd K (Γ.D (b + c + d)).carrier
      (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))) τ) k w).symm⟩

end GQ4

/-! ### The quadruple intertwiner space -/

/-- The associativity recast of the total coefficient algebra between
`GQ1`'s outer right-coefficient tower `D_{((a+b)+c)+d}` and `GQ4`'s
`D_{a+(b+c+d)}` (matching `PentagonEdgeEquiv.lean`'s `GE2`/`GE4`
`right_recast_eq`s, composed). -/
private theorem quadRightCast_eq : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

/-- **The degree-`e` quadruple intertwiner space** `Hom_e(GQ1, GQ4)`:
homogeneous of degree `e`, super-equivariant for the four slot actions,
right-linear along the associativity identification of the outer
coefficient towers. -/
noncomputable def gQuadInterSpace (e : ZMod 2) :
    Submodule K (GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d) :=
  homGrading (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d) e
    ⊓ superEquivariant (Γ.D a).grading e
    ⊓ superEquivariant (Γ.D b).grading e
    ⊓ superEquivariant (Γ.D c).grading e
    ⊓ superEquivariant (Γ.D d).grading e
    ⊓ rightSemilinear
        ((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv.toAlgHom.toRingHom)

/-- Membership unfolded: the six conditions above. -/
theorem mem_gQuadInterSpace_iff {e : ZMod 2}
    {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d} :
    f ∈ gQuadInterSpace K Γ a b c d e ↔
      f ∈ homGrading (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d) e
      ∧ f ∈ superEquivariant (Γ.D a).grading e
      ∧ f ∈ superEquivariant (Γ.D b).grading e
      ∧ f ∈ superEquivariant (Γ.D c).grading e
      ∧ f ∈ superEquivariant (Γ.D d).grading e
      ∧ f ∈ rightSemilinear
          ((Γ.gaugeCast (quadRightCast_eq a b c d)).toAlgEquiv.toAlgHom.toRingHom) := by
  show f ∈ (_ ⊓ _ ⊓ _ ⊓ _ ⊓ _ ⊓ _ : Submodule K _) ↔ _
  simp only [Submodule.mem_inf]
  tauto

/-! ### The two route composites -/

/-- **The top route** `GE3 ∘ GE2 ∘ GE1 : GQ1 → GQ4`, the composite along the
left-associated `((ab)c)d`-bracketing pentagon path, for `t₁` right-
equivariant, `t₂` a spelled generator of parity `e₂` super-equivariant for
the `(b+c)`-slot, and `t₃` right-equivariant (exactly the hypothesis
bundles `GE1`, `GE2`, `GE3` themselves require). -/
noncomputable def gTopRoute
    (t₁ : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (ht₁ : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
    (e₂ : ZMod 2) (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ2rInner K Γ a b c d,
        t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
    (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
    (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m) :
    GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d :=
  GE3 K Γ a b c d t₃ ht₃ ∘ₗ GE2 K Γ a b c d e₂ t₂ ht₂ ∘ₗ GE1 K Γ a b c d t₁ ht₁

/-- **The bottom route** `gq4Close ∘ GE5 ∘ GE4 : GQ1 → GQ4`, the composite
along the `a(b(cd))`-associated pentagon path, for `t₄` a spelled generator
of parity `e₄` super-equivariant for the `(a+b)`-slot, and `t₅` a spelled
generator of parity `e₅` super-equivariant for the `(c+d)`-slot (exactly the
hypothesis bundles `GE4`, `GE5` themselves require; `gq4Close` needs no
intertwiner data at all). -/
noncomputable def gBotRoute
    (e₄ : ZMod 2) (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i →
      ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
    (e₅ : ZMod 2) (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i →
      ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n)) :
    GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d :=
  (gq4Close K Γ a b c d).toLinearMap ∘ₗ
    GE5 K Γ a b c d e₅ t₅ ht₅ ∘ₗ GE4 K Γ a b c d e₄ t₄ ht₄

end GaugeChi

end Superfusion

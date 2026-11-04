/-
Superfusion / Bimod / Intertwiner

Milestone M8a-8a: **the intertwiner space `Hom(B_L, B_R)`** (§4.1).
For each parity `d`, the degree-`d` intertwiners are the `K`-linear
maps `B_L → B_R` that are

* homogeneous of degree `d` for the descended gradings,
* super-equivariant of degree `d` for each of the three slot actions
  of `T_a`, `T_b`, `T_c` (`f (x • m) = (-1)^{d|x|} x • f m` on
  homogeneous `x` — "left super-equivariant"),
* right-linear along the associativity identification
  `T_{(a+b)+c} ≅ T_{a+(b+c)}` of the coefficient algebras
  (`stdTowerCast`, the tower cast).

`interSpace K a b c d` is the intersection of the five submodules of
M8a-8a's general layer.  The paper's Proposition (the space is
one-dimensional, concentrated in the parity `p(a,b,c)`) is the
correspondence-theorem milestone.
-/
import Superfusion.Bimod.RouteBimod
import Superfusion.Bimod.HomGrading

namespace Superfusion

namespace Bimod

/-- Cast of the standard tower along an index equality (public local
replica of the pentagon zone's cast pattern). -/
noncomputable def stdTowerCast {K : Type*} [Field K] [Invertible (2 : K)]
    {x y : ZMod 8} (h : x = y) :
    SuperAlgEquiv (stdTower (K := K) x) (stdTower y) := by
  subst h
  exact SuperAlgEquiv.refl _

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c : ZMod 8)

/-! ### Scalars commute with the slot and right actions -/

namespace BL

instance : SMulCommClass K (stdTower (K := K) a).carrier (BL K a b c) :=
  ⟨fun k x w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (TowerColumn K (a + b) c) x) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) b).carrier (BL K a b c) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (TowerColumn K (a + b) c) y) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) c).carrier (BL K a b c) :=
  ⟨fun k z w => (LinearMap.map_smul
    (midEnd (stdTower (K := K) (a + b)).grading
      (TowerColumn.grading K a b) (stdTower (K := K) c).grading
      (TowerColumn.superCommSMul K (a + b) c) z) k w).symm⟩

instance : SMulCommClass K ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ
    (BL K a b c) :=
  ⟨fun k d w => (LinearMap.map_smul
    (rightActionEnd K (stdTower (K := K) (a + b)).carrier
      (TowerColumn K a b) (TowerColumn K (a + b) c) d) k w).symm⟩

end BL

namespace BR

instance : SMulCommClass K (stdTower (K := K) b).carrier (BR K a b c) :=
  ⟨fun k y w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (TowerColumn K a (b + c)) y) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) c).carrier (BR K a b c) :=
  ⟨fun k z w => (LinearMap.map_smul
    (leftActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (TowerColumn K a (b + c)) z) k w).symm⟩

instance : SMulCommClass K (stdTower (K := K) a).carrier (BR K a b c) :=
  ⟨fun k x w => (LinearMap.map_smul
    (midEnd (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) (stdTower (K := K) a).grading
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (b + c)).grading
        (TowerColumn.superCommSMul K a (b + c))) x) k w).symm⟩

instance : SMulCommClass K
    ((stdTower (K := K) (a + (b + c))).carrier)ᵐᵒᵖ (BR K a b c) :=
  ⟨fun k d w => (LinearMap.map_smul
    (rightActionEnd K (stdTower (K := K) (b + c)).carrier
      (TowerColumn K b c) (TowerColumn K a (b + c)) d) k w).symm⟩

end BR

/-! ### The intertwiner space -/

/-- **The degree-`d` intertwiner space** `Hom_d(B_L, B_R)` (§4.1):
homogeneous of degree `d`, super-equivariant for the three slot
actions, right-linear along the associativity identification of the
coefficient towers. -/
noncomputable def interSpace (d : ZMod 2) :
    Submodule K (BL K a b c →ₗ[K] BR K a b c) :=
  homGrading (BL.grading K a b c) (BR.grading K a b c) d
    ⊓ superEquivariant (stdTower (K := K) a).grading d
    ⊓ superEquivariant (stdTower (K := K) b).grading d
    ⊓ superEquivariant (stdTower (K := K) c).grading d
    ⊓ rightSemilinear
        ((stdTowerCast (K := K)
          (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom)

/-- Membership unfolded: the five conditions of §4.1. -/
theorem mem_interSpace_iff {d : ZMod 2}
    {f : BL K a b c →ₗ[K] BR K a b c} :
    f ∈ interSpace K a b c d ↔
      f ∈ homGrading (BL.grading K a b c) (BR.grading K a b c) d
      ∧ f ∈ superEquivariant (stdTower (K := K) a).grading d
      ∧ f ∈ superEquivariant (stdTower (K := K) b).grading d
      ∧ f ∈ superEquivariant (stdTower (K := K) c).grading d
      ∧ f ∈ rightSemilinear
          ((stdTowerCast (K := K)
            (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom) := by
  show f ∈ (_ ⊓ _ ⊓ _ ⊓ _ ⊓ _ : Submodule K _) ↔ _
  simp only [Submodule.mem_inf]
  tauto

end Bimod

end Superfusion

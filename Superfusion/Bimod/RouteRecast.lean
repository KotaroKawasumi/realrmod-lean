/-
Superfusion / Bimod / RouteRecast

Milestone M8a-8c′-0 (roadmap v3): **recasting the right action of
`B_R`**.  The coefficient algebras of `B_L` and `B_R` are the same
tower fiber spelled differently (`T_{(a+b)+c}` vs `T_{a+(b+c)}`); for
the pentagon's amplifications `map t id` the two sides must be
balanced over literally the same algebra.  This file equips `B_R`
with the right `T_{(a+b)+c}`-action pulled back along the
associativity cast, and shows that for maps `f : B_L → B_R` the
intertwiner condition `rightSemilinear (stdTowerCast …)` of M8a-8a is
literally plain right-equivariance for the recast action — so the
`E`-maps can be built with the unmodified `RelTensor.map`.
-/
import Superfusion.Bimod.Intertwiner

namespace Superfusion

namespace Bimod

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c : ZMod 8)

namespace BR

/-- The right action of the *left-associated* coefficient algebra
`T_{(a+b)+c}` on `B_R`, pulled back along the associativity cast. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ (BR K a b c) :=
  Module.compHom _
    (((stdTowerCast (K := K)
      (add_assoc a b c)).toAlgEquiv.toRingHom).op)

theorem recast_op_smul_def
    (t : (stdTower (K := K) (a + b + c)).carrier) (w : BR K a b c) :
    MulOpposite.op t • w
      = MulOpposite.op ((stdTowerCast (K := K)
          (add_assoc a b c)).toAlgEquiv t) • w := rfl

end BR

/-- Column-level recast: the right `T_{(a+b)+c}`-action on the
coefficients of `C_{a,b+c}` (needed to run the associator across the
`(a(bc))d`-vertex). -/
noncomputable instance : Module
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ
    (TowerColumn K a (b + c)) :=
  Module.compHom _
    (((stdTowerCast (K := K)
      (add_assoc a b c)).toAlgEquiv.toRingHom).op)

theorem column_recast_op_smul_def
    (t : (stdTower (K := K) (a + b + c)).carrier)
    (v : TowerColumn K a (b + c)) :
    MulOpposite.op t • v
      = MulOpposite.op ((stdTowerCast (K := K)
          (add_assoc a b c)).toAlgEquiv t) • v := rfl

/-- The recast slot actions still commute (transported from the
canonical-coefficient instances). -/
instance : SMulCommClass (stdTower (K := K) (b + c)).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ
    (TowerColumn K a (b + c)) :=
  ⟨fun y t v => smul_comm y
    (MulOpposite.op ((stdTowerCast (K := K)
      (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) v⟩

instance : SMulCommClass (stdTower (K := K) a).carrier
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ
    (TowerColumn K a (b + c)) :=
  ⟨fun x t v => smul_comm x
    (MulOpposite.op ((stdTowerCast (K := K)
      (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) v⟩

instance : IsScalarTower K
    ((stdTower (K := K) (a + b + c)).carrier)ᵐᵒᵖ
    (TowerColumn K a (b + c)) :=
  ⟨fun k t v => by
    show (MulOpposite.op ((stdTowerCast (K := K)
        (add_assoc a b c)).toAlgEquiv (MulOpposite.unop (k • t)))) • v
      = k • ((MulOpposite.op ((stdTowerCast (K := K)
          (add_assoc a b c)).toAlgEquiv (MulOpposite.unop t))) • v)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ v⟩

/-- The `B_R`-level recast action is coefficientwise: it acts through
the column-level recast on the second factor. -/
theorem BR.recast_smul_mk
    (t : (stdTower (K := K) (a + b + c)).carrier)
    (u : TowerColumn K b c) (v : TowerColumn K a (b + c)) :
    MulOpposite.op t • BR.mk K a b c u v
      = BR.mk K a b c u (MulOpposite.op t • v) := by
  rw [BR.recast_op_smul_def, BR.right_smul_mk]
  rfl

/-- For `f : B_L → B_R`, the right-semilinearity condition of the
intertwiner space is plain right-equivariance for the recast
action. -/
theorem rightSemilinear_iff_recast_equivariant
    {f : BL K a b c →ₗ[K] BR K a b c} :
    f ∈ rightSemilinear
        ((stdTowerCast (K := K)
          (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom) ↔
      ∀ (t : (stdTower (K := K) (a + b + c)).carrier) (m : BL K a b c),
        f (MulOpposite.op t • m) = MulOpposite.op t • f m :=
  Iff.rfl

/-- The tower cast preserves the grading (a `subst`-`refl` fact). -/
theorem stdTowerCast_mem_grading {x y : ZMod 8} (h : x = y) {i : ZMod 2}
    {τ : (stdTower (K := K) x).carrier}
    (hτ : τ ∈ (stdTower (K := K) x).grading i) :
    (stdTowerCast (K := K) h).toAlgEquiv τ
      ∈ (stdTower (K := K) y).grading i := by
  subst h
  exact hτ

/-! ### Casting a tower column along an index equality -/

/-- Cast of a tower column along an index equality of its second slot
(the `subst`-`refl` pattern of `stdTowerCast`). -/
noncomputable def columnCast {x y : ZMod 8} (h : x = y) :
    TowerColumn K a x ≃ₗ[K] TowerColumn K a y := by
  subst h
  exact LinearEquiv.refl K _

/-- The column cast intertwines the second-slot actions along the
tower cast. -/
theorem columnCast_symm_rslot {x y : ZMod 8} (h : x = y)
    (β : (stdTower (K := K) y).carrier) (v : TowerColumn K a y) :
    columnCast K a h.symm (β • v)
      = ((stdTowerCast (K := K) h).toAlgEquiv.symm β) •
          columnCast K a h.symm v := by
  subst h
  rfl

/-- The inverse column cast intertwines the second-slot actions along
the tower cast. -/
theorem columnCast_symm_symm_rslot {x y : ZMod 8} (h : x = y)
    (t : (stdTower (K := K) x).carrier) (w : TowerColumn K a x) :
    (columnCast K a h.symm).symm (t • w)
      = ((stdTowerCast (K := K) h).toAlgEquiv t) •
          (columnCast K a h.symm).symm w := by
  subst h
  rfl

end Bimod

end Superfusion

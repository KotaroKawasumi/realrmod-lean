import RMod.BrundanEllis.Parity
import RMod.Hierarchy.Bridge.LegacyInterchange
import RMod.Hierarchy.Bridge.LegacyNaturality
import RMod.Hierarchy.Bridge.LegacyCoherence

/-! Parity comparison laws need only the monoidal supercategory and an odd
inverse pair. In particular they do not assume fusion, graded Schur or the
classification theorem that will eventually use the parity shift. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.BrundanEllisParity
open RMod.Legacy RMod.Legacy.Hierarchy
-- These local unfolding hints affect elaboration only; the kernel still checks every proof.
set_option allowUnsafeReducibility true
attribute [local reducible] RMod.Legacy.MonoidalSupercategory.super
  RMod.Legacy.Hierarchy.toOldData RMod.Classification.PiData.shiftObj
  RMod.Classification.PiData.shiftHom RMod.Classification.PiData.zHom
  RMod.Classification.PiData.zInv RMod.Legacy.TotalCategory RMod.Legacy.superTensorProductData

variable (C : RMod.Legacy.MonoidalSupercategory)
  (p : RMod.Classification.Pi (toOldData C))

/-- Tensoring the odd inverse pair with an even identity introduces no sign. -/
theorem tensor_hom_inv (X : C.data.Obj) :
    tComp C.super.data (legacyTensor C p.data.hom (evenPoint (C.data.id X)))
      (legacyTensor C p.data.inv (evenPoint (C.data.id X))) =
        evenPoint (C.data.id ((toOldData C).tensorObj p.data.object X)) := by
  erw [legacyTensor_interchange C 1 0 _ _ _ _ p.laws.hom_odd
    (evenPoint_mem_grade C.super (C.data.id X))]
  simp only [zero_mul, ZMod.val_zero, pow_zero, one_smul]
  have hp : tComp C.super.data p.data.hom p.data.inv =
      evenPoint (C.data.id p.data.object) := p.laws.hom_inv
  erw [hp, tComp_id_right C.super]
  exact legacyTensor_id C p.data.object X

theorem tensor_inv_hom (X : C.data.Obj) :
    tComp C.super.data (legacyTensor C p.data.inv (evenPoint (C.data.id X)))
      (legacyTensor C p.data.hom (evenPoint (C.data.id X))) =
        evenPoint (C.data.id ((toOldData C).tensorObj (toOldData C).tensorUnit X)) := by
  erw [legacyTensor_interchange C 1 0 _ _ _ _ p.laws.inv_odd
    (evenPoint_mem_grade C.super (C.data.id X))]
  simp only [zero_mul, ZMod.val_zero, pow_zero, one_smul]
  have hp : tComp C.super.data p.data.inv p.data.hom =
      evenPoint (C.data.id C.data.monoidal.unit) := p.laws.inv_hom
  erw [hp, tComp_id_right C.super]
  exact legacyTensor_id C (toOldData C).tensorUnit X

/-- The unitors and the odd inverse pair give the objectwise shift isomorphism. -/
theorem z_hom_inv (X : C.data.Obj) :
    tComp C.super.data (p.data.zHom X) (p.data.zInv X) =
      evenPoint (C.data.id (p.data.shiftObj X)) := by
  change tComp C.super.data
    (tComp C.super.data (legacyTensor C p.data.hom (evenPoint (C.data.id X)))
      (evenPoint (C.data.monoidal.leftHom X)))
    (tComp C.super.data (evenPoint (C.data.monoidal.leftInv X))
      (legacyTensor C p.data.inv (evenPoint (C.data.id X)))) = _
  erw [tComp_assoc C.super, ← tComp_assoc C.super (evenPoint (C.data.monoidal.leftHom X)),
    ← evenPoint_comp, C.laws.monoidal.left_hom_inv,
    tComp_id_left C.super]
  exact tensor_hom_inv C p X

theorem z_inv_hom (X : C.data.Obj) :
    tComp C.super.data (p.data.zInv X) (p.data.zHom X) =
      evenPoint (C.data.id X) := by
  change tComp C.super.data
    (tComp C.super.data (evenPoint (C.data.monoidal.leftInv X))
      (legacyTensor C p.data.inv (evenPoint (C.data.id X))))
    (tComp C.super.data (legacyTensor C p.data.hom (evenPoint (C.data.id X)))
      (evenPoint (C.data.monoidal.leftHom X))) = _
  erw [tComp_assoc C.super, ← tComp_assoc C.super (legacyTensor C p.data.inv _),
    tensor_inv_hom, tComp_id_left C.super, ← evenPoint_comp, C.laws.monoidal.left_inv_hom]

/-- Both parity comparison components remain homogeneous of odd degree. -/
theorem z_hom_odd (X : C.data.Obj) :
    p.data.zHom X ∈ grade C.super (p.data.shiftObj X) X 1 := by
  have ht := legacyTensor_mem_grade C p.data.hom (evenPoint (C.data.id X))
    p.laws.hom_odd (evenPoint_mem_grade C.super (C.data.id X))
  have hc := tComp_mem_grade C.super _ _ ht
    (evenPoint_mem_grade C.super (C.data.monoidal.leftHom X))
  simp only [add_zero] at hc
  exact hc

theorem z_inv_odd (X : C.data.Obj) :
    p.data.zInv X ∈ grade C.super X (p.data.shiftObj X) 1 := by
  have ht := legacyTensor_mem_grade C p.data.inv (evenPoint (C.data.id X))
    p.laws.inv_odd (evenPoint_mem_grade C.super (C.data.id X))
  have hc := tComp_mem_grade C.super _ _
    (evenPoint_mem_grade C.super (C.data.monoidal.leftInv X)) ht
  simp only [add_zero, zero_add] at hc
  exact hc

/-! The odd naturality sign is obtained from interchange, rather than assumed. -/
theorem z_shift_comp {X Y : C.data.Obj} (f : THom C.super.data X Y) :
    tComp C.super.data (p.data.shiftHom f) (p.data.zHom Y) =
      tComp C.super.data (legacyTensor C p.data.hom f)
        (evenPoint (C.data.monoidal.leftHom Y)) := by
  change tComp C.super.data (legacyTensor C (evenPoint (C.data.id p.data.object)) f)
    (tComp C.super.data (legacyTensor C p.data.hom (evenPoint (C.data.id Y)))
      (evenPoint (C.data.monoidal.leftHom Y))) = _
  erw [← tComp_assoc C.super, legacyTensor_interchange C 0 0 _ _ _ _
    (evenPoint_mem_grade C.super (C.data.id p.data.object))
    (evenPoint_mem_grade C.super (C.data.id Y))]
  simp only [mul_zero, ZMod.val_zero, pow_zero, one_smul]
  erw [tComp_id_left C.super, tComp_id_right C.super]

theorem z_comp {X Y : C.data.Obj} (a : ZMod 2) (f : THom C.super.data X Y)
    (hf : f ∈ grade C.super X Y a) :
    tComp C.super.data (p.data.zHom X) f =
      (-1 : ℝ) ^ a.val • tComp C.super.data (p.data.shiftHom f) (p.data.zHom Y) := by
  erw [z_shift_comp C p]
  change tComp C.super.data
    (tComp C.super.data (legacyTensor C p.data.hom (evenPoint (C.data.id X)))
      (evenPoint (C.data.monoidal.leftHom X))) f = _
  erw [tComp_assoc C.super, ← legacyLeftNaturality C f, ← tComp_assoc C.super,
    legacyTensor_interchange C 1 a _ _ _ _ p.laws.hom_odd hf]
  simp only [mul_one]
  erw [tComp_id_right C.super, tComp_id_left C.super, tComp_smul_left]

theorem z_naturality {X Y : C.data.Obj} (a : ZMod 2) (f : THom C.super.data X Y)
    (hf : f ∈ grade C.super X Y a) :
    tComp C.super.data (p.data.shiftHom f) (p.data.zHom Y) =
      (-1 : ℝ) ^ a.val • tComp C.super.data (p.data.zHom X) f := by
  erw [z_comp C p a f hf, smul_smul, RMod.Classification.Calculus.sign_square, one_smul]

end RMod.Legacy.BrundanEllisParity

import RMod.Classification.Abstract.Normalizers
import RMod.Classification.Proofs.Parity

/-!
# Parity isomorphisms in an arbitrary reference category

The proofs use only the given category laws and the specified odd inverse
pair. In particular the odd naturality sign is checked on Hom operations;
it is not inferred from an object-level identification.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

namespace PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

/-! Parity transport is expressed entirely in the given category's maps. -/

def shiftObj (X : C.Obj) : C.Obj := C.tensorObj p.object X

def shiftHom {X Y : C.Obj} (f : C.Hom X Y) :
    C.Hom (p.shiftObj X) (p.shiftObj Y) := C.tensorHom (C.id p.object) f

def zHom (X : C.Obj) : C.Hom (p.shiftObj X) X :=
  C.comp (C.tensorHom p.hom (C.id X)) (C.leftUnitorHom X)

def zInv (X : C.Obj) : C.Hom X (p.shiftObj X) :=
  C.comp (C.leftUnitorInv X) (C.tensorHom p.inv (C.id X))

/-- The even comparison `Π² X → X`, in diagrammatic composition order. -/
def squareHom (X : C.Obj) : C.Hom (p.shiftObj (p.shiftObj X)) X :=
  C.comp (p.zHom (p.shiftObj X)) (p.zHom X)

def squareInv (X : C.Obj) : C.Hom X (p.shiftObj (p.shiftObj X)) :=
  C.comp (p.zInv X) (p.zInv (p.shiftObj X))

end PiData


variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C)

include hC

namespace Calculus

theorem comp_four {W X Y Z T : C.Obj} (f : C.Hom W X) (g : C.Hom X Y)
    (h : C.Hom Y Z) (i : C.Hom Z T) :
    C.comp (C.comp f g) (C.comp h i) = C.comp (C.comp f (C.comp g h)) i := by
  simp only [hC.comp_assoc]

omit hC in
theorem sign_square (a : ZMod 2) : ((-1 : ℝ) ^ a.val) * ((-1 : ℝ) ^ a.val) = 1 := by
  rw [← mul_pow]
  simp

theorem sign_smul_sign {X Y : C.Obj} (a : ZMod 2) (f : C.Hom X Y) :
    C.smul ((-1 : ℝ) ^ a.val) (C.smul ((-1 : ℝ) ^ a.val) f) = f := by
  rw [← hC.mul_smul, sign_square, hC.one_smul]

/-- Identify additive negation with multiplication by the real scalar -1. -/
theorem neg_as_smul {X Y : C.Obj} (f : C.Hom X Y) : C.neg f = C.smul (-1) f := by
  have hz : C.add (C.smul (-1) f) f = C.zero := by
    calc
      _ = C.add (C.smul (-1) f) (C.smul 1 f) := by rw [hC.one_smul]
      _ = C.smul ((-1 : ℝ) + 1) f := (hC.add_smul _ _ f).symm
      _ = C.zero := by rw [neg_add_cancel, hC.zero_smul]
  calc
    C.neg f = C.add (C.neg f) C.zero := (hC.add_zero _).symm
    _ = C.add (C.neg f) (C.add (C.smul (-1) f) f) := by rw [hz]
    _ = C.add (C.add (C.neg f) f) (C.smul (-1) f) := by
      rw [hC.add_comm (C.smul (-1) f) f, ← hC.add_assoc]
    _ = C.smul (-1) f := by rw [hC.neg_add, hC.zero_add]

end Calculus

namespace IsoLaws

theorem refl (X : C.Obj) : IsoLaws C (IsoData.refl C X) :=
  ⟨hC.comp_id _, hC.comp_id _⟩

omit hC in
theorem symm {X Y : C.Obj} {d : IsoData C X Y} (hd : IsoLaws C d) :
    IsoLaws C (d.symm C) := ⟨hd.inv_hom, hd.hom_inv⟩

theorem trans {X Y Z : C.Obj} {d : IsoData C X Y} {e : IsoData C Y Z}
    (hd : IsoLaws C d) (he : IsoLaws C e) : IsoLaws C (d.trans C e) := by
  constructor
  · change C.comp (C.comp d.hom e.hom) (C.comp e.inv d.inv) = _
    rw [Calculus.comp_four hC, he.hom_inv, hC.comp_id, hd.hom_inv]
  · change C.comp (C.comp e.inv d.inv) (C.comp d.hom e.hom) = _
    rw [Calculus.comp_four hC, hd.inv_hom, hC.comp_id, he.inv_hom]

theorem leftUnit (X : C.Obj) : IsoLaws C (IsoData.leftUnit C X) :=
  ⟨hC.left_unitor_hom_inv X, hC.left_unitor_inv_hom X⟩

theorem rightUnit (X : C.Obj) : IsoLaws C (IsoData.rightUnit C X) :=
  ⟨hC.right_unitor_hom_inv X, hC.right_unitor_inv_hom X⟩

end IsoLaws

namespace PiLaws

variable {p : PiData C} (hp : PiLaws C p)

include hp

/-! Tensoring the odd inverse pair with an identity produces no sign. -/

theorem tensor_hom_inv (X : C.Obj) :
    C.comp (C.tensorHom p.hom (C.id X)) (C.tensorHom p.inv (C.id X)) =
      C.id (C.tensorObj p.object X) := by
  rw [hC.super_interchange _ _ _ _ (hC.id_even X) hp.hom_odd]
  simp only [zero_mul, ZMod.val_zero, pow_zero, hC.one_smul,
    hp.hom_inv, hC.comp_id, hC.tensor_id]

theorem tensor_inv_hom (X : C.Obj) :
    C.comp (C.tensorHom p.inv (C.id X)) (C.tensorHom p.hom (C.id X)) =
      C.id (C.tensorObj C.tensorUnit X) := by
  rw [hC.super_interchange _ _ _ _ (hC.id_even X) hp.inv_odd]
  simp only [zero_mul, ZMod.val_zero, pow_zero, hC.one_smul,
    hp.inv_hom, hC.comp_id, hC.tensor_id]

/-- `z_X : ΠX → X` has the explicitly specified inverse. -/
theorem z_iso (X : C.Obj) : IsoLaws C (⟨p.zHom X, p.zInv X⟩ : IsoData C _ _) := by
  constructor
  · change C.comp (C.comp (C.tensorHom p.hom (C.id X)) (C.leftUnitorHom X))
      (C.comp (C.leftUnitorInv X) (C.tensorHom p.inv (C.id X))) =
      C.id (C.tensorObj p.object X)
    rw [Calculus.comp_four hC,
      hC.left_unitor_hom_inv, hC.comp_id, hp.tensor_hom_inv hC]
  · change C.comp (C.comp (C.leftUnitorInv X) (C.tensorHom p.inv (C.id X)))
      (C.comp (C.tensorHom p.hom (C.id X)) (C.leftUnitorHom X)) = C.id X
    rw [Calculus.comp_four hC,
      hp.tensor_inv_hom hC, hC.comp_id, hC.left_unitor_inv_hom]

theorem z_hom_odd (X : C.Obj) : C.IsHomogeneous 1 (p.zHom X) := by
  change C.comp (C.tensorHom p.hom (C.id X)) (C.leftUnitorHom X) ∈
    C.grade (C.tensorObj p.object X) X 1
  have ht := hC.tensor_grade p.hom (C.id X) hp.hom_odd (hC.id_even X)
  have hc := hC.comp_grade _ _ ht (hC.left_unitor_hom_even X)
  simpa only [add_zero] using hc

theorem z_inv_odd (X : C.Obj) : C.IsHomogeneous 1 (p.zInv X) := by
  change C.comp (C.leftUnitorInv X) (C.tensorHom p.inv (C.id X)) ∈
    C.grade X (C.tensorObj p.object X) 1
  have ht := hC.tensor_grade p.inv (C.id X) hp.inv_odd (hC.id_even X)
  have hc := hC.comp_grade _ _ (hC.left_unitor_inv_even X) ht
  simpa only [add_zero, zero_add] using hc

/-! Naturality with an odd component has the supernatural sign. -/

omit hp in
theorem z_shift_comp {X Y : C.Obj} (f : C.Hom X Y) :
    C.comp (p.shiftHom f) (p.zHom Y) = C.comp (C.tensorHom p.hom f) (C.leftUnitorHom Y) := by
  dsimp only [PiData.shiftHom, PiData.zHom, PiData.shiftObj]
  rw [← hC.comp_assoc,
    hC.super_interchange _ _ _ _ (hC.id_even Y) (hC.id_even p.object)]
  simp only [zero_mul, ZMod.val_zero, pow_zero, hC.one_smul,
    hC.id_comp, hC.comp_id]

theorem z_comp {X Y : C.Obj} {a : ZMod 2} (f : C.Hom X Y)
    (hf : C.IsHomogeneous a f) :
    C.comp (p.zHom X) f =
      C.smul ((-1 : ℝ) ^ a.val) (C.comp (p.shiftHom f) (p.zHom Y)) := by
  rw [z_shift_comp hC]
  dsimp only [PiData.zHom, PiData.shiftObj]
  rw [hC.comp_assoc, ← hC.left_unitor_naturality f,
    ← hC.comp_assoc]
  rw [hC.super_interchange _ _ _ _ hf hp.hom_odd]
  simp only [mul_one, hC.comp_id, hC.id_comp, hC.smul_comp]

/-- Naturality in exactly the direction of equation (Π) in the manuscript. -/
theorem z_naturality {X Y : C.Obj} {a : ZMod 2} (f : C.Hom X Y)
    (hf : C.IsHomogeneous a f) :
    C.comp (p.shiftHom f) (p.zHom Y) =
      C.smul ((-1 : ℝ) ^ a.val) (C.comp (p.zHom X) f) := by
  rw [hp.z_comp hC f hf, Calculus.sign_smul_sign hC]

/-- Π-completeness follows with an actual selected shifted object. -/
theorem has_odd_shift (X : C.Obj) : C.HasHomogeneousIso 1 (p.shiftObj X) X :=
  ⟨p.zHom X, p.zInv X, (hp.z_iso hC X).hom_inv,
    (hp.z_iso hC X).inv_hom, hp.z_hom_odd hC X, hp.z_inv_odd hC X⟩

/-! The double shift is evenly isomorphic to the original object. -/

theorem square_iso (X : C.Obj) :
    IsoLaws C (⟨p.squareHom X, p.squareInv X⟩ : IsoData C _ _) :=
  IsoLaws.trans hC (hp.z_iso hC (p.shiftObj X)) (hp.z_iso hC X)

theorem square_hom_even (X : C.Obj) : C.IsHomogeneous 0 (p.squareHom X) := by
  have h := hC.comp_grade _ _ (hp.z_hom_odd hC (p.shiftObj X)) (hp.z_hom_odd hC X)
  simpa only [CharTwo.add_self_eq_zero, WeaklyPointedSuperfusionData.IsHomogeneous,
    PiData.squareHom] using h

theorem square_inv_even (X : C.Obj) : C.IsHomogeneous 0 (p.squareInv X) := by
  have h := hC.comp_grade _ _ (hp.z_inv_odd hC X) (hp.z_inv_odd hC (p.shiftObj X))
  simpa only [CharTwo.add_self_eq_zero, WeaklyPointedSuperfusionData.IsHomogeneous,
    PiData.squareInv] using h

/-! Two odd tensor factors produce a minus sign; the chosen contraction
has precisely the compensating minus sign. -/

theorem contraction_iso :
    IsoLaws C (⟨p.contractionHom, p.contractionInv⟩ : IsoData C _ _) := by
  have hf : C.comp (C.tensorHom p.hom p.hom) (C.tensorHom p.inv p.inv) =
      C.smul (-1) (C.id (C.tensorObj p.object p.object)) := by
    rw [hC.super_interchange _ _ _ _ hp.inv_odd hp.hom_odd]
    simp only [one_mul, ZMod.val_one, pow_one, hp.hom_inv, hC.tensor_id]
  have hi : C.comp (C.tensorHom p.inv p.inv) (C.tensorHom p.hom p.hom) =
      C.smul (-1) (C.id (C.tensorObj C.tensorUnit C.tensorUnit)) := by
    rw [hC.super_interchange _ _ _ _ hp.hom_odd hp.inv_odd]
    simp only [one_mul, ZMod.val_one, pow_one, hp.inv_hom, hC.tensor_id]
  constructor
  · change C.comp (p.contractionHom) (p.contractionInv) = _
    dsimp only [PiData.contractionHom, PiData.contractionInv]
    rw [Calculus.neg_as_smul hC, hC.smul_comp, Calculus.comp_four hC,
      hC.left_unitor_hom_inv, hC.comp_id, hf, ← hC.mul_smul]
    simp only [neg_mul_neg, one_mul, hC.one_smul]
  · change C.comp (p.contractionInv) (p.contractionHom) = _
    dsimp only [PiData.contractionHom, PiData.contractionInv]
    rw [Calculus.neg_as_smul hC, hC.comp_smul, Calculus.comp_four hC,
      hi, hC.comp_smul, hC.comp_id, hC.smul_comp,
      hC.left_unitor_inv_hom, ← hC.mul_smul]
    simp only [neg_mul_neg, one_mul, hC.one_smul]

theorem contraction_hom_even : C.IsHomogeneous 0 p.contractionHom := by
  change C.neg (C.comp (C.tensorHom p.hom p.hom)
    (C.leftUnitorHom C.tensorUnit)) ∈ C.grade _ _ 0
  apply hC.grade_neg
  have ht := hC.tensor_grade _ _ hp.hom_odd hp.hom_odd
  have hc := hC.comp_grade _ _ ht (hC.left_unitor_hom_even C.tensorUnit)
  simpa only [CharTwo.add_self_eq_zero, zero_add] using hc

theorem contraction_inv_even : C.IsHomogeneous 0 p.contractionInv := by
  change C.comp (C.leftUnitorInv C.tensorUnit) (C.tensorHom p.inv p.inv) ∈ C.grade _ _ 0
  have ht := hC.tensor_grade _ _ hp.inv_odd hp.inv_odd
  have hc := hC.comp_grade _ _ (hC.left_unitor_inv_even C.tensorUnit) ht
  simpa only [CharTwo.add_self_eq_zero, zero_add] using hc

/-! The central comparison has two odd factors, so it is even. -/

theorem central_iso (X : C.Obj) :
    IsoLaws C (⟨p.centralHom X, p.centralInv X⟩ : IsoData C _ _) := by
  have ht : IsoLaws C
      (⟨C.tensorHom (C.id X) p.inv, C.tensorHom (C.id X) p.hom⟩ : IsoData C _ _) := by
    constructor
    · change C.comp (C.tensorHom (C.id X) p.inv) (C.tensorHom (C.id X) p.hom) = _
      rw [hC.super_interchange _ _ _ _ hp.hom_odd (hC.id_even X)]
      simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul,
        hC.comp_id, hp.inv_hom, hC.tensor_id]
    · change C.comp (C.tensorHom (C.id X) p.hom) (C.tensorHom (C.id X) p.inv) = _
      rw [hC.super_interchange _ _ _ _ hp.inv_odd (hC.id_even X)]
      simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul,
        hC.comp_id, hp.hom_inv, hC.tensor_id]
  have he := IsoLaws.trans hC (hp.z_iso hC X)
    (IsoLaws.trans hC (IsoLaws.symm (IsoLaws.rightUnit hC X)) ht)
  constructor
  · change C.comp (p.centralHom X) (p.centralInv X) = C.id (C.tensorObj p.object X)
    dsimp only [PiData.centralHom, PiData.centralInv, PiData.zHom, PiData.zInv, PiData.shiftObj]
    have hh := he.hom_inv
    dsimp only [IsoData.trans, IsoData.symm, IsoData.rightUnit,
      PiData.zHom, PiData.zInv, PiData.shiftObj] at hh
    simpa only [hC.comp_assoc] using hh
  · change C.comp (p.centralInv X) (p.centralHom X) = C.id (C.tensorObj X p.object)
    dsimp only [PiData.centralHom, PiData.centralInv, PiData.zHom, PiData.zInv, PiData.shiftObj]
    have hh := he.inv_hom
    dsimp only [IsoData.trans, IsoData.symm, IsoData.rightUnit,
      PiData.zHom, PiData.zInv, PiData.shiftObj] at hh
    simpa only [hC.comp_assoc] using hh

theorem central_hom_even (X : C.Obj) : C.IsHomogeneous 0 (p.centralHom X) := by
  change C.comp (p.zHom X)
    (C.comp (C.rightUnitorInv X) (C.tensorHom (C.id X) p.inv)) ∈ C.grade _ _ 0
  have ht := hC.tensor_grade _ _ (hC.id_even X) hp.inv_odd
  have hr := hC.comp_grade _ _ (hC.right_unitor_inv_even X) ht
  have hc := hC.comp_grade _ _ (hp.z_hom_odd hC X) hr
  simpa only [zero_add, CharTwo.add_self_eq_zero] using hc

theorem central_inv_even (X : C.Obj) : C.IsHomogeneous 0 (p.centralInv X) := by
  change C.comp (C.tensorHom (C.id X) p.hom)
    (C.comp (C.rightUnitorHom X) (p.zInv X)) ∈ C.grade _ _ 0
  have ht := hC.tensor_grade _ _ (hC.id_even X) hp.hom_odd
  have hr := hC.comp_grade _ _ (hC.right_unitor_hom_even X) (hp.z_inv_odd hC X)
  have hc := hC.comp_grade _ _ ht hr
  simpa only [zero_add, CharTwo.add_self_eq_zero] using hc

end PiLaws
end RMod.Classification

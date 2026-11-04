import RMod.Classification.Proofs.IsoCalculus

/-!
# Endpoint equality maps for a retained raw morphism

Heterogeneous equality of raw maps gives the actual commuting square with
the specified endpoint equality isomorphisms. Equality elimination reduces
the square to the original map and its identity compositions.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

theorem isoData_ofEq_inv_eq {C : WeaklyPointedSuperfusionData.{u, v}}
    {X Y : C.Obj} (e : X = Y) : (IsoData.ofEq C e).inv = (IsoData.ofEq C e.symm).hom := by
  cases e
  rfl

theorem rawHom_heq_square {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {X X' Y Y' : C.Obj}
    (eX : X = X') (eY : Y = Y') {f : C.Hom X Y} {q : C.Hom X' Y'} (he : HEq f q) :
    C.comp f (IsoData.ofEq C eY).hom = C.comp (IsoData.ofEq C eX).hom q := by
  cases eX
  cases eY
  cases he
  exact (hC.comp_id _).trans (hC.id_comp _).symm

theorem rawHom_comp_ofEq_heq {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {X Y Y' : C.Obj}
    (f : C.Hom X Y) (e : Y = Y') : HEq (C.comp f (IsoData.ofEq C e).hom) f := by
  cases e
  exact heq_of_eq (hC.comp_id f)

theorem rawHom_ofEq_comp_heq {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {X X' Y : C.Obj}
    (e : X = X') (f : C.Hom X' Y) : HEq (C.comp (IsoData.ofEq C e).hom f) f := by
  cases e
  exact heq_of_eq (hC.id_comp f)

theorem rawHom_comp_heq {C : WeaklyPointedSuperfusionData.{u, v}}
    {X X' Y Y' Z Z' : C.Obj} (eX : X = X') (eY : Y = Y') (eZ : Z = Z')
    {f : C.Hom X Y} {f' : C.Hom X' Y'} {q : C.Hom Y Z} {q' : C.Hom Y' Z'}
    (hf : HEq f f') (hq : HEq q q') : HEq (C.comp f q) (C.comp f' q') := by
  cases eX
  cases eY
  cases eZ
  cases hf
  cases hq
  rfl

theorem rawHom_tensor_heq {C : WeaklyPointedSuperfusionData.{u, v}}
    {X X' Y Y' Z Z' W W' : C.Obj}
    (eX : X = X') (eY : Y = Y') (eZ : Z = Z') (eW : W = W')
    {f : C.Hom X Y} {f' : C.Hom X' Y'} {q : C.Hom Z W} {q' : C.Hom Z' W'}
    (hf : HEq f f') (hq : HEq q q') : HEq (C.tensorHom f q) (C.tensorHom f' q') := by
  cases eX
  cases eY
  cases eZ
  cases eW
  cases hf
  cases hq
  rfl

theorem rawHom_smul_heq {C : WeaklyPointedSuperfusionData.{u, v}}
    {X X' Y Y' : C.Obj} (eX : X = X') (eY : Y = Y') (r : ℝ)
    {f : C.Hom X Y} {f' : C.Hom X' Y'} (hf : HEq f f') :
    HEq (C.smul r f) (C.smul r f') := by
  cases eX
  cases eY
  cases hf
  rfl

theorem rawEq_comp_inv_assoc {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {X Y Z W : C.Obj}
    (e : X = Y) (e' : Z = Y) (f : C.Hom Z W) :
    C.comp (IsoData.ofEq C e).hom (C.comp (IsoData.ofEq C e').inv f) =
      C.comp (IsoData.ofEq C (e.trans e'.symm)).hom f := by
  cases e
  cases e'
  exact hC.id_comp _

end RMod.Classification

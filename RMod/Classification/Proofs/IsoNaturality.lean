import RMod.Classification.Proofs.IsoCalculus

/-!
# Naturality calculus for specified even comparisons

Commutative squares compose, invert, and tensor. For tensoring, evenness
of the structural comparisons removes the interchange signs while the
horizontal maps remain arbitrary, including inhomogeneous maps. This
provides naturality for normalizers on the full supercategory.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem iso_naturality_refl {X Y : C.Obj} (f : C.Hom X Y) :
    C.comp f (IsoData.refl C Y).hom = C.comp (IsoData.refl C X).hom f := by
  exact (hC.comp_id f).trans (hC.id_comp f).symm

theorem iso_naturality_constant {X Y : C.Obj} (d : IsoData C X Y) :
    C.comp (C.id X) d.hom = C.comp d.hom (C.id Y) := by
  rw [hC.id_comp, hC.comp_id]

theorem iso_naturality_trans {X Y Z X' Y' Z' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    {e : IsoData C Y Z} {e' : IsoData C Y' Z'}
    {f : C.Hom X X'} {g : C.Hom Y Y'} {h : C.Hom Z Z'}
    (hd : C.comp f d'.hom = C.comp d.hom g)
    (he : C.comp g e'.hom = C.comp e.hom h) :
    C.comp f (d'.trans C e').hom = C.comp (d.trans C e).hom h := by
  change C.comp f (C.comp d'.hom e'.hom) = C.comp (C.comp d.hom e.hom) h
  rw [← hC.comp_assoc, hd, hC.comp_assoc, he, ← hC.comp_assoc]

theorem iso_naturality_symm {X Y X' Y' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    (hd : IsoLaws C d) (hd' : IsoLaws C d')
    {f : C.Hom X X'} {g : C.Hom Y Y'}
    (he : C.comp f d'.hom = C.comp d.hom g) :
    C.comp g (d'.symm C).hom = C.comp (d.symm C).hom f := by
  change C.comp g d'.inv = C.comp d.inv f
  have hh := congrArg (fun q => C.comp d.inv (C.comp q d'.inv)) he
  simpa only [hC.comp_assoc, hd'.hom_inv, hC.comp_id,
    ← hC.comp_assoc d.inv d.hom, hd.inv_hom, hC.id_comp] using hh.symm

theorem iso_naturality_tensor {X Y Z W X' Y' Z' W' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    {e : IsoData C Z W} {e' : IsoData C Z' W'}
    (hd : EvenIsoLaws C d) (he' : EvenIsoLaws C e')
    {f : C.Hom X X'} {g : C.Hom Y Y'} {h : C.Hom Z Z'} {k : C.Hom W W'}
    (hdn : C.comp f d'.hom = C.comp d.hom g)
    (hen : C.comp h e'.hom = C.comp e.hom k) :
    C.comp (C.tensorHom f h) (d'.tensor C e').hom =
      C.comp (d.tensor C e).hom (C.tensorHom g k) := by
  change C.comp (C.tensorHom f h) (C.tensorHom d'.hom e'.hom) =
    C.comp (C.tensorHom d.hom e.hom) (C.tensorHom g k)
  rw [interchange_second_even hC _ _ _ _ he'.hom_even,
    interchange_first_even hC _ _ _ _ hd.hom_even, hdn, hen]

theorem iso_naturality_whiskerRight {X Y X' Y' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'} (hd : EvenIsoLaws C d)
    {f : C.Hom X X'} {g : C.Hom Y Y'}
    (he : C.comp f d'.hom = C.comp d.hom g) (Q : C.Obj) :
    C.comp (C.tensorHom f (C.id Q)) (d'.tensor C (IsoData.refl C Q)).hom =
      C.comp (d.tensor C (IsoData.refl C Q)).hom (C.tensorHom g (C.id Q)) :=
  iso_naturality_tensor hC hd (EvenIsoLaws.refl hC Q) he (iso_naturality_refl hC (C.id Q))

theorem iso_naturality_scale {X Y X' Y' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    {f : C.Hom X X'} {g : C.Hom Y Y'}
    (he : C.comp f d'.hom = C.comp d.hom g) (r : ℝˣ) :
    C.comp f (d'.scale C r).hom = C.comp (d.scale C r).hom g := by
  change C.comp f (C.smul r.val d'.hom) = C.comp (C.smul r.val d.hom) g
  rw [hC.comp_smul, hC.smul_comp, he]

theorem iso_naturality_tensor_ofEq {P Q X Y : C.Obj} (he : P = Q) (f : C.Hom X Y) :
    C.comp (C.tensorHom f (C.id P))
      (IsoData.ofEq C (congrArg (C.tensorObj Y) he)).hom =
    C.comp (IsoData.ofEq C (congrArg (C.tensorObj X) he)).hom (C.tensorHom f (C.id Q)) := by
  subst Q
  exact iso_naturality_refl hC _

end RMod.Classification

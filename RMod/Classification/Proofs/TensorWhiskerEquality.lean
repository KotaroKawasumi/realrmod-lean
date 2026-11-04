import RMod.Classification.Proofs.IsoEqualityMaps

/-!
# Moving an input equality through the parity-positioned whiskerings

Equality elimination identifies the varying tensor input. Its specified
comparison map then becomes an identity on both sides, leaving only the
ordinary identity composition laws. No object or comparison is chosen.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})
  {X X' Y : C.data.Obj} (e : X = X') (f : C.data.Hom X' Y) (T P : C.data.Obj)

theorem tensor_right_right_eq_comp
    (he : C.data.tensorObj (C.data.tensorObj X T) P =
      C.data.tensorObj (C.data.tensorObj X' T) P) :
    C.data.tensorHom (C.data.tensorHom (C.data.comp (IsoData.ofEq C.data e).hom f) (C.data.id T)) (C.data.id P) =
      C.data.comp (IsoData.ofEq C.data he).hom
        (C.data.tensorHom (C.data.tensorHom f (C.data.id T)) (C.data.id P)) := by
  subst X'
  change C.data.tensorHom (C.data.tensorHom (C.data.comp (C.data.id _) f) (C.data.id T)) (C.data.id P) =
    C.data.comp (C.data.id _) (C.data.tensorHom (C.data.tensorHom f (C.data.id T)) (C.data.id P))
  rw [C.laws.id_comp, C.laws.id_comp]

theorem tensor_left_right_eq_comp
    (he : C.data.tensorObj (C.data.tensorObj T X) P =
      C.data.tensorObj (C.data.tensorObj T X') P) :
    C.data.tensorHom (C.data.tensorHom (C.data.id T) (C.data.comp (IsoData.ofEq C.data e).hom f)) (C.data.id P) =
      C.data.comp (IsoData.ofEq C.data he).hom
        (C.data.tensorHom (C.data.tensorHom (C.data.id T) f) (C.data.id P)) := by
  subst X'
  change C.data.tensorHom (C.data.tensorHom (C.data.id T) (C.data.comp (C.data.id _) f)) (C.data.id P) =
    C.data.comp (C.data.id _) (C.data.tensorHom (C.data.tensorHom (C.data.id T) f) (C.data.id P))
  rw [C.laws.id_comp, C.laws.id_comp]

end RMod.Classification

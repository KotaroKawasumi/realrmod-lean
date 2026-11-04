import RMod.Classification.Proofs.IsoCalculus

/-!
# Transporting a unit diagram to an equal unit and parity factor

The unit family and extracted zero degree are specified by equalities.
This lemma accounts for those equality maps before the unit insertion,
so a diagram proved in the normalized presentation applies unchanged to
the actual convolution summand.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusion.{0, 0}} (p : Pi C.data)

theorem leftUnitDiagram_transport {U V Y Z : C.data.Obj} (e : U = C.data.tensorUnit)
    {a : ZMod 2} (ha : a = 0) (i : C.data.Hom C.data.tensorUnit V)
    (m : C.data.Hom (C.data.tensorObj (C.data.tensorObj V Y) (p.data.factor a)) Z)
    (q : C.data.Hom Z Y)
    (hd : C.data.comp (IsoData.ofEq C.data
        (congrArg (fun z => C.data.tensorObj (C.data.tensorObj C.data.tensorUnit Y) (p.data.factor z)) ha)).inv
      (C.data.comp (C.data.comp
        (C.data.tensorHom (C.data.tensorHom i (C.data.id Y)) (C.data.id (p.data.factor a))) m) q) =
        C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit Y)) (C.data.leftUnitorHom Y))
    (hs : C.data.tensorObj (C.data.tensorObj U Y) (p.data.factor a) =
      C.data.tensorObj (C.data.tensorObj C.data.tensorUnit Y) C.data.tensorUnit) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.comp (IsoData.ofEq C.data e).hom i) (C.data.id Y)) (C.data.id (p.data.factor a))) m) q =
      C.data.comp (IsoData.ofEq C.data hs).hom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit Y)) (C.data.leftUnitorHom Y)) := by
  subst U
  subst a
  change C.data.comp (C.data.id _) _ = _ at hd
  rw [C.laws.id_comp] at hd
  change C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.comp (C.data.id _) i) (C.data.id Y)) (C.data.id C.data.tensorUnit)) m) q =
    C.data.comp (C.data.id _) _
  rw [C.laws.id_comp, C.laws.id_comp]
  exact hd

theorem rightUnitDiagram_transport {U V Y Z : C.data.Obj} (e : U = C.data.tensorUnit)
    {a : ZMod 2} (ha : a = 0) (i : C.data.Hom C.data.tensorUnit V)
    (m : C.data.Hom (C.data.tensorObj (C.data.tensorObj Y V) (p.data.factor a)) Z)
    (q : C.data.Hom Z Y)
    (hd : C.data.comp (IsoData.ofEq C.data
        (congrArg (fun z => C.data.tensorObj (C.data.tensorObj Y C.data.tensorUnit) (p.data.factor z)) ha)).inv
      (C.data.comp (C.data.comp
        (C.data.tensorHom (C.data.tensorHom (C.data.id Y) i) (C.data.id (p.data.factor a))) m) q) =
        C.data.comp (C.data.rightUnitorHom (C.data.tensorObj Y C.data.tensorUnit)) (C.data.rightUnitorHom Y))
    (hs : C.data.tensorObj (C.data.tensorObj Y U) (p.data.factor a) =
      C.data.tensorObj (C.data.tensorObj Y C.data.tensorUnit) C.data.tensorUnit) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id Y) (C.data.comp (IsoData.ofEq C.data e).hom i)) (C.data.id (p.data.factor a))) m) q =
      C.data.comp (IsoData.ofEq C.data hs).hom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj Y C.data.tensorUnit)) (C.data.rightUnitorHom Y)) := by
  subst U
  subst a
  change C.data.comp (C.data.id _) _ = _ at hd
  rw [C.laws.id_comp] at hd
  change C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id Y) (C.data.comp (C.data.id _) i)) (C.data.id C.data.tensorUnit)) m) q =
    C.data.comp (C.data.id _) _
  rw [C.laws.id_comp, C.laws.id_comp]
  exact hd

end RMod.Classification

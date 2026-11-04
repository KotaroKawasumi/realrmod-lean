import RMod.Classification.Abstract.HomogeneousSpan
import RMod.Classification.Abstract.Normalizers
import Mathlib.CategoryTheory.EqToHom

/-! # Underlying maps of equality transports in a homogeneous span -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem span_eqToHom_hom (C : WeaklyPointedSuperfusion.{0, 0}) (S : C.data.Obj)
    {X Y : HomogeneousSpanCategory C S} (h : X = Y) :
    (eqToHom h).hom = (IsoData.ofEq C.data (congrArg (fun Z => Z.obj) h)).hom := by
  subst Y
  rfl

end RMod.Classification

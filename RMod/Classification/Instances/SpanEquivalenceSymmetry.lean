import RMod.Classification.Instances.SpanSuperequivalence

/-! # Reversing a completed component superequivalence -/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperequivalence

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

def symmData (E : SpanSuperequivalenceData C D S T) : SpanSuperequivalenceData D C T S := E.symm

theorem symmLaws (E : SpanSuperequivalence C D S T) :
    SpanSuperequivalenceLaws D C T S (symmData E.data) where
  forward := E.laws.backward
  backward := E.laws.forward
  unit_hom_even := E.laws.counit_inv_even
  unit_inv_even := E.laws.counit_hom_even
  counit_hom_even := E.laws.unit_inv_even
  counit_inv_even := E.laws.unit_hom_even

def symm (E : SpanSuperequivalence C D S T) : SpanSuperequivalence D C T S :=
  ⟨symmData E.data, symmLaws E⟩

end RMod.Classification.SpanSuperequivalence

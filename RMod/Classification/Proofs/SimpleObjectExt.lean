import RMod.Classification.Abstract.SimpleObjects

/-! # Equality of completed simple objects is equality of their objects -/

set_option autoImplicit false

namespace RMod.Classification

theorem SimpleObject.ext {C : WeaklyPointedSuperfusion.{0, 0}} {S T : SimpleObject C}
    (h : S.data.object = T.data.object) : S = T := by
  rcases S with ⟨⟨s⟩, hs⟩
  rcases T with ⟨⟨t⟩, ht⟩
  cases h
  rfl

end RMod.Classification

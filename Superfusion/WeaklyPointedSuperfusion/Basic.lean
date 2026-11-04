import Superfusion.WeaklyPointedSuperfusion.CandidateLaws

/-!
# Weakly pointed superfusion categories

The concept is deliberately the smallest bundle of proof-free candidate data
and the laws for exactly that data.  It is independent of every concrete
example, including `RMod`.
-/

set_option autoImplicit false

universe u v

namespace Superfusion

/-- Proof-free candidate data together with all weakly pointed superfusion
laws for that same data. -/
structure WeaklyPointedSuperfusionCategory where
  data : CandidateData.{u, v}
  laws : CandidateLaws data

end Superfusion

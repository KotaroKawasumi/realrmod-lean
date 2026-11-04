import RMod.Classification.Instances.ParityPentagonRoutes

/-!
# The pentagon routes with their scalar weights

Each edge uses the actual local associator with its specified unit scalar.
The inverse maps retain inverse weights. The next proofs extract these
five scalar weights and apply the universal parity sign equation.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

def weightedParityPentagonThree (W X Y Z : C.Obj) (a b c d e f q _r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) (ω₁ ω₂ ω₅ : ℝˣ) :
    IsoData C
      (C.tensorObj (C.tensorObj
        (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj W X) (p.factor a)) Y) (p.factor b)) Z)
        (p.factor t))
      (C.tensorObj (C.tensorObj W
        (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor e))) (p.factor q)))
        (p.factor s)) :=
  let A₁ := ((p.localAssociator W X Y a b c d h₁ ω₁).tensor C (IsoData.refl C Z)).tensor C
    (IsoData.refl C (p.factor t))
  let A₂ := p.localAssociator W (C.tensorObj (C.tensorObj X Y) (p.factor c)) Z d t f s h₅ ω₅
  let A₃ := ((IsoData.refl C W).tensor C (p.localAssociator X Y Z c f e q h₂ ω₂)).tensor C
    (IsoData.refl C (p.factor s))
  (A₁.trans C A₂).trans C A₃

def weightedParityPentagonTwo (W X Y Z : C.Obj) (a b _c _d e _f q r s t : ZMod 2)
    (h₃ : a + r = q + s) (h₄ : b + t = e + r) (ω₃ ω₄ : ℝˣ) :
    IsoData C
      (C.tensorObj (C.tensorObj
        (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj W X) (p.factor a)) Y) (p.factor b)) Z)
        (p.factor t))
      (C.tensorObj (C.tensorObj W
        (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor e))) (p.factor q)))
        (p.factor s)) :=
  let A₁ := p.localAssociator (C.tensorObj (C.tensorObj W X) (p.factor a)) Y Z b t e r h₄ ω₄
  let A₂ := p.localAssociator W X (C.tensorObj (C.tensorObj Y Z) (p.factor e)) a r q s h₃ ω₃
  A₁.trans C A₂


end RMod.Classification.PiData

import RMod.Classification.Abstract.Normalizers

/-!
# The two explicit scalar-free parity pentagon routes

The ten parity values are the two-cochain entries on four group elements:
a=nu(g,h), b=nu(gh,k), c=nu(h,k), d=nu(g,hk), e=nu(k,l),
f=nu(hk,l), q=nu(h,kl), r=nu(gh,kl), s=nu(g,hkl), t=nu(ghk,l).
Five displayed cocycle equalities identify the local normal forms. Keeping
the parity labels independent here separates the universal word equation
from group-index transport in the convolution construction. Both routes
retain actual inverse maps through IsoData composition and tensoring.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

def parityPentagonThree (W X Y Z : C.Obj) (a b c d e f q _r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) :
    IsoData C
      (C.tensorObj (C.tensorObj
        (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj W X) (p.factor a)) Y) (p.factor b)) Z)
        (p.factor t))
      (C.tensorObj (C.tensorObj W
        (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor e))) (p.factor q)))
        (p.factor s)) :=
  let A₁ := ((p.localAssociator W X Y a b c d h₁ 1).tensor C (IsoData.refl C Z)).tensor C
    (IsoData.refl C (p.factor t))
  let A₂ := p.localAssociator W (C.tensorObj (C.tensorObj X Y) (p.factor c)) Z d t f s h₅ 1
  let A₃ := ((IsoData.refl C W).tensor C (p.localAssociator X Y Z c f e q h₂ 1)).tensor C
    (IsoData.refl C (p.factor s))
  (A₁.trans C A₂).trans C A₃

def parityPentagonTwo (W X Y Z : C.Obj) (a b _c _d e _f q r s t : ZMod 2)
    (h₃ : a + r = q + s) (h₄ : b + t = e + r) :
    IsoData C
      (C.tensorObj (C.tensorObj
        (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj W X) (p.factor a)) Y) (p.factor b)) Z)
        (p.factor t))
      (C.tensorObj (C.tensorObj W
        (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor e))) (p.factor q)))
        (p.factor s)) :=
  let A₁ := p.localAssociator (C.tensorObj (C.tensorObj W X) (p.factor a)) Y Z b t e r h₄ 1
  let A₂ := p.localAssociator W X (C.tensorObj (C.tensorObj Y Z) (p.factor e)) a r q s h₃ 1
  A₁.trans C A₂

end RMod.Classification.PiData

import RMod.BrundanEllis.StackingPullbackProductFusion
import RMod.BrundanEllis.StackingPairWeakInvertible

/-! The actual enriched completion of the product of two pullbacks is a
weakly pointed fusion pi-supercategory, with its tensor, parity and duals
coming from the explicit completed product constructions. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking

instance pullbackProductWeaklyPointed (s t : Twist) :
    WeaklyPointedFusionPiSuperCategory (PullbackProductCompletion s t) where
  splitUnit := pullbackProductSplitUnit s t
  weaklyPointed := completed_weaklyPointed (pullback s) (pullback t)

def pullbackProductCategory (s t : Twist) : WeaklyPointedFusionPiSuperCat :=
  { carrier := PullbackProductCompletion s t }

end RMod.BrundanEllis.Stacking

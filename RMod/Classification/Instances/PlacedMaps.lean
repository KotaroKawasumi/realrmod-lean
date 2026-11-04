import RMod.Classification.Instances.SingleComponentHom
import RMod.Classification.Proofs.ComponentPlacement
import RMod.Classification.Abstract.Normalizers

/-!
# Maps to and from an object placed in one component

The equality identifying the supported coordinate with the original
object gives an explicit comparison and inverse. Compose with this
comparison and extend by zero to obtain maps to an arbitrary family.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (g : t.group) {X : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)

noncomputable def placedComparisonData :
    IsoData C.toWeaklyPointedSuperfusionData (placedObj C hC t g X hX g).val X :=
  IsoData.ofEq C.toWeaklyPointedSuperfusionData (placedObj_at C hC t g X hX)

noncomputable def placedTo {A : PullbackObj C t} (f : C.Hom X (A g).val) :
    PullbackHom C t (placedObj C hC t g X hX) A :=
  singleComponentHom C t g (C.comp (placedComparisonData C hC t g hX).hom f)

noncomputable def placedFrom {A : PullbackObj C t} (f : C.Hom (A g).val X) :
    PullbackHom C t A (placedObj C hC t g X hX) :=
  singleComponentHom C t g (C.comp f (placedComparisonData C hC t g hX).inv)

end RMod.Classification

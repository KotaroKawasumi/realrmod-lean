import RMod.Classification.Instances.RightParityComparison
import RMod.Classification.Abstract.Normalizers

/-!
# Specified deletion of a right parity factor

Deletion has degree equal to the factor parity. At zero it is the right
unitor; at one it uses the specified odd identification with the unit.
Both directions are supplied before any inverse or naturality law.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

def rightFactorDeletion (X : C.Obj) (a : ZMod 2) :
    IsoData C (C.tensorObj X (p.factor a)) X := by
  by_cases ha : a = 0
  · exact ⟨by simpa only [factor, if_pos ha] using C.rightUnitorHom X,
      by simpa only [factor, if_pos ha] using C.rightUnitorInv X⟩
  · exact ⟨by simpa only [factor, if_neg ha] using p.rightZHom X,
      by simpa only [factor, if_neg ha] using p.rightZInv X⟩

end RMod.Classification.PiData

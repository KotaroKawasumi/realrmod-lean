import RMod.Classification.Instances.UnitTensorComparisonAt
import RMod.Classification.Instances.SimpleOrbits

/-!
# Unit maps for a generator identified with the tensor unit

Keep the original generator object in each tensor product. The supplied
equality with the unit transports its unitor and inverse; the span
membership proof uses the same equality. No representative is replaced
by an unrelated choice.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : WeaklyPointedSuperfusion.{0, 0}) (S T : SimpleObject A) (hS : S = unitSimple A)

def leftUnitGeneratorSpan (Y : HomogeneousSpanCategory A T.data.object) :
    HomogeneousSpanCategory A T.data.object :=
  ⟨A.data.tensorObj S.data.object Y.obj, by subst S; exact (leftUnitSpanObj A T Y).property⟩

def rightUnitGeneratorSpan (Y : HomogeneousSpanCategory A T.data.object) :
    HomogeneousSpanCategory A T.data.object :=
  ⟨A.data.tensorObj Y.obj S.data.object, by subst S; exact (rightUnitSpanObj A T Y).property⟩

def leftUnitGeneratorMap (Y : A.data.Obj) :
    IsoData A.data (A.data.tensorObj S.data.object Y) Y := by
  subst S
  exact IsoData.leftUnit A.data Y

def rightUnitGeneratorMap (Y : A.data.Obj) :
    IsoData A.data (A.data.tensorObj Y S.data.object) Y := by
  subst S
  exact IsoData.rightUnit A.data Y

end RMod.Classification

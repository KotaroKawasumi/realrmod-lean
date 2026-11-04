import RMod.Classification.Proofs.HomogeneousSumTensor

/-!
# Completed tensor products of homogeneous presentations

Bundle the explicit signed tensor data with its separately established
matrix-unit and grading laws.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.HomogeneousSum

def tensor {C : WeaklyPointedSuperfusion.{u, v}} {S T X Y : C.data.Obj} {n m : ℕ}
    (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data T Y m) :
    HomogeneousSum C.data (C.data.tensorObj S T) (C.data.tensorObj X Y) (n * m) :=
  ⟨tensorData d.data e.data, tensorLaws d e⟩

end RMod.Classification.HomogeneousSum

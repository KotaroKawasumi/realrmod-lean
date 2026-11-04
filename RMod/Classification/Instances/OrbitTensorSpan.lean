import RMod.Classification.Instances.SpanTensor
import RMod.Classification.Proofs.HomogeneousSpanChange
import RMod.Classification.Proofs.SimpleOrbitRepresentatives

/-!
# Tensoring arbitrary objects in the chosen orbit components

The intrinsic product orbit and the selected representative describe the
same full homogeneous span. Retain the actual tensor object and map,
changing only the proof of component membership. This also applies to
intermediate tensors in the reconstruction associativity diagram.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : WeaklyPointedSuperfusion.{0, 0}) (g h : SimpleOrbit A)

def orbitTensorSpanObj
    (X : HomogeneousSpanCategory A (simpleOrbitRepresentative A g).data.object)
    (Y : HomogeneousSpanCategory A (simpleOrbitRepresentative A h).data.object) :
    HomogeneousSpanCategory A (simpleOrbitRepresentative A (g * h)).data.object :=
  ⟨A.data.tensorObj X.obj Y.obj,
    (inHomogeneousSpan_congr_generator A
      (simpleTensorRepresentative A (simpleOrbitRepresentative A g) (simpleOrbitRepresentative A h)).laws.simple
      (simpleOrbitRepresentative A (g * h)).laws.simple
      (simpleOrbitRepresentative_mul A g h) _).mp
      (inHomogeneousSpan_tensor A _ _ X.property Y.property)⟩

def orbitTensorSpanHom
    {X X' : HomogeneousSpanCategory A (simpleOrbitRepresentative A g).data.object}
    {Y Y' : HomogeneousSpanCategory A (simpleOrbitRepresentative A h).data.object}
    (f : X ⟶ X') (q : Y ⟶ Y') : orbitTensorSpanObj A g h X Y ⟶ orbitTensorSpanObj A g h X' Y' :=
  ObjectProperty.homMk (A.data.tensorHom f.hom q.hom)

end RMod.Classification

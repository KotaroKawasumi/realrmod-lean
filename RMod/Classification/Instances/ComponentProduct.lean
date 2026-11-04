import RMod.Classification.Instances.ComponentSystem
import RMod.Classification.Instances.TensorProductTransport

/-!
# Using a component equivalence on tensor-product generators

Equal parity orbits give identical full homogeneous spans. The two
identity span changes therefore present the selected product component
functor on the tensor generators without changing any ambient map.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}

noncomputable def componentProductEquivalence
    (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))
    (g h : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S h)).data.object
      (S (g * h)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T h)).data.object
      (T (g * h)).data.object) :
    SpanSuperequivalence A C (simpleTensorRepresentative A (S g) (S h)).data.object
      (simpleTensorRepresentative C (T g) (T h)).data.object :=
  tensorProductTransport (S g) (S h) (S (g * h)) (T g) (T h) (T (g * h))
    (d.component (g * h)) hS hT

end RMod.Classification

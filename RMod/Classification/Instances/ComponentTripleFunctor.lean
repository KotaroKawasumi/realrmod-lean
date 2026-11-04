import RMod.Classification.Instances.ComponentSystem
import RMod.Classification.Instances.SpanReindexFunctor
import RMod.Classification.Proofs.ComponentTripleOrbit

/-!
# The selected component functor on each triple tensor span

Reindex the chosen functor at the associated group product by the proved
triple constituent orbit. These functors use the original ambient maps
of the chosen component system.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))
  (hS : ∀ g h, SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S h)).data.object
    (S (g * h)).data.object)
  (hT : ∀ g h, SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T h)).data.object
    (T (g * h)).data.object)

noncomputable def componentTripleLeftFunctor (g h k : G) :
    SpanSuperfunctor A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A (S g) (S h)) (S k)).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C (T g) (T h)) (T k)).data.object :=
  spanReindexSuperfunctor (S ((g * h) * k)) (T ((g * h) * k))
    (simpleTensorRepresentative A (simpleTensorRepresentative A (S g) (S h)) (S k))
    (simpleTensorRepresentative C (simpleTensorRepresentative C (T g) (T h)) (T k))
    (componentTripleOrbit_left S hS g h k) (componentTripleOrbit_left T hT g h k)
    (d.component ((g * h) * k)).forwardFunctor

noncomputable def componentTripleRightFunctor (g h k : G) :
    SpanSuperfunctor A C
      (simpleTensorRepresentative A (S g) (simpleTensorRepresentative A (S h) (S k))).data.object
      (simpleTensorRepresentative C (T g) (simpleTensorRepresentative C (T h) (T k))).data.object :=
  spanReindexSuperfunctor (S (g * (h * k))) (T (g * (h * k)))
    (simpleTensorRepresentative A (S g) (simpleTensorRepresentative A (S h) (S k)))
    (simpleTensorRepresentative C (T g) (simpleTensorRepresentative C (T h) (T k)))
    (componentTripleOrbit_right S hS g h k) (componentTripleOrbit_right T hT g h k)
    (d.component (g * (h * k))).forwardFunctor

end RMod.Classification

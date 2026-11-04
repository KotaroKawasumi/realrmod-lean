import RMod.Classification.Instances.ComponentOmega

/-!
# The defining scalar equation and its uniqueness on all objects

These equations compare the actual normalized maps. The unit-valued
scalar is fixed by one generator triple, while signed naturality forces
that same scalar on arbitrary objects of the three components.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (p : Pi C.data)
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))
  (hS : ∀ g h, SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S h)).data.object
    (S (g * h)).data.object)
  (hT : ∀ g h, SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T h)).data.object
    (T (g * h)).data.object)
  (ν : G → G → ZMod 2)
  (t : ∀ g h, TensorComparison (S g) (S h) (T g) (T h)
    (d.component g).forwardFunctor (d.component h).forwardFunctor
    (componentProductEquivalence d g h (hS g h) (hT g h)).forwardFunctor (ν g h))

theorem componentOmega_spec (g h k : G)
    (X : HomogeneousSpanCategory A (S g).data.object)
    (Y : HomogeneousSpanCategory A (S h).data.object)
    (Z : HomogeneousSpanCategory A (S k).data.object) :
    ((componentParityTripleRight p d hS hT ν t g h k).data.app X Y Z).hom =
      C.data.smul (componentOmega p d hS hT ν t g h k : ℝ)
        ((componentNormalizedLeft p d hS hT ν t g h k).data.app X Y Z).hom :=
  (ParityTripleComparison.comparison_eq_unique_unit_smul (d.component g) (d.component h) (d.component k)
    (componentNormalizedLeft p d hS hT ν t g h k)
    (componentParityTripleRight p d hS hT ν t g h k)).choose_spec.1 X Y Z

theorem componentOmega_unique (g h k : G) (r : ℝˣ)
    (hr : ∀ X Y Z, ((componentParityTripleRight p d hS hT ν t g h k).data.app X Y Z).hom =
      C.data.smul (r : ℝ) ((componentNormalizedLeft p d hS hT ν t g h k).data.app X Y Z).hom) :
    r = componentOmega p d hS hT ν t g h k :=
  (ParityTripleComparison.comparison_eq_unique_unit_smul (d.component g) (d.component h) (d.component k)
    (componentNormalizedLeft p d hS hT ν t g h k)
    (componentParityTripleRight p d hS hT ν t g h k)).choose_spec.2 r hr

end RMod.Classification

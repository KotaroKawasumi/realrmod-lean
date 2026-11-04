import RMod.Classification.Proofs.SimpleTensorCongruence

/-!
# Triple tensor constituents in a multiplicative family of components

Apply the binary constituent congruence to the inner product, then use
the family's product orbit law. This identifies the two bracketings with
their respective group products without identifying tensor objects with
simple objects.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  (S : G → SimpleObject A)
  (hS : ∀ g h, SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S h)).data.object
    (S (g * h)).data.object)

include hS

theorem componentTripleOrbit_left (g h k : G) :
    SameParityOrbit A.data
      (simpleTensorRepresentative A (simpleTensorRepresentative A (S g) (S h)) (S k)).data.object
      (S ((g * h) * k)).data.object :=
  SameParityOrbit.trans A.laws
    (simpleTensorRepresentative_congr A (simpleTensorRepresentative A (S g) (S h)) (S (g * h))
      (S k) (S k) (hS g h) (SameParityOrbit.refl A.laws _)) (hS (g * h) k)

theorem componentTripleOrbit_right (g h k : G) :
    SameParityOrbit A.data
      (simpleTensorRepresentative A (S g) (simpleTensorRepresentative A (S h) (S k))).data.object
      (S (g * (h * k))).data.object :=
  SameParityOrbit.trans A.laws
    (simpleTensorRepresentative_congr A (S g) (S g) (simpleTensorRepresentative A (S h) (S k))
      (S (h * k)) (SameParityOrbit.refl A.laws _) (hS h k)) (hS g (h * k))

end RMod.Classification

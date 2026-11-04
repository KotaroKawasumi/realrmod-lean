import RMod.Definitions.WeaklyPointedSuperfusion

/-!
# Homogeneous copies of one object

A sum of parity shifts can be presented by homogeneous inclusions and
projections with the same source object. The parity of each copy belongs
to the data; the matrix-unit identities belong to laws on those data.
This auxiliary presentation is used only by the proofs of Clifford types.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

structure HomogeneousSumData (D : WeaklyPointedSuperfusionData.{u, v})
    (X Y : D.Obj) (n : ℕ) where
  parity : Fin n → ZMod 2
  inclusion : Fin n → D.Hom X Y
  projection : Fin n → D.Hom Y X

structure HomogeneousSumLaws {D : WeaklyPointedSuperfusionData.{u, v}}
    {X Y : D.Obj} {n : ℕ} (d : HomogeneousSumData D X Y n) : Prop where
  inclusion_grade : ∀ i, D.IsHomogeneous (d.parity i) (d.inclusion i)
  projection_grade : ∀ i, D.IsHomogeneous (d.parity i) (d.projection i)
  diagonal : ∀ i, D.comp (d.inclusion i) (d.projection i) = D.id X
  off_diagonal : ∀ i j, i ≠ j → D.comp (d.inclusion i) (d.projection j) = D.zero
  total : D.finSum n (fun i => D.comp (d.projection i) (d.inclusion i)) = D.id Y

structure HomogeneousSum (D : WeaklyPointedSuperfusionData.{u, v})
    (X Y : D.Obj) (n : ℕ) where
  data : HomogeneousSumData D X Y n
  laws : HomogeneousSumLaws data

end RMod.Classification

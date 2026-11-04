import RMod.Classification.Proofs.SimpleDecomposition
import RMod.Classification.Instances.EvenBiproducts
import Mathlib.Logic.Equiv.Sum

/-!
# Regrouping the chosen simple decomposition by component labels

Each fiber is summed in the even category. Mathlib's iterated biproduct
isomorphism and the equivalence between the disjoint union of the fibers
and the original finite index set provide the actual even regrouping
isomorphism. Empty components are retained as empty biproducts.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X : C.data.Obj}
  (d : SimpleDecomposition C X) {I : Type} [Fintype I] (label : Fin d.data.size → I)

noncomputable def groupedSimpleObject (i : I) : EvenSubcategory ℝ (LinearCategory C) := by
  classical
  exact ⨁ (fun j : {j : Fin d.data.size // label j = i} =>
    evenObj ℝ (LinearCategory C) (d.data.summand j.val))

noncomputable def groupedSimpleIso :
    (⨁ groupedSimpleObject d label) ≅ evenObj ℝ (LinearCategory C) X := by
  classical
  exact (biproductBiproductIso (fun i => {j : Fin d.data.size // label j = i})
      (fun _ j => evenObj ℝ (LinearCategory C) (d.data.summand j.val))) ≪≫
    (biproduct.whiskerEquiv
      (f := fun p : Σ i, {j : Fin d.data.size // label j = i} =>
        evenObj ℝ (LinearCategory C) (d.data.summand p.2.val))
      (g := fun j : Fin d.data.size => evenObj ℝ (LinearCategory C) (d.data.summand j))
      (Equiv.sigmaFiberEquiv label) (fun _ => Iso.refl _)) ≪≫
    (biproduct.uniqueUpToIso _ d.toDecomposition.evenIsBilimit).symm

end RMod.Classification

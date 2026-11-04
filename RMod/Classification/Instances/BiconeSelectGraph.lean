import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Selecting a graph of summands inside a specified retract

From a pair-indexed presentation and a retract, retain the summands
indexed by (i,s i). The retained inclusions and projections are the
original maps composed with the given retract maps. The graph condition
says that the retract projector fixes these inclusions.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] {I J : Type*} {V : I × J → C}

def biconeSelectGraph (b : Bicone V) (s : I → J) {R : C}
    (incl : R ⟶ b.pt) (proj : b.pt ⟶ R)
    (hgraph : ∀ i, b.ι (i, s i) ≫ proj ≫ incl = b.ι (i, s i)) :
    Bicone (fun i => V (i, s i)) where
  pt := R
  π i := incl ≫ b.π (i, s i)
  ι i := b.ι (i, s i) ≫ proj
  ι_π i j := by
    classical
    calc
      _ = (b.ι (i, s i) ≫ proj ≫ incl) ≫ b.π (j, s j) := by simp only [Category.assoc]
      _ = b.ι (i, s i) ≫ b.π (j, s j) := by rw [hgraph]
      _ = _ := by
        split_ifs with h
        · subst j
          exact bicone_ι_π_self b (i, s i)
        · exact bicone_ι_π_ne b (fun hij => h (congrArg Prod.fst hij))

end RMod.Classification

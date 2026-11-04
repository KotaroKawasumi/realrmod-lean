import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Instances.LinearCategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The full superlinear span of a generator

An object belongs to the span when it has a finite homogeneous sum
presentation. Mathlib's full subcategory retains every morphism between
such objects. No monoidal structure is asserted on a single component.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

def InHomogeneousSpan (C : WeaklyPointedSuperfusion.{0, 0}) (S : C.data.Obj) :
    ObjectProperty (LinearCategory C) := fun X => ∃ n, Nonempty (HomogeneousSum C.data S X n)

abbrev HomogeneousSpanCategory (C : WeaklyPointedSuperfusion.{0, 0}) (S : C.data.Obj) :=
  (InHomogeneousSpan C S).FullSubcategory

end RMod.Classification

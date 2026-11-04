import RMod.Classification.Instances.LinearCategory
import Superfusion.Category.EndSuperAlgebra

/-!
# Reusing the existing endomorphism superalgebra

The existing supercategory and superalgebra interfaces receive precisely
the raw operations and the already proved laws. This is a library adapter;
the classification data continue to keep operations and laws separate.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.LinearCategory

variable (C : WeaklyPointedSuperfusion.{u, v})

instance supercategory : Superfusion.Category.Supercategory ℝ (LinearCategory C) where
  grade := grade C
  isInternal_grade := grade_isInternal C
  id_mem_even := C.laws.id_even
  comp_mem := C.laws.comp_grade

end RMod.Classification.LinearCategory

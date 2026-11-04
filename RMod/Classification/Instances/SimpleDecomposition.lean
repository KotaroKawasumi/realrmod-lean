import RMod.Classification.Abstract.SimpleDecomposition

/-!
# Choosing the actual simple decomposition data

Semisimplicity supplies a finite family and all of its matrix maps.
Classical choice selects that complete data record, and its laws verify
the selected record. No computational witness is stored only in laws.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X : C.data.Obj)

theorem exists_simpleDecompositionData :
    ∃ d : SimpleDecompositionData C.data X, SimpleDecompositionLaws C.data d := by
  obtain ⟨n, S, hs, i, p, hi, hp, hd, ho, hh⟩ := C.laws.semisimple X
  exact ⟨⟨n, S, ⟨i, p⟩⟩, ⟨hs, ⟨hi, hp, hd, ho, hh⟩⟩⟩

noncomputable def simpleDecompositionData : SimpleDecompositionData C.data X :=
  (exists_simpleDecompositionData C X).choose

theorem simpleDecompositionLaws : SimpleDecompositionLaws C.data (simpleDecompositionData C X) :=
  (exists_simpleDecompositionData C X).choose_spec

noncomputable def simpleDecomposition : SimpleDecomposition C X :=
  ⟨simpleDecompositionData C X, simpleDecompositionLaws C X⟩

end RMod.Classification

import RMod.BrundanEllis.StackingReferenceHexagonData

/-! Compact candidate rows. The certificates still compare the decoded integer
entries with the actual reference maps using ordinary kernel reduction. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

/-- Read fixed-width base digits and subtract their common offset. -/
def decodeIntegerRow (width base offset code : ℕ) : List ℤ :=
  (List.range width).map fun j =>
    Int.ofNat ((code / base ^ j) % base) - Int.ofNat offset

example : decodeIntegerRow 3 5 2 13 = [1, 0, -2] := by rfl
example : decodeIntegerRow 4 17 8 42499 = [8, -8, 3, 0] := by rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor

/-
Superfusion / GaugeChi / TableEncoding

Shared lookup functions for the bit-packed semantic gauge certificates.
This leaf contains no gauge-specific values: the canonical tables live in
`RealGaugeTables.lean`, while historical table modules are deliberately not
part of its import graph.
-/
import Superfusion.Cochain.DyadicCertificate

namespace Superfusion

namespace GaugeChi

/-- The index `0..7` of a label in `Multiplicative (ZMod 8)`. -/
def ix (a : Multiplicative (ZMod 8)) : ℕ := (Multiplicative.toAdd a).val

/-- Lexicographic index of a pair of labels. -/
def idx2 (a b : Multiplicative (ZMod 8)) : ℕ := ix a * 8 + ix b

/-- Lexicographic index of a triple of labels. -/
def idx3 (a b c : Multiplicative (ZMod 8)) : ℕ := (ix a * 8 + ix b) * 8 + ix c

/-- Lexicographic index of a quadruple of labels. -/
def idx4 (a b c d : Multiplicative (ZMod 8)) : ℕ :=
  ((ix a * 8 + ix b) * 8 + ix c) * 8 + ix d

/-- Bit-table lookup, as a parity. -/
def bitAt (table i : ℕ) : ZMod 2 := if table.testBit i then 1 else 0

/-- Nibble-table lookup with offset `8`, as an integer exponent. -/
def nibbleAt (table i : ℕ) : ℤ := (((table >>> (4 * i)) % 16 : ℕ) : ℤ) - 8

/-- Byte-table lookup with offset `128`, as an integer exponent. -/
def byteAt (table i : ℕ) : ℤ := (((table >>> (8 * i)) % 256 : ℕ) : ℤ) - 128

end GaugeChi

end Superfusion

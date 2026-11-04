import Superfusion.GaugeChi.RealGaugeTables
import Superfusion.RMod.Constructive.RawSemanticConnector

/-! Shared adapters from the concrete `TripleCerts` connectors to the
generated raw native table. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

universe u

open GaugeChi
open RawSemanticConnector

/-- Constructive eight-way elimination for `Fin 8`. -/
private def fin8Rec {P : Fin 8 → Sort u} (h0 : P 0) (h1 : P 1)
    (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6)
    (h7 : P 7) : ∀ x, P x := by
  intro x
  refine Fin.cases h0 ?_ x
  intro x
  refine Fin.cases h1 ?_ x
  intro x
  refine Fin.cases h2 ?_ x
  intro x
  refine Fin.cases h3 ?_ x
  intro x
  refine Fin.cases h4 ?_ x
  intro x
  refine Fin.cases h5 ?_ x
  intro x
  refine Fin.cases h6 ?_ x
  intro x
  refine Fin.cases h7 ?_ x
  intro x
  exact Fin.elim0 x

/-- Constructive eight-way elimination for data or proofs indexed by
`ZMod 8`. -/
def zmod8Rec {P : ZMod 8 → Sort u} (h0 : P 0) (h1 : P 1)
    (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6)
    (h7 : P 7) : ∀ x, P x := by
  intro x
  let e : Fin 8 ≃+* ZMod 8 := ZMod.finEquiv 8
  rw [← e.apply_symm_apply x]
  exact fin8Rec h0 h1 h2 h3 h4 h5 h6 h7 (e.symm x)

/-- The frozen degree of the raw connector. -/
def parity (a b c : ZMod 8) : ZMod 2 :=
  GaugeChi.realLeanParityTable
    (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
      (Multiplicative.ofAdd c)

/-! ## Uniform native-frame identification

The generated table and the checked `TripleCerts` matrices use the same
integer coefficients.  The only apparent difference is that the latter are
written in the aligned left frame and over `D ((a + b) + c)`.  The following
lemmas perform that frame and coefficient cast once, uniformly; the 512
closed cases then reduce only the equality of two integer list literals. -/

/-- Transporting a canonical real-representation basis vector along an index
equality gives the correspondingly transported basis vector. -/
theorem gaugeCast_realRepBasis {x y : ZMod 8} (h : x = y)
    (g : Fin (realRepDim x.val)) :
    (realGauge.gaugeCast h).toAlgEquiv (realRepBasis x g) =
      realRepBasis y
        (Fin.cast (congrArg (fun z : ZMod 8 => realRepDim z.val) h) g) := by
  cases h
  rfl

/-- Align a coefficient matrix from the legacy square frame to the native
rectangular frame. -/
theorem alignT_matOfCoeff (a b c : ZMod 8)
    (hsz : realGauge.gaugeSizeR a b c = realGauge.gaugeSizeL a b c)
    (L : List (List (List ℤ))) :
    alignT ℝ realGauge a b c hsz
      (matOfCoeff (realRepBasis (a + b + c)) fun r s e =>
        coeffGet L (sumPos r) (sumPos s) e.val) =
    matOfCoeff₂ (realRepBasis (a + (b + c))) fun r s e =>
      coeffGet L
        (sumPos (gaugeSizeCastEquiv ℝ realGauge a b c hsz r))
        (sumPos s) e.val := by
  ext r s
  rw [alignT_apply, matOfCoeff_apply, matOfCoeff₂_apply]
  rw [map_sum]
  let eg : Fin (realRepDim (a + b + c).val) ≃
      Fin (realRepDim (a + (b + c)).val) :=
    finCongr (congrArg (fun z : ZMod 8 => realRepDim z.val)
      (add_assoc a b c))
  rw [← Equiv.sum_comp eg (fun g =>
    ((coeffGet L
      (sumPos (gaugeSizeCastEquiv ℝ realGauge a b c hsz r))
      (sumPos s) g.val : ℤ) : ℝ) • realRepBasis (a + (b + c)) g)]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_smul]
  change ((coeffGet L _ _ _ : ℤ) : ℝ) •
      (realGauge.gaugeCast (add_assoc a b c)).toAlgEquiv
        (realRepBasis (a + b + c) g) = _
  rw [gaugeCast_realRepBasis]
  rfl

/-- The raw generated matrix is the aligned realization of the same integer
coefficient table, for every square-frame triple. -/
theorem forwardMatrix_eq_alignT_raw (a b c : ZMod 8)
    (hsz : realGauge.gaugeSizeR a b c = realGauge.gaugeSizeL a b c) :
    forwardMatrix a b c =
      alignT ℝ realGauge a b c hsz
        (matOfCoeff (realRepBasis (a + b + c)) fun r s e =>
          coeffGet (RMod.ConstructiveConnectorTable.forwardCoeff a b c)
            (sumPos r) (sumPos s) e.val) := by
  rw [alignT_matOfCoeff]
  unfold forwardMatrix
  ext r s
  rw [matOfCoeff₂_apply, matOfCoeff₂_apply]
  apply Finset.sum_congr rfl
  intro e he
  congr 2
  unfold coeffOf
  congr 2
  · rcases r with r | r
    · rfl
    · exact congrArg (fun n => n + r.val) (congrArg Prod.fst hsz)
  · rcases s with s | s <;> rfl

/-- Native rectangular realization of the raw table, with no alignment
hypothesis. -/
theorem forwardMatrix_eq_native_raw (a b c : ZMod 8) :
    forwardMatrix a b c =
      matOfCoeff₂ (realRepBasis (a + (b + c))) fun r s e =>
        coeffGet (RMod.ConstructiveConnectorTable.forwardCoeff a b c)
          (sumPos r) (sumPos s) e.val := by
  unfold forwardMatrix
  ext r s
  rw [matOfCoeff₂_apply, matOfCoeff₂_apply]
  apply Finset.sum_congr rfl
  intro e he
  congr 2
  unfold coeffOf
  congr 2
  · rcases r with r | r <;> rfl
  · rcases s with s | s <;> rfl

/-- Transport an already checked aligned connector to the generated native
table, once their finite coefficient matrices have been identified. -/
theorem memOfAligned {a b c : ZMod 8} {d : ZMod 2}
    {hsz : realGauge.gaugeSizeR a b c = realGauge.gaugeSizeL a b c}
    {T : ((realGauge.D (a + b + c)).matrixSuper
      (realGauge.gaugeSizeL a b c).1
      (realGauge.gaugeSizeL a b c).2).carrier}
    (ht : gtOfT ℝ realGauge a b c hsz T ∈
      gInterSpace ℝ realGauge a b c d)
    (hp : parity a b c = d)
    (hT : forwardMatrix a b c = alignT ℝ realGauge a b c hsz T) :
    gtOfTNative ℝ realGauge a b c (forwardMatrix a b c) ∈
      gInterSpace ℝ realGauge a b c (parity a b c) := by
  rw [hp, hT, ← gtOfT_eq_gtOfTNative]
  exact ht

/-- The corresponding adapter for the twelve triples whose checked
connector was already stated in the native rectangular frame. -/
theorem memOfNative {a b c : ZMod 8} {d : ZMod 2}
    {T : NativeT ℝ realGauge a b c}
    (ht : gtOfTNative ℝ realGauge a b c T ∈
      gInterSpace ℝ realGauge a b c d)
    (hp : parity a b c = d)
    (hT : forwardMatrix a b c = T) :
    gtOfTNative ℝ realGauge a b c (forwardMatrix a b c) ∈
      gInterSpace ℝ realGauge a b c (parity a b c) := by
  rw [hp, hT]
  exact ht

/-- Fast square-frame adapter: after the uniform frame theorem, a concrete
certificate only has to expose that its coefficient literal is the generated
raw table.  At all 500 square triples this last argument is `rfl`. -/
theorem memOfAlignedRaw {a b c : ZMod 8} {d : ZMod 2}
    {hsz : realGauge.gaugeSizeR a b c = realGauge.gaugeSizeL a b c}
    {T : ((realGauge.D (a + b + c)).matrixSuper
      (realGauge.gaugeSizeL a b c).1
      (realGauge.gaugeSizeL a b c).2).carrier}
    (ht : gtOfT ℝ realGauge a b c hsz T ∈
      gInterSpace ℝ realGauge a b c d)
    (hp : parity a b c = d)
    (hshape : T = matOfCoeff (realRepBasis (a + b + c)) fun r s e =>
      coeffGet (RMod.ConstructiveConnectorTable.forwardCoeff a b c)
        (sumPos r) (sumPos s) e.val) :
    gtOfTNative ℝ realGauge a b c (forwardMatrix a b c) ∈
      gInterSpace ℝ realGauge a b c (parity a b c) := by
  apply memOfAligned ht hp
  rw [hshape]
  exact forwardMatrix_eq_alignT_raw a b c hsz

/-- Variant of `memOfAlignedRaw` that separates the cheap matrix-shape
reduction from the closed integer-list equality.  This keeps definitional
equality from unfolding the algebra-valued matrix while searching for the
table literal. -/
theorem memOfAlignedCoeff {a b c : ZMod 8} {d : ZMod 2}
    {hsz : realGauge.gaugeSizeR a b c = realGauge.gaugeSizeL a b c}
    {T : ((realGauge.D (a + b + c)).matrixSuper
      (realGauge.gaugeSizeL a b c).1
      (realGauge.gaugeSizeL a b c).2).carrier}
    (ht : gtOfT ℝ realGauge a b c hsz T ∈
      gInterSpace ℝ realGauge a b c d)
    (hp : parity a b c = d)
    (L : List (List (List ℤ)))
    (hshape : T = matOfCoeff (realRepBasis (a + b + c)) fun r s e =>
      coeffGet L (sumPos r) (sumPos s) e.val)
    (hcoeff : RMod.ConstructiveConnectorTable.forwardCoeff a b c = L) :
    gtOfTNative ℝ realGauge a b c (forwardMatrix a b c) ∈
      gInterSpace ℝ realGauge a b c (parity a b c) := by
  apply memOfAligned ht hp
  rw [hshape, ← hcoeff]
  exact forwardMatrix_eq_alignT_raw a b c hsz

/-- Fast native rectangular adapter for the twelve exceptional triples. -/
theorem memOfNativeRaw {a b c : ZMod 8} {d : ZMod 2}
    {T : NativeT ℝ realGauge a b c}
    (ht : gtOfTNative ℝ realGauge a b c T ∈
      gInterSpace ℝ realGauge a b c d)
    (hp : parity a b c = d)
    (hshape : T =
      matOfCoeff₂ (realRepBasis (a + (b + c))) fun r s e =>
        coeffGet (RMod.ConstructiveConnectorTable.forwardCoeff a b c)
          (sumPos r) (sumPos s) e.val) :
    gtOfTNative ℝ realGauge a b c (forwardMatrix a b c) ∈
      gInterSpace ℝ realGauge a b c (parity a b c) := by
  apply memOfNative ht hp
  rw [hshape]
  exact forwardMatrix_eq_native_raw a b c

/-- Coefficient-separated native adapter, analogous to
`memOfAlignedCoeff`. -/
theorem memOfNativeCoeff {a b c : ZMod 8} {d : ZMod 2}
    {T : NativeT ℝ realGauge a b c}
    (ht : gtOfTNative ℝ realGauge a b c T ∈
      gInterSpace ℝ realGauge a b c d)
    (hp : parity a b c = d)
    (L : List (List (List ℤ)))
    (hshape : T =
      matOfCoeff₂ (realRepBasis (a + (b + c))) fun r s e =>
        coeffGet L (sumPos r) (sumPos s) e.val)
    (hcoeff : RMod.ConstructiveConnectorTable.forwardCoeff a b c = L) :
    gtOfTNative ℝ realGauge a b c (forwardMatrix a b c) ∈
      gInterSpace ℝ realGauge a b c (parity a b c) := by
  apply memOfNative ht hp
  rw [hshape, ← hcoeff]
  exact forwardMatrix_eq_native_raw a b c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

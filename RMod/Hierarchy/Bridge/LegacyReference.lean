import RMod.Hierarchy.Bridge.LegacyCategories
import RMod.Hierarchy.Bridge.BrauerWallTypes

/-!
# Reference properties for arbitrary new inputs

The extracted category has the same homogeneous total endomorphisms and
simple parity orbits. Its raw decomposition witnesses correspond to the
chosen even biproducts, so the intrinsic Brauer-Wall tests agree.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Limits
namespace RMod.Legacy.Hierarchy
variable (A : WeaklyPointedFusionPiSupercategory)

theorem legacyParityOrbit_iff (X Y : A.data.Obj) :
    Classification.SameParityOrbit (legacyCategory A).data X Y ↔
      SameParityOrbit A.toMonoidalPiSupercategory.monoidal.super X Y := by
  constructor
  · rintro ⟨a, f, g, hfg, hgf, hf, hg⟩
    exact ⟨a, ⟨f, g, hfg, hgf⟩, hf, hg⟩
  · rintro ⟨a, e, hf, hg⟩
    exact ⟨a, e.hom, e.inv, e.hom_inv_id, e.inv_hom_id, hf, hg⟩

theorem legacyDecomposition_iff (X : A.data.Obj) {n : ℕ} (S : Fin n → A.data.Obj) :
    (legacyCategory A).data.HasDecomposition X S ↔
      Nonempty (evenObj A.toMonoidalPiSupercategory.monoidal.super X ≅
        ⨁ (fun j => evenObj A.toMonoidalPiSupercategory.monoidal.super (S j))) := by
  let S' := fun j => evenObj A.toMonoidalPiSupercategory.monoidal.super (S j)
  constructor
  · intro h
    obtain ⟨d⟩ := (Classification.hasDecomposition_iff (legacyCategory A) X S).mp h
    let e := biproduct.uniqueUpToIso _ d.evenIsBilimit
    exact ⟨(legacyEvenForget A).preimageIso (e ≪≫ ((legacyEvenForget A).mapBiproduct S').symm)⟩
  · rintro ⟨e⟩
    exact legacyDecomposition A.toMonoidalPiSupercategory.monoidal _ S' e

theorem legacyCliffordEnd_iff (X : A.data.Obj) (n : ℕ) :
    Classification.HasCliffordEnd (legacyCategory A).data X n ↔
      ∃ e : CliffordAlgebra (QuadraticMap.weightedSumSquares ℝ (fun _ : Fin n => (-1 : ℝ))) ≃ₐ[ℝ]
        End (totalObj A.toMonoidalPiSupercategory.monoidal.super X),
      ∀ a x, x ∈ CliffordAlgebra.evenOdd
        (QuadraticMap.weightedSumSquares ℝ (fun _ : Fin n => (-1 : ℝ))) a ↔
        e x ∈ grade A.toMonoidalPiSupercategory.monoidal.super X X a := by
  constructor
  · rintro ⟨e, h1, hadd, hsmul, hmul, hgrade⟩
    refine ⟨{ toEquiv := e, map_mul' := hmul, map_add' := hadd, commutes' := ?_ }, hgrade⟩
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    change e (r • 1) = (legacyCategory A).data.smul r ((legacyCategory A).data.id X)
    exact (hsmul r 1).trans (congrArg ((legacyCategory A).data.smul r) h1)
  · rintro ⟨e, hgrade⟩
    exact ⟨e.toEquiv, e.map_one, e.map_add, fun r x => e.toLinearEquiv.map_smul r x, e.map_mul, hgrade⟩

theorem legacyBrauerWallType_iff (X : A.data.Obj) (r : ZMod 8) :
    Classification.HasBWType (legacyCategory A).data X r ↔
      HasBrauerWallType A.toFusionPiSupercategory
        (evenObj A.toMonoidalPiSupercategory.monoidal.super X) r := by
  let C := legacyCategory A
  let B := A.toMonoidalPiSupercategory.monoidal.super
  constructor
  · rintro ⟨n, S, Y, hn, hS, hD, hCl⟩
    let S' : Fin n → Even B := fun j => evenObj B (S j)
    refine ⟨n, S', hn, fun j => (legacyParityOrbit_iff A X (S j)).mp (hS j), ?_⟩
    obtain ⟨e⟩ := (legacyDecomposition_iff A Y S).mp hD
    let e' : oldEvenObj C Y ≅ oldEvenObj C (biproduct (C := Even B) S') := (legacyEvenForget A).mapIso e
    exact (legacyCliffordEnd_iff A (biproduct (C := Even B) S') r.val).mp
      (oldCliffordEnd_of_evenIso C e' r.val hCl)
  · rintro ⟨n, S, hn, hS, e, he⟩
    refine ⟨n, (fun j => (S j : A.data.Obj)), (biproduct (C := Even B) S : A.data.Obj), hn,
      fun j => (legacyParityOrbit_iff A X (S j)).mpr (hS j), ?_, ?_⟩
    · exact legacyDecomposition A.toMonoidalPiSupercategory.monoidal _ S (Iso.refl _)
    · exact (legacyCliffordEnd_iff A (biproduct (C := Even B) S) r.val).mpr ⟨e, he⟩

theorem toOldReference (hA : IsBrauerWallReference A) :
    Classification.ReferenceProperty (toOldPiSuperfusion A).data where
  toPiSuperfusionLaws := toOldPiSuperfusionLaws A
  simple_type X hX := by
    obtain ⟨r, hr, hu⟩ := hA.simple_type (evenObj _ X) ((legacySimple_iff _ _).mp hX)
    exact ⟨r, (legacyBrauerWallType_iff A X r).mpr hr,
      fun s hs => hu s ((legacyBrauerWallType_iff A X s).mp hs)⟩
  realizes_type r := by
    obtain ⟨X, hX, hr⟩ := hA.realizes_type r
    exact ⟨X, (legacySimple_iff _ X).mpr hX, (legacyBrauerWallType_iff A X r).mpr hr⟩
  type_detects_orbit X Y r hX hY hr := by
    exact (legacyBrauerWallType_iff A Y r).trans
      ((hA.type_detects_orbit (evenObj _ X) (evenObj _ Y) r
        ((legacySimple_iff _ _).mp hX) ((legacySimple_iff _ _).mp hY)
        ((legacyBrauerWallType_iff A X r).mp hr)).trans (legacyParityOrbit_iff A X Y).symm)

end RMod.Legacy.Hierarchy

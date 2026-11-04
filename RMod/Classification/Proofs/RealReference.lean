import RMod.Classification.Instances.RealEndomorphisms
import RMod.Classification.Proofs.BrauerWallTypes

/-!
# The intrinsic reference property of the real regular-module category

Singletons are the simple objects up to even isomorphism. Their
endomorphism algebras are the eight existing real division representatives.
Actual Clifford matrix stabilizations give the required finite-sum
witnesses, and the order-eight BW calculation proves uniqueness.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.RMod.FromRawDCT

attribute [local implicit_reducible] CategoryTheory.End
  Category.endSuperAlgebra Category.endGrading SuperAlgebra.matrixSuper
  realRModLegacy realRModData realEndpointCandidateData Candidate.dataWithAssociator
  Obj.singleton Obj.size Obj.atom

theorem realSingleton_simple (a : ZMod 8) (s : ZMod 2) :
    realRModData.IsSimple (Obj.singleton (a, s)) :=
  RealSemisimple.singleton_simple (a, s)

theorem realSingleton_shift (a : ZMod 8) (s t : ZMod 2) :
    realRModData.HasHomogeneousIso (s + t) (Obj.singleton (a, s)) (Obj.singleton (a, t)) := by
  refine ⟨RealPairing.singletonShiftHom a s t, RealPairing.singletonShiftHom a t s,
    RealPairing.singletonShiftHom_comp a s t, RealPairing.singletonShiftHom_comp a t s,
    RealPairing.singletonShiftHom_mem a s t, ?_⟩
  have h := RealPairing.singletonShiftHom_mem a t s
  rw [add_comm] at h
  exact h

/-- Every simple is in the parity orbit of a singleton of parity zero. -/
theorem realSimple_orbit_singleton {X : realRModData.Obj} (hX : realRModData.IsSimple X) :
    ∃ a : ZMod 8, SameParityOrbit realRModData X (Obj.singleton (a, 0)) := by
  obtain ⟨i, ⟨e⟩⟩ := RealSemisimple.simple_iso_atom hX
  have h : realRModData.HasHomogeneousIso 0 X (Obj.singleton (X.atom i)) :=
    ⟨e.hom, e.inv, e.hom_inv, e.inv_hom, e.hom_mem, e.inv_mem⟩
  exact ⟨(X.atom i).1, SameParityOrbit.trans realRModLaws ⟨0, h⟩
    ⟨(X.atom i).2 + 0, realSingleton_shift (X.atom i).1 (X.atom i).2 0⟩⟩

/-- A Clifford stabilization is realized by a finite sum of the required
parity shifts, with the same p|q convention as the matrix algebra. -/
theorem realSingleton_hasBWType (r : ZMod 8) :
    HasBWType realRModData (Obj.singleton (r, 0)) r := by
  obtain ⟨p, q, hpq, ⟨e⟩⟩ := negativeTower_realRep_stabilization r.val
  rw [ZMod.natCast_zmod_val] at e
  let a : Fin (p + q) → ZMod 2 := fun i => sumParity p q (finSumFinEquiv.symm i)
  let S : Fin (p + q) → realRModData.Obj := fun i => Obj.singleton (r, a i)
  have hS (i : Fin (p + q)) : realRModData.HasHomogeneousIso (a i) (Obj.singleton (r, 0)) (S i) := by
    simpa only [zero_add] using realSingleton_shift r 0 (a i)
  obtain ⟨Y, hY⟩ := realRModLaws.has_finite_biproducts S
  obtain ⟨d, hd, hda⟩ := exists_homogeneousSum_of_degrees realRModLaws a hS hY
  let b : HomogeneousSum realRModData (Obj.singleton (r, 0)) Y (p + q) := ⟨d, hd⟩
  let m := HomogeneousSum.stabilizationEquivOfIndex (C := realRModLegacy) b
    (finSumFinEquiv.symm : Fin (p + q) ≃ Fin p ⊕ Fin q)
    (fun i => congrFun hda i)
  let v := m.trans ((realSingletonEndSuperEquiv r 0).matrixSuper p q)
  refine ⟨p + q, S, Y, Nat.pos_of_ne_zero hpq, fun i => ⟨a i, hS i⟩, hY, ?_⟩
  exact hasCliffordEnd_of_towerEquiv realRModLegacy (e.trans v.symm)

/-- The numerical label of a singleton is forced by its Clifford type. -/
theorem realSingleton_type_iff (a : ZMod 8) (s : ZMod 2) (r : ZMod 8) :
    HasBWType realRModData (Obj.singleton (a, s)) r ↔ r = a := by
  have ho : SameParityOrbit realRModData (Obj.singleton (a, 0)) (Obj.singleton (a, s)) :=
    ⟨0 + s, realSingleton_shift a 0 s⟩
  have ha := (SameParityOrbit.hasBWType_iff realRModLaws ho a).mp (realSingleton_hasBWType a)
  exact ⟨fun hr => HasBWType.unique realRModLegacy hr ha, fun h => h ▸ ha⟩

/-- The specified real model realizes each intrinsic Clifford type exactly
once up to homogeneous isomorphism, as required by P. -/
theorem realReference : ReferenceProperty realPiData where
  toPiSuperfusionLaws := realPiSuperfusionLaws
  simple_type X hX := by
    obtain ⟨a, ha⟩ := realSimple_orbit_singleton hX
    have htype := (SameParityOrbit.hasBWType_iff realRModLaws ha a).mpr (realSingleton_hasBWType a)
    exact ⟨a, htype, fun r hr => HasBWType.unique realRModLegacy hr htype⟩
  realizes_type r := ⟨Obj.singleton (r, 0), realSingleton_simple r 0, realSingleton_hasBWType r⟩
  type_detects_orbit X Y r hX hY hr := by
    constructor
    · intro hs
      obtain ⟨a, ha⟩ := realSimple_orbit_singleton hX
      obtain ⟨b, hb⟩ := realSimple_orbit_singleton hY
      have hra := (realSingleton_type_iff a 0 r).mp
        ((SameParityOrbit.hasBWType_iff realRModLaws ha r).mp hr)
      have hrb := (realSingleton_type_iff b 0 r).mp
        ((SameParityOrbit.hasBWType_iff realRModLaws hb r).mp hs)
      have hab : a = b := hra.symm.trans hrb
      rw [← hab] at hb
      exact SameParityOrbit.trans realRModLaws ha hb.symm
    · intro h
      exact (SameParityOrbit.hasBWType_iff realRModLaws h r).mp hr

end RMod.Classification

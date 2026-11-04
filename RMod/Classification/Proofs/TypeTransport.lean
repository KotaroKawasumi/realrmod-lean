import RMod.Classification.Instances.EndFunctors
import RMod.Classification.Proofs.Endomorphisms
import RMod.Classification.Proofs.EvenSimple

/-!
# Invariance of the intrinsic Clifford type

A fully faithful graded functor transports a Clifford amplification by its
endomorphism algebra equivalence. Finite decompositions and parity orbits
are transported by the same functor. Applying this to both functors of an
equivalence proves invariance of the precise intrinsic type predicate,
without assuming the reference property P or a classification theorem.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}}

namespace Superfunctor

variable (F : Superfunctor C D)
  (hbij : ∀ X Y, Function.Bijective (F.data.map : C.data.Hom X Y → _))
  (hgrade : ∀ {X Y a} (f : C.data.Hom X Y),
    D.data.IsHomogeneous a (F.data.map f) ↔ C.data.IsHomogeneous a f)

include hbij hgrade

theorem map_cliffordEnd {X : C.data.Obj} {n : ℕ} (hX : HasCliffordEnd C.data X n) :
    HasCliffordEnd D.data (F.data.obj X) n := by
  obtain ⟨e, he⟩ := (hasCliffordEnd_iff C X n).mp hX
  refine (hasCliffordEnd_iff D (F.data.obj X) n).mpr
    ⟨e.trans (F.endAlgEquiv X (hbij X X)), ?_⟩
  intro a x
  exact (he a x).trans (hgrade (e x)).symm

theorem map_bwType {X : C.data.Obj} {r : ZMod 8} (hX : HasBWType C.data X r) :
    HasBWType D.data (F.data.obj X) r := by
  obtain ⟨n, S, Y, hn, hS, hd, hc⟩ := hX
  refine ⟨n, fun i => F.data.obj (S i), F.data.obj Y, hn, ?_,
    F.map_decomposition hd, F.map_cliffordEnd hbij hgrade hc⟩
  intro i
  obtain ⟨a, ha⟩ := hS i
  exact ⟨a, F.map_homogeneousIso ha⟩

end Superfunctor

namespace MonoidalSuperequivalence

variable (E : MonoidalSuperequivalence C D)

theorem hasBWType_map_iff {X : C.data.Obj} {r : ZMod 8} :
    HasBWType D.data (E.data.forward.obj X) r ↔ HasBWType C.data X r := by
  refine ⟨fun h => ?_, E.forwardFunctor.map_bwType E.map_bijective E.map_grade_iff⟩
  have hb := E.backwardFunctor.map_bwType E.backward_map_bijective E.backward_map_grade_iff h
  have hu : SameParityOrbit C.data X (E.data.backward.obj (E.data.forward.obj X)) :=
    ⟨0, E.data.unitHom X, E.data.unitInv X, E.laws.unit_hom_inv X,
      E.laws.unit_inv_hom X, E.laws.unit_hom_even X, E.laws.unit_inv_even X⟩
  exact (SameParityOrbit.hasBWType_iff C.laws hu r).mpr hb

theorem hasBWType_backward_map_iff {Y : D.data.Obj} {r : ZMod 8} :
    HasBWType C.data (E.data.backward.obj Y) r ↔ HasBWType D.data Y r := by
  refine ⟨fun h => ?_, E.backwardFunctor.map_bwType E.backward_map_bijective
    E.backward_map_grade_iff⟩
  have hf := E.forwardFunctor.map_bwType E.map_bijective E.map_grade_iff h
  have hc : SameParityOrbit D.data (E.data.forward.obj (E.data.backward.obj Y)) Y :=
    ⟨0, E.data.counitHom Y, E.data.counitInv Y, E.laws.counit_hom_inv Y,
      E.laws.counit_inv_hom Y, E.laws.counit_hom_even Y, E.laws.counit_inv_even Y⟩
  exact (SameParityOrbit.hasBWType_iff D.laws hc r).mp hf

theorem sameParityOrbit_map_iff {X Y : C.data.Obj} :
    SameParityOrbit D.data (E.data.forward.obj X) (E.data.forward.obj Y) ↔
      SameParityOrbit C.data X Y :=
  exists_congr (fun _ => E.homogeneousIso_map_iff)

theorem sameParityOrbit_backward_map_iff {X Y : D.data.Obj} :
    SameParityOrbit C.data (E.data.backward.obj X) (E.data.backward.obj Y) ↔
      SameParityOrbit D.data X Y :=
  exists_congr (fun _ => E.homogeneousIso_backward_map_iff)

/-- Component transport retains the actual finite simple decomposition. -/
theorem inComponent_map {X : C.data.Obj} {r : ZMod 8} (hX : InComponent C.data r X) :
    InComponent D.data r (E.data.forward.obj X) := by
  obtain ⟨n, S, hs, hd⟩ := hX
  exact ⟨n, fun i => E.data.forward.obj (S i),
    fun i => ⟨(E.isSimple_map_iff _).mpr (hs i).1, E.hasBWType_map_iff.mpr (hs i).2⟩,
    E.forwardFunctor.map_decomposition hd⟩

theorem inComponent_backward_map {Y : D.data.Obj} {r : ZMod 8} (hY : InComponent D.data r Y) :
    InComponent C.data r (E.data.backward.obj Y) := by
  obtain ⟨n, S, hs, hd⟩ := hY
  exact ⟨n, fun i => E.data.backward.obj (S i),
    fun i => ⟨(E.isSimple_backward_map_iff _).mpr (hs i).1,
      E.hasBWType_backward_map_iff.mpr (hs i).2⟩,
    E.backwardFunctor.map_decomposition hd⟩

theorem inComponent_map_iff {X : C.data.Obj} {r : ZMod 8} :
    InComponent D.data r (E.data.forward.obj X) ↔ InComponent C.data r X := by
  refine ⟨fun h => ?_, E.inComponent_map⟩
  obtain ⟨n, S, hs, hd⟩ := E.inComponent_backward_map h
  exact ⟨n, S, hs, decomposition_of_evenIso C.laws hd
    ⟨E.data.unitInv X, E.data.unitHom X, E.laws.unit_inv_hom X,
      E.laws.unit_hom_inv X, E.laws.unit_inv_even X, E.laws.unit_hom_even X⟩⟩

end MonoidalSuperequivalence

/-- P is a property of the completed category up to the advertised equivalence. -/
theorem ReferenceProperty.of_equivalent {C D : PiSuperfusion.{0, 0}}
    (hC : ReferenceProperty C.data) (hE : Equivalent C D) : ReferenceProperty D.data := by
  obtain ⟨E⟩ := hE
  refine { D.laws with simple_type := ?_, realizes_type := ?_, type_detects_orbit := ?_ }
  · intro X hX
    obtain ⟨r, hr, hu⟩ := hC.simple_type (E.data.backward.obj X)
      ((E.isSimple_backward_map_iff X).mpr hX)
    exact ⟨r, E.hasBWType_backward_map_iff.mp hr,
      fun s hs => hu s (E.hasBWType_backward_map_iff.mpr hs)⟩
  · intro r
    obtain ⟨X, hX, hr⟩ := hC.realizes_type r
    exact ⟨E.data.forward.obj X, (E.isSimple_map_iff X).mpr hX, E.hasBWType_map_iff.mpr hr⟩
  · intro X Y r hX hY hr
    exact E.hasBWType_backward_map_iff.symm.trans
      ((hC.type_detects_orbit (E.data.backward.obj X) (E.data.backward.obj Y) r
        ((E.isSimple_backward_map_iff X).mpr hX) ((E.isSimple_backward_map_iff Y).mpr hY)
        (E.hasBWType_backward_map_iff.mpr hr)).trans E.sameParityOrbit_backward_map_iff)

end RMod.Classification

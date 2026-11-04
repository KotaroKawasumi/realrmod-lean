import RMod.BrundanEllis.StackingReferenceHexagonAtoms355
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn355
open Superfusion

theorem innerACB_alias : HexagonAtoms355.innerACB = HexagonAtoms355.innerABC :=
  HexagonAtoms355.innerACB_eq.symm.trans HexagonAtoms355.innerABC_eq

theorem assocCAB_alias : HexagonAtoms355.assocCAB = HexagonAtoms355.assocBAC :=
  HexagonAtoms355.assocCAB_eq.symm.trans HexagonAtoms355.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716844143606710847805623514792,
    decodeIntegerRow 64 3 1 1716841431547576139648217851716,
    decodeIntegerRow 64 3 1 1716842867343561406127734872484,
    decodeIntegerRow 64 3 1 1716843984073724493709641492952,
    decodeIntegerRow 64 3 1 1717022820443057053088171101672,
    decodeIntegerRow 64 3 1 1716803143653119754008735093956,
    decodeIntegerRow 64 3 1 1716919443128026386688702885924,
    decodeIntegerRow 64 3 1 1717009898271173487740957947672,
    decodeIntegerRow 64 3 1 1731495644187121639348224429352,
    decodeIntegerRow 64 3 1 1713701824202200093687616726596,
    decodeIntegerRow 64 3 1 1723122081669638575923515148964,
    decodeIntegerRow 64 3 1 1730448948264552983463802543192,
    decodeIntegerRow 64 3 1 2903794367456353397503577289832,
    decodeIntegerRow 64 3 1 1462494948677708195040942365636,
    decodeIntegerRow 64 3 1 2225535803540225271397585037604,
    decodeIntegerRow 64 3 1 2819011997728292272559723567512,
    decodeIntegerRow 64 3 1 1716843984073724219188144788004,
    decodeIntegerRow 64 3 1 1716840952948949797429764373912,
    decodeIntegerRow 64 3 1 1716841431547574950054980433048,
    decodeIntegerRow 64 3 1 1716839676685802185895250870844,
    decodeIntegerRow 64 3 1 1717009898271173484351803667364,
    decodeIntegerRow 64 3 1 1716764377164486082153092501592,
    decodeIntegerRow 64 3 1 1716803143653119739322398829528,
    decodeIntegerRow 64 3 1 1716660999849455438347986941884,
    decodeIntegerRow 64 3 1 1730448948264552983421961132324,
    decodeIntegerRow 64 3 1 1710561738622873908539074018072,
    decodeIntegerRow 64 3 1 1713701824202200093506303933208,
    decodeIntegerRow 64 3 1 1702188176105390845393307486524,
    decodeIntegerRow 64 3 1 2819011997728292272559207006884,
    decodeIntegerRow 64 3 1 1208148016752287213257853435352,
    decodeIntegerRow 64 3 1 1462494948677708195038703936088,
    decodeIntegerRow 64 3 1 529889452836159087155304920764,
    decodeIntegerRow 64 3 1 1971188847980302637210237134556,
    decodeIntegerRow 64 3 1 2903794316248266483955793180008,
    decodeIntegerRow 64 3 1 2819012052875462794841952608872,
    decodeIntegerRow 64 3 1 1208148004935036387056929257156,
    decodeIntegerRow 64 3 1 1719981995798528419952866075996,
    decodeIntegerRow 64 3 1 1731495643554923035477264130728,
    decodeIntegerRow 64 3 1 1730448948945382249170990557992,
    decodeIntegerRow 64 3 1 1710561738476981923225650798916,
    decodeIntegerRow 64 3 1 1716880676635790459401986383836,
    decodeIntegerRow 64 3 1 1717022820435252132052727068648,
    decodeIntegerRow 64 3 1 1717009898279578787317590055912,
    decodeIntegerRow 64 3 1 1716764377162684962345582555076,
    decodeIntegerRow 64 3 1 1716842388744891872525128554076,
    decodeIntegerRow 64 3 1 1716844143606614490755796841768,
    decodeIntegerRow 64 3 1 1716843984073828262840229950632,
    decodeIntegerRow 64 3 1 1716840952948928842287875629636,
    decodeIntegerRow 64 3 1 2225535815357476097603330448552,
    decodeIntegerRow 64 3 1 2819012052875462794841436048196,
    decodeIntegerRow 64 3 1 529889504044246000703089030564,
    decodeIntegerRow 64 3 1 1971188847980302637212475563992,
    decodeIntegerRow 64 3 1 1723122081815530561627458221032,
    decodeIntegerRow 64 3 1 1730448948945382249129149143236,
    decodeIntegerRow 64 3 1 1702188176737589449264267783204,
    decodeIntegerRow 64 3 1 1719981995798528420134178860312,
    decodeIntegerRow 64 3 1 1716919443129827538128320918312,
    decodeIntegerRow 64 3 1 1717009898279578783928435460676,
    decodeIntegerRow 64 3 1 1716660999857260359383430817444,
    decodeIntegerRow 64 3 1 1716880676635790474088321913432,
    decodeIntegerRow 64 3 1 1716842867343584923470378572392,
    decodeIntegerRow 64 3 1 1716843984073827988318707736516,
    decodeIntegerRow 64 3 1 1716839676685898542945064789284,
    decodeIntegerRow 64 3 1 1716842388744893062118306451352]

def rows_innerRightABC (r : RightIndex 3 5 5) : List ℤ := rows_innerRightABCData.getD (rightPosition 3 5 5 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 3 5 5) : (tripleIndices 4 2 8).map ((HexagonAtoms355.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_0_4
  · exact rows_innerRightABC_eq_0_0_5
  · exact rows_innerRightABC_eq_0_0_6
  · exact rows_innerRightABC_eq_0_0_7
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_1_2
  · exact rows_innerRightABC_eq_0_1_3
  · exact rows_innerRightABC_eq_0_1_4
  · exact rows_innerRightABC_eq_0_1_5
  · exact rows_innerRightABC_eq_0_1_6
  · exact rows_innerRightABC_eq_0_1_7
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_1_0_4
  · exact rows_innerRightABC_eq_1_0_5
  · exact rows_innerRightABC_eq_1_0_6
  · exact rows_innerRightABC_eq_1_0_7
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_1_1_2
  · exact rows_innerRightABC_eq_1_1_3
  · exact rows_innerRightABC_eq_1_1_4
  · exact rows_innerRightABC_eq_1_1_5
  · exact rows_innerRightABC_eq_1_1_6
  · exact rows_innerRightABC_eq_1_1_7
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_0_2
  · exact rows_innerRightABC_eq_2_0_3
  · exact rows_innerRightABC_eq_2_0_4
  · exact rows_innerRightABC_eq_2_0_5
  · exact rows_innerRightABC_eq_2_0_6
  · exact rows_innerRightABC_eq_2_0_7
  · exact rows_innerRightABC_eq_2_1_0
  · exact rows_innerRightABC_eq_2_1_1
  · exact rows_innerRightABC_eq_2_1_2
  · exact rows_innerRightABC_eq_2_1_3
  · exact rows_innerRightABC_eq_2_1_4
  · exact rows_innerRightABC_eq_2_1_5
  · exact rows_innerRightABC_eq_2_1_6
  · exact rows_innerRightABC_eq_2_1_7
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_0_2
  · exact rows_innerRightABC_eq_3_0_3
  · exact rows_innerRightABC_eq_3_0_4
  · exact rows_innerRightABC_eq_3_0_5
  · exact rows_innerRightABC_eq_3_0_6
  · exact rows_innerRightABC_eq_3_0_7
  · exact rows_innerRightABC_eq_3_1_0
  · exact rows_innerRightABC_eq_3_1_1
  · exact rows_innerRightABC_eq_3_1_2
  · exact rows_innerRightABC_eq_3_1_3
  · exact rows_innerRightABC_eq_3_1_4
  · exact rows_innerRightABC_eq_3_1_5
  · exact rows_innerRightABC_eq_3_1_6
  · exact rows_innerRightABC_eq_3_1_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716781607663588032612437301756,
    decodeIntegerRow 64 3 1 1716668175866764442022770866204,
    decodeIntegerRow 64 3 1 1716848122737621151327252814716,
    decodeIntegerRow 64 3 1 1716861399637762369043701602916,
    decodeIntegerRow 64 3 1 1716666740095104389238031666876,
    decodeIntegerRow 64 3 1 1716897905168052308176312447324,
    decodeIntegerRow 64 3 1 1716822579968798291095884568636,
    decodeIntegerRow 64 3 1 1716848601992793547351299938596,
    decodeIntegerRow 64 3 1 1716861240323714193568689729352,
    decodeIntegerRow 64 3 1 1716835218299718937285570930552,
    decodeIntegerRow 64 3 1 1716666740095104389172944001208,
    decodeIntegerRow 64 3 1 1716897905168052308363820762232,
    decodeIntegerRow 64 3 1 1716835697554891333309790477512,
    decodeIntegerRow 64 3 1 1716822420654750115606906425592,
    decodeIntegerRow 64 3 1 1716781607663588032423379278648,
    decodeIntegerRow 64 3 1 1716668175866764441962332167672,
    decodeIntegerRow 64 3 1 2856693054880299827571567096328,
    decodeIntegerRow 64 3 1 2112492720714796893102870922952,
    decodeIntegerRow 64 3 1 1589145087683544369553427358712,
    decodeIntegerRow 64 3 1 1676020794771522935341094811592,
    decodeIntegerRow 64 3 1 1349451871761204183769372556168,
    decodeIntegerRow 64 3 1 2866113312274788626452227569992,
    decodeIntegerRow 64 3 1 1672880708973258708462756670072,
    decodeIntegerRow 64 3 1 1843492037342946746698816821832,
    decodeIntegerRow 64 3 1 1760803111319253638369478620836,
    decodeIntegerRow 64 3 1 1590191782949565782018039959996,
    decodeIntegerRow 64 3 1 1349451871761205414032433466916,
    decodeIntegerRow 64 3 1 2866113312274788199418768410564,
    decodeIntegerRow 64 3 1 1844538732608968067656259600356,
    decodeIntegerRow 64 3 1 1757663025520989412620858625276,
    decodeIntegerRow 64 3 1 2856693054880299431040497876836,
    decodeIntegerRow 64 3 1 2112492720714795652672346698884,
    decodeIntegerRow 64 3 1 1590191782957704246687477244156,
    decodeIntegerRow 64 3 1 1760803111321855278714626601244,
    decodeIntegerRow 64 3 1 2866113312273891337647364119676,
    decodeIntegerRow 64 3 1 1349451871760894106640706358116,
    decodeIntegerRow 64 3 1 1757663025523791179146402604476,
    decodeIntegerRow 64 3 1 1844538732600896311713620982364,
    decodeIntegerRow 64 3 1 2112492720715084723821807585596,
    decodeIntegerRow 64 3 1 2856693054879395157188338178596,
    decodeIntegerRow 64 3 1 1321191099577426520405517278648,
    decodeIntegerRow 64 3 1 576990765413116930938441691528,
    decodeIntegerRow 64 3 1 1757663025523791315842298265672,
    decodeIntegerRow 64 3 1 1844538732600896359161783109768,
    decodeIntegerRow 64 3 1 567570508018620719977025810488,
    decodeIntegerRow 64 3 1 2084231948531619608280203642888,
    decodeIntegerRow 64 3 1 1590191782957704202628469554632,
    decodeIntegerRow 64 3 1 1760803111321855416540240408328,
    decodeIntegerRow 64 3 1 1716835201230356632769614314232,
    decodeIntegerRow 64 3 1 1716861186927247497390648515128,
    decodeIntegerRow 64 3 1 1716897907210540105485388002568,
    decodeIntegerRow 64 3 1 1716666745979414471356498564408,
    decodeIntegerRow 64 3 1 1716822473613540855258897494392,
    decodeIntegerRow 64 3 1 1716835679172501159215685314488,
    decodeIntegerRow 64 3 1 1716668181799705185982114524808,
    decodeIntegerRow 64 3 1 1716781605766992220810495210168,
    decodeIntegerRow 64 3 1 1717015638492807298615298070436,
    decodeIntegerRow 64 3 1 1716902214525520263658289504956,
    decodeIntegerRow 64 3 1 1716822473613540855266120131876,
    decodeIntegerRow 64 3 1 1716835679172501159236548743364,
    decodeIntegerRow 64 3 1 1716785913081972379359975805156,
    decodeIntegerRow 64 3 1 1717017074313098013236264906236,
    decodeIntegerRow 64 3 1 1716835201230356632790649693796,
    decodeIntegerRow 64 3 1 1716861186927247497383943146884]

def rows_inverseACB (r : LeftIndex 3 5 5) : List ℤ := rows_inverseACBData.getD (leftPosition 3 5 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 5 5) : (tripleIndices 4 2 8).map ((HexagonAtoms355.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_0_4
  · exact rows_inverseACB_eq_2_0_5
  · exact rows_inverseACB_eq_2_0_6
  · exact rows_inverseACB_eq_2_0_7
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_0_4
  · exact rows_inverseACB_eq_3_0_5
  · exact rows_inverseACB_eq_3_0_6
  · exact rows_inverseACB_eq_3_0_7
  · exact rows_inverseACB_eq_4_0_0
  · exact rows_inverseACB_eq_4_0_1
  · exact rows_inverseACB_eq_4_0_2
  · exact rows_inverseACB_eq_4_0_3
  · exact rows_inverseACB_eq_4_0_4
  · exact rows_inverseACB_eq_4_0_5
  · exact rows_inverseACB_eq_4_0_6
  · exact rows_inverseACB_eq_4_0_7
  · exact rows_inverseACB_eq_5_0_0
  · exact rows_inverseACB_eq_5_0_1
  · exact rows_inverseACB_eq_5_0_2
  · exact rows_inverseACB_eq_5_0_3
  · exact rows_inverseACB_eq_5_0_4
  · exact rows_inverseACB_eq_5_0_5
  · exact rows_inverseACB_eq_5_0_6
  · exact rows_inverseACB_eq_5_0_7
  · exact rows_inverseACB_eq_6_0_0
  · exact rows_inverseACB_eq_6_0_1
  · exact rows_inverseACB_eq_6_0_2
  · exact rows_inverseACB_eq_6_0_3
  · exact rows_inverseACB_eq_6_0_4
  · exact rows_inverseACB_eq_6_0_5
  · exact rows_inverseACB_eq_6_0_6
  · exact rows_inverseACB_eq_6_0_7
  · exact rows_inverseACB_eq_7_0_0
  · exact rows_inverseACB_eq_7_0_1
  · exact rows_inverseACB_eq_7_0_2
  · exact rows_inverseACB_eq_7_0_3
  · exact rows_inverseACB_eq_7_0_4
  · exact rows_inverseACB_eq_7_0_5
  · exact rows_inverseACB_eq_7_0_6
  · exact rows_inverseACB_eq_7_0_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 64 3 1 1702369074897160498975970756200,
    decodeIntegerRow 64 3 1 1720020736831664404814190084760,
    decodeIntegerRow 64 3 1 1710484233140894478769674209632,
    decodeIntegerRow 64 3 1 1703402853908049826335217229728,
    decodeIntegerRow 64 3 1 529891711756517853907658587240,
    decodeIntegerRow 64 3 1 1971189338076210165543876103320,
    decodeIntegerRow 64 3 1 1208147053990962162002853297632,
    decodeIntegerRow 64 3 1 614673868846109516694315543328,
    decodeIntegerRow 64 3 1 1703066889467060865529418006680,
    decodeIntegerRow 64 3 1 1723044576333447088010713327720,
    decodeIntegerRow 64 3 1 1719943255057080598283419761568,
    decodeIntegerRow 64 3 1 1731676542346647026982187300192,
    decodeIntegerRow 64 3 1 614669721136961505027732966040,
    decodeIntegerRow 64 3 1 2225534852587745743380133305960,
    decodeIntegerRow 64 3 1 1971188381511091847028371105568,
    decodeIntegerRow 64 3 1 2903796575165022964774682970592,
    decodeIntegerRow 64 3 1 1702007277945864268084692482848,
    decodeIntegerRow 64 3 1 1719943255057080049239368093152,
    decodeIntegerRow 64 3 1 1710639243959065122125110086760,
    decodeIntegerRow 64 3 1 1703066889467062146627385023640,
    decodeIntegerRow 64 3 1 529887245127489505378136633248,
    decodeIntegerRow 64 3 1 1971188381511091840166409165152,
    decodeIntegerRow 64 3 1 1208148967704766737846747567720,
    decodeIntegerRow 64 3 1 614669721136961520648539837080,
    decodeIntegerRow 64 3 1 1730280966384461377219843924768,
    decodeIntegerRow 64 3 1 1710484233140894204248680973792,
    decodeIntegerRow 64 3 1 1713663083460848628885645165160,
    decodeIntegerRow 64 3 1 1702369074897159309380524748440,
    decodeIntegerRow 64 3 1 2819009951446402951952232331168,
    decodeIntegerRow 64 3 1 1208147053990962158655512637792,
    decodeIntegerRow 64 3 1 1462494482216302325808628796520,
    decodeIntegerRow 64 3 1 529891711756517839040016278680,
    decodeIntegerRow 64 3 1 614673868990200366579421944880,
    decodeIntegerRow 64 3 1 1208147053301727596719005699120,
    decodeIntegerRow 64 3 1 1462494481576298794207598494656,
    decodeIntegerRow 64 3 1 2903792108247812930979945812416,
    decodeIntegerRow 64 3 1 1703402865725278416296285642800,
    decodeIntegerRow 64 3 1 1710484177993620187356869128240,
    decodeIntegerRow 64 3 1 1713663032252664809246054961856,
    decodeIntegerRow 64 3 1 1731314721760894805759741108416,
    decodeIntegerRow 64 3 1 529887244832103277618665471280,
    decodeIntegerRow 64 3 1 1462495439405814320464964566320,
    decodeIntegerRow 64 3 1 2225534851915321777249549608896,
    decodeIntegerRow 64 3 1 614669720989268383895498585536,
    decodeIntegerRow 64 3 1 1702007254311319332784459678000,
    decodeIntegerRow 64 3 1 1713740616443422442872392769840,
    decodeIntegerRow 64 3 1 1723044521186380334859059644096,
    decodeIntegerRow 64 3 1 1703066877649787803083817145536,
    decodeIntegerRow 64 3 1 2819014099303244085141569141824,
    decodeIntegerRow 64 3 1 2225534851915321780680573094464,
    decodeIntegerRow 64 3 1 1971188380886698157330863061040,
    decodeIntegerRow 64 3 1 529887244832103263113648740400,
    decodeIntegerRow 64 3 1 1730616942642723400476065237824,
    decodeIntegerRow 64 3 1 1723044521186380609381086009664,
    decodeIntegerRow 64 3 1 1719943203849089492741403907120,
    decodeIntegerRow 64 3 1 1702007254311318143193490527280,
    decodeIntegerRow 64 3 1 529891712044699538810248213696,
    decodeIntegerRow 64 3 1 1462494481576298800902194783936,
    decodeIntegerRow 64 3 1 2225536766990784891286128780240,
    decodeIntegerRow 64 3 1 614673868990200382590748668880,
    decodeIntegerRow 64 3 1 1702369098531616489302661813696,
    decodeIntegerRow 64 3 1 1713663032252665358288040396736,
    decodeIntegerRow 64 3 1 1723199642298892571821972522960,
    decodeIntegerRow 64 3 1 1703402865725279697399073896400]

def rows_assocBCA (r : RightIndex 5 5 3) : List ℤ := rows_assocBCAData.getD (rightPosition 5 5 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 5 3) : (tripleIndices 4 2 8).map ((HexagonAtoms355.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_0_4
  · exact rows_assocBCA_eq_2_0_5
  · exact rows_assocBCA_eq_2_0_6
  · exact rows_assocBCA_eq_2_0_7
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_0_4
  · exact rows_assocBCA_eq_3_0_5
  · exact rows_assocBCA_eq_3_0_6
  · exact rows_assocBCA_eq_3_0_7
  · exact rows_assocBCA_eq_4_0_0
  · exact rows_assocBCA_eq_4_0_1
  · exact rows_assocBCA_eq_4_0_2
  · exact rows_assocBCA_eq_4_0_3
  · exact rows_assocBCA_eq_4_0_4
  · exact rows_assocBCA_eq_4_0_5
  · exact rows_assocBCA_eq_4_0_6
  · exact rows_assocBCA_eq_4_0_7
  · exact rows_assocBCA_eq_5_0_0
  · exact rows_assocBCA_eq_5_0_1
  · exact rows_assocBCA_eq_5_0_2
  · exact rows_assocBCA_eq_5_0_3
  · exact rows_assocBCA_eq_5_0_4
  · exact rows_assocBCA_eq_5_0_5
  · exact rows_assocBCA_eq_5_0_6
  · exact rows_assocBCA_eq_5_0_7
  · exact rows_assocBCA_eq_6_0_0
  · exact rows_assocBCA_eq_6_0_1
  · exact rows_assocBCA_eq_6_0_2
  · exact rows_assocBCA_eq_6_0_3
  · exact rows_assocBCA_eq_6_0_4
  · exact rows_assocBCA_eq_6_0_5
  · exact rows_assocBCA_eq_6_0_6
  · exact rows_assocBCA_eq_6_0_7
  · exact rows_assocBCA_eq_7_0_0
  · exact rows_assocBCA_eq_7_0_1
  · exact rows_assocBCA_eq_7_0_2
  · exact rows_assocBCA_eq_7_0_3
  · exact rows_assocBCA_eq_7_0_4
  · exact rows_assocBCA_eq_7_0_5
  · exact rows_assocBCA_eq_7_0_6
  · exact rows_assocBCA_eq_7_0_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 64 3 1 1717363107038282381294630733760,
    decodeIntegerRow 64 3 1 1718412669954502558172933437408,
    decodeIntegerRow 64 3 1 1721551772955508984598560614040,
    decodeIntegerRow 64 3 1 1730972384867826454722581994880,
    decodeIntegerRow 64 3 1 1759058619246919576260622615360,
    decodeIntegerRow 64 3 1 1844073534696700172956406691808,
    decodeIntegerRow 64 3 1 2098342951049278661893419980440,
    decodeIntegerRow 64 3 1 2861409644768407306178659463040,
    decodeIntegerRow 64 3 1 1702711453151462831968061344000,
    decodeIntegerRow 64 3 1 1721551826132837528494082067904,
    decodeIntegerRow 64 3 1 1715271148360363011244471637680,
    decodeIntegerRow 64 3 1 1717363101132358673322111698560,
    decodeIntegerRow 64 3 1 572274175742953863060162560000,
    decodeIntegerRow 64 3 1 2098342951705790125981935431104,
    decodeIntegerRow 64 3 1 1589610285571396871751259272880,
    decodeIntegerRow 64 3 1 1759058619174007075067672986240,
    decodeIntegerRow 64 3 1 1589726585069718282977040307840,
    decodeIntegerRow 64 3 1 1759407517668971308242919032400,
    decodeIntegerRow 64 3 1 2861396722604618146493193031104,
    decodeIntegerRow 64 3 1 1335302102751900933418220769280,
    decodeIntegerRow 64 3 1 1715272586125880199319199355520,
    decodeIntegerRow 64 3 1 1717367414428910237540087621200,
    decodeIntegerRow 64 3 1 1730972225334039738249540627904,
    decodeIntegerRow 64 3 1 1712131568738645212843637889280,
    decodeIntegerRow 64 3 1 1335302102095384527942535047040,
    decodeIntegerRow 64 3 1 572287097906721610067891148440,
    decodeIntegerRow 64 3 1 1759407517595991823801661277472,
    decodeIntegerRow 64 3 1 1843957235247009423943426087360,
    decodeIntegerRow 64 3 1 1712131515560716320909318378880,
    decodeIntegerRow 64 3 1 1702711612683448422985002034840,
    decodeIntegerRow 64 3 1 1717367408517583119307722179872,
    decodeIntegerRow 64 3 1 1718411236128068978837299696960,
    decodeIntegerRow 64 3 1 1718411236128068979399837434176,
    decodeIntegerRow 64 3 1 1717367408517583121003073172480,
    decodeIntegerRow 64 3 1 1730972207609064066756291733120,
    decodeIntegerRow 64 3 1 1721552304731796178999821340240,
    decodeIntegerRow 64 3 1 1843957235247009469508724678976,
    decodeIntegerRow 64 3 1 1759407517595991961125178113280,
    decodeIntegerRow 64 3 1 2861396722385791286351301069440,
    decodeIntegerRow 64 3 1 2098381718197129192069080297040,
    decodeIntegerRow 64 3 1 1721552251553867256562939703008,
    decodeIntegerRow 64 3 1 1702711594958472751491810535360,
    decodeIntegerRow 64 3 1 1717367414428910235844734494080,
    decodeIntegerRow 64 3 1 1715272586125880199881730718360,
    decodeIntegerRow 64 3 1 2098381717540610315885862301408,
    decodeIntegerRow 64 3 1 572287097687894749925999895360,
    decodeIntegerRow 64 3 1 1759407517668971170919402170240,
    decodeIntegerRow 64 3 1 1589726585069718328542338820760,
    decodeIntegerRow 64 3 1 1759058619174006937869680388760,
    decodeIntegerRow 64 3 1 1589610285571396917693130579840,
    decodeIntegerRow 64 3 1 1335340868586723594015732775360,
    decodeIntegerRow 64 3 1 2861409644549558209794501987872,
    decodeIntegerRow 64 3 1 1717363101132358671628310379160,
    decodeIntegerRow 64 3 1 1715271148360363011811658423680,
    decodeIntegerRow 64 3 1 1712131994159674971414885463360,
    decodeIntegerRow 64 3 1 1730972367141049647605826506272,
    decodeIntegerRow 64 3 1 572274175524104766676004376240,
    decodeIntegerRow 64 3 1 1335340869243232587424610227840,
    decodeIntegerRow 64 3 1 1844073534696700218898277920000,
    decodeIntegerRow 64 3 1 1759058619246919713458615238976,
    decodeIntegerRow 64 3 1 1702711435424686024851248459440,
    decodeIntegerRow 64 3 1 1712132047337003484808189164160,
    decodeIntegerRow 64 3 1 1718412669954502558740113843200,
    decodeIntegerRow 64 3 1 1717363107038282382988434170176]

def rows_assocBAC (r : RightIndex 5 3 5) : List ℤ := rows_assocBACData.getD (rightPosition 5 3 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 5 3 5) : (tripleIndices 8 1 8).map ((HexagonAtoms355.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_0_4
  · exact rows_assocBAC_eq_1_0_5
  · exact rows_assocBAC_eq_1_0_6
  · exact rows_assocBAC_eq_1_0_7
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_2_0_4
  · exact rows_assocBAC_eq_2_0_5
  · exact rows_assocBAC_eq_2_0_6
  · exact rows_assocBAC_eq_2_0_7
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3
  · exact rows_assocBAC_eq_3_0_4
  · exact rows_assocBAC_eq_3_0_5
  · exact rows_assocBAC_eq_3_0_6
  · exact rows_assocBAC_eq_3_0_7
  · exact rows_assocBAC_eq_4_0_0
  · exact rows_assocBAC_eq_4_0_1
  · exact rows_assocBAC_eq_4_0_2
  · exact rows_assocBAC_eq_4_0_3
  · exact rows_assocBAC_eq_4_0_4
  · exact rows_assocBAC_eq_4_0_5
  · exact rows_assocBAC_eq_4_0_6
  · exact rows_assocBAC_eq_4_0_7
  · exact rows_assocBAC_eq_5_0_0
  · exact rows_assocBAC_eq_5_0_1
  · exact rows_assocBAC_eq_5_0_2
  · exact rows_assocBAC_eq_5_0_3
  · exact rows_assocBAC_eq_5_0_4
  · exact rows_assocBAC_eq_5_0_5
  · exact rows_assocBAC_eq_5_0_6
  · exact rows_assocBAC_eq_5_0_7
  · exact rows_assocBAC_eq_6_0_0
  · exact rows_assocBAC_eq_6_0_1
  · exact rows_assocBAC_eq_6_0_2
  · exact rows_assocBAC_eq_6_0_3
  · exact rows_assocBAC_eq_6_0_4
  · exact rows_assocBAC_eq_6_0_5
  · exact rows_assocBAC_eq_6_0_6
  · exact rows_assocBAC_eq_6_0_7
  · exact rows_assocBAC_eq_7_0_0
  · exact rows_assocBAC_eq_7_0_1
  · exact rows_assocBAC_eq_7_0_2
  · exact rows_assocBAC_eq_7_0_3
  · exact rows_assocBAC_eq_7_0_4
  · exact rows_assocBAC_eq_7_0_5
  · exact rows_assocBAC_eq_7_0_6
  · exact rows_assocBAC_eq_7_0_7

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716781607663588032612437301756,
    decodeIntegerRow 64 3 1 1716668175866764442022770866204,
    decodeIntegerRow 64 3 1 1716848122737621151327252814716,
    decodeIntegerRow 64 3 1 1716861399637762369043701602916,
    decodeIntegerRow 64 3 1 1716666740095104389238031666876,
    decodeIntegerRow 64 3 1 1716897905168052308176312447324,
    decodeIntegerRow 64 3 1 1716822579968798291095884568636,
    decodeIntegerRow 64 3 1 1716848601992793547351299938596,
    decodeIntegerRow 64 3 1 1716861240323714193568689729352,
    decodeIntegerRow 64 3 1 1716835218299718937285570930552,
    decodeIntegerRow 64 3 1 1716666740095104389172944001208,
    decodeIntegerRow 64 3 1 1716897905168052308363820762232,
    decodeIntegerRow 64 3 1 1716835697554891333309790477512,
    decodeIntegerRow 64 3 1 1716822420654750115606906425592,
    decodeIntegerRow 64 3 1 1716781607663588032423379278648,
    decodeIntegerRow 64 3 1 1716668175866764441962332167672,
    decodeIntegerRow 64 3 1 2856693054880299827571567096328,
    decodeIntegerRow 64 3 1 2112492720714796893102870922952,
    decodeIntegerRow 64 3 1 1589145087683544369553427358712,
    decodeIntegerRow 64 3 1 1676020794771522935341094811592,
    decodeIntegerRow 64 3 1 1349451871761204183769372556168,
    decodeIntegerRow 64 3 1 2866113312274788626452227569992,
    decodeIntegerRow 64 3 1 1672880708973258708462756670072,
    decodeIntegerRow 64 3 1 1843492037342946746698816821832,
    decodeIntegerRow 64 3 1 1760803111319253638369478620836,
    decodeIntegerRow 64 3 1 1590191782949565782018039959996,
    decodeIntegerRow 64 3 1 1349451871761205414032433466916,
    decodeIntegerRow 64 3 1 2866113312274788199418768410564,
    decodeIntegerRow 64 3 1 1844538732608968067656259600356,
    decodeIntegerRow 64 3 1 1757663025520989412620858625276,
    decodeIntegerRow 64 3 1 2856693054880299431040497876836,
    decodeIntegerRow 64 3 1 2112492720714795652672346698884,
    decodeIntegerRow 64 3 1 1590191782957704246687477244156,
    decodeIntegerRow 64 3 1 1760803111321855278714626601244,
    decodeIntegerRow 64 3 1 2866113312273891337647364119676,
    decodeIntegerRow 64 3 1 1349451871760894106640706358116,
    decodeIntegerRow 64 3 1 1757663025523791179146402604476,
    decodeIntegerRow 64 3 1 1844538732600896311713620982364,
    decodeIntegerRow 64 3 1 2112492720715084723821807585596,
    decodeIntegerRow 64 3 1 2856693054879395157188338178596,
    decodeIntegerRow 64 3 1 1321191099577426520405517278648,
    decodeIntegerRow 64 3 1 576990765413116930938441691528,
    decodeIntegerRow 64 3 1 1757663025523791315842298265672,
    decodeIntegerRow 64 3 1 1844538732600896359161783109768,
    decodeIntegerRow 64 3 1 567570508018620719977025810488,
    decodeIntegerRow 64 3 1 2084231948531619608280203642888,
    decodeIntegerRow 64 3 1 1590191782957704202628469554632,
    decodeIntegerRow 64 3 1 1760803111321855416540240408328,
    decodeIntegerRow 64 3 1 1716835201230356632769614314232,
    decodeIntegerRow 64 3 1 1716861186927247497390648515128,
    decodeIntegerRow 64 3 1 1716897907210540105485388002568,
    decodeIntegerRow 64 3 1 1716666745979414471356498564408,
    decodeIntegerRow 64 3 1 1716822473613540855258897494392,
    decodeIntegerRow 64 3 1 1716835679172501159215685314488,
    decodeIntegerRow 64 3 1 1716668181799705185982114524808,
    decodeIntegerRow 64 3 1 1716781605766992220810495210168,
    decodeIntegerRow 64 3 1 1717015638492807298615298070436,
    decodeIntegerRow 64 3 1 1716902214525520263658289504956,
    decodeIntegerRow 64 3 1 1716822473613540855266120131876,
    decodeIntegerRow 64 3 1 1716835679172501159236548743364,
    decodeIntegerRow 64 3 1 1716785913081972379359975805156,
    decodeIntegerRow 64 3 1 1717017074313098013236264906236,
    decodeIntegerRow 64 3 1 1716835201230356632790649693796,
    decodeIntegerRow 64 3 1 1716861186927247497383943146884]

def cols_assocABC (r : LeftIndex 3 5 5) : List ℤ := cols_assocABCData.getD (leftPosition 3 5 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 5 5) : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms355.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_0_4
  · exact cols_assocABC_eq_0_0_5
  · exact cols_assocABC_eq_0_0_6
  · exact cols_assocABC_eq_0_0_7
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_0_4
  · exact cols_assocABC_eq_1_0_5
  · exact cols_assocABC_eq_1_0_6
  · exact cols_assocABC_eq_1_0_7
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_2_0_4
  · exact cols_assocABC_eq_2_0_5
  · exact cols_assocABC_eq_2_0_6
  · exact cols_assocABC_eq_2_0_7
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_3_0_4
  · exact cols_assocABC_eq_3_0_5
  · exact cols_assocABC_eq_3_0_6
  · exact cols_assocABC_eq_3_0_7
  · exact cols_assocABC_eq_4_0_0
  · exact cols_assocABC_eq_4_0_1
  · exact cols_assocABC_eq_4_0_2
  · exact cols_assocABC_eq_4_0_3
  · exact cols_assocABC_eq_4_0_4
  · exact cols_assocABC_eq_4_0_5
  · exact cols_assocABC_eq_4_0_6
  · exact cols_assocABC_eq_4_0_7
  · exact cols_assocABC_eq_5_0_0
  · exact cols_assocABC_eq_5_0_1
  · exact cols_assocABC_eq_5_0_2
  · exact cols_assocABC_eq_5_0_3
  · exact cols_assocABC_eq_5_0_4
  · exact cols_assocABC_eq_5_0_5
  · exact cols_assocABC_eq_5_0_6
  · exact cols_assocABC_eq_5_0_7
  · exact cols_assocABC_eq_6_0_0
  · exact cols_assocABC_eq_6_0_1
  · exact cols_assocABC_eq_6_0_2
  · exact cols_assocABC_eq_6_0_3
  · exact cols_assocABC_eq_6_0_4
  · exact cols_assocABC_eq_6_0_5
  · exact cols_assocABC_eq_6_0_6
  · exact cols_assocABC_eq_6_0_7
  · exact cols_assocABC_eq_7_0_0
  · exact cols_assocABC_eq_7_0_1
  · exact cols_assocABC_eq_7_0_2
  · exact cols_assocABC_eq_7_0_3
  · exact cols_assocABC_eq_7_0_4
  · exact cols_assocABC_eq_7_0_5
  · exact cols_assocABC_eq_7_0_6
  · exact cols_assocABC_eq_7_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 64 5 2 270701382420682534758767504245080642684545312,
    decodeIntegerRow 64 5 2 271106143089039619547887612134209060767225312,
    decodeIntegerRow 64 5 2 270967143169198720903707761317485427953165312,
    decodeIntegerRow 64 5 2 270706924654135150377454627305230789208045312,
    decodeIntegerRow 64 5 2 52475386043581716839980814510393132934570272,
    decodeIntegerRow 64 5 2 305745012783018538386386357093095840942382560,
    decodeIntegerRow 64 5 2 219008838628911370535206517722368300903320064,
    decodeIntegerRow 64 5 2 55944832981324657921504679924058928833007872,
    decodeIntegerRow 64 5 2 270705823313349469573052991181650466895545312,
    decodeIntegerRow 64 5 2 271133676622892494373033661395305252172225312,
    decodeIntegerRow 64 5 2 271105965456175113098337221890697097679725312,
    decodeIntegerRow 64 5 2 271400822926196383376421947032251052840845312,
    decodeIntegerRow 64 5 2 55944831219179400832217637354326233520507872,
    decodeIntegerRow 64 5 2 323092247187519788865756706740617812622070560,
    decodeIntegerRow 64 5 2 305745012498805955176067076480150161254882560,
    decodeIntegerRow 64 5 2 489625701989737102885555926853227605590820352,
    decodeIntegerRow 64 5 2 270700263316555833627285975962915115340845312,
    decodeIntegerRow 64 5 2 271105965456175113098332751542320633033165312,
    decodeIntegerRow 64 5 2 270967409619859722630689758807414627172225312,
    decodeIntegerRow 64 5 2 270705823313349469573071766644677810692345312,
    decodeIntegerRow 64 5 2 52475384253015114118170444065141668090820352,
    decodeIntegerRow 64 5 2 305745012498805955176067069316148819458008064,
    decodeIntegerRow 64 5 2 219008839055232428137969688918352187622070560,
    decodeIntegerRow 64 5 2 55944831219179400832217667347002044067382752,
    decodeIntegerRow 64 5 2 271394161588617066626252997666558914208045312,
    decodeIntegerRow 64 5 2 270967143169198720903704781085258865259725312,
    decodeIntegerRow 64 5 2 270994943153712597455843258649101638892225312,
    decodeIntegerRow 64 5 2 270701382420682534758749026805124588028345312,
    decodeIntegerRow 64 5 2 486156253261427559082221690422105803833007872,
    decodeIntegerRow 64 5 2 219008838628911370535206512961625992309570560,
    decodeIntegerRow 64 5 2 236356073459733678617340050482988419067382560,
    decodeIntegerRow 64 5 2 52475386043581716839980784899187097778320352,
    decodeIntegerRow 64 5 2 55944832981325384353112879997301087036132752,
    decodeIntegerRow 64 5 2 219008838628906779347744307067155777465820560,
    decodeIntegerRow 64 5 2 236356073459729160305869296347856583129882560,
    decodeIntegerRow 64 5 2 489625700199169410516333285814714421997070272,
    decodeIntegerRow 64 5 2 270706924654589897726478446274957351661095312,
    decodeIntegerRow 64 5 2 270967143166333812581388372927898025415975312,
    decodeIntegerRow 64 5 2 270994943150893163868794310837993240454725312,
    decodeIntegerRow 64 5 2 271399703821387561221423167735300369247045312,
    decodeIntegerRow 64 5 2 52475384253014020978298518663835515747070352,
    decodeIntegerRow 64 5 2 236356073743950765703630164408922133911132560,
    decodeIntegerRow 64 5 2 323092247187515212346625046279191910278320064,
    decodeIntegerRow 64 5 2 55944831219178672072303000742387786254882752,
    decodeIntegerRow 64 5 2 270700263315873712598180789500437087997095312,
    decodeIntegerRow 64 5 2 270995120789396537469336856156578445335975312,
    decodeIntegerRow 64 5 2 271133676620027586074183601886027908228165312,
    decodeIntegerRow 64 5 2 270705823312894722220303881913461990379845312,
    decodeIntegerRow 64 5 2 486156255023573544931423369699907317504882752,
    decodeIntegerRow 64 5 2 323092247187515212346625051055193007934570560,
    decodeIntegerRow 64 5 2 305745012498801451300096228862047133911132560,
    decodeIntegerRow 64 5 2 52475384253014020978298489147233972778320272,
    decodeIntegerRow 64 5 2 271395262929857494783403743058481521629845312,
    decodeIntegerRow 64 5 2 271133676620027586074186582118278884984725312,
    decodeIntegerRow 64 5 2 271105965453355679534385073930015945335975312,
    decodeIntegerRow 64 5 2 270700263315873712598162312060632400528295312,
    decodeIntegerRow 64 5 2 52475386043582806487393085009050359497070272,
    decodeIntegerRow 64 5 2 236356073459729160305869303488969741333008064,
    decodeIntegerRow 64 5 2 323092247613845437655982098128557144653320560,
    decodeIntegerRow 64 5 2 55944832981325384353112910086107268676757872,
    decodeIntegerRow 64 5 2 270701382421364655782284755259714431747045312,
    decodeIntegerRow 64 5 2 270994943150893163868798781186333084008165312,
    decodeIntegerRow 64 5 2 271133943076418404422341007739299392603475312,
    decodeIntegerRow 64 5 2 270706924654589897726497221738138504051795312]

def cols_right0 (r : LeftIndex 3 5 5) : List ℤ := cols_right0Data.getD (leftPosition 3 5 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 5 5) : (tripleIndices 4 2 8).map (fun j => (right0Middle3 5 5) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_0_4
  · exact cols_right0_eq_2_0_5
  · exact cols_right0_eq_2_0_6
  · exact cols_right0_eq_2_0_7
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_0_4
  · exact cols_right0_eq_3_0_5
  · exact cols_right0_eq_3_0_6
  · exact cols_right0_eq_3_0_7
  · exact cols_right0_eq_4_0_0
  · exact cols_right0_eq_4_0_1
  · exact cols_right0_eq_4_0_2
  · exact cols_right0_eq_4_0_3
  · exact cols_right0_eq_4_0_4
  · exact cols_right0_eq_4_0_5
  · exact cols_right0_eq_4_0_6
  · exact cols_right0_eq_4_0_7
  · exact cols_right0_eq_5_0_0
  · exact cols_right0_eq_5_0_1
  · exact cols_right0_eq_5_0_2
  · exact cols_right0_eq_5_0_3
  · exact cols_right0_eq_5_0_4
  · exact cols_right0_eq_5_0_5
  · exact cols_right0_eq_5_0_6
  · exact cols_right0_eq_5_0_7
  · exact cols_right0_eq_6_0_0
  · exact cols_right0_eq_6_0_1
  · exact cols_right0_eq_6_0_2
  · exact cols_right0_eq_6_0_3
  · exact cols_right0_eq_6_0_4
  · exact cols_right0_eq_6_0_5
  · exact cols_right0_eq_6_0_6
  · exact cols_right0_eq_6_0_7
  · exact cols_right0_eq_7_0_0
  · exact cols_right0_eq_7_0_1
  · exact cols_right0_eq_7_0_2
  · exact cols_right0_eq_7_0_3
  · exact cols_right0_eq_7_0_4
  · exact cols_right0_eq_7_0_5
  · exact cols_right0_eq_7_0_6
  · exact cols_right0_eq_7_0_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1716781607663588032612437301756,
    decodeIntegerRow 64 3 1 1716668175866764442022770866204,
    decodeIntegerRow 64 3 1 1716848122737621151327252814716,
    decodeIntegerRow 64 3 1 1716861399637762369043701602916,
    decodeIntegerRow 64 3 1 1716666740095104389238031666876,
    decodeIntegerRow 64 3 1 1716897905168052308176312447324,
    decodeIntegerRow 64 3 1 1716822579968798291095884568636,
    decodeIntegerRow 64 3 1 1716848601992793547351299938596,
    decodeIntegerRow 64 3 1 1716861240323714193568689729352,
    decodeIntegerRow 64 3 1 1716835218299718937285570930552,
    decodeIntegerRow 64 3 1 1716666740095104389172944001208,
    decodeIntegerRow 64 3 1 1716897905168052308363820762232,
    decodeIntegerRow 64 3 1 1716835697554891333309790477512,
    decodeIntegerRow 64 3 1 1716822420654750115606906425592,
    decodeIntegerRow 64 3 1 1716781607663588032423379278648,
    decodeIntegerRow 64 3 1 1716668175866764441962332167672,
    decodeIntegerRow 64 3 1 2856693054880299827571567096328,
    decodeIntegerRow 64 3 1 2112492720714796893102870922952,
    decodeIntegerRow 64 3 1 1589145087683544369553427358712,
    decodeIntegerRow 64 3 1 1676020794771522935341094811592,
    decodeIntegerRow 64 3 1 1349451871761204183769372556168,
    decodeIntegerRow 64 3 1 2866113312274788626452227569992,
    decodeIntegerRow 64 3 1 1672880708973258708462756670072,
    decodeIntegerRow 64 3 1 1843492037342946746698816821832,
    decodeIntegerRow 64 3 1 1760803111319253638369478620836,
    decodeIntegerRow 64 3 1 1590191782949565782018039959996,
    decodeIntegerRow 64 3 1 1349451871761205414032433466916,
    decodeIntegerRow 64 3 1 2866113312274788199418768410564,
    decodeIntegerRow 64 3 1 1844538732608968067656259600356,
    decodeIntegerRow 64 3 1 1757663025520989412620858625276,
    decodeIntegerRow 64 3 1 2856693054880299431040497876836,
    decodeIntegerRow 64 3 1 2112492720714795652672346698884,
    decodeIntegerRow 64 3 1 1590191782957704246687477244156,
    decodeIntegerRow 64 3 1 1760803111321855278714626601244,
    decodeIntegerRow 64 3 1 2866113312273891337647364119676,
    decodeIntegerRow 64 3 1 1349451871760894106640706358116,
    decodeIntegerRow 64 3 1 1757663025523791179146402604476,
    decodeIntegerRow 64 3 1 1844538732600896311713620982364,
    decodeIntegerRow 64 3 1 2112492720715084723821807585596,
    decodeIntegerRow 64 3 1 2856693054879395157188338178596,
    decodeIntegerRow 64 3 1 1321191099577426520405517278648,
    decodeIntegerRow 64 3 1 576990765413116930938441691528,
    decodeIntegerRow 64 3 1 1757663025523791315842298265672,
    decodeIntegerRow 64 3 1 1844538732600896359161783109768,
    decodeIntegerRow 64 3 1 567570508018620719977025810488,
    decodeIntegerRow 64 3 1 2084231948531619608280203642888,
    decodeIntegerRow 64 3 1 1590191782957704202628469554632,
    decodeIntegerRow 64 3 1 1760803111321855416540240408328,
    decodeIntegerRow 64 3 1 1716835201230356632769614314232,
    decodeIntegerRow 64 3 1 1716861186927247497390648515128,
    decodeIntegerRow 64 3 1 1716897907210540105485388002568,
    decodeIntegerRow 64 3 1 1716666745979414471356498564408,
    decodeIntegerRow 64 3 1 1716822473613540855258897494392,
    decodeIntegerRow 64 3 1 1716835679172501159215685314488,
    decodeIntegerRow 64 3 1 1716668181799705185982114524808,
    decodeIntegerRow 64 3 1 1716781605766992220810495210168,
    decodeIntegerRow 64 3 1 1717015638492807298615298070436,
    decodeIntegerRow 64 3 1 1716902214525520263658289504956,
    decodeIntegerRow 64 3 1 1716822473613540855266120131876,
    decodeIntegerRow 64 3 1 1716835679172501159236548743364,
    decodeIntegerRow 64 3 1 1716785913081972379359975805156,
    decodeIntegerRow 64 3 1 1717017074313098013236264906236,
    decodeIntegerRow 64 3 1 1716835201230356632790649693796,
    decodeIntegerRow 64 3 1 1716861186927247497383943146884]

def cols_left0 (r : LeftIndex 3 5 5) : List ℤ := cols_left0Data.getD (leftPosition 3 5 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 5 5) : (tripleIndices 4 2 8).map (fun j => (left0Middle3 5 5) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_0_4
  · exact cols_left0_eq_2_0_5
  · exact cols_left0_eq_2_0_6
  · exact cols_left0_eq_2_0_7
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_0_4
  · exact cols_left0_eq_3_0_5
  · exact cols_left0_eq_3_0_6
  · exact cols_left0_eq_3_0_7
  · exact cols_left0_eq_4_0_0
  · exact cols_left0_eq_4_0_1
  · exact cols_left0_eq_4_0_2
  · exact cols_left0_eq_4_0_3
  · exact cols_left0_eq_4_0_4
  · exact cols_left0_eq_4_0_5
  · exact cols_left0_eq_4_0_6
  · exact cols_left0_eq_4_0_7
  · exact cols_left0_eq_5_0_0
  · exact cols_left0_eq_5_0_1
  · exact cols_left0_eq_5_0_2
  · exact cols_left0_eq_5_0_3
  · exact cols_left0_eq_5_0_4
  · exact cols_left0_eq_5_0_5
  · exact cols_left0_eq_5_0_6
  · exact cols_left0_eq_5_0_7
  · exact cols_left0_eq_6_0_0
  · exact cols_left0_eq_6_0_1
  · exact cols_left0_eq_6_0_2
  · exact cols_left0_eq_6_0_3
  · exact cols_left0_eq_6_0_4
  · exact cols_left0_eq_6_0_5
  · exact cols_left0_eq_6_0_6
  · exact cols_left0_eq_6_0_7
  · exact cols_left0_eq_7_0_0
  · exact cols_left0_eq_7_0_1
  · exact cols_left0_eq_7_0_2
  · exact cols_left0_eq_7_0_3
  · exact cols_left0_eq_7_0_4
  · exact cols_left0_eq_7_0_5
  · exact cols_left0_eq_7_0_6
  · exact cols_left0_eq_7_0_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 64 17 8 2803502666730800654816945661715837717451294086603145836892429107810428624253440,
    decodeIntegerRow 64 17 8 2803502769615214362920768818612963930063663754294486202948718877777540052767232,
    decodeIntegerRow 64 17 8 2803504518650165599818634445928750323340846471844015565562100703054277246914560,
    decodeIntegerRow 64 17 8 2803534252244341439874102131813045136829625472709208860467124466194769841369600,
    decodeIntegerRow 64 17 8 2804039722967078933488062438244849016741084854812123226762248488466361496547840,
    decodeIntegerRow 64 17 8 2812632732084393489494407917622447801796279246391561678637514684280346120376832,
    decodeIntegerRow 64 17 8 2958713880246654964026802029281926904820295890840811094052006540891316839976960,
    decodeIntegerRow 64 17 8 5442093399406987441523130027625024211592729957437527642798311492116848666882560,
    decodeIntegerRow 64 17 8 2803471068356717813293602797103081417291891195498690744367352914000046365432320,
    decodeIntegerRow 64 17 8 2803504518650165599927081881653222854942879299854619908363314649175711120213504,
    decodeIntegerRow 64 17 8 2803502550985844890240534775795378914560753660434455643927454620319349942825920,
    decodeIntegerRow 64 17 8 2803502666730800654816570411074106962900778330290266048908038805307499419824640,
    decodeIntegerRow 64 17 8 164911921194071811638195716745204700488163057753952869953341666203232440568320,
    decodeIntegerRow 64 17 8 2958713880246654964026803327727057165146653798761480777140938371855437311624704,
    decodeIntegerRow 64 17 8 2794372588516665763666917750104367983242329962779241663638703363004713596662720,
    decodeIntegerRow 64 17 8 2804039722967078933488062433751959303606018147710864860921422275610630205698560,
    decodeIntegerRow 64 17 8 2794372588561165940532351901056314578231919331365323735592208715649165342568960,
    decodeIntegerRow 64 17 8 2804039723723581940200442999935051418429037413668847698396003818435213114945600,
    decodeIntegerRow 64 17 8 5442093399406833461672384580736831619377297399209309429777693539811059609224704,
    decodeIntegerRow 64 17 8 2648291440351786631671851041609902640503895573377956600699235271246701916736000,
    decodeIntegerRow 64 17 8 2803502550985845423042808563711687432727381566112358296098478059388574257082880,
    decodeIntegerRow 64 17 8 2803502666730809712455224805651351771733452726814611071012741429632966848884800,
    decodeIntegerRow 64 17 8 2803534252244341438030495724496904512527765393708272279667757139978310482773504,
    decodeIntegerRow 64 17 8 2803500801950893622001382297688880319929004320427711054891264473729333558336000,
    decodeIntegerRow 64 17 8 2648291440351786631671849743164772380106221739779795198206057415327973972226560,
    decodeIntegerRow 64 17 8 164911921194225791488941163633397291415713899335702973732575520799345370664960,
    decodeIntegerRow 64 17 8 2804039723723581940200442995442161683395508855228480826959599642776917550207488,
    decodeIntegerRow 64 17 8 2812632732039893312628973767199076468463666069896800195433847525324831540195840,
    decodeIntegerRow 64 17 8 2803500801950893621892934861964401459675953754136354136828809854659630775513600,
    decodeIntegerRow 64 17 8 2803471068356717815137209204419114454526448819631095598276731286875624623247360,
    decodeIntegerRow 64 17 8 2803502666730809712454849555007792037038795184185269539305364843775849414169088,
    decodeIntegerRow 64 17 8 2803502769615213830118539177831084264205575454436714224265763273921033394762240,
    decodeIntegerRow 64 17 8 2803502769615213830118539177831084264205575454442145399181638251906156403375616,
    decodeIntegerRow 64 17 8 2803502666730809712454849555007792037038795184277599578127948623750003772787200,
    decodeIntegerRow 64 17 8 2803534252244341438024116463571989147477443581703267585716611684853514679841280,
    decodeIntegerRow 64 17 8 2803504518650165631268390806026702142327938672311779545718843186288758315626560,
    decodeIntegerRow 64 17 8 2812632732039893312628973767199076468463666523513960344214647976627605858172416,
    decodeIntegerRow 64 17 8 2804039723723581940200442995442161683395516566725653327980265443741353092160000,
    decodeIntegerRow 64 17 8 5442093399406833461672384504357706310588309595880661484893245902145620680143360,
    decodeIntegerRow 64 17 8 2958713880249272621489475924826331221899899282662379010900886946961855581597760,
    decodeIntegerRow 64 17 8 2803504518650165631159943370302223282074888052653660318256806208645890915717632,
    decodeIntegerRow 64 17 8 2803471068356717815130829943494199089476127007626090904325677429288477131747840,
    decodeIntegerRow 64 17 8 2803502666730809712455224805651351771733452726722281032190157631014887768076800,
    decodeIntegerRow 64 17 8 2803502550985845423042808563711687432727381566117789471014352720427200985108480,
    decodeIntegerRow 64 17 8 2958713880249272621489474626381200961497768203709374245889538701761143953183232,
    decodeIntegerRow 64 17 8 164911921194225791488941087254271982626726096007055028848127884230607123427840,
    decodeIntegerRow 64 17 8 2804039723723581940200442999935051418429029702171675197375338017470554348597760,
    decodeIntegerRow 64 17 8 2794372588561165940532351901056314578231919784982483884373009166948144848506880,
    decodeIntegerRow 64 17 8 2804039722967078933488062433751959303606010436213729945912805151396881833594880,
    decodeIntegerRow 64 17 8 2794372588516665763666917750104367983242330416397040774624331319069169804751360,
    decodeIntegerRow 64 17 8 2648291440354404289134522340264046436859467223680693301910600977712071525347840,
    decodeIntegerRow 64 17 8 5442093399406987441523129951245898901515598246559185516174670029805512941081088,
    decodeIntegerRow 64 17 8 2803502666730800654816570411074106962900778330197936010535473727799499130081280,
    decodeIntegerRow 64 17 8 2803502550985844890240534775795378914560753660439886826493647540229316118950400,
    decodeIntegerRow 64 17 8 2803500801950893653234243786337880747061013126593513774182781233632656585699840,
    decodeIntegerRow 64 17 8 2803534252244341439867722870888022184712001202696451127308550761123615176626688,
    decodeIntegerRow 64 17 8 164911921194071811638195640366079390411031346875610743329700202795196032922560,
    decodeIntegerRow 64 17 8 2648291440354404289134523638709176697181367886246519882592172444838849746792960,
    decodeIntegerRow 64 17 8 2812632732084393489494407917622447801796279700009360789623142640341007516408320,
    decodeIntegerRow 64 17 8 2804039722967078933488062438244849016741092566309258141770865612680333092732416,
    decodeIntegerRow 64 17 8 2803471068356717813287223536178058465174266925485933011208687611391243383911360,
    decodeIntegerRow 64 17 8 2803500801950893653342691222062353278663045901237355807587527137460968521495040,
    decodeIntegerRow 64 17 8 2803502769615214362920768818612963930063663754299917385514911480741008403499520,
    decodeIntegerRow 64 17 8 2803502666730800654816945661715837717451294086695475875264994203962327374511616]

def cols_right2 (r : LeftIndex 3 5 5) : List ℤ := cols_right2Data.getD (leftPosition 3 5 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 5 5) : (tripleIndices 8 1 8).map (fun j => (right2Middle3 5 5) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_0_4
  · exact cols_right2_eq_2_0_5
  · exact cols_right2_eq_2_0_6
  · exact cols_right2_eq_2_0_7
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_0_4
  · exact cols_right2_eq_3_0_5
  · exact cols_right2_eq_3_0_6
  · exact cols_right2_eq_3_0_7
  · exact cols_right2_eq_4_0_0
  · exact cols_right2_eq_4_0_1
  · exact cols_right2_eq_4_0_2
  · exact cols_right2_eq_4_0_3
  · exact cols_right2_eq_4_0_4
  · exact cols_right2_eq_4_0_5
  · exact cols_right2_eq_4_0_6
  · exact cols_right2_eq_4_0_7
  · exact cols_right2_eq_5_0_0
  · exact cols_right2_eq_5_0_1
  · exact cols_right2_eq_5_0_2
  · exact cols_right2_eq_5_0_3
  · exact cols_right2_eq_5_0_4
  · exact cols_right2_eq_5_0_5
  · exact cols_right2_eq_5_0_6
  · exact cols_right2_eq_5_0_7
  · exact cols_right2_eq_6_0_0
  · exact cols_right2_eq_6_0_1
  · exact cols_right2_eq_6_0_2
  · exact cols_right2_eq_6_0_3
  · exact cols_right2_eq_6_0_4
  · exact cols_right2_eq_6_0_5
  · exact cols_right2_eq_6_0_6
  · exact cols_right2_eq_6_0_7
  · exact cols_right2_eq_7_0_0
  · exact cols_right2_eq_7_0_1
  · exact cols_right2_eq_7_0_2
  · exact cols_right2_eq_7_0_3
  · exact cols_right2_eq_7_0_4
  · exact cols_right2_eq_7_0_5
  · exact cols_right2_eq_7_0_6
  · exact cols_right2_eq_7_0_7

theorem product0_eq : HexagonAtoms355.outerABC * HexagonAtoms355.assocABC = HexagonAtoms355.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms355.assocBAC * HexagonAtoms355.innerABC = HexagonAtoms355.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms355.innerRightABC * HexagonAtoms355.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms355.inverseACB * right0Middle3 5 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms355.innerABC * right1Middle3 5 5 = right1Middle3 5 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms355.assocBCA * left0Middle3 5 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms355.innerRightBAC * left1Middle3 5 5 = left1Middle3 5 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms355.assocBAC * right2Middle3 5 5 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn355

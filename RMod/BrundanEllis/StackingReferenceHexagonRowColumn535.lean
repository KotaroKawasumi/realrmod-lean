import RMod.BrundanEllis.StackingReferenceHexagonAtoms535
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn535
open Superfusion

theorem assocBCA_alias : HexagonAtoms535.assocBCA = HexagonAtoms535.assocBAC :=
  HexagonAtoms535.assocBCA_eq.symm.trans HexagonAtoms535.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 1713700867223698638605163923152,
    decodeIntegerRow 64 3 1 1731497717458175286833227848640,
    decodeIntegerRow 64 3 1 1730446714828410917824978896640,
    decodeIntegerRow 64 3 1 1723121602998022866691694739496,
    decodeIntegerRow 64 3 1 1462417433419112575252261369552,
    decodeIntegerRow 64 3 1 2903962302411747026267174941760,
    decodeIntegerRow 64 3 1 2818831089400733088192909665280,
    decodeIntegerRow 64 3 1 2225497031139363928751486662696,
    decodeIntegerRow 64 3 1 1971111332725309295449231422400,
    decodeIntegerRow 64 3 1 2903626381300677761540270464112,
    decodeIntegerRow 64 3 1 2819192961194616695447672042664,
    decodeIntegerRow 64 3 1 1208109232535976183421138693120,
    decodeIntegerRow 64 3 1 1719981038820071986579277423680,
    decodeIntegerRow 64 3 1 1731493570283964555365190528112,
    decodeIntegerRow 64 3 1 1730451182381421826737774570664,
    decodeIntegerRow 64 3 1 1710561259805388724562346146560,
    decodeIntegerRow 64 3 1 2903626381300677776224195403520,
    decodeIntegerRow 64 3 1 1971111332725309288671439264984,
    decodeIntegerRow 64 3 1 1208109232535976180030951212752,
    decodeIntegerRow 64 3 1 2819192961194616679629379937600,
    decodeIntegerRow 64 3 1 1731493570283965744763110620160,
    decodeIntegerRow 64 3 1 1719981038820071437578112672984,
    decodeIntegerRow 64 3 1 1710561259805388449957160236752,
    decodeIntegerRow 64 3 1 1730451182381420545456114060480,
    decodeIntegerRow 64 3 1 1731497717458176476621723063464,
    decodeIntegerRow 64 3 1 1713700867223699187690037008640,
    decodeIntegerRow 64 3 1 1723121602998023141129527752640,
    decodeIntegerRow 64 3 1 1730446714828409636905884442768,
    decodeIntegerRow 64 3 1 2903962302411747040955921796264,
    decodeIntegerRow 64 3 1 1462417433419112582031086963200,
    decodeIntegerRow 64 3 1 2225497031139363932139608057920,
    decodeIntegerRow 64 3 1 2818831089400733072379093684368,
    decodeIntegerRow 64 3 1 2225497054775666716781720320048,
    decodeIntegerRow 64 3 1 2818831140617225301317325358400,
    decodeIntegerRow 64 3 1 529721462741399857143888719360,
    decodeIntegerRow 64 3 1 1971266398687048464361794377944,
    decodeIntegerRow 64 3 1 1723121603289829073951333632048,
    decodeIntegerRow 64 3 1 1730446715460713290826485132480,
    decodeIntegerRow 64 3 1 1702186102153604289167225893120,
    decodeIntegerRow 64 3 1 1719982953214661359076823113944,
    decodeIntegerRow 64 3 1 1723122560195362025320396498240,
    decodeIntegerRow 64 3 1 1703232638543185492660429356688,
    decodeIntegerRow 64 3 1 1731493569603038932608154580056,
    decodeIntegerRow 64 3 1 1719981038674135528586074589440,
    decodeIntegerRow 64 3 1 2225574564123835784453604717760,
    decodeIntegerRow 64 3 1 614490910297577403181328838288,
    decodeIntegerRow 64 3 1 2903626326145702318222597127256,
    decodeIntegerRow 64 3 1 1971111320904456197998768806400,
    decodeIntegerRow 64 3 1 1703232638543186773942149379840,
    decodeIntegerRow 64 3 1 1723122560195362299925595158744,
    decodeIntegerRow 64 3 1 1719981038674134979584884327632,
    decodeIntegerRow 64 3 1 1731493569603040122006129951040,
    decodeIntegerRow 64 3 1 614490910297577418999621678080,
    decodeIntegerRow 64 3 1 2225574564123835787843792355544,
    decodeIntegerRow 64 3 1 1971111320904456191220976334032,
    decodeIntegerRow 64 3 1 2903626326145702332906522749120,
    decodeIntegerRow 64 3 1 2818831140617225285503510112424,
    decodeIntegerRow 64 3 1 2225497054775666720169841557760,
    decodeIntegerRow 64 3 1 1971266398687048457582969099200,
    decodeIntegerRow 64 3 1 529721462741399842455142547088,
    decodeIntegerRow 64 3 1 1730446715460712009907450208424,
    decodeIntegerRow 64 3 1 1723121603289829348389153886720,
    decodeIntegerRow 64 3 1 1719982953214660809991975535680,
    decodeIntegerRow 64 3 1 1702186102153603099378785939088]

def rows_inverseACB (r : LeftIndex 5 5 3) : List ℤ := rows_inverseACBData.getD (leftPosition 5 5 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 5 3) : (tripleIndices 8 1 8).map ((HexagonAtoms535.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_1_4
  · exact rows_inverseACB_eq_0_1_5
  · exact rows_inverseACB_eq_0_1_6
  · exact rows_inverseACB_eq_0_1_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_1_1_4
  · exact rows_inverseACB_eq_1_1_5
  · exact rows_inverseACB_eq_1_1_6
  · exact rows_inverseACB_eq_1_1_7
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_0_4
  · exact rows_inverseACB_eq_2_0_5
  · exact rows_inverseACB_eq_2_0_6
  · exact rows_inverseACB_eq_2_0_7
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_2_1_4
  · exact rows_inverseACB_eq_2_1_5
  · exact rows_inverseACB_eq_2_1_6
  · exact rows_inverseACB_eq_2_1_7
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_0_4
  · exact rows_inverseACB_eq_3_0_5
  · exact rows_inverseACB_eq_3_0_6
  · exact rows_inverseACB_eq_3_0_7
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3
  · exact rows_inverseACB_eq_3_1_4
  · exact rows_inverseACB_eq_3_1_5
  · exact rows_inverseACB_eq_3_1_6
  · exact rows_inverseACB_eq_3_1_7

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716844143606710847805623514792,
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

def rows_innerACB (r : LeftIndex 5 5 3) : List ℤ := rows_innerACBData.getD (leftPosition 5 5 3 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 5 5 3) : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_0_4
  · exact rows_innerACB_eq_0_0_5
  · exact rows_innerACB_eq_0_0_6
  · exact rows_innerACB_eq_0_0_7
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_1_2
  · exact rows_innerACB_eq_0_1_3
  · exact rows_innerACB_eq_0_1_4
  · exact rows_innerACB_eq_0_1_5
  · exact rows_innerACB_eq_0_1_6
  · exact rows_innerACB_eq_0_1_7
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_1_0_4
  · exact rows_innerACB_eq_1_0_5
  · exact rows_innerACB_eq_1_0_6
  · exact rows_innerACB_eq_1_0_7
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_1_1_2
  · exact rows_innerACB_eq_1_1_3
  · exact rows_innerACB_eq_1_1_4
  · exact rows_innerACB_eq_1_1_5
  · exact rows_innerACB_eq_1_1_6
  · exact rows_innerACB_eq_1_1_7
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_0_2
  · exact rows_innerACB_eq_2_0_3
  · exact rows_innerACB_eq_2_0_4
  · exact rows_innerACB_eq_2_0_5
  · exact rows_innerACB_eq_2_0_6
  · exact rows_innerACB_eq_2_0_7
  · exact rows_innerACB_eq_2_1_0
  · exact rows_innerACB_eq_2_1_1
  · exact rows_innerACB_eq_2_1_2
  · exact rows_innerACB_eq_2_1_3
  · exact rows_innerACB_eq_2_1_4
  · exact rows_innerACB_eq_2_1_5
  · exact rows_innerACB_eq_2_1_6
  · exact rows_innerACB_eq_2_1_7
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_0_2
  · exact rows_innerACB_eq_3_0_3
  · exact rows_innerACB_eq_3_0_4
  · exact rows_innerACB_eq_3_0_5
  · exact rows_innerACB_eq_3_0_6
  · exact rows_innerACB_eq_3_0_7
  · exact rows_innerACB_eq_3_1_0
  · exact rows_innerACB_eq_3_1_1
  · exact rows_innerACB_eq_3_1_2
  · exact rows_innerACB_eq_3_1_3
  · exact rows_innerACB_eq_3_1_4
  · exact rows_innerACB_eq_3_1_5
  · exact rows_innerACB_eq_3_1_6
  · exact rows_innerACB_eq_3_1_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716841913114126877389940976168,
    decodeIntegerRow 64 3 1 1716841909201994016217851491716,
    decodeIntegerRow 64 3 1 1716841883666716405245932202724,
    decodeIntegerRow 64 3 1 1716841919336999216268494532712,
    decodeIntegerRow 64 3 1 1716841911171569159718199027048,
    decodeIntegerRow 64 3 1 1716841913087111078383015421956,
    decodeIntegerRow 64 3 1 1716841918681385803536842621284,
    decodeIntegerRow 64 3 1 1716841936844334005667426859432,
    decodeIntegerRow 64 3 1 1760978278429551339486514493288,
    decodeIntegerRow 64 3 1 1590247778996674956825164546044,
    decodeIntegerRow 64 3 1 1349432568281824542057653033116,
    decodeIntegerRow 64 3 1 2866106611893121524758968924072,
    decodeIntegerRow 64 3 1 1844599036035898329026463648808,
    decodeIntegerRow 64 3 1 1757489294209368935905100649084,
    decodeIntegerRow 64 3 1 2856699276662407488435720392476,
    decodeIntegerRow 64 3 1 2112473257702830051569933147752,
    decodeIntegerRow 64 3 1 2084251252010687942600197075324,
    decodeIntegerRow 64 3 1 2866106611893121524758965720792,
    decodeIntegerRow 64 3 1 1672705541862961145171324676248,
    decodeIntegerRow 64 3 1 1590247778996674956825193125916,
    decodeIntegerRow 64 3 1 576984543630104996222125522684,
    decodeIntegerRow 64 3 1 2112473257702830051569932041112,
    decodeIntegerRow 64 3 1 1589084784256614155631356624728,
    decodeIntegerRow 64 3 1 1757489294209368935905091436956,
    decodeIntegerRow 64 3 1 1716841936625796216047374947076,
    decodeIntegerRow 64 3 1 1716841919336999168631271205272,
    decodeIntegerRow 64 3 1 1716841907178384366844615737688,
    decodeIntegerRow 64 3 1 1716841909201994412769755324004,
    decodeIntegerRow 64 3 1 1716841901611126637249510293636,
    decodeIntegerRow 64 3 1 1716841936844333867776726414552,
    decodeIntegerRow 64 3 1 1716841909120942897927197702808,
    decodeIntegerRow 64 3 1 1716841913087109848113239222244,
    decodeIntegerRow 64 3 1 1716841909193922656806282091644,
    decodeIntegerRow 64 3 1 1716841913111326351294921217128,
    decodeIntegerRow 64 3 1 1716841919337903442672492102312,
    decodeIntegerRow 64 3 1 1716841883667005339699497433116,
    decodeIntegerRow 64 3 1 1716841913089711488465102495484,
    decodeIntegerRow 64 3 1 1716841911163431122082220900648,
    decodeIntegerRow 64 3 1 1716841936844645175233540165992,
    decodeIntegerRow 64 3 1 1716841918680488985824446021276,
    decodeIntegerRow 64 3 1 1843548033381917456836504122364,
    decodeIntegerRow 64 3 1 1673055876080954769234644557272,
    decodeIntegerRow 64 3 1 567563807636954045317226322328,
    decodeIntegerRow 64 3 1 2084212645052238736305423212956,
    decodeIntegerRow 64 3 1 1675847063457100692099792851324,
    decodeIntegerRow 64 3 1 1589205391118546386866270026392,
    decodeIntegerRow 64 3 1 1321171636565460919303103723608,
    decodeIntegerRow 64 3 1 576996987195224988333664205596,
    decodeIntegerRow 64 3 1 567563807636954045317223122072,
    decodeIntegerRow 64 3 1 1349471175240273748352426904196,
    decodeIntegerRow 64 3 1 1843548033381917456836532701924,
    decodeIntegerRow 64 3 1 1760627944211557715423194611288,
    decodeIntegerRow 64 3 1 1321171636565460919303102625752,
    decodeIntegerRow 64 3 1 2856686833097287496324181706756,
    decodeIntegerRow 64 3 1 1675847063457100692099783640164,
    decodeIntegerRow 64 3 1 1844478429173966097791550246808,
    decodeIntegerRow 64 3 1 1716841919337903489931593032488,
    decodeIntegerRow 64 3 1 1716841936625507008202018403076,
    decodeIntegerRow 64 3 1 1716841909193922260296047485284,
    decodeIntegerRow 64 3 1 1716841907181187373800683945832,
    decodeIntegerRow 64 3 1 1716841936844645312994067326568,
    decodeIntegerRow 64 3 1 1716841901612023543079922275716,
    decodeIntegerRow 64 3 1 1716841913089712718721448118244,
    decodeIntegerRow 64 3 1 1716841909129081789630094147752]

def rows_assocBAC (r : RightIndex 3 5 5) : List ℤ := rows_assocBACData.getD (rightPosition 3 5 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 3 5 5) : (tripleIndices 8 1 8).map ((HexagonAtoms535.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_0_1_4
  · exact rows_assocBAC_eq_0_1_5
  · exact rows_assocBAC_eq_0_1_6
  · exact rows_assocBAC_eq_0_1_7
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_0_4
  · exact rows_assocBAC_eq_1_0_5
  · exact rows_assocBAC_eq_1_0_6
  · exact rows_assocBAC_eq_1_0_7
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3
  · exact rows_assocBAC_eq_1_1_4
  · exact rows_assocBAC_eq_1_1_5
  · exact rows_assocBAC_eq_1_1_6
  · exact rows_assocBAC_eq_1_1_7
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_2_0_4
  · exact rows_assocBAC_eq_2_0_5
  · exact rows_assocBAC_eq_2_0_6
  · exact rows_assocBAC_eq_2_0_7
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_2_1_2
  · exact rows_assocBAC_eq_2_1_3
  · exact rows_assocBAC_eq_2_1_4
  · exact rows_assocBAC_eq_2_1_5
  · exact rows_assocBAC_eq_2_1_6
  · exact rows_assocBAC_eq_2_1_7
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3
  · exact rows_assocBAC_eq_3_0_4
  · exact rows_assocBAC_eq_3_0_5
  · exact rows_assocBAC_eq_3_0_6
  · exact rows_assocBAC_eq_3_0_7
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1
  · exact rows_assocBAC_eq_3_1_2
  · exact rows_assocBAC_eq_3_1_3
  · exact rows_assocBAC_eq_3_1_4
  · exact rows_assocBAC_eq_3_1_5
  · exact rows_assocBAC_eq_3_1_6
  · exact rows_assocBAC_eq_3_1_7

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716844143606710847805623514792,
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

def rows_innerRightBAC (r : RightIndex 3 5 5) : List ℤ := rows_innerRightBACData.getD (rightPosition 3 5 5 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 3 5 5) : (tripleIndices 4 2 8).map ((HexagonAtoms535.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_0_4
  · exact rows_innerRightBAC_eq_0_0_5
  · exact rows_innerRightBAC_eq_0_0_6
  · exact rows_innerRightBAC_eq_0_0_7
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_0_1_4
  · exact rows_innerRightBAC_eq_0_1_5
  · exact rows_innerRightBAC_eq_0_1_6
  · exact rows_innerRightBAC_eq_0_1_7
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_1_0_4
  · exact rows_innerRightBAC_eq_1_0_5
  · exact rows_innerRightBAC_eq_1_0_6
  · exact rows_innerRightBAC_eq_1_0_7
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_1_1_2
  · exact rows_innerRightBAC_eq_1_1_3
  · exact rows_innerRightBAC_eq_1_1_4
  · exact rows_innerRightBAC_eq_1_1_5
  · exact rows_innerRightBAC_eq_1_1_6
  · exact rows_innerRightBAC_eq_1_1_7
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_0_2
  · exact rows_innerRightBAC_eq_2_0_3
  · exact rows_innerRightBAC_eq_2_0_4
  · exact rows_innerRightBAC_eq_2_0_5
  · exact rows_innerRightBAC_eq_2_0_6
  · exact rows_innerRightBAC_eq_2_0_7
  · exact rows_innerRightBAC_eq_2_1_0
  · exact rows_innerRightBAC_eq_2_1_1
  · exact rows_innerRightBAC_eq_2_1_2
  · exact rows_innerRightBAC_eq_2_1_3
  · exact rows_innerRightBAC_eq_2_1_4
  · exact rows_innerRightBAC_eq_2_1_5
  · exact rows_innerRightBAC_eq_2_1_6
  · exact rows_innerRightBAC_eq_2_1_7
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_0_2
  · exact rows_innerRightBAC_eq_3_0_3
  · exact rows_innerRightBAC_eq_3_0_4
  · exact rows_innerRightBAC_eq_3_0_5
  · exact rows_innerRightBAC_eq_3_0_6
  · exact rows_innerRightBAC_eq_3_0_7
  · exact rows_innerRightBAC_eq_3_1_0
  · exact rows_innerRightBAC_eq_3_1_1
  · exact rows_innerRightBAC_eq_3_1_2
  · exact rows_innerRightBAC_eq_3_1_3
  · exact rows_innerRightBAC_eq_3_1_4
  · exact rows_innerRightBAC_eq_3_1_5
  · exact rows_innerRightBAC_eq_3_1_6
  · exact rows_innerRightBAC_eq_3_1_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 64 3 1 1702369074897160498975970756200,
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

def rows_assocCAB (r : RightIndex 5 5 3) : List ℤ := rows_assocCABData.getD (rightPosition 5 5 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 5 3) : (tripleIndices 4 2 8).map ((HexagonAtoms535.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_0_4
  · exact rows_assocCAB_eq_2_0_5
  · exact rows_assocCAB_eq_2_0_6
  · exact rows_assocCAB_eq_2_0_7
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_0_4
  · exact rows_assocCAB_eq_3_0_5
  · exact rows_assocCAB_eq_3_0_6
  · exact rows_assocCAB_eq_3_0_7
  · exact rows_assocCAB_eq_4_0_0
  · exact rows_assocCAB_eq_4_0_1
  · exact rows_assocCAB_eq_4_0_2
  · exact rows_assocCAB_eq_4_0_3
  · exact rows_assocCAB_eq_4_0_4
  · exact rows_assocCAB_eq_4_0_5
  · exact rows_assocCAB_eq_4_0_6
  · exact rows_assocCAB_eq_4_0_7
  · exact rows_assocCAB_eq_5_0_0
  · exact rows_assocCAB_eq_5_0_1
  · exact rows_assocCAB_eq_5_0_2
  · exact rows_assocCAB_eq_5_0_3
  · exact rows_assocCAB_eq_5_0_4
  · exact rows_assocCAB_eq_5_0_5
  · exact rows_assocCAB_eq_5_0_6
  · exact rows_assocCAB_eq_5_0_7
  · exact rows_assocCAB_eq_6_0_0
  · exact rows_assocCAB_eq_6_0_1
  · exact rows_assocCAB_eq_6_0_2
  · exact rows_assocCAB_eq_6_0_3
  · exact rows_assocCAB_eq_6_0_4
  · exact rows_assocCAB_eq_6_0_5
  · exact rows_assocCAB_eq_6_0_6
  · exact rows_assocCAB_eq_6_0_7
  · exact rows_assocCAB_eq_7_0_0
  · exact rows_assocCAB_eq_7_0_1
  · exact rows_assocCAB_eq_7_0_2
  · exact rows_assocCAB_eq_7_0_3
  · exact rows_assocCAB_eq_7_0_4
  · exact rows_assocCAB_eq_7_0_5
  · exact rows_assocCAB_eq_7_0_6
  · exact rows_assocCAB_eq_7_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230103363218355520,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1712132047337003500059288475240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1589610285595812311701442397472,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1718412671932149473413377451600,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 1335340868586722358675913658176,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1843957235222794201680808781440,
    decodeIntegerRow 64 3 1 1674276302623541176414930056880,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 2098381717540611551239628320000,
    decodeIntegerRow 64 3 1 1718411234166632285338649733760,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1702711594958472746408308461376,
    decodeIntegerRow 64 3 1 1721552251553867271814211200000,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1674276302696520660856187811808,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1730972207609064061672847054440,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1715272584164443505258011655104,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1702711612683448417901557356160,
    decodeIntegerRow 64 3 1 1712131515560716305658027749040,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 572287097906721198306548019840,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1730972225334039733166038553920,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1335302102751902168771986787872,
    decodeIntegerRow 64 3 1 2861396722604617734731849193920,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 1843957235222794156115510268520,
    decodeIntegerRow 64 3 1 1674625201118505546788168700520,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 2098342951705788890642116313920,
    decodeIntegerRow 64 3 1 572274175742954274863347101408,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 1721551826132837513242963625920,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 2861409644768407717981844713040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 1589610285595812265759571169280,
    decodeIntegerRow 64 3 1 1674625201045592771199233850304,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1715271150338009925917735246080,
    decodeIntegerRow 64 3 1 1716320713254230101669414919104]

def cols_right0 (r : LeftIndex 5 3 5) : List ℤ := cols_right0Data.getD (leftPosition 5 3 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 3 5) : (tripleIndices 8 1 8).map (fun j => (right0Middle5 3 5) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 64 9 4 5895092275325170344796952452359238800901939875462412241142976,
    decodeIntegerRow 64 9 4 5895092167141244174112770622873925083982565583537000845523136,
    decodeIntegerRow 64 9 4 5895092289036044531164028210307287600567270131416226588079296,
    decodeIntegerRow 64 9 4 5895092290372160714769052015466591796209031274365034962612544,
    decodeIntegerRow 64 9 4 5895092167137121153948097002860948162330980085850773336300736,
    decodeIntegerRow 64 9 4 5895092302376305645220573357500821756954390194801100249309376,
    decodeIntegerRow 64 9 4 5895092287366473358139569812024298509790458572553714342513856,
    decodeIntegerRow 64 9 4 5895092289036502645377811091301563213017570172980288670173504,
    decodeIntegerRow 64 9 4 5895092290372109813381303049388220155887850147811611012797520,
    decodeIntegerRow 64 9 4 5895092288702080526143061770110955452659766054205439991717040,
    decodeIntegerRow 64 9 4 5895092167137121153948097002860948162323091111817306725573040,
    decodeIntegerRow 64 9 4 5895092302376305645220573357500821757025292498980902611083440,
    decodeIntegerRow 64 9 4 5895092288702538640356844651105231065110066125417880883991120,
    decodeIntegerRow 64 9 4 5895092287366422456751820845945926869469082922986916802558640,
    decodeIntegerRow 64 9 4 5895092275325170344796952452359238800831035169768444438635440,
    decodeIntegerRow 64 9 4 5895092167141244174112770622873925083974698223131010803941040,
    decodeIntegerRow 64 9 4 11135085582170394504895125763860233851844419764721621371549520,
    decodeIntegerRow 64 9 4 6478122297285973711805601352069805068823608253170499998947920,
    decodeIntegerRow 64 9 4 5830398822501392080822161155751594915202698588172044572440240,
    decodeIntegerRow 64 9 4 5887914107808453693188807005128090148525184821332168483376720,
    decodeIntegerRow 64 9 4 5313659622941422287457861002771725199195191774594126281463120,
    decodeIntegerRow 64 9 4 11135263064669151485755413485297407770434517069473728729226320,
    decodeIntegerRow 64 9 4 5887894387530814028648775016051219116390615868380513334974640,
    decodeIntegerRow 64 9 4 5959783564095231127972041489102436750109598903981473238487120,
    decodeIntegerRow 64 9 4 5902290190207769142872097845361261867619886209321668360649024,
    decodeIntegerRow 64 9 4 5830401013643352043548831372310086096606493005643844872797376,
    decodeIntegerRow 64 9 4 5313659622941422287457861002774777310902352227433769088723264,
    decodeIntegerRow 64 9 4 11135263064669151485755413485297068175970419315525136850586944,
    decodeIntegerRow 64 9 4 5959785755237191090698711705660919557951264883684678114156864,
    decodeIntegerRow 64 9 4 5902270469930129478332065856284390836761580345599973370062016,
    decodeIntegerRow 64 9 4 11135085582170394504895125763859895187776114059413984539152704,
    decodeIntegerRow 64 9 4 6478122297285973711805601352066752853739137572704084408771904,
    decodeIntegerRow 64 9 4 5830401013643352043548962760161259297421210947444536752436416,
    decodeIntegerRow 64 9 4 5902290190207769142872112423738922948258972271212915286370496,
    decodeIntegerRow 64 9 4 11135263064669151485755411863279770410912201762911752659723456,
    decodeIntegerRow 64 9 4 5313659622941422287457860822300355716327896033817220956586304,
    decodeIntegerRow 64 9 4 5902270469930129478332080474712539997292532028540372073155776,
    decodeIntegerRow 64 9 4 5959785755237191090698580322259800588235643122000558654214336,
    decodeIntegerRow 64 9 4 6478122297285973711805601532046723978191471968529902272052416,
    decodeIntegerRow 64 9 4 11135085582170394504895124141787658481593216307046074762860864,
    decodeIntegerRow 64 9 4 5312062280452609459715271329362742472402268943279523245923760,
    decodeIntegerRow 64 9 4 655098995568188666625748719624521520016689579922129513944400,
    decodeIntegerRow 64 9 4 5902270469930129478332080474712577677683978453884071405342800,
    decodeIntegerRow 64 9 4 5959785755237191090698580322259804780759891242419677068222800,
    decodeIntegerRow 64 9 4 654921513069431685765460998132408660301912075415496570838960,
    decodeIntegerRow 64 9 4 6476524954797160884063012039115215061057476011298262960715600,
    decodeIntegerRow 64 9 4 5830401013643352043548962760161255116383330630095059758763600,
    decodeIntegerRow 64 9 4 5902290190207769142872112423738960629926681785786574776370000,
    decodeIntegerRow 64 9 4 5895092288702079898591705960940126213258544812157597737859760,
    decodeIntegerRow 64 9 4 5895092290372104157565130807090072019953461526495292900976560,
    decodeIntegerRow 64 9 4 5895092302376305652989405431518843486518626027448744003992400,
    decodeIntegerRow 64 9 4 5895092167137121223770623076927332802067742281951730716451760,
    decodeIntegerRow 64 9 4 5895092287366428112376432845323082688785827703875260063734960,
    decodeIntegerRow 64 9 4 5895092288702538011081446655645470976150050319522728058365360,
    decodeIntegerRow 64 9 4 5895092167141244243937661638210939258492406724628743126309200,
    decodeIntegerRow 64 9 4 5895092275325170337049404849776882884295217623570322929328560,
    decodeIntegerRow 64 9 4 5895092410597338927583211223201579407177937507245633012517184,
    decodeIntegerRow 64 9 4 5895092302413412834471468011635635781312089262970881212755136,
    decodeIntegerRow 64 9 4 5895092287366428112376432845323082688785925098433622825335104,
    decodeIntegerRow 64 9 4 5895092288702538011081446655645470976150925658258775597456704,
    decodeIntegerRow 64 9 4 5895092275362277518531467429893675179230487869047570008879424,
    decodeIntegerRow 64 9 4 5895092410601461947750249784485185863602580336295156455773376,
    decodeIntegerRow 64 9 4 5895092288702079898591705960940126213259420180541912510030144,
    decodeIntegerRow 64 9 4 5895092290372104157565130807090072019953364398772339430995264]

def cols_right1 (r : LeftIndex 5 3 5) : List ℤ := cols_right1Data.getD (leftPosition 5 3 5 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 5 3 5) : (tripleIndices 4 2 8).map (fun j => (right1Middle5 3 5) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_0_4
  · exact cols_right1_eq_0_0_5
  · exact cols_right1_eq_0_0_6
  · exact cols_right1_eq_0_0_7
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_0_4
  · exact cols_right1_eq_1_0_5
  · exact cols_right1_eq_1_0_6
  · exact cols_right1_eq_1_0_7
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_0_2
  · exact cols_right1_eq_2_0_3
  · exact cols_right1_eq_2_0_4
  · exact cols_right1_eq_2_0_5
  · exact cols_right1_eq_2_0_6
  · exact cols_right1_eq_2_0_7
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_0_2
  · exact cols_right1_eq_3_0_3
  · exact cols_right1_eq_3_0_4
  · exact cols_right1_eq_3_0_5
  · exact cols_right1_eq_3_0_6
  · exact cols_right1_eq_3_0_7
  · exact cols_right1_eq_4_0_0
  · exact cols_right1_eq_4_0_1
  · exact cols_right1_eq_4_0_2
  · exact cols_right1_eq_4_0_3
  · exact cols_right1_eq_4_0_4
  · exact cols_right1_eq_4_0_5
  · exact cols_right1_eq_4_0_6
  · exact cols_right1_eq_4_0_7
  · exact cols_right1_eq_5_0_0
  · exact cols_right1_eq_5_0_1
  · exact cols_right1_eq_5_0_2
  · exact cols_right1_eq_5_0_3
  · exact cols_right1_eq_5_0_4
  · exact cols_right1_eq_5_0_5
  · exact cols_right1_eq_5_0_6
  · exact cols_right1_eq_5_0_7
  · exact cols_right1_eq_6_0_0
  · exact cols_right1_eq_6_0_1
  · exact cols_right1_eq_6_0_2
  · exact cols_right1_eq_6_0_3
  · exact cols_right1_eq_6_0_4
  · exact cols_right1_eq_6_0_5
  · exact cols_right1_eq_6_0_6
  · exact cols_right1_eq_6_0_7
  · exact cols_right1_eq_7_0_0
  · exact cols_right1_eq_7_0_1
  · exact cols_right1_eq_7_0_2
  · exact cols_right1_eq_7_0_3
  · exact cols_right1_eq_7_0_4
  · exact cols_right1_eq_7_0_5
  · exact cols_right1_eq_7_0_6
  · exact cols_right1_eq_7_0_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230103363218355520,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1712132047337003500059288475240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1589610285595812311701442397472,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1718412671932149473413377451600,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 1335340868586722358675913658176,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1843957235222794201680808781440,
    decodeIntegerRow 64 3 1 1674276302623541176414930056880,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 2098381717540611551239628320000,
    decodeIntegerRow 64 3 1 1718411234166632285338649733760,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1702711594958472746408308461376,
    decodeIntegerRow 64 3 1 1721552251553867271814211200000,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1674276302696520660856187811808,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1730972207609064061672847054440,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1715272584164443505258011655104,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1702711612683448417901557356160,
    decodeIntegerRow 64 3 1 1712131515560716305658027749040,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 572287097906721198306548019840,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1730972225334039733166038553920,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1335302102751902168771986787872,
    decodeIntegerRow 64 3 1 2861396722604617734731849193920,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 1843957235222794156115510268520,
    decodeIntegerRow 64 3 1 1674625201118505546788168700520,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 2098342951705788890642116313920,
    decodeIntegerRow 64 3 1 572274175742954274863347101408,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 1721551826132837513242963625920,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 2861409644768407717981844713040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 1589610285595812265759571169280,
    decodeIntegerRow 64 3 1 1674625201045592771199233850304,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1715271150338009925917735246080,
    decodeIntegerRow 64 3 1 1716320713254230101669414919104]

def cols_left0 (r : LeftIndex 5 3 5) : List ℤ := cols_left0Data.getD (leftPosition 5 3 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 3 5) : (tripleIndices 8 1 8).map (fun j => (left0Middle5 3 5) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1716781607663588032612437301756,
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

def cols_left1 (r : LeftIndex 5 3 5) : List ℤ := cols_left1Data.getD (leftPosition 5 3 5 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 5 3 5) : (tripleIndices 4 2 8).map (fun j => (left1Middle5 3 5) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_0_4
  · exact cols_left1_eq_0_0_5
  · exact cols_left1_eq_0_0_6
  · exact cols_left1_eq_0_0_7
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_0_4
  · exact cols_left1_eq_1_0_5
  · exact cols_left1_eq_1_0_6
  · exact cols_left1_eq_1_0_7
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_0_2
  · exact cols_left1_eq_2_0_3
  · exact cols_left1_eq_2_0_4
  · exact cols_left1_eq_2_0_5
  · exact cols_left1_eq_2_0_6
  · exact cols_left1_eq_2_0_7
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_0_2
  · exact cols_left1_eq_3_0_3
  · exact cols_left1_eq_3_0_4
  · exact cols_left1_eq_3_0_5
  · exact cols_left1_eq_3_0_6
  · exact cols_left1_eq_3_0_7
  · exact cols_left1_eq_4_0_0
  · exact cols_left1_eq_4_0_1
  · exact cols_left1_eq_4_0_2
  · exact cols_left1_eq_4_0_3
  · exact cols_left1_eq_4_0_4
  · exact cols_left1_eq_4_0_5
  · exact cols_left1_eq_4_0_6
  · exact cols_left1_eq_4_0_7
  · exact cols_left1_eq_5_0_0
  · exact cols_left1_eq_5_0_1
  · exact cols_left1_eq_5_0_2
  · exact cols_left1_eq_5_0_3
  · exact cols_left1_eq_5_0_4
  · exact cols_left1_eq_5_0_5
  · exact cols_left1_eq_5_0_6
  · exact cols_left1_eq_5_0_7
  · exact cols_left1_eq_6_0_0
  · exact cols_left1_eq_6_0_1
  · exact cols_left1_eq_6_0_2
  · exact cols_left1_eq_6_0_3
  · exact cols_left1_eq_6_0_4
  · exact cols_left1_eq_6_0_5
  · exact cols_left1_eq_6_0_6
  · exact cols_left1_eq_6_0_7
  · exact cols_left1_eq_7_0_0
  · exact cols_left1_eq_7_0_1
  · exact cols_left1_eq_7_0_2
  · exact cols_left1_eq_7_0_3
  · exact cols_left1_eq_7_0_4
  · exact cols_left1_eq_7_0_5
  · exact cols_left1_eq_7_0_6
  · exact cols_left1_eq_7_0_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 64 17 8 2803471062304770750435167344437283330687638094779181769388242213493240106173440,
    decodeIntegerRow 64 17 8 2803504409356422405251689557459040914713212744344372585633830964506372759756800,
    decodeIntegerRow 64 17 8 2803500692612650250569003258531512133277056249821301850697289259859555822187008,
    decodeIntegerRow 64 17 8 2803471075165167884695266696925176625650700232074933279894479756006367138017792,
    decodeIntegerRow 64 17 8 164374858149352521040921254341604609227773160767209548929002930470127815214080,
    decodeIntegerRow 64 17 8 2949583808486350269007581714528534722404522071850424362774757136743638403522560,
    decodeIntegerRow 64 17 8 2639161368591481403850379012522962697300968833647717851382685132664340976644608,
    decodeIntegerRow 64 17 8 165448984238954139724494617214260818092142922229161280473769500770742845665792,
    decodeIntegerRow 64 17 8 2803471074408818857839635592405490740444856690330517777218362348587524677959680,
    decodeIntegerRow 64 17 8 2803504627941291168372685170964348569932187479079344169912957585785670684369920,
    decodeIntegerRow 64 17 8 2803504409314539885957353366027917277040742264429596798605968186592854096753152,
    decodeIntegerRow 64 17 8 2803534259052945489282529820564600850419907947597733266344155925507237983810048,
    decodeIntegerRow 64 17 8 165448984238945083929821952481983669999026151075618391820936078592342808330240,
    decodeIntegerRow 64 17 8 2967843952009577285167387315454988580821518953520533899569294404087756537717760,
    decodeIntegerRow 64 17 8 2949583808486349767546640222733759382985242220430083935396057938869598507479552,
    decodeIntegerRow 64 17 8 5442630462451715791602289884028170354237058447743478613220167360862432265794048,
    decodeIntegerRow 64 17 8 2803471061548113763878795847426502751581756283107077278979915149373282593894912,
    decodeIntegerRow 64 17 8 2803504409314539885957353366027917277040603457480830054104176665112393383817728,
    decodeIntegerRow 64 17 8 2803500692659768084788640497026755032071581536730949029488864673908997099996160,
    decodeIntegerRow 64 17 8 2803471074408818857839635592405490740447085766625419019507021690550795050557440,
    decodeIntegerRow 64 17 8 164374858149343461559035783962933247766833925343643354744421707459578133606912,
    decodeIntegerRow 64 17 8 2949583808486349767546640222733759382985242218768123342162796915310712624624128,
    decodeIntegerRow 64 17 8 2639161368591481967993938352536115021182373444766920323182337813731546223723520,
    decodeIntegerRow 64 17 8 165448984238945083929821952481983669999026177764111179130869063059682686279680,
    decodeIntegerRow 64 17 8 2803534245435891368466058971065926976350963091394917998012844969650387180810752,
    decodeIntegerRow 64 17 8 2803500692612650250569003258531512133276932865866842522674799364926968762741248,
    decodeIntegerRow 64 17 8 2803500911244636847909636110532062687290818462369146686239329334841063692559360,
    decodeIntegerRow 64 17 8 2803471062304770750435167344437283330685409925719239779215693337033074811863040,
    decodeIntegerRow 64 17 8 5441556336362105113436831050776842783911749450846459367803929869931443432714752,
    decodeIntegerRow 64 17 8 2639161368591481403850379012522962697300968832170454921356530064444560189403648,
    decodeIntegerRow 64 17 8 2657421512114708984153743953462568879599370329576248961352520777583249837777920,
    decodeIntegerRow 64 17 8 164374858149352521040921254341604609227773134088940156896315410280148079738880,
    decodeIntegerRow 64 17 8 165448984238954139724494689099635706902485382499838176935061562486929446073280,
    decodeIntegerRow 64 17 8 2639161368591481403850377713797995310559750788898889822475125750821517397750720,
    decodeIntegerRow 64 17 8 2657421512114708984153742655266183083166146266903696647369910808876435603437056,
    decodeIntegerRow 64 17 8 5442630462451706732120404332778452242864483971193031470399896923060484983338496,
    decodeIntegerRow 64 17 8 2803471075165167884701270707207500529306935363215150379914914637182469107610560,
    decodeIntegerRow 64 17 8 2803500692612650250460533749239821825020563523313279150098787930439336156427200,
    decodeIntegerRow 64 17 8 2803500911244636847801210748374801231418499705764822859320288169588822636013056,
    decodeIntegerRow 64 17 8 2803534258296288502719403811986205879702989782452826520936627712731445195613696,
    decodeIntegerRow 64 17 8 164374858149343461559035703089949930643754440077207700373375237956051366278080,
    decodeIntegerRow 64 17 8 2657421512114709485614686743422643681652481667752186663841022401246829451408320,
    decodeIntegerRow 64 17 8 2967843952009577285167386016761120185181729064659849086294236818504418985227776,
    decodeIntegerRow 64 17 8 165448984238945083929821880594887388111844362680892868039326457132041393255936,
    decodeIntegerRow 64 17 8 2803471061548113763872041335858888336784129593739779752675225137350693430784960,
    decodeIntegerRow 64 17 8 2803500911286519367312397664120447408637513974161429241375626776448700127704000,
    decodeIntegerRow 64 17 8 2803504627941291168264215661672658634025057205465274943808483297490379635467776,
    decodeIntegerRow 64 17 8 2803471074408818857833631582123166816178319038395193769370826255529862233499136,
    decodeIntegerRow 64 17 8 5441556336362114169231503787396216213892048010395366872498605431054147492068864,
    decodeIntegerRow 64 17 8 2967843952009577285167386016761120185181729066137147391390555347195434756161024,
    decodeIntegerRow 64 17 8 2949583808486349767546638924568459920351410730350605270773484126629306569585600,
    decodeIntegerRow 64 17 8 164374858149343461559035703089949930643754413399577140490110209805432804045760,
    decodeIntegerRow 64 17 8 2803534246192240395327694085867936785823344285074657516188373570191755002392064,
    decodeIntegerRow 64 17 8 2803504627941291168264215661672658634025180589419734272254520206508784246337024,
    decodeIntegerRow 64 17 8 2803504409314539885848928003870656193366239618654556541970440868590483929232320,
    decodeIntegerRow 64 17 8 2803471061548113763872041335858888336781901424679837770151437044675348464825280,
    decodeIntegerRow 64 17 8 164374858149352521040921335212651359139408401893451665415269653222164242802176,
    decodeIntegerRow 64 17 8 2657421512114708984153742655266183083166146268565617443649237939405182129972736,
    decodeIntegerRow 64 17 8 2967843952009577849310947954193108291444141612343125635398796906121108476358720,
    decodeIntegerRow 64 17 8 165448984238954139724494689099635706902485409188970056505227064438271930986560,
    decodeIntegerRow 64 17 8 2803471062304770750441921856004897722298674448251984016738682578364253599806976,
    decodeIntegerRow 64 17 8 2803500911244636847801210748374801231418638512713589603345589300222766506292736,
    decodeIntegerRow 64 17 8 2803504627988409002700791918751281776983452260405932705771561131013368383041600,
    decodeIntegerRow 64 17 8 2803471075165167884701270707207500529309164439510051629855449079210604032946240]

def cols_right2 (r : LeftIndex 5 3 5) : List ℤ := cols_right2Data.getD (leftPosition 5 3 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 3 5) : (tripleIndices 4 2 8).map (fun j => (right2Middle5 3 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms535.outerABC * HexagonAtoms535.assocABC = HexagonAtoms535.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms535.assocBAC * HexagonAtoms535.innerABC = HexagonAtoms535.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms535.innerRightABC * HexagonAtoms535.assocABC = HexagonAtoms535.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms535.inverseACB * right0Middle5 3 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms535.innerACB * right1Middle5 3 5 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms535.assocBAC * left0Middle5 3 5 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms535.innerRightBAC * left1Middle5 3 5 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms535.assocCAB * right2Middle5 3 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn535

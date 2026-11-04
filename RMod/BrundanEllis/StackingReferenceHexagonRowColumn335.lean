import RMod.BrundanEllis.StackingReferenceHexagonAtoms335
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn335
open Superfusion

theorem assocBAC_alias : HexagonAtoms335.assocBAC = HexagonAtoms335.assocABC :=
  HexagonAtoms335.assocBAC_eq.symm.trans HexagonAtoms335.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms335.innerRightBAC = HexagonAtoms335.innerRightABC :=
  HexagonAtoms335.innerRightBAC_eq.symm.trans HexagonAtoms335.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 2098013684379656462278489549508,
    decodeIntegerRow 64 3 1 2859774937798503689793797935084,
    decodeIntegerRow 64 3 1 1754544477758447161270528384612,
    decodeIntegerRow 64 3 1 1829877823182725436009625352716,
    decodeIntegerRow 64 3 1 1669757853600349919790070967284,
    decodeIntegerRow 64 3 1 1575532308671189898861816406372,
    decodeIntegerRow 64 3 1 1334972356794684661215100141076,
    decodeIntegerRow 64 3 1 570652550399470976229928580548,
    decodeIntegerRow 64 3 1 1858140030505631045304522168076,
    decodeIntegerRow 64 3 1 1763960427546275447384287141732,
    decodeIntegerRow 64 3 1 570768637235907765096501364756,
    decodeIntegerRow 64 3 1 1334623919269765210746498431292,
    decodeIntegerRow 64 3 1 2859891343554821624206255414468,
    decodeIntegerRow 64 3 1 2097664289608786956809956631316,
    decodeIntegerRow 64 3 1 1603791645715172518817336630428,
    decodeIntegerRow 64 3 1 1679182418601706739182453863436,
    decodeIntegerRow 64 3 1 2099059883313071374201337072708,
    decodeIntegerRow 64 3 1 2862915129954626991717311224684,
    decodeIntegerRow 64 3 1 1763960425794571142896257827812,
    decodeIntegerRow 64 3 1 1858140025253853059807201874316,
    decodeIntegerRow 64 3 1 1754501403878385145385869764724,
    decodeIntegerRow 64 3 1 1829892181142746107945350193892,
    decodeIntegerRow 64 3 1 2097664307350885768437534975636,
    decodeIntegerRow 64 3 1 2859891396808093920864622089028,
    decodeIntegerRow 64 3 1 1829877816617852963672686489204,
    decodeIntegerRow 64 3 1 1754544475569266751901389035548,
    decodeIntegerRow 64 3 1 573908935741885097109570543724,
    decodeIntegerRow 64 3 1 1335670153671142818502443992388,
    decodeIntegerRow 64 3 1 570652497292082429058388550332,
    decodeIntegerRow 64 3 1 1334972339101241218234076631404,
    decodeIntegerRow 64 3 1 1858151516873767658598532006372,
    decodeIntegerRow 64 3 1 1763925968441865607564244903284,
    decodeIntegerRow 64 3 1 570652497292082841593530332724,
    decodeIntegerRow 64 3 1 2098711481191272503402437561892,
    decodeIntegerRow 64 3 1 1575532303418744876915228887636,
    decodeIntegerRow 64 3 1 1763925968441865760069993041028,
    decodeIntegerRow 64 3 1 1603806003674659561631771804548,
    decodeIntegerRow 64 3 1 1754544475569266873918700748204,
    decodeIntegerRow 64 3 1 573908935741885508138440596772,
    decodeIntegerRow 64 3 1 2098013666621370899870497397196,
    decodeIntegerRow 64 3 1 1679182416414127461273787131772,
    decodeIntegerRow 64 3 1 1829892181142746148638447495084,
    decodeIntegerRow 64 3 1 2097664307350884534848196575012,
    decodeIntegerRow 64 3 1 573792423484418152387286829364,
    decodeIntegerRow 64 3 1 2099059883313070137097262600244,
    decodeIntegerRow 64 3 1 570768690337885080781433131228,
    decodeIntegerRow 64 3 1 1669723394497941494279742523564,
    decodeIntegerRow 64 3 1 1858140025253853110625923201668,
    decodeIntegerRow 64 3 1 2859891343554821212800296076724,
    decodeIntegerRow 64 3 1 1336019530683724294258496585892,
    decodeIntegerRow 64 3 1 1829892174577339925147412794836,
    decodeIntegerRow 64 3 1 1679182418601706617180638970628,
    decodeIntegerRow 64 3 1 1575543789786881490172046360068,
    decodeIntegerRow 64 3 1 1763960427546275599902432734764,
    decodeIntegerRow 64 3 1 570768637235908177255587001252,
    decodeIntegerRow 64 3 1 2099059901022748511015367810636,
    decodeIntegerRow 64 3 1 1763925966692162412362024315908,
    decodeIntegerRow 64 3 1 1575532308671189848005902710996,
    decodeIntegerRow 64 3 1 1334972356794685898193822559068,
    decodeIntegerRow 64 3 1 2863031269893041920963081405516,
    decodeIntegerRow 64 3 1 2098013684379655228563454726476,
    decodeIntegerRow 64 3 1 573908882494008383835200250532,
    decodeIntegerRow 64 3 1 1679139342534065445404625331156,
    decodeIntegerRow 64 3 1 1829877823182725476656232196092]

def rows_assocABC (r : RightIndex 3 3 5) : List ℤ := rows_assocABCData.getD (rightPosition 3 3 5 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 3 3 5) : (tripleIndices 4 2 8).map ((HexagonAtoms335.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_0_0_4
  · exact rows_assocABC_eq_0_0_5
  · exact rows_assocABC_eq_0_0_6
  · exact rows_assocABC_eq_0_0_7
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_0_2
  · exact rows_assocABC_eq_1_0_3
  · exact rows_assocABC_eq_1_0_4
  · exact rows_assocABC_eq_1_0_5
  · exact rows_assocABC_eq_1_0_6
  · exact rows_assocABC_eq_1_0_7
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_0_2
  · exact rows_assocABC_eq_2_0_3
  · exact rows_assocABC_eq_2_0_4
  · exact rows_assocABC_eq_2_0_5
  · exact rows_assocABC_eq_2_0_6
  · exact rows_assocABC_eq_2_0_7
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_0_2
  · exact rows_assocABC_eq_3_0_3
  · exact rows_assocABC_eq_3_0_4
  · exact rows_assocABC_eq_3_0_5
  · exact rows_assocABC_eq_3_0_6
  · exact rows_assocABC_eq_3_0_7
  · exact rows_assocABC_eq_4_0_0
  · exact rows_assocABC_eq_4_0_1
  · exact rows_assocABC_eq_4_0_2
  · exact rows_assocABC_eq_4_0_3
  · exact rows_assocABC_eq_4_0_4
  · exact rows_assocABC_eq_4_0_5
  · exact rows_assocABC_eq_4_0_6
  · exact rows_assocABC_eq_4_0_7
  · exact rows_assocABC_eq_5_0_0
  · exact rows_assocABC_eq_5_0_1
  · exact rows_assocABC_eq_5_0_2
  · exact rows_assocABC_eq_5_0_3
  · exact rows_assocABC_eq_5_0_4
  · exact rows_assocABC_eq_5_0_5
  · exact rows_assocABC_eq_5_0_6
  · exact rows_assocABC_eq_5_0_7
  · exact rows_assocABC_eq_6_0_0
  · exact rows_assocABC_eq_6_0_1
  · exact rows_assocABC_eq_6_0_2
  · exact rows_assocABC_eq_6_0_3
  · exact rows_assocABC_eq_6_0_4
  · exact rows_assocABC_eq_6_0_5
  · exact rows_assocABC_eq_6_0_6
  · exact rows_assocABC_eq_6_0_7
  · exact rows_assocABC_eq_7_0_0
  · exact rows_assocABC_eq_7_0_1
  · exact rows_assocABC_eq_7_0_2
  · exact rows_assocABC_eq_7_0_3
  · exact rows_assocABC_eq_7_0_4
  · exact rows_assocABC_eq_7_0_5
  · exact rows_assocABC_eq_7_0_6
  · exact rows_assocABC_eq_7_0_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230101669414919104,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1712131568738645212843637889280,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1589726585069718328542338820760,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1715272586125880199319199355520,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 2098381717540610315885862301408,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1844073534696700218898277920000,
    decodeIntegerRow 64 3 1 1759407517595991823801661277472,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 1335340868586723594015732775360,
    decodeIntegerRow 64 3 1 1715271148360363011244471637680,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1730972207609064066756291733120,
    decodeIntegerRow 64 3 1 1721551772955508984598560614040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1759407517668971308242919032400,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1702711594958472751491810535360,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1718412669954502558740113843200,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1730972225334039738249540627904,
    decodeIntegerRow 64 3 1 1712131994159674971414885463360,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 2861396722385791286351301069440,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1702711612683448422985002034840,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 2098342951705790125981935431104,
    decodeIntegerRow 64 3 1 572287097687894749925999895360,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 1844073534696700172956406691808,
    decodeIntegerRow 64 3 1 1759058619246919713458615238976,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1335302102751900933418220769280,
    decodeIntegerRow 64 3 1 2861409644549558209794501987872,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1721552304731796178999821340240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 572274175524104766676004376240,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 1589726585069718282977040307840,
    decodeIntegerRow 64 3 1 1759058619174006937869680388760,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1718411236128068979399837434176,
    decodeIntegerRow 64 3 1 1716320713254230103363218355520]

def rows_inverseACB (r : LeftIndex 3 5 3) : List ℤ := rows_inverseACBData.getD (leftPosition 3 5 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 5 3) : (tripleIndices 8 1 8).map ((HexagonAtoms335.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230101669414919104,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1712131568738645212843637889280,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1589726585069718328542338820760,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1715272586125880199319199355520,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 2098381717540610315885862301408,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1844073534696700218898277920000,
    decodeIntegerRow 64 3 1 1759407517595991823801661277472,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 1335340868586723594015732775360,
    decodeIntegerRow 64 3 1 1715271148360363011244471637680,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1730972207609064066756291733120,
    decodeIntegerRow 64 3 1 1721551772955508984598560614040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1759407517668971308242919032400,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1702711594958472751491810535360,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1718412669954502558740113843200,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1730972225334039738249540627904,
    decodeIntegerRow 64 3 1 1712131994159674971414885463360,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 2861396722385791286351301069440,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1702711612683448422985002034840,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 2098342951705790125981935431104,
    decodeIntegerRow 64 3 1 572287097687894749925999895360,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 1844073534696700172956406691808,
    decodeIntegerRow 64 3 1 1759058619246919713458615238976,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1335302102751900933418220769280,
    decodeIntegerRow 64 3 1 2861409644549558209794501987872,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1721552304731796178999821340240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 572274175524104766676004376240,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 1589726585069718282977040307840,
    decodeIntegerRow 64 3 1 1759058619174006937869680388760,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1718411236128068979399837434176,
    decodeIntegerRow 64 3 1 1716320713254230103363218355520]

def rows_assocBCA (r : RightIndex 3 5 3) : List ℤ := rows_assocBCAData.getD (rightPosition 3 5 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 5 3) : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 64 3 1 1985922194862547137962642155000,
    decodeIntegerRow 64 3 1 2825473560327419520176361335712,
    decodeIntegerRow 64 3 1 2906765454827278525752039167456,
    decodeIntegerRow 64 3 1 2239101836455517062640654702680,
    decodeIntegerRow 64 3 1 2900821314636404966355618435960,
    decodeIntegerRow 64 3 1 2211965316155370459892822048672,
    decodeIntegerRow 64 3 1 1956459673264827970290004320736,
    decodeIntegerRow 64 3 1 2812551447757030866616379581400,
    decodeIntegerRow 64 3 1 608210209040406668365061958944,
    decodeIntegerRow 64 3 1 1985922206002473416480356573480,
    decodeIntegerRow 64 3 1 1194581960836388455302595555720,
    decodeIntegerRow 64 3 1 2906765509820796050201066707808,
    decodeIntegerRow 64 3 1 1221718528405745908265853247456,
    decodeIntegerRow 64 3 1 2900821259335492530727477624920,
    decodeIntegerRow 64 3 1 621132424026924708000821923320,
    decodeIntegerRow 64 3 1 1956459660770445323666787639712,
    decodeIntegerRow 64 3 1 1477073228913684443476978385248,
    decodeIntegerRow 64 3 1 620771509138574310906505091720,
    decodeIntegerRow 64 3 1 533196567527562853854084010200,
    decodeIntegerRow 64 3 1 1221791570200905344918481243616,
    decodeIntegerRow 64 3 1 2907103345472391709108656826272,
    decodeIntegerRow 64 3 1 2239183836357302721270151857400,
    decodeIntegerRow 64 3 1 1985762981045671614826039052200,
    decodeIntegerRow 64 3 1 2825110782552688967249947245344,
    decodeIntegerRow 64 3 1 2812912259645640011991306444120,
    decodeIntegerRow 64 3 1 1477073241415464346304604883936,
    decodeIntegerRow 64 3 1 2211892225826813066107380359008,
    decodeIntegerRow 64 3 1 533196622812776502521133617160,
    decodeIntegerRow 64 3 1 1194499960931208064051813648600,
    decodeIntegerRow 64 3 1 2907103400481430130748011445216,
    decodeIntegerRow 64 3 1 608572986831903347788364996448,
    decodeIntegerRow 64 3 1 1985762992178586064557585130120,
    decodeIntegerRow 64 3 1 526580419811081790224722444680,
    decodeIntegerRow 64 3 1 2239183859361303136298819757472,
    decodeIntegerRow 64 3 1 1985762992178587261124905632736,
    decodeIntegerRow 64 3 1 608572986831903638211855765800,
    decodeIntegerRow 64 3 1 1477073241415463163684477255160,
    decodeIntegerRow 64 3 1 2812912259645639753367302166368,
    decodeIntegerRow 64 3 1 2900487197479736516532816193824,
    decodeIntegerRow 64 3 1 1221791594465700696441941594200,
    decodeIntegerRow 64 3 1 1194499983935208479080540904224,
    decodeIntegerRow 64 3 1 526580474820121339234282637400,
    decodeIntegerRow 64 3 1 2825110782552689257673425991160,
    decodeIntegerRow 64 3 1 1985762981045670418258773513568,
    decodeIntegerRow 64 3 1 620771509138574052282487328544,
    decodeIntegerRow 64 3 1 1477073228913685626097161589720,
    decodeIntegerRow 64 3 1 2211892250091608417630900396920,
    decodeIntegerRow 64 3 1 2900487252764949096407638163808,
    decodeIntegerRow 64 3 1 532862560957019419613132333472,
    decodeIntegerRow 64 3 1 2211965291886765298861082304520,
    decodeIntegerRow 64 3 1 1956459660770446506676401991000,
    decodeIntegerRow 64 3 1 621132424026924966787714989344,
    decodeIntegerRow 64 3 1 1985922206002474612656124092832,
    decodeIntegerRow 64 3 1 608210209040406958616710214280,
    decodeIntegerRow 64 3 1 526918310471715870683163121880,
    decodeIntegerRow 64 3 1 2239101859456122744683346021664,
    decodeIntegerRow 64 3 1 1221718504137140747234053832920,
    decodeIntegerRow 64 3 1 532862505656108052619495973664,
    decodeIntegerRow 64 3 1 2812551447757031125403286140832,
    decodeIntegerRow 64 3 1 1956459673264826787280334375560,
    decodeIntegerRow 64 3 1 2825473560327419810427997575080,
    decodeIntegerRow 64 3 1 1985922194862545941786929581536,
    decodeIntegerRow 64 3 1 1194581983836994137345346247008,
    decodeIntegerRow 64 3 1 526918365465234522679404352760]

def rows_assocCAB (r : RightIndex 5 3 3) : List ℤ := rows_assocCABData.getD (rightPosition 5 3 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 3 3) : (tripleIndices 8 1 8).map ((HexagonAtoms335.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_1_4
  · exact rows_assocCAB_eq_0_1_5
  · exact rows_assocCAB_eq_0_1_6
  · exact rows_assocCAB_eq_0_1_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_1_1_4
  · exact rows_assocCAB_eq_1_1_5
  · exact rows_assocCAB_eq_1_1_6
  · exact rows_assocCAB_eq_1_1_7
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_0_4
  · exact rows_assocCAB_eq_2_0_5
  · exact rows_assocCAB_eq_2_0_6
  · exact rows_assocCAB_eq_2_0_7
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_2_1_2
  · exact rows_assocCAB_eq_2_1_3
  · exact rows_assocCAB_eq_2_1_4
  · exact rows_assocCAB_eq_2_1_5
  · exact rows_assocCAB_eq_2_1_6
  · exact rows_assocCAB_eq_2_1_7
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_0_4
  · exact rows_assocCAB_eq_3_0_5
  · exact rows_assocCAB_eq_3_0_6
  · exact rows_assocCAB_eq_3_0_7
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1
  · exact rows_assocCAB_eq_3_1_2
  · exact rows_assocCAB_eq_3_1_3
  · exact rows_assocCAB_eq_3_1_4
  · exact rows_assocCAB_eq_3_1_5
  · exact rows_assocCAB_eq_3_1_6
  · exact rows_assocCAB_eq_3_1_7

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 1712131861324870279014072089872,
    decodeIntegerRow 64 3 1 1730972535209061703904289359380,
    decodeIntegerRow 64 3 1 1717365975665096334394099244740,
    decodeIntegerRow 64 3 1 1715274020977559995219472014384,
    decodeIntegerRow 64 3 1 1335327955613987661544651307248,
    decodeIntegerRow 64 3 1 2861422540233496774088559789100,
    decodeIntegerRow 64 3 1 1759291217172353739627351945340,
    decodeIntegerRow 64 3 1 1589842887481876905904749978576,
    decodeIntegerRow 64 3 1 1717364539869155540399142303088,
    decodeIntegerRow 64 3 1 1718414106702778165681437941740,
    decodeIntegerRow 64 3 1 1721552118500524790609176940860,
    decodeIntegerRow 64 3 1 1730972056610414315036777317456,
    decodeIntegerRow 64 3 1 1759174917701049347692121824912,
    decodeIntegerRow 64 3 1 1844189831224548713888935273940,
    decodeIntegerRow 64 3 1 2098368786842003085494624390020,
    decodeIntegerRow 64 3 1 2861383773743061982425407276464,
    decodeIntegerRow 64 3 1 1721551958967642342716248555792,
    decodeIntegerRow 64 3 1 1702711285083450826569907823380,
    decodeIntegerRow 64 3 1 1716317844627414914896007871940,
    decodeIntegerRow 64 3 1 1718409799314952077663076888624,
    decodeIntegerRow 64 3 1 2098355864678524821420945046768,
    decodeIntegerRow 64 3 1 572261280059015710003655373100,
    decodeIntegerRow 64 3 1 1674392603120158760281950748540,
    decodeIntegerRow 64 3 1 1843840932810635583836744792016,
    decodeIntegerRow 64 3 1 1716319280423358179584607345008,
    decodeIntegerRow 64 3 1 1715269713589733907187163823340,
    decodeIntegerRow 64 3 1 1712131701791987831497716428860,
    decodeIntegerRow 64 3 1 1702711763682098123930247919696,
    decodeIntegerRow 64 3 1 1674508902591463121714790220432,
    decodeIntegerRow 64 3 1 1589493989067963775852731683540,
    decodeIntegerRow 64 3 1 1335315033450509397466322918020,
    decodeIntegerRow 64 3 1 572300046549450502796526057904,
    decodeIntegerRow 64 3 1 1844189837141279237296640505660,
    decodeIntegerRow 64 3 1 1759174919667889448623998660784,
    decodeIntegerRow 64 3 1 572299993372722352129217245072,
    decodeIntegerRow 64 3 1 1335315015724332970587628469740,
    decodeIntegerRow 64 3 1 1715269713516688263131862009220,
    decodeIntegerRow 64 3 1 1716319280399074967704020959056,
    decodeIntegerRow 64 3 1 1730972057266917131704719423088,
    decodeIntegerRow 64 3 1 1721552118719366474912576169940,
    decodeIntegerRow 64 3 1 572261226880486424842500716740,
    decodeIntegerRow 64 3 1 2098355882404100873147605936336,
    decodeIntegerRow 64 3 1 1589842881581356603109120415728,
    decodeIntegerRow 64 3 1 1759291219144597247429920040980,
    decodeIntegerRow 64 3 1 1730972535865586756814495561340,
    decodeIntegerRow 64 3 1 1712131861106036006791421890864,
    decodeIntegerRow 64 3 1 1718409799387798419102511082512,
    decodeIntegerRow 64 3 1 1716317844603067464982207955500,
    decodeIntegerRow 64 3 1 1844189837141279232212822873660,
    decodeIntegerRow 64 3 1 1759174919667889463874934996144,
    decodeIntegerRow 64 3 1 572299993372722352693301463952,
    decodeIntegerRow 64 3 1 1335315015724332968890726767340,
    decodeIntegerRow 64 3 1 1715269713516687851342633817220,
    decodeIntegerRow 64 3 1 1716319280399076203029864123216,
    decodeIntegerRow 64 3 1 1730972057266917177395541152368,
    decodeIntegerRow 64 3 1 1721552118719366337463538275540,
    decodeIntegerRow 64 3 1 572261226880486424276866815940,
    decodeIntegerRow 64 3 1 2098355882404100871455353279696,
    decodeIntegerRow 64 3 1 1589842881581356598025474970608,
    decodeIntegerRow 64 3 1 1759291219144597232178467144980,
    decodeIntegerRow 64 3 1 1730972535865586710998149596540,
    decodeIntegerRow 64 3 1 1712131861106035869718956703024,
    decodeIntegerRow 64 3 1 1718409799387798007327230027792,
    decodeIntegerRow 64 3 1 1716317844603066229614523379500]

def cols_innerABC (r : LeftIndex 3 3 5) : List ℤ := cols_innerABCData.getD (leftPosition 3 3 5 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 3 3 5) : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms335.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_0_4
  · exact cols_innerABC_eq_0_0_5
  · exact cols_innerABC_eq_0_0_6
  · exact cols_innerABC_eq_0_0_7
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_1_2
  · exact cols_innerABC_eq_0_1_3
  · exact cols_innerABC_eq_0_1_4
  · exact cols_innerABC_eq_0_1_5
  · exact cols_innerABC_eq_0_1_6
  · exact cols_innerABC_eq_0_1_7
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_0_2
  · exact cols_innerABC_eq_1_0_3
  · exact cols_innerABC_eq_1_0_4
  · exact cols_innerABC_eq_1_0_5
  · exact cols_innerABC_eq_1_0_6
  · exact cols_innerABC_eq_1_0_7
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_1_1_2
  · exact cols_innerABC_eq_1_1_3
  · exact cols_innerABC_eq_1_1_4
  · exact cols_innerABC_eq_1_1_5
  · exact cols_innerABC_eq_1_1_6
  · exact cols_innerABC_eq_1_1_7
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_0_2
  · exact cols_innerABC_eq_2_0_3
  · exact cols_innerABC_eq_2_0_4
  · exact cols_innerABC_eq_2_0_5
  · exact cols_innerABC_eq_2_0_6
  · exact cols_innerABC_eq_2_0_7
  · exact cols_innerABC_eq_2_1_0
  · exact cols_innerABC_eq_2_1_1
  · exact cols_innerABC_eq_2_1_2
  · exact cols_innerABC_eq_2_1_3
  · exact cols_innerABC_eq_2_1_4
  · exact cols_innerABC_eq_2_1_5
  · exact cols_innerABC_eq_2_1_6
  · exact cols_innerABC_eq_2_1_7
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_0_2
  · exact cols_innerABC_eq_3_0_3
  · exact cols_innerABC_eq_3_0_4
  · exact cols_innerABC_eq_3_0_5
  · exact cols_innerABC_eq_3_0_6
  · exact cols_innerABC_eq_3_0_7
  · exact cols_innerABC_eq_3_1_0
  · exact cols_innerABC_eq_3_1_1
  · exact cols_innerABC_eq_3_1_2
  · exact cols_innerABC_eq_3_1_3
  · exact cols_innerABC_eq_3_1_4
  · exact cols_innerABC_eq_3_1_5
  · exact cols_innerABC_eq_3_1_6
  · exact cols_innerABC_eq_3_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1669565933784056595011996549012,
    decodeIntegerRow 64 3 1 1858204003194494462403465669772,
    decodeIntegerRow 64 3 1 2098864154166978263920584347236,
    decodeIntegerRow 64 3 1 570717746244005433612490987204,
    decodeIntegerRow 64 3 1 1335827612626228648821080675524,
    decodeIntegerRow 64 3 1 2859838857236458857110329335964,
    decodeIntegerRow 64 3 1 1754348728722414610632618107532,
    decodeIntegerRow 64 3 1 1603856894664123324198426592108,
    decodeIntegerRow 64 3 1 1829943072134648434913070686092,
    decodeIntegerRow 64 3 1 1754697150734154172323097405548,
    decodeIntegerRow 64 3 1 573856396173281986542827605444,
    decodeIntegerRow 64 3 1 1335862053979446287514505846684,
    decodeIntegerRow 64 3 1 570703441388934321739967189404,
    decodeIntegerRow 64 3 1 1334776609947833617962656870716,
    decodeIntegerRow 64 3 1 1858087538935490750414501178988,
    decodeIntegerRow 64 3 1 1763768507737075361885773703028,
    decodeIntegerRow 64 3 1 1678986671754854475841271418572,
    decodeIntegerRow 64 3 1 1829943065566803728195377374292,
    decodeIntegerRow 64 3 1 2097821748563874020773088990716,
    decodeIntegerRow 64 3 1 573856449423522741207813930844,
    decodeIntegerRow 64 3 1 2098907228047041513449681169316,
    decodeIntegerRow 64 3 1 570703388283985172870916454396,
    decodeIntegerRow 64 3 1 1669915310812827166780546694828,
    decodeIntegerRow 64 3 1 1858087544184904190474244809932,
    decodeIntegerRow 64 3 1 1858203997939684946214078971308,
    decodeIntegerRow 64 3 1 1764117884749658193303633685452,
    decodeIntegerRow 64 3 1 570717799348421735101962624676,
    decodeIntegerRow 64 3 1 1334819683826293390744155004156,
    decodeIntegerRow 64 3 1 2859838910487367523737548848644,
    decodeIntegerRow 64 3 1 2097856225417474799928243080356,
    decodeIntegerRow 64 3 1 1603856888101689334757547522868,
    decodeIntegerRow 64 3 1 1679335089389834472396952773548,
    decodeIntegerRow 64 3 1 1575596276107608253325724134116,
    decodeIntegerRow 64 3 1 1669915310812827288852778935996,
    decodeIntegerRow 64 3 1 2862980432008527722985731989228,
    decodeIntegerRow 64 3 1 2098907228047040279803693285132,
    decodeIntegerRow 64 3 1 573856449423523153578191975692,
    decodeIntegerRow 64 3 1 1335862071728637226835613243412,
    decodeIntegerRow 64 3 1 1829943065566803677546604505276,
    decodeIntegerRow 64 3 1 1754697148537658161265681990684,
    decodeIntegerRow 64 3 1 1754348730902678164835691392324,
    decodeIntegerRow 64 3 1 1603856888101689385783407778276,
    decodeIntegerRow 64 3 1 1335827594875036447696013290228,
    decodeIntegerRow 64 3 1 2859838910487367111413680368108,
    decodeIntegerRow 64 3 1 1334819683826294624402597818348,
    decodeIntegerRow 64 3 1 2862966020944091160791897344012,
    decodeIntegerRow 64 3 1 1764117884749658071356746409956,
    decodeIntegerRow 64 3 1 1575479822352827497961943765436,
    decodeIntegerRow 64 3 1 1829826925628389211485284650884,
    decodeIntegerRow 64 3 1 1754348728722414458057817359324,
    decodeIntegerRow 64 3 1 573844963056053215223632168012,
    decodeIntegerRow 64 3 1 1335827612626229885854730710828,
    decodeIntegerRow 64 3 1 570717746244005844848482707412,
    decodeIntegerRow 64 3 1 1334819666125532987078879402572,
    decodeIntegerRow 64 3 1 1858204003194494421921641670436,
    decodeIntegerRow 64 3 1 1764117886508456011592732732804,
    decodeIntegerRow 64 3 1 1669915312555437000699836056284,
    decodeIntegerRow 64 3 1 1858087538935490709556618663036,
    decodeIntegerRow 64 3 1 2098907210344680100341237576748,
    decodeIntegerRow 64 3 1 570703441388934732938785700788,
    decodeIntegerRow 64 3 1 1335862053979447524563595384652,
    decodeIntegerRow 64 3 1 2859827424119230910485380422188,
    decodeIntegerRow 64 3 1 1754697150734154019873998751364,
    decodeIntegerRow 64 3 1 1603740748157863999096007415004]

def cols_right0 (r : LeftIndex 3 3 5) : List ℤ := cols_right0Data.getD (leftPosition 3 3 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 3 5) : (tripleIndices 8 1 8).map (fun j => (right0Middle3 3 5) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_1_4
  · exact cols_right0_eq_0_1_5
  · exact cols_right0_eq_0_1_6
  · exact cols_right0_eq_0_1_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_1_1_4
  · exact cols_right0_eq_1_1_5
  · exact cols_right0_eq_1_1_6
  · exact cols_right0_eq_1_1_7
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_0_4
  · exact cols_right0_eq_2_0_5
  · exact cols_right0_eq_2_0_6
  · exact cols_right0_eq_2_0_7
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_1_2
  · exact cols_right0_eq_2_1_3
  · exact cols_right0_eq_2_1_4
  · exact cols_right0_eq_2_1_5
  · exact cols_right0_eq_2_1_6
  · exact cols_right0_eq_2_1_7
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_0_4
  · exact cols_right0_eq_3_0_5
  · exact cols_right0_eq_3_0_6
  · exact cols_right0_eq_3_0_7
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_1_2
  · exact cols_right0_eq_3_1_3
  · exact cols_right0_eq_3_1_4
  · exact cols_right0_eq_3_1_5
  · exact cols_right0_eq_3_1_6
  · exact cols_right0_eq_3_1_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1669565933784056595011996549012,
    decodeIntegerRow 64 3 1 1858204003194494462403465669772,
    decodeIntegerRow 64 3 1 2098864154166978263920584347236,
    decodeIntegerRow 64 3 1 570717746244005433612490987204,
    decodeIntegerRow 64 3 1 1335827612626228648821080675524,
    decodeIntegerRow 64 3 1 2859838857236458857110329335964,
    decodeIntegerRow 64 3 1 1754348728722414610632618107532,
    decodeIntegerRow 64 3 1 1603856894664123324198426592108,
    decodeIntegerRow 64 3 1 1829943072134648434913070686092,
    decodeIntegerRow 64 3 1 1754697150734154172323097405548,
    decodeIntegerRow 64 3 1 573856396173281986542827605444,
    decodeIntegerRow 64 3 1 1335862053979446287514505846684,
    decodeIntegerRow 64 3 1 570703441388934321739967189404,
    decodeIntegerRow 64 3 1 1334776609947833617962656870716,
    decodeIntegerRow 64 3 1 1858087538935490750414501178988,
    decodeIntegerRow 64 3 1 1763768507737075361885773703028,
    decodeIntegerRow 64 3 1 1678986671754854475841271418572,
    decodeIntegerRow 64 3 1 1829943065566803728195377374292,
    decodeIntegerRow 64 3 1 2097821748563874020773088990716,
    decodeIntegerRow 64 3 1 573856449423522741207813930844,
    decodeIntegerRow 64 3 1 2098907228047041513449681169316,
    decodeIntegerRow 64 3 1 570703388283985172870916454396,
    decodeIntegerRow 64 3 1 1669915310812827166780546694828,
    decodeIntegerRow 64 3 1 1858087544184904190474244809932,
    decodeIntegerRow 64 3 1 1858203997939684946214078971308,
    decodeIntegerRow 64 3 1 1764117884749658193303633685452,
    decodeIntegerRow 64 3 1 570717799348421735101962624676,
    decodeIntegerRow 64 3 1 1334819683826293390744155004156,
    decodeIntegerRow 64 3 1 2859838910487367523737548848644,
    decodeIntegerRow 64 3 1 2097856225417474799928243080356,
    decodeIntegerRow 64 3 1 1603856888101689334757547522868,
    decodeIntegerRow 64 3 1 1679335089389834472396952773548,
    decodeIntegerRow 64 3 1 1575596276107608253325724134116,
    decodeIntegerRow 64 3 1 1669915310812827288852778935996,
    decodeIntegerRow 64 3 1 2862980432008527722985731989228,
    decodeIntegerRow 64 3 1 2098907228047040279803693285132,
    decodeIntegerRow 64 3 1 573856449423523153578191975692,
    decodeIntegerRow 64 3 1 1335862071728637226835613243412,
    decodeIntegerRow 64 3 1 1829943065566803677546604505276,
    decodeIntegerRow 64 3 1 1754697148537658161265681990684,
    decodeIntegerRow 64 3 1 1754348730902678164835691392324,
    decodeIntegerRow 64 3 1 1603856888101689385783407778276,
    decodeIntegerRow 64 3 1 1335827594875036447696013290228,
    decodeIntegerRow 64 3 1 2859838910487367111413680368108,
    decodeIntegerRow 64 3 1 1334819683826294624402597818348,
    decodeIntegerRow 64 3 1 2862966020944091160791897344012,
    decodeIntegerRow 64 3 1 1764117884749658071356746409956,
    decodeIntegerRow 64 3 1 1575479822352827497961943765436,
    decodeIntegerRow 64 3 1 1829826925628389211485284650884,
    decodeIntegerRow 64 3 1 1754348728722414458057817359324,
    decodeIntegerRow 64 3 1 573844963056053215223632168012,
    decodeIntegerRow 64 3 1 1335827612626229885854730710828,
    decodeIntegerRow 64 3 1 570717746244005844848482707412,
    decodeIntegerRow 64 3 1 1334819666125532987078879402572,
    decodeIntegerRow 64 3 1 1858204003194494421921641670436,
    decodeIntegerRow 64 3 1 1764117886508456011592732732804,
    decodeIntegerRow 64 3 1 1669915312555437000699836056284,
    decodeIntegerRow 64 3 1 1858087538935490709556618663036,
    decodeIntegerRow 64 3 1 2098907210344680100341237576748,
    decodeIntegerRow 64 3 1 570703441388934732938785700788,
    decodeIntegerRow 64 3 1 1335862053979447524563595384652,
    decodeIntegerRow 64 3 1 2859827424119230910485380422188,
    decodeIntegerRow 64 3 1 1754697150734154019873998751364,
    decodeIntegerRow 64 3 1 1603740748157863999096007415004]

def cols_left0 (r : LeftIndex 3 3 5) : List ℤ := cols_left0Data.getD (leftPosition 3 3 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 3 5) : (tripleIndices 8 1 8).map (fun j => (left0Middle3 3 5) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_1_4
  · exact cols_left0_eq_0_1_5
  · exact cols_left0_eq_0_1_6
  · exact cols_left0_eq_0_1_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_1_1_4
  · exact cols_left0_eq_1_1_5
  · exact cols_left0_eq_1_1_6
  · exact cols_left0_eq_1_1_7
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_0_4
  · exact cols_left0_eq_2_0_5
  · exact cols_left0_eq_2_0_6
  · exact cols_left0_eq_2_0_7
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_1_2
  · exact cols_left0_eq_2_1_3
  · exact cols_left0_eq_2_1_4
  · exact cols_left0_eq_2_1_5
  · exact cols_left0_eq_2_1_6
  · exact cols_left0_eq_2_1_7
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_0_4
  · exact cols_left0_eq_3_0_5
  · exact cols_left0_eq_3_0_6
  · exact cols_left0_eq_3_0_7
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_1_2
  · exact cols_left0_eq_3_1_3
  · exact cols_left0_eq_3_1_4
  · exact cols_left0_eq_3_1_5
  · exact cols_left0_eq_3_1_6
  · exact cols_left0_eq_3_1_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 64 5 2 236006219241472177558208421045738662207850352,
    decodeIntegerRow 64 5 2 55861005680301358580416176581583318579920064,
    decodeIntegerRow 64 5 2 52420424882282278334545049931726165064282560,
    decodeIntegerRow 64 5 2 218664759417902718602328172498759780410977872,
    decodeIntegerRow 64 5 2 52530345840639457519920650754174866236158064,
    decodeIntegerRow 64 5 2 219352920056804254594279990917644180801602752,
    decodeIntegerRow 64 5 2 236705926200057188876906953579002701270350272,
    decodeIntegerRow 64 5 2 56028658235984520645639005934915857642420560,
    decodeIntegerRow 64 5 2 486240080565269207937469814086160974632970560,
    decodeIntegerRow 64 5 2 236006219241022012325955949550670302832850352,
    decodeIntegerRow 64 5 2 323436326825527107181607356840190567489412752,
    decodeIntegerRow 64 5 2 52420424879418104834682229790964446314282560,
    decodeIntegerRow 64 5 2 322748166185261329113526807552775893661287872,
    decodeIntegerRow 64 5 2 52530345843505100646815154816904358423658064,
    decodeIntegerRow 64 5 2 486072428003947178724980059897623357445470064,
    decodeIntegerRow 64 5 2 236705926200516518323330596262401138770350272,
    decodeIntegerRow 64 5 2 305395424734074955237118914848381484520350272,
    decodeIntegerRow 64 5 2 486073546827359431547867987429819402367420560,
    decodeIntegerRow 64 5 2 489569639487197965564033839974603362523658064,
    decodeIntegerRow 64 5 2 322747990340831715323964527374705825301602752,
    decodeIntegerRow 64 5 2 52419323114716215938152823720255217798608064,
    decodeIntegerRow 64 5 2 218664579991651085614247790104332290176912752,
    decodeIntegerRow 64 5 2 236006487457144070546145156150859511817540272,
    decodeIntegerRow 64 5 2 55862125069327267709946368014611883032970560,
    decodeIntegerRow 64 5 2 56027539418213317761021588122568445532970064,
    decodeIntegerRow 64 5 2 305395424733615622275138817602580703270350272,
    decodeIntegerRow 64 5 2 219353095902607132623905709511241592911287872,
    decodeIntegerRow 64 5 2 489569639484332336878227177884378753148658064,
    decodeIntegerRow 64 5 2 323436506251778742474524846798363174910977872,
    decodeIntegerRow 64 5 2 52419323111852028008378032471856780298608064,
    decodeIntegerRow 64 5 2 486238961176243284143334362780847253929920064,
    decodeIntegerRow 64 5 2 236006487456693908783255539709526504005040272,
    decodeIntegerRow 64 5 2 489681763130900188995352867867669768579858064,
    decodeIntegerRow 64 5 2 218664579990973474529220333820763077254727872,
    decodeIntegerRow 64 5 2 236006487456693908783237055069011246239100352,
    decodeIntegerRow 64 5 2 486238961176243284143331352496347722876720560,
    decodeIntegerRow 64 5 2 305395424733615622275157287841850601661290352,
    decodeIntegerRow 64 5 2 56027539418213317761024538302697820336170560,
    decodeIntegerRow 64 5 2 52531446758419880125494781758585296117408064,
    decodeIntegerRow 64 5 2 322747990340145084379801920181712784317537872,
    decodeIntegerRow 64 5 2 323436506251101131389497390514793715958162752,
    decodeIntegerRow 64 5 2 489681763128036001065569076810160002954858064,
    decodeIntegerRow 64 5 2 55862125069327267709943357730112390648670064,
    decodeIntegerRow 64 5 2 236006487457144070546163640791374527489100352,
    decodeIntegerRow 64 5 2 486073546827359431547870937609948816626720064,
    decodeIntegerRow 64 5 2 305395424734074955237100444609111343848790352,
    decodeIntegerRow 64 5 2 219353095901920501679743102318248305770352752,
    decodeIntegerRow 64 5 2 52531446755554251439697001252374358617408064,
    decodeIntegerRow 64 5 2 489570740399247116356915686394968323267408064,
    decodeIntegerRow 64 5 2 219352920057490887890218363529643569442537872,
    decodeIntegerRow 64 5 2 236705926200516518323312125927025283348790352,
    decodeIntegerRow 64 5 2 486072428003947178724977109694757166236170560,
    decodeIntegerRow 64 5 2 236006219241022012325937465006309830223790272,
    decodeIntegerRow 64 5 2 486240080565269207937466803824700994361170064,
    decodeIntegerRow 64 5 2 489680661363334112169048670563974700220532560,
    decodeIntegerRow 64 5 2 218664759417225109822137823873576797958162752,
    decodeIntegerRow 64 5 2 322748166185947962409465180164775528457852752,
    decodeIntegerRow 64 5 2 489570740402112759483801308903894104517408064,
    decodeIntegerRow 64 5 2 56028658235984520645636055732049626976720064,
    decodeIntegerRow 64 5 2 236705926200057188876925423914378798973790352,
    decodeIntegerRow 64 5 2 55861005680301358580413166320123376976720560,
    decodeIntegerRow 64 5 2 236006219241472177558226905590098892723790272,
    decodeIntegerRow 64 5 2 323436326824849498401417008215007339004727872,
    decodeIntegerRow 64 5 2 489680661360469938669176850583276458033032560]

def cols_right2 (r : LeftIndex 3 3 5) : List ℤ := cols_right2Data.getD (leftPosition 3 3 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 3 5) : (tripleIndices 8 1 8).map (fun j => (right2Middle3 3 5) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_1_4
  · exact cols_right2_eq_0_1_5
  · exact cols_right2_eq_0_1_6
  · exact cols_right2_eq_0_1_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_1_1_4
  · exact cols_right2_eq_1_1_5
  · exact cols_right2_eq_1_1_6
  · exact cols_right2_eq_1_1_7
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_0_4
  · exact cols_right2_eq_2_0_5
  · exact cols_right2_eq_2_0_6
  · exact cols_right2_eq_2_0_7
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_1_2
  · exact cols_right2_eq_2_1_3
  · exact cols_right2_eq_2_1_4
  · exact cols_right2_eq_2_1_5
  · exact cols_right2_eq_2_1_6
  · exact cols_right2_eq_2_1_7
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_0_4
  · exact cols_right2_eq_3_0_5
  · exact cols_right2_eq_3_0_6
  · exact cols_right2_eq_3_0_7
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_1_2
  · exact cols_right2_eq_3_1_3
  · exact cols_right2_eq_3_1_4
  · exact cols_right2_eq_3_1_5
  · exact cols_right2_eq_3_1_6
  · exact cols_right2_eq_3_1_7

theorem product0_eq : HexagonAtoms335.outerABC * HexagonAtoms335.assocABC = HexagonAtoms335.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms335.assocABC * HexagonAtoms335.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms335.innerRightABC * HexagonAtoms335.assocABC = HexagonAtoms335.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms335.inverseACB * right0Middle3 3 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms335.innerACB * right1Middle3 3 5 = right1Middle3 3 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms335.assocBCA * left0Middle3 3 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms335.innerRightABC * left1Middle3 3 5 = left1Middle3 3 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms335.assocCAB * right2Middle3 3 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn335

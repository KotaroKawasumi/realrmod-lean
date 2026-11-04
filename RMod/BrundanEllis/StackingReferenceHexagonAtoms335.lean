import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 64 3 1 2098013684379656462278489549508,
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

def assocABC : Matrix (RightIndex 3 3 5) (LeftIndex 3 3 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 3 5 r) []).getD (leftPosition 3 3 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_4 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_5 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_6 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_7 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_4 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_5 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_6 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_7 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_0 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_1 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_2 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_3 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_4 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_5 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_6 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_4_0_7 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_0 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_1 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_2 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_3 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_4 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_5 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_6 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_5_0_7 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_0 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_1 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_2 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_3 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_4 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_5 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_6 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_6_0_7 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_0 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_1 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_2 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_3 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_4 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_5 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_6 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_7_0_7 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 3 5 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_0_2
  · exact assocABC_row_0_0_3
  · exact assocABC_row_0_0_4
  · exact assocABC_row_0_0_5
  · exact assocABC_row_0_0_6
  · exact assocABC_row_0_0_7
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_0_4
  · exact assocABC_row_1_0_5
  · exact assocABC_row_1_0_6
  · exact assocABC_row_1_0_7
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_0_2
  · exact assocABC_row_2_0_3
  · exact assocABC_row_2_0_4
  · exact assocABC_row_2_0_5
  · exact assocABC_row_2_0_6
  · exact assocABC_row_2_0_7
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_0_2
  · exact assocABC_row_3_0_3
  · exact assocABC_row_3_0_4
  · exact assocABC_row_3_0_5
  · exact assocABC_row_3_0_6
  · exact assocABC_row_3_0_7
  · exact assocABC_row_4_0_0
  · exact assocABC_row_4_0_1
  · exact assocABC_row_4_0_2
  · exact assocABC_row_4_0_3
  · exact assocABC_row_4_0_4
  · exact assocABC_row_4_0_5
  · exact assocABC_row_4_0_6
  · exact assocABC_row_4_0_7
  · exact assocABC_row_5_0_0
  · exact assocABC_row_5_0_1
  · exact assocABC_row_5_0_2
  · exact assocABC_row_5_0_3
  · exact assocABC_row_5_0_4
  · exact assocABC_row_5_0_5
  · exact assocABC_row_5_0_6
  · exact assocABC_row_5_0_7
  · exact assocABC_row_6_0_0
  · exact assocABC_row_6_0_1
  · exact assocABC_row_6_0_2
  · exact assocABC_row_6_0_3
  · exact assocABC_row_6_0_4
  · exact assocABC_row_6_0_5
  · exact assocABC_row_6_0_6
  · exact assocABC_row_6_0_7
  · exact assocABC_row_7_0_0
  · exact assocABC_row_7_0_1
  · exact assocABC_row_7_0_2
  · exact assocABC_row_7_0_3
  · exact assocABC_row_7_0_4
  · exact assocABC_row_7_0_5
  · exact assocABC_row_7_0_6
  · exact assocABC_row_7_0_7

def outerABC : Matrix (LeftIndex 3 5 3) (RightIndex 3 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_0 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_1 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_2 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_3 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_4 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_5 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_6 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_7 : (outerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_0 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_1 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_2 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_3 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_4 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_5 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_6 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_7 : (outerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_0 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_1 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_2 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_3 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_4 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_5 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_6 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_7 : (outerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_0 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_1 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_2 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_3 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_4 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_5 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_6 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_7 : (outerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 3 5 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_0_4
  · exact outerABC_row_0_0_5
  · exact outerABC_row_0_0_6
  · exact outerABC_row_0_0_7
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_0_4
  · exact outerABC_row_2_0_5
  · exact outerABC_row_2_0_6
  · exact outerABC_row_2_0_7
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_0_4
  · exact outerABC_row_3_0_5
  · exact outerABC_row_3_0_6
  · exact outerABC_row_3_0_7
  · exact outerABC_row_4_0_0
  · exact outerABC_row_4_0_1
  · exact outerABC_row_4_0_2
  · exact outerABC_row_4_0_3
  · exact outerABC_row_4_0_4
  · exact outerABC_row_4_0_5
  · exact outerABC_row_4_0_6
  · exact outerABC_row_4_0_7
  · exact outerABC_row_5_0_0
  · exact outerABC_row_5_0_1
  · exact outerABC_row_5_0_2
  · exact outerABC_row_5_0_3
  · exact outerABC_row_5_0_4
  · exact outerABC_row_5_0_5
  · exact outerABC_row_5_0_6
  · exact outerABC_row_5_0_7
  · exact outerABC_row_6_0_0
  · exact outerABC_row_6_0_1
  · exact outerABC_row_6_0_2
  · exact outerABC_row_6_0_3
  · exact outerABC_row_6_0_4
  · exact outerABC_row_6_0_5
  · exact outerABC_row_6_0_6
  · exact outerABC_row_6_0_7
  · exact outerABC_row_7_0_0
  · exact outerABC_row_7_0_1
  · exact outerABC_row_7_0_2
  · exact outerABC_row_7_0_3
  · exact outerABC_row_7_0_4
  · exact outerABC_row_7_0_5
  · exact outerABC_row_7_0_6
  · exact outerABC_row_7_0_7

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 64 3 1 2098013684379656462278489549508,
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

def assocBAC : Matrix (RightIndex 3 3 5) (LeftIndex 3 3 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 3 3 5 r) []).getD (leftPosition 3 3 5 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_4 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_5 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_6 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_7 : (associatorZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_4 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_5 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_6 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_7 : (associatorZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_4 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_5 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_6 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_7 : (associatorZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_4 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_5 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_6 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_7 : (associatorZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_0 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_1 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_2 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_3 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_4 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_5 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_6 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_7 : (associatorZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_0 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_1 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_2 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_3 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_4 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_5 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_6 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_7 : (associatorZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_0 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_1 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_2 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_3 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_4 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_5 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_6 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_7 : (associatorZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_0 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_1 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_2 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_3 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_4 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_5 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_6 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_7 : (associatorZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 3 3 5 = assocBAC := by
  funext r
  fin_cases r
  · exact assocBAC_row_0_0_0
  · exact assocBAC_row_0_0_1
  · exact assocBAC_row_0_0_2
  · exact assocBAC_row_0_0_3
  · exact assocBAC_row_0_0_4
  · exact assocBAC_row_0_0_5
  · exact assocBAC_row_0_0_6
  · exact assocBAC_row_0_0_7
  · exact assocBAC_row_1_0_0
  · exact assocBAC_row_1_0_1
  · exact assocBAC_row_1_0_2
  · exact assocBAC_row_1_0_3
  · exact assocBAC_row_1_0_4
  · exact assocBAC_row_1_0_5
  · exact assocBAC_row_1_0_6
  · exact assocBAC_row_1_0_7
  · exact assocBAC_row_2_0_0
  · exact assocBAC_row_2_0_1
  · exact assocBAC_row_2_0_2
  · exact assocBAC_row_2_0_3
  · exact assocBAC_row_2_0_4
  · exact assocBAC_row_2_0_5
  · exact assocBAC_row_2_0_6
  · exact assocBAC_row_2_0_7
  · exact assocBAC_row_3_0_0
  · exact assocBAC_row_3_0_1
  · exact assocBAC_row_3_0_2
  · exact assocBAC_row_3_0_3
  · exact assocBAC_row_3_0_4
  · exact assocBAC_row_3_0_5
  · exact assocBAC_row_3_0_6
  · exact assocBAC_row_3_0_7
  · exact assocBAC_row_4_0_0
  · exact assocBAC_row_4_0_1
  · exact assocBAC_row_4_0_2
  · exact assocBAC_row_4_0_3
  · exact assocBAC_row_4_0_4
  · exact assocBAC_row_4_0_5
  · exact assocBAC_row_4_0_6
  · exact assocBAC_row_4_0_7
  · exact assocBAC_row_5_0_0
  · exact assocBAC_row_5_0_1
  · exact assocBAC_row_5_0_2
  · exact assocBAC_row_5_0_3
  · exact assocBAC_row_5_0_4
  · exact assocBAC_row_5_0_5
  · exact assocBAC_row_5_0_6
  · exact assocBAC_row_5_0_7
  · exact assocBAC_row_6_0_0
  · exact assocBAC_row_6_0_1
  · exact assocBAC_row_6_0_2
  · exact assocBAC_row_6_0_3
  · exact assocBAC_row_6_0_4
  · exact assocBAC_row_6_0_5
  · exact assocBAC_row_6_0_6
  · exact assocBAC_row_6_0_7
  · exact assocBAC_row_7_0_0
  · exact assocBAC_row_7_0_1
  · exact assocBAC_row_7_0_2
  · exact assocBAC_row_7_0_3
  · exact assocBAC_row_7_0_4
  · exact assocBAC_row_7_0_5
  · exact assocBAC_row_7_0_6
  · exact assocBAC_row_7_0_7

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1712131861324870279014072089872,
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

def innerABC : Matrix (LeftIndex 3 3 5) (LeftIndex 3 3 5) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 3 3 5 r) []).getD (leftPosition 3 3 5 s) 0

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_4 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_5 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_6 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_7 : (innerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_4 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_5 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_6 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_7 : (innerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_2 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_3 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_4 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_5 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_6 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_7 : (innerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_2 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_3 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_4 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_5 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_6 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_7 : (innerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 3 5 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_0_4
  · exact innerABC_row_0_0_5
  · exact innerABC_row_0_0_6
  · exact innerABC_row_0_0_7
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_1_2
  · exact innerABC_row_0_1_3
  · exact innerABC_row_0_1_4
  · exact innerABC_row_0_1_5
  · exact innerABC_row_0_1_6
  · exact innerABC_row_0_1_7
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_0_4
  · exact innerABC_row_1_0_5
  · exact innerABC_row_1_0_6
  · exact innerABC_row_1_0_7
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_1_1_4
  · exact innerABC_row_1_1_5
  · exact innerABC_row_1_1_6
  · exact innerABC_row_1_1_7
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_0_4
  · exact innerABC_row_2_0_5
  · exact innerABC_row_2_0_6
  · exact innerABC_row_2_0_7
  · exact innerABC_row_2_1_0
  · exact innerABC_row_2_1_1
  · exact innerABC_row_2_1_2
  · exact innerABC_row_2_1_3
  · exact innerABC_row_2_1_4
  · exact innerABC_row_2_1_5
  · exact innerABC_row_2_1_6
  · exact innerABC_row_2_1_7
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_0_4
  · exact innerABC_row_3_0_5
  · exact innerABC_row_3_0_6
  · exact innerABC_row_3_0_7
  · exact innerABC_row_3_1_0
  · exact innerABC_row_3_1_1
  · exact innerABC_row_3_1_2
  · exact innerABC_row_3_1_3
  · exact innerABC_row_3_1_4
  · exact innerABC_row_3_1_5
  · exact innerABC_row_3_1_6
  · exact innerABC_row_3_1_7

def innerRightABC : Matrix (RightIndex 3 5 3) (RightIndex 3 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_4 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_5 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_6 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_7 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_4 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_5 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_6 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_7 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_0 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_1 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_2 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_3 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_4 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_5 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_6 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_7 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_0 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_1 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_2 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_3 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_4 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_5 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_6 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_7 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_0 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_1 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_2 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_3 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_4 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_5 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_6 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_7 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_0 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_1 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_2 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_3 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_4 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_5 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_6 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_7 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 3 5 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_0_0_4
  · exact innerRightABC_row_0_0_5
  · exact innerRightABC_row_0_0_6
  · exact innerRightABC_row_0_0_7
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_0_4
  · exact innerRightABC_row_1_0_5
  · exact innerRightABC_row_1_0_6
  · exact innerRightABC_row_1_0_7
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_0_2
  · exact innerRightABC_row_2_0_3
  · exact innerRightABC_row_2_0_4
  · exact innerRightABC_row_2_0_5
  · exact innerRightABC_row_2_0_6
  · exact innerRightABC_row_2_0_7
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_0_2
  · exact innerRightABC_row_3_0_3
  · exact innerRightABC_row_3_0_4
  · exact innerRightABC_row_3_0_5
  · exact innerRightABC_row_3_0_6
  · exact innerRightABC_row_3_0_7
  · exact innerRightABC_row_4_0_0
  · exact innerRightABC_row_4_0_1
  · exact innerRightABC_row_4_0_2
  · exact innerRightABC_row_4_0_3
  · exact innerRightABC_row_4_0_4
  · exact innerRightABC_row_4_0_5
  · exact innerRightABC_row_4_0_6
  · exact innerRightABC_row_4_0_7
  · exact innerRightABC_row_5_0_0
  · exact innerRightABC_row_5_0_1
  · exact innerRightABC_row_5_0_2
  · exact innerRightABC_row_5_0_3
  · exact innerRightABC_row_5_0_4
  · exact innerRightABC_row_5_0_5
  · exact innerRightABC_row_5_0_6
  · exact innerRightABC_row_5_0_7
  · exact innerRightABC_row_6_0_0
  · exact innerRightABC_row_6_0_1
  · exact innerRightABC_row_6_0_2
  · exact innerRightABC_row_6_0_3
  · exact innerRightABC_row_6_0_4
  · exact innerRightABC_row_6_0_5
  · exact innerRightABC_row_6_0_6
  · exact innerRightABC_row_6_0_7
  · exact innerRightABC_row_7_0_0
  · exact innerRightABC_row_7_0_1
  · exact innerRightABC_row_7_0_2
  · exact innerRightABC_row_7_0_3
  · exact innerRightABC_row_7_0_4
  · exact innerRightABC_row_7_0_5
  · exact innerRightABC_row_7_0_6
  · exact innerRightABC_row_7_0_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230101669414919104,
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

def inverseACB : Matrix (LeftIndex 3 5 3) (RightIndex 3 5 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 5 3 r) []).getD (rightPosition 3 5 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_4 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_5 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_6 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_7 : (associatorInverseZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_4 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_5 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_6 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_7 : (associatorInverseZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_4 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_5 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_6 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_7 : (associatorInverseZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_4 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_5 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_6 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_7 : (associatorInverseZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 5 3 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_0_4
  · exact inverseACB_row_0_0_5
  · exact inverseACB_row_0_0_6
  · exact inverseACB_row_0_0_7
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_0_4
  · exact inverseACB_row_1_0_5
  · exact inverseACB_row_1_0_6
  · exact inverseACB_row_1_0_7
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_0_4
  · exact inverseACB_row_2_0_5
  · exact inverseACB_row_2_0_6
  · exact inverseACB_row_2_0_7
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_0_4
  · exact inverseACB_row_3_0_5
  · exact inverseACB_row_3_0_6
  · exact inverseACB_row_3_0_7
  · exact inverseACB_row_4_0_0
  · exact inverseACB_row_4_0_1
  · exact inverseACB_row_4_0_2
  · exact inverseACB_row_4_0_3
  · exact inverseACB_row_4_0_4
  · exact inverseACB_row_4_0_5
  · exact inverseACB_row_4_0_6
  · exact inverseACB_row_4_0_7
  · exact inverseACB_row_5_0_0
  · exact inverseACB_row_5_0_1
  · exact inverseACB_row_5_0_2
  · exact inverseACB_row_5_0_3
  · exact inverseACB_row_5_0_4
  · exact inverseACB_row_5_0_5
  · exact inverseACB_row_5_0_6
  · exact inverseACB_row_5_0_7
  · exact inverseACB_row_6_0_0
  · exact inverseACB_row_6_0_1
  · exact inverseACB_row_6_0_2
  · exact inverseACB_row_6_0_3
  · exact inverseACB_row_6_0_4
  · exact inverseACB_row_6_0_5
  · exact inverseACB_row_6_0_6
  · exact inverseACB_row_6_0_7
  · exact inverseACB_row_7_0_0
  · exact inverseACB_row_7_0_1
  · exact inverseACB_row_7_0_2
  · exact inverseACB_row_7_0_3
  · exact inverseACB_row_7_0_4
  · exact inverseACB_row_7_0_5
  · exact inverseACB_row_7_0_6
  · exact inverseACB_row_7_0_7

def innerACB : Matrix (LeftIndex 5 3 3) (LeftIndex 3 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_4 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_5 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_6 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_7 : (innerLeftZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_4 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_5 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_6 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_7 : (innerLeftZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_0 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_1 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_2 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_3 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_4 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_5 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_6 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_4_0_7 : (innerLeftZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_0 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_1 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_2 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_3 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_4 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_5 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_6 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_5_0_7 : (innerLeftZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_0 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_1 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_2 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_3 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_4 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_5 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_6 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_6_0_7 : (innerLeftZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_0 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_1 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_2 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_3 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_4 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_5 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_6 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_7_0_7 : (innerLeftZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 5 3 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_0_0_4
  · exact innerACB_row_0_0_5
  · exact innerACB_row_0_0_6
  · exact innerACB_row_0_0_7
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_0_4
  · exact innerACB_row_1_0_5
  · exact innerACB_row_1_0_6
  · exact innerACB_row_1_0_7
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_2_0_4
  · exact innerACB_row_2_0_5
  · exact innerACB_row_2_0_6
  · exact innerACB_row_2_0_7
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_3_0_4
  · exact innerACB_row_3_0_5
  · exact innerACB_row_3_0_6
  · exact innerACB_row_3_0_7
  · exact innerACB_row_4_0_0
  · exact innerACB_row_4_0_1
  · exact innerACB_row_4_0_2
  · exact innerACB_row_4_0_3
  · exact innerACB_row_4_0_4
  · exact innerACB_row_4_0_5
  · exact innerACB_row_4_0_6
  · exact innerACB_row_4_0_7
  · exact innerACB_row_5_0_0
  · exact innerACB_row_5_0_1
  · exact innerACB_row_5_0_2
  · exact innerACB_row_5_0_3
  · exact innerACB_row_5_0_4
  · exact innerACB_row_5_0_5
  · exact innerACB_row_5_0_6
  · exact innerACB_row_5_0_7
  · exact innerACB_row_6_0_0
  · exact innerACB_row_6_0_1
  · exact innerACB_row_6_0_2
  · exact innerACB_row_6_0_3
  · exact innerACB_row_6_0_4
  · exact innerACB_row_6_0_5
  · exact innerACB_row_6_0_6
  · exact innerACB_row_6_0_7
  · exact innerACB_row_7_0_0
  · exact innerACB_row_7_0_1
  · exact innerACB_row_7_0_2
  · exact innerACB_row_7_0_3
  · exact innerACB_row_7_0_4
  · exact innerACB_row_7_0_5
  · exact innerACB_row_7_0_6
  · exact innerACB_row_7_0_7

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230101669414919104,
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

def assocBCA : Matrix (RightIndex 3 5 3) (LeftIndex 3 5 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 3 5 3 r) []).getD (leftPosition 3 5 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 3 5 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 3 5 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_4 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_5 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_6 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_7 : (associatorZ 3 5 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_4 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_5 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_6 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_7 : (associatorZ 3 5 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_0 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_1 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_2 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_3 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_4 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_5 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_6 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_7 : (associatorZ 3 5 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_0 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_1 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_2 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_3 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_4 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_5 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_6 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_7 : (associatorZ 3 5 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_0 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_1 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_2 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_3 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_4 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_5 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_6 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_7 : (associatorZ 3 5 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_0 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_1 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_2 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_3 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_4 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_5 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_6 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_7 : (associatorZ 3 5 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 3 5 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_0_0_4
  · exact assocBCA_row_0_0_5
  · exact assocBCA_row_0_0_6
  · exact assocBCA_row_0_0_7
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_0_4
  · exact assocBCA_row_1_0_5
  · exact assocBCA_row_1_0_6
  · exact assocBCA_row_1_0_7
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_2_0_4
  · exact assocBCA_row_2_0_5
  · exact assocBCA_row_2_0_6
  · exact assocBCA_row_2_0_7
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_3_0_4
  · exact assocBCA_row_3_0_5
  · exact assocBCA_row_3_0_6
  · exact assocBCA_row_3_0_7
  · exact assocBCA_row_4_0_0
  · exact assocBCA_row_4_0_1
  · exact assocBCA_row_4_0_2
  · exact assocBCA_row_4_0_3
  · exact assocBCA_row_4_0_4
  · exact assocBCA_row_4_0_5
  · exact assocBCA_row_4_0_6
  · exact assocBCA_row_4_0_7
  · exact assocBCA_row_5_0_0
  · exact assocBCA_row_5_0_1
  · exact assocBCA_row_5_0_2
  · exact assocBCA_row_5_0_3
  · exact assocBCA_row_5_0_4
  · exact assocBCA_row_5_0_5
  · exact assocBCA_row_5_0_6
  · exact assocBCA_row_5_0_7
  · exact assocBCA_row_6_0_0
  · exact assocBCA_row_6_0_1
  · exact assocBCA_row_6_0_2
  · exact assocBCA_row_6_0_3
  · exact assocBCA_row_6_0_4
  · exact assocBCA_row_6_0_5
  · exact assocBCA_row_6_0_6
  · exact assocBCA_row_6_0_7
  · exact assocBCA_row_7_0_0
  · exact assocBCA_row_7_0_1
  · exact assocBCA_row_7_0_2
  · exact assocBCA_row_7_0_3
  · exact assocBCA_row_7_0_4
  · exact assocBCA_row_7_0_5
  · exact assocBCA_row_7_0_6
  · exact assocBCA_row_7_0_7

def innerRightBAC : Matrix (RightIndex 3 5 3) (RightIndex 3 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 3 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 3 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 3 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 3 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_0 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_1 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_2 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_3 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_4 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_5 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_6 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_7 : (innerRightZ 3 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_0 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_1 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_2 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_3 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_4 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_5 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_6 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_7 : (innerRightZ 3 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_0 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_1 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_2 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_3 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_4 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_5 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_6 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_7 : (innerRightZ 3 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_0 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_1 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_2 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_3 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_4 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_5 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_6 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_7 : (innerRightZ 3 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 3 3 5 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_0_0_4
  · exact innerRightBAC_row_0_0_5
  · exact innerRightBAC_row_0_0_6
  · exact innerRightBAC_row_0_0_7
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_0_4
  · exact innerRightBAC_row_1_0_5
  · exact innerRightBAC_row_1_0_6
  · exact innerRightBAC_row_1_0_7
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_2_0_4
  · exact innerRightBAC_row_2_0_5
  · exact innerRightBAC_row_2_0_6
  · exact innerRightBAC_row_2_0_7
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_3_0_4
  · exact innerRightBAC_row_3_0_5
  · exact innerRightBAC_row_3_0_6
  · exact innerRightBAC_row_3_0_7
  · exact innerRightBAC_row_4_0_0
  · exact innerRightBAC_row_4_0_1
  · exact innerRightBAC_row_4_0_2
  · exact innerRightBAC_row_4_0_3
  · exact innerRightBAC_row_4_0_4
  · exact innerRightBAC_row_4_0_5
  · exact innerRightBAC_row_4_0_6
  · exact innerRightBAC_row_4_0_7
  · exact innerRightBAC_row_5_0_0
  · exact innerRightBAC_row_5_0_1
  · exact innerRightBAC_row_5_0_2
  · exact innerRightBAC_row_5_0_3
  · exact innerRightBAC_row_5_0_4
  · exact innerRightBAC_row_5_0_5
  · exact innerRightBAC_row_5_0_6
  · exact innerRightBAC_row_5_0_7
  · exact innerRightBAC_row_6_0_0
  · exact innerRightBAC_row_6_0_1
  · exact innerRightBAC_row_6_0_2
  · exact innerRightBAC_row_6_0_3
  · exact innerRightBAC_row_6_0_4
  · exact innerRightBAC_row_6_0_5
  · exact innerRightBAC_row_6_0_6
  · exact innerRightBAC_row_6_0_7
  · exact innerRightBAC_row_7_0_0
  · exact innerRightBAC_row_7_0_1
  · exact innerRightBAC_row_7_0_2
  · exact innerRightBAC_row_7_0_3
  · exact innerRightBAC_row_7_0_4
  · exact innerRightBAC_row_7_0_5
  · exact innerRightBAC_row_7_0_6
  · exact innerRightBAC_row_7_0_7

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1985922194862547137962642155000,
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

def assocCAB : Matrix (RightIndex 5 3 3) (LeftIndex 5 3 3) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 5 3 3 r) []).getD (leftPosition 5 3 3 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_4 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_5 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_6 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_7 : (associatorZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_2 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_3 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_4 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_5 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_6 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_7 : (associatorZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_4 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_5 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_6 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_7 : (associatorZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_2 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_3 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_4 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_5 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_6 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_7 : (associatorZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_0 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_1 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_2 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_3 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_4 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_5 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_6 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_7 : (associatorZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_0 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_1 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_2 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_3 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_4 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_5 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_6 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_7 : (associatorZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_0 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_1 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_2 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_3 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_4 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_5 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_6 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_7 : (associatorZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_0 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_1 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_2 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_3 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_4 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_5 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_6 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_7 : (associatorZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 5 3 3 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_0_2
  · exact assocCAB_row_0_0_3
  · exact assocCAB_row_0_0_4
  · exact assocCAB_row_0_0_5
  · exact assocCAB_row_0_0_6
  · exact assocCAB_row_0_0_7
  · exact assocCAB_row_0_1_0
  · exact assocCAB_row_0_1_1
  · exact assocCAB_row_0_1_2
  · exact assocCAB_row_0_1_3
  · exact assocCAB_row_0_1_4
  · exact assocCAB_row_0_1_5
  · exact assocCAB_row_0_1_6
  · exact assocCAB_row_0_1_7
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_0_4
  · exact assocCAB_row_1_0_5
  · exact assocCAB_row_1_0_6
  · exact assocCAB_row_1_0_7
  · exact assocCAB_row_1_1_0
  · exact assocCAB_row_1_1_1
  · exact assocCAB_row_1_1_2
  · exact assocCAB_row_1_1_3
  · exact assocCAB_row_1_1_4
  · exact assocCAB_row_1_1_5
  · exact assocCAB_row_1_1_6
  · exact assocCAB_row_1_1_7
  · exact assocCAB_row_2_0_0
  · exact assocCAB_row_2_0_1
  · exact assocCAB_row_2_0_2
  · exact assocCAB_row_2_0_3
  · exact assocCAB_row_2_0_4
  · exact assocCAB_row_2_0_5
  · exact assocCAB_row_2_0_6
  · exact assocCAB_row_2_0_7
  · exact assocCAB_row_2_1_0
  · exact assocCAB_row_2_1_1
  · exact assocCAB_row_2_1_2
  · exact assocCAB_row_2_1_3
  · exact assocCAB_row_2_1_4
  · exact assocCAB_row_2_1_5
  · exact assocCAB_row_2_1_6
  · exact assocCAB_row_2_1_7
  · exact assocCAB_row_3_0_0
  · exact assocCAB_row_3_0_1
  · exact assocCAB_row_3_0_2
  · exact assocCAB_row_3_0_3
  · exact assocCAB_row_3_0_4
  · exact assocCAB_row_3_0_5
  · exact assocCAB_row_3_0_6
  · exact assocCAB_row_3_0_7
  · exact assocCAB_row_3_1_0
  · exact assocCAB_row_3_1_1
  · exact assocCAB_row_3_1_2
  · exact assocCAB_row_3_1_3
  · exact assocCAB_row_3_1_4
  · exact assocCAB_row_3_1_5
  · exact assocCAB_row_3_1_6
  · exact assocCAB_row_3_1_7

def outerLeftABC : Matrix (RightIndex 5 3 3) (LeftIndex 3 3 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 8) (Fin 4 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 3 3 5) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_4 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_5 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_6 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_7 : (outerLeftZ 3 3 5) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 3 3 5) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_4 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_5 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_6 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_7 : (outerLeftZ 3 3 5) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 3 3 5) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_4 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_5 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_6 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_7 : (outerLeftZ 3 3 5) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 3 3 5) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_4 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_5 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_6 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_7 : (outerLeftZ 3 3 5) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 3 5 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_0_4
  · exact outerLeftABC_row_0_0_5
  · exact outerLeftABC_row_0_0_6
  · exact outerLeftABC_row_0_0_7
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_1_2
  · exact outerLeftABC_row_0_1_3
  · exact outerLeftABC_row_0_1_4
  · exact outerLeftABC_row_0_1_5
  · exact outerLeftABC_row_0_1_6
  · exact outerLeftABC_row_0_1_7
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_0_4
  · exact outerLeftABC_row_1_0_5
  · exact outerLeftABC_row_1_0_6
  · exact outerLeftABC_row_1_0_7
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_1_1_4
  · exact outerLeftABC_row_1_1_5
  · exact outerLeftABC_row_1_1_6
  · exact outerLeftABC_row_1_1_7
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_0_4
  · exact outerLeftABC_row_2_0_5
  · exact outerLeftABC_row_2_0_6
  · exact outerLeftABC_row_2_0_7
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_1_2
  · exact outerLeftABC_row_2_1_3
  · exact outerLeftABC_row_2_1_4
  · exact outerLeftABC_row_2_1_5
  · exact outerLeftABC_row_2_1_6
  · exact outerLeftABC_row_2_1_7
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_0_4
  · exact outerLeftABC_row_3_0_5
  · exact outerLeftABC_row_3_0_6
  · exact outerLeftABC_row_3_0_7
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_1_2
  · exact outerLeftABC_row_3_1_3
  · exact outerLeftABC_row_3_1_4
  · exact outerLeftABC_row_3_1_5
  · exact outerLeftABC_row_3_1_6
  · exact outerLeftABC_row_3_1_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335

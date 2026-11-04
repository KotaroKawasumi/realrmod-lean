import RMod.BrundanEllis.StackingReferenceHexagonAtoms533
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn533
open Superfusion

theorem innerACB_alias : HexagonAtoms533.innerACB = HexagonAtoms533.innerABC :=
  HexagonAtoms533.innerACB_eq.symm.trans HexagonAtoms533.innerABC_eq

theorem assocCAB_alias : HexagonAtoms533.assocCAB = HexagonAtoms533.assocBAC :=
  HexagonAtoms533.assocCAB_eq.symm.trans HexagonAtoms533.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 1712131861324870279014072089872,
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

def rows_innerRightABC (r : RightIndex 5 3 3) : List ℤ := rows_innerRightABCData.getD (rightPosition 5 3 3 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 5 3 3) : (tripleIndices 4 2 8).map ((HexagonAtoms533.innerRightABC) r) = rows_innerRightABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 2897554982954507054731842505336,
    decodeIntegerRow 64 3 1 1222970223449979722641381551680,
    decodeIntegerRow 64 3 1 1449067880720130889938550628160,
    decodeIntegerRow 64 3 1 2822227385089355910184213181032,
    decodeIntegerRow 64 3 1 1193661775176433885492181119040,
    decodeIntegerRow 64 3 1 2910111233441095383976830271816,
    decodeIntegerRow 64 3 1 617732088666983396577370964008,
    decodeIntegerRow 64 3 1 1957399960069170525083945800640,
    decodeIntegerRow 64 3 1 617732140024461086764009046632,
    decodeIntegerRow 64 3 1 1957399947628083115165384520000,
    decodeIntegerRow 64 3 1 1193661798122280389280100963520,
    decodeIntegerRow 64 3 1 2910111178583811873083718763144,
    decodeIntegerRow 64 3 1 1984615950748985231280655225280,
    decodeIntegerRow 64 3 1 611456384137255865695711776808,
    decodeIntegerRow 64 3 1 536128781897345593374390823864,
    decodeIntegerRow 64 3 1 2210713621150079707418858070720,
    decodeIntegerRow 64 3 1 2910037848311567701821323448640,
    decodeIntegerRow 64 3 1 1193326756107685137995083510568,
    decodeIntegerRow 64 3 1 1475920125234549400854492316344,
    decodeIntegerRow 64 3 1 2815792198735876551736359807040,
    decodeIntegerRow 64 3 1 2211050530290305498826236685672,
    decodeIntegerRow 64 3 1 536210518174010803943277622720,
    decodeIntegerRow 64 3 1 2822076786048532555428114556480,
    decodeIntegerRow 64 3 1 1448707974537416627031130604424,
    decodeIntegerRow 64 3 1 611606983185490781536870640320,
    decodeIntegerRow 64 3 1 1984975856948596665902297598536,
    decodeIntegerRow 64 3 1 1222633265679092095085493699368,
    decodeIntegerRow 64 3 1 2897473357555750830400553915200,
    decodeIntegerRow 64 3 1 1475920137692360850921976801656,
    decodeIntegerRow 64 3 1 2815792147385396444198516989120,
    decodeIntegerRow 64 3 1 2910037793458078109821050758080,
    decodeIntegerRow 64 3 1 1193326779069183407694286503272,
    decodeIntegerRow 64 3 1 1984975845755094671508730994880,
    decodeIntegerRow 64 3 1 2822076786048532815459587889736,
    decodeIntegerRow 64 3 1 2897473302118501115674689884968,
    decodeIntegerRow 64 3 1 2211050530290306786665349657920,
    decodeIntegerRow 64 3 1 2815792198735876841138425928056,
    decodeIntegerRow 64 3 1 1957763695057961890902294440640,
    decodeIntegerRow 64 3 1 1193326756107683863717124667840,
    decodeIntegerRow 64 3 1 523645971980945316245306740072,
    decodeIntegerRow 64 3 1 2240357041223327802685543908800,
    decodeIntegerRow 64 3 1 2910037793458078643229858109912,
    decodeIntegerRow 64 3 1 617891672907116329861410302536,
    decodeIntegerRow 64 3 1 1475920137692359658020859360960,
    decodeIntegerRow 64 3 1 2897473357555751395440410714008,
    decodeIntegerRow 64 3 1 2211050554613419101733301622080,
    decodeIntegerRow 64 3 1 1984975856948597852020229664960,
    decodeIntegerRow 64 3 1 2822076837107021443089518561656,
    decodeIntegerRow 64 3 1 1957399960069171718147552547432,
    decodeIntegerRow 64 3 1 2815951731625528799066865605440,
    decodeIntegerRow 64 3 1 2910111233441095917021952680640,
    decodeIntegerRow 64 3 1 2240022045116077324799549444744,
    decodeIntegerRow 64 3 1 611456435203156834112523136960,
    decodeIntegerRow 64 3 1 1449067880720129703648376250408,
    decodeIntegerRow 64 3 1 2210713596842531474098148596664,
    decodeIntegerRow 64 3 1 2897554982954507619410131622080,
    decodeIntegerRow 64 3 1 2210713621150080995337117803144,
    decodeIntegerRow 64 3 1 2897555038395166326605193914560,
    decodeIntegerRow 64 3 1 611456384137255606056837976000,
    decodeIntegerRow 64 3 1 1449067869543528439667312810648,
    decodeIntegerRow 64 3 1 523572641708701144619278970560,
    decodeIntegerRow 64 3 1 1193661798122279114913922599864,
    decodeIntegerRow 64 3 1 1476283872664430562556126432472,
    decodeIntegerRow 64 3 1 617732140024460797750384463680]

def rows_inverseACB (r : LeftIndex 5 3 3) : List ℤ := rows_inverseACBData.getD (leftPosition 5 3 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 3 3) : (tripleIndices 4 2 8).map ((HexagonAtoms533.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 64 3 1 2098013684379656462278489549508,
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

def rows_assocBCA (r : RightIndex 3 3 5) : List ℤ := rows_assocBCAData.getD (rightPosition 3 3 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 3 5) : (tripleIndices 4 2 8).map ((HexagonAtoms533.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230101669414919104,
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

def rows_assocBAC (r : RightIndex 3 5 3) : List ℤ := rows_assocBACData.getD (rightPosition 3 5 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_4_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_5_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_6_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_7_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 3 5 3) : (tripleIndices 8 1 8).map ((HexagonAtoms533.assocBAC) r) = rows_assocBAC r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 2897554982954507054731842505336,
    decodeIntegerRow 64 3 1 1222970223449979722641381551680,
    decodeIntegerRow 64 3 1 1449067880720130889938550628160,
    decodeIntegerRow 64 3 1 2822227385089355910184213181032,
    decodeIntegerRow 64 3 1 1193661775176433885492181119040,
    decodeIntegerRow 64 3 1 2910111233441095383976830271816,
    decodeIntegerRow 64 3 1 617732088666983396577370964008,
    decodeIntegerRow 64 3 1 1957399960069170525083945800640,
    decodeIntegerRow 64 3 1 617732140024461086764009046632,
    decodeIntegerRow 64 3 1 1957399947628083115165384520000,
    decodeIntegerRow 64 3 1 1193661798122280389280100963520,
    decodeIntegerRow 64 3 1 2910111178583811873083718763144,
    decodeIntegerRow 64 3 1 1984615950748985231280655225280,
    decodeIntegerRow 64 3 1 611456384137255865695711776808,
    decodeIntegerRow 64 3 1 536128781897345593374390823864,
    decodeIntegerRow 64 3 1 2210713621150079707418858070720,
    decodeIntegerRow 64 3 1 2910037848311567701821323448640,
    decodeIntegerRow 64 3 1 1193326756107685137995083510568,
    decodeIntegerRow 64 3 1 1475920125234549400854492316344,
    decodeIntegerRow 64 3 1 2815792198735876551736359807040,
    decodeIntegerRow 64 3 1 2211050530290305498826236685672,
    decodeIntegerRow 64 3 1 536210518174010803943277622720,
    decodeIntegerRow 64 3 1 2822076786048532555428114556480,
    decodeIntegerRow 64 3 1 1448707974537416627031130604424,
    decodeIntegerRow 64 3 1 611606983185490781536870640320,
    decodeIntegerRow 64 3 1 1984975856948596665902297598536,
    decodeIntegerRow 64 3 1 1222633265679092095085493699368,
    decodeIntegerRow 64 3 1 2897473357555750830400553915200,
    decodeIntegerRow 64 3 1 1475920137692360850921976801656,
    decodeIntegerRow 64 3 1 2815792147385396444198516989120,
    decodeIntegerRow 64 3 1 2910037793458078109821050758080,
    decodeIntegerRow 64 3 1 1193326779069183407694286503272,
    decodeIntegerRow 64 3 1 1984975845755094671508730994880,
    decodeIntegerRow 64 3 1 2822076786048532815459587889736,
    decodeIntegerRow 64 3 1 2897473302118501115674689884968,
    decodeIntegerRow 64 3 1 2211050530290306786665349657920,
    decodeIntegerRow 64 3 1 2815792198735876841138425928056,
    decodeIntegerRow 64 3 1 1957763695057961890902294440640,
    decodeIntegerRow 64 3 1 1193326756107683863717124667840,
    decodeIntegerRow 64 3 1 523645971980945316245306740072,
    decodeIntegerRow 64 3 1 2240357041223327802685543908800,
    decodeIntegerRow 64 3 1 2910037793458078643229858109912,
    decodeIntegerRow 64 3 1 617891672907116329861410302536,
    decodeIntegerRow 64 3 1 1475920137692359658020859360960,
    decodeIntegerRow 64 3 1 2897473357555751395440410714008,
    decodeIntegerRow 64 3 1 2211050554613419101733301622080,
    decodeIntegerRow 64 3 1 1984975856948597852020229664960,
    decodeIntegerRow 64 3 1 2822076837107021443089518561656,
    decodeIntegerRow 64 3 1 1957399960069171718147552547432,
    decodeIntegerRow 64 3 1 2815951731625528799066865605440,
    decodeIntegerRow 64 3 1 2910111233441095917021952680640,
    decodeIntegerRow 64 3 1 2240022045116077324799549444744,
    decodeIntegerRow 64 3 1 611456435203156834112523136960,
    decodeIntegerRow 64 3 1 1449067880720129703648376250408,
    decodeIntegerRow 64 3 1 2210713596842531474098148596664,
    decodeIntegerRow 64 3 1 2897554982954507619410131622080,
    decodeIntegerRow 64 3 1 2210713621150080995337117803144,
    decodeIntegerRow 64 3 1 2897555038395166326605193914560,
    decodeIntegerRow 64 3 1 611456384137255606056837976000,
    decodeIntegerRow 64 3 1 1449067869543528439667312810648,
    decodeIntegerRow 64 3 1 523572641708701144619278970560,
    decodeIntegerRow 64 3 1 1193661798122279114913922599864,
    decodeIntegerRow 64 3 1 1476283872664430562556126432472,
    decodeIntegerRow 64 3 1 617732140024460797750384463680]

def cols_assocABC (r : LeftIndex 5 3 3) : List ℤ := cols_assocABCData.getD (leftPosition 5 3 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 3 3) : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms533.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 64 9 4 5312861925537657597248526656757735035380230329576367471516144,
    decodeIntegerRow 64 9 4 655020127983220285432780068782529268879150313544544757136496,
    decodeIntegerRow 64 9 4 5887992987397617906221044342010786423174435233170181707687664,
    decodeIntegerRow 64 9 4 5831198589485822267514091690092770233339729179016506594703216,
    decodeIntegerRow 64 9 4 5902369069834040537492836339986789539794370513244930318891664,
    decodeIntegerRow 64 9 4 5960583331075538295360005460086434985647219029149530977263344,
    decodeIntegerRow 64 9 4 6477324599882667134949342830394282304844643409586763430851984,
    decodeIntegerRow 64 9 4 11135184197084132203089543384258266718590553387579821580669424,
    decodeIntegerRow 64 9 4 5829601246992886420467667201632180582259488291067783517163376,
    decodeIntegerRow 64 9 4 5887815504935968106949241537816058499955582925447018211741424,
    decodeIntegerRow 64 9 4 11135184170033053452101011613475520939133866318293000309679504,
    decodeIntegerRow 64 9 4 6477324843342427423646072165197345857070195277870983379875856,
    decodeIntegerRow 64 9 4 655020100932039731498474594357035446587375150723519650081264,
    decodeIntegerRow 64 9 4 5312862168998334112651144508537152824512276211459196134329744,
    decodeIntegerRow 64 9 4 5958985988590848486921250966633506236646561955485382253986576,
    decodeIntegerRow 64 9 4 5902191587298176375044063661201743535212468961907831840532336,
    decodeIntegerRow 64 9 4 5312859734396156376287126513765471856581459301104188665894384,
    decodeIntegerRow 64 9 4 655000407705535375129596534626781336377224914177539926401136,
    decodeIntegerRow 64 9 4 5887815504935968114611652896725724294000256950715404256305904,
    decodeIntegerRow 64 9 4 5829601246992886489429354470737195328017182247776879022463856,
    decodeIntegerRow 64 9 4 5887992990440406788622840842469576128985386531250250443896464,
    decodeIntegerRow 64 9 4 5831198589147734613913892078930682488250520578187820754287344,
    decodeIntegerRow 64 9 4 5312862168998333484236716520962412085504484493223639036227984,
    decodeIntegerRow 64 9 4 655020100932034075767425639426454041159345509518591528496624,
    decodeIntegerRow 64 9 4 5831198589485822338199821149936761686194936145746938084492944,
    decodeIntegerRow 64 9 4 5887992987397617914075015903791031816004237940381592385089296,
    decodeIntegerRow 64 9 4 11135164449755357230357073034450279291274581905854141138090096,
    decodeIntegerRow 64 9 4 6477322652200924945857655446322201190866215274686574658895344,
    decodeIntegerRow 64 9 4 11135184197084137858799307867808799510859957715440224821294096,
    decodeIntegerRow 64 9 4 6477324599882667763361405876197838712181381199797167508680816,
    decodeIntegerRow 64 9 4 5829601246663044807199179767316621984145682746659654780588784,
    decodeIntegerRow 64 9 4 5887815507904542626365628446656085882971955858659790331399824,
    decodeIntegerRow 64 9 4 11135184197084137858799307867808460380884721069840378009016464,
    decodeIntegerRow 64 9 4 5312859977855915408159466985211627784365709078331257023253744,
    decodeIntegerRow 64 9 4 5960583331075538364321693094095892443061944967821423056515984,
    decodeIntegerRow 64 9 4 5887815507904542626365628446656047736744577924967307392983024,
    decodeIntegerRow 64 9 4 5958985988252760833321051711475752844391752500182497860679664,
    decodeIntegerRow 64 9 4 5887992987397617914075015903790994600172457532642049728802416,
    decodeIntegerRow 64 9 4 11135164449755357230357073034449940162717415359032665821881584,
    decodeIntegerRow 64 9 4 5312861925537658225663217415087265317151486468782295400122736,
    decodeIntegerRow 64 9 4 5902191587298176382898032018942905320861241577488729621967376,
    decodeIntegerRow 64 9 4 5831198589147734613913892078930678353157225314392403285876336,
    decodeIntegerRow 64 9 4 5312862168998333484236716520965464243149237974653084972709104,
    decodeIntegerRow 64 9 4 11135164476806549095753447221986403753217839905962042740981904,
    decodeIntegerRow 64 9 4 5312859734396156376287126513768524025728336923332471915939984,
    decodeIntegerRow 64 9 4 11135184170033047796391276326786076459134416580984643162635536,
    decodeIntegerRow 64 9 4 5902369072802615056909219964686756225450384586694605999199856,
    decodeIntegerRow 64 9 4 5829601246992886489429354470737191089548327460176274096312304,
    decodeIntegerRow 64 9 4 655020100932039731498474594357374575286348974294342255017104,
    decodeIntegerRow 64 9 4 6477322408740249058869728352878417998810688865540355214987504,
    decodeIntegerRow 64 9 4 5831198589147734684599621894779016564124944900590450985588624,
    decodeIntegerRow 64 9 4 5902191587298176375044063661201780751044052445485864833868784,
    decodeIntegerRow 64 9 4 5960583330745696751053205659780333844949868513611915748858864,
    decodeIntegerRow 64 9 4 5887815504935968106949241537816020353728012870621355114556016,
    decodeIntegerRow 64 9 4 11135184170033053452101011613475181809300436415772686243743984,
    decodeIntegerRow 64 9 4 5312859734396155747874800696212120639461138695470826402465136,
    decodeIntegerRow 64 9 4 5887815507904542634028036521425767272111219012763561484815344,
    decodeIntegerRow 64 9 4 5960583331075538295360005460086439224117802906948757334245264,
    decodeIntegerRow 64 9 4 6477324599882667134949342830391230135713522092145094947406096,
    decodeIntegerRow 64 9 4 655000380654450968431329477153912817112421558730144649090416,
    decodeIntegerRow 64 9 4 5312861925537657597248526656760787193040740175089074200849776,
    decodeIntegerRow 64 9 4 11135164449755362886088092792630328525356227825186742376669424,
    decodeIntegerRow 64 9 4 5902191590340965265299828519401695026671995951407288695433104,
    decodeIntegerRow 64 9 4 5831198589485822267514091690092766098248206232674676090979856]

def cols_right0 (r : LeftIndex 5 3 3) : List ℤ := cols_right0Data.getD (leftPosition 5 3 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 3 3) : (tripleIndices 4 2 8).map (fun j => (right0Middle5 3 3) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 2897554982954507054731842505336,
    decodeIntegerRow 64 3 1 1222970223449979722641381551680,
    decodeIntegerRow 64 3 1 1449067880720130889938550628160,
    decodeIntegerRow 64 3 1 2822227385089355910184213181032,
    decodeIntegerRow 64 3 1 1193661775176433885492181119040,
    decodeIntegerRow 64 3 1 2910111233441095383976830271816,
    decodeIntegerRow 64 3 1 617732088666983396577370964008,
    decodeIntegerRow 64 3 1 1957399960069170525083945800640,
    decodeIntegerRow 64 3 1 617732140024461086764009046632,
    decodeIntegerRow 64 3 1 1957399947628083115165384520000,
    decodeIntegerRow 64 3 1 1193661798122280389280100963520,
    decodeIntegerRow 64 3 1 2910111178583811873083718763144,
    decodeIntegerRow 64 3 1 1984615950748985231280655225280,
    decodeIntegerRow 64 3 1 611456384137255865695711776808,
    decodeIntegerRow 64 3 1 536128781897345593374390823864,
    decodeIntegerRow 64 3 1 2210713621150079707418858070720,
    decodeIntegerRow 64 3 1 2910037848311567701821323448640,
    decodeIntegerRow 64 3 1 1193326756107685137995083510568,
    decodeIntegerRow 64 3 1 1475920125234549400854492316344,
    decodeIntegerRow 64 3 1 2815792198735876551736359807040,
    decodeIntegerRow 64 3 1 2211050530290305498826236685672,
    decodeIntegerRow 64 3 1 536210518174010803943277622720,
    decodeIntegerRow 64 3 1 2822076786048532555428114556480,
    decodeIntegerRow 64 3 1 1448707974537416627031130604424,
    decodeIntegerRow 64 3 1 611606983185490781536870640320,
    decodeIntegerRow 64 3 1 1984975856948596665902297598536,
    decodeIntegerRow 64 3 1 1222633265679092095085493699368,
    decodeIntegerRow 64 3 1 2897473357555750830400553915200,
    decodeIntegerRow 64 3 1 1475920137692360850921976801656,
    decodeIntegerRow 64 3 1 2815792147385396444198516989120,
    decodeIntegerRow 64 3 1 2910037793458078109821050758080,
    decodeIntegerRow 64 3 1 1193326779069183407694286503272,
    decodeIntegerRow 64 3 1 1984975845755094671508730994880,
    decodeIntegerRow 64 3 1 2822076786048532815459587889736,
    decodeIntegerRow 64 3 1 2897473302118501115674689884968,
    decodeIntegerRow 64 3 1 2211050530290306786665349657920,
    decodeIntegerRow 64 3 1 2815792198735876841138425928056,
    decodeIntegerRow 64 3 1 1957763695057961890902294440640,
    decodeIntegerRow 64 3 1 1193326756107683863717124667840,
    decodeIntegerRow 64 3 1 523645971980945316245306740072,
    decodeIntegerRow 64 3 1 2240357041223327802685543908800,
    decodeIntegerRow 64 3 1 2910037793458078643229858109912,
    decodeIntegerRow 64 3 1 617891672907116329861410302536,
    decodeIntegerRow 64 3 1 1475920137692359658020859360960,
    decodeIntegerRow 64 3 1 2897473357555751395440410714008,
    decodeIntegerRow 64 3 1 2211050554613419101733301622080,
    decodeIntegerRow 64 3 1 1984975856948597852020229664960,
    decodeIntegerRow 64 3 1 2822076837107021443089518561656,
    decodeIntegerRow 64 3 1 1957399960069171718147552547432,
    decodeIntegerRow 64 3 1 2815951731625528799066865605440,
    decodeIntegerRow 64 3 1 2910111233441095917021952680640,
    decodeIntegerRow 64 3 1 2240022045116077324799549444744,
    decodeIntegerRow 64 3 1 611456435203156834112523136960,
    decodeIntegerRow 64 3 1 1449067880720129703648376250408,
    decodeIntegerRow 64 3 1 2210713596842531474098148596664,
    decodeIntegerRow 64 3 1 2897554982954507619410131622080,
    decodeIntegerRow 64 3 1 2210713621150080995337117803144,
    decodeIntegerRow 64 3 1 2897555038395166326605193914560,
    decodeIntegerRow 64 3 1 611456384137255606056837976000,
    decodeIntegerRow 64 3 1 1449067869543528439667312810648,
    decodeIntegerRow 64 3 1 523572641708701144619278970560,
    decodeIntegerRow 64 3 1 1193661798122279114913922599864,
    decodeIntegerRow 64 3 1 1476283872664430562556126432472,
    decodeIntegerRow 64 3 1 617732140024460797750384463680]

def cols_left0 (r : LeftIndex 5 3 3) : List ℤ := cols_left0Data.getD (leftPosition 5 3 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 3 3) : (tripleIndices 4 2 8).map (fun j => (left0Middle5 3 3) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 64 65 32 53140401267381025575805604793511912808582216994433976792305508671475547609066282636080105861508813322642447586445312,
    decodeIntegerRow 64 65 32 53140401266697935580962866142272076021016103353834878642902826346449116103362866072745076195607836307512428514445312,
    decodeIntegerRow 64 65 32 53140401222297085916773433302167210624199526971217574477558288854789211914271937176129456923371432248762613423245312,
    decodeIntegerRow 64 65 32 53140398336241857744469641124879449317964803628778260366393472469386030115315796395571369662815926412009841347725312,
    decodeIntegerRow 64 65 32 53140210742652190749048691498283823139934064507757410588130939396883826759087217645208434950262114107076593110157312,
    decodeIntegerRow 64 65 32 53128017159313001087412401242992911103654908437690561037776642304381801938525781794407735954911839996598748294080512,
    decodeIntegerRow 64 65 32 52335434242276179592811805496822932207381553329934401319813998543558116590029638673404911660299499220446959418943232,
    decodeIntegerRow 64 65 32 817544634882949212586165432458974568794287662331685143446407046394490155235417368878334844128765024985876293945344,
    decodeIntegerRow 64 65 32 53140404198541539969461723405417731051146426318683486036075079201162806675081960550579042479887738906164139365165312,
    decodeIntegerRow 64 65 32 53140401312486311797157931229144755479657521831661239273918274847318742801147184864424076569802050933122304789645312,
    decodeIntegerRow 64 65 32 53140401266697935580962866142272079773921923883504582286834434107889289699358918015304540740084896307512428514445312,
    decodeIntegerRow 64 65 32 53140401267381025575805604793512156747460761612667428857422334681781540542786041839674479502611382291392447586445312,
    decodeIntegerRow 64 65 32 105463257899900448501345199097822349772323277131301545374612829868471666039254899423887910404812136996899041918945280,
    decodeIntegerRow 64 65 32 53945368292507218121119559033458392076887260523839924794771896000845644058295502845685910560832307855148896293947392,
    decodeIntegerRow 64 65 32 53128017159313001087412401242992911103654698198227207252141481373523623070574611235673741308681273590348748294080512,
    decodeIntegerRow 64 65 32 53140210742652190749048691498283823139920398942627639600647194585130046602521451387354622093909614107076593110157312,
    decodeIntegerRow 64 65 32 53152785375470401678959753477239385404093071881969337884241889656741093710814945562986079912466311584733513918810112,
    decodeIntegerRow 64 65 32 53140591792131535373534035378810691975311758537762133918064121540243061151862574447213640756207339784566827502733312,
    decodeIntegerRow 64 65 32 817544634882949213782009406468430420194463320034073719865221226171884978845238166286886668275634158764276293945344,
    decodeIntegerRow 64 65 32 52335434242276179670541663807437562548392971080589656000093624309151691152896772966517132772252843896408661918943232,
    decodeIntegerRow 64 65 32 53140401266697935580962583102278227629098608953545450912178887981096207440893972065271944239204130012463366014445312,
    decodeIntegerRow 64 65 32 53140401267381025575787207193911767333945291165323889504811836440231193742564671112103994365585366502046447586445312,
    decodeIntegerRow 64 65 32 53140404198541539969461723338410160503711574972152660166474932948571838850670640060994678230747745848875076865165312,
    decodeIntegerRow 64 65 32 53140401312486311797157926873652669896392184307157557749908768428905834214411353068908331669768484786272304789645312,
    decodeIntegerRow 64 65 32 53945368292507218043389700722843761735875842773184670115832156580073315628282897652855140222356517500476256293947392,
    decodeIntegerRow 64 65 32 105463257899900448500149355123812893920923101473599156883966730737689585432205031921512723898963607706870641918945280,
    decodeIntegerRow 64 65 32 53140591792131535373534035378810691975325424102891910480794650649990506683578911624132521378224894105855890002733312,
    decodeIntegerRow 64 65 32 53152785375470401678959753477239385404093282121433054060917717555444472097418554987997228218059670959733513918810112,
    decodeIntegerRow 64 65 32 53140401222297085916773437655598012683762419944124235802077019359137561623304628492815073658189574356862613423245312,
    decodeIntegerRow 64 65 32 53140398336241857744469641191855307811188848136053747463693760630991389341608607030790303277200165948009841347725312,
    decodeIntegerRow 64 65 32 53140401267381025575787207193912011272823835883078981113115008246709594787277504312884687332647408127046447586445312,
    decodeIntegerRow 64 65 32 53140401266697935580962583102278231382004435952121724863222972493760409136873809729688966438908744333752428514445312,
    decodeIntegerRow 64 65 32 53140401268085462132968781428003092960001390574946801079686524394393241073822220078521573708195853708752428514445312,
    decodeIntegerRow 64 65 32 53140401267381025575787207193912011272823835883078981113115008246709729377617448546895292948371243894838470626445312,
    decodeIntegerRow 64 65 32 53140404198541539969461723338426016530816978391014778479215736257171007170563179892291281747048798760509841347725312,
    decodeIntegerRow 64 65 32 53140401222297085916773437655598012683762419944124235802077019359706205809568901190523952414455054227522304789645312,
    decodeIntegerRow 64 65 32 53152785375470401678959753477239385404093282121433054060917717592406344236451982101439011033458019758440466794080512,
    decodeIntegerRow 64 65 32 53140210742651862340397329151470632366680402424176615462114848640684828423538737440128327684825464784566827502733312,
    decodeIntegerRow 64 65 32 105463257899900448500149355123812893920923101473599156883966886901599238258087102195421531322545766971264276293945344,
    decodeIntegerRow 64 65 32 52335434242276179670541663807437562606129983753883855827087490962207766194617055370923658479497630781726256293947392,
    decodeIntegerRow 64 65 32 53140401312486311797157926873652669896392184307157557749908768429474478400675625766617207349958663329362613423245312,
    decodeIntegerRow 64 65 32 53140398336241857744469641191871163838294251554915865776434563939590557661501146862086706848606632567625076865165312,
    decodeIntegerRow 64 65 32 53140401267381025575787207193911767333945291165323889504811836440231059152224726878093388749133465573549408126445312,
    decodeIntegerRow 64 65 32 53140401268085462132968781428003096712907217573523075030730608907057438628560825121287856682603559333752428514445312,
    decodeIntegerRow 64 65 32 53945368292507218043389700722843761793612855446478869942826023233129390670003180057261665929601476708908661918943232,
    decodeIntegerRow 64 65 32 817544634882949213782009406468430420194463320034073719865377390081537804727308440195694091868994425620641918945280,
    decodeIntegerRow 64 65 32 53140210742651862340397329151470632366694067989306392024845372945388900021170603483295851296978824159566827502733312,
    decodeIntegerRow 64 65 32 53152785375470401678959753477239385404093071881969337884241889619779221571781518449544297097067965437151404294080512,
    decodeIntegerRow 64 65 32 53140591792131206964882673031997501202085427584440886342262304705545288503616022238077230660193793794576593110157312,
    decodeIntegerRow 64 65 32 53128017159313001087412401242992911103654698198227207252141481410485495145896634825230764042527808119036169918810112,
    decodeIntegerRow 64 65 32 52335434242276179592811805496822932265118566003228601148127450233180570398955139131118926765666292230148896293947392,
    decodeIntegerRow 64 65 32 105463257899900448501345199097822349772323277131301545374612673704562013213357749527843272268784640024985876293945344,
    decodeIntegerRow 64 65 32 53140401267381025575805604793512156747460761612667428857422334681781405952446097660573740562647992386742470626445312,
    decodeIntegerRow 64 65 32 53140401268085462132968498388009244568083902643563943656075062780264356370095882740396594153476009588762428514445312,
    decodeIntegerRow 64 65 32 53140401312486311797157931229144755479657521831661239273918274847887386987411457562145951744215639785051675923245312,
    decodeIntegerRow 64 65 32 53140398336241857744469641124863593290859400208385039906834417686999589837089826373347309723988309584875076865165312,
    decodeIntegerRow 64 65 32 817544634882949212586165432458974568794287662331685143446250882484837329338267472833696708090067050609979418945280,
    decodeIntegerRow 64 65 32 53945368292507218121119559033458392134624273197134124623085347690468097867221003303399925666198928541736021918943232,
    decodeIntegerRow 64 65 32 53128017159313001087412401242992911103654908437690561037776642267419929863203758204850713221065308119036169918810112,
    decodeIntegerRow 64 65 32 53140591792131206964882673031997501202071762019311115354778555088748134414926135724130053411871000825826593110157312,
    decodeIntegerRow 64 65 32 53140404198541539969461723405401875024041022898290265576516024418776366396855990528354782596165535787009841347725312,
    decodeIntegerRow 64 65 32 53140401222297085916773433302167210624199526971217574477558288855357856100536209873851329021709719773122304789645312,
    decodeIntegerRow 64 65 32 53140401268085462132968498388009248320989723173233647300006670541704534107333160166324130074392015995012428514445312,
    decodeIntegerRow 64 65 32 53140401267381025575805604793511912808582216994433976792305508671475682199406226815180844802200268386742470626445312]

def cols_right2 (r : LeftIndex 5 3 3) : List ℤ := cols_right2Data.getD (leftPosition 5 3 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 3 3) : (tripleIndices 8 1 8).map (fun j => (right2Middle5 3 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms533.outerABC * HexagonAtoms533.assocABC = HexagonAtoms533.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms533.assocBAC * HexagonAtoms533.innerABC = HexagonAtoms533.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms533.innerRightABC * HexagonAtoms533.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms533.inverseACB * right0Middle5 3 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms533.innerABC * right1Middle5 3 3 = right1Middle5 3 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms533.assocBCA * left0Middle5 3 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms533.innerRightBAC * left1Middle5 3 3 = left1Middle5 3 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms533.assocBAC * right2Middle5 3 3 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn533

import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1716841913114126877389940976168,
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

def assocABC : Matrix (RightIndex 3 5 5) (LeftIndex 3 5 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 5 5 r) []).getD (leftPosition 3 5 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_4 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_5 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_6 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_7 : (associatorZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_4 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_5 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_6 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_7 : (associatorZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_4 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_5 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_6 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_7 : (associatorZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_2 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_3 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_4 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_5 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_6 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_7 : (associatorZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_4 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_5 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_6 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_7 : (associatorZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_2 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_3 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_4 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_5 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_6 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_7 : (associatorZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = assocABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 5 5 = assocABC := by
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
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_1_2
  · exact assocABC_row_0_1_3
  · exact assocABC_row_0_1_4
  · exact assocABC_row_0_1_5
  · exact assocABC_row_0_1_6
  · exact assocABC_row_0_1_7
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_0_4
  · exact assocABC_row_1_0_5
  · exact assocABC_row_1_0_6
  · exact assocABC_row_1_0_7
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_1_2
  · exact assocABC_row_1_1_3
  · exact assocABC_row_1_1_4
  · exact assocABC_row_1_1_5
  · exact assocABC_row_1_1_6
  · exact assocABC_row_1_1_7
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_0_2
  · exact assocABC_row_2_0_3
  · exact assocABC_row_2_0_4
  · exact assocABC_row_2_0_5
  · exact assocABC_row_2_0_6
  · exact assocABC_row_2_0_7
  · exact assocABC_row_2_1_0
  · exact assocABC_row_2_1_1
  · exact assocABC_row_2_1_2
  · exact assocABC_row_2_1_3
  · exact assocABC_row_2_1_4
  · exact assocABC_row_2_1_5
  · exact assocABC_row_2_1_6
  · exact assocABC_row_2_1_7
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_0_2
  · exact assocABC_row_3_0_3
  · exact assocABC_row_3_0_4
  · exact assocABC_row_3_0_5
  · exact assocABC_row_3_0_6
  · exact assocABC_row_3_0_7
  · exact assocABC_row_3_1_0
  · exact assocABC_row_3_1_1
  · exact assocABC_row_3_1_2
  · exact assocABC_row_3_1_3
  · exact assocABC_row_3_1_4
  · exact assocABC_row_3_1_5
  · exact assocABC_row_3_1_6
  · exact assocABC_row_3_1_7

def outerABC : Matrix (LeftIndex 5 5 3) (RightIndex 3 5 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 8) (Fin 4 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_4 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_5 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_6 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_7 : (outerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_4 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_5 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_6 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_7 : (outerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_4 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_5 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_6 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_7 : (outerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_4 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_5 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_6 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_7 : (outerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 5 5 = outerABC := by
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
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_0_1_4
  · exact outerABC_row_0_1_5
  · exact outerABC_row_0_1_6
  · exact outerABC_row_0_1_7
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_1_1_4
  · exact outerABC_row_1_1_5
  · exact outerABC_row_1_1_6
  · exact outerABC_row_1_1_7
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_0_4
  · exact outerABC_row_2_0_5
  · exact outerABC_row_2_0_6
  · exact outerABC_row_2_0_7
  · exact outerABC_row_2_1_0
  · exact outerABC_row_2_1_1
  · exact outerABC_row_2_1_2
  · exact outerABC_row_2_1_3
  · exact outerABC_row_2_1_4
  · exact outerABC_row_2_1_5
  · exact outerABC_row_2_1_6
  · exact outerABC_row_2_1_7
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_0_4
  · exact outerABC_row_3_0_5
  · exact outerABC_row_3_0_6
  · exact outerABC_row_3_0_7
  · exact outerABC_row_3_1_0
  · exact outerABC_row_3_1_1
  · exact outerABC_row_3_1_2
  · exact outerABC_row_3_1_3
  · exact outerABC_row_3_1_4
  · exact outerABC_row_3_1_5
  · exact outerABC_row_3_1_6
  · exact outerABC_row_3_1_7

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1717363107038282381294630733760,
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

def assocBAC : Matrix (RightIndex 5 3 5) (LeftIndex 5 3 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 5 3 5 r) []).getD (leftPosition 5 3 5 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_4 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_5 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_6 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_7 : (associatorZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_4 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_5 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_6 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_7 : (associatorZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_4 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_5 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_6 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_7 : (associatorZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_4 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_5 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_6 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_7 : (associatorZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_0 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_1 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_2 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_3 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_4 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_5 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_6 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_4_0_7 : (associatorZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_0 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_1 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_2 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_3 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_4 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_5 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_6 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_5_0_7 : (associatorZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_0 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_1 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_2 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_3 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_4 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_5 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_6 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_6_0_7 : (associatorZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_0 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_1 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_2 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_3 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_4 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_5 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_6 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_7_0_7 : (associatorZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 5 3 5 = assocBAC := by
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

def innerABC : Matrix (LeftIndex 5 3 5) (LeftIndex 3 5 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_0 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_1 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_2 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_3 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_4 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_5 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_6 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_7 : (innerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_0 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_1 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_2 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_3 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_4 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_5 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_6 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_7 : (innerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_0 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_1 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_2 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_3 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_4 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_5 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_6 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_7 : (innerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_0 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_1 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_2 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_3 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_4 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_5 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_6 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_7 : (innerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 5 5 = innerABC := by
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
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_0_4
  · exact innerABC_row_1_0_5
  · exact innerABC_row_1_0_6
  · exact innerABC_row_1_0_7
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_0_4
  · exact innerABC_row_2_0_5
  · exact innerABC_row_2_0_6
  · exact innerABC_row_2_0_7
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_0_4
  · exact innerABC_row_3_0_5
  · exact innerABC_row_3_0_6
  · exact innerABC_row_3_0_7
  · exact innerABC_row_4_0_0
  · exact innerABC_row_4_0_1
  · exact innerABC_row_4_0_2
  · exact innerABC_row_4_0_3
  · exact innerABC_row_4_0_4
  · exact innerABC_row_4_0_5
  · exact innerABC_row_4_0_6
  · exact innerABC_row_4_0_7
  · exact innerABC_row_5_0_0
  · exact innerABC_row_5_0_1
  · exact innerABC_row_5_0_2
  · exact innerABC_row_5_0_3
  · exact innerABC_row_5_0_4
  · exact innerABC_row_5_0_5
  · exact innerABC_row_5_0_6
  · exact innerABC_row_5_0_7
  · exact innerABC_row_6_0_0
  · exact innerABC_row_6_0_1
  · exact innerABC_row_6_0_2
  · exact innerABC_row_6_0_3
  · exact innerABC_row_6_0_4
  · exact innerABC_row_6_0_5
  · exact innerABC_row_6_0_6
  · exact innerABC_row_6_0_7
  · exact innerABC_row_7_0_0
  · exact innerABC_row_7_0_1
  · exact innerABC_row_7_0_2
  · exact innerABC_row_7_0_3
  · exact innerABC_row_7_0_4
  · exact innerABC_row_7_0_5
  · exact innerABC_row_7_0_6
  · exact innerABC_row_7_0_7

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1716844143606710847805623514792,
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

def innerRightABC : Matrix (RightIndex 3 5 5) (RightIndex 3 5 5) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 3 5 5 r) []).getD (rightPosition 3 5 5 s) 0

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 3 5 5) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_4 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_5 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_6 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_7 : (innerRightZ 3 5 5) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 3 5 5) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_4 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_5 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_6 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_7 : (innerRightZ 3 5 5) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_4 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_5 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_6 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_7 : (innerRightZ 3 5 5) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_2 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_3 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_4 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_5 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_6 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_7 : (innerRightZ 3 5 5) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_4 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_5 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_6 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_7 : (innerRightZ 3 5 5) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_2 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_3 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_4 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_5 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_6 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_7 : (innerRightZ 3 5 5) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 5 5 = innerRightABC := by
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
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_1_2
  · exact innerRightABC_row_0_1_3
  · exact innerRightABC_row_0_1_4
  · exact innerRightABC_row_0_1_5
  · exact innerRightABC_row_0_1_6
  · exact innerRightABC_row_0_1_7
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_0_4
  · exact innerRightABC_row_1_0_5
  · exact innerRightABC_row_1_0_6
  · exact innerRightABC_row_1_0_7
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_1_2
  · exact innerRightABC_row_1_1_3
  · exact innerRightABC_row_1_1_4
  · exact innerRightABC_row_1_1_5
  · exact innerRightABC_row_1_1_6
  · exact innerRightABC_row_1_1_7
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_0_2
  · exact innerRightABC_row_2_0_3
  · exact innerRightABC_row_2_0_4
  · exact innerRightABC_row_2_0_5
  · exact innerRightABC_row_2_0_6
  · exact innerRightABC_row_2_0_7
  · exact innerRightABC_row_2_1_0
  · exact innerRightABC_row_2_1_1
  · exact innerRightABC_row_2_1_2
  · exact innerRightABC_row_2_1_3
  · exact innerRightABC_row_2_1_4
  · exact innerRightABC_row_2_1_5
  · exact innerRightABC_row_2_1_6
  · exact innerRightABC_row_2_1_7
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_0_2
  · exact innerRightABC_row_3_0_3
  · exact innerRightABC_row_3_0_4
  · exact innerRightABC_row_3_0_5
  · exact innerRightABC_row_3_0_6
  · exact innerRightABC_row_3_0_7
  · exact innerRightABC_row_3_1_0
  · exact innerRightABC_row_3_1_1
  · exact innerRightABC_row_3_1_2
  · exact innerRightABC_row_3_1_3
  · exact innerRightABC_row_3_1_4
  · exact innerRightABC_row_3_1_5
  · exact innerRightABC_row_3_1_6
  · exact innerRightABC_row_3_1_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1716781607663588032612437301756,
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

def inverseACB : Matrix (LeftIndex 3 5 5) (RightIndex 3 5 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 5 5 r) []).getD (rightPosition 3 5 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_4 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_5 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_6 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_7 : (associatorInverseZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_4 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_5 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_6 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_7 : (associatorInverseZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_4 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_5 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_6 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_7 : (associatorInverseZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_4 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_5 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_6 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_7 : (associatorInverseZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 5 5 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 5 3 5) (LeftIndex 3 5 5) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 3 5 5 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 64 3 1 1702369074897160498975970756200,
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

def assocBCA : Matrix (RightIndex 5 5 3) (LeftIndex 5 5 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 5 3 r) []).getD (leftPosition 5 5 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_4 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_5 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_6 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_7 : (associatorZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_4 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_5 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_6 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_7 : (associatorZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_0 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_1 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_2 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_3 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_4 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_5 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_6 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_4_0_7 : (associatorZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_0 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_1 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_2 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_3 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_4 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_5 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_6 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_5_0_7 : (associatorZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_0 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_1 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_2 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_3 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_4 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_5 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_6 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_6_0_7 : (associatorZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_0 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_1 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_2 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_3 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_4 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_5 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_6 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_7_0_7 : (associatorZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 5 5 3 = assocBCA := by
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

def innerRightBAC : Matrix (RightIndex 5 5 3) (RightIndex 5 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_0 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_1 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_2 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_3 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_4 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_5 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_6 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_4_0_7 : (innerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_0 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_1 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_2 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_3 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_4 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_5 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_6 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_5_0_7 : (innerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_0 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_1 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_2 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_3 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_4 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_5 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_6 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_6_0_7 : (innerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_0 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_1 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_2 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_3 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_4 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_5 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_6 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_7_0_7 : (innerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 5 3 5 = innerRightBAC := by
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

def assocCAB : Matrix (RightIndex 5 3 5) (LeftIndex 5 3 5) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 5 3 5 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 5 3 5) (LeftIndex 3 5 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 3 5 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 3 5 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 3 5 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 3 5 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_0 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_1 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_2 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_3 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_4 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_5 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_6 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_7 : (outerLeftZ 3 5 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_0 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_1 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_2 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_3 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_4 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_5 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_6 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_7 : (outerLeftZ 3 5 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_0 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_1 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_2 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_3 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_4 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_5 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_6 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_7 : (outerLeftZ 3 5 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_0 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_1 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_2 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_3 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_4 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_5 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_6 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_7 : (outerLeftZ 3 5 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 5 5 = outerLeftABC := by
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
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_0_4
  · exact outerLeftABC_row_1_0_5
  · exact outerLeftABC_row_1_0_6
  · exact outerLeftABC_row_1_0_7
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_0_4
  · exact outerLeftABC_row_2_0_5
  · exact outerLeftABC_row_2_0_6
  · exact outerLeftABC_row_2_0_7
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_0_4
  · exact outerLeftABC_row_3_0_5
  · exact outerLeftABC_row_3_0_6
  · exact outerLeftABC_row_3_0_7
  · exact outerLeftABC_row_4_0_0
  · exact outerLeftABC_row_4_0_1
  · exact outerLeftABC_row_4_0_2
  · exact outerLeftABC_row_4_0_3
  · exact outerLeftABC_row_4_0_4
  · exact outerLeftABC_row_4_0_5
  · exact outerLeftABC_row_4_0_6
  · exact outerLeftABC_row_4_0_7
  · exact outerLeftABC_row_5_0_0
  · exact outerLeftABC_row_5_0_1
  · exact outerLeftABC_row_5_0_2
  · exact outerLeftABC_row_5_0_3
  · exact outerLeftABC_row_5_0_4
  · exact outerLeftABC_row_5_0_5
  · exact outerLeftABC_row_5_0_6
  · exact outerLeftABC_row_5_0_7
  · exact outerLeftABC_row_6_0_0
  · exact outerLeftABC_row_6_0_1
  · exact outerLeftABC_row_6_0_2
  · exact outerLeftABC_row_6_0_3
  · exact outerLeftABC_row_6_0_4
  · exact outerLeftABC_row_6_0_5
  · exact outerLeftABC_row_6_0_6
  · exact outerLeftABC_row_6_0_7
  · exact outerLeftABC_row_7_0_0
  · exact outerLeftABC_row_7_0_1
  · exact outerLeftABC_row_7_0_2
  · exact outerLeftABC_row_7_0_3
  · exact outerLeftABC_row_7_0_4
  · exact outerLeftABC_row_7_0_5
  · exact outerLeftABC_row_7_0_6
  · exact outerLeftABC_row_7_0_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355

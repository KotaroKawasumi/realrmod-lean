import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 6, 1.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle6

private def rows0_1_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows1_1_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows2_1_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows3_1_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows4_1_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows0_1_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 52,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 14]

private def rows1_1_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 66,
    decodeIntegerRow 4 3 1 28]

private def rows2_1_1 : List (List ℤ) := [decodeIntegerRow 4 5 2 314,
    decodeIntegerRow 4 5 2 562,
    decodeIntegerRow 4 5 2 322,
    decodeIntegerRow 4 5 2 362]

private def rows3_1_1 : List (List ℤ) := [decodeIntegerRow 4 5 2 352,
    decodeIntegerRow 4 5 2 564,
    decodeIntegerRow 4 5 2 560,
    decodeIntegerRow 4 5 2 252]

private def rows4_1_1 : List (List ℤ) := [decodeIntegerRow 4 5 2 352,
    decodeIntegerRow 4 5 2 564,
    decodeIntegerRow 4 5 2 560,
    decodeIntegerRow 4 5 2 252]

private def rows0_1_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 4226,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 3738,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 1018,
    decodeIntegerRow 8 3 1 3794,
    decodeIntegerRow 8 3 1 1186,
    decodeIntegerRow 8 3 1 4278]

private def rows1_1_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 4226,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 3738,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 1018,
    decodeIntegerRow 8 3 1 3794,
    decodeIntegerRow 8 3 1 1186,
    decodeIntegerRow 8 3 1 4278]

private def rows2_1_2 : List (List ℤ) := [decodeIntegerRow 8 9 4 21523364,
    decodeIntegerRow 8 9 4 21523396,
    decodeIntegerRow 8 9 4 23649124,
    decodeIntegerRow 8 9 4 40655236,
    decodeIntegerRow 8 9 4 21523684,
    decodeIntegerRow 8 9 4 21526276,
    decodeIntegerRow 8 9 4 21549604,
    decodeIntegerRow 8 9 4 21759556]

private def rows3_1_2 : List (List ℤ) := [decodeIntegerRow 8 9 4 23882408,
    decodeIntegerRow 8 9 4 40629352,
    decodeIntegerRow 8 9 4 23410008,
    decodeIntegerRow 8 9 4 40681768,
    decodeIntegerRow 8 9 4 2365528,
    decodeIntegerRow 8 9 4 23415848,
    decodeIntegerRow 8 9 4 2418088,
    decodeIntegerRow 8 9 4 23888232]

private def rows4_1_2 : List (List ℤ) := [decodeIntegerRow 8 9 4 23882408,
    decodeIntegerRow 8 9 4 40629352,
    decodeIntegerRow 8 9 4 23410008,
    decodeIntegerRow 8 9 4 40681768,
    decodeIntegerRow 8 9 4 2365528,
    decodeIntegerRow 8 9 4 23415848,
    decodeIntegerRow 8 9 4 2418088,
    decodeIntegerRow 8 9 4 23888232]

private def rows0_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 24897832,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 28068964,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 15314392,
    decodeIntegerRow 16 3 1 6604644,
    decodeIntegerRow 16 3 1 36363396,
    decodeIntegerRow 16 3 1 28073512,
    decodeIntegerRow 16 3 1 24893596,
    decodeIntegerRow 16 3 1 35262552,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 6602648,
    decodeIntegerRow 16 3 1 35419044,
    decodeIntegerRow 16 3 1 18516328]

private def rows1_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 24884692,
    decodeIntegerRow 16 3 1 7745772,
    decodeIntegerRow 16 3 1 6563336,
    decodeIntegerRow 16 3 1 27714664,
    decodeIntegerRow 16 3 1 24543532,
    decodeIntegerRow 16 3 1 7666988,
    decodeIntegerRow 16 3 1 6720744,
    decodeIntegerRow 16 3 1 28082104,
    decodeIntegerRow 16 3 1 7666068,
    decodeIntegerRow 16 3 1 18507412,
    decodeIntegerRow 16 3 1 28086616,
    decodeIntegerRow 16 3 1 36323976,
    decodeIntegerRow 16 3 1 7744748,
    decodeIntegerRow 16 3 1 18166228,
    decodeIntegerRow 16 3 1 27719224,
    decodeIntegerRow 16 3 1 36481496]

private def rows2_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 24897832,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 28068964,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 15314392,
    decodeIntegerRow 16 3 1 6604644,
    decodeIntegerRow 16 3 1 36363396,
    decodeIntegerRow 16 3 1 28073512,
    decodeIntegerRow 16 3 1 24893596,
    decodeIntegerRow 16 3 1 35262552,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 6602648,
    decodeIntegerRow 16 3 1 35419044,
    decodeIntegerRow 16 3 1 18516328]

private def rows3_1_3 : List (List ℤ) := [decodeIntegerRow 16 5 2 75786101564,
    decodeIntegerRow 16 5 2 73950351572,
    decodeIntegerRow 16 5 2 64087696612,
    decodeIntegerRow 16 5 2 15254876812,
    decodeIntegerRow 16 5 2 75825164060,
    decodeIntegerRow 16 5 2 73755039052,
    decodeIntegerRow 16 5 2 64086134012,
    decodeIntegerRow 16 5 2 15262688812,
    decodeIntegerRow 16 5 2 64086131612,
    decodeIntegerRow 16 5 2 137325188812,
    decodeIntegerRow 16 5 2 76762664060,
    decodeIntegerRow 16 5 2 73754726572,
    decodeIntegerRow 16 5 2 64087694012,
    decodeIntegerRow 16 5 2 137333001812,
    decodeIntegerRow 16 5 2 76801726564,
    decodeIntegerRow 16 5 2 73950039052]

private def rows4_1_3 : List (List ℤ) := [decodeIntegerRow 16 5 2 75786101564,
    decodeIntegerRow 16 5 2 73950351572,
    decodeIntegerRow 16 5 2 64087696612,
    decodeIntegerRow 16 5 2 15254876812,
    decodeIntegerRow 16 5 2 75825164060,
    decodeIntegerRow 16 5 2 73755039052,
    decodeIntegerRow 16 5 2 64086134012,
    decodeIntegerRow 16 5 2 15262688812,
    decodeIntegerRow 16 5 2 64086131612,
    decodeIntegerRow 16 5 2 137325188812,
    decodeIntegerRow 16 5 2 76762664060,
    decodeIntegerRow 16 5 2 73754726572,
    decodeIntegerRow 16 5 2 64087694012,
    decodeIntegerRow 16 5 2 137333001812,
    decodeIntegerRow 16 5 2 76801726564,
    decodeIntegerRow 16 5 2 73950039052]

private def rows0_1_4 : List (List ℤ) := [decodeIntegerRow 16 3 1 21563698,
    decodeIntegerRow 16 3 1 21355042,
    decodeIntegerRow 16 3 1 21337546,
    decodeIntegerRow 16 3 1 21601606,
    decodeIntegerRow 16 3 1 24711994,
    decodeIntegerRow 16 3 1 7705866,
    decodeIntegerRow 16 3 1 6643038,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21350506,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 18334702,
    decodeIntegerRow 16 3 1 7705922]

private def rows1_1_4 : List (List ℤ) := [decodeIntegerRow 16 3 1 18162016,
    decodeIntegerRow 16 3 1 7667040,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 15332032,
    decodeIntegerRow 16 3 1 7744800,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 28086640,
    decodeIntegerRow 16 3 1 36481440,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 24880480,
    decodeIntegerRow 16 3 1 15327520,
    decodeIntegerRow 16 3 1 36324032,
    decodeIntegerRow 16 3 1 18503200,
    decodeIntegerRow 16 3 1 35301000,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 14964640]

private def rows2_1_4 : List (List ℤ) := [decodeIntegerRow 16 3 1 21563698,
    decodeIntegerRow 16 3 1 21355042,
    decodeIntegerRow 16 3 1 21337546,
    decodeIntegerRow 16 3 1 21601606,
    decodeIntegerRow 16 3 1 24711994,
    decodeIntegerRow 16 3 1 7705866,
    decodeIntegerRow 16 3 1 6643038,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21350506,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 18334702,
    decodeIntegerRow 16 3 1 7705922]

private def rows3_1_4 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293162812,
    decodeIntegerRow 16 5 2 76290045312,
    decodeIntegerRow 16 5 2 76274445312,
    decodeIntegerRow 16 5 2 76196132812,
    decodeIntegerRow 16 5 2 75805664064,
    decodeIntegerRow 16 5 2 73852539052,
    decodeIntegerRow 16 5 2 64086914012,
    decodeIntegerRow 16 5 2 15258789312,
    decodeIntegerRow 16 5 2 75805664060,
    decodeIntegerRow 16 5 2 78735351552,
    decodeIntegerRow 16 5 2 88500976512,
    decodeIntegerRow 16 5 2 15258788812,
    decodeIntegerRow 16 5 2 76294725312,
    decodeIntegerRow 16 5 2 76290032812,
    decodeIntegerRow 16 5 2 76274382812,
    decodeIntegerRow 16 5 2 76391445312]

private def rows4_1_4 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293162812,
    decodeIntegerRow 16 5 2 76290045312,
    decodeIntegerRow 16 5 2 76274445312,
    decodeIntegerRow 16 5 2 76196132812,
    decodeIntegerRow 16 5 2 75805664064,
    decodeIntegerRow 16 5 2 73852539052,
    decodeIntegerRow 16 5 2 64086914012,
    decodeIntegerRow 16 5 2 15258789312,
    decodeIntegerRow 16 5 2 75805664060,
    decodeIntegerRow 16 5 2 78735351552,
    decodeIntegerRow 16 5 2 88500976512,
    decodeIntegerRow 16 5 2 15258788812,
    decodeIntegerRow 16 5 2 76294725312,
    decodeIntegerRow 16 5 2 76290032812,
    decodeIntegerRow 16 5 2 76274382812,
    decodeIntegerRow 16 5 2 76391445312]

private def rows0_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 31089302,
    decodeIntegerRow 16 3 1 40655238,
    decodeIntegerRow 16 3 1 20460514,
    decodeIntegerRow 16 3 1 19397614,
    decodeIntegerRow 16 3 1 21405586,
    decodeIntegerRow 16 3 1 21287326,
    decodeIntegerRow 16 3 1 21539398,
    decodeIntegerRow 16 3 1 21551062,
    decodeIntegerRow 16 3 1 21498574,
    decodeIntegerRow 16 3 1 21513154,
    decodeIntegerRow 16 3 1 21287002,
    decodeIntegerRow 16 3 1 21404938,
    decodeIntegerRow 16 3 1 19397578,
    decodeIntegerRow 16 3 1 20460442,
    decodeIntegerRow 16 3 1 2391486,
    decodeIntegerRow 16 3 1 11957426]

private def rows1_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 21707068,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21523334,
    decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 15146068,
    decodeIntegerRow 16 3 1 36403708,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21523846,
    decodeIntegerRow 16 3 1 21522388,
    decodeIntegerRow 16 3 1 21521092]

private def rows2_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 2391482,
    decodeIntegerRow 16 3 1 31089302,
    decodeIntegerRow 16 3 1 23649106,
    decodeIntegerRow 16 3 1 20460514,
    decodeIntegerRow 16 3 1 21495658,
    decodeIntegerRow 16 3 1 21507322,
    decodeIntegerRow 16 3 1 21287326,
    decodeIntegerRow 16 3 1 21405586,
    decodeIntegerRow 16 3 1 21533566,
    decodeIntegerRow 16 3 1 21498574,
    decodeIntegerRow 16 3 1 21641782,
    decodeIntegerRow 16 3 1 21287002,
    decodeIntegerRow 16 3 1 31089294,
    decodeIntegerRow 16 3 1 40655234,
    decodeIntegerRow 16 3 1 20460442,
    decodeIntegerRow 16 3 1 19397578]

private def rows3_1_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 926494597606360,
    decodeIntegerRow 16 9 4 926635790851240,
    decodeIntegerRow 16 9 4 926384742374368,
    decodeIntegerRow 16 9 4 926522491881568,
    decodeIntegerRow 16 9 4 926510094423008,
    decodeIntegerRow 16 9 4 926510094425632,
    decodeIntegerRow 16 9 4 926510094426280,
    decodeIntegerRow 16 9 4 926510094428840,
    decodeIntegerRow 16 9 4 1028184727559080,
    decodeIntegerRow 16 9 4 101815847901400,
    decodeIntegerRow 16 9 4 1748944904658592,
    decodeIntegerRow 16 9 4 845170387919392,
    decodeIntegerRow 16 9 4 926510075320288,
    decodeIntegerRow 16 9 4 926510092536352,
    decodeIntegerRow 16 9 4 926510096787880,
    decodeIntegerRow 16 9 4 926510113584040]

private def rows4_1_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 926494597606360,
    decodeIntegerRow 16 9 4 926635790851240,
    decodeIntegerRow 16 9 4 926384742374368,
    decodeIntegerRow 16 9 4 926522491881568,
    decodeIntegerRow 16 9 4 926510094423008,
    decodeIntegerRow 16 9 4 926510094425632,
    decodeIntegerRow 16 9 4 926510094426280,
    decodeIntegerRow 16 9 4 926510094428840,
    decodeIntegerRow 16 9 4 1028184727559080,
    decodeIntegerRow 16 9 4 101815847901400,
    decodeIntegerRow 16 9 4 1748944904658592,
    decodeIntegerRow 16 9 4 845170387919392,
    decodeIntegerRow 16 9 4 926510075320288,
    decodeIntegerRow 16 9 4 926510092536352,
    decodeIntegerRow 16 9 4 926510096787880,
    decodeIntegerRow 16 9 4 926510113584040]

private def rows0_1_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 76309595312,
    decodeIntegerRow 16 5 2 76195665312,
    decodeIntegerRow 16 5 2 76197225312,
    decodeIntegerRow 16 5 2 76270470312,
    decodeIntegerRow 16 5 2 86059570352,
    decodeIntegerRow 16 5 2 14770508064,
    decodeIntegerRow 16 5 2 15747070560,
    decodeIntegerRow 16 5 2 61645507752,
    decodeIntegerRow 16 5 2 86059570272,
    decodeIntegerRow 16 5 2 137817383064,
    decodeIntegerRow 16 5 2 136840820560,
    decodeIntegerRow 16 5 2 61645507872,
    decodeIntegerRow 16 5 2 76309545312,
    decodeIntegerRow 16 5 2 76392540312,
    decodeIntegerRow 16 5 2 76390975312,
    decodeIntegerRow 16 5 2 76270545312]

private def rows1_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 23122048,
    decodeIntegerRow 16 3 1 26483560,
    decodeIntegerRow 16 3 1 7233744,
    decodeIntegerRow 16 3 1 23113300,
    decodeIntegerRow 16 3 1 22073728,
    decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 7115648,
    decodeIntegerRow 16 3 1 26129260,
    decodeIntegerRow 16 3 1 21012304,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 7233260]

private def rows2_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21051698,
    decodeIntegerRow 16 3 1 22942726,
    decodeIntegerRow 16 3 1 26312818,
    decodeIntegerRow 16 3 1 7154554,
    decodeIntegerRow 16 3 1 26299858,
    decodeIntegerRow 16 3 1 7194406,
    decodeIntegerRow 16 3 1 22114578,
    decodeIntegerRow 16 3 1 19754074,
    decodeIntegerRow 16 3 1 26312962,
    decodeIntegerRow 16 3 1 35891734,
    decodeIntegerRow 16 3 1 21050238,
    decodeIntegerRow 16 3 1 20108374,
    decodeIntegerRow 16 3 1 22113122,
    decodeIntegerRow 16 3 1 23297014,
    decodeIntegerRow 16 3 1 26299678,
    decodeIntegerRow 16 3 1 35852854]

private def rows3_1_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 76778351312,
    decodeIntegerRow 16 5 2 73851914112,
    decodeIntegerRow 16 5 2 63989256552,
    decodeIntegerRow 16 5 2 137309564064,
    decodeIntegerRow 16 5 2 73853164112,
    decodeIntegerRow 16 5 2 75801789312,
    decodeIntegerRow 16 5 2 15239251560,
    decodeIntegerRow 16 5 2 64184571552,
    decodeIntegerRow 16 5 2 73853476512,
    decodeIntegerRow 16 5 2 76786164312,
    decodeIntegerRow 16 5 2 137348626560,
    decodeIntegerRow 16 5 2 64184569072,
    decodeIntegerRow 16 5 2 76778289312,
    decodeIntegerRow 16 5 2 78736289112,
    decodeIntegerRow 16 5 2 88598631552,
    decodeIntegerRow 16 5 2 137309576560]

private def rows4_1_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 137309564064,
    decodeIntegerRow 16 5 2 88598634072,
    decodeIntegerRow 16 5 2 73851914112,
    decodeIntegerRow 16 5 2 75809539312,
    decodeIntegerRow 16 5 2 64184571552,
    decodeIntegerRow 16 5 2 137348639064,
    decodeIntegerRow 16 5 2 75801789312,
    decodeIntegerRow 16 5 2 78734726512,
    decodeIntegerRow 16 5 2 78736289112,
    decodeIntegerRow 16 5 2 75809601312,
    decodeIntegerRow 16 5 2 15278314064,
    decodeIntegerRow 16 5 2 88598631552,
    decodeIntegerRow 16 5 2 76786164312,
    decodeIntegerRow 16 5 2 78734414112,
    decodeIntegerRow 16 5 2 88403321552,
    decodeIntegerRow 16 5 2 137348626560]

private def rows0_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3010,
    decodeIntegerRow 8 3 1 2552,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 2550,
    decodeIntegerRow 8 3 1 5464,
    decodeIntegerRow 8 3 1 3190,
    decodeIntegerRow 8 3 1 3496]

private def rows1_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3010,
    decodeIntegerRow 8 3 1 2552,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 2550,
    decodeIntegerRow 8 3 1 5464,
    decodeIntegerRow 8 3 1 3190,
    decodeIntegerRow 8 3 1 3496]

private def rows2_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3010,
    decodeIntegerRow 8 3 1 2552,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 2550,
    decodeIntegerRow 8 3 1 5464,
    decodeIntegerRow 8 3 1 3190,
    decodeIntegerRow 8 3 1 3496]

private def rows3_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3010,
    decodeIntegerRow 8 3 1 2552,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 2550,
    decodeIntegerRow 8 3 1 5464,
    decodeIntegerRow 8 3 1 3190,
    decodeIntegerRow 8 3 1 3496]

private def rows4_1_7 : List (List ℤ) := [decodeIntegerRow 8 5 2 195352,
    decodeIntegerRow 8 5 2 195060,
    decodeIntegerRow 8 5 2 195064,
    decodeIntegerRow 8 5 2 195252,
    decodeIntegerRow 8 5 2 170312,
    decodeIntegerRow 8 5 2 352812,
    decodeIntegerRow 8 5 2 350312,
    decodeIntegerRow 8 5 2 232812]

def rowsB1 : ℕ → ℕ → List (List ℤ)
  | 0, 0 => rows0_1_0
  | 1, 0 => rows1_1_0
  | 2, 0 => rows2_1_0
  | 3, 0 => rows3_1_0
  | 4, 0 => rows4_1_0
  | 0, 1 => rows0_1_1
  | 1, 1 => rows1_1_1
  | 2, 1 => rows2_1_1
  | 3, 1 => rows3_1_1
  | 4, 1 => rows4_1_1
  | 0, 2 => rows0_1_2
  | 1, 2 => rows1_1_2
  | 2, 2 => rows2_1_2
  | 3, 2 => rows3_1_2
  | 4, 2 => rows4_1_2
  | 0, 3 => rows0_1_3
  | 1, 3 => rows1_1_3
  | 2, 3 => rows2_1_3
  | 3, 3 => rows3_1_3
  | 4, 3 => rows4_1_3
  | 0, 4 => rows0_1_4
  | 1, 4 => rows1_1_4
  | 2, 4 => rows2_1_4
  | 3, 4 => rows3_1_4
  | 4, 4 => rows4_1_4
  | 0, 5 => rows0_1_5
  | 1, 5 => rows1_1_5
  | 2, 5 => rows2_1_5
  | 3, 5 => rows3_1_5
  | 4, 5 => rows4_1_5
  | 0, 6 => rows0_1_6
  | 1, 6 => rows1_1_6
  | 2, 6 => rows2_1_6
  | 3, 6 => rows3_1_6
  | 4, 6 => rows4_1_6
  | 0, 7 => rows0_1_7
  | 1, 7 => rows1_1_7
  | 2, 7 => rows2_1_7
  | 3, 7 => rows3_1_7
  | 4, 7 => rows4_1_7
  | _, _ => []

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle6

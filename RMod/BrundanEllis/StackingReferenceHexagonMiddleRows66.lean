import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 6, 6.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle6

private def rows0_6_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3271,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3037,
    decodeIntegerRow 8 3 1 3199]

private def rows1_6_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3271,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3037,
    decodeIntegerRow 8 3 1 3199]

private def rows2_6_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_6_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows4_6_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows0_6_1 : List (List ℤ) := [decodeIntegerRow 16 5 2 15278326564,
    decodeIntegerRow 16 5 2 63989256572,
    decodeIntegerRow 16 5 2 78735976612,
    decodeIntegerRow 16 5 2 76778351812,
    decodeIntegerRow 16 5 2 88403321572,
    decodeIntegerRow 16 5 2 15239264060,
    decodeIntegerRow 16 5 2 76786163812,
    decodeIntegerRow 16 5 2 73853476612,
    decodeIntegerRow 16 5 2 73853164012,
    decodeIntegerRow 16 5 2 76786101812,
    decodeIntegerRow 16 5 2 137348639060,
    decodeIntegerRow 16 5 2 64184571572,
    decodeIntegerRow 16 5 2 76778288812,
    decodeIntegerRow 16 5 2 78736289012,
    decodeIntegerRow 16 5 2 88598631572,
    decodeIntegerRow 16 5 2 137309576564]

private def rows1_6_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21691840,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 6642984,
    decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 27900640,
    decodeIntegerRow 16 3 1 21484480,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21601120]

private def rows2_6_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 36403222]

private def rows3_6_1 : List (List ℤ) := [decodeIntegerRow 16 5 2 15239226812,
    decodeIntegerRow 16 5 2 64184414012,
    decodeIntegerRow 16 5 2 78734571572,
    decodeIntegerRow 16 5 2 76786139060,
    decodeIntegerRow 16 5 2 63989414012,
    decodeIntegerRow 16 5 2 137309538812,
    decodeIntegerRow 16 5 2 75809576564,
    decodeIntegerRow 16 5 2 78736131572,
    decodeIntegerRow 16 5 2 78736134052,
    decodeIntegerRow 16 5 2 75809564060,
    decodeIntegerRow 16 5 2 15278288812,
    decodeIntegerRow 16 5 2 88598789012,
    decodeIntegerRow 16 5 2 76786126564,
    decodeIntegerRow 16 5 2 78734569052,
    decodeIntegerRow 16 5 2 88403164012,
    decodeIntegerRow 16 5 2 137348601812]

private def rows4_6_1 : List (List ℤ) := [decodeIntegerRow 16 5 2 15239226812,
    decodeIntegerRow 16 5 2 64184414012,
    decodeIntegerRow 16 5 2 78734571572,
    decodeIntegerRow 16 5 2 76786139060,
    decodeIntegerRow 16 5 2 63989414012,
    decodeIntegerRow 16 5 2 137309538812,
    decodeIntegerRow 16 5 2 75809576564,
    decodeIntegerRow 16 5 2 78736131572,
    decodeIntegerRow 16 5 2 78736134052,
    decodeIntegerRow 16 5 2 75809564060,
    decodeIntegerRow 16 5 2 15278288812,
    decodeIntegerRow 16 5 2 88598789012,
    decodeIntegerRow 16 5 2 76786126564,
    decodeIntegerRow 16 5 2 78734569052,
    decodeIntegerRow 16 5 2 88403164012,
    decodeIntegerRow 16 5 2 137348601812]

private def rows0_6_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35871538]

private def rows1_6_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 19929028,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 7174452,
    decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 16740388,
    decodeIntegerRow 16 3 1 35872266,
    decodeIntegerRow 16 3 1 20991892,
    decodeIntegerRow 16 3 1 23117674,
    decodeIntegerRow 16 3 1 21464068,
    decodeIntegerRow 16 3 1 21700426,
    decodeIntegerRow 16 3 1 21514612,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21543772,
    decodeIntegerRow 16 3 1 21527734,
    decodeIntegerRow 16 3 1 21700588,
    decodeIntegerRow 16 3 1 21582166]

private def rows2_6_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35871538]

private def rows3_6_2 : List (List ℤ) := [decodeIntegerRow 16 5 2 73852539012,
    decodeIntegerRow 16 5 2 75805664312,
    decodeIntegerRow 16 5 2 15258789060,
    decodeIntegerRow 16 5 2 64086914072,
    decodeIntegerRow 16 5 2 64086914052,
    decodeIntegerRow 16 5 2 137329101560,
    decodeIntegerRow 16 5 2 75805663812,
    decodeIntegerRow 16 5 2 78735351512,
    decodeIntegerRow 16 5 2 76274407812,
    decodeIntegerRow 16 5 2 76391600312,
    decodeIntegerRow 16 5 2 76293007812,
    decodeIntegerRow 16 5 2 76297820312,
    decodeIntegerRow 16 5 2 76297882812,
    decodeIntegerRow 16 5 2 76294570312,
    decodeIntegerRow 16 5 2 76391602812,
    decodeIntegerRow 16 5 2 76313470312]

private def rows4_6_2 : List (List ℤ) := [decodeIntegerRow 16 5 2 73852539012,
    decodeIntegerRow 16 5 2 75805664312,
    decodeIntegerRow 16 5 2 15258789060,
    decodeIntegerRow 16 5 2 64086914072,
    decodeIntegerRow 16 5 2 64086914052,
    decodeIntegerRow 16 5 2 137329101560,
    decodeIntegerRow 16 5 2 75805663812,
    decodeIntegerRow 16 5 2 78735351512,
    decodeIntegerRow 16 5 2 76274407812,
    decodeIntegerRow 16 5 2 76391600312,
    decodeIntegerRow 16 5 2 76293007812,
    decodeIntegerRow 16 5 2 76297820312,
    decodeIntegerRow 16 5 2 76297882812,
    decodeIntegerRow 16 5 2 76294570312,
    decodeIntegerRow 16 5 2 76391602812,
    decodeIntegerRow 16 5 2 76313470312]

private def rows0_6_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320]

private def rows1_6_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 26642876,
    decodeIntegerRow 16 3 1 17111928,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 34329592,
    decodeIntegerRow 16 3 1 25929912,
    decodeIntegerRow 16 3 1 26639004,
    decodeIntegerRow 16 3 1 37400356,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 27036552,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 5515192,
    decodeIntegerRow 16 3 1 8822044,
    decodeIntegerRow 16 3 1 17431716]

private def rows2_6_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320]

private def rows3_6_3 : List (List ℤ) := [decodeIntegerRow 16 5 2 12837665552,
    decodeIntegerRow 16 5 2 63700045360,
    decodeIntegerRow 16 5 2 88106607864,
    decodeIntegerRow 16 5 2 134906478072,
    decodeIntegerRow 16 5 2 17681478072,
    decodeIntegerRow 16 5 2 64481607864,
    decodeIntegerRow 16 5 2 63700345264,
    decodeIntegerRow 16 5 2 12837725072,
    decodeIntegerRow 16 5 2 87919107760,
    decodeIntegerRow 16 5 2 134868977552,
    decodeIntegerRow 16 5 2 12797040072,
    decodeIntegerRow 16 5 2 63496920264,
    decodeIntegerRow 16 5 2 89090670264,
    decodeIntegerRow 16 5 2 139790790072,
    decodeIntegerRow 16 5 2 134868913072,
    decodeIntegerRow 16 5 2 87918782864]

private def rows4_6_3 : List (List ℤ) := [decodeIntegerRow 16 5 2 12837665552,
    decodeIntegerRow 16 5 2 63700045360,
    decodeIntegerRow 16 5 2 88106607864,
    decodeIntegerRow 16 5 2 134906478072,
    decodeIntegerRow 16 5 2 17681478072,
    decodeIntegerRow 16 5 2 64481607864,
    decodeIntegerRow 16 5 2 63700345264,
    decodeIntegerRow 16 5 2 12837725072,
    decodeIntegerRow 16 5 2 87919107760,
    decodeIntegerRow 16 5 2 134868977552,
    decodeIntegerRow 16 5 2 12797040072,
    decodeIntegerRow 16 5 2 63496920264,
    decodeIntegerRow 16 5 2 89090670264,
    decodeIntegerRow 16 5 2 139790790072,
    decodeIntegerRow 16 5 2 134868913072,
    decodeIntegerRow 16 5 2 87918782864]

private def rows0_6_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 2551,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows1_6_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3277,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 3199,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3271]

private def rows2_6_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 2551,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows3_6_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 2551,
    decodeIntegerRow 8 3 1 1093,
    decodeIntegerRow 8 3 1 3037,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 3289]

private def rows4_6_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 2551,
    decodeIntegerRow 8 3 1 1093,
    decodeIntegerRow 8 3 1 3037,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 3289]

private def rows0_6_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 16407716,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8717128,
    decodeIntegerRow 16 3 1 25934792,
    decodeIntegerRow 16 3 1 34224676,
    decodeIntegerRow 16 3 1 17116808,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 17431716,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 37531528,
    decodeIntegerRow 16 3 1 16403844,
    decodeIntegerRow 16 3 1 5646364,
    decodeIntegerRow 16 3 1 27036552]

private def rows1_6_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 34226128,
    decodeIntegerRow 16 3 1 17116304,
    decodeIntegerRow 16 3 1 8715664,
    decodeIntegerRow 16 3 1 25615472,
    decodeIntegerRow 16 3 1 16408220,
    decodeIntegerRow 16 3 1 5513740,
    decodeIntegerRow 16 3 1 16014540,
    decodeIntegerRow 16 3 1 5644900,
    decodeIntegerRow 16 3 1 27037020,
    decodeIntegerRow 16 3 1 37400140,
    decodeIntegerRow 16 3 1 16403340,
    decodeIntegerRow 16 3 1 5515300,
    decodeIntegerRow 16 3 1 8716912,
    decodeIntegerRow 16 3 1 25619376,
    decodeIntegerRow 16 3 1 8821936,
    decodeIntegerRow 16 3 1 25934288]

private def rows2_6_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 16407716,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8717128,
    decodeIntegerRow 16 3 1 25934792,
    decodeIntegerRow 16 3 1 34224676,
    decodeIntegerRow 16 3 1 17116808,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 17431716,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 37531528,
    decodeIntegerRow 16 3 1 16403844,
    decodeIntegerRow 16 3 1 5646364,
    decodeIntegerRow 16 3 1 27036552]

private def rows3_6_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 17718915072,
    decodeIntegerRow 16 5 2 88106295360,
    decodeIntegerRow 16 5 2 134906475072,
    decodeIntegerRow 16 5 2 64669095360,
    decodeIntegerRow 16 5 2 88887532760,
    decodeIntegerRow 16 5 2 139790852552,
    decodeIntegerRow 16 5 2 89090657864,
    decodeIntegerRow 16 5 2 139750228072,
    decodeIntegerRow 16 5 2 63496907864,
    decodeIntegerRow 16 5 2 12837728072,
    decodeIntegerRow 16 5 2 88887857864,
    decodeIntegerRow 16 5 2 139790788072,
    decodeIntegerRow 16 5 2 134906415552,
    decodeIntegerRow 16 5 2 64668795264,
    decodeIntegerRow 16 5 2 134868915072,
    decodeIntegerRow 16 5 2 64481295360]

private def rows4_6_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 17718915072,
    decodeIntegerRow 16 5 2 88106295360,
    decodeIntegerRow 16 5 2 134906475072,
    decodeIntegerRow 16 5 2 64669095360,
    decodeIntegerRow 16 5 2 88887532760,
    decodeIntegerRow 16 5 2 139790852552,
    decodeIntegerRow 16 5 2 89090657864,
    decodeIntegerRow 16 5 2 139750228072,
    decodeIntegerRow 16 5 2 63496907864,
    decodeIntegerRow 16 5 2 12837728072,
    decodeIntegerRow 16 5 2 88887857864,
    decodeIntegerRow 16 5 2 139790788072,
    decodeIntegerRow 16 5 2 134906415552,
    decodeIntegerRow 16 5 2 64668795264,
    decodeIntegerRow 16 5 2 134868915072,
    decodeIntegerRow 16 5 2 64481295360]

private def rows0_6_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043]

private def rows1_6_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 22054801]

private def rows2_6_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387]

private def rows3_6_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919]

private def rows4_6_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361]

private def rows0_6_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

private def rows1_6_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 15143800,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21562752,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 21339640,
    decodeIntegerRow 16 3 1 35340340,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 15148336,
    decodeIntegerRow 16 3 1 6642040]

private def rows2_6_7 : List (List ℤ) := [decodeIntegerRow 16 5 2 76801789064,
    decodeIntegerRow 16 5 2 73755039072,
    decodeIntegerRow 16 5 2 64086134112,
    decodeIntegerRow 16 5 2 137333014312,
    decodeIntegerRow 16 5 2 88500196512,
    decodeIntegerRow 16 5 2 15262701312,
    decodeIntegerRow 16 5 2 75825226560,
    decodeIntegerRow 16 5 2 78637851552,
    decodeIntegerRow 16 5 2 73950351552,
    decodeIntegerRow 16 5 2 75825164064,
    decodeIntegerRow 16 5 2 137325201312,
    decodeIntegerRow 16 5 2 88500194112,
    decodeIntegerRow 16 5 2 137333001312,
    decodeIntegerRow 16 5 2 88501759112,
    decodeIntegerRow 16 5 2 73754726552,
    decodeIntegerRow 16 5 2 75786164064]

private def rows3_6_7 : List (List ℤ) := [decodeIntegerRow 16 9 4 926522491878656,
    decodeIntegerRow 16 9 4 926384742374080,
    decodeIntegerRow 16 9 4 926384398000960,
    decodeIntegerRow 16 9 4 926525591248400,
    decodeIntegerRow 16 9 4 1007849781826816,
    decodeIntegerRow 16 9 4 104075282303680,
    decodeIntegerRow 16 9 4 101815850263360,
    decodeIntegerRow 16 9 4 1028184746717200,
    decodeIntegerRow 16 9 4 926384742374656,
    decodeIntegerRow 16 9 4 926497696967360,
    decodeIntegerRow 16 9 4 926525591242560,
    decodeIntegerRow 16 9 4 926635790851600,
    decodeIntegerRow 16 9 4 104075286082816,
    decodeIntegerRow 16 9 4 845170368813760,
    decodeIntegerRow 16 9 4 1028184708400960,
    decodeIntegerRow 16 9 4 1751204343312400]

private def rows4_6_7 : List (List ℤ) := [decodeIntegerRow 16 17 8 1431210577063215472,
    decodeIntegerRow 16 17 8 25677618606115367056,
    decodeIntegerRow 16 17 8 24251085135117016432,
    decodeIntegerRow 16 17 8 24335273043489375376,
    decodeIntegerRow 16 17 8 24251633485457938288,
    decodeIntegerRow 16 17 8 24335240787586968176,
    decodeIntegerRow 16 17 8 1431212474469318032,
    decodeIntegerRow 16 17 8 25677618494503252624,
    decodeIntegerRow 16 17 8 22983573381164956816,
    decodeIntegerRow 16 17 8 1431212474446521712,
    decodeIntegerRow 16 17 8 24325951087693699184,
    decodeIntegerRow 16 17 8 24251633492023357328,
    decodeIntegerRow 16 17 8 24335273043875576464,
    decodeIntegerRow 16 17 8 24410106733984433552,
    decodeIntegerRow 16 17 8 25677618606114035344,
    decodeIntegerRow 16 17 8 47229981298626292112]

def rowsB6 : ℕ → ℕ → List (List ℤ)
  | 0, 0 => rows0_6_0
  | 1, 0 => rows1_6_0
  | 2, 0 => rows2_6_0
  | 3, 0 => rows3_6_0
  | 4, 0 => rows4_6_0
  | 0, 1 => rows0_6_1
  | 1, 1 => rows1_6_1
  | 2, 1 => rows2_6_1
  | 3, 1 => rows3_6_1
  | 4, 1 => rows4_6_1
  | 0, 2 => rows0_6_2
  | 1, 2 => rows1_6_2
  | 2, 2 => rows2_6_2
  | 3, 2 => rows3_6_2
  | 4, 2 => rows4_6_2
  | 0, 3 => rows0_6_3
  | 1, 3 => rows1_6_3
  | 2, 3 => rows2_6_3
  | 3, 3 => rows3_6_3
  | 4, 3 => rows4_6_3
  | 0, 4 => rows0_6_4
  | 1, 4 => rows1_6_4
  | 2, 4 => rows2_6_4
  | 3, 4 => rows3_6_4
  | 4, 4 => rows4_6_4
  | 0, 5 => rows0_6_5
  | 1, 5 => rows1_6_5
  | 2, 5 => rows2_6_5
  | 3, 5 => rows3_6_5
  | 4, 5 => rows4_6_5
  | 0, 6 => rows0_6_6
  | 1, 6 => rows1_6_6
  | 2, 6 => rows2_6_6
  | 3, 6 => rows3_6_6
  | 4, 6 => rows4_6_6
  | 0, 7 => rows0_6_7
  | 1, 7 => rows1_6_7
  | 2, 7 => rows2_6_7
  | 3, 7 => rows3_6_7
  | 4, 7 => rows4_6_7
  | _, _ => []

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle6

import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 5, 7.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle5

private def rows0_7_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows1_7_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows2_7_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_7_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows4_7_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows0_7_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 6642526,
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

private def rows1_7_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 18153124,
    decodeIntegerRow 16 3 1 6683324,
    decodeIntegerRow 16 3 1 7627676,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 6604644,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 14977756,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 35262552,
    decodeIntegerRow 16 3 1 28073512,
    decodeIntegerRow 16 3 1 24530392,
    decodeIntegerRow 16 3 1 6602648,
    decodeIntegerRow 16 3 1 15314392,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 18148888]

private def rows2_7_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 6642526,
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

private def rows3_7_1 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293164072,
    decodeIntegerRow 16 5 2 76290039064,
    decodeIntegerRow 16 5 2 76274414312,
    decodeIntegerRow 16 5 2 76196289112,
    decodeIntegerRow 16 5 2 75805670312,
    decodeIntegerRow 16 5 2 73852540312,
    decodeIntegerRow 16 5 2 64087070312,
    decodeIntegerRow 16 5 2 15258820312,
    decodeIntegerRow 16 5 2 137329132812,
    decodeIntegerRow 16 5 2 88501132812,
    decodeIntegerRow 16 5 2 73852537812,
    decodeIntegerRow 16 5 2 75805657812,
    decodeIntegerRow 16 5 2 76391601612,
    decodeIntegerRow 16 5 2 76313476812,
    decodeIntegerRow 16 5 2 76290039060,
    decodeIntegerRow 16 5 2 76293164052]

private def rows4_7_1 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293164072,
    decodeIntegerRow 16 5 2 76290039064,
    decodeIntegerRow 16 5 2 76274414312,
    decodeIntegerRow 16 5 2 76196289112,
    decodeIntegerRow 16 5 2 75805670312,
    decodeIntegerRow 16 5 2 73852540312,
    decodeIntegerRow 16 5 2 64087070312,
    decodeIntegerRow 16 5 2 15258820312,
    decodeIntegerRow 16 5 2 137329132812,
    decodeIntegerRow 16 5 2 88501132812,
    decodeIntegerRow 16 5 2 73852537812,
    decodeIntegerRow 16 5 2 75805657812,
    decodeIntegerRow 16 5 2 76391601612,
    decodeIntegerRow 16 5 2 76313476812,
    decodeIntegerRow 16 5 2 76290039060,
    decodeIntegerRow 16 5 2 76293164052]

private def rows0_7_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 20992162,
    decodeIntegerRow 16 3 1 19929118,
    decodeIntegerRow 16 3 1 16742578,
    decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 21346222,
    decodeIntegerRow 16 3 1 21582382,
    decodeIntegerRow 16 3 1 21503678,
    decodeIntegerRow 16 3 1 21529918]

private def rows1_7_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 35852368,
    decodeIntegerRow 16 3 1 16733740,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 20932140,
    decodeIntegerRow 16 3 1 22113120,
    decodeIntegerRow 16 3 1 22942720,
    decodeIntegerRow 16 3 1 26312800,
    decodeIntegerRow 16 3 1 35852800,
    decodeIntegerRow 16 3 1 26299840,
    decodeIntegerRow 16 3 1 7155040,
    decodeIntegerRow 16 3 1 21996480,
    decodeIntegerRow 16 3 1 19754080,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 26299696]

private def rows2_7_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35871538,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516802]

private def rows3_7_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 27727972,
    decodeIntegerRow 16 3 1 7785572,
    decodeIntegerRow 16 3 1 36443588,
    decodeIntegerRow 16 3 1 24897988,
    decodeIntegerRow 16 3 1 24893440,
    decodeIntegerRow 16 3 1 6604160,
    decodeIntegerRow 16 3 1 7783680,
    decodeIntegerRow 16 3 1 15314560,
    decodeIntegerRow 16 3 1 6681920,
    decodeIntegerRow 16 3 1 24530560,
    decodeIntegerRow 16 3 1 14977600,
    decodeIntegerRow 16 3 1 7628160,
    decodeIntegerRow 16 3 1 7626164,
    decodeIntegerRow 16 3 1 28073356,
    decodeIntegerRow 16 3 1 24526036,
    decodeIntegerRow 16 3 1 36363884]

private def rows4_7_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 27727972,
    decodeIntegerRow 16 3 1 7785572,
    decodeIntegerRow 16 3 1 36443588,
    decodeIntegerRow 16 3 1 24897988,
    decodeIntegerRow 16 3 1 24893440,
    decodeIntegerRow 16 3 1 6604160,
    decodeIntegerRow 16 3 1 7783680,
    decodeIntegerRow 16 3 1 15314560,
    decodeIntegerRow 16 3 1 6681920,
    decodeIntegerRow 16 3 1 24530560,
    decodeIntegerRow 16 3 1 14977600,
    decodeIntegerRow 16 3 1 7628160,
    decodeIntegerRow 16 3 1 7626164,
    decodeIntegerRow 16 3 1 28073356,
    decodeIntegerRow 16 3 1 24526036,
    decodeIntegerRow 16 3 1 36363884]

private def rows0_7_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232]

private def rows1_7_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
    decodeIntegerRow 16 3 1 35931238,
    decodeIntegerRow 16 3 1 16917294,
    decodeIntegerRow 16 3 1 7233418,
    decodeIntegerRow 16 3 1 20974414,
    decodeIntegerRow 16 3 1 19923178,
    decodeIntegerRow 16 3 1 21009406,
    decodeIntegerRow 16 3 1 19934842,
    decodeIntegerRow 16 3 1 19936354,
    decodeIntegerRow 16 3 1 21013798,
    decodeIntegerRow 16 3 1 23124946,
    decodeIntegerRow 16 3 1 22076662,
    decodeIntegerRow 16 3 1 7233586,
    decodeIntegerRow 16 3 1 16917782,
    decodeIntegerRow 16 3 1 7115326,
    decodeIntegerRow 16 3 1 16563002]

private def rows2_7_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232]

private def rows3_7_3 : List (List ℤ) := [decodeIntegerRow 16 9 4 834877400603832,
    decodeIntegerRow 16 9 4 102931618935928,
    decodeIntegerRow 16 9 4 1017891740243528,
    decodeIntegerRow 16 9 4 1750060675693192,
    decodeIntegerRow 16 9 4 927641343122248,
    decodeIntegerRow 16 9 4 936677727803272,
    decodeIntegerRow 16 9 4 927638282022088,
    decodeIntegerRow 16 9 4 936677387681032,
    decodeIntegerRow 16 9 4 936677383423672,
    decodeIntegerRow 16 9 4 927638243757688,
    decodeIntegerRow 16 9 4 916342456802872,
    decodeIntegerRow 16 9 4 925378807466488,
    decodeIntegerRow 16 9 4 1750060675640632,
    decodeIntegerRow 16 9 4 1017891739771128,
    decodeIntegerRow 16 9 4 1750088569968328,
    decodeIntegerRow 16 9 4 1018142788720392]

private def rows4_7_3 : List (List ℤ) := [decodeIntegerRow 16 9 4 834877400603832,
    decodeIntegerRow 16 9 4 102931618935928,
    decodeIntegerRow 16 9 4 1017891740243528,
    decodeIntegerRow 16 9 4 1750060675693192,
    decodeIntegerRow 16 9 4 927641343122248,
    decodeIntegerRow 16 9 4 936677727803272,
    decodeIntegerRow 16 9 4 927638282022088,
    decodeIntegerRow 16 9 4 936677387681032,
    decodeIntegerRow 16 9 4 936677383423672,
    decodeIntegerRow 16 9 4 927638243757688,
    decodeIntegerRow 16 9 4 916342456802872,
    decodeIntegerRow 16 9 4 925378807466488,
    decodeIntegerRow 16 9 4 1750060675640632,
    decodeIntegerRow 16 9 4 1017891739771128,
    decodeIntegerRow 16 9 4 1750088569968328,
    decodeIntegerRow 16 9 4 1018142788720392]

private def rows0_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 2956,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3284]

private def rows1_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3282,
    decodeIntegerRow 8 3 1 3442,
    decodeIntegerRow 8 3 1 3298,
    decodeIntegerRow 8 3 1 3284,
    decodeIntegerRow 8 3 1 364,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 2956]

private def rows2_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 2956,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3284]

private def rows3_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 4738,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3284,
    decodeIntegerRow 8 3 1 364,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 2956]

private def rows4_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 4738,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3284,
    decodeIntegerRow 8 3 1 364,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 2956]

private def rows0_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21582328,
    decodeIntegerRow 16 3 1 21700264]

private def rows1_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 37414780,
    decodeIntegerRow 16 3 1 16053420,
    decodeIntegerRow 16 3 1 25580496,
    decodeIntegerRow 16 3 1 34342768,
    decodeIntegerRow 16 3 1 8702380,
    decodeIntegerRow 16 3 1 25575620,
    decodeIntegerRow 16 3 1 16049552,
    decodeIntegerRow 16 3 1 5633296,
    decodeIntegerRow 16 3 1 26682260,
    decodeIntegerRow 16 3 1 37518460,
    decodeIntegerRow 16 3 1 34213168,
    decodeIntegerRow 16 3 1 17077424,
    decodeIntegerRow 16 3 1 17072580,
    decodeIntegerRow 16 3 1 8835220,
    decodeIntegerRow 16 3 1 5527024,
    decodeIntegerRow 16 3 1 26678352]

private def rows2_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21582328,
    decodeIntegerRow 16 3 1 21700264]

private def rows3_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 5631940,
    decodeIntegerRow 16 3 1 26993300,
    decodeIntegerRow 16 3 1 17466224,
    decodeIntegerRow 16 3 1 8703952,
    decodeIntegerRow 16 3 1 34344340,
    decodeIntegerRow 16 3 1 17471100,
    decodeIntegerRow 16 3 1 26997168,
    decodeIntegerRow 16 3 1 37413424,
    decodeIntegerRow 16 3 1 16364460,
    decodeIntegerRow 16 3 1 5528260,
    decodeIntegerRow 16 3 1 8833552,
    decodeIntegerRow 16 3 1 25969296,
    decodeIntegerRow 16 3 1 25974140,
    decodeIntegerRow 16 3 1 34211500,
    decodeIntegerRow 16 3 1 37519696,
    decodeIntegerRow 16 3 1 16368368]

private def rows4_7_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 926637168346640,
    decodeIntegerRow 16 9 4 926495975104384,
    decodeIntegerRow 16 9 4 1739907161590720,
    decodeIntegerRow 16 9 4 836132661647680,
    decodeIntegerRow 16 9 4 926383020505856,
    decodeIntegerRow 16 9 4 926524213753360,
    decodeIntegerRow 16 9 4 1739907157391680,
    decodeIntegerRow 16 9 4 836132623856320,
    decodeIntegerRow 16 9 4 926523869373760,
    decodeIntegerRow 16 9 4 926634068982720,
    decodeIntegerRow 16 9 4 1019146963023616,
    decodeIntegerRow 16 9 4 1760242088269840,
    decodeIntegerRow 16 9 4 926496319472320,
    decodeIntegerRow 16 9 4 926386119869760,
    decodeIntegerRow 16 9 4 1019147001759760,
    decodeIntegerRow 16 9 4 1760242083965824]

private def rows0_7_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 28086460,
    decodeIntegerRow 16 3 1 6722256,
    decodeIntegerRow 16 3 1 35379248,
    decodeIntegerRow 16 3 1 18503020,
    decodeIntegerRow 16 3 1 24880336,
    decodeIntegerRow 16 3 1 7744260,
    decodeIntegerRow 16 3 1 6563820,
    decodeIntegerRow 16 3 1 27714832,
    decodeIntegerRow 16 3 1 7665584,
    decodeIntegerRow 16 3 1 18507580,
    decodeIntegerRow 16 3 1 28082260,
    decodeIntegerRow 16 3 1 36325488,
    decodeIntegerRow 16 3 1 36481980,
    decodeIntegerRow 16 3 1 27719056,
    decodeIntegerRow 16 3 1 24884848,
    decodeIntegerRow 16 3 1 35300460]

private def rows1_7_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 6642040,
    decodeIntegerRow 16 3 1 15148336,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 7706380]

private def rows2_7_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 35340340,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 21352768,
    decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21602120,
    decodeIntegerRow 16 3 1 21707056]

private def rows3_7_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 21352768,
    decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21602120,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 35340340]

private def rows4_7_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 21352768,
    decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21602120,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 35340340]

private def rows0_7_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

private def rows1_7_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

private def rows2_7_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912]

private def rows3_7_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912]

private def rows4_7_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912]

def rowsB7 : ℕ → ℕ → List (List ℤ)
  | 0, 0 => rows0_7_0
  | 1, 0 => rows1_7_0
  | 2, 0 => rows2_7_0
  | 3, 0 => rows3_7_0
  | 4, 0 => rows4_7_0
  | 0, 1 => rows0_7_1
  | 1, 1 => rows1_7_1
  | 2, 1 => rows2_7_1
  | 3, 1 => rows3_7_1
  | 4, 1 => rows4_7_1
  | 0, 2 => rows0_7_2
  | 1, 2 => rows1_7_2
  | 2, 2 => rows2_7_2
  | 3, 2 => rows3_7_2
  | 4, 2 => rows4_7_2
  | 0, 3 => rows0_7_3
  | 1, 3 => rows1_7_3
  | 2, 3 => rows2_7_3
  | 3, 3 => rows3_7_3
  | 4, 3 => rows4_7_3
  | 0, 4 => rows0_7_4
  | 1, 4 => rows1_7_4
  | 2, 4 => rows2_7_4
  | 3, 4 => rows3_7_4
  | 4, 4 => rows4_7_4
  | 0, 5 => rows0_7_5
  | 1, 5 => rows1_7_5
  | 2, 5 => rows2_7_5
  | 3, 5 => rows3_7_5
  | 4, 5 => rows4_7_5
  | 0, 6 => rows0_7_6
  | 1, 6 => rows1_7_6
  | 2, 6 => rows2_7_6
  | 3, 6 => rows3_7_6
  | 4, 6 => rows4_7_6
  | 0, 7 => rows0_7_7
  | 1, 7 => rows1_7_7
  | 2, 7 => rows2_7_7
  | 3, 7 => rows3_7_7
  | 4, 7 => rows4_7_7
  | _, _ => []

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle5

import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 7, 5.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

private def rows0_5_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows1_5_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows2_5_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_5_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows4_5_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows0_5_1 : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922239072,
    decodeIntegerRow 16 9 4 926508544743968,
    decodeIntegerRow 16 9 4 926496147291232,
    decodeIntegerRow 16 9 4 926384570187808,
    decodeIntegerRow 16 9 4 925380376516192,
    decodeIntegerRow 16 9 4 916342631138848,
    decodeIntegerRow 16 9 4 835002943737952,
    decodeIntegerRow 16 9 4 102945568173088,
    decodeIntegerRow 16 9 4 1750074624930280,
    decodeIntegerRow 16 9 4 1018017283377640,
    decodeIntegerRow 16 9 4 916342631086360,
    decodeIntegerRow 16 9 4 925380376043800,
    decodeIntegerRow 16 9 4 926635618664680,
    decodeIntegerRow 16 9 4 926524041566440,
    decodeIntegerRow 16 9 4 926508544743960,
    decodeIntegerRow 16 9 4 926509922239000]

private def rows1_5_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 6642526,
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

private def rows2_5_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 18153124,
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

private def rows3_5_1 : List (List ℤ) := [decodeIntegerRow 16 9 4 101815846011832,
    decodeIntegerRow 16 9 4 845170368761272,
    decodeIntegerRow 16 9 4 1028184708453448,
    decodeIntegerRow 16 9 4 104075286555208,
    decodeIntegerRow 16 9 4 926384398000312,
    decodeIntegerRow 16 9 4 926497696967352,
    decodeIntegerRow 16 9 4 926525591242568,
    decodeIntegerRow 16 9 4 926384742374728,
    decodeIntegerRow 16 9 4 926384742374008,
    decodeIntegerRow 16 9 4 926525591248392,
    decodeIntegerRow 16 9 4 926522491878648,
    decodeIntegerRow 16 9 4 926635790850952,
    decodeIntegerRow 16 9 4 104075281831288,
    decodeIntegerRow 16 9 4 1028184746664712,
    decodeIntegerRow 16 9 4 1007849781774328,
    decodeIntegerRow 16 9 4 1751204339060872]

private def rows4_5_1 : List (List ℤ) := [decodeIntegerRow 16 9 4 101815846011832,
    decodeIntegerRow 16 9 4 845170368761272,
    decodeIntegerRow 16 9 4 1028184708453448,
    decodeIntegerRow 16 9 4 104075286555208,
    decodeIntegerRow 16 9 4 926384398000312,
    decodeIntegerRow 16 9 4 926497696967352,
    decodeIntegerRow 16 9 4 926525591242568,
    decodeIntegerRow 16 9 4 926384742374728,
    decodeIntegerRow 16 9 4 926384742374008,
    decodeIntegerRow 16 9 4 926525591248392,
    decodeIntegerRow 16 9 4 926522491878648,
    decodeIntegerRow 16 9 4 926635790850952,
    decodeIntegerRow 16 9 4 104075281831288,
    decodeIntegerRow 16 9 4 1028184746664712,
    decodeIntegerRow 16 9 4 1007849781774328,
    decodeIntegerRow 16 9 4 1751204339060872]

private def rows0_5_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 15318748,
    decodeIntegerRow 16 3 1 35261148,
    decodeIntegerRow 16 3 1 6603132,
    decodeIntegerRow 16 3 1 18148732,
    decodeIntegerRow 16 3 1 18153280,
    decodeIntegerRow 16 3 1 36442560,
    decodeIntegerRow 16 3 1 35263040,
    decodeIntegerRow 16 3 1 27732160,
    decodeIntegerRow 16 3 1 36364800,
    decodeIntegerRow 16 3 1 18516160,
    decodeIntegerRow 16 3 1 28069120,
    decodeIntegerRow 16 3 1 35418560,
    decodeIntegerRow 16 3 1 35420556,
    decodeIntegerRow 16 3 1 14973364,
    decodeIntegerRow 16 3 1 18520684,
    decodeIntegerRow 16 3 1 6682836]

private def rows1_5_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
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

private def rows2_5_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 35852368,
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

private def rows3_5_2 : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922239000,
    decodeIntegerRow 16 9 4 926508544743960,
    decodeIntegerRow 16 9 4 926496147285400,
    decodeIntegerRow 16 9 4 926384570187160,
    decodeIntegerRow 16 9 4 1750074624930280,
    decodeIntegerRow 16 9 4 835002905474200,
    decodeIntegerRow 16 9 4 936677557765480,
    decodeIntegerRow 16 9 4 925380376043800,
    decodeIntegerRow 16 9 4 927639812335648,
    decodeIntegerRow 16 9 4 936677557712992,
    decodeIntegerRow 16 9 4 1018017245113888,
    decodeIntegerRow 16 9 4 1750074620678752,
    decodeIntegerRow 16 9 4 926635618664032,
    decodeIntegerRow 16 9 4 926496147291232,
    decodeIntegerRow 16 9 4 926511644107872,
    decodeIntegerRow 16 9 4 926509922239072]

private def rows4_5_2 : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922239000,
    decodeIntegerRow 16 9 4 926508544743960,
    decodeIntegerRow 16 9 4 926496147285400,
    decodeIntegerRow 16 9 4 926384570187160,
    decodeIntegerRow 16 9 4 1750074624930280,
    decodeIntegerRow 16 9 4 835002905474200,
    decodeIntegerRow 16 9 4 936677557765480,
    decodeIntegerRow 16 9 4 925380376043800,
    decodeIntegerRow 16 9 4 927639812335648,
    decodeIntegerRow 16 9 4 936677557712992,
    decodeIntegerRow 16 9 4 1018017245113888,
    decodeIntegerRow 16 9 4 1750074620678752,
    decodeIntegerRow 16 9 4 926635618664032,
    decodeIntegerRow 16 9 4 926496147291232,
    decodeIntegerRow 16 9 4 926511644107872,
    decodeIntegerRow 16 9 4 926509922239072]

private def rows0_5_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
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

private def rows1_5_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
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

private def rows2_5_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
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

private def rows3_5_3 : List (List ℤ) := [decodeIntegerRow 16 5 2 139790787552,
    decodeIntegerRow 16 5 2 89090657760,
    decodeIntegerRow 16 5 2 12837727552,
    decodeIntegerRow 16 5 2 63700357760,
    decodeIntegerRow 16 5 2 64668795360,
    decodeIntegerRow 16 5 2 17718915552,
    decodeIntegerRow 16 5 2 88106595360,
    decodeIntegerRow 16 5 2 134906475552,
    decodeIntegerRow 16 5 2 88887857760,
    decodeIntegerRow 16 5 2 139750227552,
    decodeIntegerRow 16 5 2 89090982864,
    decodeIntegerRow 16 5 2 139790853072,
    decodeIntegerRow 16 5 2 134906415072,
    decodeIntegerRow 16 5 2 88106295264,
    decodeIntegerRow 16 5 2 134868915552,
    decodeIntegerRow 16 5 2 87918795360]

private def rows4_5_3 : List (List ℤ) := [decodeIntegerRow 16 5 2 139790787552,
    decodeIntegerRow 16 5 2 89090657760,
    decodeIntegerRow 16 5 2 12837727552,
    decodeIntegerRow 16 5 2 63700357760,
    decodeIntegerRow 16 5 2 64668795360,
    decodeIntegerRow 16 5 2 17718915552,
    decodeIntegerRow 16 5 2 88106595360,
    decodeIntegerRow 16 5 2 134906475552,
    decodeIntegerRow 16 5 2 88887857760,
    decodeIntegerRow 16 5 2 139750227552,
    decodeIntegerRow 16 5 2 89090982864,
    decodeIntegerRow 16 5 2 139790853072,
    decodeIntegerRow 16 5 2 134906415072,
    decodeIntegerRow 16 5 2 88106295264,
    decodeIntegerRow 16 5 2 134868915552,
    decodeIntegerRow 16 5 2 87918795360]

private def rows0_5_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3282,
    decodeIntegerRow 8 3 1 3442,
    decodeIntegerRow 8 3 1 3298,
    decodeIntegerRow 8 3 1 3276,
    decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 3316,
    decodeIntegerRow 8 3 1 3604]

private def rows1_5_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 2956,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3284]

private def rows2_5_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3282,
    decodeIntegerRow 8 3 1 3442,
    decodeIntegerRow 8 3 1 3298,
    decodeIntegerRow 8 3 1 3284,
    decodeIntegerRow 8 3 1 364,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 2956]

private def rows3_5_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 2956,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3284]

private def rows4_5_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 2956,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3284]

private def rows0_5_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 37414780,
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

private def rows1_5_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 21582490,
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

private def rows2_5_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 926383020505200,
    decodeIntegerRow 16 9 4 926524213747456,
    decodeIntegerRow 16 9 4 113113027261120,
    decodeIntegerRow 16 9 4 1016887527204160,
    decodeIntegerRow 16 9 4 926637168345984,
    decodeIntegerRow 16 9 4 926495975098480,
    decodeIntegerRow 16 9 4 113113031460160,
    decodeIntegerRow 16 9 4 1016887564995520,
    decodeIntegerRow 16 9 4 926496319478080,
    decodeIntegerRow 16 9 4 926386119869120,
    decodeIntegerRow 16 9 4 833873225828224,
    decodeIntegerRow 16 9 4 92778100582000,
    decodeIntegerRow 16 9 4 926523869379520,
    decodeIntegerRow 16 9 4 926634068982080,
    decodeIntegerRow 16 9 4 833873187092080,
    decodeIntegerRow 16 9 4 92778104886016]

private def rows3_5_5 : List (List ℤ) := [decodeIntegerRow 16 33 16 988992576226015655761120,
    decodeIntegerRow 16 33 16 988991792057574593171680,
    decodeIntegerRow 16 33 16 989873246395174615601440,
    decodeIntegerRow 16 33 16 988965914499040191190240,
    decodeIntegerRow 16 33 16 959931293822738629006592,
    decodeIntegerRow 16 33 16 29969472749432710272256,
    decodeIntegerRow 16 33 16 988992599989377583623424,
    decodeIntegerRow 16 33 16 988992600753761313371392,
    decodeIntegerRow 16 33 16 988992599988013793448160,
    decodeIntegerRow 16 33 16 988992600753802640346400,
    decodeIntegerRow 16 33 16 1018053907639820248927520,
    decodeIntegerRow 16 33 16 1948015728713126167662880,
    decodeIntegerRow 16 33 16 988111955067384263482624,
    decodeIntegerRow 16 33 16 989019286963518686708992,
    decodeIntegerRow 16 33 16 988992576226015693710592,
    decodeIntegerRow 16 33 16 988991792057575845504256]

private def rows4_5_5 : List (List ℤ) := [decodeIntegerRow 16 33 16 988992576226015655761120,
    decodeIntegerRow 16 33 16 988991792057574593171680,
    decodeIntegerRow 16 33 16 989873246395174615601440,
    decodeIntegerRow 16 33 16 988965914499040191190240,
    decodeIntegerRow 16 33 16 959931293822738629006592,
    decodeIntegerRow 16 33 16 29969472749432710272256,
    decodeIntegerRow 16 33 16 988992599989377583623424,
    decodeIntegerRow 16 33 16 988992600753761313371392,
    decodeIntegerRow 16 33 16 988992599988013793448160,
    decodeIntegerRow 16 33 16 988992600753802640346400,
    decodeIntegerRow 16 33 16 1018053907639820248927520,
    decodeIntegerRow 16 33 16 1948015728713126167662880,
    decodeIntegerRow 16 33 16 988111955067384263482624,
    decodeIntegerRow 16 33 16 989019286963518686708992,
    decodeIntegerRow 16 33 16 988992576226015693710592,
    decodeIntegerRow 16 33 16 988991792057575845504256]

private def rows0_5_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
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

private def rows1_5_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507]

private def rows2_5_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
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

private def rows3_5_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 61546915352,
    decodeIntegerRow 16 5 2 137793920064,
    decodeIntegerRow 16 5 2 15731482560,
    decodeIntegerRow 16 5 2 85962852872,
    decodeIntegerRow 16 5 2 66431602752,
    decodeIntegerRow 16 5 2 136825233064,
    decodeIntegerRow 16 5 2 137840845064,
    decodeIntegerRow 16 5 2 61744100352,
    decodeIntegerRow 16 5 2 136856482560,
    decodeIntegerRow 16 5 2 85962537752,
    decodeIntegerRow 16 5 2 61547225272,
    decodeIntegerRow 16 5 2 14793920064,
    decodeIntegerRow 16 5 2 14747095064,
    decodeIntegerRow 16 5 2 61743790272,
    decodeIntegerRow 16 5 2 66431287872,
    decodeIntegerRow 16 5 2 15762733064]

private def rows4_5_6 : List (List ℤ) := [decodeIntegerRow 16 17 8 24330595937834104720,
    decodeIntegerRow 16 17 8 24330595937844753792,
    decodeIntegerRow 16 17 8 24330595938026534784,
    decodeIntegerRow 16 17 8 24330595941116143760,
    decodeIntegerRow 16 17 8 24409558386926220672,
    decodeIntegerRow 16 17 8 24325918831984392560,
    decodeIntegerRow 16 17 8 47229981298614972560,
    decodeIntegerRow 16 17 8 22983573381164286336,
    decodeIntegerRow 16 17 8 24325951087886799744,
    decodeIntegerRow 16 17 8 24251085138399725680,
    decodeIntegerRow 16 17 8 22983573269552167280,
    decodeIntegerRow 16 17 8 1431212474457919872,
    decodeIntegerRow 16 17 8 24330595937822036080,
    decodeIntegerRow 16 17 8 24330595937834100096,
    decodeIntegerRow 16 17 8 24330595934550724992,
    decodeIntegerRow 16 17 8 24330595938026534800]

private def rows0_5_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
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

private def rows1_5_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

private def rows2_5_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
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

private def rows3_5_7 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293945314,
    decodeIntegerRow 16 5 2 76293945322,
    decodeIntegerRow 16 5 2 76293945362,
    decodeIntegerRow 16 5 2 76293945562,
    decodeIntegerRow 16 5 2 76293946562,
    decodeIntegerRow 16 5 2 76293951562,
    decodeIntegerRow 16 5 2 76293976562,
    decodeIntegerRow 16 5 2 76294101562,
    decodeIntegerRow 16 5 2 76294726562,
    decodeIntegerRow 16 5 2 76297851562,
    decodeIntegerRow 16 5 2 76313476562,
    decodeIntegerRow 16 5 2 76391601562,
    decodeIntegerRow 16 5 2 76782226562,
    decodeIntegerRow 16 5 2 78735351562,
    decodeIntegerRow 16 5 2 88500976562,
    decodeIntegerRow 16 5 2 137329101562]

private def rows4_5_7 : List (List ℤ) := [decodeIntegerRow 16 5 2 78735195312,
    decodeIntegerRow 16 5 2 76782257812,
    decodeIntegerRow 16 5 2 15258782812,
    decodeIntegerRow 16 5 2 64086915312,
    decodeIntegerRow 16 5 2 76290039312,
    decodeIntegerRow 16 5 2 76293164012,
    decodeIntegerRow 16 5 2 76391601572,
    decodeIntegerRow 16 5 2 76313476560,
    decodeIntegerRow 16 5 2 137329095312,
    decodeIntegerRow 16 5 2 64086912812,
    decodeIntegerRow 16 5 2 78735507812,
    decodeIntegerRow 16 5 2 75805695312,
    decodeIntegerRow 16 5 2 76196289072,
    decodeIntegerRow 16 5 2 76313476564,
    decodeIntegerRow 16 5 2 76290038812,
    decodeIntegerRow 16 5 2 76294726512]

def rowsB5 : ℕ → ℕ → List (List ℤ)
  | 0, 0 => rows0_5_0
  | 1, 0 => rows1_5_0
  | 2, 0 => rows2_5_0
  | 3, 0 => rows3_5_0
  | 4, 0 => rows4_5_0
  | 0, 1 => rows0_5_1
  | 1, 1 => rows1_5_1
  | 2, 1 => rows2_5_1
  | 3, 1 => rows3_5_1
  | 4, 1 => rows4_5_1
  | 0, 2 => rows0_5_2
  | 1, 2 => rows1_5_2
  | 2, 2 => rows2_5_2
  | 3, 2 => rows3_5_2
  | 4, 2 => rows4_5_2
  | 0, 3 => rows0_5_3
  | 1, 3 => rows1_5_3
  | 2, 3 => rows2_5_3
  | 3, 3 => rows3_5_3
  | 4, 3 => rows4_5_3
  | 0, 4 => rows0_5_4
  | 1, 4 => rows1_5_4
  | 2, 4 => rows2_5_4
  | 3, 4 => rows3_5_4
  | 4, 4 => rows4_5_4
  | 0, 5 => rows0_5_5
  | 1, 5 => rows1_5_5
  | 2, 5 => rows2_5_5
  | 3, 5 => rows3_5_5
  | 4, 5 => rows4_5_5
  | 0, 6 => rows0_5_6
  | 1, 6 => rows1_5_6
  | 2, 6 => rows2_5_6
  | 3, 6 => rows3_5_6
  | 4, 6 => rows4_5_6
  | 0, 7 => rows0_5_7
  | 1, 7 => rows1_5_7
  | 2, 7 => rows2_5_7
  | 3, 7 => rows3_5_7
  | 4, 7 => rows4_5_7
  | _, _ => []

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 7, 6.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

private def rows0_6_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4224,
    decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 5560]

private def rows1_6_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4224,
    decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 5560]

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

private def rows0_6_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 3308,
    decodeIntegerRow 8 3 1 3306,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 3766,
    decodeIntegerRow 8 3 1 1012,
    decodeIntegerRow 8 3 1 1174,
    decodeIntegerRow 8 3 1 2308]

private def rows1_6_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 3792,
    decodeIntegerRow 8 3 1 5560]

private def rows2_6_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_6_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 3792,
    decodeIntegerRow 8 3 1 5560]

private def rows4_6_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 3792,
    decodeIntegerRow 8 3 1 5560]

private def rows0_6_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows1_6_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 1346,
    decodeIntegerRow 8 3 1 2662,
    decodeIntegerRow 8 3 1 4114,
    decodeIntegerRow 8 3 1 5718,
    decodeIntegerRow 8 3 1 3958,
    decodeIntegerRow 8 3 1 5234,
    decodeIntegerRow 8 3 1 858,
    decodeIntegerRow 8 3 1 2494]

private def rows2_6_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_6_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 1346,
    decodeIntegerRow 8 3 1 2662,
    decodeIntegerRow 8 3 1 4114,
    decodeIntegerRow 8 3 1 5718,
    decodeIntegerRow 8 3 1 3958,
    decodeIntegerRow 8 3 1 5234,
    decodeIntegerRow 8 3 1 858,
    decodeIntegerRow 8 3 1 2494]

private def rows4_6_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 1346,
    decodeIntegerRow 8 3 1 2662,
    decodeIntegerRow 8 3 1 4114,
    decodeIntegerRow 8 3 1 5718,
    decodeIntegerRow 8 3 1 3958,
    decodeIntegerRow 8 3 1 5234,
    decodeIntegerRow 8 3 1 858,
    decodeIntegerRow 8 3 1 2494]

private def rows0_6_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3199,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 1093,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3289]

private def rows1_6_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3302,
    decodeIntegerRow 8 3 1 3318,
    decodeIntegerRow 8 3 1 5062,
    decodeIntegerRow 8 3 1 6358,
    decodeIntegerRow 8 3 1 6034,
    decodeIntegerRow 8 3 1 4414,
    decodeIntegerRow 8 3 1 3314,
    decodeIntegerRow 8 3 1 3294]

private def rows2_6_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3289]

private def rows3_6_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3302,
    decodeIntegerRow 8 3 1 3318,
    decodeIntegerRow 8 3 1 5062,
    decodeIntegerRow 8 3 1 6358,
    decodeIntegerRow 8 3 1 6034,
    decodeIntegerRow 8 3 1 4414,
    decodeIntegerRow 8 3 1 3314,
    decodeIntegerRow 8 3 1 3294]

private def rows4_6_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3302,
    decodeIntegerRow 8 3 1 3318,
    decodeIntegerRow 8 3 1 5062,
    decodeIntegerRow 8 3 1 6358,
    decodeIntegerRow 8 3 1 6034,
    decodeIntegerRow 8 3 1 4414,
    decodeIntegerRow 8 3 1 3314,
    decodeIntegerRow 8 3 1 3294]

private def rows0_6_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 842,
    decodeIntegerRow 8 3 1 4066,
    decodeIntegerRow 8 3 1 2602,
    decodeIntegerRow 8 3 1 1346,
    decodeIntegerRow 8 3 1 4114,
    decodeIntegerRow 8 3 1 5702,
    decodeIntegerRow 8 3 1 5234,
    decodeIntegerRow 8 3 1 2662]

private def rows1_6_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 165312,
    decodeIntegerRow 8 5 2 45312,
    decodeIntegerRow 8 5 2 162812,
    decodeIntegerRow 8 5 2 32812,
    decodeIntegerRow 8 5 2 195264,
    decodeIntegerRow 8 5 2 195072,
    decodeIntegerRow 8 5 2 195260,
    decodeIntegerRow 8 5 2 195052]

private def rows2_6_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 842,
    decodeIntegerRow 8 3 1 4066,
    decodeIntegerRow 8 3 1 2602,
    decodeIntegerRow 8 3 1 1346,
    decodeIntegerRow 8 3 1 4114,
    decodeIntegerRow 8 3 1 5702,
    decodeIntegerRow 8 3 1 5234,
    decodeIntegerRow 8 3 1 2662]

private def rows3_6_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 165312,
    decodeIntegerRow 8 5 2 45312,
    decodeIntegerRow 8 5 2 162812,
    decodeIntegerRow 8 5 2 32812,
    decodeIntegerRow 8 5 2 195264,
    decodeIntegerRow 8 5 2 195072,
    decodeIntegerRow 8 5 2 195260,
    decodeIntegerRow 8 5 2 195052]

private def rows4_6_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 165312,
    decodeIntegerRow 8 5 2 45312,
    decodeIntegerRow 8 5 2 162812,
    decodeIntegerRow 8 5 2 32812,
    decodeIntegerRow 8 5 2 195264,
    decodeIntegerRow 8 5 2 195072,
    decodeIntegerRow 8 5 2 195260,
    decodeIntegerRow 8 5 2 195052]

private def rows0_6_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 7877464,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 27824052,
    decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 15065256,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 24753612,
    decodeIntegerRow 16 3 1 27977304,
    decodeIntegerRow 16 3 1 6458824,
    decodeIntegerRow 16 3 1 35512372,
    decodeIntegerRow 16 3 1 18297588,
    decodeIntegerRow 16 3 1 35171224,
    decodeIntegerRow 16 3 1 24670344,
    decodeIntegerRow 16 3 1 15226932,
    decodeIntegerRow 16 3 1 6826228]

private def rows1_6_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 6471460,
    decodeIntegerRow 16 3 1 15108944,
    decodeIntegerRow 16 3 1 18411312,
    decodeIntegerRow 16 3 1 7890100,
    decodeIntegerRow 16 3 1 24792816,
    decodeIntegerRow 16 3 1 7522660,
    decodeIntegerRow 16 3 1 6812620,
    decodeIntegerRow 16 3 1 27858992,
    decodeIntegerRow 16 3 1 15183140,
    decodeIntegerRow 16 3 1 36232144,
    decodeIntegerRow 16 3 1 7521712,
    decodeIntegerRow 16 3 1 24788660,
    decodeIntegerRow 16 3 1 7889104,
    decodeIntegerRow 16 3 1 18415580,
    decodeIntegerRow 16 3 1 27942260,
    decodeIntegerRow 16 3 1 36573328]

private def rows2_6_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 7877464,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 27824052,
    decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 15065256,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 24753612,
    decodeIntegerRow 16 3 1 15069416,
    decodeIntegerRow 16 3 1 36587896,
    decodeIntegerRow 16 3 1 7534348,
    decodeIntegerRow 16 3 1 24749132,
    decodeIntegerRow 16 3 1 7875496,
    decodeIntegerRow 16 3 1 18376376,
    decodeIntegerRow 16 3 1 27819788,
    decodeIntegerRow 16 3 1 36220492]

private def rows3_6_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 137914295272,
    decodeIntegerRow 16 5 2 90957850560,
    decodeIntegerRow 16 5 2 86036288064,
    decodeIntegerRow 16 5 2 136742357752,
    decodeIntegerRow 16 5 2 66504728064,
    decodeIntegerRow 16 5 2 136939232872,
    decodeIntegerRow 16 5 2 137720545352,
    decodeIntegerRow 16 5 2 61661290560,
    decodeIntegerRow 16 5 2 90926915560,
    decodeIntegerRow 16 5 2 14867420352,
    decodeIntegerRow 16 5 2 136939282752,
    decodeIntegerRow 16 5 2 66505037560,
    decodeIntegerRow 16 5 2 136742407872,
    decodeIntegerRow 16 5 2 86035977560,
    decodeIntegerRow 16 5 2 61629725560,
    decodeIntegerRow 16 5 2 14673670272]

private def rows4_6_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 137914295272,
    decodeIntegerRow 16 5 2 90957850560,
    decodeIntegerRow 16 5 2 86036288064,
    decodeIntegerRow 16 5 2 136742357752,
    decodeIntegerRow 16 5 2 66504728064,
    decodeIntegerRow 16 5 2 136939232872,
    decodeIntegerRow 16 5 2 137720545352,
    decodeIntegerRow 16 5 2 61661290560,
    decodeIntegerRow 16 5 2 90926915560,
    decodeIntegerRow 16 5 2 14867420352,
    decodeIntegerRow 16 5 2 136939282752,
    decodeIntegerRow 16 5 2 66505037560,
    decodeIntegerRow 16 5 2 136742407872,
    decodeIntegerRow 16 5 2 86035977560,
    decodeIntegerRow 16 5 2 61629725560,
    decodeIntegerRow 16 5 2 14673670272]

private def rows0_6_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 20932654,
    decodeIntegerRow 16 3 1 23294758,
    decodeIntegerRow 16 3 1 26315074,
    decodeIntegerRow 16 3 1 7155498,
    decodeIntegerRow 16 3 1 16749142,
    decodeIntegerRow 16 3 1 35853314,
    decodeIntegerRow 16 3 1 21995482,
    decodeIntegerRow 16 3 1 20106094,
    decodeIntegerRow 16 3 1 26310706,
    decodeIntegerRow 16 3 1 35892678,
    decodeIntegerRow 16 3 1 22113634,
    decodeIntegerRow 16 3 1 23294902,
    decodeIntegerRow 16 3 1 21996022,
    decodeIntegerRow 16 3 1 22940446,
    decodeIntegerRow 16 3 1 26301958,
    decodeIntegerRow 16 3 1 35851854]

private def rows1_6_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 76762689312,
    decodeIntegerRow 16 5 2 73950194112,
    decodeIntegerRow 16 5 2 64087851552,
    decodeIntegerRow 16 5 2 137325226560,
    decodeIntegerRow 16 5 2 64086289072,
    decodeIntegerRow 16 5 2 137333039064,
    decodeIntegerRow 16 5 2 76801751312,
    decodeIntegerRow 16 5 2 73754881512,
    decodeIntegerRow 16 5 2 73950196512,
    decodeIntegerRow 16 5 2 75825189312,
    decodeIntegerRow 16 5 2 137325164064,
    decodeIntegerRow 16 5 2 88500351552,
    decodeIntegerRow 16 5 2 137332976560,
    decodeIntegerRow 16 5 2 88501914072,
    decodeIntegerRow 16 5 2 73754884112,
    decodeIntegerRow 16 5 2 75786126312]

private def rows2_6_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 7155498,
    decodeIntegerRow 16 3 1 26315074,
    decodeIntegerRow 16 3 1 19751962,
    decodeIntegerRow 16 3 1 22114066,
    decodeIntegerRow 16 3 1 20106094,
    decodeIntegerRow 16 3 1 21995482,
    decodeIntegerRow 16 3 1 7193406,
    decodeIntegerRow 16 3 1 26297578,
    decodeIntegerRow 16 3 1 20106274,
    decodeIntegerRow 16 3 1 21050698,
    decodeIntegerRow 16 3 1 35851854,
    decodeIntegerRow 16 3 1 26301958,
    decodeIntegerRow 16 3 1 35892678,
    decodeIntegerRow 16 3 1 26310706,
    decodeIntegerRow 16 3 1 19751818,
    decodeIntegerRow 16 3 1 20933086]

private def rows3_6_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 76762689312,
    decodeIntegerRow 16 5 2 73950194112,
    decodeIntegerRow 16 5 2 64087851552,
    decodeIntegerRow 16 5 2 137325226560,
    decodeIntegerRow 16 5 2 64086289072,
    decodeIntegerRow 16 5 2 137333039064,
    decodeIntegerRow 16 5 2 76801751312,
    decodeIntegerRow 16 5 2 73754881512,
    decodeIntegerRow 16 5 2 73950196512,
    decodeIntegerRow 16 5 2 75825189312,
    decodeIntegerRow 16 5 2 137325164064,
    decodeIntegerRow 16 5 2 88500351552,
    decodeIntegerRow 16 5 2 137332976560,
    decodeIntegerRow 16 5 2 88501914072,
    decodeIntegerRow 16 5 2 73754884112,
    decodeIntegerRow 16 5 2 75786126312]

private def rows4_6_6 : List (List ℤ) := [decodeIntegerRow 16 9 4 926494597609272,
    decodeIntegerRow 16 9 4 926635790851528,
    decodeIntegerRow 16 9 4 926384742374008,
    decodeIntegerRow 16 9 4 926522491878648,
    decodeIntegerRow 16 9 4 824835480398392,
    decodeIntegerRow 16 9 4 1751204342840008,
    decodeIntegerRow 16 9 4 104075281831288,
    decodeIntegerRow 16 9 4 1007849781774328,
    decodeIntegerRow 16 9 4 824835442187128,
    decodeIntegerRow 16 9 4 101815849790968,
    decodeIntegerRow 16 9 4 1748944902296632,
    decodeIntegerRow 16 9 4 1007849820090568,
    decodeIntegerRow 16 9 4 926525591248392,
    decodeIntegerRow 16 9 4 926635790850952,
    decodeIntegerRow 16 9 4 926384742374728,
    decodeIntegerRow 16 9 4 926497696967352]

private def rows0_6_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 5710,
    decodeIntegerRow 8 3 1 3928,
    decodeIntegerRow 8 3 1 5224,
    decodeIntegerRow 8 3 1 2470,
    decodeIntegerRow 8 3 1 3290,
    decodeIntegerRow 8 3 1 3256,
    decodeIntegerRow 8 3 1 3288,
    decodeIntegerRow 8 3 1 3310]

private def rows1_6_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3302,
    decodeIntegerRow 8 3 1 3318,
    decodeIntegerRow 8 3 1 3314,
    decodeIntegerRow 8 3 1 3294,
    decodeIntegerRow 8 3 1 6034,
    decodeIntegerRow 8 3 1 2146,
    decodeIntegerRow 8 3 1 1498,
    decodeIntegerRow 8 3 1 6358]

private def rows2_6_7 : List (List ℤ) := [decodeIntegerRow 8 5 2 352812,
    decodeIntegerRow 8 5 2 232812,
    decodeIntegerRow 8 5 2 220312,
    decodeIntegerRow 8 5 2 350312,
    decodeIntegerRow 8 5 2 195064,
    decodeIntegerRow 8 5 2 195272,
    decodeIntegerRow 8 5 2 195372,
    decodeIntegerRow 8 5 2 195564]

private def rows3_6_7 : List (List ℤ) := [decodeIntegerRow 8 5 2 195004,
    decodeIntegerRow 8 5 2 195524,
    decodeIntegerRow 8 5 2 195124,
    decodeIntegerRow 8 5 2 195604,
    decodeIntegerRow 8 5 2 2812,
    decodeIntegerRow 8 5 2 327812,
    decodeIntegerRow 8 5 2 77812,
    decodeIntegerRow 8 5 2 377812]

private def rows4_6_7 : List (List ℤ) := [decodeIntegerRow 8 9 4 19423840,
    decodeIntegerRow 8 9 4 40891432,
    decodeIntegerRow 8 9 4 23675368,
    decodeIntegerRow 8 9 4 40419040,
    decodeIntegerRow 8 9 4 21520408,
    decodeIntegerRow 8 9 4 21523040,
    decodeIntegerRow 8 9 4 21520480,
    decodeIntegerRow 8 9 4 21523688]

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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

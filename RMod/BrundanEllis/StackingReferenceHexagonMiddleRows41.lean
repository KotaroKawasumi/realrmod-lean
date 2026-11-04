import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 4, 1.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle4

private def rows0_1_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows1_1_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows2_1_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_1_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows4_1_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows0_1_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows1_1_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 5548,
    decodeIntegerRow 8 3 1 2794,
    decodeIntegerRow 8 3 1 4252,
    decodeIntegerRow 8 3 1 5386,
    decodeIntegerRow 8 3 1 3306,
    decodeIntegerRow 8 3 1 3268,
    decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 3252]

private def rows2_1_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 1012,
    decodeIntegerRow 8 3 1 3766,
    decodeIntegerRow 8 3 1 2308,
    decodeIntegerRow 8 3 1 1174,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 3286,
    decodeIntegerRow 8 3 1 3308]

private def rows3_1_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 1012,
    decodeIntegerRow 8 3 1 3766,
    decodeIntegerRow 8 3 1 2308,
    decodeIntegerRow 8 3 1 1174,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 3286,
    decodeIntegerRow 8 3 1 3308]

private def rows4_1_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 1012,
    decodeIntegerRow 8 3 1 3766,
    decodeIntegerRow 8 3 1 2308,
    decodeIntegerRow 8 3 1 1174,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 3286,
    decodeIntegerRow 8 3 1 3308]

private def rows0_1_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 2632,
    decodeIntegerRow 8 3 1 1336,
    decodeIntegerRow 8 3 1 4090,
    decodeIntegerRow 8 3 1 5710,
    decodeIntegerRow 8 3 1 3270,
    decodeIntegerRow 8 3 1 3250,
    decodeIntegerRow 8 3 1 3272,
    decodeIntegerRow 8 3 1 3256]

private def rows1_1_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 3226,
    decodeIntegerRow 8 3 1 3046,
    decodeIntegerRow 8 3 1 1094,
    decodeIntegerRow 8 3 1 2554,
    decodeIntegerRow 8 3 1 3532,
    decodeIntegerRow 8 3 1 3388,
    decodeIntegerRow 8 3 1 2548,
    decodeIntegerRow 8 3 1 1092]

private def rows2_1_2 : List (List ℤ) := [decodeIntegerRow 8 5 2 196312,
    decodeIntegerRow 8 5 2 201512,
    decodeIntegerRow 8 5 2 226572,
    decodeIntegerRow 8 5 2 351564,
    decodeIntegerRow 8 5 2 351560,
    decodeIntegerRow 8 5 2 226552,
    decodeIntegerRow 8 5 2 189012,
    decodeIntegerRow 8 5 2 193812]

private def rows3_1_2 : List (List ℤ) := [decodeIntegerRow 8 5 2 196312,
    decodeIntegerRow 8 5 2 201512,
    decodeIntegerRow 8 5 2 351560,
    decodeIntegerRow 8 5 2 226552,
    decodeIntegerRow 8 5 2 189012,
    decodeIntegerRow 8 5 2 193812,
    decodeIntegerRow 8 5 2 226572,
    decodeIntegerRow 8 5 2 351564]

private def rows4_1_2 : List (List ℤ) := [decodeIntegerRow 8 5 2 196312,
    decodeIntegerRow 8 5 2 201512,
    decodeIntegerRow 8 5 2 351560,
    decodeIntegerRow 8 5 2 226552,
    decodeIntegerRow 8 5 2 189012,
    decodeIntegerRow 8 5 2 193812,
    decodeIntegerRow 8 5 2 226572,
    decodeIntegerRow 8 5 2 351564]

private def rows0_1_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 2632,
    decodeIntegerRow 8 3 1 1336,
    decodeIntegerRow 8 3 1 5710,
    decodeIntegerRow 8 3 1 4090,
    decodeIntegerRow 8 3 1 3270,
    decodeIntegerRow 8 3 1 3250,
    decodeIntegerRow 8 3 1 3256,
    decodeIntegerRow 8 3 1 3272]

private def rows1_1_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 3277,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3281]

private def rows2_1_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 2632,
    decodeIntegerRow 8 3 1 5224,
    decodeIntegerRow 8 3 1 850,
    decodeIntegerRow 8 3 1 2470,
    decodeIntegerRow 8 3 1 3270,
    decodeIntegerRow 8 3 1 3310,
    decodeIntegerRow 8 3 1 3304,
    decodeIntegerRow 8 3 1 3288]

private def rows3_1_3 : List (List ℤ) := [decodeIntegerRow 8 5 2 195262,
    decodeIntegerRow 8 5 2 189062,
    decodeIntegerRow 8 5 2 195322,
    decodeIntegerRow 8 5 2 164062,
    decodeIntegerRow 8 5 2 196562,
    decodeIntegerRow 8 5 2 195062,
    decodeIntegerRow 8 5 2 351562,
    decodeIntegerRow 8 5 2 195314]

private def rows4_1_3 : List (List ℤ) := [decodeIntegerRow 8 5 2 195262,
    decodeIntegerRow 8 5 2 189062,
    decodeIntegerRow 8 5 2 195322,
    decodeIntegerRow 8 5 2 164062,
    decodeIntegerRow 8 5 2 196562,
    decodeIntegerRow 8 5 2 195062,
    decodeIntegerRow 8 5 2 351562,
    decodeIntegerRow 8 5 2 195314]

private def rows0_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3271,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows1_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 1093,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3277,
    decodeIntegerRow 8 3 1 3037,
    decodeIntegerRow 8 3 1 3361]

private def rows2_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3271,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3271,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 2551,
    decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 3199]

private def rows4_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3271,
    decodeIntegerRow 8 3 1 3253,
    decodeIntegerRow 8 3 1 1093,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3277,
    decodeIntegerRow 8 3 1 3037,
    decodeIntegerRow 8 3 1 3361]

private def rows0_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21346942,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 26306356,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916]

private def rows1_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 35525032,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 15183192,
    decodeIntegerRow 16 3 1 6814564,
    decodeIntegerRow 16 3 1 6473404,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 36575272,
    decodeIntegerRow 16 3 1 15108996,
    decodeIntegerRow 16 3 1 27859044,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 18253848]

private def rows2_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21346942,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 26306356,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916]

private def rows3_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 26326066,
    decodeIntegerRow 16 3 1 7168126,
    decodeIntegerRow 16 3 1 21169798,
    decodeIntegerRow 16 3 1 23060822,
    decodeIntegerRow 16 3 1 19867802,
    decodeIntegerRow 16 3 1 22231222,
    decodeIntegerRow 16 3 1 7181266,
    decodeIntegerRow 16 3 1 26286754,
    decodeIntegerRow 16 3 1 22232674,
    decodeIntegerRow 16 3 1 23174546,
    decodeIntegerRow 16 3 1 26286538,
    decodeIntegerRow 16 3 1 35865958,
    decodeIntegerRow 16 3 1 35879062,
    decodeIntegerRow 16 3 1 26325958,
    decodeIntegerRow 16 3 1 19990274,
    decodeIntegerRow 16 3 1 21168334]

private def rows4_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 26326066,
    decodeIntegerRow 16 3 1 7168126,
    decodeIntegerRow 16 3 1 21169798,
    decodeIntegerRow 16 3 1 23060822,
    decodeIntegerRow 16 3 1 19867802,
    decodeIntegerRow 16 3 1 22231222,
    decodeIntegerRow 16 3 1 7181266,
    decodeIntegerRow 16 3 1 26286754,
    decodeIntegerRow 16 3 1 22232674,
    decodeIntegerRow 16 3 1 23174546,
    decodeIntegerRow 16 3 1 26286538,
    decodeIntegerRow 16 3 1 35865958,
    decodeIntegerRow 16 3 1 35879062,
    decodeIntegerRow 16 3 1 26325958,
    decodeIntegerRow 16 3 1 19990274,
    decodeIntegerRow 16 3 1 21168334]

private def rows0_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 7705408,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21602064,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 36404680]

private def rows1_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 24880336,
    decodeIntegerRow 16 3 1 35381136,
    decodeIntegerRow 16 3 1 36325488,
    decodeIntegerRow 16 3 1 27714832,
    decodeIntegerRow 16 3 1 35302460,
    decodeIntegerRow 16 3 1 24539140,
    decodeIntegerRow 16 3 1 14964460,
    decodeIntegerRow 16 3 1 6563820,
    decodeIntegerRow 16 3 1 36481980,
    decodeIntegerRow 16 3 1 14960260,
    decodeIntegerRow 16 3 1 18503020,
    decodeIntegerRow 16 3 1 35300460,
    decodeIntegerRow 16 3 1 27719056,
    decodeIntegerRow 16 3 1 6722256,
    decodeIntegerRow 16 3 1 35379248,
    decodeIntegerRow 16 3 1 18161872]

private def rows2_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 7705408,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21484020,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21602064,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 36404680]

private def rows3_1_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293164072,
    decodeIntegerRow 16 5 2 76290039060,
    decodeIntegerRow 16 5 2 76274414312,
    decodeIntegerRow 16 5 2 76196289012,
    decodeIntegerRow 16 5 2 75805670312,
    decodeIntegerRow 16 5 2 73852537812,
    decodeIntegerRow 16 5 2 64087070312,
    decodeIntegerRow 16 5 2 15258757812,
    decodeIntegerRow 16 5 2 137329070312,
    decodeIntegerRow 16 5 2 64086757812,
    decodeIntegerRow 16 5 2 78735350312,
    decodeIntegerRow 16 5 2 75805657812,
    decodeIntegerRow 16 5 2 76196289112,
    decodeIntegerRow 16 5 2 76313476812,
    decodeIntegerRow 16 5 2 76290039064,
    decodeIntegerRow 16 5 2 76294726572]

private def rows4_1_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293164072,
    decodeIntegerRow 16 5 2 76290039060,
    decodeIntegerRow 16 5 2 76274414312,
    decodeIntegerRow 16 5 2 76196289012,
    decodeIntegerRow 16 5 2 75805670312,
    decodeIntegerRow 16 5 2 73852537812,
    decodeIntegerRow 16 5 2 64087070312,
    decodeIntegerRow 16 5 2 15258757812,
    decodeIntegerRow 16 5 2 137329070312,
    decodeIntegerRow 16 5 2 64086757812,
    decodeIntegerRow 16 5 2 78735350312,
    decodeIntegerRow 16 5 2 75805657812,
    decodeIntegerRow 16 5 2 76196289112,
    decodeIntegerRow 16 5 2 76313476812,
    decodeIntegerRow 16 5 2 76290039064,
    decodeIntegerRow 16 5 2 76294726572]

private def rows0_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 3604,
    decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3282,
    decodeIntegerRow 8 3 1 3284]

private def rows1_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3314,
    decodeIntegerRow 8 3 1 3266,
    decodeIntegerRow 8 3 1 3258,
    decodeIntegerRow 8 3 1 3318,
    decodeIntegerRow 8 3 1 6358,
    decodeIntegerRow 8 3 1 1498,
    decodeIntegerRow 8 3 1 4414,
    decodeIntegerRow 8 3 1 526]

private def rows2_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 3604,
    decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3282,
    decodeIntegerRow 8 3 1 3284]

private def rows3_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3246,
    decodeIntegerRow 8 3 1 3294,
    decodeIntegerRow 8 3 1 3302,
    decodeIntegerRow 8 3 1 3242,
    decodeIntegerRow 8 3 1 202,
    decodeIntegerRow 8 3 1 5062,
    decodeIntegerRow 8 3 1 2146,
    decodeIntegerRow 8 3 1 6034]

private def rows4_1_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3246,
    decodeIntegerRow 8 3 1 3294,
    decodeIntegerRow 8 3 1 3302,
    decodeIntegerRow 8 3 1 3242,
    decodeIntegerRow 8 3 1 202,
    decodeIntegerRow 8 3 1 5062,
    decodeIntegerRow 8 3 1 2146,
    decodeIntegerRow 8 3 1 6034]

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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle4

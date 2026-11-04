import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 7, 7.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

private def rows0_7_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 68,
    decodeIntegerRow 4 3 1 66,
    decodeIntegerRow 4 3 1 52]

private def rows1_7_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 68,
    decodeIntegerRow 4 3 1 66,
    decodeIntegerRow 4 3 1 52]

private def rows2_7_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows3_7_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows4_7_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows0_7_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows1_7_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 28]

private def rows2_7_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows3_7_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 28]

private def rows4_7_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 28]

private def rows0_7_2 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 13,
    decodeIntegerRow 4 3 1 37]

private def rows1_7_2 : List (List ℤ) := [decodeIntegerRow 4 3 1 22,
    decodeIntegerRow 4 3 1 38,
    decodeIntegerRow 4 3 1 36,
    decodeIntegerRow 4 3 1 4]

private def rows2_7_2 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67,
    decodeIntegerRow 4 3 1 43]

private def rows3_7_2 : List (List ℤ) := [decodeIntegerRow 4 3 1 22,
    decodeIntegerRow 4 3 1 38,
    decodeIntegerRow 4 3 1 44,
    decodeIntegerRow 4 3 1 76]

private def rows4_7_2 : List (List ℤ) := [decodeIntegerRow 4 3 1 22,
    decodeIntegerRow 4 3 1 38,
    decodeIntegerRow 4 3 1 44,
    decodeIntegerRow 4 3 1 76]

private def rows0_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows1_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3928,
    decodeIntegerRow 8 3 1 5224,
    decodeIntegerRow 8 3 1 3288,
    decodeIntegerRow 8 3 1 3304,
    decodeIntegerRow 8 3 1 3290,
    decodeIntegerRow 8 3 1 3310,
    decodeIntegerRow 8 3 1 4090,
    decodeIntegerRow 8 3 1 5710]

private def rows2_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows3_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 2632,
    decodeIntegerRow 8 3 1 1336,
    decodeIntegerRow 8 3 1 3272,
    decodeIntegerRow 8 3 1 3256,
    decodeIntegerRow 8 3 1 3270,
    decodeIntegerRow 8 3 1 3250,
    decodeIntegerRow 8 3 1 2470,
    decodeIntegerRow 8 3 1 850]

private def rows4_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 2632,
    decodeIntegerRow 8 3 1 1336,
    decodeIntegerRow 8 3 1 3272,
    decodeIntegerRow 8 3 1 3256,
    decodeIntegerRow 8 3 1 3270,
    decodeIntegerRow 8 3 1 3250,
    decodeIntegerRow 8 3 1 2470,
    decodeIntegerRow 8 3 1 850]

private def rows0_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 5548,
    decodeIntegerRow 8 3 1 4252,
    decodeIntegerRow 8 3 1 3766,
    decodeIntegerRow 8 3 1 5386,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 3308]

private def rows1_7_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 195310,
    decodeIntegerRow 8 5 2 195302,
    decodeIntegerRow 8 5 2 195262,
    decodeIntegerRow 8 5 2 195062,
    decodeIntegerRow 8 5 2 194062,
    decodeIntegerRow 8 5 2 189062,
    decodeIntegerRow 8 5 2 164062,
    decodeIntegerRow 8 5 2 39062]

private def rows2_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 5548,
    decodeIntegerRow 8 3 1 4252,
    decodeIntegerRow 8 3 1 3766,
    decodeIntegerRow 8 3 1 5386,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 3308]

private def rows3_7_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 195314,
    decodeIntegerRow 8 5 2 195322,
    decodeIntegerRow 8 5 2 195362,
    decodeIntegerRow 8 5 2 195562,
    decodeIntegerRow 8 5 2 196562,
    decodeIntegerRow 8 5 2 201562,
    decodeIntegerRow 8 5 2 226562,
    decodeIntegerRow 8 5 2 351562]

private def rows4_7_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 195314,
    decodeIntegerRow 8 5 2 195322,
    decodeIntegerRow 8 5 2 195362,
    decodeIntegerRow 8 5 2 195562,
    decodeIntegerRow 8 5 2 196562,
    decodeIntegerRow 8 5 2 201562,
    decodeIntegerRow 8 5 2 226562,
    decodeIntegerRow 8 5 2 351562]

private def rows0_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
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

private def rows1_7_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293945310,
    decodeIntegerRow 16 5 2 76293945302,
    decodeIntegerRow 16 5 2 76293945262,
    decodeIntegerRow 16 5 2 76293945062,
    decodeIntegerRow 16 5 2 76293944062,
    decodeIntegerRow 16 5 2 76293939062,
    decodeIntegerRow 16 5 2 76293914062,
    decodeIntegerRow 16 5 2 76293789062,
    decodeIntegerRow 16 5 2 76293164062,
    decodeIntegerRow 16 5 2 76290039062,
    decodeIntegerRow 16 5 2 76274414062,
    decodeIntegerRow 16 5 2 76196289062,
    decodeIntegerRow 16 5 2 75805664062,
    decodeIntegerRow 16 5 2 73852539062,
    decodeIntegerRow 16 5 2 64086914062,
    decodeIntegerRow 16 5 2 15258789062]

private def rows2_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
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

private def rows3_7_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293945314,
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

private def rows4_7_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 76293945314,
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

private def rows0_7_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 5710,
    decodeIntegerRow 8 3 1 3928,
    decodeIntegerRow 8 3 1 5224,
    decodeIntegerRow 8 3 1 2470,
    decodeIntegerRow 8 3 1 3290,
    decodeIntegerRow 8 3 1 3256,
    decodeIntegerRow 8 3 1 3288,
    decodeIntegerRow 8 3 1 3310]

private def rows1_7_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 3320,
    decodeIntegerRow 8 3 1 3264,
    decodeIntegerRow 8 3 1 3312,
    decodeIntegerRow 8 3 1 3300,
    decodeIntegerRow 8 3 1 6520,
    decodeIntegerRow 8 3 1 1984,
    decodeIntegerRow 8 3 1 5872,
    decodeIntegerRow 8 3 1 4900]

private def rows2_7_6 : List (List ℤ) := [decodeIntegerRow 8 5 2 200312,
    decodeIntegerRow 8 5 2 187812,
    decodeIntegerRow 8 5 2 320312,
    decodeIntegerRow 8 5 2 7812,
    decodeIntegerRow 8 5 2 195612,
    decodeIntegerRow 8 5 2 195112,
    decodeIntegerRow 8 5 2 195300,
    decodeIntegerRow 8 5 2 195320]

private def rows3_7_6 : List (List ℤ) := [decodeIntegerRow 8 5 2 195624,
    decodeIntegerRow 8 5 2 195120,
    decodeIntegerRow 8 5 2 195600,
    decodeIntegerRow 8 5 2 195520,
    decodeIntegerRow 8 5 2 390312,
    decodeIntegerRow 8 5 2 75312,
    decodeIntegerRow 8 5 2 375312,
    decodeIntegerRow 8 5 2 325312]

private def rows4_7_6 : List (List ℤ) := [decodeIntegerRow 8 17 8 3487878856,
    decodeIntegerRow 8 17 8 3487878712,
    decodeIntegerRow 8 17 8 3487918024,
    decodeIntegerRow 8 17 8 3487876408,
    decodeIntegerRow 8 17 8 6770588104,
    decodeIntegerRow 8 17 8 3680979272,
    decodeIntegerRow 8 17 8 3476519864,
    decodeIntegerRow 8 17 8 3487210552]

private def rows0_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4224,
    decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 5560]

private def rows1_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 3308,
    decodeIntegerRow 8 3 1 3306,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 2794,
    decodeIntegerRow 8 3 1 5548,
    decodeIntegerRow 8 3 1 5386,
    decodeIntegerRow 8 3 1 4252]

private def rows2_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3496,
    decodeIntegerRow 8 3 1 4010,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 4008,
    decodeIntegerRow 8 3 1 1096,
    decodeIntegerRow 8 3 1 3370,
    decodeIntegerRow 8 3 1 3010]

private def rows3_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3496,
    decodeIntegerRow 8 3 1 4010,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 4008,
    decodeIntegerRow 8 3 1 1096,
    decodeIntegerRow 8 3 1 3370,
    decodeIntegerRow 8 3 1 3010]

private def rows4_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 2766,
    decodeIntegerRow 8 3 1 1018,
    decodeIntegerRow 8 3 1 1162,
    decodeIntegerRow 8 3 1 4226,
    decodeIntegerRow 8 3 1 1006,
    decodeIntegerRow 8 3 1 3738,
    decodeIntegerRow 8 3 1 2282,
    decodeIntegerRow 8 3 1 1186]

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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

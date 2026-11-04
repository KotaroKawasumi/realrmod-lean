import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 6, 7.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle6

private def rows0_7_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3794,
    decodeIntegerRow 8 3 1 5542,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 2334,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 2822,
    decodeIntegerRow 8 3 1 4278,
    decodeIntegerRow 8 3 1 5374]

private def rows1_7_0 : List (List ℤ) := [decodeIntegerRow 8 3 1 3794,
    decodeIntegerRow 8 3 1 5542,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 2334,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 2822,
    decodeIntegerRow 8 3 1 4278,
    decodeIntegerRow 8 3 1 5374]

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

private def rows0_7_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows1_7_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 2822,
    decodeIntegerRow 8 3 1 5542,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 4278,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 2766,
    decodeIntegerRow 8 3 1 4226,
    decodeIntegerRow 8 3 1 5374]

private def rows2_7_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467]

private def rows3_7_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3010,
    decodeIntegerRow 8 3 1 2552,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 2550,
    decodeIntegerRow 8 3 1 5464,
    decodeIntegerRow 8 3 1 3190,
    decodeIntegerRow 8 3 1 3496]

private def rows4_7_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3010,
    decodeIntegerRow 8 3 1 2552,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 2550,
    decodeIntegerRow 8 3 1 5464,
    decodeIntegerRow 8 3 1 3190,
    decodeIntegerRow 8 3 1 3496]

private def rows0_7_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows1_7_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 5216,
    decodeIntegerRow 8 3 1 3904,
    decodeIntegerRow 8 3 1 5720,
    decodeIntegerRow 8 3 1 4120,
    decodeIntegerRow 8 3 1 2608,
    decodeIntegerRow 8 3 1 1328,
    decodeIntegerRow 8 3 1 4060,
    decodeIntegerRow 8 3 1 5700]

private def rows2_7_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows3_7_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 5216,
    decodeIntegerRow 8 3 1 3904,
    decodeIntegerRow 8 3 1 5720,
    decodeIntegerRow 8 3 1 4120,
    decodeIntegerRow 8 3 1 2608,
    decodeIntegerRow 8 3 1 1328,
    decodeIntegerRow 8 3 1 4060,
    decodeIntegerRow 8 3 1 5700]

private def rows4_7_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 5216,
    decodeIntegerRow 8 3 1 3904,
    decodeIntegerRow 8 3 1 5720,
    decodeIntegerRow 8 3 1 4120,
    decodeIntegerRow 8 3 1 2608,
    decodeIntegerRow 8 3 1 1328,
    decodeIntegerRow 8 3 1 4060,
    decodeIntegerRow 8 3 1 5700]

private def rows0_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows1_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3260,
    decodeIntegerRow 8 3 1 1660,
    decodeIntegerRow 8 3 1 3320,
    decodeIntegerRow 8 3 1 6520,
    decodeIntegerRow 8 3 1 688,
    decodeIntegerRow 8 3 1 3248,
    decodeIntegerRow 8 3 1 1984,
    decodeIntegerRow 8 3 1 3264]

private def rows2_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3281,
    decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3361,
    decodeIntegerRow 8 3 1 3523,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 3289,
    decodeIntegerRow 8 3 1 3307]

private def rows3_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3260,
    decodeIntegerRow 8 3 1 1660,
    decodeIntegerRow 8 3 1 3320,
    decodeIntegerRow 8 3 1 6520,
    decodeIntegerRow 8 3 1 5872,
    decodeIntegerRow 8 3 1 3312,
    decodeIntegerRow 8 3 1 4576,
    decodeIntegerRow 8 3 1 3296]

private def rows4_7_3 : List (List ℤ) := [decodeIntegerRow 8 3 1 3260,
    decodeIntegerRow 8 3 1 1660,
    decodeIntegerRow 8 3 1 3320,
    decodeIntegerRow 8 3 1 6520,
    decodeIntegerRow 8 3 1 5872,
    decodeIntegerRow 8 3 1 3312,
    decodeIntegerRow 8 3 1 4576,
    decodeIntegerRow 8 3 1 3296]

private def rows0_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3388,
    decodeIntegerRow 8 3 1 3514,
    decodeIntegerRow 8 3 1 2548,
    decodeIntegerRow 8 3 1 1094,
    decodeIntegerRow 8 3 1 5468,
    decodeIntegerRow 8 3 1 2554,
    decodeIntegerRow 8 3 1 3028,
    decodeIntegerRow 8 3 1 3334]

private def rows1_7_4 : List (List ℤ) := [decodeIntegerRow 8 9 4 21523364,
    decodeIntegerRow 8 9 4 21523396,
    decodeIntegerRow 8 9 4 21549604,
    decodeIntegerRow 8 9 4 21759556,
    decodeIntegerRow 8 9 4 23649124,
    decodeIntegerRow 8 9 4 40655236,
    decodeIntegerRow 8 9 4 21523684,
    decodeIntegerRow 8 9 4 21526276]

private def rows2_7_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 3388,
    decodeIntegerRow 8 3 1 3514,
    decodeIntegerRow 8 3 1 2548,
    decodeIntegerRow 8 3 1 1094,
    decodeIntegerRow 8 3 1 5468,
    decodeIntegerRow 8 3 1 2554,
    decodeIntegerRow 8 3 1 3028,
    decodeIntegerRow 8 3 1 3334]

private def rows3_7_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 195314,
    decodeIntegerRow 8 5 2 195322,
    decodeIntegerRow 8 5 2 196562,
    decodeIntegerRow 8 5 2 201562,
    decodeIntegerRow 8 5 2 226562,
    decodeIntegerRow 8 5 2 351562,
    decodeIntegerRow 8 5 2 195362,
    decodeIntegerRow 8 5 2 195562]

private def rows4_7_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 195314,
    decodeIntegerRow 8 5 2 195322,
    decodeIntegerRow 8 5 2 196562,
    decodeIntegerRow 8 5 2 201562,
    decodeIntegerRow 8 5 2 226562,
    decodeIntegerRow 8 5 2 351562,
    decodeIntegerRow 8 5 2 195362,
    decodeIntegerRow 8 5 2 195562]

private def rows0_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 23117682,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 22054798,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21543124,
    decodeIntegerRow 16 3 1 21530164,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21699778]

private def rows1_7_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 137914295272,
    decodeIntegerRow 16 5 2 90957850560,
    decodeIntegerRow 16 5 2 86036288064,
    decodeIntegerRow 16 5 2 136742357752,
    decodeIntegerRow 16 5 2 66504728064,
    decodeIntegerRow 16 5 2 136939232872,
    decodeIntegerRow 16 5 2 137720545352,
    decodeIntegerRow 16 5 2 61661290560,
    decodeIntegerRow 16 5 2 61660975064,
    decodeIntegerRow 16 5 2 137720470272,
    decodeIntegerRow 16 5 2 15648607872,
    decodeIntegerRow 16 5 2 86082853064,
    decodeIntegerRow 16 5 2 15845482752,
    decodeIntegerRow 16 5 2 66551913064,
    decodeIntegerRow 16 5 2 90958165064,
    decodeIntegerRow 16 5 2 137914220352]

private def rows2_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 23117682,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 22054798,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21543124,
    decodeIntegerRow 16 3 1 21530164,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21699778]

private def rows3_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 6471460,
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

private def rows4_7_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 6471460,
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

private def rows0_7_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
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

private def rows1_7_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 76278320564,
    decodeIntegerRow 16 5 2 76390820372,
    decodeIntegerRow 16 5 2 76392382852,
    decodeIntegerRow 16 5 2 76270508060,
    decodeIntegerRow 16 5 2 66528477812,
    decodeIntegerRow 16 5 2 136840857812,
    decodeIntegerRow 16 5 2 137817407812,
    decodeIntegerRow 16 5 2 61645662812,
    decodeIntegerRow 16 5 2 76392382772,
    decodeIntegerRow 16 5 2 76317383060,
    decodeIntegerRow 16 5 2 76309570564,
    decodeIntegerRow 16 5 2 76390820252,
    decodeIntegerRow 16 5 2 137817357812,
    decodeIntegerRow 16 5 2 90942537812,
    decodeIntegerRow 16 5 2 86059727812,
    decodeIntegerRow 16 5 2 136840782812]

private def rows2_7_6 : List (List ℤ) := [decodeIntegerRow 16 5 2 137309539312,
    decodeIntegerRow 16 5 2 64184414112,
    decodeIntegerRow 16 5 2 78736131552,
    decodeIntegerRow 16 5 2 75801751560,
    decodeIntegerRow 16 5 2 63989414112,
    decodeIntegerRow 16 5 2 137348664312,
    decodeIntegerRow 16 5 2 76778314064,
    decodeIntegerRow 16 5 2 73853319072,
    decodeIntegerRow 16 5 2 63989101512,
    decodeIntegerRow 16 5 2 15239289312,
    decodeIntegerRow 16 5 2 75809564064,
    decodeIntegerRow 16 5 2 73853321552,
    decodeIntegerRow 16 5 2 15278289312,
    decodeIntegerRow 16 5 2 64184726512,
    decodeIntegerRow 16 5 2 78736134072,
    decodeIntegerRow 16 5 2 76786126560]

private def rows3_7_6 : List (List ℤ) := [decodeIntegerRow 16 9 4 926497696973192,
    decodeIntegerRow 16 9 4 926635446477832,
    decodeIntegerRow 16 9 4 926635790851528,
    decodeIntegerRow 16 9 4 926494597609272,
    decodeIntegerRow 16 9 4 845170407077512,
    decodeIntegerRow 16 9 4 1748944907020552,
    decodeIntegerRow 16 9 4 1751204342840008,
    decodeIntegerRow 16 9 4 824835480398392,
    decodeIntegerRow 16 9 4 926635790850952,
    decodeIntegerRow 16 9 4 926525591248392,
    decodeIntegerRow 16 9 4 926522491884488,
    decodeIntegerRow 16 9 4 926635446477112,
    decodeIntegerRow 16 9 4 1751204339060872,
    decodeIntegerRow 16 9 4 1028184746664712,
    decodeIntegerRow 16 9 4 1007849820090568,
    decodeIntegerRow 16 9 4 1748944902296632]

private def rows4_7_6 : List (List ℤ) := [decodeIntegerRow 16 9 4 926494597609272,
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

private def rows0_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 3283,
    decodeIntegerRow 8 3 1 3279,
    decodeIntegerRow 8 3 1 3307,
    decodeIntegerRow 8 3 1 3271,
    decodeIntegerRow 8 3 1 5467,
    decodeIntegerRow 8 3 1 4009,
    decodeIntegerRow 8 3 1 3037,
    decodeIntegerRow 8 3 1 3199]

private def rows1_7_7 : List (List ℤ) := [decodeIntegerRow 8 5 2 320312,
    decodeIntegerRow 8 5 2 382812,
    decodeIntegerRow 8 5 2 190312,
    decodeIntegerRow 8 5 2 187812,
    decodeIntegerRow 8 5 2 195112,
    decodeIntegerRow 8 5 2 195012,
    decodeIntegerRow 8 5 2 195320,
    decodeIntegerRow 8 5 2 195324]

private def rows2_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 4738,
    decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 2956,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3282,
    decodeIntegerRow 8 3 1 3284]

private def rows3_7_7 : List (List ℤ) := [decodeIntegerRow 8 3 1 4738,
    decodeIntegerRow 8 3 1 6196,
    decodeIntegerRow 8 3 1 3118,
    decodeIntegerRow 8 3 1 2956,
    decodeIntegerRow 8 3 1 3262,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3282,
    decodeIntegerRow 8 3 1 3284]

private def rows4_7_7 : List (List ℤ) := [decodeIntegerRow 8 5 2 165312,
    decodeIntegerRow 8 5 2 357812,
    decodeIntegerRow 8 5 2 227812,
    decodeIntegerRow 8 5 2 345312,
    decodeIntegerRow 8 5 2 195052,
    decodeIntegerRow 8 5 2 195264,
    decodeIntegerRow 8 5 2 195072,
    decodeIntegerRow 8 5 2 195364]

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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle6

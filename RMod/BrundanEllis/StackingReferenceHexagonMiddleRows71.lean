import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 7, 1.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

private def rows0_1_0 : List (List ℤ) := [decodeIntegerRow 2 3 1 5,
    decodeIntegerRow 2 3 1 7]

private def rows1_1_0 : List (List ℤ) := [decodeIntegerRow 2 3 1 5,
    decodeIntegerRow 2 3 1 7]

private def rows2_1_0 : List (List ℤ) := [decodeIntegerRow 2 3 1 5,
    decodeIntegerRow 2 3 1 7]

private def rows3_1_0 : List (List ℤ) := [decodeIntegerRow 2 3 1 5,
    decodeIntegerRow 2 3 1 7]

private def rows4_1_0 : List (List ℤ) := [decodeIntegerRow 2 3 1 5,
    decodeIntegerRow 2 3 1 7]

private def rows0_1_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 52,
    decodeIntegerRow 4 3 1 66,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 46]

private def rows1_1_1 : List (List ℤ) := [decodeIntegerRow 4 3 1 52,
    decodeIntegerRow 4 3 1 66,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 46]

private def rows2_1_1 : List (List ℤ) := [decodeIntegerRow 4 5 2 310,
    decodeIntegerRow 4 5 2 302,
    decodeIntegerRow 4 5 2 262,
    decodeIntegerRow 4 5 2 62]

private def rows3_1_1 : List (List ℤ) := [decodeIntegerRow 4 5 2 372,
    decodeIntegerRow 4 5 2 560,
    decodeIntegerRow 4 5 2 60,
    decodeIntegerRow 4 5 2 352]

private def rows4_1_1 : List (List ℤ) := [decodeIntegerRow 4 5 2 372,
    decodeIntegerRow 4 5 2 560,
    decodeIntegerRow 4 5 2 60,
    decodeIntegerRow 4 5 2 352]

private def rows0_1_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 3792,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 1000,
    decodeIntegerRow 8 3 1 4224,
    decodeIntegerRow 8 3 1 5392,
    decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 2280,
    decodeIntegerRow 8 3 1 1024]

private def rows1_1_2 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 5380,
    decodeIntegerRow 8 3 1 5560,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 5392,
    decodeIntegerRow 8 3 1 3740,
    decodeIntegerRow 8 3 1 2280,
    decodeIntegerRow 8 3 1 1024]

private def rows2_1_2 : List (List ℤ) := [decodeIntegerRow 8 9 4 21523364,
    decodeIntegerRow 8 9 4 21523396,
    decodeIntegerRow 8 9 4 21523684,
    decodeIntegerRow 8 9 4 21526276,
    decodeIntegerRow 8 9 4 21549604,
    decodeIntegerRow 8 9 4 21759556,
    decodeIntegerRow 8 9 4 23649124,
    decodeIntegerRow 8 9 4 40655236]

private def rows3_1_2 : List (List ℤ) := [decodeIntegerRow 8 9 4 21496792,
    decodeIntegerRow 8 9 4 21290080,
    decodeIntegerRow 8 9 4 19397600,
    decodeIntegerRow 8 9 4 2391448,
    decodeIntegerRow 8 9 4 19397592,
    decodeIntegerRow 8 9 4 40655200,
    decodeIntegerRow 8 9 4 21549280,
    decodeIntegerRow 8 9 4 21284248]

private def rows4_1_2 : List (List ℤ) := [decodeIntegerRow 8 9 4 21496792,
    decodeIntegerRow 8 9 4 21290080,
    decodeIntegerRow 8 9 4 19397600,
    decodeIntegerRow 8 9 4 2391448,
    decodeIntegerRow 8 9 4 19397592,
    decodeIntegerRow 8 9 4 40655200,
    decodeIntegerRow 8 9 4 21549280,
    decodeIntegerRow 8 9 4 21284248]

private def rows0_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 20972992,
    decodeIntegerRow 16 3 1 23126440,
    decodeIntegerRow 16 3 1 26129260,
    decodeIntegerRow 16 3 1 7233744,
    decodeIntegerRow 16 3 1 19937776,
    decodeIntegerRow 16 3 1 22035820,
    decodeIntegerRow 16 3 1 7115160,
    decodeIntegerRow 16 3 1 26483392,
    decodeIntegerRow 16 3 1 23122048,
    decodeIntegerRow 16 3 1 22075240,
    decodeIntegerRow 16 3 1 7233260,
    decodeIntegerRow 16 3 1 16917616,
    decodeIntegerRow 16 3 1 22034416,
    decodeIntegerRow 16 3 1 23113300,
    decodeIntegerRow 16 3 1 26483560,
    decodeIntegerRow 16 3 1 35931072]

private def rows1_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 18162016,
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

private def rows2_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 20972992,
    decodeIntegerRow 16 3 1 23126440,
    decodeIntegerRow 16 3 1 26129260,
    decodeIntegerRow 16 3 1 7233744,
    decodeIntegerRow 16 3 1 19937776,
    decodeIntegerRow 16 3 1 22035820,
    decodeIntegerRow 16 3 1 7115160,
    decodeIntegerRow 16 3 1 26483392,
    decodeIntegerRow 16 3 1 23122048,
    decodeIntegerRow 16 3 1 22075240,
    decodeIntegerRow 16 3 1 7233260,
    decodeIntegerRow 16 3 1 16917616,
    decodeIntegerRow 16 3 1 22034416,
    decodeIntegerRow 16 3 1 23113300,
    decodeIntegerRow 16 3 1 26483560,
    decodeIntegerRow 16 3 1 35931072]

private def rows3_1_3 : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922212792,
    decodeIntegerRow 16 9 4 926508544980160,
    decodeIntegerRow 16 9 4 926496149414080,
    decodeIntegerRow 16 9 4 926384551055608,
    decodeIntegerRow 16 9 4 925380376280000,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 835002924605752,
    decodeIntegerRow 16 9 4 102945566050240,
    decodeIntegerRow 16 9 4 925380376279992,
    decodeIntegerRow 16 9 4 936677557739200,
    decodeIntegerRow 16 9 4 1018017264245440,
    decodeIntegerRow 16 9 4 102945566044408,
    decodeIntegerRow 16 9 4 926510266586560,
    decodeIntegerRow 16 9 4 926508544507768,
    decodeIntegerRow 16 9 4 926496145162552,
    decodeIntegerRow 16 9 4 926635599532480]

private def rows4_1_3 : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922212792,
    decodeIntegerRow 16 9 4 926508544980160,
    decodeIntegerRow 16 9 4 926496149414080,
    decodeIntegerRow 16 9 4 926384551055608,
    decodeIntegerRow 16 9 4 925380376280000,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 835002924605752,
    decodeIntegerRow 16 9 4 102945566050240,
    decodeIntegerRow 16 9 4 925380376279992,
    decodeIntegerRow 16 9 4 936677557739200,
    decodeIntegerRow 16 9 4 1018017264245440,
    decodeIntegerRow 16 9 4 102945566044408,
    decodeIntegerRow 16 9 4 926510266586560,
    decodeIntegerRow 16 9 4 926508544507768,
    decodeIntegerRow 16 9 4 926496145162552,
    decodeIntegerRow 16 9 4 926635599532480]

private def rows0_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 364,
    decodeIntegerRow 8 3 1 3442,
    decodeIntegerRow 8 3 1 3604,
    decodeIntegerRow 8 3 1 3276,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3262]

private def rows1_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 4252,
    decodeIntegerRow 8 3 1 1012,
    decodeIntegerRow 8 3 1 5386,
    decodeIntegerRow 8 3 1 2794,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 3308]

private def rows2_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1822,
    decodeIntegerRow 8 3 1 364,
    decodeIntegerRow 8 3 1 3442,
    decodeIntegerRow 8 3 1 3604,
    decodeIntegerRow 8 3 1 3276,
    decodeIntegerRow 8 3 1 3278,
    decodeIntegerRow 8 3 1 3244,
    decodeIntegerRow 8 3 1 3262]

private def rows3_1_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 232812,
    decodeIntegerRow 8 5 2 37812,
    decodeIntegerRow 8 5 2 350312,
    decodeIntegerRow 8 5 2 170312,
    decodeIntegerRow 8 5 2 195064,
    decodeIntegerRow 8 5 2 195272,
    decodeIntegerRow 8 5 2 195372,
    decodeIntegerRow 8 5 2 195564]

private def rows4_1_4 : List (List ℤ) := [decodeIntegerRow 8 5 2 232812,
    decodeIntegerRow 8 5 2 37812,
    decodeIntegerRow 8 5 2 350312,
    decodeIntegerRow 8 5 2 170312,
    decodeIntegerRow 8 5 2 195064,
    decodeIntegerRow 8 5 2 195272,
    decodeIntegerRow 8 5 2 195372,
    decodeIntegerRow 8 5 2 195564]

private def rows0_1_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922265280,
    decodeIntegerRow 16 9 4 926508544507768,
    decodeIntegerRow 16 9 4 926496145162552,
    decodeIntegerRow 16 9 4 926384589319360,
    decodeIntegerRow 16 9 4 925380376280000,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 835002924605752,
    decodeIntegerRow 16 9 4 102945566050240,
    decodeIntegerRow 16 9 4 925380376279992,
    decodeIntegerRow 16 9 4 936677557739200,
    decodeIntegerRow 16 9 4 1018017264245440,
    decodeIntegerRow 16 9 4 102945566044408,
    decodeIntegerRow 16 9 4 926509922212792,
    decodeIntegerRow 16 9 4 926511643871680,
    decodeIntegerRow 16 9 4 926524039437760,
    decodeIntegerRow 16 9 4 926384551055608]

private def rows1_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 21601606,
    decodeIntegerRow 16 3 1 21350506,
    decodeIntegerRow 16 3 1 21704962,
    decodeIntegerRow 16 3 1 21563698,
    decodeIntegerRow 16 3 1 27900646,
    decodeIntegerRow 16 3 1 7705866,
    decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 21337546,
    decodeIntegerRow 16 3 1 21561754,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21355042,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 24711994,
    decodeIntegerRow 16 3 1 15146062,
    decodeIntegerRow 16 3 1 7705922]

private def rows2_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 18153268,
    decodeIntegerRow 16 3 1 6682892,
    decodeIntegerRow 16 3 1 7626216,
    decodeIntegerRow 16 3 1 27732184,
    decodeIntegerRow 16 3 1 6603188,
    decodeIntegerRow 16 3 1 24530572,
    decodeIntegerRow 16 3 1 14977576,
    decodeIntegerRow 16 3 1 7785624,
    decodeIntegerRow 16 3 1 6681864,
    decodeIntegerRow 16 3 1 18148744,
    decodeIntegerRow 16 3 1 27727948,
    decodeIntegerRow 16 3 1 7628108,
    decodeIntegerRow 16 3 1 24526024,
    decodeIntegerRow 16 3 1 6604104,
    decodeIntegerRow 16 3 1 7783628,
    decodeIntegerRow 16 3 1 14973388]

private def rows3_1_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 926494599495928,
    decodeIntegerRow 16 9 4 926635465635592,
    decodeIntegerRow 16 9 4 926384417106232,
    decodeIntegerRow 16 9 4 926497694608312,
    decodeIntegerRow 16 9 4 824835461293048,
    decodeIntegerRow 16 9 4 1748944904661512,
    decodeIntegerRow 16 9 4 101815847904312,
    decodeIntegerRow 16 9 4 845170387919032,
    decodeIntegerRow 16 9 4 926635809956872,
    decodeIntegerRow 16 9 4 926497699332232,
    decodeIntegerRow 16 9 4 926525593135048,
    decodeIntegerRow 16 9 4 926635427319352,
    decodeIntegerRow 16 9 4 1751204340953352,
    decodeIntegerRow 16 9 4 845170387919752,
    decodeIntegerRow 16 9 4 1028184727559368,
    decodeIntegerRow 16 9 4 1748944904655672]

private def rows4_1_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 926494599495928,
    decodeIntegerRow 16 9 4 926635465635592,
    decodeIntegerRow 16 9 4 926384417106232,
    decodeIntegerRow 16 9 4 926497694608312,
    decodeIntegerRow 16 9 4 824835461293048,
    decodeIntegerRow 16 9 4 1748944904661512,
    decodeIntegerRow 16 9 4 101815847904312,
    decodeIntegerRow 16 9 4 845170387919032,
    decodeIntegerRow 16 9 4 926635809956872,
    decodeIntegerRow 16 9 4 926497699332232,
    decodeIntegerRow 16 9 4 926525593135048,
    decodeIntegerRow 16 9 4 926635427319352,
    decodeIntegerRow 16 9 4 1751204340953352,
    decodeIntegerRow 16 9 4 845170387919752,
    decodeIntegerRow 16 9 4 1028184727559368,
    decodeIntegerRow 16 9 4 1748944904655672]

private def rows0_1_6 : List (List ℤ) := [decodeIntegerRow 8 5 2 196512,
    decodeIntegerRow 8 5 2 201812,
    decodeIntegerRow 8 5 2 226560,
    decodeIntegerRow 8 5 2 351572,
    decodeIntegerRow 8 5 2 226564,
    decodeIntegerRow 8 5 2 39072,
    decodeIntegerRow 8 5 2 196612,
    decodeIntegerRow 8 5 2 189312]

private def rows1_1_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 2822,
    decodeIntegerRow 8 3 1 5542,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 4278,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 2766,
    decodeIntegerRow 8 3 1 4226,
    decodeIntegerRow 8 3 1 5374]

private def rows2_1_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 2822,
    decodeIntegerRow 8 3 1 5542,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 4278,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 2766,
    decodeIntegerRow 8 3 1 4226,
    decodeIntegerRow 8 3 1 5374]

private def rows3_1_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 2822,
    decodeIntegerRow 8 3 1 5542,
    decodeIntegerRow 8 3 1 5398,
    decodeIntegerRow 8 3 1 4278,
    decodeIntegerRow 8 3 1 5554,
    decodeIntegerRow 8 3 1 2766,
    decodeIntegerRow 8 3 1 4226,
    decodeIntegerRow 8 3 1 5374]

private def rows4_1_6 : List (List ℤ) := [decodeIntegerRow 8 9 4 21523364,
    decodeIntegerRow 8 9 4 21523396,
    decodeIntegerRow 8 9 4 21523684,
    decodeIntegerRow 8 9 4 21526276,
    decodeIntegerRow 8 9 4 21549604,
    decodeIntegerRow 8 9 4 21759556,
    decodeIntegerRow 8 9 4 23649124,
    decodeIntegerRow 8 9 4 40655236]

private def rows0_1_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 28]

private def rows1_1_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 28]

private def rows2_1_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 28]

private def rows3_1_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 34,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 12,
    decodeIntegerRow 4 3 1 28]

private def rows4_1_7 : List (List ℤ) := [decodeIntegerRow 4 5 2 314,
    decodeIntegerRow 4 5 2 322,
    decodeIntegerRow 4 5 2 362,
    decodeIntegerRow 4 5 2 562]

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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

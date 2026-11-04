import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 7, 2.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

private def rows0_2_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows1_2_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows2_2_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows3_2_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows4_2_0 : List (List ℤ) := [decodeIntegerRow 4 3 1 41,
    decodeIntegerRow 4 3 1 43,
    decodeIntegerRow 4 3 1 49,
    decodeIntegerRow 4 3 1 67]

private def rows0_2_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3352,
    decodeIntegerRow 8 3 1 3550,
    decodeIntegerRow 8 3 1 4010,
    decodeIntegerRow 8 3 1 5464,
    decodeIntegerRow 8 3 1 2552,
    decodeIntegerRow 8 3 1 5470,
    decodeIntegerRow 8 3 1 3370,
    decodeIntegerRow 8 3 1 3064]

private def rows1_2_1 : List (List ℤ) := [decodeIntegerRow 8 3 1 3208,
    decodeIntegerRow 8 3 1 3010,
    decodeIntegerRow 8 3 1 2550,
    decodeIntegerRow 8 3 1 1096,
    decodeIntegerRow 8 3 1 4008,
    decodeIntegerRow 8 3 1 1090,
    decodeIntegerRow 8 3 1 3190,
    decodeIntegerRow 8 3 1 3496]

private def rows2_2_1 : List (List ℤ) := [decodeIntegerRow 8 5 2 195352,
    decodeIntegerRow 8 5 2 195064,
    decodeIntegerRow 8 5 2 195060,
    decodeIntegerRow 8 5 2 195372,
    decodeIntegerRow 8 5 2 220312,
    decodeIntegerRow 8 5 2 40312,
    decodeIntegerRow 8 5 2 37812,
    decodeIntegerRow 8 5 2 232812]

private def rows3_2_1 : List (List ℤ) := [decodeIntegerRow 8 9 4 21497440,
    decodeIntegerRow 8 9 4 21284248,
    decodeIntegerRow 8 9 4 19397592,
    decodeIntegerRow 8 9 4 2391520,
    decodeIntegerRow 8 9 4 23649120,
    decodeIntegerRow 8 9 4 2391448,
    decodeIntegerRow 8 9 4 21496792,
    decodeIntegerRow 8 9 4 21756640]

private def rows4_2_1 : List (List ℤ) := [decodeIntegerRow 8 9 4 21497440,
    decodeIntegerRow 8 9 4 21284248,
    decodeIntegerRow 8 9 4 19397592,
    decodeIntegerRow 8 9 4 2391520,
    decodeIntegerRow 8 9 4 23649120,
    decodeIntegerRow 8 9 4 2391448,
    decodeIntegerRow 8 9 4 21496792,
    decodeIntegerRow 8 9 4 21756640]

private def rows0_2_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 14977744,
    decodeIntegerRow 16 3 1 6602700,
    decodeIntegerRow 16 3 1 35419100,
    decodeIntegerRow 16 3 1 24897808,
    decodeIntegerRow 16 3 1 7784112,
    decodeIntegerRow 16 3 1 18520540,
    decodeIntegerRow 16 3 1 27732340,
    decodeIntegerRow 16 3 1 36363344,
    decodeIntegerRow 16 3 1 35420016,
    decodeIntegerRow 16 3 1 18153100,
    decodeIntegerRow 16 3 1 28073500,
    decodeIntegerRow 16 3 1 6604592,
    decodeIntegerRow 16 3 1 27727792,
    decodeIntegerRow 16 3 1 6681380,
    decodeIntegerRow 16 3 1 35261580,
    decodeIntegerRow 16 3 1 18516304]

private def rows1_2_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 20104000,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 35852368,
    decodeIntegerRow 16 3 1 16733920,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 22114580,
    decodeIntegerRow 16 3 1 19754080,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 7193920,
    decodeIntegerRow 16 3 1 21050240,
    decodeIntegerRow 16 3 1 20108368,
    decodeIntegerRow 16 3 1 22113120,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 26312980,
    decodeIntegerRow 16 3 1 35891680]

private def rows2_2_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 24897808,
    decodeIntegerRow 16 3 1 35419100,
    decodeIntegerRow 16 3 1 36444020,
    decodeIntegerRow 16 3 1 28068976,
    decodeIntegerRow 16 3 1 36363344,
    decodeIntegerRow 16 3 1 27732340,
    decodeIntegerRow 16 3 1 24526180,
    decodeIntegerRow 16 3 1 35262608,
    decodeIntegerRow 16 3 1 35261580,
    decodeIntegerRow 16 3 1 18516304,
    decodeIntegerRow 16 3 1 27727792,
    decodeIntegerRow 16 3 1 6681380,
    decodeIntegerRow 16 3 1 14973220,
    decodeIntegerRow 16 3 1 36442128,
    decodeIntegerRow 16 3 1 7626704,
    decodeIntegerRow 16 3 1 24893620]

private def rows3_2_2 : List (List ℤ) := [decodeIntegerRow 16 9 4 926522493771136,
    decodeIntegerRow 16 9 4 926384761480000,
    decodeIntegerRow 16 9 4 926384417158720,
    decodeIntegerRow 16 9 4 926525593607440,
    decodeIntegerRow 16 9 4 1007849800932160,
    decodeIntegerRow 16 9 4 104075284190336,
    decodeIntegerRow 16 9 4 101815847898480,
    decodeIntegerRow 16 9 4 1028184727558720,
    decodeIntegerRow 16 9 4 1007849800932736,
    decodeIntegerRow 16 9 4 1748944904655680,
    decodeIntegerRow 16 9 4 1751204340947520,
    decodeIntegerRow 16 9 4 1028184727559440,
    decodeIntegerRow 16 9 4 926497698859840,
    decodeIntegerRow 16 9 4 926384723268736,
    decodeIntegerRow 16 9 4 926384378842480,
    decodeIntegerRow 16 9 4 926494599968320]

private def rows4_2_2 : List (List ℤ) := [decodeIntegerRow 16 9 4 926522493771136,
    decodeIntegerRow 16 9 4 926384761480000,
    decodeIntegerRow 16 9 4 926384417158720,
    decodeIntegerRow 16 9 4 926525593607440,
    decodeIntegerRow 16 9 4 1007849800932160,
    decodeIntegerRow 16 9 4 104075284190336,
    decodeIntegerRow 16 9 4 101815847898480,
    decodeIntegerRow 16 9 4 1028184727558720,
    decodeIntegerRow 16 9 4 1007849800932736,
    decodeIntegerRow 16 9 4 1748944904655680,
    decodeIntegerRow 16 9 4 1751204340947520,
    decodeIntegerRow 16 9 4 1028184727559440,
    decodeIntegerRow 16 9 4 926497698859840,
    decodeIntegerRow 16 9 4 926384723268736,
    decodeIntegerRow 16 9 4 926384378842480,
    decodeIntegerRow 16 9 4 926494599968320]

private def rows0_2_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 7705920,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 27900640,
    decodeIntegerRow 16 3 1 36403680,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21445600,
    decodeIntegerRow 16 3 1 21484480,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146056]

private def rows1_2_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 21419680,
    decodeIntegerRow 16 3 1 21264160,
    decodeIntegerRow 16 3 1 21652960,
    decodeIntegerRow 16 3 1 21316000,
    decodeIntegerRow 16 3 1 38529504,
    decodeIntegerRow 16 3 1 10894520,
    decodeIntegerRow 16 3 1 265680,
    decodeIntegerRow 16 3 1 13020288,
    decodeIntegerRow 16 3 1 13020320,
    decodeIntegerRow 16 3 1 265760,
    decodeIntegerRow 16 3 1 32152160,
    decodeIntegerRow 16 3 1 4517280,
    decodeIntegerRow 16 3 1 21310816,
    decodeIntegerRow 16 3 1 21656200,
    decodeIntegerRow 16 3 1 21789040,
    decodeIntegerRow 16 3 1 21629632]

private def rows2_2_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712000,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 21691840,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146056]

private def rows3_2_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 21782560,
    decodeIntegerRow 16 3 1 21419680,
    decodeIntegerRow 16 3 1 21730720,
    decodeIntegerRow 16 3 1 21652960,
    decodeIntegerRow 16 3 1 42781040,
    decodeIntegerRow 16 3 1 13020288,
    decodeIntegerRow 16 3 1 38529504,
    decodeIntegerRow 16 3 1 32152200,
    decodeIntegerRow 16 3 1 42780960,
    decodeIntegerRow 16 3 1 13020320,
    decodeIntegerRow 16 3 1 38529440,
    decodeIntegerRow 16 3 1 32152160,
    decodeIntegerRow 16 3 1 21257680,
    decodeIntegerRow 16 3 1 21629632,
    decodeIntegerRow 16 3 1 21310816,
    decodeIntegerRow 16 3 1 21390520]

private def rows4_2_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 21782560,
    decodeIntegerRow 16 3 1 21419680,
    decodeIntegerRow 16 3 1 21730720,
    decodeIntegerRow 16 3 1 21652960,
    decodeIntegerRow 16 3 1 42781040,
    decodeIntegerRow 16 3 1 13020288,
    decodeIntegerRow 16 3 1 38529504,
    decodeIntegerRow 16 3 1 32152200,
    decodeIntegerRow 16 3 1 42780960,
    decodeIntegerRow 16 3 1 13020320,
    decodeIntegerRow 16 3 1 38529440,
    decodeIntegerRow 16 3 1 32152160,
    decodeIntegerRow 16 3 1 21257680,
    decodeIntegerRow 16 3 1 21629632,
    decodeIntegerRow 16 3 1 21310816,
    decodeIntegerRow 16 3 1 21390520]

private def rows0_2_4 : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922265280,
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

private def rows1_2_4 : List (List ℤ) := [decodeIntegerRow 16 3 1 21530002,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21702694,
    decodeIntegerRow 16 3 1 22054802,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 35872294,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 16740382]

private def rows2_2_4 : List (List ℤ) := [decodeIntegerRow 16 3 1 18153268,
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

private def rows3_2_4 : List (List ℤ) := [decodeIntegerRow 16 9 4 926510266639048,
    decodeIntegerRow 16 9 4 926511643871680,
    decodeIntegerRow 16 9 4 926524039437760,
    decodeIntegerRow 16 9 4 926635637796232,
    decodeIntegerRow 16 9 4 927639812571848,
    decodeIntegerRow 16 9 4 936677557739200,
    decodeIntegerRow 16 9 4 1018017264245440,
    decodeIntegerRow 16 9 4 1750074622807432,
    decodeIntegerRow 16 9 4 926508544507768,
    decodeIntegerRow 16 9 4 926509922265280,
    decodeIntegerRow 16 9 4 926384589319360,
    decodeIntegerRow 16 9 4 926496145162552,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 925380376280000,
    decodeIntegerRow 16 9 4 102945566050240,
    decodeIntegerRow 16 9 4 835002924605752]

private def rows4_2_4 : List (List ℤ) := [decodeIntegerRow 16 9 4 926510266639048,
    decodeIntegerRow 16 9 4 926511643871680,
    decodeIntegerRow 16 9 4 926524039437760,
    decodeIntegerRow 16 9 4 926635637796232,
    decodeIntegerRow 16 9 4 927639812571848,
    decodeIntegerRow 16 9 4 936677557739200,
    decodeIntegerRow 16 9 4 1018017264245440,
    decodeIntegerRow 16 9 4 1750074622807432,
    decodeIntegerRow 16 9 4 926508544507768,
    decodeIntegerRow 16 9 4 926509922265280,
    decodeIntegerRow 16 9 4 926384589319360,
    decodeIntegerRow 16 9 4 926496145162552,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 925380376280000,
    decodeIntegerRow 16 9 4 102945566050240,
    decodeIntegerRow 16 9 4 835002924605752]

private def rows0_2_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 76762664064,
    decodeIntegerRow 16 5 2 78833164072,
    decodeIntegerRow 16 5 2 88500194112,
    decodeIntegerRow 16 5 2 137333014312,
    decodeIntegerRow 16 5 2 75786164064,
    decodeIntegerRow 16 5 2 73950039072,
    decodeIntegerRow 16 5 2 64086134112,
    decodeIntegerRow 16 5 2 15262689312,
    decodeIntegerRow 16 5 2 88501759112,
    decodeIntegerRow 16 5 2 15262701312,
    decodeIntegerRow 16 5 2 76801789064,
    decodeIntegerRow 16 5 2 73950351552,
    decodeIntegerRow 16 5 2 88500196512,
    decodeIntegerRow 16 5 2 15254889312,
    decodeIntegerRow 16 5 2 76762726560,
    decodeIntegerRow 16 5 2 73755039072]

private def rows1_2_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21700426,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346132]

private def rows2_2_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 18520684,
    decodeIntegerRow 16 3 1 36363884,
    decodeIntegerRow 16 3 1 35420556,
    decodeIntegerRow 16 3 1 28073356,
    decodeIntegerRow 16 3 1 24893440,
    decodeIntegerRow 16 3 1 6604160,
    decodeIntegerRow 16 3 1 7783680,
    decodeIntegerRow 16 3 1 15314560,
    decodeIntegerRow 16 3 1 36443588,
    decodeIntegerRow 16 3 1 18148732,
    decodeIntegerRow 16 3 1 27727972,
    decodeIntegerRow 16 3 1 35261148,
    decodeIntegerRow 16 3 1 36364800,
    decodeIntegerRow 16 3 1 18516160,
    decodeIntegerRow 16 3 1 28069120,
    decodeIntegerRow 16 3 1 35418560]

private def rows3_2_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 835002924606040,
    decodeIntegerRow 16 9 4 1750074622804512,
    decodeIntegerRow 16 9 4 925380376277080,
    decodeIntegerRow 16 9 4 936677557738912,
    decodeIntegerRow 16 9 4 926508546869728,
    decodeIntegerRow 16 9 4 926509903107160,
    decodeIntegerRow 16 9 4 926384570213728,
    decodeIntegerRow 16 9 4 926496147052120,
    decodeIntegerRow 16 9 4 102945566047320,
    decodeIntegerRow 16 9 4 1018017264245728,
    decodeIntegerRow 16 9 4 916342631112280,
    decodeIntegerRow 16 9 4 927639812568928,
    decodeIntegerRow 16 9 4 926510247480928,
    decodeIntegerRow 16 9 4 926511646233640,
    decodeIntegerRow 16 9 4 926524041327328,
    decodeIntegerRow 16 9 4 926635618690600]

private def rows4_2_5 : List (List ℤ) := [decodeIntegerRow 16 9 4 835002924606040,
    decodeIntegerRow 16 9 4 1750074622804512,
    decodeIntegerRow 16 9 4 925380376277080,
    decodeIntegerRow 16 9 4 936677557738912,
    decodeIntegerRow 16 9 4 926508546869728,
    decodeIntegerRow 16 9 4 926509903107160,
    decodeIntegerRow 16 9 4 926384570213728,
    decodeIntegerRow 16 9 4 926496147052120,
    decodeIntegerRow 16 9 4 102945566047320,
    decodeIntegerRow 16 9 4 1018017264245728,
    decodeIntegerRow 16 9 4 916342631112280,
    decodeIntegerRow 16 9 4 927639812568928,
    decodeIntegerRow 16 9 4 926510247480928,
    decodeIntegerRow 16 9 4 926511646233640,
    decodeIntegerRow 16 9 4 926524041327328,
    decodeIntegerRow 16 9 4 926635618690600]

private def rows0_2_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 5560,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 2820]

private def rows1_2_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 5560,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 2820]

private def rows2_2_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 5560,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 2820]

private def rows3_2_6 : List (List ℤ) := [decodeIntegerRow 8 3 1 2768,
    decodeIntegerRow 8 3 1 1168,
    decodeIntegerRow 8 3 1 4280,
    decodeIntegerRow 8 3 1 5560,
    decodeIntegerRow 8 3 1 1024,
    decodeIntegerRow 8 3 1 2336,
    decodeIntegerRow 8 3 1 1180,
    decodeIntegerRow 8 3 1 2820]

private def rows4_2_6 : List (List ℤ) := [decodeIntegerRow 8 9 4 21523364,
    decodeIntegerRow 8 9 4 21523396,
    decodeIntegerRow 8 9 4 23649124,
    decodeIntegerRow 8 9 4 40655236,
    decodeIntegerRow 8 9 4 21523684,
    decodeIntegerRow 8 9 4 21526276,
    decodeIntegerRow 8 9 4 21549604,
    decodeIntegerRow 8 9 4 21759556]

private def rows0_2_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 52,
    decodeIntegerRow 4 3 1 68,
    decodeIntegerRow 4 3 1 14,
    decodeIntegerRow 4 3 1 34]

private def rows1_2_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 52,
    decodeIntegerRow 4 3 1 46,
    decodeIntegerRow 4 3 1 68,
    decodeIntegerRow 4 3 1 66]

private def rows2_2_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 52,
    decodeIntegerRow 4 3 1 68,
    decodeIntegerRow 4 3 1 66,
    decodeIntegerRow 4 3 1 46]

private def rows3_2_7 : List (List ℤ) := [decodeIntegerRow 4 3 1 52,
    decodeIntegerRow 4 3 1 46,
    decodeIntegerRow 4 3 1 68,
    decodeIntegerRow 4 3 1 66]

private def rows4_2_7 : List (List ℤ) := [decodeIntegerRow 4 5 2 314,
    decodeIntegerRow 4 5 2 62,
    decodeIntegerRow 4 5 2 322,
    decodeIntegerRow 4 5 2 262]

def rowsB2 : ℕ → ℕ → List (List ℤ)
  | 0, 0 => rows0_2_0
  | 1, 0 => rows1_2_0
  | 2, 0 => rows2_2_0
  | 3, 0 => rows3_2_0
  | 4, 0 => rows4_2_0
  | 0, 1 => rows0_2_1
  | 1, 1 => rows1_2_1
  | 2, 1 => rows2_2_1
  | 3, 1 => rows3_2_1
  | 4, 1 => rows4_2_1
  | 0, 2 => rows0_2_2
  | 1, 2 => rows1_2_2
  | 2, 2 => rows2_2_2
  | 3, 2 => rows3_2_2
  | 4, 2 => rows4_2_2
  | 0, 3 => rows0_2_3
  | 1, 3 => rows1_2_3
  | 2, 3 => rows2_2_3
  | 3, 3 => rows3_2_3
  | 4, 3 => rows4_2_3
  | 0, 4 => rows0_2_4
  | 1, 4 => rows1_2_4
  | 2, 4 => rows2_2_4
  | 3, 4 => rows3_2_4
  | 4, 4 => rows4_2_4
  | 0, 5 => rows0_2_5
  | 1, 5 => rows1_2_5
  | 2, 5 => rows2_2_5
  | 3, 5 => rows3_2_5
  | 4, 5 => rows4_2_5
  | 0, 6 => rows0_2_6
  | 1, 6 => rows1_2_6
  | 2, 6 => rows2_2_6
  | 3, 6 => rows3_2_6
  | 4, 6 => rows4_2_6
  | 0, 7 => rows0_2_7
  | 1, 7 => rows1_2_7
  | 2, 7 => rows2_2_7
  | 3, 7 => rows3_2_7
  | 4, 7 => rows4_2_7
  | _, _ => []

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle7

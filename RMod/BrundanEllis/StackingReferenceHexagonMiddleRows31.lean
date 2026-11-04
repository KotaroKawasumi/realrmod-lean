import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding

/-! Intermediate integer matrices for labels 3, 1.
The certificates check these candidates against the actual reference maps. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle3

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

private def rows0_1_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 18166408,
    decodeIntegerRow 16 3 1 6722204,
    decodeIntegerRow 16 3 1 7744316,
    decodeIntegerRow 16 3 1 28086472,
    decodeIntegerRow 16 3 1 7667528,
    decodeIntegerRow 16 3 1 27714844,
    decodeIntegerRow 16 3 1 24543676,
    decodeIntegerRow 16 3 1 36482952,
    decodeIntegerRow 16 3 1 7746204,
    decodeIntegerRow 16 3 1 14964472,
    decodeIntegerRow 16 3 1 18161848,
    decodeIntegerRow 16 3 1 36325436,
    decodeIntegerRow 16 3 1 24539164,
    decodeIntegerRow 16 3 1 6564792,
    decodeIntegerRow 16 3 1 7665528,
    decodeIntegerRow 16 3 1 15327676]

private def rows1_1_1 : List (List ℤ) := [decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 35872996,
    decodeIntegerRow 16 3 1 20991676,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21516796,
    decodeIntegerRow 16 3 1 21503676,
    decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 16742578,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 21346222,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21529918]

private def rows2_1_1 : List (List ℤ) := [decodeIntegerRow 16 5 2 76786101312,
    decodeIntegerRow 16 5 2 73853164112,
    decodeIntegerRow 16 5 2 64184571552,
    decodeIntegerRow 16 5 2 137348639064,
    decodeIntegerRow 16 5 2 78735976512,
    decodeIntegerRow 16 5 2 76778351312,
    decodeIntegerRow 16 5 2 137309564064,
    decodeIntegerRow 16 5 2 88598634072,
    decodeIntegerRow 16 5 2 73853476512,
    decodeIntegerRow 16 5 2 76786164312,
    decodeIntegerRow 16 5 2 137348626560,
    decodeIntegerRow 16 5 2 64184569072,
    decodeIntegerRow 16 5 2 76778289312,
    decodeIntegerRow 16 5 2 78736289112,
    decodeIntegerRow 16 5 2 88598631552,
    decodeIntegerRow 16 5 2 137309576560]

private def rows3_1_1 : List (List ℤ) := [decodeIntegerRow 16 17 8 22983573322075517424,
    decodeIntegerRow 16 17 8 1431211525561807344,
    decodeIntegerRow 16 17 8 24335256915742631184,
    decodeIntegerRow 16 17 8 24409832562097349904,
    decodeIntegerRow 16 17 8 24330579809882191344,
    decodeIntegerRow 16 17 8 24330321762662970864,
    decodeIntegerRow 16 17 8 24330595993639493904,
    decodeIntegerRow 16 17 8 24330596886536446224,
    decodeIntegerRow 16 17 8 47229980349718860032,
    decodeIntegerRow 16 17 8 25677618547025932288,
    decodeIntegerRow 16 17 8 24251359313570854912,
    decodeIntegerRow 16 17 8 24325934959946955008,
    decodeIntegerRow 16 17 8 24330870113003892992,
    decodeIntegerRow 16 17 8 24330612065784598528,
    decodeIntegerRow 16 17 8 24330594989130422272,
    decodeIntegerRow 16 17 8 24330595882027374848]

private def rows4_1_1 : List (List ℤ) := [decodeIntegerRow 16 17 8 22983573322075517424,
    decodeIntegerRow 16 17 8 1431211525561807344,
    decodeIntegerRow 16 17 8 24335256915742631184,
    decodeIntegerRow 16 17 8 24409832562097349904,
    decodeIntegerRow 16 17 8 24330579809882191344,
    decodeIntegerRow 16 17 8 24330321762662970864,
    decodeIntegerRow 16 17 8 24330595993639493904,
    decodeIntegerRow 16 17 8 24330596886536446224,
    decodeIntegerRow 16 17 8 47229980349718860032,
    decodeIntegerRow 16 17 8 25677618547025932288,
    decodeIntegerRow 16 17 8 24251359313570854912,
    decodeIntegerRow 16 17 8 24325934959946955008,
    decodeIntegerRow 16 17 8 24330870113003892992,
    decodeIntegerRow 16 17 8 24330612065784598528,
    decodeIntegerRow 16 17 8 24330594989130422272,
    decodeIntegerRow 16 17 8 24330595882027374848]

private def rows0_1_2 : List (List ℤ) := [decodeIntegerRow 16 5 2 136840782812,
    decodeIntegerRow 16 5 2 61645662812,
    decodeIntegerRow 16 5 2 66528162812,
    decodeIntegerRow 16 5 2 14770482812,
    decodeIntegerRow 16 5 2 76278320060,
    decodeIntegerRow 16 5 2 76392382852,
    decodeIntegerRow 16 5 2 76390820252,
    decodeIntegerRow 16 5 2 76317382564,
    decodeIntegerRow 16 5 2 90942537812,
    decodeIntegerRow 16 5 2 15747032812,
    decodeIntegerRow 16 5 2 137817357812,
    decodeIntegerRow 16 5 2 86059412812,
    decodeIntegerRow 16 5 2 76392382772,
    decodeIntegerRow 16 5 2 76278320564,
    decodeIntegerRow 16 5 2 76317383060,
    decodeIntegerRow 16 5 2 76390820372]

private def rows1_1_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 21522604,
    decodeIntegerRow 16 3 1 21523604,
    decodeIntegerRow 16 3 1 21523276,
    decodeIntegerRow 16 3 1 20972236,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 16563244,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 22035118,
    decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 26129182,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 21525538,
    decodeIntegerRow 16 3 1 21522658,
    decodeIntegerRow 16 3 1 21523602,
    decodeIntegerRow 16 3 1 21523282]

private def rows2_1_2 : List (List ℤ) := [decodeIntegerRow 16 3 1 18507412,
    decodeIntegerRow 16 3 1 36323976,
    decodeIntegerRow 16 3 1 35300948,
    decodeIntegerRow 16 3 1 27714664,
    decodeIntegerRow 16 3 1 18503188,
    decodeIntegerRow 16 3 1 36325976,
    decodeIntegerRow 16 3 1 35301972,
    decodeIntegerRow 16 3 1 27719224,
    decodeIntegerRow 16 3 1 6565224,
    decodeIntegerRow 16 3 1 24880492,
    decodeIntegerRow 16 3 1 14964616,
    decodeIntegerRow 16 3 1 7666988,
    decodeIntegerRow 16 3 1 36483384,
    decodeIntegerRow 16 3 1 18162028,
    decodeIntegerRow 16 3 1 28086616,
    decodeIntegerRow 16 3 1 35380652]

private def rows3_1_2 : List (List ℤ) := [decodeIntegerRow 16 9 4 926510113558120,
    decodeIntegerRow 16 9 4 926510092297240,
    decodeIntegerRow 16 9 4 926510094662120,
    decodeIntegerRow 16 9 4 926510094399640,
    decodeIntegerRow 16 9 4 925378826598040,
    decodeIntegerRow 16 9 4 916342458925720,
    decodeIntegerRow 16 9 4 834877400367640,
    decodeIntegerRow 16 9 4 102931618909720,
    decodeIntegerRow 16 9 4 925381925961952,
    decodeIntegerRow 16 9 4 916342803299488,
    decodeIntegerRow 16 9 4 835128448844512,
    decodeIntegerRow 16 9 4 102959513184928,
    decodeIntegerRow 16 9 4 926510075294368,
    decodeIntegerRow 16 9 4 926510096548768,
    decodeIntegerRow 16 9 4 926510094189728,
    decodeIntegerRow 16 9 4 926510094452128]

private def rows4_1_2 : List (List ℤ) := [decodeIntegerRow 16 9 4 926510113558120,
    decodeIntegerRow 16 9 4 926510092297240,
    decodeIntegerRow 16 9 4 926510094662120,
    decodeIntegerRow 16 9 4 926510094399640,
    decodeIntegerRow 16 9 4 925378826598040,
    decodeIntegerRow 16 9 4 916342458925720,
    decodeIntegerRow 16 9 4 834877400367640,
    decodeIntegerRow 16 9 4 102931618909720,
    decodeIntegerRow 16 9 4 925381925961952,
    decodeIntegerRow 16 9 4 916342803299488,
    decodeIntegerRow 16 9 4 835128448844512,
    decodeIntegerRow 16 9 4 102959513184928,
    decodeIntegerRow 16 9 4 926510075294368,
    decodeIntegerRow 16 9 4 926510096548768,
    decodeIntegerRow 16 9 4 926510094189728,
    decodeIntegerRow 16 9 4 926510094452128]

private def rows0_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346214,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 21503686]

private def rows1_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37465780,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 21575872]

private def rows2_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346214,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 21503686]

private def rows3_1_3 : List (List ℤ) := [decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37465780,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 21575872]

private def rows4_1_3 : List (List ℤ) := [decodeIntegerRow 16 9 4 926524041537280,
    decodeIntegerRow 16 9 4 926635618428160,
    decodeIntegerRow 16 9 4 835002924606072,
    decodeIntegerRow 16 9 4 102945566047288,
    decodeIntegerRow 16 9 4 936677557736320,
    decodeIntegerRow 16 9 4 927639812571520,
    decodeIntegerRow 16 9 4 926511663239752,
    decodeIntegerRow 16 9 4 926510268738568,
    decodeIntegerRow 16 9 4 927639812572168,
    decodeIntegerRow 16 9 4 936677557742152,
    decodeIntegerRow 16 9 4 926510264487040,
    decodeIntegerRow 16 9 4 926511624976000,
    decodeIntegerRow 16 9 4 926635618900552,
    decodeIntegerRow 16 9 4 926524041589768,
    decodeIntegerRow 16 9 4 102945566047360,
    decodeIntegerRow 16 9 4 835002924606080]

private def rows0_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1174,
    decodeIntegerRow 8 3 1 2794,
    decodeIntegerRow 8 3 1 5548,
    decodeIntegerRow 8 3 1 4252,
    decodeIntegerRow 8 3 1 3252,
    decodeIntegerRow 8 3 1 3268,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3274]

private def rows1_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 5548,
    decodeIntegerRow 8 3 1 3268,
    decodeIntegerRow 8 3 1 3766,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3252,
    decodeIntegerRow 8 3 1 2308,
    decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 1174]

private def rows2_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1174,
    decodeIntegerRow 8 3 1 2794,
    decodeIntegerRow 8 3 1 5548,
    decodeIntegerRow 8 3 1 4252,
    decodeIntegerRow 8 3 1 3252,
    decodeIntegerRow 8 3 1 3268,
    decodeIntegerRow 8 3 1 3254,
    decodeIntegerRow 8 3 1 3274]

private def rows3_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1012,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 2794,
    decodeIntegerRow 8 3 1 3306,
    decodeIntegerRow 8 3 1 3252,
    decodeIntegerRow 8 3 1 2308,
    decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 1174]

private def rows4_1_4 : List (List ℤ) := [decodeIntegerRow 8 3 1 1012,
    decodeIntegerRow 8 3 1 3292,
    decodeIntegerRow 8 3 1 2794,
    decodeIntegerRow 8 3 1 3306,
    decodeIntegerRow 8 3 1 3252,
    decodeIntegerRow 8 3 1 2308,
    decodeIntegerRow 8 3 1 3274,
    decodeIntegerRow 8 3 1 1174]

private def rows0_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21530650,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 21582328,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 20991910]

private def rows1_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
    decodeIntegerRow 16 3 1 19988818,
    decodeIntegerRow 16 3 1 26325778,
    decodeIntegerRow 16 3 1 35865814,
    decodeIntegerRow 16 3 1 21879842,
    decodeIntegerRow 16 3 1 23176006,
    decodeIntegerRow 16 3 1 26286394,
    decodeIntegerRow 16 3 1 35878882,
    decodeIntegerRow 16 3 1 7167946,
    decodeIntegerRow 16 3 1 26286898,
    decodeIntegerRow 16 3 1 23177458,
    decodeIntegerRow 16 3 1 21171254,
    decodeIntegerRow 16 3 1 7181122,
    decodeIntegerRow 16 3 1 26326246,
    decodeIntegerRow 16 3 1 19987354,
    decodeIntegerRow 16 3 1 22229762]

private def rows2_1_5 : List (List ℤ) := [decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21530650,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 21582328,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 20991910]

private def rows3_1_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 75707851564,
    decodeIntegerRow 16 5 2 73872101572,
    decodeIntegerRow 16 5 2 88504876612,
    decodeIntegerRow 16 5 2 137328321812,
    decodeIntegerRow 16 5 2 76684726564,
    decodeIntegerRow 16 5 2 78754851572,
    decodeIntegerRow 16 5 2 88497064012,
    decodeIntegerRow 16 5 2 137329883812,
    decodeIntegerRow 16 5 2 15258008812,
    decodeIntegerRow 16 5 2 88497076612,
    decodeIntegerRow 16 5 2 78754914052,
    decodeIntegerRow 16 5 2 75903476564,
    decodeIntegerRow 16 5 2 15259571812,
    decodeIntegerRow 16 5 2 88504889012,
    decodeIntegerRow 16 5 2 73872039052,
    decodeIntegerRow 16 5 2 76879726564]

private def rows4_1_5 : List (List ℤ) := [decodeIntegerRow 16 5 2 75707851564,
    decodeIntegerRow 16 5 2 73872101572,
    decodeIntegerRow 16 5 2 88504876612,
    decodeIntegerRow 16 5 2 137328321812,
    decodeIntegerRow 16 5 2 76684726564,
    decodeIntegerRow 16 5 2 78754851572,
    decodeIntegerRow 16 5 2 88497064012,
    decodeIntegerRow 16 5 2 137329883812,
    decodeIntegerRow 16 5 2 15258008812,
    decodeIntegerRow 16 5 2 88497076612,
    decodeIntegerRow 16 5 2 78754914052,
    decodeIntegerRow 16 5 2 75903476564,
    decodeIntegerRow 16 5 2 15259571812,
    decodeIntegerRow 16 5 2 88504889012,
    decodeIntegerRow 16 5 2 73872039052,
    decodeIntegerRow 16 5 2 76879726564]

private def rows0_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 24897832,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 28068964,
    decodeIntegerRow 16 3 1 7627676,
    decodeIntegerRow 16 3 1 18516328,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 36444072,
    decodeIntegerRow 16 3 1 6604644,
    decodeIntegerRow 16 3 1 15314392,
    decodeIntegerRow 16 3 1 18520516,
    decodeIntegerRow 16 3 1 7626648,
    decodeIntegerRow 16 3 1 28073512,
    decodeIntegerRow 16 3 1 6683324,
    decodeIntegerRow 16 3 1 35262552,
    decodeIntegerRow 16 3 1 18153124]

private def rows1_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 7705920,
    decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 27900664,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 21484480,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 21350668]

private def rows2_1_6 : List (List ℤ) := [decodeIntegerRow 16 3 1 24897832,
    decodeIntegerRow 16 3 1 7785084,
    decodeIntegerRow 16 3 1 6681432,
    decodeIntegerRow 16 3 1 28068964,
    decodeIntegerRow 16 3 1 7627676,
    decodeIntegerRow 16 3 1 18516328,
    decodeIntegerRow 16 3 1 27727804,
    decodeIntegerRow 16 3 1 36444072,
    decodeIntegerRow 16 3 1 36442076,
    decodeIntegerRow 16 3 1 27732328,
    decodeIntegerRow 16 3 1 24526204,
    decodeIntegerRow 16 3 1 35420072,
    decodeIntegerRow 16 3 1 14973208,
    decodeIntegerRow 16 3 1 36363396,
    decodeIntegerRow 16 3 1 7784168,
    decodeIntegerRow 16 3 1 24893596]

private def rows3_1_6 : List (List ℤ) := [decodeIntegerRow 16 9 4 916342631112640,
    decodeIntegerRow 16 9 4 927639812571840,
    decodeIntegerRow 16 9 4 102945566050240,
    decodeIntegerRow 16 9 4 1018017264245440,
    decodeIntegerRow 16 9 4 835002924605752,
    decodeIntegerRow 16 9 4 1750074622807432,
    decodeIntegerRow 16 9 4 927639812571848,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 926524039437760,
    decodeIntegerRow 16 9 4 926384589319360,
    decodeIntegerRow 16 9 4 926509922265280,
    decodeIntegerRow 16 9 4 926511643871680,
    decodeIntegerRow 16 9 4 926511644344072,
    decodeIntegerRow 16 9 4 926509922212792,
    decodeIntegerRow 16 9 4 926635637796232,
    decodeIntegerRow 16 9 4 926496145162552]

private def rows4_1_6 : List (List ℤ) := [decodeIntegerRow 16 9 4 916342631112640,
    decodeIntegerRow 16 9 4 927639812571840,
    decodeIntegerRow 16 9 4 102945566050240,
    decodeIntegerRow 16 9 4 1018017264245440,
    decodeIntegerRow 16 9 4 835002924605752,
    decodeIntegerRow 16 9 4 1750074622807432,
    decodeIntegerRow 16 9 4 927639812571848,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 926524039437760,
    decodeIntegerRow 16 9 4 926384589319360,
    decodeIntegerRow 16 9 4 926509922265280,
    decodeIntegerRow 16 9 4 926511643871680,
    decodeIntegerRow 16 9 4 926511644344072,
    decodeIntegerRow 16 9 4 926509922212792,
    decodeIntegerRow 16 9 4 926635637796232,
    decodeIntegerRow 16 9 4 926496145162552]

private def rows0_1_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 35813974,
    decodeIntegerRow 16 3 1 16919734,
    decodeIntegerRow 16 3 1 23124322,
    decodeIntegerRow 16 3 1 20972478,
    decodeIntegerRow 16 3 1 16565422,
    decodeIntegerRow 16 3 1 35932018,
    decodeIntegerRow 16 3 1 22034874,
    decodeIntegerRow 16 3 1 19935514,
    decodeIntegerRow 16 3 1 23111038,
    decodeIntegerRow 16 3 1 22035362,
    decodeIntegerRow 16 3 1 7116106,
    decodeIntegerRow 16 3 1 16561066,
    decodeIntegerRow 16 3 1 20971994,
    decodeIntegerRow 16 3 1 19922554,
    decodeIntegerRow 16 3 1 16915342,
    decodeIntegerRow 16 3 1 7234258]

private def rows1_1_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 20991892,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 16740388,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 21346294,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21504406,
    decodeIntegerRow 16 3 1 21532108]

private def rows2_1_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 35813974,
    decodeIntegerRow 16 3 1 16919734,
    decodeIntegerRow 16 3 1 23124322,
    decodeIntegerRow 16 3 1 20972478,
    decodeIntegerRow 16 3 1 16565422,
    decodeIntegerRow 16 3 1 35932018,
    decodeIntegerRow 16 3 1 22034874,
    decodeIntegerRow 16 3 1 19935514,
    decodeIntegerRow 16 3 1 23111038,
    decodeIntegerRow 16 3 1 22035362,
    decodeIntegerRow 16 3 1 7116106,
    decodeIntegerRow 16 3 1 16561066,
    decodeIntegerRow 16 3 1 20971994,
    decodeIntegerRow 16 3 1 19922554,
    decodeIntegerRow 16 3 1 16915342,
    decodeIntegerRow 16 3 1 7234258]

private def rows3_1_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 24893620,
    decodeIntegerRow 16 3 1 35420016,
    decodeIntegerRow 16 3 1 36442128,
    decodeIntegerRow 16 3 1 28073500,
    decodeIntegerRow 16 3 1 36365340,
    decodeIntegerRow 16 3 1 27727792,
    decodeIntegerRow 16 3 1 24530416,
    decodeIntegerRow 16 3 1 35261580,
    decodeIntegerRow 16 3 1 7784112,
    decodeIntegerRow 16 3 1 24526180,
    decodeIntegerRow 16 3 1 15314380,
    decodeIntegerRow 16 3 1 36363344,
    decodeIntegerRow 16 3 1 28068976,
    decodeIntegerRow 16 3 1 6602700,
    decodeIntegerRow 16 3 1 35419100,
    decodeIntegerRow 16 3 1 18148912]

private def rows4_1_7 : List (List ℤ) := [decodeIntegerRow 16 3 1 24893620,
    decodeIntegerRow 16 3 1 35420016,
    decodeIntegerRow 16 3 1 36442128,
    decodeIntegerRow 16 3 1 28073500,
    decodeIntegerRow 16 3 1 36365340,
    decodeIntegerRow 16 3 1 27727792,
    decodeIntegerRow 16 3 1 24530416,
    decodeIntegerRow 16 3 1 35261580,
    decodeIntegerRow 16 3 1 7784112,
    decodeIntegerRow 16 3 1 24526180,
    decodeIntegerRow 16 3 1 15314380,
    decodeIntegerRow 16 3 1 36363344,
    decodeIntegerRow 16 3 1 28068976,
    decodeIntegerRow 16 3 1 6602700,
    decodeIntegerRow 16 3 1 35419100,
    decodeIntegerRow 16 3 1 18148912]

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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonMiddle3

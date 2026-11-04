import RMod.BrundanEllis.StackingReferenceHexagonAtoms353
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn353
open Superfusion

theorem assocBCA_alias : HexagonAtoms353.assocBCA = HexagonAtoms353.assocBAC :=
  HexagonAtoms353.assocBCA_eq.symm.trans HexagonAtoms353.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 1669565933784056595011996549012,
    decodeIntegerRow 64 3 1 1858204003194494462403465669772,
    decodeIntegerRow 64 3 1 2098864154166978263920584347236,
    decodeIntegerRow 64 3 1 570717746244005433612490987204,
    decodeIntegerRow 64 3 1 1335827612626228648821080675524,
    decodeIntegerRow 64 3 1 2859838857236458857110329335964,
    decodeIntegerRow 64 3 1 1754348728722414610632618107532,
    decodeIntegerRow 64 3 1 1603856894664123324198426592108,
    decodeIntegerRow 64 3 1 1829943072134648434913070686092,
    decodeIntegerRow 64 3 1 1754697150734154172323097405548,
    decodeIntegerRow 64 3 1 573856396173281986542827605444,
    decodeIntegerRow 64 3 1 1335862053979446287514505846684,
    decodeIntegerRow 64 3 1 570703441388934321739967189404,
    decodeIntegerRow 64 3 1 1334776609947833617962656870716,
    decodeIntegerRow 64 3 1 1858087538935490750414501178988,
    decodeIntegerRow 64 3 1 1763768507737075361885773703028,
    decodeIntegerRow 64 3 1 1678986671754854475841271418572,
    decodeIntegerRow 64 3 1 1829943065566803728195377374292,
    decodeIntegerRow 64 3 1 2097821748563874020773088990716,
    decodeIntegerRow 64 3 1 573856449423522741207813930844,
    decodeIntegerRow 64 3 1 2098907228047041513449681169316,
    decodeIntegerRow 64 3 1 570703388283985172870916454396,
    decodeIntegerRow 64 3 1 1669915310812827166780546694828,
    decodeIntegerRow 64 3 1 1858087544184904190474244809932,
    decodeIntegerRow 64 3 1 1858203997939684946214078971308,
    decodeIntegerRow 64 3 1 1764117884749658193303633685452,
    decodeIntegerRow 64 3 1 570717799348421735101962624676,
    decodeIntegerRow 64 3 1 1334819683826293390744155004156,
    decodeIntegerRow 64 3 1 2859838910487367523737548848644,
    decodeIntegerRow 64 3 1 2097856225417474799928243080356,
    decodeIntegerRow 64 3 1 1603856888101689334757547522868,
    decodeIntegerRow 64 3 1 1679335089389834472396952773548,
    decodeIntegerRow 64 3 1 1575596276107608253325724134116,
    decodeIntegerRow 64 3 1 1669915310812827288852778935996,
    decodeIntegerRow 64 3 1 2862980432008527722985731989228,
    decodeIntegerRow 64 3 1 2098907228047040279803693285132,
    decodeIntegerRow 64 3 1 573856449423523153578191975692,
    decodeIntegerRow 64 3 1 1335862071728637226835613243412,
    decodeIntegerRow 64 3 1 1829943065566803677546604505276,
    decodeIntegerRow 64 3 1 1754697148537658161265681990684,
    decodeIntegerRow 64 3 1 1754348730902678164835691392324,
    decodeIntegerRow 64 3 1 1603856888101689385783407778276,
    decodeIntegerRow 64 3 1 1335827594875036447696013290228,
    decodeIntegerRow 64 3 1 2859838910487367111413680368108,
    decodeIntegerRow 64 3 1 1334819683826294624402597818348,
    decodeIntegerRow 64 3 1 2862966020944091160791897344012,
    decodeIntegerRow 64 3 1 1764117884749658071356746409956,
    decodeIntegerRow 64 3 1 1575479822352827497961943765436,
    decodeIntegerRow 64 3 1 1829826925628389211485284650884,
    decodeIntegerRow 64 3 1 1754348728722414458057817359324,
    decodeIntegerRow 64 3 1 573844963056053215223632168012,
    decodeIntegerRow 64 3 1 1335827612626229885854730710828,
    decodeIntegerRow 64 3 1 570717746244005844848482707412,
    decodeIntegerRow 64 3 1 1334819666125532987078879402572,
    decodeIntegerRow 64 3 1 1858204003194494421921641670436,
    decodeIntegerRow 64 3 1 1764117886508456011592732732804,
    decodeIntegerRow 64 3 1 1669915312555437000699836056284,
    decodeIntegerRow 64 3 1 1858087538935490709556618663036,
    decodeIntegerRow 64 3 1 2098907210344680100341237576748,
    decodeIntegerRow 64 3 1 570703441388934732938785700788,
    decodeIntegerRow 64 3 1 1335862053979447524563595384652,
    decodeIntegerRow 64 3 1 2859827424119230910485380422188,
    decodeIntegerRow 64 3 1 1754697150734154019873998751364,
    decodeIntegerRow 64 3 1 1603740748157863999096007415004]

def rows_inverseACB (r : LeftIndex 3 3 5) : List ℤ := rows_inverseACBData.getD (leftPosition 3 3 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 3 5) : (tripleIndices 8 1 8).map ((HexagonAtoms353.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_1_4
  · exact rows_inverseACB_eq_0_1_5
  · exact rows_inverseACB_eq_0_1_6
  · exact rows_inverseACB_eq_0_1_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_1_1_4
  · exact rows_inverseACB_eq_1_1_5
  · exact rows_inverseACB_eq_1_1_6
  · exact rows_inverseACB_eq_1_1_7
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_0_4
  · exact rows_inverseACB_eq_2_0_5
  · exact rows_inverseACB_eq_2_0_6
  · exact rows_inverseACB_eq_2_0_7
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_2_1_4
  · exact rows_inverseACB_eq_2_1_5
  · exact rows_inverseACB_eq_2_1_6
  · exact rows_inverseACB_eq_2_1_7
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_0_4
  · exact rows_inverseACB_eq_3_0_5
  · exact rows_inverseACB_eq_3_0_6
  · exact rows_inverseACB_eq_3_0_7
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3
  · exact rows_inverseACB_eq_3_1_4
  · exact rows_inverseACB_eq_3_1_5
  · exact rows_inverseACB_eq_3_1_6
  · exact rows_inverseACB_eq_3_1_7

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 1712131861324870279014072089872,
    decodeIntegerRow 64 3 1 1730972535209061703904289359380,
    decodeIntegerRow 64 3 1 1717365975665096334394099244740,
    decodeIntegerRow 64 3 1 1715274020977559995219472014384,
    decodeIntegerRow 64 3 1 1335327955613987661544651307248,
    decodeIntegerRow 64 3 1 2861422540233496774088559789100,
    decodeIntegerRow 64 3 1 1759291217172353739627351945340,
    decodeIntegerRow 64 3 1 1589842887481876905904749978576,
    decodeIntegerRow 64 3 1 1717364539869155540399142303088,
    decodeIntegerRow 64 3 1 1718414106702778165681437941740,
    decodeIntegerRow 64 3 1 1721552118500524790609176940860,
    decodeIntegerRow 64 3 1 1730972056610414315036777317456,
    decodeIntegerRow 64 3 1 1759174917701049347692121824912,
    decodeIntegerRow 64 3 1 1844189831224548713888935273940,
    decodeIntegerRow 64 3 1 2098368786842003085494624390020,
    decodeIntegerRow 64 3 1 2861383773743061982425407276464,
    decodeIntegerRow 64 3 1 1721551958967642342716248555792,
    decodeIntegerRow 64 3 1 1702711285083450826569907823380,
    decodeIntegerRow 64 3 1 1716317844627414914896007871940,
    decodeIntegerRow 64 3 1 1718409799314952077663076888624,
    decodeIntegerRow 64 3 1 2098355864678524821420945046768,
    decodeIntegerRow 64 3 1 572261280059015710003655373100,
    decodeIntegerRow 64 3 1 1674392603120158760281950748540,
    decodeIntegerRow 64 3 1 1843840932810635583836744792016,
    decodeIntegerRow 64 3 1 1716319280423358179584607345008,
    decodeIntegerRow 64 3 1 1715269713589733907187163823340,
    decodeIntegerRow 64 3 1 1712131701791987831497716428860,
    decodeIntegerRow 64 3 1 1702711763682098123930247919696,
    decodeIntegerRow 64 3 1 1674508902591463121714790220432,
    decodeIntegerRow 64 3 1 1589493989067963775852731683540,
    decodeIntegerRow 64 3 1 1335315033450509397466322918020,
    decodeIntegerRow 64 3 1 572300046549450502796526057904,
    decodeIntegerRow 64 3 1 1844189837141279237296640505660,
    decodeIntegerRow 64 3 1 1759174919667889448623998660784,
    decodeIntegerRow 64 3 1 572299993372722352129217245072,
    decodeIntegerRow 64 3 1 1335315015724332970587628469740,
    decodeIntegerRow 64 3 1 1715269713516688263131862009220,
    decodeIntegerRow 64 3 1 1716319280399074967704020959056,
    decodeIntegerRow 64 3 1 1730972057266917131704719423088,
    decodeIntegerRow 64 3 1 1721552118719366474912576169940,
    decodeIntegerRow 64 3 1 572261226880486424842500716740,
    decodeIntegerRow 64 3 1 2098355882404100873147605936336,
    decodeIntegerRow 64 3 1 1589842881581356603109120415728,
    decodeIntegerRow 64 3 1 1759291219144597247429920040980,
    decodeIntegerRow 64 3 1 1730972535865586756814495561340,
    decodeIntegerRow 64 3 1 1712131861106036006791421890864,
    decodeIntegerRow 64 3 1 1718409799387798419102511082512,
    decodeIntegerRow 64 3 1 1716317844603067464982207955500,
    decodeIntegerRow 64 3 1 1844189837141279232212822873660,
    decodeIntegerRow 64 3 1 1759174919667889463874934996144,
    decodeIntegerRow 64 3 1 572299993372722352693301463952,
    decodeIntegerRow 64 3 1 1335315015724332968890726767340,
    decodeIntegerRow 64 3 1 1715269713516687851342633817220,
    decodeIntegerRow 64 3 1 1716319280399076203029864123216,
    decodeIntegerRow 64 3 1 1730972057266917177395541152368,
    decodeIntegerRow 64 3 1 1721552118719366337463538275540,
    decodeIntegerRow 64 3 1 572261226880486424276866815940,
    decodeIntegerRow 64 3 1 2098355882404100871455353279696,
    decodeIntegerRow 64 3 1 1589842881581356598025474970608,
    decodeIntegerRow 64 3 1 1759291219144597232178467144980,
    decodeIntegerRow 64 3 1 1730972535865586710998149596540,
    decodeIntegerRow 64 3 1 1712131861106035869718956703024,
    decodeIntegerRow 64 3 1 1718409799387798007327230027792,
    decodeIntegerRow 64 3 1 1716317844603066229614523379500]

def rows_innerACB (r : LeftIndex 3 3 5) : List ℤ := rows_innerACBData.getD (leftPosition 3 3 5 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 3 3 5) : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_0_4
  · exact rows_innerACB_eq_0_0_5
  · exact rows_innerACB_eq_0_0_6
  · exact rows_innerACB_eq_0_0_7
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_1_2
  · exact rows_innerACB_eq_0_1_3
  · exact rows_innerACB_eq_0_1_4
  · exact rows_innerACB_eq_0_1_5
  · exact rows_innerACB_eq_0_1_6
  · exact rows_innerACB_eq_0_1_7
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_1_0_4
  · exact rows_innerACB_eq_1_0_5
  · exact rows_innerACB_eq_1_0_6
  · exact rows_innerACB_eq_1_0_7
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_1_1_2
  · exact rows_innerACB_eq_1_1_3
  · exact rows_innerACB_eq_1_1_4
  · exact rows_innerACB_eq_1_1_5
  · exact rows_innerACB_eq_1_1_6
  · exact rows_innerACB_eq_1_1_7
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_0_2
  · exact rows_innerACB_eq_2_0_3
  · exact rows_innerACB_eq_2_0_4
  · exact rows_innerACB_eq_2_0_5
  · exact rows_innerACB_eq_2_0_6
  · exact rows_innerACB_eq_2_0_7
  · exact rows_innerACB_eq_2_1_0
  · exact rows_innerACB_eq_2_1_1
  · exact rows_innerACB_eq_2_1_2
  · exact rows_innerACB_eq_2_1_3
  · exact rows_innerACB_eq_2_1_4
  · exact rows_innerACB_eq_2_1_5
  · exact rows_innerACB_eq_2_1_6
  · exact rows_innerACB_eq_2_1_7
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_0_2
  · exact rows_innerACB_eq_3_0_3
  · exact rows_innerACB_eq_3_0_4
  · exact rows_innerACB_eq_3_0_5
  · exact rows_innerACB_eq_3_0_6
  · exact rows_innerACB_eq_3_0_7
  · exact rows_innerACB_eq_3_1_0
  · exact rows_innerACB_eq_3_1_1
  · exact rows_innerACB_eq_3_1_2
  · exact rows_innerACB_eq_3_1_3
  · exact rows_innerACB_eq_3_1_4
  · exact rows_innerACB_eq_3_1_5
  · exact rows_innerACB_eq_3_1_6
  · exact rows_innerACB_eq_3_1_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 64 3 1 1985922194862547137962642155000,
    decodeIntegerRow 64 3 1 2825473560327419520176361335712,
    decodeIntegerRow 64 3 1 2906765454827278525752039167456,
    decodeIntegerRow 64 3 1 2239101836455517062640654702680,
    decodeIntegerRow 64 3 1 2900821314636404966355618435960,
    decodeIntegerRow 64 3 1 2211965316155370459892822048672,
    decodeIntegerRow 64 3 1 1956459673264827970290004320736,
    decodeIntegerRow 64 3 1 2812551447757030866616379581400,
    decodeIntegerRow 64 3 1 608210209040406668365061958944,
    decodeIntegerRow 64 3 1 1985922206002473416480356573480,
    decodeIntegerRow 64 3 1 1194581960836388455302595555720,
    decodeIntegerRow 64 3 1 2906765509820796050201066707808,
    decodeIntegerRow 64 3 1 1221718528405745908265853247456,
    decodeIntegerRow 64 3 1 2900821259335492530727477624920,
    decodeIntegerRow 64 3 1 621132424026924708000821923320,
    decodeIntegerRow 64 3 1 1956459660770445323666787639712,
    decodeIntegerRow 64 3 1 1477073228913684443476978385248,
    decodeIntegerRow 64 3 1 620771509138574310906505091720,
    decodeIntegerRow 64 3 1 533196567527562853854084010200,
    decodeIntegerRow 64 3 1 1221791570200905344918481243616,
    decodeIntegerRow 64 3 1 2907103345472391709108656826272,
    decodeIntegerRow 64 3 1 2239183836357302721270151857400,
    decodeIntegerRow 64 3 1 1985762981045671614826039052200,
    decodeIntegerRow 64 3 1 2825110782552688967249947245344,
    decodeIntegerRow 64 3 1 2812912259645640011991306444120,
    decodeIntegerRow 64 3 1 1477073241415464346304604883936,
    decodeIntegerRow 64 3 1 2211892225826813066107380359008,
    decodeIntegerRow 64 3 1 533196622812776502521133617160,
    decodeIntegerRow 64 3 1 1194499960931208064051813648600,
    decodeIntegerRow 64 3 1 2907103400481430130748011445216,
    decodeIntegerRow 64 3 1 608572986831903347788364996448,
    decodeIntegerRow 64 3 1 1985762992178586064557585130120,
    decodeIntegerRow 64 3 1 526580419811081790224722444680,
    decodeIntegerRow 64 3 1 2239183859361303136298819757472,
    decodeIntegerRow 64 3 1 1985762992178587261124905632736,
    decodeIntegerRow 64 3 1 608572986831903638211855765800,
    decodeIntegerRow 64 3 1 1477073241415463163684477255160,
    decodeIntegerRow 64 3 1 2812912259645639753367302166368,
    decodeIntegerRow 64 3 1 2900487197479736516532816193824,
    decodeIntegerRow 64 3 1 1221791594465700696441941594200,
    decodeIntegerRow 64 3 1 1194499983935208479080540904224,
    decodeIntegerRow 64 3 1 526580474820121339234282637400,
    decodeIntegerRow 64 3 1 2825110782552689257673425991160,
    decodeIntegerRow 64 3 1 1985762981045670418258773513568,
    decodeIntegerRow 64 3 1 620771509138574052282487328544,
    decodeIntegerRow 64 3 1 1477073228913685626097161589720,
    decodeIntegerRow 64 3 1 2211892250091608417630900396920,
    decodeIntegerRow 64 3 1 2900487252764949096407638163808,
    decodeIntegerRow 64 3 1 532862560957019419613132333472,
    decodeIntegerRow 64 3 1 2211965291886765298861082304520,
    decodeIntegerRow 64 3 1 1956459660770446506676401991000,
    decodeIntegerRow 64 3 1 621132424026924966787714989344,
    decodeIntegerRow 64 3 1 1985922206002474612656124092832,
    decodeIntegerRow 64 3 1 608210209040406958616710214280,
    decodeIntegerRow 64 3 1 526918310471715870683163121880,
    decodeIntegerRow 64 3 1 2239101859456122744683346021664,
    decodeIntegerRow 64 3 1 1221718504137140747234053832920,
    decodeIntegerRow 64 3 1 532862505656108052619495973664,
    decodeIntegerRow 64 3 1 2812551447757031125403286140832,
    decodeIntegerRow 64 3 1 1956459673264826787280334375560,
    decodeIntegerRow 64 3 1 2825473560327419810427997575080,
    decodeIntegerRow 64 3 1 1985922194862545941786929581536,
    decodeIntegerRow 64 3 1 1194581983836994137345346247008,
    decodeIntegerRow 64 3 1 526918365465234522679404352760]

def rows_assocBAC (r : RightIndex 5 3 3) : List ℤ := rows_assocBACData.getD (rightPosition 5 3 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 5 3 3) : (tripleIndices 8 1 8).map ((HexagonAtoms353.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_0_1_4
  · exact rows_assocBAC_eq_0_1_5
  · exact rows_assocBAC_eq_0_1_6
  · exact rows_assocBAC_eq_0_1_7
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_0_4
  · exact rows_assocBAC_eq_1_0_5
  · exact rows_assocBAC_eq_1_0_6
  · exact rows_assocBAC_eq_1_0_7
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3
  · exact rows_assocBAC_eq_1_1_4
  · exact rows_assocBAC_eq_1_1_5
  · exact rows_assocBAC_eq_1_1_6
  · exact rows_assocBAC_eq_1_1_7
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_2_0_4
  · exact rows_assocBAC_eq_2_0_5
  · exact rows_assocBAC_eq_2_0_6
  · exact rows_assocBAC_eq_2_0_7
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_2_1_2
  · exact rows_assocBAC_eq_2_1_3
  · exact rows_assocBAC_eq_2_1_4
  · exact rows_assocBAC_eq_2_1_5
  · exact rows_assocBAC_eq_2_1_6
  · exact rows_assocBAC_eq_2_1_7
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3
  · exact rows_assocBAC_eq_3_0_4
  · exact rows_assocBAC_eq_3_0_5
  · exact rows_assocBAC_eq_3_0_6
  · exact rows_assocBAC_eq_3_0_7
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1
  · exact rows_assocBAC_eq_3_1_2
  · exact rows_assocBAC_eq_3_1_3
  · exact rows_assocBAC_eq_3_1_4
  · exact rows_assocBAC_eq_3_1_5
  · exact rows_assocBAC_eq_3_1_6
  · exact rows_assocBAC_eq_3_1_7

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 64 3 1 1712131861324870279014072089872,
    decodeIntegerRow 64 3 1 1730972535209061703904289359380,
    decodeIntegerRow 64 3 1 1717365975665096334394099244740,
    decodeIntegerRow 64 3 1 1715274020977559995219472014384,
    decodeIntegerRow 64 3 1 1335327955613987661544651307248,
    decodeIntegerRow 64 3 1 2861422540233496774088559789100,
    decodeIntegerRow 64 3 1 1759291217172353739627351945340,
    decodeIntegerRow 64 3 1 1589842887481876905904749978576,
    decodeIntegerRow 64 3 1 1717364539869155540399142303088,
    decodeIntegerRow 64 3 1 1718414106702778165681437941740,
    decodeIntegerRow 64 3 1 1721552118500524790609176940860,
    decodeIntegerRow 64 3 1 1730972056610414315036777317456,
    decodeIntegerRow 64 3 1 1759174917701049347692121824912,
    decodeIntegerRow 64 3 1 1844189831224548713888935273940,
    decodeIntegerRow 64 3 1 2098368786842003085494624390020,
    decodeIntegerRow 64 3 1 2861383773743061982425407276464,
    decodeIntegerRow 64 3 1 1721551958967642342716248555792,
    decodeIntegerRow 64 3 1 1702711285083450826569907823380,
    decodeIntegerRow 64 3 1 1716317844627414914896007871940,
    decodeIntegerRow 64 3 1 1718409799314952077663076888624,
    decodeIntegerRow 64 3 1 2098355864678524821420945046768,
    decodeIntegerRow 64 3 1 572261280059015710003655373100,
    decodeIntegerRow 64 3 1 1674392603120158760281950748540,
    decodeIntegerRow 64 3 1 1843840932810635583836744792016,
    decodeIntegerRow 64 3 1 1716319280423358179584607345008,
    decodeIntegerRow 64 3 1 1715269713589733907187163823340,
    decodeIntegerRow 64 3 1 1712131701791987831497716428860,
    decodeIntegerRow 64 3 1 1702711763682098123930247919696,
    decodeIntegerRow 64 3 1 1674508902591463121714790220432,
    decodeIntegerRow 64 3 1 1589493989067963775852731683540,
    decodeIntegerRow 64 3 1 1335315033450509397466322918020,
    decodeIntegerRow 64 3 1 572300046549450502796526057904,
    decodeIntegerRow 64 3 1 1844189837141279237296640505660,
    decodeIntegerRow 64 3 1 1759174919667889448623998660784,
    decodeIntegerRow 64 3 1 572299993372722352129217245072,
    decodeIntegerRow 64 3 1 1335315015724332970587628469740,
    decodeIntegerRow 64 3 1 1715269713516688263131862009220,
    decodeIntegerRow 64 3 1 1716319280399074967704020959056,
    decodeIntegerRow 64 3 1 1730972057266917131704719423088,
    decodeIntegerRow 64 3 1 1721552118719366474912576169940,
    decodeIntegerRow 64 3 1 572261226880486424842500716740,
    decodeIntegerRow 64 3 1 2098355882404100873147605936336,
    decodeIntegerRow 64 3 1 1589842881581356603109120415728,
    decodeIntegerRow 64 3 1 1759291219144597247429920040980,
    decodeIntegerRow 64 3 1 1730972535865586756814495561340,
    decodeIntegerRow 64 3 1 1712131861106036006791421890864,
    decodeIntegerRow 64 3 1 1718409799387798419102511082512,
    decodeIntegerRow 64 3 1 1716317844603067464982207955500,
    decodeIntegerRow 64 3 1 1844189837141279232212822873660,
    decodeIntegerRow 64 3 1 1759174919667889463874934996144,
    decodeIntegerRow 64 3 1 572299993372722352693301463952,
    decodeIntegerRow 64 3 1 1335315015724332968890726767340,
    decodeIntegerRow 64 3 1 1715269713516687851342633817220,
    decodeIntegerRow 64 3 1 1716319280399076203029864123216,
    decodeIntegerRow 64 3 1 1730972057266917177395541152368,
    decodeIntegerRow 64 3 1 1721552118719366337463538275540,
    decodeIntegerRow 64 3 1 572261226880486424276866815940,
    decodeIntegerRow 64 3 1 2098355882404100871455353279696,
    decodeIntegerRow 64 3 1 1589842881581356598025474970608,
    decodeIntegerRow 64 3 1 1759291219144597232178467144980,
    decodeIntegerRow 64 3 1 1730972535865586710998149596540,
    decodeIntegerRow 64 3 1 1712131861106035869718956703024,
    decodeIntegerRow 64 3 1 1718409799387798007327230027792,
    decodeIntegerRow 64 3 1 1716317844603066229614523379500]

def rows_innerRightBAC (r : RightIndex 5 3 3) : List ℤ := rows_innerRightBACData.getD (rightPosition 5 3 3 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_1_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 5 3 3) : (tripleIndices 4 2 8).map ((HexagonAtoms353.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_0_4
  · exact rows_innerRightBAC_eq_0_0_5
  · exact rows_innerRightBAC_eq_0_0_6
  · exact rows_innerRightBAC_eq_0_0_7
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_0_1_4
  · exact rows_innerRightBAC_eq_0_1_5
  · exact rows_innerRightBAC_eq_0_1_6
  · exact rows_innerRightBAC_eq_0_1_7
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_1_0_4
  · exact rows_innerRightBAC_eq_1_0_5
  · exact rows_innerRightBAC_eq_1_0_6
  · exact rows_innerRightBAC_eq_1_0_7
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_1_1_2
  · exact rows_innerRightBAC_eq_1_1_3
  · exact rows_innerRightBAC_eq_1_1_4
  · exact rows_innerRightBAC_eq_1_1_5
  · exact rows_innerRightBAC_eq_1_1_6
  · exact rows_innerRightBAC_eq_1_1_7
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_0_2
  · exact rows_innerRightBAC_eq_2_0_3
  · exact rows_innerRightBAC_eq_2_0_4
  · exact rows_innerRightBAC_eq_2_0_5
  · exact rows_innerRightBAC_eq_2_0_6
  · exact rows_innerRightBAC_eq_2_0_7
  · exact rows_innerRightBAC_eq_2_1_0
  · exact rows_innerRightBAC_eq_2_1_1
  · exact rows_innerRightBAC_eq_2_1_2
  · exact rows_innerRightBAC_eq_2_1_3
  · exact rows_innerRightBAC_eq_2_1_4
  · exact rows_innerRightBAC_eq_2_1_5
  · exact rows_innerRightBAC_eq_2_1_6
  · exact rows_innerRightBAC_eq_2_1_7
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_0_2
  · exact rows_innerRightBAC_eq_3_0_3
  · exact rows_innerRightBAC_eq_3_0_4
  · exact rows_innerRightBAC_eq_3_0_5
  · exact rows_innerRightBAC_eq_3_0_6
  · exact rows_innerRightBAC_eq_3_0_7
  · exact rows_innerRightBAC_eq_3_1_0
  · exact rows_innerRightBAC_eq_3_1_1
  · exact rows_innerRightBAC_eq_3_1_2
  · exact rows_innerRightBAC_eq_3_1_3
  · exact rows_innerRightBAC_eq_3_1_4
  · exact rows_innerRightBAC_eq_3_1_5
  · exact rows_innerRightBAC_eq_3_1_6
  · exact rows_innerRightBAC_eq_3_1_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 64 3 1 2098013684379656462278489549508,
    decodeIntegerRow 64 3 1 2859774937798503689793797935084,
    decodeIntegerRow 64 3 1 1754544477758447161270528384612,
    decodeIntegerRow 64 3 1 1829877823182725436009625352716,
    decodeIntegerRow 64 3 1 1669757853600349919790070967284,
    decodeIntegerRow 64 3 1 1575532308671189898861816406372,
    decodeIntegerRow 64 3 1 1334972356794684661215100141076,
    decodeIntegerRow 64 3 1 570652550399470976229928580548,
    decodeIntegerRow 64 3 1 1858140030505631045304522168076,
    decodeIntegerRow 64 3 1 1763960427546275447384287141732,
    decodeIntegerRow 64 3 1 570768637235907765096501364756,
    decodeIntegerRow 64 3 1 1334623919269765210746498431292,
    decodeIntegerRow 64 3 1 2859891343554821624206255414468,
    decodeIntegerRow 64 3 1 2097664289608786956809956631316,
    decodeIntegerRow 64 3 1 1603791645715172518817336630428,
    decodeIntegerRow 64 3 1 1679182418601706739182453863436,
    decodeIntegerRow 64 3 1 2099059883313071374201337072708,
    decodeIntegerRow 64 3 1 2862915129954626991717311224684,
    decodeIntegerRow 64 3 1 1763960425794571142896257827812,
    decodeIntegerRow 64 3 1 1858140025253853059807201874316,
    decodeIntegerRow 64 3 1 1754501403878385145385869764724,
    decodeIntegerRow 64 3 1 1829892181142746107945350193892,
    decodeIntegerRow 64 3 1 2097664307350885768437534975636,
    decodeIntegerRow 64 3 1 2859891396808093920864622089028,
    decodeIntegerRow 64 3 1 1829877816617852963672686489204,
    decodeIntegerRow 64 3 1 1754544475569266751901389035548,
    decodeIntegerRow 64 3 1 573908935741885097109570543724,
    decodeIntegerRow 64 3 1 1335670153671142818502443992388,
    decodeIntegerRow 64 3 1 570652497292082429058388550332,
    decodeIntegerRow 64 3 1 1334972339101241218234076631404,
    decodeIntegerRow 64 3 1 1858151516873767658598532006372,
    decodeIntegerRow 64 3 1 1763925968441865607564244903284,
    decodeIntegerRow 64 3 1 570652497292082841593530332724,
    decodeIntegerRow 64 3 1 2098711481191272503402437561892,
    decodeIntegerRow 64 3 1 1575532303418744876915228887636,
    decodeIntegerRow 64 3 1 1763925968441865760069993041028,
    decodeIntegerRow 64 3 1 1603806003674659561631771804548,
    decodeIntegerRow 64 3 1 1754544475569266873918700748204,
    decodeIntegerRow 64 3 1 573908935741885508138440596772,
    decodeIntegerRow 64 3 1 2098013666621370899870497397196,
    decodeIntegerRow 64 3 1 1679182416414127461273787131772,
    decodeIntegerRow 64 3 1 1829892181142746148638447495084,
    decodeIntegerRow 64 3 1 2097664307350884534848196575012,
    decodeIntegerRow 64 3 1 573792423484418152387286829364,
    decodeIntegerRow 64 3 1 2099059883313070137097262600244,
    decodeIntegerRow 64 3 1 570768690337885080781433131228,
    decodeIntegerRow 64 3 1 1669723394497941494279742523564,
    decodeIntegerRow 64 3 1 1858140025253853110625923201668,
    decodeIntegerRow 64 3 1 2859891343554821212800296076724,
    decodeIntegerRow 64 3 1 1336019530683724294258496585892,
    decodeIntegerRow 64 3 1 1829892174577339925147412794836,
    decodeIntegerRow 64 3 1 1679182418601706617180638970628,
    decodeIntegerRow 64 3 1 1575543789786881490172046360068,
    decodeIntegerRow 64 3 1 1763960427546275599902432734764,
    decodeIntegerRow 64 3 1 570768637235908177255587001252,
    decodeIntegerRow 64 3 1 2099059901022748511015367810636,
    decodeIntegerRow 64 3 1 1763925966692162412362024315908,
    decodeIntegerRow 64 3 1 1575532308671189848005902710996,
    decodeIntegerRow 64 3 1 1334972356794685898193822559068,
    decodeIntegerRow 64 3 1 2863031269893041920963081405516,
    decodeIntegerRow 64 3 1 2098013684379655228563454726476,
    decodeIntegerRow 64 3 1 573908882494008383835200250532,
    decodeIntegerRow 64 3 1 1679139342534065445404625331156,
    decodeIntegerRow 64 3 1 1829877823182725476656232196092]

def rows_assocCAB (r : RightIndex 3 3 5) : List ℤ := rows_assocCABData.getD (rightPosition 3 3 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 3 5) : (tripleIndices 4 2 8).map ((HexagonAtoms353.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_0_4
  · exact rows_assocCAB_eq_2_0_5
  · exact rows_assocCAB_eq_2_0_6
  · exact rows_assocCAB_eq_2_0_7
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_0_4
  · exact rows_assocCAB_eq_3_0_5
  · exact rows_assocCAB_eq_3_0_6
  · exact rows_assocCAB_eq_3_0_7
  · exact rows_assocCAB_eq_4_0_0
  · exact rows_assocCAB_eq_4_0_1
  · exact rows_assocCAB_eq_4_0_2
  · exact rows_assocCAB_eq_4_0_3
  · exact rows_assocCAB_eq_4_0_4
  · exact rows_assocCAB_eq_4_0_5
  · exact rows_assocCAB_eq_4_0_6
  · exact rows_assocCAB_eq_4_0_7
  · exact rows_assocCAB_eq_5_0_0
  · exact rows_assocCAB_eq_5_0_1
  · exact rows_assocCAB_eq_5_0_2
  · exact rows_assocCAB_eq_5_0_3
  · exact rows_assocCAB_eq_5_0_4
  · exact rows_assocCAB_eq_5_0_5
  · exact rows_assocCAB_eq_5_0_6
  · exact rows_assocCAB_eq_5_0_7
  · exact rows_assocCAB_eq_6_0_0
  · exact rows_assocCAB_eq_6_0_1
  · exact rows_assocCAB_eq_6_0_2
  · exact rows_assocCAB_eq_6_0_3
  · exact rows_assocCAB_eq_6_0_4
  · exact rows_assocCAB_eq_6_0_5
  · exact rows_assocCAB_eq_6_0_6
  · exact rows_assocCAB_eq_6_0_7
  · exact rows_assocCAB_eq_7_0_0
  · exact rows_assocCAB_eq_7_0_1
  · exact rows_assocCAB_eq_7_0_2
  · exact rows_assocCAB_eq_7_0_3
  · exact rows_assocCAB_eq_7_0_4
  · exact rows_assocCAB_eq_7_0_5
  · exact rows_assocCAB_eq_7_0_6
  · exact rows_assocCAB_eq_7_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230101669414919104,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1712131568738645212843637889280,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1589726585069718328542338820760,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1715272586125880199319199355520,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 2098381717540610315885862301408,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1844073534696700218898277920000,
    decodeIntegerRow 64 3 1 1759407517595991823801661277472,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 1335340868586723594015732775360,
    decodeIntegerRow 64 3 1 1715271148360363011244471637680,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1730972207609064066756291733120,
    decodeIntegerRow 64 3 1 1721551772955508984598560614040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1759407517668971308242919032400,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1702711594958472751491810535360,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1718412669954502558740113843200,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1730972225334039738249540627904,
    decodeIntegerRow 64 3 1 1712131994159674971414885463360,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 2861396722385791286351301069440,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1702711612683448422985002034840,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 2098342951705790125981935431104,
    decodeIntegerRow 64 3 1 572287097687894749925999895360,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 1844073534696700172956406691808,
    decodeIntegerRow 64 3 1 1759058619246919713458615238976,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1335302102751900933418220769280,
    decodeIntegerRow 64 3 1 2861409644549558209794501987872,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1721552304731796178999821340240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 572274175524104766676004376240,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 1589726585069718282977040307840,
    decodeIntegerRow 64 3 1 1759058619174006937869680388760,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1718411236128068979399837434176,
    decodeIntegerRow 64 3 1 1716320713254230103363218355520]

def cols_right0 (r : LeftIndex 3 5 3) : List ℤ := cols_right0Data.getD (leftPosition 3 5 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 5 3) : (tripleIndices 8 1 8).map (fun j => (right0Middle3 5 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_0_4
  · exact cols_right0_eq_2_0_5
  · exact cols_right0_eq_2_0_6
  · exact cols_right0_eq_2_0_7
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_0_4
  · exact cols_right0_eq_3_0_5
  · exact cols_right0_eq_3_0_6
  · exact cols_right0_eq_3_0_7
  · exact cols_right0_eq_4_0_0
  · exact cols_right0_eq_4_0_1
  · exact cols_right0_eq_4_0_2
  · exact cols_right0_eq_4_0_3
  · exact cols_right0_eq_4_0_4
  · exact cols_right0_eq_4_0_5
  · exact cols_right0_eq_4_0_6
  · exact cols_right0_eq_4_0_7
  · exact cols_right0_eq_5_0_0
  · exact cols_right0_eq_5_0_1
  · exact cols_right0_eq_5_0_2
  · exact cols_right0_eq_5_0_3
  · exact cols_right0_eq_5_0_4
  · exact cols_right0_eq_5_0_5
  · exact cols_right0_eq_5_0_6
  · exact cols_right0_eq_5_0_7
  · exact cols_right0_eq_6_0_0
  · exact cols_right0_eq_6_0_1
  · exact cols_right0_eq_6_0_2
  · exact cols_right0_eq_6_0_3
  · exact cols_right0_eq_6_0_4
  · exact cols_right0_eq_6_0_5
  · exact cols_right0_eq_6_0_6
  · exact cols_right0_eq_6_0_7
  · exact cols_right0_eq_7_0_0
  · exact cols_right0_eq_7_0_1
  · exact cols_right0_eq_7_0_2
  · exact cols_right0_eq_7_0_3
  · exact cols_right0_eq_7_0_4
  · exact cols_right0_eq_7_0_5
  · exact cols_right0_eq_7_0_6
  · exact cols_right0_eq_7_0_7

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 64 5 2 52558562177663339419863108641106047875040272,
    decodeIntegerRow 64 5 2 322741976334851286962463132891855606543970560,
    decodeIntegerRow 64 5 2 306088622439079344106654247784814468856408064,
    decodeIntegerRow 64 5 2 55889188618951016875552866512736882837852752,
    decodeIntegerRow 64 5 2 323441417125264343695549830947198501075170560,
    decodeIntegerRow 64 5 2 52392030483250641149110052591746887719100272,
    decodeIntegerRow 64 5 2 486100877114725813911309573656138982640977872,
    decodeIntegerRow 64 5 2 236700802504811371391473731553277603653282560,
    decodeIntegerRow 64 5 2 486100877111905651005553905064049138890977872,
    decodeIntegerRow 64 5 2 236700802505270622504691199803629166153282560,
    decodeIntegerRow 64 5 2 323441417124586813742110900428018813575170560,
    decodeIntegerRow 64 5 2 52392030486114459241749826961571106469100272,
    decodeIntegerRow 64 5 2 236012463803222643976847252392968886856482560,
    decodeIntegerRow 64 5 2 486211897626619907865869734341106043187537872,
    decodeIntegerRow 64 5 2 489542524067954878440699461943107971900350352,
    decodeIntegerRow 64 5 2 219359109907214232377542726550302749168920064,
    decodeIntegerRow 64 5 2 52392206356788597664805237299388518775350272,
    decodeIntegerRow 64 5 2 323442518182287684766391686950006241356420560,
    decodeIntegerRow 64 5 2 305401403269075316557495317006387955215858064,
    decodeIntegerRow 64 5 2 56000477372120008979937169605675115453162752,
    decodeIntegerRow 64 5 2 219358008282443414797841183688440079200170064,
    decodeIntegerRow 64 5 2 489542344667258954026377681785625090844100352,
    decodeIntegerRow 64 5 2 55889453281909231039708558613261804906602752,
    decodeIntegerRow 64 5 2 306089741117562517471446113133630507950158064,
    decodeIntegerRow 64 5 2 486211632963661690185790959888896550806287872,
    decodeIntegerRow 64 5 2 236011345124739455938173846745690933700232560,
    decodeIntegerRow 64 5 2 322743077960995514301417939212121596825220560,
    decodeIntegerRow 64 5 2 52558741572627264425731185966533264868790272,
    decodeIntegerRow 64 5 2 305401403268616050781498269593438736465858064,
    decodeIntegerRow 64 5 2 56000477374940168416696492677745427953162752,
    decodeIntegerRow 64 5 2 52392206359652413406050655895286956275350272,
    decodeIntegerRow 64 5 2 323442518181610140373765096213541397606420560,
    decodeIntegerRow 64 5 2 236011345125189699532298759961328261856408064,
    decodeIntegerRow 64 5 2 55889453281909231039705607896843328150037872,
    decodeIntegerRow 64 5 2 52558741575493262977353219085734954125350352,
    decodeIntegerRow 64 5 2 219358008282443414797822401080332046043970560,
    decodeIntegerRow 64 5 2 56000477372120008979934159761485681665977872,
    decodeIntegerRow 64 5 2 236699682973676900446249565625467545059608064,
    decodeIntegerRow 64 5 2 323442518182287684766410455252847915137720064,
    decodeIntegerRow 64 5 2 489708879885963619338916722780650725806600272,
    decodeIntegerRow 64 5 2 218658568061142076629980072524271378075170560,
    decodeIntegerRow 64 5 2 52392206359652413406046215540355286156290352,
    decodeIntegerRow 64 5 2 486100608867812048587026897913035955296912752,
    decodeIntegerRow 64 5 2 305401403268616050781516751790323623153282560,
    decodeIntegerRow 64 5 2 52558741572627264425726685530144133812850352,
    decodeIntegerRow 64 5 2 219358008281756702702327243830957046043970560,
    decodeIntegerRow 64 5 2 236011345124739455938155374085703261856408064,
    decodeIntegerRow 64 5 2 55889453279090526817938391262492742212537872,
    decodeIntegerRow 64 5 2 236700802504811371391455249333658584090858064,
    decodeIntegerRow 64 5 2 56000209128026403092419836526927556859727872,
    decodeIntegerRow 64 5 2 52392030483250641149105612331444182837540352,
    decodeIntegerRow 64 5 2 218659669117487873308195337806024184668920560,
    decodeIntegerRow 64 5 2 486211897623801200128170583301982488306602752,
    decodeIntegerRow 64 5 2 306088622439079344106672720467844375137732560,
    decodeIntegerRow 64 5 2 219359109907900930041282050166330704200220560,
    decodeIntegerRow 64 5 2 52558562177663339419858608299296936744100352,
    decodeIntegerRow 64 5 2 219359109907214232377523943927087540137720560,
    decodeIntegerRow 64 5 2 52558562174797338563031438833671936744100352,
    decodeIntegerRow 64 5 2 486211897626619907865872684961357488306602752,
    decodeIntegerRow 64 5 2 306088622439529573026860675358972304825232560,
    decodeIntegerRow 64 5 2 489709055756637757761972133213096985375350272,
    decodeIntegerRow 64 5 2 323441417124586813742129668746270889793970064,
    decodeIntegerRow 64 5 2 305400283737481594499016718411722427872032560,
    decodeIntegerRow 64 5 2 486100877111905651005556914812144861353162752]

def cols_right1 (r : LeftIndex 3 5 3) : List ℤ := cols_right1Data.getD (leftPosition 3 5 3 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 3 5 3) : (tripleIndices 4 2 8).map (fun j => (right1Middle3 5 3) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_0_4
  · exact cols_right1_eq_0_0_5
  · exact cols_right1_eq_0_0_6
  · exact cols_right1_eq_0_0_7
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_0_4
  · exact cols_right1_eq_1_0_5
  · exact cols_right1_eq_1_0_6
  · exact cols_right1_eq_1_0_7
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_0_2
  · exact cols_right1_eq_2_0_3
  · exact cols_right1_eq_2_0_4
  · exact cols_right1_eq_2_0_5
  · exact cols_right1_eq_2_0_6
  · exact cols_right1_eq_2_0_7
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_0_2
  · exact cols_right1_eq_3_0_3
  · exact cols_right1_eq_3_0_4
  · exact cols_right1_eq_3_0_5
  · exact cols_right1_eq_3_0_6
  · exact cols_right1_eq_3_0_7
  · exact cols_right1_eq_4_0_0
  · exact cols_right1_eq_4_0_1
  · exact cols_right1_eq_4_0_2
  · exact cols_right1_eq_4_0_3
  · exact cols_right1_eq_4_0_4
  · exact cols_right1_eq_4_0_5
  · exact cols_right1_eq_4_0_6
  · exact cols_right1_eq_4_0_7
  · exact cols_right1_eq_5_0_0
  · exact cols_right1_eq_5_0_1
  · exact cols_right1_eq_5_0_2
  · exact cols_right1_eq_5_0_3
  · exact cols_right1_eq_5_0_4
  · exact cols_right1_eq_5_0_5
  · exact cols_right1_eq_5_0_6
  · exact cols_right1_eq_5_0_7
  · exact cols_right1_eq_6_0_0
  · exact cols_right1_eq_6_0_1
  · exact cols_right1_eq_6_0_2
  · exact cols_right1_eq_6_0_3
  · exact cols_right1_eq_6_0_4
  · exact cols_right1_eq_6_0_5
  · exact cols_right1_eq_6_0_6
  · exact cols_right1_eq_6_0_7
  · exact cols_right1_eq_7_0_0
  · exact cols_right1_eq_7_0_1
  · exact cols_right1_eq_7_0_2
  · exact cols_right1_eq_7_0_3
  · exact cols_right1_eq_7_0_4
  · exact cols_right1_eq_7_0_5
  · exact cols_right1_eq_7_0_6
  · exact cols_right1_eq_7_0_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230101669414919104,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1712131568738645212843637889280,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1589726585069718328542338820760,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1715272586125880199319199355520,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 2098381717540610315885862301408,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1844073534696700218898277920000,
    decodeIntegerRow 64 3 1 1759407517595991823801661277472,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 1335340868586723594015732775360,
    decodeIntegerRow 64 3 1 1715271148360363011244471637680,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1730972207609064066756291733120,
    decodeIntegerRow 64 3 1 1721551772955508984598560614040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1759407517668971308242919032400,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1702711594958472751491810535360,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1718412669954502558740113843200,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1730972225334039738249540627904,
    decodeIntegerRow 64 3 1 1712131994159674971414885463360,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 2861396722385791286351301069440,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1702711612683448422985002034840,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 2098342951705790125981935431104,
    decodeIntegerRow 64 3 1 572287097687894749925999895360,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 1844073534696700172956406691808,
    decodeIntegerRow 64 3 1 1759058619246919713458615238976,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1335302102751900933418220769280,
    decodeIntegerRow 64 3 1 2861409644549558209794501987872,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1721552304731796178999821340240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 572274175524104766676004376240,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 1589726585069718282977040307840,
    decodeIntegerRow 64 3 1 1759058619174006937869680388760,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1718411236128068979399837434176,
    decodeIntegerRow 64 3 1 1716320713254230103363218355520]

def cols_left0 (r : LeftIndex 3 5 3) : List ℤ := cols_left0Data.getD (leftPosition 3 5 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 5 3) : (tripleIndices 8 1 8).map (fun j => (left0Middle3 5 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_0_4
  · exact cols_left0_eq_2_0_5
  · exact cols_left0_eq_2_0_6
  · exact cols_left0_eq_2_0_7
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_0_4
  · exact cols_left0_eq_3_0_5
  · exact cols_left0_eq_3_0_6
  · exact cols_left0_eq_3_0_7
  · exact cols_left0_eq_4_0_0
  · exact cols_left0_eq_4_0_1
  · exact cols_left0_eq_4_0_2
  · exact cols_left0_eq_4_0_3
  · exact cols_left0_eq_4_0_4
  · exact cols_left0_eq_4_0_5
  · exact cols_left0_eq_4_0_6
  · exact cols_left0_eq_4_0_7
  · exact cols_left0_eq_5_0_0
  · exact cols_left0_eq_5_0_1
  · exact cols_left0_eq_5_0_2
  · exact cols_left0_eq_5_0_3
  · exact cols_left0_eq_5_0_4
  · exact cols_left0_eq_5_0_5
  · exact cols_left0_eq_5_0_6
  · exact cols_left0_eq_5_0_7
  · exact cols_left0_eq_6_0_0
  · exact cols_left0_eq_6_0_1
  · exact cols_left0_eq_6_0_2
  · exact cols_left0_eq_6_0_3
  · exact cols_left0_eq_6_0_4
  · exact cols_left0_eq_6_0_5
  · exact cols_left0_eq_6_0_6
  · exact cols_left0_eq_6_0_7
  · exact cols_left0_eq_7_0_0
  · exact cols_left0_eq_7_0_1
  · exact cols_left0_eq_7_0_2
  · exact cols_left0_eq_7_0_3
  · exact cols_left0_eq_7_0_4
  · exact cols_left0_eq_7_0_5
  · exact cols_left0_eq_7_0_6
  · exact cols_left0_eq_7_0_7

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 64 3 1 2897554982954507054731842505336,
    decodeIntegerRow 64 3 1 1222970223449979722641381551680,
    decodeIntegerRow 64 3 1 1449067880720130889938550628160,
    decodeIntegerRow 64 3 1 2822227385089355910184213181032,
    decodeIntegerRow 64 3 1 1193661775176433885492181119040,
    decodeIntegerRow 64 3 1 2910111233441095383976830271816,
    decodeIntegerRow 64 3 1 617732088666983396577370964008,
    decodeIntegerRow 64 3 1 1957399960069170525083945800640,
    decodeIntegerRow 64 3 1 617732140024461086764009046632,
    decodeIntegerRow 64 3 1 1957399947628083115165384520000,
    decodeIntegerRow 64 3 1 1193661798122280389280100963520,
    decodeIntegerRow 64 3 1 2910111178583811873083718763144,
    decodeIntegerRow 64 3 1 1984615950748985231280655225280,
    decodeIntegerRow 64 3 1 611456384137255865695711776808,
    decodeIntegerRow 64 3 1 536128781897345593374390823864,
    decodeIntegerRow 64 3 1 2210713621150079707418858070720,
    decodeIntegerRow 64 3 1 2910037848311567701821323448640,
    decodeIntegerRow 64 3 1 1193326756107685137995083510568,
    decodeIntegerRow 64 3 1 1475920125234549400854492316344,
    decodeIntegerRow 64 3 1 2815792198735876551736359807040,
    decodeIntegerRow 64 3 1 2211050530290305498826236685672,
    decodeIntegerRow 64 3 1 536210518174010803943277622720,
    decodeIntegerRow 64 3 1 2822076786048532555428114556480,
    decodeIntegerRow 64 3 1 1448707974537416627031130604424,
    decodeIntegerRow 64 3 1 611606983185490781536870640320,
    decodeIntegerRow 64 3 1 1984975856948596665902297598536,
    decodeIntegerRow 64 3 1 1222633265679092095085493699368,
    decodeIntegerRow 64 3 1 2897473357555750830400553915200,
    decodeIntegerRow 64 3 1 1475920137692360850921976801656,
    decodeIntegerRow 64 3 1 2815792147385396444198516989120,
    decodeIntegerRow 64 3 1 2910037793458078109821050758080,
    decodeIntegerRow 64 3 1 1193326779069183407694286503272,
    decodeIntegerRow 64 3 1 1984975845755094671508730994880,
    decodeIntegerRow 64 3 1 2822076786048532815459587889736,
    decodeIntegerRow 64 3 1 2897473302118501115674689884968,
    decodeIntegerRow 64 3 1 2211050530290306786665349657920,
    decodeIntegerRow 64 3 1 2815792198735876841138425928056,
    decodeIntegerRow 64 3 1 1957763695057961890902294440640,
    decodeIntegerRow 64 3 1 1193326756107683863717124667840,
    decodeIntegerRow 64 3 1 523645971980945316245306740072,
    decodeIntegerRow 64 3 1 2240357041223327802685543908800,
    decodeIntegerRow 64 3 1 2910037793458078643229858109912,
    decodeIntegerRow 64 3 1 617891672907116329861410302536,
    decodeIntegerRow 64 3 1 1475920137692359658020859360960,
    decodeIntegerRow 64 3 1 2897473357555751395440410714008,
    decodeIntegerRow 64 3 1 2211050554613419101733301622080,
    decodeIntegerRow 64 3 1 1984975856948597852020229664960,
    decodeIntegerRow 64 3 1 2822076837107021443089518561656,
    decodeIntegerRow 64 3 1 1957399960069171718147552547432,
    decodeIntegerRow 64 3 1 2815951731625528799066865605440,
    decodeIntegerRow 64 3 1 2910111233441095917021952680640,
    decodeIntegerRow 64 3 1 2240022045116077324799549444744,
    decodeIntegerRow 64 3 1 611456435203156834112523136960,
    decodeIntegerRow 64 3 1 1449067880720129703648376250408,
    decodeIntegerRow 64 3 1 2210713596842531474098148596664,
    decodeIntegerRow 64 3 1 2897554982954507619410131622080,
    decodeIntegerRow 64 3 1 2210713621150080995337117803144,
    decodeIntegerRow 64 3 1 2897555038395166326605193914560,
    decodeIntegerRow 64 3 1 611456384137255606056837976000,
    decodeIntegerRow 64 3 1 1449067869543528439667312810648,
    decodeIntegerRow 64 3 1 523572641708701144619278970560,
    decodeIntegerRow 64 3 1 1193661798122279114913922599864,
    decodeIntegerRow 64 3 1 1476283872664430562556126432472,
    decodeIntegerRow 64 3 1 617732140024460797750384463680]

def cols_left1 (r : LeftIndex 3 5 3) : List ℤ := cols_left1Data.getD (leftPosition 3 5 3 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 3 5 3) : (tripleIndices 4 2 8).map (fun j => (left1Middle3 5 3) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_0_4
  · exact cols_left1_eq_0_0_5
  · exact cols_left1_eq_0_0_6
  · exact cols_left1_eq_0_0_7
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_0_4
  · exact cols_left1_eq_1_0_5
  · exact cols_left1_eq_1_0_6
  · exact cols_left1_eq_1_0_7
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_0_2
  · exact cols_left1_eq_2_0_3
  · exact cols_left1_eq_2_0_4
  · exact cols_left1_eq_2_0_5
  · exact cols_left1_eq_2_0_6
  · exact cols_left1_eq_2_0_7
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_0_2
  · exact cols_left1_eq_3_0_3
  · exact cols_left1_eq_3_0_4
  · exact cols_left1_eq_3_0_5
  · exact cols_left1_eq_3_0_6
  · exact cols_left1_eq_3_0_7
  · exact cols_left1_eq_4_0_0
  · exact cols_left1_eq_4_0_1
  · exact cols_left1_eq_4_0_2
  · exact cols_left1_eq_4_0_3
  · exact cols_left1_eq_4_0_4
  · exact cols_left1_eq_4_0_5
  · exact cols_left1_eq_4_0_6
  · exact cols_left1_eq_4_0_7
  · exact cols_left1_eq_5_0_0
  · exact cols_left1_eq_5_0_1
  · exact cols_left1_eq_5_0_2
  · exact cols_left1_eq_5_0_3
  · exact cols_left1_eq_5_0_4
  · exact cols_left1_eq_5_0_5
  · exact cols_left1_eq_5_0_6
  · exact cols_left1_eq_5_0_7
  · exact cols_left1_eq_6_0_0
  · exact cols_left1_eq_6_0_1
  · exact cols_left1_eq_6_0_2
  · exact cols_left1_eq_6_0_3
  · exact cols_left1_eq_6_0_4
  · exact cols_left1_eq_6_0_5
  · exact cols_left1_eq_6_0_6
  · exact cols_left1_eq_6_0_7
  · exact cols_left1_eq_7_0_0
  · exact cols_left1_eq_7_0_1
  · exact cols_left1_eq_7_0_2
  · exact cols_left1_eq_7_0_3
  · exact cols_left1_eq_7_0_4
  · exact cols_left1_eq_7_0_5
  · exact cols_left1_eq_7_0_6
  · exact cols_left1_eq_7_0_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 64 17 8 2958713874195939754732938576321649558959067960805250364863146033498198581845536,
    decodeIntegerRow 64 17 8 5442093290069975892358469542863472366547314705635118063054097690867752434099232,
    decodeIntegerRow 64 17 8 2804037864997007805431889870351465987828040632740619233003019150524965031557664,
    decodeIntegerRow 64 17 8 2812601140118254332366934072639066617825840784525641699080284560085854557014048,
    decodeIntegerRow 64 17 8 2802963738907397127266430884341780211569301952137453828474966747669169601444832,
    decodeIntegerRow 64 17 8 2794340996595027316207128471712612759408844354903402237655979677174984462653984,
    decodeIntegerRow 64 17 8 2648291434301071391036677365551184949165179395106501538702918325809220122255328,
    decodeIntegerRow 64 17 8 164911811857214244167887081695957043770352713169918209830469284278495559990816,
    decodeIntegerRow 64 17 8 2812664324005878489906077415936907327296485681622988785063039343329549042231328,
    decodeIntegerRow 64 17 8 2804041581696270725719310234002086999661063906584830464363989950961821682473504,
    decodeIntegerRow 64 17 8 164911811901714419081267393835943205319869974306438250264676231487065889791968,
    decodeIntegerRow 64 17 8 2648291433544568415659226467573777153732751916358944769438671889302609282131424,
    decodeIntegerRow 64 17 8 5442093290114476070959062660649852741464916595266617959429769950975603490676256,
    decodeIntegerRow 64 17 8 2958713873439436716672869829068714255746106091345364346540889488800009452666848,
    decodeIntegerRow 64 17 8 2794404180482650408141770983202525805578803880748946648655842026681178402154976,
    decodeIntegerRow 64 17 8 2802967455606678162830409688619850970688635657289431271890947914908184670488608,
    decodeIntegerRow 64 17 8 2958713887056490837495719939741098588648607025316876549604821054017486789307936,
    decodeIntegerRow 64 17 8 5442093508699344833971610842924488914950604744203471048079824588416705795200032,
    decodeIntegerRow 64 17 8 2804041581696270725719288236813943903269415729024109313798239028692784105196064,
    decodeIntegerRow 64 17 8 2812664324005878489905703463739395518310646557720362535977507042112002551330848,
    decodeIntegerRow 64 17 8 2804037864994381090330938129317538759505737399229586854402495650182442133801952,
    decodeIntegerRow 64 17 8 2812601140118408845019931233876356454785976268849818961157583665851253108910624,
    decodeIntegerRow 64 17 8 2958713873439436716679249090242424714579662622639192083378238697565318253834208,
    decodeIntegerRow 64 17 8 5442093290114476071067510100868132651510809137291624434201866001266591163846176,
    decodeIntegerRow 64 17 8 2812601140118254332366557523551294266217524397994340193615485712722965325056992,
    decodeIntegerRow 64 17 8 2804037864997007805431867720405072644843846799840218987471506829989096249358816,
    decodeIntegerRow 64 17 8 164912030531083360911303565344082165434101621055813187136330714468010164433952,
    decodeIntegerRow 64 17 8 2648291446405119498434766352874257163040647426944301635069710274909876899761696,
    decodeIntegerRow 64 17 8 164911811857214244059439650463456581817020074750299399753906311441973891380704,
    decodeIntegerRow 64 17 8 2648291434301071391030298104906049753281200208807855256600490331522739872322592,
    decodeIntegerRow 64 17 8 2812664324006031936954571148476009002130351388756294716794539977019322951485984,
    decodeIntegerRow 64 17 8 2804041581693662125894916780837358527485346885318648417709494165377924821412832,
    decodeIntegerRow 64 17 8 164911811857214244059439650463456581817151170207663095833020180078270285865952,
    decodeIntegerRow 64 17 8 2958713886299987862131027563085053848724920813726630133071034404364447260590624,
    decodeIntegerRow 64 17 8 2794340996595027316206754519515094599873541466195549198741082469238144732170208,
    decodeIntegerRow 64 17 8 2804041581693662125894916780837358527485354623499183215620454915130725086406176,
    decodeIntegerRow 64 17 8 2794404180482804920794768144439809335786368453818280198660720641755835688502816,
    decodeIntegerRow 64 17 8 2804037864997007805431867720405072644843854484653991606039847708977571006888992,
    decodeIntegerRow 64 17 8 164912030531083360911303565344082165434232716501675563528554885484482437898784,
    decodeIntegerRow 64 17 8 2958713874195939754726559315116846438965473595405561263418805859139579477549088,
    decodeIntegerRow 64 17 8 2802967455606678162830387538673564842498162685348938161508280363190928781794784,
    decodeIntegerRow 64 17 8 2812601140118408845019931233876356454785976720897689044178133992209343498419232,
    decodeIntegerRow 64 17 8 2958713873439436716679249090242424714577434000054119298751279163564595321938464,
    decodeIntegerRow 64 17 8 164912030486583182093815567122970950492952167026626755022475190282146830664672,
    decodeIntegerRow 64 17 8 2958713887056490837495719939741098588646378402547106101770572369602362133586912,
    decodeIntegerRow 64 17 8 164911811901714419189714825066614687053156560104556745867271138854672056836576,
    decodeIntegerRow 64 17 8 2802963738904788527442037431177159698734484408921178141565967514782547857546272,
    decodeIntegerRow 64 17 8 2812664324005878489905703463739395518310647012907451720373703064977678420698656,
    decodeIntegerRow 64 17 8 5442093290114476070959062660649852741464785499820116620806246586817073419817952,
    decodeIntegerRow 64 17 8 2648291447161622536488455838922389346255557685834315396679918547274407071150624,
    decodeIntegerRow 64 17 8 2812601140118408845019554684788577796425088066967935796171466795868889576355808,
    decodeIntegerRow 64 17 8 2802967455606678162830409688619850970688627972475658783828030751108197832185376,
    decodeIntegerRow 64 17 8 2794340996595180763255248252054196274707407173328852927181015828573308895655456,
    decodeIntegerRow 64 17 8 2804041581696270725719310234002086999661071644765365391880337010970775461923872,
    decodeIntegerRow 64 17 8 164911811901714419081267393835943205320001069763162984165434283742056301466144,
    decodeIntegerRow 64 17 8 2958713887056490837502099200417326448273369106175578206243344365195242908594208,
    decodeIntegerRow 64 17 8 2804041581693662125894894783649323390434582709446763901461931354344815574562336,
    decodeIntegerRow 64 17 8 2794340996595027316207128471712612759408843899716310849968216379954698756331488,
    decodeIntegerRow 64 17 8 2648291434301071391036677365551184949167408017876234400526675491613678175359456,
    decodeIntegerRow 64 17 8 5442093508743845008993438586295146558233670782052198014096509140064622451388448,
    decodeIntegerRow 64 17 8 2958713874195939754732938576321649558956839338220139994222580664606767912554528,
    decodeIntegerRow 64 17 8 164912030531083360802856125127631235456446598683772088401542693823017096131104,
    decodeIntegerRow 64 17 8 2802967455604051447729435797639637614175859451837905913413180578036893797939168,
    decodeIntegerRow 64 17 8 2812601140118254332366934072639066617825841236573509563508631728239650410221024]

def cols_right2 (r : LeftIndex 3 5 3) : List ℤ := cols_right2Data.getD (leftPosition 3 5 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_4 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_5 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_6 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_7 : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 5 3) : (tripleIndices 4 2 8).map (fun j => (right2Middle3 5 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_0_4
  · exact cols_right2_eq_2_0_5
  · exact cols_right2_eq_2_0_6
  · exact cols_right2_eq_2_0_7
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_0_4
  · exact cols_right2_eq_3_0_5
  · exact cols_right2_eq_3_0_6
  · exact cols_right2_eq_3_0_7
  · exact cols_right2_eq_4_0_0
  · exact cols_right2_eq_4_0_1
  · exact cols_right2_eq_4_0_2
  · exact cols_right2_eq_4_0_3
  · exact cols_right2_eq_4_0_4
  · exact cols_right2_eq_4_0_5
  · exact cols_right2_eq_4_0_6
  · exact cols_right2_eq_4_0_7
  · exact cols_right2_eq_5_0_0
  · exact cols_right2_eq_5_0_1
  · exact cols_right2_eq_5_0_2
  · exact cols_right2_eq_5_0_3
  · exact cols_right2_eq_5_0_4
  · exact cols_right2_eq_5_0_5
  · exact cols_right2_eq_5_0_6
  · exact cols_right2_eq_5_0_7
  · exact cols_right2_eq_6_0_0
  · exact cols_right2_eq_6_0_1
  · exact cols_right2_eq_6_0_2
  · exact cols_right2_eq_6_0_3
  · exact cols_right2_eq_6_0_4
  · exact cols_right2_eq_6_0_5
  · exact cols_right2_eq_6_0_6
  · exact cols_right2_eq_6_0_7
  · exact cols_right2_eq_7_0_0
  · exact cols_right2_eq_7_0_1
  · exact cols_right2_eq_7_0_2
  · exact cols_right2_eq_7_0_3
  · exact cols_right2_eq_7_0_4
  · exact cols_right2_eq_7_0_5
  · exact cols_right2_eq_7_0_6
  · exact cols_right2_eq_7_0_7

theorem product0_eq : HexagonAtoms353.outerABC * HexagonAtoms353.assocABC = HexagonAtoms353.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms353.assocBAC * HexagonAtoms353.innerABC = HexagonAtoms353.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms353.innerRightABC * HexagonAtoms353.assocABC = HexagonAtoms353.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 8 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms353.inverseACB * right0Middle3 5 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms353.innerACB * right1Middle3 5 3 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms353.assocBAC * left0Middle3 5 3 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms353.innerRightBAC * left1Middle3 5 3 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms353.assocCAB * right2Middle3 5 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn353

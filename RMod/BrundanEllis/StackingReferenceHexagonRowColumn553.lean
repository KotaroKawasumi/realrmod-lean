import RMod.BrundanEllis.StackingReferenceHexagonAtoms553
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn553
open Superfusion

theorem assocBAC_alias : HexagonAtoms553.assocBAC = HexagonAtoms553.assocABC :=
  HexagonAtoms553.assocBAC_eq.symm.trans HexagonAtoms553.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms553.innerRightBAC = HexagonAtoms553.innerRightABC :=
  HexagonAtoms553.innerRightBAC_eq.symm.trans HexagonAtoms553.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 1702369074897160498975970756200,
    decodeIntegerRow 64 3 1 1720020736831664404814190084760,
    decodeIntegerRow 64 3 1 1710484233140894478769674209632,
    decodeIntegerRow 64 3 1 1703402853908049826335217229728,
    decodeIntegerRow 64 3 1 529891711756517853907658587240,
    decodeIntegerRow 64 3 1 1971189338076210165543876103320,
    decodeIntegerRow 64 3 1 1208147053990962162002853297632,
    decodeIntegerRow 64 3 1 614673868846109516694315543328,
    decodeIntegerRow 64 3 1 1703066889467060865529418006680,
    decodeIntegerRow 64 3 1 1723044576333447088010713327720,
    decodeIntegerRow 64 3 1 1719943255057080598283419761568,
    decodeIntegerRow 64 3 1 1731676542346647026982187300192,
    decodeIntegerRow 64 3 1 614669721136961505027732966040,
    decodeIntegerRow 64 3 1 2225534852587745743380133305960,
    decodeIntegerRow 64 3 1 1971188381511091847028371105568,
    decodeIntegerRow 64 3 1 2903796575165022964774682970592,
    decodeIntegerRow 64 3 1 1702007277945864268084692482848,
    decodeIntegerRow 64 3 1 1719943255057080049239368093152,
    decodeIntegerRow 64 3 1 1710639243959065122125110086760,
    decodeIntegerRow 64 3 1 1703066889467062146627385023640,
    decodeIntegerRow 64 3 1 529887245127489505378136633248,
    decodeIntegerRow 64 3 1 1971188381511091840166409165152,
    decodeIntegerRow 64 3 1 1208148967704766737846747567720,
    decodeIntegerRow 64 3 1 614669721136961520648539837080,
    decodeIntegerRow 64 3 1 1730280966384461377219843924768,
    decodeIntegerRow 64 3 1 1710484233140894204248680973792,
    decodeIntegerRow 64 3 1 1713663083460848628885645165160,
    decodeIntegerRow 64 3 1 1702369074897159309380524748440,
    decodeIntegerRow 64 3 1 2819009951446402951952232331168,
    decodeIntegerRow 64 3 1 1208147053990962158655512637792,
    decodeIntegerRow 64 3 1 1462494482216302325808628796520,
    decodeIntegerRow 64 3 1 529891711756517839040016278680,
    decodeIntegerRow 64 3 1 614673868990200366579421944880,
    decodeIntegerRow 64 3 1 1208147053301727596719005699120,
    decodeIntegerRow 64 3 1 1462494481576298794207598494656,
    decodeIntegerRow 64 3 1 2903792108247812930979945812416,
    decodeIntegerRow 64 3 1 1703402865725278416296285642800,
    decodeIntegerRow 64 3 1 1710484177993620187356869128240,
    decodeIntegerRow 64 3 1 1713663032252664809246054961856,
    decodeIntegerRow 64 3 1 1731314721760894805759741108416,
    decodeIntegerRow 64 3 1 529887244832103277618665471280,
    decodeIntegerRow 64 3 1 1462495439405814320464964566320,
    decodeIntegerRow 64 3 1 2225534851915321777249549608896,
    decodeIntegerRow 64 3 1 614669720989268383895498585536,
    decodeIntegerRow 64 3 1 1702007254311319332784459678000,
    decodeIntegerRow 64 3 1 1713740616443422442872392769840,
    decodeIntegerRow 64 3 1 1723044521186380334859059644096,
    decodeIntegerRow 64 3 1 1703066877649787803083817145536,
    decodeIntegerRow 64 3 1 2819014099303244085141569141824,
    decodeIntegerRow 64 3 1 2225534851915321780680573094464,
    decodeIntegerRow 64 3 1 1971188380886698157330863061040,
    decodeIntegerRow 64 3 1 529887244832103263113648740400,
    decodeIntegerRow 64 3 1 1730616942642723400476065237824,
    decodeIntegerRow 64 3 1 1723044521186380609381086009664,
    decodeIntegerRow 64 3 1 1719943203849089492741403907120,
    decodeIntegerRow 64 3 1 1702007254311318143193490527280,
    decodeIntegerRow 64 3 1 529891712044699538810248213696,
    decodeIntegerRow 64 3 1 1462494481576298800902194783936,
    decodeIntegerRow 64 3 1 2225536766990784891286128780240,
    decodeIntegerRow 64 3 1 614673868990200382590748668880,
    decodeIntegerRow 64 3 1 1702369098531616489302661813696,
    decodeIntegerRow 64 3 1 1713663032252665358288040396736,
    decodeIntegerRow 64 3 1 1723199642298892571821972522960,
    decodeIntegerRow 64 3 1 1703402865725279697399073896400]

def rows_assocABC (r : RightIndex 5 5 3) : List ℤ := rows_assocABCData.getD (rightPosition 5 5 3 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_4_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_5_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_6_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_0 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_1 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_2 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_3 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_4 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_5 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_6 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_7_0_7 : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 5 5 3) : (tripleIndices 4 2 8).map ((HexagonAtoms553.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_0_0_4
  · exact rows_assocABC_eq_0_0_5
  · exact rows_assocABC_eq_0_0_6
  · exact rows_assocABC_eq_0_0_7
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_0_2
  · exact rows_assocABC_eq_1_0_3
  · exact rows_assocABC_eq_1_0_4
  · exact rows_assocABC_eq_1_0_5
  · exact rows_assocABC_eq_1_0_6
  · exact rows_assocABC_eq_1_0_7
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_0_2
  · exact rows_assocABC_eq_2_0_3
  · exact rows_assocABC_eq_2_0_4
  · exact rows_assocABC_eq_2_0_5
  · exact rows_assocABC_eq_2_0_6
  · exact rows_assocABC_eq_2_0_7
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_0_2
  · exact rows_assocABC_eq_3_0_3
  · exact rows_assocABC_eq_3_0_4
  · exact rows_assocABC_eq_3_0_5
  · exact rows_assocABC_eq_3_0_6
  · exact rows_assocABC_eq_3_0_7
  · exact rows_assocABC_eq_4_0_0
  · exact rows_assocABC_eq_4_0_1
  · exact rows_assocABC_eq_4_0_2
  · exact rows_assocABC_eq_4_0_3
  · exact rows_assocABC_eq_4_0_4
  · exact rows_assocABC_eq_4_0_5
  · exact rows_assocABC_eq_4_0_6
  · exact rows_assocABC_eq_4_0_7
  · exact rows_assocABC_eq_5_0_0
  · exact rows_assocABC_eq_5_0_1
  · exact rows_assocABC_eq_5_0_2
  · exact rows_assocABC_eq_5_0_3
  · exact rows_assocABC_eq_5_0_4
  · exact rows_assocABC_eq_5_0_5
  · exact rows_assocABC_eq_5_0_6
  · exact rows_assocABC_eq_5_0_7
  · exact rows_assocABC_eq_6_0_0
  · exact rows_assocABC_eq_6_0_1
  · exact rows_assocABC_eq_6_0_2
  · exact rows_assocABC_eq_6_0_3
  · exact rows_assocABC_eq_6_0_4
  · exact rows_assocABC_eq_6_0_5
  · exact rows_assocABC_eq_6_0_6
  · exact rows_assocABC_eq_6_0_7
  · exact rows_assocABC_eq_7_0_0
  · exact rows_assocABC_eq_7_0_1
  · exact rows_assocABC_eq_7_0_2
  · exact rows_assocABC_eq_7_0_3
  · exact rows_assocABC_eq_7_0_4
  · exact rows_assocABC_eq_7_0_5
  · exact rows_assocABC_eq_7_0_6
  · exact rows_assocABC_eq_7_0_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230103363218355520,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1712132047337003500059288475240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1589610285595812311701442397472,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1718412671932149473413377451600,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 1335340868586722358675913658176,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1843957235222794201680808781440,
    decodeIntegerRow 64 3 1 1674276302623541176414930056880,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 2098381717540611551239628320000,
    decodeIntegerRow 64 3 1 1718411234166632285338649733760,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1702711594958472746408308461376,
    decodeIntegerRow 64 3 1 1721552251553867271814211200000,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1674276302696520660856187811808,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1730972207609064061672847054440,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1715272584164443505258011655104,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1702711612683448417901557356160,
    decodeIntegerRow 64 3 1 1712131515560716305658027749040,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 572287097906721198306548019840,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1730972225334039733166038553920,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1335302102751902168771986787872,
    decodeIntegerRow 64 3 1 2861396722604617734731849193920,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 1843957235222794156115510268520,
    decodeIntegerRow 64 3 1 1674625201118505546788168700520,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 2098342951705788890642116313920,
    decodeIntegerRow 64 3 1 572274175742954274863347101408,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 1721551826132837513242963625920,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 2861409644768407717981844713040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 1589610285595812265759571169280,
    decodeIntegerRow 64 3 1 1674625201045592771199233850304,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1715271150338009925917735246080,
    decodeIntegerRow 64 3 1 1716320713254230101669414919104]

def rows_inverseACB (r : LeftIndex 5 3 5) : List ℤ := rows_inverseACBData.getD (leftPosition 5 3 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 3 5) : (tripleIndices 8 1 8).map ((HexagonAtoms553.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_0_4
  · exact rows_inverseACB_eq_2_0_5
  · exact rows_inverseACB_eq_2_0_6
  · exact rows_inverseACB_eq_2_0_7
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_0_4
  · exact rows_inverseACB_eq_3_0_5
  · exact rows_inverseACB_eq_3_0_6
  · exact rows_inverseACB_eq_3_0_7
  · exact rows_inverseACB_eq_4_0_0
  · exact rows_inverseACB_eq_4_0_1
  · exact rows_inverseACB_eq_4_0_2
  · exact rows_inverseACB_eq_4_0_3
  · exact rows_inverseACB_eq_4_0_4
  · exact rows_inverseACB_eq_4_0_5
  · exact rows_inverseACB_eq_4_0_6
  · exact rows_inverseACB_eq_4_0_7
  · exact rows_inverseACB_eq_5_0_0
  · exact rows_inverseACB_eq_5_0_1
  · exact rows_inverseACB_eq_5_0_2
  · exact rows_inverseACB_eq_5_0_3
  · exact rows_inverseACB_eq_5_0_4
  · exact rows_inverseACB_eq_5_0_5
  · exact rows_inverseACB_eq_5_0_6
  · exact rows_inverseACB_eq_5_0_7
  · exact rows_inverseACB_eq_6_0_0
  · exact rows_inverseACB_eq_6_0_1
  · exact rows_inverseACB_eq_6_0_2
  · exact rows_inverseACB_eq_6_0_3
  · exact rows_inverseACB_eq_6_0_4
  · exact rows_inverseACB_eq_6_0_5
  · exact rows_inverseACB_eq_6_0_6
  · exact rows_inverseACB_eq_6_0_7
  · exact rows_inverseACB_eq_7_0_0
  · exact rows_inverseACB_eq_7_0_1
  · exact rows_inverseACB_eq_7_0_2
  · exact rows_inverseACB_eq_7_0_3
  · exact rows_inverseACB_eq_7_0_4
  · exact rows_inverseACB_eq_7_0_5
  · exact rows_inverseACB_eq_7_0_6
  · exact rows_inverseACB_eq_7_0_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 64 3 1 1717363107038282381294630733760,
    decodeIntegerRow 64 3 1 1718412669954502558172933437408,
    decodeIntegerRow 64 3 1 1721551772955508984598560614040,
    decodeIntegerRow 64 3 1 1730972384867826454722581994880,
    decodeIntegerRow 64 3 1 1759058619246919576260622615360,
    decodeIntegerRow 64 3 1 1844073534696700172956406691808,
    decodeIntegerRow 64 3 1 2098342951049278661893419980440,
    decodeIntegerRow 64 3 1 2861409644768407306178659463040,
    decodeIntegerRow 64 3 1 1702711453151462831968061344000,
    decodeIntegerRow 64 3 1 1721551826132837528494082067904,
    decodeIntegerRow 64 3 1 1715271148360363011244471637680,
    decodeIntegerRow 64 3 1 1717363101132358673322111698560,
    decodeIntegerRow 64 3 1 572274175742953863060162560000,
    decodeIntegerRow 64 3 1 2098342951705790125981935431104,
    decodeIntegerRow 64 3 1 1589610285571396871751259272880,
    decodeIntegerRow 64 3 1 1759058619174007075067672986240,
    decodeIntegerRow 64 3 1 1589726585069718282977040307840,
    decodeIntegerRow 64 3 1 1759407517668971308242919032400,
    decodeIntegerRow 64 3 1 2861396722604618146493193031104,
    decodeIntegerRow 64 3 1 1335302102751900933418220769280,
    decodeIntegerRow 64 3 1 1715272586125880199319199355520,
    decodeIntegerRow 64 3 1 1717367414428910237540087621200,
    decodeIntegerRow 64 3 1 1730972225334039738249540627904,
    decodeIntegerRow 64 3 1 1712131568738645212843637889280,
    decodeIntegerRow 64 3 1 1335302102095384527942535047040,
    decodeIntegerRow 64 3 1 572287097906721610067891148440,
    decodeIntegerRow 64 3 1 1759407517595991823801661277472,
    decodeIntegerRow 64 3 1 1843957235247009423943426087360,
    decodeIntegerRow 64 3 1 1712131515560716320909318378880,
    decodeIntegerRow 64 3 1 1702711612683448422985002034840,
    decodeIntegerRow 64 3 1 1717367408517583119307722179872,
    decodeIntegerRow 64 3 1 1718411236128068978837299696960,
    decodeIntegerRow 64 3 1 1718411236128068979399837434176,
    decodeIntegerRow 64 3 1 1717367408517583121003073172480,
    decodeIntegerRow 64 3 1 1730972207609064066756291733120,
    decodeIntegerRow 64 3 1 1721552304731796178999821340240,
    decodeIntegerRow 64 3 1 1843957235247009469508724678976,
    decodeIntegerRow 64 3 1 1759407517595991961125178113280,
    decodeIntegerRow 64 3 1 2861396722385791286351301069440,
    decodeIntegerRow 64 3 1 2098381718197129192069080297040,
    decodeIntegerRow 64 3 1 1721552251553867256562939703008,
    decodeIntegerRow 64 3 1 1702711594958472751491810535360,
    decodeIntegerRow 64 3 1 1717367414428910235844734494080,
    decodeIntegerRow 64 3 1 1715272586125880199881730718360,
    decodeIntegerRow 64 3 1 2098381717540610315885862301408,
    decodeIntegerRow 64 3 1 572287097687894749925999895360,
    decodeIntegerRow 64 3 1 1759407517668971170919402170240,
    decodeIntegerRow 64 3 1 1589726585069718328542338820760,
    decodeIntegerRow 64 3 1 1759058619174006937869680388760,
    decodeIntegerRow 64 3 1 1589610285571396917693130579840,
    decodeIntegerRow 64 3 1 1335340868586723594015732775360,
    decodeIntegerRow 64 3 1 2861409644549558209794501987872,
    decodeIntegerRow 64 3 1 1717363101132358671628310379160,
    decodeIntegerRow 64 3 1 1715271148360363011811658423680,
    decodeIntegerRow 64 3 1 1712131994159674971414885463360,
    decodeIntegerRow 64 3 1 1730972367141049647605826506272,
    decodeIntegerRow 64 3 1 572274175524104766676004376240,
    decodeIntegerRow 64 3 1 1335340869243232587424610227840,
    decodeIntegerRow 64 3 1 1844073534696700218898277920000,
    decodeIntegerRow 64 3 1 1759058619246919713458615238976,
    decodeIntegerRow 64 3 1 1702711435424686024851248459440,
    decodeIntegerRow 64 3 1 1712132047337003484808189164160,
    decodeIntegerRow 64 3 1 1718412669954502558740113843200,
    decodeIntegerRow 64 3 1 1717363107038282382988434170176]

def rows_assocBCA (r : RightIndex 5 3 5) : List ℤ := rows_assocBCAData.getD (rightPosition 5 3 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 3 5) : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_0_4
  · exact rows_assocBCA_eq_2_0_5
  · exact rows_assocBCA_eq_2_0_6
  · exact rows_assocBCA_eq_2_0_7
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_0_4
  · exact rows_assocBCA_eq_3_0_5
  · exact rows_assocBCA_eq_3_0_6
  · exact rows_assocBCA_eq_3_0_7
  · exact rows_assocBCA_eq_4_0_0
  · exact rows_assocBCA_eq_4_0_1
  · exact rows_assocBCA_eq_4_0_2
  · exact rows_assocBCA_eq_4_0_3
  · exact rows_assocBCA_eq_4_0_4
  · exact rows_assocBCA_eq_4_0_5
  · exact rows_assocBCA_eq_4_0_6
  · exact rows_assocBCA_eq_4_0_7
  · exact rows_assocBCA_eq_5_0_0
  · exact rows_assocBCA_eq_5_0_1
  · exact rows_assocBCA_eq_5_0_2
  · exact rows_assocBCA_eq_5_0_3
  · exact rows_assocBCA_eq_5_0_4
  · exact rows_assocBCA_eq_5_0_5
  · exact rows_assocBCA_eq_5_0_6
  · exact rows_assocBCA_eq_5_0_7
  · exact rows_assocBCA_eq_6_0_0
  · exact rows_assocBCA_eq_6_0_1
  · exact rows_assocBCA_eq_6_0_2
  · exact rows_assocBCA_eq_6_0_3
  · exact rows_assocBCA_eq_6_0_4
  · exact rows_assocBCA_eq_6_0_5
  · exact rows_assocBCA_eq_6_0_6
  · exact rows_assocBCA_eq_6_0_7
  · exact rows_assocBCA_eq_7_0_0
  · exact rows_assocBCA_eq_7_0_1
  · exact rows_assocBCA_eq_7_0_2
  · exact rows_assocBCA_eq_7_0_3
  · exact rows_assocBCA_eq_7_0_4
  · exact rows_assocBCA_eq_7_0_5
  · exact rows_assocBCA_eq_7_0_6
  · exact rows_assocBCA_eq_7_0_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716841913114126877389940976168,
    decodeIntegerRow 64 3 1 1716841909201994016217851491716,
    decodeIntegerRow 64 3 1 1716841883666716405245932202724,
    decodeIntegerRow 64 3 1 1716841919336999216268494532712,
    decodeIntegerRow 64 3 1 1716841911171569159718199027048,
    decodeIntegerRow 64 3 1 1716841913087111078383015421956,
    decodeIntegerRow 64 3 1 1716841918681385803536842621284,
    decodeIntegerRow 64 3 1 1716841936844334005667426859432,
    decodeIntegerRow 64 3 1 1760978278429551339486514493288,
    decodeIntegerRow 64 3 1 1590247778996674956825164546044,
    decodeIntegerRow 64 3 1 1349432568281824542057653033116,
    decodeIntegerRow 64 3 1 2866106611893121524758968924072,
    decodeIntegerRow 64 3 1 1844599036035898329026463648808,
    decodeIntegerRow 64 3 1 1757489294209368935905100649084,
    decodeIntegerRow 64 3 1 2856699276662407488435720392476,
    decodeIntegerRow 64 3 1 2112473257702830051569933147752,
    decodeIntegerRow 64 3 1 2084251252010687942600197075324,
    decodeIntegerRow 64 3 1 2866106611893121524758965720792,
    decodeIntegerRow 64 3 1 1672705541862961145171324676248,
    decodeIntegerRow 64 3 1 1590247778996674956825193125916,
    decodeIntegerRow 64 3 1 576984543630104996222125522684,
    decodeIntegerRow 64 3 1 2112473257702830051569932041112,
    decodeIntegerRow 64 3 1 1589084784256614155631356624728,
    decodeIntegerRow 64 3 1 1757489294209368935905091436956,
    decodeIntegerRow 64 3 1 1716841936625796216047374947076,
    decodeIntegerRow 64 3 1 1716841919336999168631271205272,
    decodeIntegerRow 64 3 1 1716841907178384366844615737688,
    decodeIntegerRow 64 3 1 1716841909201994412769755324004,
    decodeIntegerRow 64 3 1 1716841901611126637249510293636,
    decodeIntegerRow 64 3 1 1716841936844333867776726414552,
    decodeIntegerRow 64 3 1 1716841909120942897927197702808,
    decodeIntegerRow 64 3 1 1716841913087109848113239222244,
    decodeIntegerRow 64 3 1 1716841909193922656806282091644,
    decodeIntegerRow 64 3 1 1716841913111326351294921217128,
    decodeIntegerRow 64 3 1 1716841919337903442672492102312,
    decodeIntegerRow 64 3 1 1716841883667005339699497433116,
    decodeIntegerRow 64 3 1 1716841913089711488465102495484,
    decodeIntegerRow 64 3 1 1716841911163431122082220900648,
    decodeIntegerRow 64 3 1 1716841936844645175233540165992,
    decodeIntegerRow 64 3 1 1716841918680488985824446021276,
    decodeIntegerRow 64 3 1 1843548033381917456836504122364,
    decodeIntegerRow 64 3 1 1673055876080954769234644557272,
    decodeIntegerRow 64 3 1 567563807636954045317226322328,
    decodeIntegerRow 64 3 1 2084212645052238736305423212956,
    decodeIntegerRow 64 3 1 1675847063457100692099792851324,
    decodeIntegerRow 64 3 1 1589205391118546386866270026392,
    decodeIntegerRow 64 3 1 1321171636565460919303103723608,
    decodeIntegerRow 64 3 1 576996987195224988333664205596,
    decodeIntegerRow 64 3 1 567563807636954045317223122072,
    decodeIntegerRow 64 3 1 1349471175240273748352426904196,
    decodeIntegerRow 64 3 1 1843548033381917456836532701924,
    decodeIntegerRow 64 3 1 1760627944211557715423194611288,
    decodeIntegerRow 64 3 1 1321171636565460919303102625752,
    decodeIntegerRow 64 3 1 2856686833097287496324181706756,
    decodeIntegerRow 64 3 1 1675847063457100692099783640164,
    decodeIntegerRow 64 3 1 1844478429173966097791550246808,
    decodeIntegerRow 64 3 1 1716841919337903489931593032488,
    decodeIntegerRow 64 3 1 1716841936625507008202018403076,
    decodeIntegerRow 64 3 1 1716841909193922260296047485284,
    decodeIntegerRow 64 3 1 1716841907181187373800683945832,
    decodeIntegerRow 64 3 1 1716841936844645312994067326568,
    decodeIntegerRow 64 3 1 1716841901612023543079922275716,
    decodeIntegerRow 64 3 1 1716841913089712718721448118244,
    decodeIntegerRow 64 3 1 1716841909129081789630094147752]

def rows_assocCAB (r : RightIndex 3 5 5) : List ℤ := rows_assocCABData.getD (rightPosition 3 5 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_4 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_5 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_6 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_7 : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 5 5) : (tripleIndices 8 1 8).map ((HexagonAtoms553.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_1_4
  · exact rows_assocCAB_eq_0_1_5
  · exact rows_assocCAB_eq_0_1_6
  · exact rows_assocCAB_eq_0_1_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_1_1_4
  · exact rows_assocCAB_eq_1_1_5
  · exact rows_assocCAB_eq_1_1_6
  · exact rows_assocCAB_eq_1_1_7
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_0_4
  · exact rows_assocCAB_eq_2_0_5
  · exact rows_assocCAB_eq_2_0_6
  · exact rows_assocCAB_eq_2_0_7
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_2_1_2
  · exact rows_assocCAB_eq_2_1_3
  · exact rows_assocCAB_eq_2_1_4
  · exact rows_assocCAB_eq_2_1_5
  · exact rows_assocCAB_eq_2_1_6
  · exact rows_assocCAB_eq_2_1_7
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_0_4
  · exact rows_assocCAB_eq_3_0_5
  · exact rows_assocCAB_eq_3_0_6
  · exact rows_assocCAB_eq_3_0_7
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1
  · exact rows_assocCAB_eq_3_1_2
  · exact rows_assocCAB_eq_3_1_3
  · exact rows_assocCAB_eq_3_1_4
  · exact rows_assocCAB_eq_3_1_5
  · exact rows_assocCAB_eq_3_1_6
  · exact rows_assocCAB_eq_3_1_7

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 64 3 1 1716839676685801636852225574488,
    decodeIntegerRow 64 3 1 1716842388744936345009631237564,
    decodeIntegerRow 64 3 1 1716840952948951078530114216796,
    decodeIntegerRow 64 3 1 1716839836218787990948207596328,
    decodeIntegerRow 64 3 1 1716660999849455431569677987608,
    decodeIntegerRow 64 3 1 1716880676639392730649113995324,
    decodeIntegerRow 64 3 1 1716764377164486097969146203356,
    decodeIntegerRow 64 3 1 1716673922021338996916891141608,
    decodeIntegerRow 64 3 1 1702188176105390845309624659928,
    decodeIntegerRow 64 3 1 1719981996090312390970232362684,
    decodeIntegerRow 64 3 1 1710561738622873908734333940316,
    decodeIntegerRow 64 3 1 1703234872027959501194046546088,
    decodeIntegerRow 64 3 1 529889452836159087154271799448,
    decodeIntegerRow 64 3 1 1971188871614804289616906723644,
    decodeIntegerRow 64 3 1 1208148016752287213260264051676,
    decodeIntegerRow 64 3 1 614671822564220212098125521768,
    decodeIntegerRow 64 3 1 1716839836218788265469704301276,
    decodeIntegerRow 64 3 1 1716842867343562687228084715368,
    decodeIntegerRow 64 3 1 1716842388744937534602868656232,
    decodeIntegerRow 64 3 1 1716844143606710298762598218436,
    decodeIntegerRow 64 3 1 1716673922021339000306045421916,
    decodeIntegerRow 64 3 1 1716919443128026402504756587688,
    decodeIntegerRow 64 3 1 1716880676639392745335450259752,
    decodeIntegerRow 64 3 1 1717022820443057046309862147396,
    decodeIntegerRow 64 3 1 1703234872027959501235887956956,
    decodeIntegerRow 64 3 1 1723122081669638576118775071208,
    decodeIntegerRow 64 3 1 1719981996090312391151545156072,
    decodeIntegerRow 64 3 1 1731495644187121639264541602756,
    decodeIntegerRow 64 3 1 614671822564220212098642082396,
    decodeIntegerRow 64 3 1 2225535803540225271399995653928,
    decodeIntegerRow 64 3 1 1971188871614804289619145153192,
    decodeIntegerRow 64 3 1 2903794367456353397502544168516,
    decodeIntegerRow 64 3 1 1462494972312209847447611954724,
    decodeIntegerRow 64 3 1 529889504044246000702055909272,
    decodeIntegerRow 64 3 1 614671767417049689815896480408,
    decodeIntegerRow 64 3 1 2225535815357476097600919832124,
    decodeIntegerRow 64 3 1 1713701824493984064704983013284,
    decodeIntegerRow 64 3 1 1702188176737589449180584958552,
    decodeIntegerRow 64 3 1 1703234871347130235486858531288,
    decodeIntegerRow 64 3 1 1723122081815530561432198290364,
    decodeIntegerRow 64 3 1 1716803143656722025255862705444,
    decodeIntegerRow 64 3 1 1716660999857260352605122020632,
    decodeIntegerRow 64 3 1 1716673922012933697340259033368,
    decodeIntegerRow 64 3 1 1716919443129827522312266534204,
    decodeIntegerRow 64 3 1 1716841431547620612132720535204,
    decodeIntegerRow 64 3 1 1716839676685897993902052247512,
    decodeIntegerRow 64 3 1 1716839836218684221817619138648,
    decodeIntegerRow 64 3 1 1716842867343583642369973459644,
    decodeIntegerRow 64 3 1 1208148004935036387054518640728,
    decodeIntegerRow 64 3 1 614671767417049689816413041084,
    decodeIntegerRow 64 3 1 2903794316248266483954760058716,
    decodeIntegerRow 64 3 1 1462494972312209847445373525288,
    decodeIntegerRow 64 3 1 1710561738476981923030390868248,
    decodeIntegerRow 64 3 1 1703234871347130235528699946044,
    decodeIntegerRow 64 3 1 1731495643554923035393581306076,
    decodeIntegerRow 64 3 1 1713701824493984064523670228968,
    decodeIntegerRow 64 3 1 1716764377162684946529528170968,
    decodeIntegerRow 64 3 1 1716673922012933700729413628604,
    decodeIntegerRow 64 3 1 1717022820435252125274418271836,
    decodeIntegerRow 64 3 1 1716803143656722010569527175848,
    decodeIntegerRow 64 3 1 1716840952948927561187470516888,
    decodeIntegerRow 64 3 1 1716839836218684496339141352764,
    decodeIntegerRow 64 3 1 1716844143606613941712784299996,
    decodeIntegerRow 64 3 1 1716841431547619422539542637928]

def cols_innerABC (r : LeftIndex 5 5 3) : List ℤ := cols_innerABCData.getD (leftPosition 5 5 3 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_1 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_2 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_3 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_4 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_5 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_6 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_7 : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 5 5 3) : (tripleIndices 4 2 8).map (fun j => (HexagonAtoms553.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_0_4
  · exact cols_innerABC_eq_0_0_5
  · exact cols_innerABC_eq_0_0_6
  · exact cols_innerABC_eq_0_0_7
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_1_2
  · exact cols_innerABC_eq_0_1_3
  · exact cols_innerABC_eq_0_1_4
  · exact cols_innerABC_eq_0_1_5
  · exact cols_innerABC_eq_0_1_6
  · exact cols_innerABC_eq_0_1_7
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_0_2
  · exact cols_innerABC_eq_1_0_3
  · exact cols_innerABC_eq_1_0_4
  · exact cols_innerABC_eq_1_0_5
  · exact cols_innerABC_eq_1_0_6
  · exact cols_innerABC_eq_1_0_7
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_1_1_2
  · exact cols_innerABC_eq_1_1_3
  · exact cols_innerABC_eq_1_1_4
  · exact cols_innerABC_eq_1_1_5
  · exact cols_innerABC_eq_1_1_6
  · exact cols_innerABC_eq_1_1_7
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_0_2
  · exact cols_innerABC_eq_2_0_3
  · exact cols_innerABC_eq_2_0_4
  · exact cols_innerABC_eq_2_0_5
  · exact cols_innerABC_eq_2_0_6
  · exact cols_innerABC_eq_2_0_7
  · exact cols_innerABC_eq_2_1_0
  · exact cols_innerABC_eq_2_1_1
  · exact cols_innerABC_eq_2_1_2
  · exact cols_innerABC_eq_2_1_3
  · exact cols_innerABC_eq_2_1_4
  · exact cols_innerABC_eq_2_1_5
  · exact cols_innerABC_eq_2_1_6
  · exact cols_innerABC_eq_2_1_7
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_0_2
  · exact cols_innerABC_eq_3_0_3
  · exact cols_innerABC_eq_3_0_4
  · exact cols_innerABC_eq_3_0_5
  · exact cols_innerABC_eq_3_0_6
  · exact cols_innerABC_eq_3_0_7
  · exact cols_innerABC_eq_3_1_0
  · exact cols_innerABC_eq_3_1_1
  · exact cols_innerABC_eq_3_1_2
  · exact cols_innerABC_eq_3_1_3
  · exact cols_innerABC_eq_3_1_4
  · exact cols_innerABC_eq_3_1_5
  · exact cols_innerABC_eq_3_1_6
  · exact cols_innerABC_eq_3_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1713700867223698638605163923152,
    decodeIntegerRow 64 3 1 1731497717458175286833227848640,
    decodeIntegerRow 64 3 1 1730446714828410917824978896640,
    decodeIntegerRow 64 3 1 1723121602998022866691694739496,
    decodeIntegerRow 64 3 1 1462417433419112575252261369552,
    decodeIntegerRow 64 3 1 2903962302411747026267174941760,
    decodeIntegerRow 64 3 1 2818831089400733088192909665280,
    decodeIntegerRow 64 3 1 2225497031139363928751486662696,
    decodeIntegerRow 64 3 1 1971111332725309295449231422400,
    decodeIntegerRow 64 3 1 2903626381300677761540270464112,
    decodeIntegerRow 64 3 1 2819192961194616695447672042664,
    decodeIntegerRow 64 3 1 1208109232535976183421138693120,
    decodeIntegerRow 64 3 1 1719981038820071986579277423680,
    decodeIntegerRow 64 3 1 1731493570283964555365190528112,
    decodeIntegerRow 64 3 1 1730451182381421826737774570664,
    decodeIntegerRow 64 3 1 1710561259805388724562346146560,
    decodeIntegerRow 64 3 1 2903626381300677776224195403520,
    decodeIntegerRow 64 3 1 1971111332725309288671439264984,
    decodeIntegerRow 64 3 1 1208109232535976180030951212752,
    decodeIntegerRow 64 3 1 2819192961194616679629379937600,
    decodeIntegerRow 64 3 1 1731493570283965744763110620160,
    decodeIntegerRow 64 3 1 1719981038820071437578112672984,
    decodeIntegerRow 64 3 1 1710561259805388449957160236752,
    decodeIntegerRow 64 3 1 1730451182381420545456114060480,
    decodeIntegerRow 64 3 1 1731497717458176476621723063464,
    decodeIntegerRow 64 3 1 1713700867223699187690037008640,
    decodeIntegerRow 64 3 1 1723121602998023141129527752640,
    decodeIntegerRow 64 3 1 1730446714828409636905884442768,
    decodeIntegerRow 64 3 1 2903962302411747040955921796264,
    decodeIntegerRow 64 3 1 1462417433419112582031086963200,
    decodeIntegerRow 64 3 1 2225497031139363932139608057920,
    decodeIntegerRow 64 3 1 2818831089400733072379093684368,
    decodeIntegerRow 64 3 1 2225497054775666716781720320048,
    decodeIntegerRow 64 3 1 2818831140617225301317325358400,
    decodeIntegerRow 64 3 1 529721462741399857143888719360,
    decodeIntegerRow 64 3 1 1971266398687048464361794377944,
    decodeIntegerRow 64 3 1 1723121603289829073951333632048,
    decodeIntegerRow 64 3 1 1730446715460713290826485132480,
    decodeIntegerRow 64 3 1 1702186102153604289167225893120,
    decodeIntegerRow 64 3 1 1719982953214661359076823113944,
    decodeIntegerRow 64 3 1 1723122560195362025320396498240,
    decodeIntegerRow 64 3 1 1703232638543185492660429356688,
    decodeIntegerRow 64 3 1 1731493569603038932608154580056,
    decodeIntegerRow 64 3 1 1719981038674135528586074589440,
    decodeIntegerRow 64 3 1 2225574564123835784453604717760,
    decodeIntegerRow 64 3 1 614490910297577403181328838288,
    decodeIntegerRow 64 3 1 2903626326145702318222597127256,
    decodeIntegerRow 64 3 1 1971111320904456197998768806400,
    decodeIntegerRow 64 3 1 1703232638543186773942149379840,
    decodeIntegerRow 64 3 1 1723122560195362299925595158744,
    decodeIntegerRow 64 3 1 1719981038674134979584884327632,
    decodeIntegerRow 64 3 1 1731493569603040122006129951040,
    decodeIntegerRow 64 3 1 614490910297577418999621678080,
    decodeIntegerRow 64 3 1 2225574564123835787843792355544,
    decodeIntegerRow 64 3 1 1971111320904456191220976334032,
    decodeIntegerRow 64 3 1 2903626326145702332906522749120,
    decodeIntegerRow 64 3 1 2818831140617225285503510112424,
    decodeIntegerRow 64 3 1 2225497054775666720169841557760,
    decodeIntegerRow 64 3 1 1971266398687048457582969099200,
    decodeIntegerRow 64 3 1 529721462741399842455142547088,
    decodeIntegerRow 64 3 1 1730446715460712009907450208424,
    decodeIntegerRow 64 3 1 1723121603289829348389153886720,
    decodeIntegerRow 64 3 1 1719982953214660809991975535680,
    decodeIntegerRow 64 3 1 1702186102153603099378785939088]

def cols_right0 (r : LeftIndex 5 5 3) : List ℤ := cols_right0Data.getD (leftPosition 5 5 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_4 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_5 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_6 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_7 : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 5 3) : (tripleIndices 8 1 8).map (fun j => (right0Middle5 5 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_1_4
  · exact cols_right0_eq_0_1_5
  · exact cols_right0_eq_0_1_6
  · exact cols_right0_eq_0_1_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_1_1_4
  · exact cols_right0_eq_1_1_5
  · exact cols_right0_eq_1_1_6
  · exact cols_right0_eq_1_1_7
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_0_4
  · exact cols_right0_eq_2_0_5
  · exact cols_right0_eq_2_0_6
  · exact cols_right0_eq_2_0_7
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_1_2
  · exact cols_right0_eq_2_1_3
  · exact cols_right0_eq_2_1_4
  · exact cols_right0_eq_2_1_5
  · exact cols_right0_eq_2_1_6
  · exact cols_right0_eq_2_1_7
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_0_4
  · exact cols_right0_eq_3_0_5
  · exact cols_right0_eq_3_0_6
  · exact cols_right0_eq_3_0_7
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_1_2
  · exact cols_right0_eq_3_1_3
  · exact cols_right0_eq_3_1_4
  · exact cols_right0_eq_3_1_5
  · exact cols_right0_eq_3_1_6
  · exact cols_right0_eq_3_1_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 64 3 1 1713700867223698638605163923152,
    decodeIntegerRow 64 3 1 1731497717458175286833227848640,
    decodeIntegerRow 64 3 1 1730446714828410917824978896640,
    decodeIntegerRow 64 3 1 1723121602998022866691694739496,
    decodeIntegerRow 64 3 1 1462417433419112575252261369552,
    decodeIntegerRow 64 3 1 2903962302411747026267174941760,
    decodeIntegerRow 64 3 1 2818831089400733088192909665280,
    decodeIntegerRow 64 3 1 2225497031139363928751486662696,
    decodeIntegerRow 64 3 1 1971111332725309295449231422400,
    decodeIntegerRow 64 3 1 2903626381300677761540270464112,
    decodeIntegerRow 64 3 1 2819192961194616695447672042664,
    decodeIntegerRow 64 3 1 1208109232535976183421138693120,
    decodeIntegerRow 64 3 1 1719981038820071986579277423680,
    decodeIntegerRow 64 3 1 1731493570283964555365190528112,
    decodeIntegerRow 64 3 1 1730451182381421826737774570664,
    decodeIntegerRow 64 3 1 1710561259805388724562346146560,
    decodeIntegerRow 64 3 1 2903626381300677776224195403520,
    decodeIntegerRow 64 3 1 1971111332725309288671439264984,
    decodeIntegerRow 64 3 1 1208109232535976180030951212752,
    decodeIntegerRow 64 3 1 2819192961194616679629379937600,
    decodeIntegerRow 64 3 1 1731493570283965744763110620160,
    decodeIntegerRow 64 3 1 1719981038820071437578112672984,
    decodeIntegerRow 64 3 1 1710561259805388449957160236752,
    decodeIntegerRow 64 3 1 1730451182381420545456114060480,
    decodeIntegerRow 64 3 1 1731497717458176476621723063464,
    decodeIntegerRow 64 3 1 1713700867223699187690037008640,
    decodeIntegerRow 64 3 1 1723121602998023141129527752640,
    decodeIntegerRow 64 3 1 1730446714828409636905884442768,
    decodeIntegerRow 64 3 1 2903962302411747040955921796264,
    decodeIntegerRow 64 3 1 1462417433419112582031086963200,
    decodeIntegerRow 64 3 1 2225497031139363932139608057920,
    decodeIntegerRow 64 3 1 2818831089400733072379093684368,
    decodeIntegerRow 64 3 1 2225497054775666716781720320048,
    decodeIntegerRow 64 3 1 2818831140617225301317325358400,
    decodeIntegerRow 64 3 1 529721462741399857143888719360,
    decodeIntegerRow 64 3 1 1971266398687048464361794377944,
    decodeIntegerRow 64 3 1 1723121603289829073951333632048,
    decodeIntegerRow 64 3 1 1730446715460713290826485132480,
    decodeIntegerRow 64 3 1 1702186102153604289167225893120,
    decodeIntegerRow 64 3 1 1719982953214661359076823113944,
    decodeIntegerRow 64 3 1 1723122560195362025320396498240,
    decodeIntegerRow 64 3 1 1703232638543185492660429356688,
    decodeIntegerRow 64 3 1 1731493569603038932608154580056,
    decodeIntegerRow 64 3 1 1719981038674135528586074589440,
    decodeIntegerRow 64 3 1 2225574564123835784453604717760,
    decodeIntegerRow 64 3 1 614490910297577403181328838288,
    decodeIntegerRow 64 3 1 2903626326145702318222597127256,
    decodeIntegerRow 64 3 1 1971111320904456197998768806400,
    decodeIntegerRow 64 3 1 1703232638543186773942149379840,
    decodeIntegerRow 64 3 1 1723122560195362299925595158744,
    decodeIntegerRow 64 3 1 1719981038674134979584884327632,
    decodeIntegerRow 64 3 1 1731493569603040122006129951040,
    decodeIntegerRow 64 3 1 614490910297577418999621678080,
    decodeIntegerRow 64 3 1 2225574564123835787843792355544,
    decodeIntegerRow 64 3 1 1971111320904456191220976334032,
    decodeIntegerRow 64 3 1 2903626326145702332906522749120,
    decodeIntegerRow 64 3 1 2818831140617225285503510112424,
    decodeIntegerRow 64 3 1 2225497054775666720169841557760,
    decodeIntegerRow 64 3 1 1971266398687048457582969099200,
    decodeIntegerRow 64 3 1 529721462741399842455142547088,
    decodeIntegerRow 64 3 1 1730446715460712009907450208424,
    decodeIntegerRow 64 3 1 1723121603289829348389153886720,
    decodeIntegerRow 64 3 1 1719982953214660809991975535680,
    decodeIntegerRow 64 3 1 1702186102153603099378785939088]

def cols_left0 (r : LeftIndex 5 5 3) : List ℤ := cols_left0Data.getD (leftPosition 5 5 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_4 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_5 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_6 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_7 : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 5 3) : (tripleIndices 8 1 8).map (fun j => (left0Middle5 5 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_1_4
  · exact cols_left0_eq_0_1_5
  · exact cols_left0_eq_0_1_6
  · exact cols_left0_eq_0_1_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_1_1_4
  · exact cols_left0_eq_1_1_5
  · exact cols_left0_eq_1_1_6
  · exact cols_left0_eq_1_1_7
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_0_4
  · exact cols_left0_eq_2_0_5
  · exact cols_left0_eq_2_0_6
  · exact cols_left0_eq_2_0_7
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_1_2
  · exact cols_left0_eq_2_1_3
  · exact cols_left0_eq_2_1_4
  · exact cols_left0_eq_2_1_5
  · exact cols_left0_eq_2_1_6
  · exact cols_left0_eq_2_1_7
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_0_4
  · exact cols_left0_eq_3_0_5
  · exact cols_left0_eq_3_0_6
  · exact cols_left0_eq_3_0_7
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_1_2
  · exact cols_left0_eq_3_1_3
  · exact cols_left0_eq_3_1_4
  · exact cols_left0_eq_3_1_5
  · exact cols_left0_eq_3_1_6
  · exact cols_left0_eq_3_1_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 64 9 4 5895092288869291620672889247587314892821249245493210049641040,
    decodeIntegerRow 64 9 4 5895092288869291581886728321115471527394417382692823112913984,
    decodeIntegerRow 64 9 4 5895092288869288757948130341027714701146355740342207531663424,
    decodeIntegerRow 64 9 4 5895092288869291900398134617400023120525241235144674005180240,
    decodeIntegerRow 64 9 4 5895092288869291589644918161640687000761520337656330423001680,
    decodeIntegerRow 64 9 4 5895092288869291620671692178552147168245517140631311732446784,
    decodeIntegerRow 64 9 4 5895092288869291899536115146300320744585336186070313513116224,
    decodeIntegerRow 64 9 4 5895092288869294413668522461618141444356871254198607712864080,
    decodeIntegerRow 64 9 4 5902290311939939539773181525362230099413028609700285552192080,
    decodeIntegerRow 64 9 4 5830401027150366106893450030039243895392314132022735668986816,
    decodeIntegerRow 64 9 4 5313659621438606887745080415003153702680042427144379794831296,
    decodeIntegerRow 64 9 4 11135263064501940112362360109107870590793846736615113447161680,
    decodeIntegerRow 64 9 4 5959785768781312335535903793598560659596105108839984796009040,
    decodeIntegerRow 64 9 4 5902270348202082101596852865334657095621159757777224177927616,
    decodeIntegerRow 64 9 4 11135085582337147764936415730154854478927427940996851567516096,
    decodeIntegerRow 64 9 4 6478122295783107410609291856986509969795938325515063327676240,
    decodeIntegerRow 64 9 4 6476524956299976283775792446409364962998169165133717612930496,
    decodeIntegerRow 64 9 4 11135263064501940112362360109107870590793846736594778171903920,
    decodeIntegerRow 64 9 4 5887894265798643631747691336050288566265182982392290169260720,
    decodeIntegerRow 64 9 4 5830401027150366106893450030039243895392314133669836831521216,
    decodeIntegerRow 64 9 4 655098995401435406584457131257664186750783651258654963573696,
    decodeIntegerRow 64 9 4 6478122295783107410609291856986509969795938325512800753756080,
    decodeIntegerRow 64 9 4 5830398808957270835984969067813958006082106481788699362108080,
    decodeIntegerRow 64 9 4 5902270348202082101596852865334657095621159757594460886292416,
    decodeIntegerRow 64 9 4 5895092288869294413572742520384841644915434916873605365429824,
    decodeIntegerRow 64 9 4 5895092288869291900398134617400018927930088409011253202165680,
    decodeIntegerRow 64 9 4 5895092288869291550847983613822151557772589061057341521570480,
    decodeIntegerRow 64 9 4 5895092288869291581886728321115810191463598425089350533317184,
    decodeIntegerRow 64 9 4 5895092288869291271984757715112193740125897393056188230825024,
    decodeIntegerRow 64 9 4 5895092288869294413668522461618103762681272765593737987327920,
    decodeIntegerRow 64 9 4 5895092288869291581875954699771492070453468867408132417196720,
    decodeIntegerRow 64 9 4 5895092288869291620671692178549095056538259559885450066616384,
    decodeIntegerRow 64 9 4 5895092288869291581886596937714691221747101326316340481070016,
    decodeIntegerRow 64 9 4 5895092288869291620672874629162217947374768243019226898931280,
    decodeIntegerRow 64 9 4 5895092288869291900398136239472255634183890867093465363270480,
    decodeIntegerRow 64 9 4 5895092288869288757948130521007648145207243710824326101493696,
    decodeIntegerRow 64 9 4 5895092288869291620671706756926756137177442749682915888698816,
    decodeIntegerRow 64 9 4 5895092288869291589644786773789853394410900149804230417692240,
    decodeIntegerRow 64 9 4 5895092288869294413668522642092525357263617933241496393737040,
    decodeIntegerRow 64 9 4 5895092288869291899536113524283027160564998950806406320130496,
    decodeIntegerRow 64 9 4 5959783577602245191316528758980421348080702088559672150832576,
    decodeIntegerRow 64 9 4 5887894509262984425549844117674526267544672206867883562060720,
    decodeIntegerRow 64 9 4 654921512902220312372407621943211075125339496505473163103920,
    decodeIntegerRow 64 9 4 6476524953294345484350231451343591452835166211008873704614336,
    decodeIntegerRow 64 9 4 5887913986080406316453579395750207246853812550569020549411776,
    decodeIntegerRow 64 9 4 5830398836045513325659484627090354986563160575011470718428080,
    decodeIntegerRow 64 9 4 5312062278949743158518961834282499588459069696090502127036080,
    decodeIntegerRow 64 9 4 655098995734941926667038685919480811168003461504996538009536,
    decodeIntegerRow 64 9 4 654921512902220312372407621943211075125339496485137896360880,
    decodeIntegerRow 64 9 4 5313659624444237687170641410068927212843045381269223779673664,
    decodeIntegerRow 64 9 4 5959783577602245191316528758980421348080702090206773313262144,
    decodeIntegerRow 64 9 4 5902290068475598745971028743737992398133539385224692158447280,
    decodeIntegerRow 64 9 4 5312062278949743158518961834282499588459069696088239629644720,
    decodeIntegerRow 64 9 4 11135085582003641244853834175493037854510208130750509984588864,
    decodeIntegerRow 64 9 4 5887913986080406316453579395750207246853812550386257258721344,
    decodeIntegerRow 64 9 4 5959785741693069845861388234322163679115051015617213439583920,
    decodeIntegerRow 64 9 4 5895092288869291900398136239472259826637234281798281396764240,
    decodeIntegerRow 64 9 4 5895092288869294413572742340404832840071654095704088207754304,
    decodeIntegerRow 64 9 4 5895092288869291581886596937714352557679670958097594236784704,
    decodeIntegerRow 64 9 4 5895092288869291550847998232253352933388011424464155853577040,
    decodeIntegerRow 64 9 4 5895092288869294413668522642092563038923438473783945571673680,
    decodeIntegerRow 64 9 4 5895092288869291271984759337129495686221995263019049419671104,
    decodeIntegerRow 64 9 4 5895092288869291620671706756929808248884506074616339838333504,
    decodeIntegerRow 64 9 4 5895092288869291581876086087623004865732284563157416179680080]

def cols_right2 (r : LeftIndex 5 5 3) : List ℤ := cols_right2Data.getD (leftPosition 5 5 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_4 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_5 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_6 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_7 : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 5 3) : (tripleIndices 8 1 8).map (fun j => (right2Middle5 5 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_1_4
  · exact cols_right2_eq_0_1_5
  · exact cols_right2_eq_0_1_6
  · exact cols_right2_eq_0_1_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_1_1_4
  · exact cols_right2_eq_1_1_5
  · exact cols_right2_eq_1_1_6
  · exact cols_right2_eq_1_1_7
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_0_4
  · exact cols_right2_eq_2_0_5
  · exact cols_right2_eq_2_0_6
  · exact cols_right2_eq_2_0_7
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_1_2
  · exact cols_right2_eq_2_1_3
  · exact cols_right2_eq_2_1_4
  · exact cols_right2_eq_2_1_5
  · exact cols_right2_eq_2_1_6
  · exact cols_right2_eq_2_1_7
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_0_4
  · exact cols_right2_eq_3_0_5
  · exact cols_right2_eq_3_0_6
  · exact cols_right2_eq_3_0_7
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_1_2
  · exact cols_right2_eq_3_1_3
  · exact cols_right2_eq_3_1_4
  · exact cols_right2_eq_3_1_5
  · exact cols_right2_eq_3_1_6
  · exact cols_right2_eq_3_1_7

theorem product0_eq : HexagonAtoms553.outerABC * HexagonAtoms553.assocABC = HexagonAtoms553.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms553.assocABC * HexagonAtoms553.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms553.innerRightABC * HexagonAtoms553.assocABC = HexagonAtoms553.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms553.inverseACB * right0Middle5 5 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms553.innerACB * right1Middle5 5 3 = right1Middle5 5 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms553.assocBCA * left0Middle5 5 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms553.innerRightABC * left1Middle5 5 3 = left1Middle5 5 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 8) (n := Fin 4 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms553.assocCAB * right2Middle5 5 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn553

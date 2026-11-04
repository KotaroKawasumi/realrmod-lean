import RMod.BrundanEllis.StackingReferenceHexagonAtoms633
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn633
open Superfusion

theorem innerACB_alias : HexagonAtoms633.innerACB = HexagonAtoms633.innerABC :=
  HexagonAtoms633.innerACB_eq.symm.trans HexagonAtoms633.innerABC_eq

theorem assocCAB_alias : HexagonAtoms633.assocCAB = HexagonAtoms633.assocBAC :=
  HexagonAtoms633.assocCAB_eq.symm.trans HexagonAtoms633.assocBAC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094445603,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094603067,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510108774827,
    decodeIntegerRow 32 3 1 926510099208889,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510051379199,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926509707005431,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926499634072717,
    decodeIntegerRow 32 3 1 926506607641519,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 926227664889439,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 923968228597591,
    decodeIntegerRow 32 3 1 1544183490709867,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 857879717061037,
    decodeIntegerRow 32 3 1 903633301970959]

def rows_outerABC (r : LeftIndex 3 3 6) : List ℤ := rows_outerABCData.getD (leftPosition 3 3 6 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 3 6) : (tripleIndices 4 2 4).map ((HexagonAtoms633.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_2_1_0
  · exact rows_outerABC_eq_2_1_1
  · exact rows_outerABC_eq_2_1_2
  · exact rows_outerABC_eq_2_1_3
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3
  · exact rows_outerABC_eq_3_1_0
  · exact rows_outerABC_eq_3_1_1
  · exact rows_outerABC_eq_3_1_2
  · exact rows_outerABC_eq_3_1_3

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 927639649952356,
    decodeIntegerRow 32 3 1 927074886540232,
    decodeIntegerRow 32 3 1 936676006994236,
    decodeIntegerRow 32 3 1 931593049115512,
    decodeIntegerRow 32 3 1 1018003316990044,
    decodeIntegerRow 32 3 1 972256705530808,
    decodeIntegerRow 32 3 1 1749949098579204,
    decodeIntegerRow 32 3 1 1338229596522248,
    decodeIntegerRow 32 3 1 925380558034276,
    decodeIntegerRow 32 3 1 925945340581192,
    decodeIntegerRow 32 3 1 916344179731516,
    decodeIntegerRow 32 3 1 921427135484152,
    decodeIntegerRow 32 3 1 835016871625564,
    decodeIntegerRow 32 3 1 880763482848568,
    decodeIntegerRow 32 3 1 103071090298884,
    decodeIntegerRow 32 3 1 514790592382088,
    decodeIntegerRow 32 3 1 102820041795768,
    decodeIntegerRow 32 3 1 1338355120760676,
    decodeIntegerRow 32 3 1 1018031211265288,
    decodeIntegerRow 32 3 1 880749536183356,
    decodeIntegerRow 32 3 1 936679106358472,
    decodeIntegerRow 32 3 1 921425590053724,
    decodeIntegerRow 32 3 1 925380194528632,
    decodeIntegerRow 32 3 1 927075058721284,
    decodeIntegerRow 32 3 1 102820041822008,
    decodeIntegerRow 32 3 1 1338355120708196,
    decodeIntegerRow 32 3 1 1018031211501448,
    decodeIntegerRow 32 3 1 880749535711036,
    decodeIntegerRow 32 3 1 936679108483912,
    decodeIntegerRow 32 3 1 921425585802844,
    decodeIntegerRow 32 3 1 925380213657592,
    decodeIntegerRow 32 3 1 927075020463364]

def rows_innerRightABC (r : RightIndex 6 3 3) : List ℤ := rows_innerRightABCData.getD (rightPosition 6 3 3 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 6 3 3) : (tripleIndices 4 2 4).map ((HexagonAtoms633.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_1_2
  · exact rows_innerRightABC_eq_0_1_3
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_1_1_2
  · exact rows_innerRightABC_eq_1_1_3
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_0_2
  · exact rows_innerRightABC_eq_2_0_3
  · exact rows_innerRightABC_eq_2_1_0
  · exact rows_innerRightABC_eq_2_1_1
  · exact rows_innerRightABC_eq_2_1_2
  · exact rows_innerRightABC_eq_2_1_3
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_0_2
  · exact rows_innerRightABC_eq_3_0_3
  · exact rows_innerRightABC_eq_3_1_0
  · exact rows_innerRightABC_eq_3_1_1
  · exact rows_innerRightABC_eq_3_1_2
  · exact rows_innerRightABC_eq_3_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 925943704803040,
    decodeIntegerRow 32 3 1 927640577846560,
    decodeIntegerRow 32 3 1 921426532831840,
    decodeIntegerRow 32 3 1 936677472705760,
    decodeIntegerRow 32 3 1 102938592465364,
    decodeIntegerRow 32 3 1 1338306305779084,
    decodeIntegerRow 32 3 1 1017954502008452,
    decodeIntegerRow 32 3 1 880882033990628,
    decodeIntegerRow 32 3 1 927639028165252,
    decodeIntegerRow 32 3 1 927073384685212,
    decodeIntegerRow 32 3 1 936677644898476,
    decodeIntegerRow 32 3 1 931594000396684,
    decodeIntegerRow 32 3 1 1338278411503840,
    decodeIntegerRow 32 3 1 1750067649248800,
    decodeIntegerRow 32 3 1 880630985513760,
    decodeIntegerRow 32 3 1 834940162604960,
    decodeIntegerRow 32 3 1 880630985041364,
    decodeIntegerRow 32 3 1 1018080026483084,
    decodeIntegerRow 32 3 1 514741777400452,
    decodeIntegerRow 32 3 1 1750067649222628,
    decodeIntegerRow 32 3 1 916342546084960,
    decodeIntegerRow 32 3 1 931593996142240,
    decodeIntegerRow 32 3 1 927639047296480,
    decodeIntegerRow 32 3 1 925946765903200,
    decodeIntegerRow 32 3 1 835065686607200,
    decodeIntegerRow 32 3 1 880882033518240,
    decodeIntegerRow 32 3 1 102938592491680,
    decodeIntegerRow 32 3 1 514713883125280,
    decodeIntegerRow 32 3 1 921426537080452,
    decodeIntegerRow 32 3 1 916342718266012,
    decodeIntegerRow 32 3 1 927076522312876,
    decodeIntegerRow 32 3 1 927640596979084]

def rows_inverseACB (r : LeftIndex 6 3 3) : List ℤ := rows_inverseACBData.getD (leftPosition 6 3 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 3 3) : (tripleIndices 4 2 4).map ((HexagonAtoms633.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 1521306698438614,
    decodeIntegerRow 32 3 1 1063770849234418,
    decodeIntegerRow 32 3 1 651988585005754,
    decodeIntegerRow 32 3 1 285959905857598,
    decodeIntegerRow 32 3 1 926510352705274,
    decodeIntegerRow 32 3 1 926508975213442,
    decodeIntegerRow 32 3 1 926508889115626,
    decodeIntegerRow 32 3 1 926510610987058,
    decodeIntegerRow 32 3 1 651988584927022,
    decodeIntegerRow 32 3 1 1567060283335414,
    decodeIntegerRow 32 3 1 331713490780642,
    decodeIntegerRow 32 3 1 1063770849076954,
    decodeIntegerRow 32 3 1 926511299732002,
    decodeIntegerRow 32 3 1 926510610986086,
    decodeIntegerRow 32 3 1 926510352707218,
    decodeIntegerRow 32 3 1 926511213642934,
    decodeIntegerRow 32 3 1 924815523584326,
    decodeIntegerRow 32 3 1 933853247494078,
    decodeIntegerRow 32 3 1 934418135264854,
    decodeIntegerRow 32 3 1 923120936799502,
    decodeIntegerRow 32 3 1 926419438031466,
    decodeIntegerRow 32 3 1 926489173719502,
    decodeIntegerRow 32 3 1 926551935838726,
    decodeIntegerRow 32 3 1 926607724389122,
    decodeIntegerRow 32 3 1 918602081221918,
    decodeIntegerRow 32 3 1 923120943176794,
    decodeIntegerRow 32 3 1 924815510829742,
    decodeIntegerRow 32 3 1 919166911597066,
    decodeIntegerRow 32 3 1 926551935838738,
    decodeIntegerRow 32 3 1 926412464462666,
    decodeIntegerRow 32 3 1 926600750820318,
    decodeIntegerRow 32 3 1 926489173719526]

def rows_assocBCA (r : RightIndex 3 3 6) : List ℤ := rows_assocBCAData.getD (rightPosition 3 3 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 3 6) : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_1_0
  · exact rows_assocBCA_eq_2_1_1
  · exact rows_assocBCA_eq_2_1_2
  · exact rows_assocBCA_eq_2_1_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_1_0
  · exact rows_assocBCA_eq_3_1_1
  · exact rows_assocBCA_eq_3_1_2
  · exact rows_assocBCA_eq_3_1_3

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 32 3 1 916343396390560,
    decodeIntegerRow 32 3 1 931595356631200,
    decodeIntegerRow 32 3 1 927639727540960,
    decodeIntegerRow 32 3 1 925945065292000,
    decodeIntegerRow 32 3 1 102882803809972,
    decodeIntegerRow 32 3 1 1338166834140604,
    decodeIntegerRow 32 3 1 1018024237827692,
    decodeIntegerRow 32 3 1 880770456679844,
    decodeIntegerRow 32 3 1 931595394897868,
    decodeIntegerRow 32 3 1 936676773335236,
    decodeIntegerRow 32 3 1 925945061040148,
    decodeIntegerRow 32 3 1 925380463435996,
    decodeIntegerRow 32 3 1 514853354238880,
    decodeIntegerRow 32 3 1 102882804046240,
    decodeIntegerRow 32 3 1 972249732224480,
    decodeIntegerRow 32 3 1 1018024237801440,
    decodeIntegerRow 32 3 1 1338417883089868,
    decodeIntegerRow 32 3 1 1750011860567236,
    decodeIntegerRow 32 3 1 880742562352148,
    decodeIntegerRow 32 3 1 835009898187996,
    decodeIntegerRow 32 3 1 931592295531040,
    decodeIntegerRow 32 3 1 936678323011360,
    decodeIntegerRow 32 3 1 925945405414240,
    decodeIntegerRow 32 3 1 925380291249760,
    decodeIntegerRow 32 3 1 1750011860803360,
    decodeIntegerRow 32 3 1 514602306234400,
    decodeIntegerRow 32 3 1 835009898161760,
    decodeIntegerRow 32 3 1 972277626447200,
    decodeIntegerRow 32 3 1 916341846702772,
    decodeIntegerRow 32 3 1 931592257270204,
    decodeIntegerRow 32 3 1 927639899728492,
    decodeIntegerRow 32 3 1 925945409665444]

def rows_assocBAC (r : RightIndex 3 6 3) : List ℤ := rows_assocBACData.getD (rightPosition 3 6 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 3 6 3) : (tripleIndices 4 2 4).map ((HexagonAtoms633.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_2_1_2
  · exact rows_assocBAC_eq_2_1_3
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1
  · exact rows_assocBAC_eq_3_1_2
  · exact rows_assocBAC_eq_3_1_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 925943704803040,
    decodeIntegerRow 32 3 1 927640577846560,
    decodeIntegerRow 32 3 1 921426532831840,
    decodeIntegerRow 32 3 1 936677472705760,
    decodeIntegerRow 32 3 1 102938592465364,
    decodeIntegerRow 32 3 1 1338306305779084,
    decodeIntegerRow 32 3 1 1017954502008452,
    decodeIntegerRow 32 3 1 880882033990628,
    decodeIntegerRow 32 3 1 927639028165252,
    decodeIntegerRow 32 3 1 927073384685212,
    decodeIntegerRow 32 3 1 936677644898476,
    decodeIntegerRow 32 3 1 931594000396684,
    decodeIntegerRow 32 3 1 1338278411503840,
    decodeIntegerRow 32 3 1 1750067649248800,
    decodeIntegerRow 32 3 1 880630985513760,
    decodeIntegerRow 32 3 1 834940162604960,
    decodeIntegerRow 32 3 1 880630985041364,
    decodeIntegerRow 32 3 1 1018080026483084,
    decodeIntegerRow 32 3 1 514741777400452,
    decodeIntegerRow 32 3 1 1750067649222628,
    decodeIntegerRow 32 3 1 916342546084960,
    decodeIntegerRow 32 3 1 931593996142240,
    decodeIntegerRow 32 3 1 927639047296480,
    decodeIntegerRow 32 3 1 925946765903200,
    decodeIntegerRow 32 3 1 835065686607200,
    decodeIntegerRow 32 3 1 880882033518240,
    decodeIntegerRow 32 3 1 102938592491680,
    decodeIntegerRow 32 3 1 514713883125280,
    decodeIntegerRow 32 3 1 921426537080452,
    decodeIntegerRow 32 3 1 916342718266012,
    decodeIntegerRow 32 3 1 927076522312876,
    decodeIntegerRow 32 3 1 927640596979084]

def cols_assocABC (r : LeftIndex 6 3 3) : List ℤ := cols_assocABCData.getD (leftPosition 6 3 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 3 3) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms633.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_2_1_2
  · exact cols_assocABC_eq_2_1_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1
  · exact cols_assocABC_eq_3_1_2
  · exact cols_assocABC_eq_3_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 9 4 188666821706363473653073447672,
    decodeIntegerRow 32 9 4 1528436762256406449057412448632,
    decodeIntegerRow 32 9 4 1566117791834376407737129651912,
    decodeIntegerRow 32 9 4 192853602770582357947682175928,
    decodeIntegerRow 32 9 4 1716841910151667061280370030792,
    decodeIntegerRow 32 9 4 1716841910146923329596930313032,
    decodeIntegerRow 32 9 4 1716841910146789912143333032968,
    decodeIntegerRow 32 9 4 1716841910151652237118858743672,
    decodeIntegerRow 32 9 4 1566117791834376407485736801272,
    decodeIntegerRow 32 9 4 3240830217521930126679173274232,
    decodeIntegerRow 32 9 4 3245016998586149010979980730312,
    decodeIntegerRow 32 9 4 1528436762256406448806708345528,
    decodeIntegerRow 32 9 4 1716841910145722572514554372552,
    decodeIntegerRow 32 9 4 1716841910151652237118863467592,
    decodeIntegerRow 32 9 4 1716841910151667061280373809928,
    decodeIntegerRow 32 9 4 1716841910145589155060956987512,
    decodeIntegerRow 32 9 4 1717074828160040628718019052232,
    decodeIntegerRow 32 9 4 1716870626065764738867285587272,
    decodeIntegerRow 32 9 4 1716864882881863206306011717128,
    decodeIntegerRow 32 9 4 1717074190028495993403013518712,
    decodeIntegerRow 32 9 4 1716841874645873101882692445432,
    decodeIntegerRow 32 9 4 1716841905769496677068430179192,
    decodeIntegerRow 32 9 4 1716841906644848590120529052872,
    decodeIntegerRow 32 9 4 1716841874743134425555147875768,
    decodeIntegerRow 32 9 4 1716818937410650927740330421192,
    decodeIntegerRow 32 9 4 1717074190028496196752279785032,
    decodeIntegerRow 32 9 4 1717074828160040791397432065288,
    decodeIntegerRow 32 9 4 1716813194226749390660183967352,
    decodeIntegerRow 32 9 4 1716841906644848590120529047032,
    decodeIntegerRow 32 9 4 1716841945549378059102701212792,
    decodeIntegerRow 32 9 4 1716841945646639382775156643272,
    decodeIntegerRow 32 9 4 1716841905769496677068430173368]

def cols_right0 (r : LeftIndex 6 3 3) : List ℤ := cols_right0Data.getD (leftPosition 6 3 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 3 3) : (tripleIndices 4 2 4).map (fun j => (right0Middle6 3 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_1_2
  · exact cols_right0_eq_2_1_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_1_2
  · exact cols_right0_eq_3_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 925381153248196,
    decodeIntegerRow 32 3 1 925946786100712,
    decodeIntegerRow 32 3 1 916342564150876,
    decodeIntegerRow 32 3 1 921426200147992,
    decodeIntegerRow 32 3 1 834940162460632,
    decodeIntegerRow 32 3 1 880630985264476,
    decodeIntegerRow 32 3 1 102952539379928,
    decodeIntegerRow 32 3 1 514741777256124,
    decodeIntegerRow 32 3 1 925943686730968,
    decodeIntegerRow 32 3 1 927640585288516,
    decodeIntegerRow 32 3 1 921426544522408,
    decodeIntegerRow 32 3 1 936677452513756,
    decodeIntegerRow 32 3 1 880882033741276,
    decodeIntegerRow 32 3 1 1017954502152808,
    decodeIntegerRow 32 3 1 514713882980924,
    decodeIntegerRow 32 3 1 1750081596609512,
    decodeIntegerRow 32 3 1 514713883217112,
    decodeIntegerRow 32 3 1 102938592714716,
    decodeIntegerRow 32 3 1 972138155084248,
    decodeIntegerRow 32 3 1 1017954502100284,
    decodeIntegerRow 32 3 1 931593663461956,
    decodeIntegerRow 32 3 1 936677490777832,
    decodeIntegerRow 32 3 1 925943684611036,
    decodeIntegerRow 32 3 1 925379599314712,
    decodeIntegerRow 32 3 1 1750067648999516,
    decodeIntegerRow 32 3 1 514741777492328,
    decodeIntegerRow 32 3 1 834940162513084,
    decodeIntegerRow 32 3 1 972389203561192,
    decodeIntegerRow 32 3 1 916342525887448,
    decodeIntegerRow 32 3 1 931594007835076,
    decodeIntegerRow 32 3 1 927639039858088,
    decodeIntegerRow 32 3 1 925946783969116]

def cols_left0 (r : LeftIndex 6 3 3) : List ℤ := cols_left0Data.getD (leftPosition 6 3 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 3 3) : (tripleIndices 4 2 4).map (fun j => (left0Middle6 3 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_1_2
  · exact cols_left0_eq_2_1_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_1_2
  · exact cols_left0_eq_3_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 17 8 1183969923876137251757819289855142391040,
    decodeIntegerRow 32 17 8 1183943240494982327738561885431419720960,
    decodeIntegerRow 32 17 8 1183955748499624959846496864434888541440,
    decodeIntegerRow 32 17 8 1183955840829663558199504675522859900160,
    decodeIntegerRow 32 17 8 2363814862047903911260536557602454461216,
    decodeIntegerRow 32 17 8 135192184645080685902186685370458265888,
    decodeIntegerRow 32 17 8 1179873240063044452374169123023998188256,
    decodeIntegerRow 32 17 8 1187584737216687439313125350955596791008,
    decodeIntegerRow 32 17 8 1183943240494982327690069071376133035744,
    decodeIntegerRow 32 17 8 1183941670884329994129391731058063874272,
    decodeIntegerRow 32 17 8 1183955840829663558199672470727203452704,
    decodeIntegerRow 32 17 8 1183955846260842285997460281593355941152,
    decodeIntegerRow 32 17 8 2232719410115386559941920192556736236800,
    decodeIntegerRow 32 17 8 2363814862047903911260536041508015863040,
    decodeIntegerRow 32 17 8 1180326857543779806530980944356336313600,
    decodeIntegerRow 32 17 8 1179873240063044452374169124809792093440,
    decodeIntegerRow 32 17 8 2232719410453660668380010948741266365216,
    decodeIntegerRow 32 17 8 2363814861747215814871122036010655897888,
    decodeIntegerRow 32 17 8 1180326857542609307885866443469884652256,
    decodeIntegerRow 32 17 8 1179873240064084895614270903375526903008,
    decodeIntegerRow 32 17 8 1183968354265480867985715030433841583360,
    decodeIntegerRow 32 17 8 1183969923876140851864334295593533451520,
    decodeIntegerRow 32 17 8 1183955753930803701658857086785827298560,
    decodeIntegerRow 32 17 8 1183955748499624947389380895556901029120,
    decodeIntegerRow 32 17 8 2363814861747215814871122552105094329600,
    decodeIntegerRow 32 17 8 135192184306806577464095929185928285440,
    decodeIntegerRow 32 17 8 1179873240064084895614270901589732998400,
    decodeIntegerRow 32 17 8 1187584737217857937958239851842048451840,
    decodeIntegerRow 32 17 8 1183941670884326393936667278121259538144,
    decodeIntegerRow 32 17 8 1183968354265480867937222216390913333472,
    decodeIntegerRow 32 17 8 1183955846260842298454874553056805091104,
    decodeIntegerRow 32 17 8 1183955753930803701659024881990128088352]

def cols_right2 (r : LeftIndex 6 3 3) : List ℤ := cols_right2Data.getD (leftPosition 6 3 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 3 3) : (tripleIndices 4 2 4).map (fun j => (right2Middle6 3 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_1_2
  · exact cols_right2_eq_2_1_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_1_2
  · exact cols_right2_eq_3_1_3

theorem product0_eq : HexagonAtoms633.outerABC * HexagonAtoms633.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms633.assocBAC * HexagonAtoms633.innerABC = HexagonAtoms633.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms633.innerRightABC * HexagonAtoms633.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms633.inverseACB * right0Middle6 3 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms633.innerABC * right1Middle6 3 3 = right1Middle6 3 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms633.assocBCA * left0Middle6 3 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms633.innerRightBAC * left1Middle6 3 3 = left1Middle6 3 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms633.assocBAC * right2Middle6 3 3 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn633

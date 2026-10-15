import Paper2.Certificates.Q6CoverageCompact.Layer10Part009

namespace Paper2.Certificates.Q6.Coverage

def ntree10LLRLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨576,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨577,by decide⟩,⟨2,by decide⟩,⟨578,by decide⟩] | 2 => ![⟨579,by decide⟩,⟨580,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨581,by decide⟩,⟨582,by decide⟩,⟨583,by decide⟩] | 4 => ![⟨584,by decide⟩,⟨585,by decide⟩,⟨585,by decide⟩] | 5 => ![⟨586,by decide⟩,⟨586,by decide⟩,⟨585,by decide⟩] | 6 => ![⟨587,by decide⟩,⟨13,by decide⟩,⟨588,by decide⟩] | _ => ![⟨589,by decide⟩,⟨585,by decide⟩,⟨589,by decide⟩]

def ntree10LLRLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLLLRRL i else ntree10LLRLLLRRR (i - 8)

def ntree10LLRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRLLLRL i else ntree10LLRLLLRR (i - 16)

def ntree10LLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRLLLL i else ntree10LLRLLLR (i - 31)

def ntree10LLRLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨590,by decide⟩,⟨586,by decide⟩,⟨589,by decide⟩] | 1 => ![⟨591,by decide⟩,⟨592,by decide⟩,⟨589,by decide⟩] | 2 => ![⟨3,by decide⟩,⟨593,by decide⟩,⟨593,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨594,by decide⟩,⟨593,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨596,by decide⟩,⟨595,by decide⟩] | _ => ![⟨576,by decide⟩,⟨593,by decide⟩,⟨593,by decide⟩]

def ntree10LLRLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨577,by decide⟩,⟨594,by decide⟩,⟨597,by decide⟩] | 1 => ![⟨598,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 2 => ![⟨587,by decide⟩,⟨596,by decide⟩,⟨599,by decide⟩] | 3 => ![⟨584,by decide⟩,⟨600,by decide⟩,⟨600,by decide⟩] | 4 => ![⟨586,by decide⟩,⟨586,by decide⟩,⟨601,by decide⟩] | 5 => ![⟨585,by decide⟩,⟨585,by decide⟩,⟨585,by decide⟩] | 6 => ![⟨31,by decide⟩,⟨602,by decide⟩,⟨595,by decide⟩] | _ => ![⟨14,by decide⟩,⟨595,by decide⟩,⟨603,by decide⟩]

def ntree10LLRLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRLLRLLL i else ntree10LLRLLRLLR (i - 7)

def ntree10LLRLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨604,by decide⟩,⟨602,by decide⟩,⟨605,by decide⟩] | 1 => ![⟨579,by decide⟩,⟨606,by decide⟩,⟨603,by decide⟩] | 2 => ![⟨607,by decide⟩,⟨607,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨608,by decide⟩,⟨609,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨610,by decide⟩,⟨3,by decide⟩,⟨610,by decide⟩] | 5 => ![⟨611,by decide⟩,⟨2,by decide⟩,⟨610,by decide⟩] | 6 => ![⟨612,by decide⟩,⟨580,by decide⟩,⟨613,by decide⟩] | _ => ![⟨614,by decide⟩,⟨13,by decide⟩,⟨613,by decide⟩]

def ntree10LLRLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨582,by decide⟩,⟨582,by decide⟩,⟨615,by decide⟩] | 1 => ![⟨616,by decide⟩,⟨585,by decide⟩,⟨616,by decide⟩] | 2 => ![⟨617,by decide⟩,⟨586,by decide⟩,⟨616,by decide⟩] | 3 => ![⟨618,by decide⟩,⟨585,by decide⟩,⟨585,by decide⟩] | 4 => ![⟨619,by decide⟩,⟨13,by decide⟩,⟨620,by decide⟩] | 5 => ![⟨621,by decide⟩,⟨592,by decide⟩,⟨616,by decide⟩] | 6 => ![⟨622,by decide⟩,⟨582,by decide⟩,⟨623,by decide⟩] | _ => ![⟨610,by decide⟩,⟨3,by decide⟩,⟨610,by decide⟩]

def ntree10LLRLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLLRLRL i else ntree10LLRLLRLRR (i - 8)

def ntree10LLRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRLLRLL i else ntree10LLRLLRLR (i - 15)

def ntree10LLRLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨611,by decide⟩,⟨2,by decide⟩,⟨624,by decide⟩] | 1 => ![⟨613,by decide⟩,⟨15,by decide⟩,⟨613,by decide⟩] | 2 => ![⟨614,by decide⟩,⟨13,by decide⟩,⟨625,by decide⟩] | 3 => ![⟨616,by decide⟩,⟨626,by decide⟩,⟨616,by decide⟩] | 4 => ![⟨617,by decide⟩,⟨627,by decide⟩,⟨628,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨629,by decide⟩,⟨630,by decide⟩] | 6 => ![⟨31,by decide⟩,⟨631,by decide⟩,⟨630,by decide⟩] | _ => ![⟨51,by decide⟩,⟨632,by decide⟩,⟨633,by decide⟩]

def ntree10LLRLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨634,by decide⟩,⟨15,by decide⟩,⟨634,by decide⟩] | 1 => ![⟨635,by decide⟩,⟨31,by decide⟩,⟨636,by decide⟩] | 2 => ![⟨580,by decide⟩,⟨580,by decide⟩,⟨637,by decide⟩] | 3 => ![⟨638,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨639,by decide⟩,⟨640,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨641,by decide⟩,⟨642,by decide⟩,⟨630,by decide⟩] | 6 => ![⟨643,by decide⟩,⟨644,by decide⟩,⟨633,by decide⟩] | _ => ![⟨645,by decide⟩,⟨646,by decide⟩,⟨645,by decide⟩]

def ntree10LLRLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLLRRLL i else ntree10LLRLLRRLR (i - 8)

def ntree10LLRLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨647,by decide⟩,⟨648,by decide⟩,⟨645,by decide⟩] | 1 => ![⟨649,by decide⟩,⟨650,by decide⟩,⟨649,by decide⟩] | 2 => ![⟨651,by decide⟩,⟨652,by decide⟩,⟨649,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨593,by decide⟩,⟨653,by decide⟩] | 4 => ![⟨46,by decide⟩,⟨594,by decide⟩,⟨653,by decide⟩] | 5 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨654,by decide⟩] | 6 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨654,by decide⟩] | _ => ![⟨51,by decide⟩,⟨595,by decide⟩,⟨655,by decide⟩]

def ntree10LLRLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨50,by decide⟩,⟨596,by decide⟩,⟨655,by decide⟩] | 1 => ![⟨610,by decide⟩,⟨593,by decide⟩,⟨656,by decide⟩] | 2 => ![⟨613,by decide⟩,⟨595,by decide⟩,⟨657,by decide⟩] | 3 => ![⟨616,by decide⟩,⟨600,by decide⟩,⟨658,by decide⟩] | 4 => ![⟨585,by decide⟩,⟨585,by decide⟩,⟨659,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨660,by decide⟩] | 6 => ![⟨67,by decide⟩,⟨602,by decide⟩,⟨655,by decide⟩] | _ => ![⟨14,by decide⟩,⟨661,by decide⟩,⟨662,by decide⟩]

def ntree10LLRLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLLRRRL i else ntree10LLRLLRRRR (i - 8)

def ntree10LLRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRLLRRL i else ntree10LLRLLRRR (i - 16)

def ntree10LLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRLLRL i else ntree10LLRLLRR (i - 31)

def ntree10LLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLRLLL i else ntree10LLRLLR (i - 63)

def ntree10LLRLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨33,by decide⟩,⟨663,by decide⟩,⟨662,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨664,by decide⟩,⟨665,by decide⟩] | 2 => ![⟨634,by decide⟩,⟨595,by decide⟩,⟨666,by decide⟩] | 3 => ![⟨635,by decide⟩,⟨31,by decide⟩,⟨634,by decide⟩] | 4 => ![⟨667,by decide⟩,⟨668,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨639,by decide⟩,⟨607,by decide⟩,⟨51,by decide⟩] | _ => ![⟨608,by decide⟩,⟨607,by decide⟩,⟨14,by decide⟩]

def ntree10LLRLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨669,by decide⟩,⟨670,by decide⟩,⟨76,by decide⟩] | 1 => ![⟨671,by decide⟩,⟨671,by decide⟩,⟨3,by decide⟩] | 2 => ![⟨672,by decide⟩,⟨671,by decide⟩,⟨7,by decide⟩] | 3 => ![⟨673,by decide⟩,⟨674,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨675,by decide⟩,⟨675,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨676,by decide⟩,⟨675,by decide⟩,⟨578,by decide⟩] | 6 => ![⟨677,by decide⟩,⟨675,by decide⟩,⟨7,by decide⟩] | _ => ![⟨678,by decide⟩,⟨679,by decide⟩,⟨14,by decide⟩]

def ntree10LLRLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRLRLLLL i else ntree10LLRLRLLLR (i - 7)

def ntree10LLRLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨680,by decide⟩,⟨681,by decide⟩,⟨583,by decide⟩] | 1 => ![⟨682,by decide⟩,⟨682,by decide⟩,⟨585,by decide⟩] | 2 => ![⟨683,by decide⟩,⟨585,by decide⟩,⟨585,by decide⟩] | 3 => ![⟨684,by decide⟩,⟨685,by decide⟩,⟨588,by decide⟩] | 4 => ![⟨686,by decide⟩,⟨682,by decide⟩,⟨589,by decide⟩] | 5 => ![⟨687,by decide⟩,⟨685,by decide⟩,⟨14,by decide⟩] | 6 => ![⟨583,by decide⟩,⟨615,by decide⟩,⟨583,by decide⟩] | _ => ![⟨3,by decide⟩,⟨688,by decide⟩,⟨3,by decide⟩]

def ntree10LLRLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨689,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨690,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨691,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨692,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨578,by decide⟩,⟨688,by decide⟩,⟨578,by decide⟩] | 5 => ![⟨693,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 6 => ![⟨694,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨695,by decide⟩,⟨692,by decide⟩,⟨696,by decide⟩]

def ntree10LLRLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLRLLRL i else ntree10LLRLRLLRR (i - 8)

def ntree10LLRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRLRLLL i else ntree10LLRLRLLR (i - 15)

def ntree10LLRLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨588,by decide⟩,⟨692,by decide⟩,⟨588,by decide⟩] | 1 => ![⟨697,by decide⟩,⟨698,by decide⟩,⟨698,by decide⟩] | 2 => ![⟨699,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨674,by decide⟩,⟨674,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨700,by decide⟩,⟨701,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨702,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨685,by decide⟩,⟨685,by decide⟩,⟨15,by decide⟩] | _ => ![⟨703,by decide⟩,⟨704,by decide⟩,⟨705,by decide⟩]

def ntree10LLRLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨687,by decide⟩,⟨706,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨707,by decide⟩,⟨708,by decide⟩,⟨709,by decide⟩] | 2 => ![⟨710,by decide⟩,⟨671,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨711,by decide⟩,⟨674,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨712,by decide⟩,⟨675,by decide⟩,⟨610,by decide⟩] | 5 => ![⟨713,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 6 => ![⟨714,by decide⟩,⟨679,by decide⟩,⟨613,by decide⟩] | _ => ![⟨715,by decide⟩,⟨15,by decide⟩,⟨613,by decide⟩]

def ntree10LLRLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLRLRLL i else ntree10LLRLRLRLR (i - 8)

def ntree10LLRLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨681,by decide⟩,⟨681,by decide⟩,⟨615,by decide⟩] | 1 => ![⟨716,by decide⟩,⟨682,by decide⟩,⟨616,by decide⟩] | 2 => ![⟨717,by decide⟩,⟨685,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨718,by decide⟩,⟨585,by decide⟩,⟨585,by decide⟩] | 4 => ![⟨719,by decide⟩,⟨685,by decide⟩,⟨620,by decide⟩] | 5 => ![⟨623,by decide⟩,⟨615,by decide⟩,⟨623,by decide⟩] | 6 => ![⟨3,by decide⟩,⟨720,by decide⟩,⟨720,by decide⟩] | _ => ![⟨51,by decide⟩,⟨721,by decide⟩,⟨722,by decide⟩]

def ntree10LLRLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨713,by decide⟩,⟨723,by decide⟩,⟨723,by decide⟩] | 1 => ![⟨715,by decide⟩,⟨724,by decide⟩,⟨725,by decide⟩] | 2 => ![⟨718,by decide⟩,⟨726,by decide⟩,⟨726,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨727,by decide⟩,⟨727,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨728,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨729,by decide⟩,⟨730,by decide⟩,⟨731,by decide⟩] | 6 => ![⟨732,by decide⟩,⟨733,by decide⟩,⟨733,by decide⟩] | _ => ![⟨734,by decide⟩,⟨148,by decide⟩,⟨148,by decide⟩]

def ntree10LLRLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLRLRRL i else ntree10LLRLRLRRR (i - 8)

def ntree10LLRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRLRLRL i else ntree10LLRLRLRR (i - 16)

def ntree10LLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRLRLL i else ntree10LLRLRLR (i - 31)

def ntree10LLRLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨717,by decide⟩,⟨735,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨736,by decide⟩,⟨737,by decide⟩,⟨610,by decide⟩] | 2 => ![⟨738,by decide⟩,⟨737,by decide⟩,⟨7,by decide⟩] | 3 => ![⟨739,by decide⟩,⟨740,by decide⟩,⟨645,by decide⟩] | 4 => ![⟨741,by decide⟩,⟨742,by decide⟩,⟨616,by decide⟩] | 5 => ![⟨743,by decide⟩,⟨742,by decide⟩,⟨589,by decide⟩] | _ => ![⟨47,by decide⟩,⟨688,by decide⟩,⟨47,by decide⟩]

def ntree10LLRLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨692,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨613,by decide⟩,⟨15,by decide⟩,⟨744,by decide⟩] | 3 => ![⟨585,by decide⟩,⟨698,by decide⟩,⟨698,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨51,by decide⟩,⟨702,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨745,by decide⟩,⟨14,by decide⟩] | _ => ![⟨634,by decide⟩,⟨148,by decide⟩,⟨731,by decide⟩]

def ntree10LLRLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRLRRLLL i else ntree10LLRLRRLLR (i - 7)

def ntree10LLRLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨746,by decide⟩,⟨747,by decide⟩,⟨634,by decide⟩] | 1 => ![⟨748,by decide⟩,⟨747,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨148,by decide⟩,⟨150,by decide⟩] | 3 => ![⟨749,by decide⟩,⟨747,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨750,by decide⟩,⟨685,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨751,by decide⟩,⟨752,by decide⟩,⟨753,by decide⟩] | 6 => ![⟨754,by decide⟩,⟨752,by decide⟩,⟨755,by decide⟩] | _ => ![⟨756,by decide⟩,⟨685,by decide⟩,⟨757,by decide⟩]

def ntree10LLRLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨758,by decide⟩,⟨13,by decide⟩,⟨757,by decide⟩] | 1 => ![⟨752,by decide⟩,⟨752,by decide⟩,⟨759,by decide⟩] | 2 => ![⟨690,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨760,by decide⟩] | 4 => ![⟨761,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 5 => ![⟨762,by decide⟩,⟨596,by decide⟩,⟨605,by decide⟩] | 6 => ![⟨699,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨763,by decide⟩,⟨13,by decide⟩,⟨764,by decide⟩]

def ntree10LLRLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLRRLRL i else ntree10LLRLRRLRR (i - 8)

def ntree10LLRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRLRRLL i else ntree10LLRLRRLR (i - 15)

def ntree10LLRLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨699,by decide⟩,⟨146,by decide⟩,⟨146,by decide⟩] | 1 => ![⟨763,by decide⟩,⟨13,by decide⟩,⟨765,by decide⟩] | 2 => ![⟨674,by decide⟩,⟨766,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨767,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨673,by decide⟩,⟨766,by decide⟩,⟨603,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨767,by decide⟩,⟨14,by decide⟩] | 6 => ![⟨685,by decide⟩,⟨768,by decide⟩,⟨595,by decide⟩] | _ => ![⟨703,by decide⟩,⟨768,by decide⟩,⟨605,by decide⟩]

def ntree10LLRLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨687,by decide⟩,⟨769,by decide⟩,⟨40,by decide⟩] | 1 => ![⟨707,by decide⟩,⟨159,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨729,by decide⟩,⟨685,by decide⟩,⟨634,by decide⟩] | 3 => ![⟨770,by decide⟩,⟨13,by decide⟩,⟨634,by decide⟩] | 4 => ![⟨771,by decide⟩,⟨685,by decide⟩,⟨772,by decide⟩] | 5 => ![⟨773,by decide⟩,⟨13,by decide⟩,⟨772,by decide⟩] | 6 => ![⟨734,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨774,by decide⟩,⟨752,by decide⟩,⟨775,by decide⟩]

def ntree10LLRLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLRRRLL i else ntree10LLRLRRRLR (i - 8)

def ntree10LLRLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨776,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨13,by decide⟩,⟨777,by decide⟩,⟨778,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨779,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨50,by decide⟩,⟨780,by decide⟩,⟨781,by decide⟩] | 4 => ![⟨634,by decide⟩,⟨15,by decide⟩,⟨634,by decide⟩] | 5 => ![⟨770,by decide⟩,⟨13,by decide⟩,⟨636,by decide⟩] | 6 => ![⟨772,by decide⟩,⟨782,by decide⟩,⟨772,by decide⟩] | _ => ![⟨773,by decide⟩,⟨783,by decide⟩,⟨784,by decide⟩]

def ntree10LLRLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨785,by decide⟩] | 2 => ![⟨772,by decide⟩,⟨168,by decide⟩,⟨772,by decide⟩] | 3 => ![⟨773,by decide⟩,⟨169,by decide⟩,⟨786,by decide⟩] | 4 => ![⟨674,by decide⟩,⟨787,by decide⟩,⟨630,by decide⟩] | 5 => ![⟨711,by decide⟩,⟨788,by decide⟩,⟨633,by decide⟩] | 6 => ![⟨634,by decide⟩,⟨15,by decide⟩,⟨636,by decide⟩] | _ => ![⟨685,by decide⟩,⟨685,by decide⟩,⟨35,by decide⟩]

def ntree10LLRLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLRRRRL i else ntree10LLRLRRRRR (i - 8)

def ntree10LLRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRLRRRL i else ntree10LLRLRRRR (i - 16)

def ntree10LLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRLRRL i else ntree10LLRLRRR (i - 31)

def ntree10LLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLRLRL i else ntree10LLRLRR (i - 63)

def ntree10LLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LLRLL i else ntree10LLRLR (i - 126)

def ntree10LLRRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨685,by decide⟩,⟨789,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨732,by decide⟩,⟨790,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨734,by decide⟩,⟨791,by decide⟩,⟨637,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨637,by decide⟩] | 4 => ![⟨685,by decide⟩,⟨792,by decide⟩,⟨630,by decide⟩] | 5 => ![⟨732,by decide⟩,⟨168,by decide⟩,⟨15,by decide⟩] | _ => ![⟨793,by decide⟩,⟨794,by decide⟩,⟨793,by decide⟩]

def ntree10LLRRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨795,by decide⟩,⟨796,by decide⟩,⟨793,by decide⟩] | 1 => ![⟨797,by decide⟩,⟨794,by decide⟩,⟨797,by decide⟩] | 2 => ![⟨798,by decide⟩,⟨796,by decide⟩,⟨797,by decide⟩] | 3 => ![⟨799,by decide⟩,⟨794,by decide⟩,⟨799,by decide⟩] | 4 => ![⟨800,by decide⟩,⟨796,by decide⟩,⟨799,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨660,by decide⟩] | 6 => ![⟨772,by decide⟩,⟨15,by decide⟩,⟨801,by decide⟩] | _ => ![⟨772,by decide⟩,⟨146,by decide⟩,⟨802,by decide⟩]

def ntree10LLRRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRRLLLLL i else ntree10LLRRLLLLR (i - 7)

def ntree10LLRRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨803,by decide⟩,⟨3,by decide⟩] | 2 => ![⟨7,by decide⟩,⟨804,by decide⟩,⟨7,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨805,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨806,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨576,by decide⟩,⟨807,by decide⟩,⟨807,by decide⟩] | 6 => ![⟨579,by decide⟩,⟨808,by decide⟩,⟨809,by decide⟩] | _ => ![⟨598,by decide⟩,⟨810,by decide⟩,⟨810,by decide⟩]

def ntree10LLRRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨607,by decide⟩,⟨607,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨598,by decide⟩,⟨811,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨812,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨608,by decide⟩,⟨813,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨186,by decide⟩,⟨593,by decide⟩,⟨593,by decide⟩] | 5 => ![⟨187,by decide⟩,⟨187,by decide⟩,⟨3,by decide⟩] | 6 => ![⟨187,by decide⟩,⟨814,by decide⟩,⟨593,by decide⟩] | _ => ![⟨815,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩]

def ntree10LLRRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRLLLRL i else ntree10LLRRLLLRR (i - 8)

def ntree10LLRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRRLLLL i else ntree10LLRRLLLR (i - 15)

def ntree10LLRRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨193,by decide⟩,⟨193,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨193,by decide⟩,⟨816,by decide⟩,⟨595,by decide⟩] | 2 => ![⟨817,by decide⟩,⟨818,by decide⟩,⟨818,by decide⟩] | 3 => ![⟨819,by decide⟩,⟨819,by decide⟩,⟨819,by decide⟩] | 4 => ![⟨820,by decide⟩,⟨821,by decide⟩,⟨821,by decide⟩] | 5 => ![⟨822,by decide⟩,⟨822,by decide⟩,⟨822,by decide⟩] | 6 => ![⟨823,by decide⟩,⟨824,by decide⟩,⟨824,by decide⟩] | _ => ![⟨825,by decide⟩,⟨825,by decide⟩,⟨826,by decide⟩]

def ntree10LLRRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨827,by decide⟩,⟨828,by decide⟩,⟨595,by decide⟩] | 1 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 2 => ![⟨199,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨201,by decide⟩,⟨828,by decide⟩,⟨595,by decide⟩] | 5 => ![⟨214,by decide⟩,⟨829,by decide⟩,⟨14,by decide⟩] | 6 => ![⟨830,by decide⟩,⟨831,by decide⟩,⟨830,by decide⟩] | _ => ![⟨832,by decide⟩,⟨833,by decide⟩,⟨830,by decide⟩]

def ntree10LLRRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRLLRLL i else ntree10LLRRLLRLR (i - 8)

def ntree10LLRRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨47,by decide⟩,⟨834,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨835,by decide⟩,⟨3,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨836,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨51,by decide⟩,⟨837,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨838,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨580,by decide⟩,⟨580,by decide⟩,⟨839,by decide⟩] | 6 => ![⟨638,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨580,by decide⟩,⟨840,by decide⟩,⟨15,by decide⟩]

def ntree10LLRRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨841,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨639,by decide⟩,⟨842,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨641,by decide⟩,⟨843,by decide⟩,⟨844,by decide⟩] | 3 => ![⟨641,by decide⟩,⟨845,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨643,by decide⟩,⟨580,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨229,by decide⟩,⟨846,by decide⟩,⟨47,by decide⟩] | 6 => ![⟨232,by decide⟩,⟨847,by decide⟩,⟨51,by decide⟩] | _ => ![⟨848,by decide⟩,⟨819,by decide⟩,⟨819,by decide⟩]

def ntree10LLRRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRLLRRL i else ntree10LLRRLLRRR (i - 8)

def ntree10LLRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRRLLRL i else ntree10LLRRLLRR (i - 16)

def ntree10LLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRRLLL i else ntree10LLRRLLR (i - 31)

def ntree10LLRRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨849,by decide⟩,⟨822,by decide⟩,⟨822,by decide⟩] | 1 => ![⟨850,by decide⟩,⟨851,by decide⟩,⟨850,by decide⟩] | 2 => ![⟨852,by decide⟩,⟨853,by decide⟩,⟨850,by decide⟩] | 3 => ![⟨239,by decide⟩,⟨854,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨252,by decide⟩,⟨855,by decide⟩,⟨630,by decide⟩] | 5 => ![⟨201,by decide⟩,⟨856,by decide⟩,⟨630,by decide⟩] | _ => ![⟨857,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩]

def ntree10LLRRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨845,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨858,by decide⟩,⟨859,by decide⟩,⟨860,by decide⟩] | 2 => ![⟨861,by decide⟩,⟨862,by decide⟩,⟨630,by decide⟩] | 3 => ![⟨76,by decide⟩,⟨863,by decide⟩,⟨76,by decide⟩] | 4 => ![⟨667,by decide⟩,⟨864,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨256,by decide⟩,⟨865,by decide⟩,⟨653,by decide⟩] | 6 => ![⟨257,by decide⟩,⟨257,by decide⟩,⟨654,by decide⟩] | _ => ![⟨866,by decide⟩,⟨867,by decide⟩,⟨655,by decide⟩]

def ntree10LLRRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRRLRLLL i else ntree10LLRRLRLLR (i - 7)

def ntree10LLRRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨264,by decide⟩,⟨868,by decide⟩,⟨655,by decide⟩] | 1 => ![⟨265,by decide⟩,⟨265,by decide⟩,⟨660,by decide⟩] | 2 => ![⟨272,by decide⟩,⟨869,by decide⟩,⟨662,by decide⟩] | 3 => ![⟨638,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨675,by decide⟩,⟨675,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨677,by decide⟩,⟨870,by decide⟩,⟨7,by decide⟩] | 6 => ![⟨678,by decide⟩,⟨871,by decide⟩,⟨14,by decide⟩] | _ => ![⟨685,by decide⟩,⟨685,by decide⟩,⟨15,by decide⟩]

def ntree10LLRRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨707,by decide⟩,⟨872,by decide⟩,⟨274,by decide⟩] | 1 => ![⟨685,by decide⟩,⟨873,by decide⟩,⟨274,by decide⟩] | 2 => ![⟨687,by decide⟩,⟨874,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨875,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 4 => ![⟨287,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨281,by decide⟩,⟨281,by decide⟩,⟨876,by decide⟩] | 6 => ![⟨281,by decide⟩,⟨877,by decide⟩,⟨15,by decide⟩] | _ => ![⟨878,by decide⟩,⟨819,by decide⟩,⟨819,by decide⟩]

def ntree10LLRRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRLRLRL i else ntree10LLRRLRLRR (i - 8)

def ntree10LLRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRRLRLL i else ntree10LLRRLRLR (i - 15)

def ntree10LLRRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨879,by decide⟩,⟨822,by decide⟩,⟨822,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨811,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨880,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 3 => ![⟨299,by decide⟩,⟨299,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨300,by decide⟩,⟨881,by decide⟩,⟨882,by decide⟩] | 5 => ![⟨300,by decide⟩,⟨811,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨302,by decide⟩,⟨883,by decide⟩,⟨14,by decide⟩] | _ => ![⟨304,by decide⟩,⟨281,by decide⟩,⟨14,by decide⟩]

def ntree10LLRRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨884,by decide⟩,⟨884,by decide⟩,⟨826,by decide⟩] | 1 => ![⟨885,by decide⟩,⟨886,by decide⟩,⟨830,by decide⟩] | 2 => ![⟨887,by decide⟩,⟨888,by decide⟩,⟨889,by decide⟩] | 3 => ![⟨890,by decide⟩,⟨891,by decide⟩,⟨274,by decide⟩] | 4 => ![⟨713,by decide⟩,⟨306,by decide⟩,⟨306,by decide⟩] | 5 => ![⟨675,by decide⟩,⟨892,by decide⟩,⟨306,by decide⟩] | 6 => ![⟨679,by decide⟩,⟨679,by decide⟩,⟨15,by decide⟩] | _ => ![⟨893,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩]

def ntree10LLRRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRLRRLL i else ntree10LLRRLRRLR (i - 8)

def ntree10LLRRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨679,by decide⟩,⟨894,by decide⟩,⟨308,by decide⟩] | 1 => ![⟨717,by decide⟩,⟨895,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨732,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 3 => ![⟨685,by decide⟩,⟨896,by decide⟩,⟨308,by decide⟩] | 4 => ![⟨312,by decide⟩,⟨897,by decide⟩,⟨897,by decide⟩] | 5 => ![⟨314,by decide⟩,⟨898,by decide⟩,⟨899,by decide⟩] | 6 => ![⟨900,by decide⟩,⟨901,by decide⟩,⟨901,by decide⟩] | _ => ![⟨902,by decide⟩,⟨903,by decide⟩,⟨903,by decide⟩]

def ntree10LLRRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨904,by decide⟩,⟨905,by decide⟩,⟨905,by decide⟩] | 1 => ![⟨327,by decide⟩,⟨906,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨317,by decide⟩,⟨907,by decide⟩,⟨907,by decide⟩] | 3 => ![⟨317,by decide⟩,⟨845,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨908,by decide⟩,⟨896,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨909,by decide⟩,⟨910,by decide⟩,⟨850,by decide⟩] | 6 => ![⟨737,by decide⟩,⟨737,by decide⟩,⟨329,by decide⟩] | _ => ![⟨738,by decide⟩,⟨911,by decide⟩,⟨330,by decide⟩]

def ntree10LLRRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRLRRRL i else ntree10LLRRLRRRR (i - 8)

def ntree10LLRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRRLRRL i else ntree10LLRRLRRR (i - 16)

def ntree10LLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRRLRL i else ntree10LLRRLRR (i - 31)

def ntree10LLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLRRLL i else ntree10LLRRLR (i - 63)

def ntree10LLRRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨912,by decide⟩,⟨913,by decide⟩,⟨331,by decide⟩] | 1 => ![⟨749,by decide⟩,⟨914,by decide⟩,⟨333,by decide⟩] | 2 => ![⟨748,by decide⟩,⟨915,by decide⟩,⟨331,by decide⟩] | 3 => ![⟨342,by decide⟩,⟨916,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨287,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨747,by decide⟩,⟨747,by decide⟩,⟨347,by decide⟩] | _ => ![⟨15,by decide⟩,⟨917,by decide⟩,⟨15,by decide⟩]

def ntree10LLRRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨811,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨918,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨750,by decide⟩,⟨919,by decide⟩,⟨920,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨921,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨922,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨201,by decide⟩,⟨923,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨924,by decide⟩,⟨925,by decide⟩,⟨925,by decide⟩]

def ntree10LLRRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRRRLLLL i else ntree10LLRRRLLLR (i - 7)

def ntree10LLRRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨926,by decide⟩,⟨926,by decide⟩,⟨926,by decide⟩] | 1 => ![⟨927,by decide⟩,⟨926,by decide⟩,⟨926,by decide⟩] | 2 => ![⟨928,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨699,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨929,by decide⟩,⟨201,by decide⟩,⟨930,by decide⟩] | 6 => ![⟨931,by decide⟩,⟨595,by decide⟩,⟨932,by decide⟩] | _ => ![⟨933,by decide⟩,⟨768,by decide⟩,⟨595,by decide⟩]

def ntree10LLRRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨159,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨934,by decide⟩,⟨935,by decide⟩,⟨274,by decide⟩] | 2 => ![⟨936,by decide⟩,⟨937,by decide⟩,⟨938,by decide⟩] | 3 => ![⟨939,by decide⟩,⟨940,by decide⟩,⟨941,by decide⟩] | 4 => ![⟨942,by decide⟩,⟨943,by decide⟩,⟨944,by decide⟩] | 5 => ![⟨51,by decide⟩,⟨945,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨946,by decide⟩,⟨15,by decide⟩] | _ => ![⟨15,by decide⟩,⟨845,by decide⟩,⟨15,by decide⟩]

def ntree10LLRRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRRLLRL i else ntree10LLRRRLLRR (i - 8)

def ntree10LLRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRRRLLL i else ntree10LLRRRLLR (i - 15)

def ntree10LLRRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨947,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨685,by decide⟩,⟨948,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨381,by decide⟩,⟨949,by decide⟩,⟨950,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨951,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨952,by decide⟩,⟨926,by decide⟩,⟨926,by decide⟩] | 6 => ![⟨953,by decide⟩,⟨954,by decide⟩,⟨954,by decide⟩] | _ => ![⟨955,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩]

def ntree10LLRRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨168,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨956,by decide⟩,⟨389,by decide⟩,⟨308,by decide⟩] | 2 => ![⟨251,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨957,by decide⟩,⟨685,by decide⟩,⟨958,by decide⟩] | 4 => ![⟨959,by decide⟩,⟨308,by decide⟩,⟨960,by decide⟩] | 5 => ![⟨961,by decide⟩,⟨962,by decide⟩,⟨963,by decide⟩] | 6 => ![⟨964,by decide⟩,⟨965,by decide⟩,⟨630,by decide⟩] | _ => ![⟨966,by decide⟩,⟨967,by decide⟩,⟨968,by decide⟩]

def ntree10LLRRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRRLRLL i else ntree10LLRRRLRLR (i - 8)

def ntree10LLRRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨969,by decide⟩,⟨970,by decide⟩,⟨971,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨972,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨973,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨974,by decide⟩,⟨975,by decide⟩,⟨347,by decide⟩] | 4 => ![⟨976,by decide⟩,⟨977,by decide⟩,⟨660,by decide⟩] | 5 => ![⟨978,by decide⟩,⟨979,by decide⟩,⟨979,by decide⟩] | 6 => ![⟨980,by decide⟩,⟨308,by decide⟩,⟨981,by decide⟩] | _ => ![⟨982,by decide⟩,⟨979,by decide⟩,⟨983,by decide⟩]

def ntree10LLRRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨984,by decide⟩,⟨595,by decide⟩,⟨985,by decide⟩] | 1 => ![⟨986,by decide⟩,⟨979,by decide⟩,⟨987,by decide⟩] | 2 => ![⟨988,by decide⟩,⟨989,by decide⟩,⟨990,by decide⟩] | 3 => ![⟨991,by decide⟩,⟨992,by decide⟩,⟨993,by decide⟩] | 4 => ![⟨994,by decide⟩,⟨995,by decide⟩,⟨996,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨997,by decide⟩,⟨997,by decide⟩] | 6 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨998,by decide⟩] | _ => ![⟨13,by decide⟩,⟨999,by decide⟩,⟨997,by decide⟩]

def ntree10LLRRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRRLRRL i else ntree10LLRRRLRRR (i - 8)

def ntree10LLRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRRRLRL i else ntree10LLRRRLRR (i - 16)

def ntree10LLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRRRLL i else ntree10LLRRRLR (i - 31)

def ntree10LLRRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨407,by decide⟩,⟨805,by decide⟩,⟨407,by decide⟩] | 1 => ![⟨406,by decide⟩,⟨1000,by decide⟩,⟨1001,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨805,by decide⟩,⟨1002,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨1000,by decide⟩,⟨1003,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1002,by decide⟩] | 5 => ![⟨598,by decide⟩,⟨805,by decide⟩,⟨1004,by decide⟩] | _ => ![⟨584,by decide⟩,⟨1005,by decide⟩,⟨1005,by decide⟩]

def ntree10LLRRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨586,by decide⟩,⟨586,by decide⟩,⟨1006,by decide⟩] | 1 => ![⟨587,by decide⟩,⟨999,by decide⟩,⟨1007,by decide⟩] | 2 => ![⟨585,by decide⟩,⟨585,by decide⟩,⟨585,by decide⟩] | 3 => ![⟨411,by decide⟩,⟨1008,by decide⟩,⟨1008,by decide⟩] | 4 => ![⟨413,by decide⟩,⟨413,by decide⟩,⟨1009,by decide⟩] | 5 => ![⟨413,by decide⟩,⟨1010,by decide⟩,⟨1008,by decide⟩] | 6 => ![⟨412,by decide⟩,⟨412,by decide⟩,⟨412,by decide⟩] | _ => ![⟨1011,by decide⟩,⟨1011,by decide⟩,⟨1012,by decide⟩]

def ntree10LLRRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRRRRLLL i else ntree10LLRRRRLLR (i - 7)

def ntree10LLRRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1013,by decide⟩,⟨1014,by decide⟩,⟨1014,by decide⟩] | 1 => ![⟨1015,by decide⟩,⟨1015,by decide⟩,⟨1016,by decide⟩] | 2 => ![⟨1017,by decide⟩,⟨1010,by decide⟩,⟨1018,by decide⟩] | 3 => ![⟨1019,by decide⟩,⟨1019,by decide⟩,⟨1019,by decide⟩] | 4 => ![⟨429,by decide⟩,⟨15,by decide⟩,⟨429,by decide⟩] | 5 => ![⟨428,by decide⟩,⟨1020,by decide⟩,⟨1021,by decide⟩] | 6 => ![⟨429,by decide⟩,⟨595,by decide⟩,⟨1022,by decide⟩] | _ => ![⟨429,by decide⟩,⟨1003,by decide⟩,⟨1021,by decide⟩]

def ntree10LLRRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1023,by decide⟩,⟨1024,by decide⟩,⟨1024,by decide⟩] | 1 => ![⟨1025,by decide⟩,⟨1003,by decide⟩,⟨1003,by decide⟩] | 2 => ![⟨50,by decide⟩,⟨1026,by decide⟩,⟨1027,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1028,by decide⟩,⟨1028,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨1029,by decide⟩,⟨1028,by decide⟩] | 5 => ![⟨51,by decide⟩,⟨1028,by decide⟩,⟨1030,by decide⟩] | 6 => ![⟨50,by decide⟩,⟨1029,by decide⟩,⟨1030,by decide⟩] | _ => ![⟨613,by decide⟩,⟨15,by decide⟩,⟨613,by decide⟩]

def ntree10LLRRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRRRLRL i else ntree10LLRRRRLRR (i - 8)

def ntree10LLRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRRRRLL i else ntree10LLRRRRLR (i - 15)

def ntree10LLRRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨614,by decide⟩,⟨13,by decide⟩,⟨1031,by decide⟩] | 1 => ![⟨613,by decide⟩,⟨1028,by decide⟩,⟨1032,by decide⟩] | 2 => ![⟨616,by decide⟩,⟨1033,by decide⟩,⟨616,by decide⟩] | 3 => ![⟨617,by decide⟩,⟨1034,by decide⟩,⟨1035,by decide⟩] | 4 => ![⟨444,by decide⟩,⟨1036,by decide⟩,⟨444,by decide⟩] | 5 => ![⟨445,by decide⟩,⟨1037,by decide⟩,⟨1038,by decide⟩] | 6 => ![⟨1039,by decide⟩,⟨826,by decide⟩,⟨1039,by decide⟩] | _ => ![⟨1040,by decide⟩,⟨1011,by decide⟩,⟨1041,by decide⟩]

def ntree10LLRRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1042,by decide⟩,⟨1043,by decide⟩,⟨1042,by decide⟩] | 1 => ![⟨1044,by decide⟩,⟨1045,by decide⟩,⟨1046,by decide⟩] | 2 => ![⟨201,by decide⟩,⟨1047,by decide⟩,⟨1028,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨1048,by decide⟩,⟨1048,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1028,by decide⟩,⟨1028,by decide⟩] | 5 => ![⟨51,by decide⟩,⟨805,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨50,by decide⟩,⟨1000,by decide⟩,⟨1049,by decide⟩] | _ => ![⟨613,by decide⟩,⟨805,by decide⟩,⟨613,by decide⟩]

def ntree10LLRRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRRRRLL i else ntree10LLRRRRRLR (i - 8)

def ntree10LLRRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨614,by decide⟩,⟨1000,by decide⟩,⟨1050,by decide⟩] | 1 => ![⟨1051,by decide⟩,⟨595,by decide⟩,⟨657,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨81,by decide⟩] | 3 => ![⟨1052,by decide⟩,⟨1053,by decide⟩,⟨658,by decide⟩] | 4 => ![⟨1054,by decide⟩,⟨1054,by decide⟩,⟨659,by decide⟩] | 5 => ![⟨435,by decide⟩,⟨1003,by decide⟩,⟨1003,by decide⟩] | 6 => ![⟨435,by decide⟩,⟨1055,by decide⟩,⟨660,by decide⟩] | _ => ![⟨51,by decide⟩,⟨1003,by decide⟩,⟨1049,by decide⟩]

def ntree10LLRRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨72,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨638,by decide⟩,⟨1003,by decide⟩,⟨1003,by decide⟩] | 2 => ![⟨674,by decide⟩,⟨674,by decide⟩,⟨1056,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1057,by decide⟩,⟨1057,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨811,by decide⟩,⟨1056,by decide⟩] | 5 => ![⟨1058,by decide⟩,⟨1059,by decide⟩,⟨1060,by decide⟩] | 6 => ![⟨407,by decide⟩,⟨1061,by decide⟩,⟨1060,by decide⟩] | _ => ![⟨674,by decide⟩,⟨1059,by decide⟩,⟨1061,by decide⟩]

def ntree10LLRRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRRRRRRL i else ntree10LLRRRRRRR (i - 8)

def ntree10LLRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLRRRRRL i else ntree10LLRRRRRR (i - 16)

def ntree10LLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLRRRRL i else ntree10LLRRRRR (i - 31)

def ntree10LLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLRRRL i else ntree10LLRRRR (i - 63)

def ntree10LLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LLRRL i else ntree10LLRRR (i - 126)

def ntree10LLR (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10LLRL i else ntree10LLRR (i - 252)

def ntree10LL (i : Nat) : Fin 3 → Fin 3959 := if i < 504 then ntree10LLL i else ntree10LLR (i - 504)

def ntree10LRLLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨805,by decide⟩,⟨1062,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1061,by decide⟩,⟨1061,by decide⟩] | 2 => ![⟨679,by decide⟩,⟨679,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨1063,by decide⟩,⟨679,by decide⟩,⟨588,by decide⟩] | 4 => ![⟨1064,by decide⟩,⟨871,by decide⟩,⟨407,by decide⟩] | 5 => ![⟨1064,by decide⟩,⟨679,by decide⟩,⟨407,by decide⟩] | _ => ![⟨679,by decide⟩,⟨871,by decide⟩,⟨15,by decide⟩]

def ntree10LRLLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨588,by decide⟩,⟨811,by decide⟩,⟨588,by decide⟩] | 1 => ![⟨697,by decide⟩,⟨1065,by decide⟩,⟨1065,by decide⟩] | 2 => ![⟨699,by decide⟩,⟨1061,by decide⟩,⟨1061,by decide⟩] | 3 => ![⟨585,by decide⟩,⟨1065,by decide⟩,⟨1065,by decide⟩] | 4 => ![⟨585,by decide⟩,⟨585,by decide⟩,⟨1066,by decide⟩] | 5 => ![⟨588,by decide⟩,⟨1061,by decide⟩,⟨1067,by decide⟩] | 6 => ![⟨412,by decide⟩,⟨1068,by decide⟩,⟨412,by decide⟩] | _ => ![⟨500,by decide⟩,⟨1069,by decide⟩,⟨1069,by decide⟩]

def ntree10LRLLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLLLLLLL i else ntree10LRLLLLLLR (i - 7)

def ntree10LRLLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨412,by decide⟩,⟨1069,by decide⟩,⟨1069,by decide⟩] | 1 => ![⟨287,by decide⟩,⟨1061,by decide⟩,⟨1061,by decide⟩] | 2 => ![⟨281,by decide⟩,⟨281,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨281,by decide⟩,⟨1070,by decide⟩,⟨1061,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1062,by decide⟩] | 5 => ![⟨1071,by decide⟩,⟨1068,by decide⟩,⟨1071,by decide⟩] | 6 => ![⟨1072,by decide⟩,⟨1073,by decide⟩,⟨1073,by decide⟩] | _ => ![⟨1074,by decide⟩,⟨1069,by decide⟩,⟨1069,by decide⟩]

def ntree10LRLLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1075,by decide⟩,⟨1065,by decide⟩,⟨1065,by decide⟩] | 1 => ![⟨1076,by decide⟩,⟨1076,by decide⟩,⟨1066,by decide⟩] | 2 => ![⟨1077,by decide⟩,⟨1070,by decide⟩,⟨1067,by decide⟩] | 3 => ![⟨1078,by decide⟩,⟨674,by decide⟩,⟨1079,by decide⟩] | 4 => ![⟨429,by decide⟩,⟨15,by decide⟩,⟨1079,by decide⟩] | 5 => ![⟨1078,by decide⟩,⟨674,by decide⟩,⟨429,by decide⟩] | 6 => ![⟨1080,by decide⟩,⟨281,by decide⟩,⟨429,by decide⟩] | _ => ![⟨826,by decide⟩,⟨1081,by decide⟩,⟨1081,by decide⟩]

def ntree10LRLLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLLLLRL i else ntree10LRLLLLLRR (i - 8)

def ntree10LRLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLLLLLL i else ntree10LRLLLLLR (i - 15)

def ntree10LRLLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨711,by decide⟩,⟨1082,by decide⟩,⟨1083,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨1084,by decide⟩,⟨1083,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨1085,by decide⟩,⟨1085,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨837,by decide⟩,⟨1056,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨1085,by decide⟩,⟨1086,by decide⟩] | 5 => ![⟨714,by decide⟩,⟨1087,by decide⟩,⟨1088,by decide⟩] | 6 => ![⟨679,by decide⟩,⟨1087,by decide⟩,⟨1084,by decide⟩] | _ => ![⟨613,by decide⟩,⟨308,by decide⟩,⟨1089,by decide⟩]

def ntree10LRLLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨718,by decide⟩,⟨1090,by decide⟩,⟨1090,by decide⟩] | 1 => ![⟨616,by decide⟩,⟨1090,by decide⟩,⟨1091,by decide⟩] | 2 => ![⟨518,by decide⟩,⟨1092,by decide⟩,⟨1092,by decide⟩] | 3 => ![⟨314,by decide⟩,⟨1093,by decide⟩,⟨1086,by decide⟩] | 4 => ![⟨1094,by decide⟩,⟨308,by decide⟩,⟨1089,by decide⟩] | 5 => ![⟨1095,by decide⟩,⟨1096,by decide⟩,⟨1096,by decide⟩] | 6 => ![⟨1097,by decide⟩,⟨1098,by decide⟩,⟨1091,by decide⟩] | _ => ![⟨317,by decide⟩,⟨1099,by decide⟩,⟨1056,by decide⟩]

def ntree10LRLLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLLLRLL i else ntree10LRLLLLRLR (i - 8)

def ntree10LRLLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1100,by decide⟩,⟨1101,by decide⟩,⟨1101,by decide⟩] | 1 => ![⟨1102,by decide⟩,⟨1084,by decide⟩,⟨1084,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨1103,by decide⟩,⟨1104,by decide⟩] | 3 => ![⟨407,by decide⟩,⟨1105,by decide⟩,⟨1106,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨1105,by decide⟩,⟨1086,by decide⟩] | 5 => ![⟨1107,by decide⟩,⟨1108,by decide⟩,⟨1109,by decide⟩] | 6 => ![⟨1110,by decide⟩,⟨913,by decide⟩,⟨529,by decide⟩] | _ => ![⟨1107,by decide⟩,⟨913,by decide⟩,⟨1089,by decide⟩]

def ntree10LRLLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1111,by decide⟩,⟨1112,by decide⟩,⟨613,by decide⟩] | 1 => ![⟨1113,by decide⟩,⟨1114,by decide⟩,⟨308,by decide⟩] | 2 => ![⟨1115,by decide⟩,⟨698,by decide⟩,⟨698,by decide⟩] | 3 => ![⟨1116,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 4 => ![⟨1117,by decide⟩,⟨1118,by decide⟩,⟨616,by decide⟩] | 5 => ![⟨1119,by decide⟩,⟨1114,by decide⟩,⟨311,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1120,by decide⟩] | _ => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩]

def ntree10LRLLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLLLRRL i else ntree10LRLLLLRRR (i - 8)

def ntree10LRLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLLLLRL i else ntree10LRLLLLRR (i - 16)

def ntree10LRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLLLLL i else ntree10LRLLLLR (i - 31)

def ntree10LRLLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1121,by decide⟩,⟨148,by decide⟩,⟨148,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨287,by decide⟩,⟨148,by decide⟩,⟨148,by decide⟩] | 3 => ![⟨674,by decide⟩,⟨1122,by decide⟩,⟨1123,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨1124,by decide⟩,⟨1125,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨999,by decide⟩,⟨1123,by decide⟩] | _ => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1056,by decide⟩]

def ntree10LRLLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1126,by decide⟩,⟨501,by decide⟩,⟨501,by decide⟩] | 1 => ![⟨1127,by decide⟩,⟨413,by decide⟩,⟨1128,by decide⟩] | 2 => ![⟨1129,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨1130,by decide⟩,⟨596,by decide⟩,⟨932,by decide⟩] | 4 => ![⟨1131,by decide⟩,⟨766,by decide⟩,⟨1132,by decide⟩] | 5 => ![⟨1133,by decide⟩,⟨1134,by decide⟩,⟨1135,by decide⟩] | 6 => ![⟨1133,by decide⟩,⟨828,by decide⟩,⟨1132,by decide⟩] | _ => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨1056,by decide⟩]

def ntree10LRLLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLLLRLLL i else ntree10LRLLLRLLR (i - 7)

def ntree10LRLLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1136,by decide⟩,⟨160,by decide⟩,⟨160,by decide⟩] | 1 => ![⟨699,by decide⟩,⟨160,by decide⟩,⟨160,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨50,by decide⟩,⟨1137,by decide⟩,⟨1083,by decide⟩] | 4 => ![⟨734,by decide⟩,⟨1084,by decide⟩,⟨1084,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨1137,by decide⟩,⟨1084,by decide⟩] | 6 => ![⟨772,by decide⟩,⟨567,by decide⟩,⟨772,by decide⟩] | _ => ![⟨773,by decide⟩,⟨555,by decide⟩,⟨1138,by decide⟩]

def ntree10LRLLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨734,by decide⟩,⟨567,by decide⟩,⟨1139,by decide⟩] | 1 => ![⟨451,by decide⟩,⟨15,by decide⟩,⟨451,by decide⟩] | 2 => ![⟨452,by decide⟩,⟨13,by decide⟩,⟨1140,by decide⟩] | 3 => ![⟨1141,by decide⟩,⟨565,by decide⟩,⟨1141,by decide⟩] | 4 => ![⟨1142,by decide⟩,⟨566,by decide⟩,⟨1143,by decide⟩] | 5 => ![⟨239,by decide⟩,⟨1144,by decide⟩,⟨1083,by decide⟩] | 6 => ![⟨251,by decide⟩,⟨1084,by decide⟩,⟨1084,by decide⟩] | _ => ![⟨50,by decide⟩,⟨1145,by decide⟩,⟨1146,by decide⟩]

def ntree10LRLLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLLRLRL i else ntree10LRLLLRLRR (i - 8)

def ntree10LRLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLLLRLL i else ntree10LRLLLRLR (i - 15)

def ntree10LRLLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1147,by decide⟩] | 2 => ![⟨1148,by decide⟩,⟨1149,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨1150,by decide⟩,⟨1151,by decide⟩,⟨979,by decide⟩] | 4 => ![⟨1152,by decide⟩,⟨572,by decide⟩,⟨802,by decide⟩] | 5 => ![⟨1153,by decide⟩,⟨555,by decide⟩,⟨981,by decide⟩] | 6 => ![⟨1154,by decide⟩,⟨1149,by decide⟩,⟨655,by decide⟩] | _ => ![⟨1155,by decide⟩,⟨1151,by decide⟩,⟨983,by decide⟩]

def ntree10LRLLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1156,by decide⟩,⟨1157,by decide⟩,⟨1157,by decide⟩] | 1 => ![⟨1158,by decide⟩,⟨1158,by decide⟩,⟨1157,by decide⟩] | 2 => ![⟨1159,by decide⟩,⟨1158,by decide⟩,⟨1160,by decide⟩] | 3 => ![⟨1161,by decide⟩,⟨1157,by decide⟩,⟨1161,by decide⟩] | 4 => ![⟨1162,by decide⟩,⟨1158,by decide⟩,⟨1161,by decide⟩] | 5 => ![⟨1163,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 6 => ![⟨1164,by decide⟩,⟨1165,by decide⟩,⟨8,by decide⟩] | _ => ![⟨18,by decide⟩,⟨595,by decide⟩,⟨1166,by decide⟩]

def ntree10LRLLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLLRRLL i else ntree10LRLLLRRLR (i - 8)

def ntree10LRLLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1167,by decide⟩,⟨15,by decide⟩,⟨1167,by decide⟩] | 1 => ![⟨1168,by decide⟩,⟨13,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨1170,by decide⟩,⟨1171,by decide⟩,⟨1166,by decide⟩] | 3 => ![⟨9,by decide⟩,⟨1172,by decide⟩,⟨1172,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨1172,by decide⟩,⟨1173,by decide⟩] | 5 => ![⟨1156,by decide⟩,⟨1174,by decide⟩,⟨1174,by decide⟩] | 6 => ![⟨1157,by decide⟩,⟨1157,by decide⟩,⟨1157,by decide⟩] | _ => ![⟨1161,by decide⟩,⟨1175,by decide⟩,⟨1161,by decide⟩]

def ntree10LRLLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1163,by decide⟩,⟨1172,by decide⟩,⟨1172,by decide⟩] | 1 => ![⟨1164,by decide⟩,⟨1176,by decide⟩,⟨1173,by decide⟩] | 2 => ![⟨1177,by decide⟩,⟨9,by decide⟩,⟨1177,by decide⟩] | 3 => ![⟨1178,by decide⟩,⟨11,by decide⟩,⟨1177,by decide⟩] | 4 => ![⟨1179,by decide⟩,⟨13,by decide⟩,⟨1180,by decide⟩] | 5 => ![⟨1181,by decide⟩,⟨1157,by decide⟩,⟨1181,by decide⟩] | 6 => ![⟨1182,by decide⟩,⟨1158,by decide⟩,⟨1181,by decide⟩] | _ => ![⟨1183,by decide⟩,⟨1157,by decide⟩,⟨1157,by decide⟩]

def ntree10LRLLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLLRRRL i else ntree10LRLLLRRRR (i - 8)

def ntree10LRLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLLLRRL i else ntree10LRLLLRRR (i - 16)

def ntree10LRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLLLRL i else ntree10LRLLLRR (i - 31)

def ntree10LRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRLLLL i else ntree10LRLLLR (i - 63)

def ntree10LRLLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1184,by decide⟩,⟨9,by decide⟩,⟨1184,by decide⟩] | 1 => ![⟨1185,by decide⟩,⟨11,by decide⟩,⟨1184,by decide⟩] | 2 => ![⟨1186,by decide⟩,⟨13,by decide⟩,⟨1187,by decide⟩] | 3 => ![⟨1188,by decide⟩,⟨1165,by decide⟩,⟨1184,by decide⟩] | 4 => ![⟨1189,by decide⟩,⟨582,by decide⟩,⟨1190,by decide⟩] | 5 => ![⟨1180,by decide⟩,⟨15,by decide⟩,⟨1180,by decide⟩] | _ => ![⟨15,by decide⟩,⟨1191,by decide⟩,⟨1192,by decide⟩]

def ntree10LRLLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1193,by decide⟩] | 1 => ![⟨1194,by decide⟩,⟨1195,by decide⟩,⟨1196,by decide⟩] | 2 => ![⟨1197,by decide⟩,⟨1198,by decide⟩,⟨1199,by decide⟩] | 3 => ![⟨1200,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 4 => ![⟨1201,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨1202,by decide⟩] | 6 => ![⟨1203,by decide⟩,⟨1204,by decide⟩,⟨1204,by decide⟩] | _ => ![⟨1205,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩]

def ntree10LRLLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLLRLLLL i else ntree10LRLLRLLLR (i - 7)

def ntree10LRLLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1206,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨1165,by decide⟩,⟨1165,by decide⟩,⟨1202,by decide⟩] | 2 => ![⟨1207,by decide⟩,⟨1208,by decide⟩,⟨637,by decide⟩] | 3 => ![⟨1209,by decide⟩,⟨1210,by decide⟩,⟨613,by decide⟩] | 4 => ![⟨1211,by decide⟩,⟨1210,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨1212,by decide⟩,⟨15,by decide⟩,⟨613,by decide⟩] | 6 => ![⟨1213,by decide⟩,⟨1214,by decide⟩,⟨645,by decide⟩] | _ => ![⟨1180,by decide⟩,⟨595,by decide⟩,⟨1215,by decide⟩]

def ntree10LRLLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1179,by decide⟩,⟨596,by decide⟩,⟨1215,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1216,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1216,by decide⟩] | 3 => ![⟨1194,by decide⟩,⟨15,by decide⟩,⟨81,by decide⟩] | 4 => ![⟨1197,by decide⟩,⟨1171,by decide⟩,⟨657,by decide⟩] | 5 => ![⟨614,by decide⟩,⟨26,by decide⟩,⟨1217,by decide⟩] | 6 => ![⟨1201,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | _ => ![⟨638,by decide⟩,⟨87,by decide⟩,⟨87,by decide⟩]

def ntree10LRLLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLRLLRL i else ntree10LRLLRLLRR (i - 8)

def ntree10LRLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLLRLLL i else ntree10LRLLRLLR (i - 15)

def ntree10LRLLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1218,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 1 => ![⟨638,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨1219,by decide⟩,⟨1171,by decide⟩,⟨603,by decide⟩] | 3 => ![⟨667,by decide⟩,⟨1220,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨1221,by decide⟩,⟨1221,by decide⟩,⟨1157,by decide⟩] | 5 => ![⟨1222,by decide⟩,⟨1157,by decide⟩,⟨1157,by decide⟩] | 6 => ![⟨1223,by decide⟩,⟨1221,by decide⟩,⟨1160,by decide⟩] | _ => ![⟨1224,by decide⟩,⟨1221,by decide⟩,⟨1161,by decide⟩]

def ntree10LRLLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1225,by decide⟩,⟨1226,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨1227,by decide⟩,⟨1228,by decide⟩,⟨583,by decide⟩] | 2 => ![⟨1229,by decide⟩,⟨1229,by decide⟩,⟨9,by decide⟩] | 3 => ![⟨1230,by decide⟩,⟨1229,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1231,by decide⟩,⟨1232,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨1233,by decide⟩,⟨1234,by decide⟩] | 6 => ![⟨18,by decide⟩,⟨1231,by decide⟩,⟨1235,by decide⟩] | _ => ![⟨1236,by decide⟩,⟨1231,by decide⟩,⟨1237,by decide⟩]

def ntree10LRLLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLRLRLL i else ntree10LRLLRLRLR (i - 8)

def ntree10LRLLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1238,by decide⟩,⟨1233,by decide⟩,⟨1239,by decide⟩] | 1 => ![⟨1240,by decide⟩,⟨97,by decide⟩,⟨1241,by decide⟩] | 2 => ![⟨1242,by decide⟩,⟨1242,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨1243,by decide⟩,⟨1244,by decide⟩,⟨18,by decide⟩] | 4 => ![⟨1221,by decide⟩,⟨1221,by decide⟩,⟨1245,by decide⟩] | 5 => ![⟨1224,by decide⟩,⟨1246,by decide⟩,⟨1247,by decide⟩] | 6 => ![⟨1229,by decide⟩,⟨1229,by decide⟩,⟨9,by decide⟩] | _ => ![⟨1230,by decide⟩,⟨1248,by decide⟩,⟨8,by decide⟩]

def ntree10LRLLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1249,by decide⟩,⟨95,by decide⟩,⟨1177,by decide⟩] | 1 => ![⟨1250,by decide⟩,⟨97,by decide⟩,⟨1180,by decide⟩] | 2 => ![⟨1251,by decide⟩,⟨1221,by decide⟩,⟨1181,by decide⟩] | 3 => ![⟨1252,by decide⟩,⟨1157,by decide⟩,⟨1157,by decide⟩] | 4 => ![⟨1253,by decide⟩,⟨97,by decide⟩,⟨613,by decide⟩] | 5 => ![⟨1254,by decide⟩,⟨1226,by decide⟩,⟨613,by decide⟩] | 6 => ![⟨1228,by decide⟩,⟨1228,by decide⟩,⟨615,by decide⟩] | _ => ![⟨1255,by decide⟩,⟨1229,by decide⟩,⟨1184,by decide⟩]

def ntree10LRLLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLRLRRL i else ntree10LRLLRLRRR (i - 8)

def ntree10LRLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLLRLRL i else ntree10LRLLRLRR (i - 16)

def ntree10LRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLLRLL i else ntree10LRLLRLR (i - 31)

def ntree10LRLLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1256,by decide⟩,⟨685,by decide⟩,⟨1187,by decide⟩] | 1 => ![⟨1257,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨1258,by decide⟩,⟨685,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨1190,by decide⟩,⟨615,by decide⟩,⟨1190,by decide⟩] | 4 => ![⟨1253,by decide⟩,⟨97,by decide⟩,⟨1259,by decide⟩] | 5 => ![⟨1260,by decide⟩,⟨1261,by decide⟩,⟨1262,by decide⟩] | _ => ![⟨1263,by decide⟩,⟨166,by decide⟩,⟨166,by decide⟩]

def ntree10LRLLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨9,by decide⟩,⟨1264,by decide⟩,⟨1264,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨1265,by decide⟩,⟨1266,by decide⟩] | 2 => ![⟨1252,by decide⟩,⟨1267,by decide⟩,⟨1267,by decide⟩] | 3 => ![⟨1257,by decide⟩,⟨1268,by decide⟩,⟨1268,by decide⟩] | 4 => ![⟨1258,by decide⟩,⟨1269,by decide⟩,⟨1270,by decide⟩] | 5 => ![⟨1271,by decide⟩,⟨747,by decide⟩,⟨613,by decide⟩] | 6 => ![⟨1272,by decide⟩,⟨1273,by decide⟩,⟨645,by decide⟩] | _ => ![⟨1260,by decide⟩,⟨1242,by decide⟩,⟨613,by decide⟩]

def ntree10LRLLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLLRRLLL i else ntree10LRLLRRLLR (i - 7)

def ntree10LRLLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1263,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨1274,by decide⟩,⟨1242,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨1180,by decide⟩,⟨1231,by decide⟩,⟨1275,by decide⟩] | 3 => ![⟨1250,by decide⟩,⟨1233,by decide⟩,⟨1276,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1277,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1278,by decide⟩] | 6 => ![⟨613,by decide⟩,⟨1231,by decide⟩,⟨1279,by decide⟩] | _ => ![⟨732,by decide⟩,⟨15,by decide⟩,⟨144,by decide⟩]

def ntree10LRLLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨613,by decide⟩,⟨109,by decide⟩,⟨1280,by decide⟩] | 1 => ![⟨1263,by decide⟩,⟨692,by decide⟩,⟨1281,by decide⟩] | 2 => ![⟨1242,by decide⟩,⟨1244,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨732,by decide⟩,⟨25,by decide⟩,⟨1282,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨613,by decide⟩,⟨25,by decide⟩,⟨613,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨1283,by decide⟩,⟨1284,by decide⟩] | _ => ![⟨96,by decide⟩,⟨1285,by decide⟩,⟨1286,by decide⟩]

def ntree10LRLLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLRRLRL i else ntree10LRLLRRLRR (i - 8)

def ntree10LRLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLLRRLL i else ntree10LRLLRRLR (i - 15)

def ntree10LRLLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨747,by decide⟩,⟨747,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨748,by decide⟩,⟨1287,by decide⟩,⟨149,by decide⟩] | 2 => ![⟨1242,by decide⟩,⟨1242,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨747,by decide⟩,⟨747,by decide⟩,⟨1288,by decide⟩] | 4 => ![⟨1274,by decide⟩,⟨1244,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨748,by decide⟩,⟨1289,by decide⟩,⟨1290,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨1291,by decide⟩,⟨14,by decide⟩] | _ => ![⟨1292,by decide⟩,⟨1292,by decide⟩,⟨1293,by decide⟩]

def ntree10LRLLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1294,by decide⟩,⟨1292,by decide⟩,⟨1295,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨1296,by decide⟩,⟨595,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨1297,by decide⟩,⟨1298,by decide⟩] | 3 => ![⟨151,by decide⟩,⟨1299,by decide⟩,⟨1300,by decide⟩] | 4 => ![⟨103,by decide⟩,⟨1296,by decide⟩,⟨1166,by decide⟩] | 5 => ![⟨19,by decide⟩,⟨1297,by decide⟩,⟨1301,by decide⟩] | 6 => ![⟨1240,by decide⟩,⟨97,by decide⟩,⟨1167,by decide⟩] | _ => ![⟨1168,by decide⟩,⟨13,by decide⟩,⟨1167,by decide⟩]

def ntree10LRLLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLRRRLL i else ntree10LRLLRRRLR (i - 8)

def ntree10LRLLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1302,by decide⟩,⟨151,by decide⟩,⟨1303,by decide⟩] | 1 => ![⟨1242,by decide⟩,⟨1304,by decide⟩,⟨595,by decide⟩] | 2 => ![⟨1243,by decide⟩,⟨1242,by decide⟩,⟨18,by decide⟩] | 3 => ![⟨95,by decide⟩,⟨1305,by decide⟩,⟨1172,by decide⟩] | 4 => ![⟨9,by decide⟩,⟨1306,by decide⟩,⟨9,by decide⟩] | 5 => ![⟨94,by decide⟩,⟨1305,by decide⟩,⟨1173,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨1306,by decide⟩,⟨8,by decide⟩] | _ => ![⟨96,by decide⟩,⟨1296,by decide⟩,⟨603,by decide⟩]

def ntree10LRLLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1221,by decide⟩,⟨1307,by decide⟩,⟨1174,by decide⟩] | 1 => ![⟨1157,by decide⟩,⟨1308,by decide⟩,⟨1157,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨1309,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨1229,by decide⟩,⟨1310,by decide⟩,⟨1172,by decide⟩] | 4 => ![⟨1311,by decide⟩,⟨1221,by decide⟩,⟨1312,by decide⟩] | 5 => ![⟨1313,by decide⟩,⟨1158,by decide⟩,⟨1312,by decide⟩] | 6 => ![⟨1314,by decide⟩,⟨1229,by decide⟩,⟨1315,by decide⟩] | _ => ![⟨1316,by decide⟩,⟨11,by decide⟩,⟨1315,by decide⟩]

def ntree10LRLLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLLRRRRL i else ntree10LRLLRRRRR (i - 8)

def ntree10LRLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLLRRRL i else ntree10LRLLRRRR (i - 16)

def ntree10LRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLLRRL i else ntree10LRLLRRR (i - 31)

def ntree10LRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRLLRL i else ntree10LRLLRR (i - 63)

def ntree10LRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LRLLL i else ntree10LRLLR (i - 126)

def ntree10LRLRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1317,by decide⟩,⟨752,by decide⟩,⟨1318,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1193,by decide⟩] | 2 => ![⟨1319,by decide⟩,⟨97,by decide⟩,⟨772,by decide⟩] | 3 => ![⟨1242,by decide⟩,⟨1261,by decide⟩,⟨166,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨167,by decide⟩,⟨166,by decide⟩] | 5 => ![⟨1320,by decide⟩,⟨1242,by decide⟩,⟨772,by decide⟩] | _ => ![⟨95,by decide⟩,⟨95,by decide⟩,⟨1202,by decide⟩]

def ntree10LRLRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨637,by decide⟩] | 2 => ![⟨1157,by decide⟩,⟨1204,by decide⟩,⟨1204,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨685,by decide⟩,⟨1321,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨1322,by decide⟩,⟨794,by decide⟩] | 6 => ![⟨796,by decide⟩,⟨796,by decide⟩,⟨794,by decide⟩] | _ => ![⟨1323,by decide⟩,⟨1322,by decide⟩,⟨797,by decide⟩]

def ntree10LRLRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLRLLLLL i else ntree10LRLRLLLLR (i - 7)

def ntree10LRLRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1324,by decide⟩,⟨1324,by decide⟩,⟨794,by decide⟩] | 1 => ![⟨1325,by decide⟩,⟨1324,by decide⟩,⟨797,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨1309,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨747,by decide⟩,⟨1326,by decide⟩,⟨87,by decide⟩] | 4 => ![⟨747,by decide⟩,⟨1327,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1328,by decide⟩,⟨1328,by decide⟩] | 6 => ![⟨180,by decide⟩,⟨180,by decide⟩,⟨1329,by decide⟩] | _ => ![⟨15,by decide⟩,⟨806,by decide⟩,⟨1329,by decide⟩]

def ntree10LRLRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨179,by decide⟩,⟨1330,by decide⟩,⟨1331,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨1332,by decide⟩,⟨1331,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨1328,by decide⟩,⟨1333,by decide⟩] | 3 => ![⟨1156,by decide⟩,⟨1334,by decide⟩,⟨1334,by decide⟩] | 4 => ![⟨1157,by decide⟩,⟨1157,by decide⟩,⟨1157,by decide⟩] | 5 => ![⟨1161,by decide⟩,⟨1335,by decide⟩,⟨1161,by decide⟩] | 6 => ![⟨579,by decide⟩,⟨1336,by decide⟩,⟨1333,by decide⟩] | _ => ![⟨598,by decide⟩,⟨1337,by decide⟩,⟨1329,by decide⟩]

def ntree10LRLRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRLLLRL i else ntree10LRLRLLLRR (i - 8)

def ntree10LRLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLRLLLL i else ntree10LRLRLLLR (i - 15)

def ntree10LRLRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨193,by decide⟩,⟨193,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨191,by decide⟩,⟨15,by decide⟩,⟨191,by decide⟩] | 2 => ![⟨192,by decide⟩,⟨1338,by decide⟩,⟨1339,by decide⟩] | 3 => ![⟨193,by decide⟩,⟨1338,by decide⟩,⟨1332,by decide⟩] | 4 => ![⟨191,by decide⟩,⟨595,by decide⟩,⟨1340,by decide⟩] | 5 => ![⟨1341,by decide⟩,⟨826,by decide⟩,⟨1341,by decide⟩] | 6 => ![⟨1342,by decide⟩,⟨595,by decide⟩,⟨1340,by decide⟩] | _ => ![⟨1343,by decide⟩,⟨1344,by decide⟩,⟨1344,by decide⟩]

def ntree10LRLRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1345,by decide⟩,⟨1332,by decide⟩,⟨1332,by decide⟩] | 1 => ![⟨207,by decide⟩,⟨1346,by decide⟩,⟨1346,by decide⟩] | 2 => ![⟨208,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩] | 3 => ![⟨212,by decide⟩,⟨1347,by decide⟩,⟨212,by decide⟩] | 4 => ![⟨212,by decide⟩,⟨1346,by decide⟩,⟨1348,by decide⟩] | 5 => ![⟨1349,by decide⟩,⟨1350,by decide⟩,⟨1350,by decide⟩] | 6 => ![⟨1351,by decide⟩,⟨1351,by decide⟩,⟨1351,by decide⟩] | _ => ![⟨1352,by decide⟩,⟨1353,by decide⟩,⟨1352,by decide⟩]

def ntree10LRLRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRLLRLL i else ntree10LRLRLLRLR (i - 8)

def ntree10LRLRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1354,by decide⟩,⟨1355,by decide⟩,⟨1348,by decide⟩] | 1 => ![⟨1180,by decide⟩,⟨836,by decide⟩,⟨1180,by decide⟩] | 2 => ![⟨1356,by decide⟩,⟨1357,by decide⟩,⟨1358,by decide⟩] | 3 => ![⟨1180,by decide⟩,⟨1359,by decide⟩,⟨1358,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1360,by decide⟩,⟨1360,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨845,by decide⟩,⟨1329,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨836,by decide⟩,⟨1361,by decide⟩] | _ => ![⟨180,by decide⟩,⟨1357,by decide⟩,⟨1359,by decide⟩]

def ntree10LRLRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1359,by decide⟩,⟨1359,by decide⟩] | 1 => ![⟨1203,by decide⟩,⟨1362,by decide⟩,⟨1362,by decide⟩] | 2 => ![⟨1157,by decide⟩,⟨1362,by decide⟩,⟨1362,by decide⟩] | 3 => ![⟨1157,by decide⟩,⟨1363,by decide⟩,⟨1157,by decide⟩] | 4 => ![⟨580,by decide⟩,⟨580,by decide⟩,⟨1361,by decide⟩] | 5 => ![⟨638,by decide⟩,⟨1359,by decide⟩,⟨1359,by decide⟩] | 6 => ![⟨580,by decide⟩,⟨1364,by decide⟩,⟨1359,by decide⟩] | _ => ![⟨1187,by decide⟩,⟨15,by decide⟩,⟨1187,by decide⟩]

def ntree10LRLRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRLLRRL i else ntree10LRLRLLRRR (i - 8)

def ntree10LRLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLRLLRL i else ntree10LRLRLLRR (i - 16)

def ntree10LRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLRLLL i else ntree10LRLRLLR (i - 31)

def ntree10LRLRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1365,by decide⟩,⟨180,by decide⟩,⟨1366,by decide⟩] | 1 => ![⟨1187,by decide⟩,⟨15,by decide⟩,⟨1366,by decide⟩] | 2 => ![⟨1367,by decide⟩,⟨580,by decide⟩,⟨1187,by decide⟩] | 3 => ![⟨1365,by decide⟩,⟨180,by decide⟩,⟨1187,by decide⟩] | 4 => ![⟨1368,by decide⟩,⟨847,by decide⟩,⟨1180,by decide⟩] | 5 => ![⟨1368,by decide⟩,⟨193,by decide⟩,⟨1180,by decide⟩] | _ => ![⟨1369,by decide⟩,⟨193,by decide⟩,⟨248,by decide⟩]

def ntree10LRLRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨193,by decide⟩,⟨847,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1361,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨1370,by decide⟩,⟨1370,by decide⟩] | 3 => ![⟨249,by decide⟩,⟨1371,by decide⟩,⟨1371,by decide⟩] | 4 => ![⟨251,by decide⟩,⟨1359,by decide⟩,⟨1359,by decide⟩] | 5 => ![⟨248,by decide⟩,⟨845,by decide⟩,⟨248,by decide⟩] | 6 => ![⟨208,by decide⟩,⟨208,by decide⟩,⟨1372,by decide⟩] | _ => ![⟨208,by decide⟩,⟨1371,by decide⟩,⟨1371,by decide⟩]

def ntree10LRLRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLRLRLLL i else ntree10LRLRLRLLR (i - 7)

def ntree10LRLRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨248,by decide⟩,⟨1359,by decide⟩,⟨1373,by decide⟩] | 1 => ![⟨1374,by decide⟩,⟨1375,by decide⟩,⟨1375,by decide⟩] | 2 => ![⟨1376,by decide⟩,⟨1362,by decide⟩,⟨1362,by decide⟩] | 3 => ![⟨1377,by decide⟩,⟨1363,by decide⟩,⟨1377,by decide⟩] | 4 => ![⟨1378,by decide⟩,⟨1378,by decide⟩,⟨1372,by decide⟩] | 5 => ![⟨1379,by decide⟩,⟨1371,by decide⟩,⟨1371,by decide⟩] | 6 => ![⟨1380,by decide⟩,⟨1364,by decide⟩,⟨1373,by decide⟩] | _ => ![⟨1180,by decide⟩,⟨1381,by decide⟩,⟨1382,by decide⟩]

def ntree10LRLRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨14,by decide⟩,⟨1383,by decide⟩,⟨1384,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨1381,by decide⟩,⟨1333,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨836,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1385,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨1386,by decide⟩,⟨867,by decide⟩,⟨1215,by decide⟩] | 6 => ![⟨1387,by decide⟩,⟨1388,by decide⟩,⟨1389,by decide⟩] | _ => ![⟨1387,by decide⟩,⟨867,by decide⟩,⟨1340,by decide⟩]

def ntree10LRLRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRLRLRL i else ntree10LRLRLRLRR (i - 8)

def ntree10LRLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLRLRLL i else ntree10LRLRLRLR (i - 15)

def ntree10LRLRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨191,by decide⟩,⟨836,by decide⟩,⟨191,by decide⟩] | 1 => ![⟨1390,by decide⟩,⟨1391,by decide⟩,⟨191,by decide⟩] | 2 => ![⟨1392,by decide⟩,⟨1393,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨1394,by decide⟩,⟨84,by decide⟩,⟨84,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨638,by decide⟩,⟨84,by decide⟩,⟨84,by decide⟩] | 6 => ![⟨1395,by decide⟩,⟨250,by decide⟩,⟨250,by decide⟩] | _ => ![⟨1396,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩]

def ntree10LRLRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1397,by decide⟩,⟨1398,by decide⟩,⟨212,by decide⟩] | 1 => ![⟨1399,by decide⟩,⟨1393,by decide⟩,⟨603,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1400,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1401,by decide⟩,⟨1401,by decide⟩] | 4 => ![⟨97,by decide⟩,⟨1402,by decide⟩,⟨1401,by decide⟩] | 5 => ![⟨96,by decide⟩,⟨1403,by decide⟩,⟨1404,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨1401,by decide⟩,⟨1405,by decide⟩] | _ => ![⟨96,by decide⟩,⟨1402,by decide⟩,⟨1405,by decide⟩]

def ntree10LRLRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRLRRLL i else ntree10LRLRLRRLR (i - 8)

def ntree10LRLRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1221,by decide⟩,⟨1221,by decide⟩,⟨1406,by decide⟩] | 1 => ![⟨1224,by decide⟩,⟨1407,by decide⟩,⟨1408,by decide⟩] | 2 => ![⟨685,by decide⟩,⟨1409,by decide⟩,⟨1401,by decide⟩] | 3 => ![⟨279,by decide⟩,⟨97,by decide⟩,⟨1410,by decide⟩] | 4 => ![⟨191,by decide⟩,⟨1401,by decide⟩,⟨1411,by decide⟩] | 5 => ![⟨1412,by decide⟩,⟨1412,by decide⟩,⟨1413,by decide⟩] | 6 => ![⟨1414,by decide⟩,⟨1412,by decide⟩,⟨1415,by decide⟩] | _ => ![⟨826,by decide⟩,⟨1416,by decide⟩,⟨1416,by decide⟩]

def ntree10LRLRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1401,by decide⟩,⟨1401,by decide⟩] | 1 => ![⟨289,by decide⟩,⟨289,by decide⟩,⟨1417,by decide⟩] | 2 => ![⟨292,by decide⟩,⟨1418,by decide⟩,⟨1419,by decide⟩] | 3 => ![⟨1420,by decide⟩,⟨1420,by decide⟩,⟨1421,by decide⟩] | 4 => ![⟨1422,by decide⟩,⟨1423,by decide⟩,⟨1424,by decide⟩] | 5 => ![⟨1250,by decide⟩,⟨1425,by decide⟩,⟨1426,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨1427,by decide⟩,⟨1427,by decide⟩] | _ => ![⟨97,by decide⟩,⟨1428,by decide⟩,⟨1427,by decide⟩]

def ntree10LRLRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRLRRRL i else ntree10LRLRLRRRR (i - 8)

def ntree10LRLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLRLRRL i else ntree10LRLRLRRR (i - 16)

def ntree10LRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLRLRL i else ntree10LRLRLRR (i - 31)

def ntree10LRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRLRLL i else ntree10LRLRLR (i - 63)

def ntree10LRLRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨1425,by decide⟩,⟨1429,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨836,by decide⟩,⟨1430,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1430,by decide⟩] | 3 => ![⟨1252,by decide⟩,⟨1431,by decide⟩,⟨1431,by decide⟩] | 4 => ![⟨1221,by decide⟩,⟨1432,by decide⟩,⟨1431,by decide⟩] | 5 => ![⟨1256,by decide⟩,⟨1433,by decide⟩,⟨1434,by decide⟩] | _ => ![⟨1187,by decide⟩,⟨1429,by decide⟩,⟨1434,by decide⟩]

def ntree10LRLRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1187,by decide⟩,⟨308,by decide⟩,⟨1435,by decide⟩] | 1 => ![⟨317,by decide⟩,⟨836,by decide⟩,⟨1436,by decide⟩] | 2 => ![⟨1437,by decide⟩,⟨1438,by decide⟩,⟨1438,by decide⟩] | 3 => ![⟨1439,by decide⟩,⟨1429,by decide⟩,⟨1429,by decide⟩] | 4 => ![⟨324,by decide⟩,⟨1440,by decide⟩,⟨1440,by decide⟩] | 5 => ![⟨318,by decide⟩,⟨1428,by decide⟩,⟨1441,by decide⟩] | 6 => ![⟨1442,by decide⟩,⟨1443,by decide⟩,⟨1443,by decide⟩] | _ => ![⟨1444,by decide⟩,⟨1432,by decide⟩,⟨1445,by decide⟩]

def ntree10LRLRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLRRLLLL i else ntree10LRLRRLLLR (i - 7)

def ntree10LRLRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨96,by decide⟩,⟨1425,by decide⟩,⟨1446,by decide⟩] | 1 => ![⟨1263,by decide⟩,⟨1429,by decide⟩,⟨1429,by decide⟩] | 2 => ![⟨1263,by decide⟩,⟨1447,by decide⟩,⟨347,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨1429,by decide⟩,⟨1446,by decide⟩] | 4 => ![⟨279,by decide⟩,⟨1425,by decide⟩,⟨1448,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨144,by decide⟩] | 6 => ![⟨1449,by decide⟩,⟨308,by decide⟩,⟨340,by decide⟩] | _ => ![⟨15,by decide⟩,⟨109,by decide⟩,⟨109,by decide⟩]

def ntree10LRLRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨287,by decide⟩,⟨1429,by decide⟩,⟨1429,by decide⟩] | 1 => ![⟨1450,by decide⟩,⟨1450,by decide⟩,⟨346,by decide⟩] | 2 => ![⟨1451,by decide⟩,⟨1452,by decide⟩,⟨348,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1329,by decide⟩] | 4 => ![⟨96,by decide⟩,⟨1453,by decide⟩,⟨1331,by decide⟩] | 5 => ![⟨685,by decide⟩,⟨685,by decide⟩,⟨1329,by decide⟩] | 6 => ![⟨687,by decide⟩,⟨1454,by decide⟩,⟨1331,by decide⟩] | _ => ![⟨359,by decide⟩,⟨1296,by decide⟩,⟨1455,by decide⟩]

def ntree10LRLRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRRLLRL i else ntree10LRLRRLLRR (i - 8)

def ntree10LRLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLRRLLL i else ntree10LRLRRLLR (i - 15)

def ntree10LRLRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨360,by decide⟩,⟨1309,by decide⟩,⟨360,by decide⟩] | 1 => ![⟨206,by decide⟩,⟨1332,by decide⟩,⟨1332,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨1453,by decide⟩,⟨1332,by decide⟩] | 3 => ![⟨206,by decide⟩,⟨1309,by decide⟩,⟨1456,by decide⟩] | 4 => ![⟨1240,by decide⟩,⟨97,by decide⟩,⟨1457,by decide⟩] | 5 => ![⟨1167,by decide⟩,⟨15,by decide⟩,⟨1167,by decide⟩] | 6 => ![⟨699,by decide⟩,⟨1332,by decide⟩,⟨1332,by decide⟩] | _ => ![⟨1458,by decide⟩,⟨1307,by decide⟩,⟨1459,by decide⟩]

def ntree10LRLRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1460,by decide⟩,⟨1308,by decide⟩,⟨1460,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨1461,by decide⟩,⟨1462,by decide⟩] | 2 => ![⟨180,by decide⟩,⟨1463,by decide⟩,⟨1464,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨1428,by decide⟩,⟨1464,by decide⟩] | 4 => ![⟨1465,by decide⟩,⟨1466,by decide⟩,⟨1467,by decide⟩] | 5 => ![⟨1468,by decide⟩,⟨378,by decide⟩,⟨1469,by decide⟩] | 6 => ![⟨1465,by decide⟩,⟨896,by decide⟩,⟨1469,by decide⟩] | _ => ![⟨1470,by decide⟩,⟨166,by decide⟩,⟨166,by decide⟩]

def ntree10LRLRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRRLRLL i else ntree10LRLRRLRLR (i - 8)

def ntree10LRLRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨251,by decide⟩,⟨166,by decide⟩,⟨166,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨1471,by decide⟩,⟨1204,by decide⟩,⟨1204,by decide⟩] | 3 => ![⟨1472,by decide⟩,⟨1221,by decide⟩,⟨1473,by decide⟩] | 4 => ![⟨1474,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨1475,by decide⟩,⟨309,by decide⟩,⟨960,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1476,by decide⟩] | _ => ![⟨96,by decide⟩,⟨1477,by decide⟩,⟨1478,by decide⟩]

def ntree10LRLRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1479,by decide⟩,⟨1480,by decide⟩,⟨308,by decide⟩] | 1 => ![⟨1481,by decide⟩,⟨1482,by decide⟩,⟨979,by decide⟩] | 2 => ![⟨1483,by decide⟩,⟨1326,by decide⟩,⟨403,by decide⟩] | 3 => ![⟨1484,by decide⟩,⟨1296,by decide⟩,⟨985,by decide⟩] | 4 => ![⟨1485,by decide⟩,⟨1480,by decide⟩,⟨331,by decide⟩] | 5 => ![⟨1486,by decide⟩,⟨1482,by decide⟩,⟨987,by decide⟩] | 6 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | _ => ![⟨11,by decide⟩,⟨11,by decide⟩,⟨1487,by decide⟩]

def ntree10LRLRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRRLRRL i else ntree10LRLRRLRRR (i - 8)

def ntree10LRLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLRRLRL i else ntree10LRLRRLRR (i - 16)

def ntree10LRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLRRLL i else ntree10LRLRRLR (i - 31)

def ntree10LRLRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1329,by decide⟩] | 1 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨1488,by decide⟩] | 2 => ![⟨1168,by decide⟩,⟨13,by decide⟩,⟨1489,by decide⟩] | 3 => ![⟨598,by decide⟩,⟨15,by decide⟩,⟨1361,by decide⟩] | 4 => ![⟨1163,by decide⟩,⟨1490,by decide⟩,⟨1490,by decide⟩] | 5 => ![⟨587,by decide⟩,⟨1491,by decide⟩,⟨1492,by decide⟩] | _ => ![⟨418,by decide⟩,⟨13,by decide⟩,⟨1493,by decide⟩]

def ntree10LRLRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1494,by decide⟩,⟨1011,by decide⟩,⟨1495,by decide⟩] | 1 => ![⟨423,by decide⟩,⟨1172,by decide⟩,⟨1172,by decide⟩] | 2 => ![⟨1496,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨426,by decide⟩,⟨9,by decide⟩,⟨426,by decide⟩] | 4 => ![⟨429,by decide⟩,⟨15,by decide⟩,⟨429,by decide⟩] | 5 => ![⟨426,by decide⟩,⟨1172,by decide⟩,⟨1497,by decide⟩] | 6 => ![⟨1498,by decide⟩,⟨1499,by decide⟩,⟨1499,by decide⟩] | _ => ![⟨1500,by decide⟩,⟨1500,by decide⟩,⟨1500,by decide⟩]

def ntree10LRLRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRLRRRLLL i else ntree10LRLRRRLLR (i - 7)

def ntree10LRLRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1501,by decide⟩,⟨1502,by decide⟩,⟨1502,by decide⟩] | 1 => ![⟨1503,by decide⟩,⟨1503,by decide⟩,⟨1503,by decide⟩] | 2 => ![⟨1194,by decide⟩,⟨439,by decide⟩,⟨1504,by decide⟩] | 3 => ![⟨613,by decide⟩,⟨439,by decide⟩,⟨1505,by decide⟩] | 4 => ![⟨1184,by decide⟩,⟨9,by decide⟩,⟨1184,by decide⟩] | 5 => ![⟨1185,by decide⟩,⟨11,by decide⟩,⟨1506,by decide⟩] | 6 => ![⟨1186,by decide⟩,⟨13,by decide⟩,⟨1366,by decide⟩] | _ => ![⟨454,by decide⟩,⟨1507,by decide⟩,⟨1508,by decide⟩]

def ntree10LRLRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨456,by decide⟩,⟨13,by decide⟩,⟨248,by decide⟩] | 1 => ![⟨454,by decide⟩,⟨15,by decide⟩,⟨1361,by decide⟩] | 2 => ![⟨1509,by decide⟩,⟨1510,by decide⟩,⟨1511,by decide⟩] | 3 => ![⟨1512,by decide⟩,⟨439,by decide⟩,⟨1513,by decide⟩] | 4 => ![⟨1514,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 5 => ![⟨251,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨248,by decide⟩,⟨1515,by decide⟩,⟨248,by decide⟩] | _ => ![⟨248,by decide⟩,⟨15,by decide⟩,⟨1516,by decide⟩]

def ntree10LRLRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRRRLRL i else ntree10LRLRRRLRR (i - 8)

def ntree10LRLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRLRRRLL i else ntree10LRLRRRLR (i - 15)

def ntree10LRLRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1517,by decide⟩,⟨1500,by decide⟩,⟨1500,by decide⟩] | 1 => ![⟨1518,by decide⟩,⟨1503,by decide⟩,⟨1503,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1361,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1519,by decide⟩] | 4 => ![⟨1212,by decide⟩,⟨1520,by decide⟩,⟨1521,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1522,by decide⟩] | 6 => ![⟨1523,by decide⟩,⟨439,by decide⟩,⟨1524,by decide⟩] | _ => ![⟨1525,by decide⟩,⟨1526,by decide⟩,⟨1527,by decide⟩]

def ntree10LRLRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1528,by decide⟩,⟨1529,by decide⟩,⟨1530,by decide⟩] | 1 => ![⟨1531,by decide⟩,⟨1532,by decide⟩,⟨1533,by decide⟩] | 2 => ![⟨1534,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨191,by decide⟩,⟨15,by decide⟩,⟨1535,by decide⟩] | 4 => ![⟨1536,by decide⟩,⟨1537,by decide⟩,⟨1537,by decide⟩] | 5 => ![⟨1538,by decide⟩,⟨1539,by decide⟩,⟨1539,by decide⟩] | 6 => ![⟨1540,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | _ => ![⟨1539,by decide⟩,⟨1539,by decide⟩,⟨1539,by decide⟩]

def ntree10LRLRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRRRRLL i else ntree10LRLRRRRLR (i - 8)

def ntree10LRLRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨95,by decide⟩,⟨95,by decide⟩,⟨1541,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1056,by decide⟩] | 3 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨1542,by decide⟩] | 4 => ![⟨1236,by decide⟩,⟨1543,by decide⟩,⟨1544,by decide⟩] | 5 => ![⟨1238,by decide⟩,⟨97,by decide⟩,⟨588,by decide⟩] | 6 => ![⟨1236,by decide⟩,⟨15,by decide⟩,⟨1062,by decide⟩] | _ => ![⟨588,by decide⟩,⟨1545,by decide⟩,⟨588,by decide⟩]

def ntree10LRLRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1546,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨699,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨588,by decide⟩,⟨15,by decide⟩,⟨1547,by decide⟩] | 3 => ![⟨497,by decide⟩,⟨1231,by decide⟩,⟨1548,by decide⟩] | 4 => ![⟨191,by decide⟩,⟨1231,by decide⟩,⟨1549,by decide⟩] | 5 => ![⟨1550,by decide⟩,⟨1551,by decide⟩,⟨1552,by decide⟩] | 6 => ![⟨1553,by decide⟩,⟨1231,by decide⟩,⟨1554,by decide⟩] | _ => ![⟨502,by decide⟩,⟨95,by decide⟩,⟨1555,by decide⟩]

def ntree10LRLRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRLRRRRRL i else ntree10LRLRRRRRR (i - 8)

def ntree10LRLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRLRRRRL i else ntree10LRLRRRRR (i - 16)

def ntree10LRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRLRRRL i else ntree10LRLRRRR (i - 31)

def ntree10LRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRLRRL i else ntree10LRLRRR (i - 63)

def ntree10LRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LRLRL i else ntree10LRLRR (i - 126)

def ntree10LRL (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10LRLL i else ntree10LRLR (i - 252)

def ntree10LRRLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨503,by decide⟩,⟨97,by decide⟩,⟨1079,by decide⟩] | 1 => ![⟨1556,by decide⟩,⟨1500,by decide⟩,⟨1500,by decide⟩] | 2 => ![⟨1557,by decide⟩,⟨1503,by decide⟩,⟨1503,by decide⟩] | 3 => ![⟨1253,by decide⟩,⟨97,by decide⟩,⟨1558,by decide⟩] | 4 => ![⟨1187,by decide⟩,⟨15,by decide⟩,⟨1187,by decide⟩] | 5 => ![⟨1257,by decide⟩,⟨515,by decide⟩,⟨515,by decide⟩] | _ => ![⟨1559,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩]

def ntree10LRRLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1184,by decide⟩,⟨515,by decide⟩,⟨1560,by decide⟩] | 1 => ![⟨520,by decide⟩,⟨97,by decide⟩,⟨1561,by decide⟩] | 2 => ![⟨317,by decide⟩,⟨15,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨1562,by decide⟩,⟨1412,by decide⟩,⟨1563,by decide⟩] | 4 => ![⟨523,by decide⟩,⟨1564,by decide⟩,⟨1564,by decide⟩] | 5 => ![⟨318,by decide⟩,⟨1565,by decide⟩,⟨1566,by decide⟩] | 6 => ![⟨1567,by decide⟩,⟨1568,by decide⟩,⟨1568,by decide⟩] | _ => ![⟨1569,by decide⟩,⟨1570,by decide⟩,⟨1570,by decide⟩]

def ntree10LRRLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRLLLLLL i else ntree10LRRLLLLLR (i - 7)

def ntree10LRRLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1571,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1062,by decide⟩] | 2 => ![⟨1572,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨613,by decide⟩,⟨15,by decide⟩,⟨1573,by decide⟩] | 4 => ![⟨1574,by decide⟩,⟨1231,by decide⟩,⟨1575,by decide⟩] | 5 => ![⟨1576,by decide⟩,⟨1577,by decide⟩,⟨1578,by decide⟩] | 6 => ![⟨1579,by decide⟩,⟨1580,by decide⟩,⟨1581,by decide⟩] | _ => ![⟨1582,by decide⟩,⟨1583,by decide⟩,⟨1584,by decide⟩]

def ntree10LRRLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨533,by decide⟩,⟨1585,by decide⟩,⟨1586,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨1587,by decide⟩] | 2 => ![⟨1588,by decide⟩,⟨1539,by decide⟩,⟨1539,by decide⟩] | 3 => ![⟨1589,by decide⟩,⟨1590,by decide⟩,⟨1590,by decide⟩] | 4 => ![⟨1591,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨151,by decide⟩,⟨151,by decide⟩,⟨1592,by decide⟩] | 6 => ![⟨763,by decide⟩,⟨13,by decide⟩,⟨1593,by decide⟩] | _ => ![⟨545,by decide⟩,⟨1297,by decide⟩,⟨1594,by decide⟩]

def ntree10LRRLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLLLLRL i else ntree10LRRLLLLRR (i - 8)

def ntree10LRRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRLLLLL i else ntree10LRRLLLLR (i - 15)

def ntree10LRRLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨546,by decide⟩,⟨1305,by decide⟩,⟨1595,by decide⟩] | 1 => ![⟨547,by decide⟩,⟨1306,by decide⟩,⟨547,by decide⟩] | 2 => ![⟨1596,by decide⟩,⟨1296,by decide⟩,⟨1132,by decide⟩] | 3 => ![⟨1319,by decide⟩,⟨553,by decide⟩,⟨1597,by decide⟩] | 4 => ![⟨1315,by decide⟩,⟨559,by decide⟩,⟨1315,by decide⟩] | 5 => ![⟨1316,by decide⟩,⟨560,by decide⟩,⟨1598,by decide⟩] | 6 => ![⟨1599,by decide⟩,⟨555,by decide⟩,⟨1469,by decide⟩] | _ => ![⟨384,by decide⟩,⟨97,by decide⟩,⟨1600,by decide⟩]

def ntree10LRRLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1601,by decide⟩,⟨567,by decide⟩,⟨1602,by decide⟩] | 1 => ![⟨1603,by decide⟩,⟨1604,by decide⟩,⟨1605,by decide⟩] | 2 => ![⟨1606,by decide⟩,⟨1607,by decide⟩,⟨1608,by decide⟩] | 3 => ![⟨1609,by decide⟩,⟨1610,by decide⟩,⟨1611,by decide⟩] | 4 => ![⟨1612,by decide⟩,⟨1309,by decide⟩,⟨1613,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1614,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1,by decide⟩,⟨1615,by decide⟩,⟨1616,by decide⟩] | _ => ![⟨2,by decide⟩,⟨1617,by decide⟩,⟨1618,by decide⟩]

def ntree10LRRLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLLLRLL i else ntree10LRRLLLRLR (i - 8)

def ntree10LRRLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨9,by decide⟩,⟨1619,by decide⟩,⟨1620,by decide⟩] | 1 => ![⟨11,by decide⟩,⟨1621,by decide⟩,⟨1622,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨1623,by decide⟩,⟨1624,by decide⟩] | 3 => ![⟨3,by decide⟩,⟨1625,by decide⟩,⟨3,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨1627,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨1623,by decide⟩,⟨1628,by decide⟩] | 6 => ![⟨9,by decide⟩,⟨1619,by decide⟩,⟨9,by decide⟩] | _ => ![⟨3,by decide⟩,⟨1629,by decide⟩,⟨3,by decide⟩]

def ntree10LRRLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2,by decide⟩,⟨1630,by decide⟩,⟨1631,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1632,by decide⟩,⟨1627,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨1633,by decide⟩,⟨1634,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1627,by decide⟩] | 4 => ![⟨1635,by decide⟩,⟨1635,by decide⟩,⟨1635,by decide⟩] | 5 => ![⟨1636,by decide⟩,⟨1636,by decide⟩,⟨1635,by decide⟩] | 6 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨1638,by decide⟩] | _ => ![⟨1639,by decide⟩,⟨1639,by decide⟩,⟨1637,by decide⟩]

def ntree10LRRLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLLLRRL i else ntree10LRRLLLRRR (i - 8)

def ntree10LRRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRLLLRL i else ntree10LRRLLLRR (i - 16)

def ntree10LRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRLLLL i else ntree10LRRLLLR (i - 31)

def ntree10LRRLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1639,by decide⟩,⟨1639,by decide⟩,⟨1638,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨1640,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨1639,by decide⟩,⟨1641,by decide⟩,⟨1642,by decide⟩] | 4 => ![⟨1637,by decide⟩,⟨1640,by decide⟩,⟨1638,by decide⟩] | 5 => ![⟨30,by decide⟩,⟨1643,by decide⟩,⟨1644,by decide⟩] | _ => ![⟨31,by decide⟩,⟨1645,by decide⟩,⟨1646,by decide⟩]

def ntree10LRRLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨1647,by decide⟩,⟨1647,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨1648,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨1647,by decide⟩,⟨1649,by decide⟩,⟨1650,by decide⟩] | 4 => ![⟨1637,by decide⟩,⟨1648,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨1651,by decide⟩,⟨1651,by decide⟩,⟨1651,by decide⟩] | 6 => ![⟨1651,by decide⟩,⟨1652,by decide⟩,⟨1651,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1653,by decide⟩,⟨1653,by decide⟩]

def ntree10LRRLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRLLRLLL i else ntree10LRRLLRLLR (i - 7)

def ntree10LRRLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2,by decide⟩,⟨1654,by decide⟩,⟨1655,by decide⟩] | 1 => ![⟨48,by decide⟩,⟨1656,by decide⟩,⟨1657,by decide⟩] | 2 => ![⟨50,by decide⟩,⟨1658,by decide⟩,⟨1659,by decide⟩] | 3 => ![⟨3,by decide⟩,⟨1660,by decide⟩,⟨1660,by decide⟩] | 4 => ![⟨54,by decide⟩,⟨1661,by decide⟩,⟨1662,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨1656,by decide⟩,⟨1656,by decide⟩] | 6 => ![⟨13,by decide⟩,⟨1658,by decide⟩,⟨1663,by decide⟩] | _ => ![⟨3,by decide⟩,⟨1655,by decide⟩,⟨1655,by decide⟩]

def ntree10LRRLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨1663,by decide⟩,⟨1659,by decide⟩] | 1 => ![⟨1664,by decide⟩,⟨1637,by decide⟩,⟨1664,by decide⟩] | 2 => ![⟨1665,by decide⟩,⟨1639,by decide⟩,⟨1664,by decide⟩] | 3 => ![⟨1637,by decide⟩,⟨1666,by decide⟩,⟨1666,by decide⟩] | 4 => ![⟨1639,by decide⟩,⟨1667,by decide⟩,⟨1666,by decide⟩] | 5 => ![⟨1664,by decide⟩,⟨1666,by decide⟩,⟨1668,by decide⟩] | 6 => ![⟨1665,by decide⟩,⟨1667,by decide⟩,⟨1668,by decide⟩] | _ => ![⟨9,by decide⟩,⟨1669,by decide⟩,⟨1669,by decide⟩]

def ntree10LRRLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLLRLRL i else ntree10LRRLLRLRR (i - 8)

def ntree10LRRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRLLRLL i else ntree10LRRLLRLR (i - 15)

def ntree10LRRLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨31,by decide⟩,⟨1670,by decide⟩,⟨1671,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨1672,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨1673,by decide⟩,⟨1637,by decide⟩,⟨1673,by decide⟩] | 3 => ![⟨1674,by decide⟩,⟨1647,by decide⟩,⟨1673,by decide⟩] | 4 => ![⟨1637,by decide⟩,⟨1675,by decide⟩,⟨1675,by decide⟩] | 5 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 6 => ![⟨1676,by decide⟩,⟨1651,by decide⟩,⟨1676,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1677,by decide⟩,⟨1637,by decide⟩]

def ntree10LRRLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1664,by decide⟩,⟨1677,by decide⟩,⟨1664,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨1678,by decide⟩,⟨1655,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨1679,by decide⟩,⟨1680,by decide⟩] | 3 => ![⟨51,by decide⟩,⟨1681,by decide⟩,⟨1659,by decide⟩] | 4 => ![⟨50,by decide⟩,⟨1623,by decide⟩,⟨1682,by decide⟩] | 5 => ![⟨50,by decide⟩,⟨1683,by decide⟩,⟨1684,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨1681,by decide⟩,⟨1663,by decide⟩] | _ => ![⟨13,by decide⟩,⟨1683,by decide⟩,⟨1685,by decide⟩]

def ntree10LRRLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLLRRLL i else ntree10LRRLLRRLR (i - 8)

def ntree10LRRLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1627,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1686,by decide⟩,⟨1663,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨1686,by decide⟩,⟨1659,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1687,by decide⟩,⟨1671,by decide⟩] | 4 => ![⟨31,by decide⟩,⟨1688,by decide⟩,⟨1689,by decide⟩] | 5 => ![⟨51,by decide⟩,⟨1626,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨1690,by decide⟩,⟨51,by decide⟩] | _ => ![⟨1691,by decide⟩,⟨15,by decide⟩,⟨1691,by decide⟩]

def ntree10LRRLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1692,by decide⟩,⟨31,by decide⟩,⟨1691,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1693,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨1691,by decide⟩,⟨1626,by decide⟩,⟨1691,by decide⟩] | 3 => ![⟨1694,by decide⟩,⟨1695,by decide⟩,⟨1694,by decide⟩] | 4 => ![⟨1695,by decide⟩,⟨1696,by decide⟩,⟨1695,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1690,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨1694,by decide⟩,⟨1696,by decide⟩,⟨1694,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1697,by decide⟩]

def ntree10LRRLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLLRRRL i else ntree10LRRLLRRRR (i - 8)

def ntree10LRRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRLLRRL i else ntree10LRRLLRRR (i - 16)

def ntree10LRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRLLRL i else ntree10LRRLLRR (i - 31)

def ntree10LRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRRLLL i else ntree10LRRLLR (i - 63)

def ntree10LRRLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨0,by decide⟩,⟨1698,by decide⟩,⟨1698,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨1699,by decide⟩,⟨1700,by decide⟩] | 2 => ![⟨1701,by decide⟩,⟨1614,by decide⟩,⟨1697,by decide⟩] | 3 => ![⟨1702,by decide⟩,⟨1625,by decide⟩,⟨1703,by decide⟩] | 4 => ![⟨1704,by decide⟩,⟨1619,by decide⟩,⟨1705,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨1706,by decide⟩,⟨1707,by decide⟩] | _ => ![⟨1708,by decide⟩,⟨1709,by decide⟩,⟨1710,by decide⟩]

def ntree10LRRLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨1703,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨1699,by decide⟩,⟨1699,by decide⟩] | 2 => ![⟨1708,by decide⟩,⟨1626,by decide⟩,⟨1711,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1709,by decide⟩,⟨1712,by decide⟩] | 4 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨1713,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨1714,by decide⟩,⟨1714,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨1715,by decide⟩,⟨1716,by decide⟩] | _ => ![⟨1717,by decide⟩,⟨1619,by decide⟩,⟨1713,by decide⟩]

def ntree10LRRLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRLRLLLL i else ntree10LRRLRLLLR (i - 7)

def ntree10LRRLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1718,by decide⟩,⟨1626,by decide⟩,⟨1719,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨1720,by decide⟩,⟨1720,by decide⟩] | 2 => ![⟨1721,by decide⟩,⟨1629,by decide⟩,⟨1703,by decide⟩] | 3 => ![⟨1722,by decide⟩,⟨1632,by decide⟩,⟨1711,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1723,by decide⟩,⟨1724,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩] | 6 => ![⟨1635,by decide⟩,⟨1635,by decide⟩,⟨1725,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨1726,by decide⟩]

def ntree10LRRLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨1726,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨1727,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨1728,by decide⟩,⟨1728,by decide⟩] | 3 => ![⟨1729,by decide⟩,⟨1640,by decide⟩,⟨1727,by decide⟩] | 4 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨1705,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨1707,by decide⟩,⟨1707,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨1712,by decide⟩,⟨1710,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1730,by decide⟩,⟨1730,by decide⟩]

def ntree10LRRLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLRLLRL i else ntree10LRRLRLLRR (i - 8)

def ntree10LRRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRLRLLL i else ntree10LRRLRLLR (i - 15)

def ntree10LRRLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨1730,by decide⟩,⟨1731,by decide⟩] | 1 => ![⟨1732,by decide⟩,⟨1648,by decide⟩,⟨1726,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨1733,by decide⟩,⟨1730,by decide⟩] | 3 => ![⟨1732,by decide⟩,⟨1733,by decide⟩,⟨1731,by decide⟩] | 4 => ![⟨44,by decide⟩,⟨1734,by decide⟩,⟨1735,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨1736,by decide⟩,⟨1737,by decide⟩] | 6 => ![⟨3,by decide⟩,⟨1738,by decide⟩,⟨1703,by decide⟩] | _ => ![⟨48,by decide⟩,⟨1739,by decide⟩,⟨1740,by decide⟩]

def ntree10LRRLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨1741,by decide⟩,⟨1742,by decide⟩] | 1 => ![⟨52,by decide⟩,⟨1743,by decide⟩,⟨1744,by decide⟩] | 2 => ![⟨54,by decide⟩,⟨1745,by decide⟩,⟨1746,by decide⟩] | 3 => ![⟨48,by decide⟩,⟨1747,by decide⟩,⟨1748,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨1749,by decide⟩,⟨1750,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1672,by decide⟩,⟨1719,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨1751,by decide⟩,⟨1742,by decide⟩] | _ => ![⟨1664,by decide⟩,⟨1752,by decide⟩,⟨1753,by decide⟩]

def ntree10LRRLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLRLRLL i else ntree10LRRLRLRLR (i - 8)

def ntree10LRRLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨1677,by decide⟩,⟨1727,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1672,by decide⟩,⟨1711,by decide⟩] | 2 => ![⟨1673,by decide⟩,⟨1754,by decide⟩,⟨1755,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨1699,by decide⟩,⟨1756,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨1757,by decide⟩,⟨1758,by decide⟩] | 5 => ![⟨3,by decide⟩,⟨1625,by decide⟩,⟨1759,by decide⟩] | 6 => ![⟨1702,by decide⟩,⟨1760,by decide⟩,⟨1761,by decide⟩] | _ => ![⟨1762,by decide⟩,⟨1763,by decide⟩,⟨1742,by decide⟩]

def ntree10LRRLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨1709,by decide⟩,⟨1764,by decide⟩] | 1 => ![⟨1762,by decide⟩,⟨1765,by decide⟩,⟨1766,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨1715,by decide⟩,⟨1767,by decide⟩] | 3 => ![⟨51,by decide⟩,⟨1768,by decide⟩,⟨1769,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨1770,by decide⟩] | 5 => ![⟨1718,by decide⟩,⟨1690,by decide⟩,⟨1771,by decide⟩] | 6 => ![⟨1772,by decide⟩,⟨1773,by decide⟩,⟨1711,by decide⟩] | _ => ![⟨1774,by decide⟩,⟨25,by decide⟩,⟨1719,by decide⟩]

def ntree10LRRLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLRLRRL i else ntree10LRRLRLRRR (i - 8)

def ntree10LRRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRLRLRL i else ntree10LRRLRLRR (i - 16)

def ntree10LRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRLRLL i else ntree10LRRLRLR (i - 31)

def ntree10LRRLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨1712,by decide⟩,⟨1764,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨1775,by decide⟩,⟨1766,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨1776,by decide⟩] | 3 => ![⟨1708,by decide⟩,⟨1690,by decide⟩,⟨1777,by decide⟩] | 4 => ![⟨1691,by decide⟩,⟨148,by decide⟩,⟨1778,by decide⟩] | 5 => ![⟨1691,by decide⟩,⟨1712,by decide⟩,⟨1779,by decide⟩] | _ => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨144,by decide⟩]

def ntree10LRRLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1780,by decide⟩,⟨1781,by decide⟩,⟨1778,by decide⟩] | 1 => ![⟨1691,by decide⟩,⟨1709,by decide⟩,⟨1779,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨1782,by decide⟩,⟨1705,by decide⟩] | 3 => ![⟨11,by decide⟩,⟨1783,by decide⟩,⟨1707,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨1784,by decide⟩,⟨1710,by decide⟩] | 5 => ![⟨1785,by decide⟩,⟨1623,by decide⟩,⟨1786,by decide⟩] | 6 => ![⟨1704,by decide⟩,⟨1787,by decide⟩,⟨1788,by decide⟩] | _ => ![⟨11,by decide⟩,⟨1789,by decide⟩,⟨1790,by decide⟩]

def ntree10LRRLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRLRRLLL i else ntree10LRRLRRLLR (i - 7)

def ntree10LRRLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1785,by decide⟩,⟨1791,by decide⟩,⟨1792,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1793,by decide⟩,⟨1711,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨1784,by decide⟩,⟨1712,by decide⟩] | 3 => ![⟨1708,by decide⟩,⟨1794,by decide⟩,⟨1795,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨1791,by decide⟩,⟨1796,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1797,by decide⟩,⟨1711,by decide⟩] | 6 => ![⟨13,by decide⟩,⟨1798,by decide⟩,⟨1724,by decide⟩] | _ => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1711,by decide⟩]

def ntree10LRRLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1722,by decide⟩,⟨1799,by decide⟩,⟨1795,by decide⟩] | 1 => ![⟨13,by decide⟩,⟨1800,by decide⟩,⟨1801,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1795,by decide⟩] | 3 => ![⟨1802,by decide⟩,⟨1802,by decide⟩,⟨1803,by decide⟩] | 4 => ![⟨1804,by decide⟩,⟨1804,by decide⟩,⟨1802,by decide⟩] | 5 => ![⟨1804,by decide⟩,⟨1804,by decide⟩,⟨1803,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1795,by decide⟩] | _ => ![⟨1805,by decide⟩,⟨1632,by decide⟩,⟨108,by decide⟩]

def ntree10LRRLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLRRLRL i else ntree10LRRLRRLRR (i - 8)

def ntree10LRRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRLRRLL i else ntree10LRRLRRLR (i - 15)

def ntree10LRRLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨159,by decide⟩,⟨1711,by decide⟩] | 1 => ![⟨1806,by decide⟩,⟨1807,by decide⟩,⟨1712,by decide⟩] | 2 => ![⟨1806,by decide⟩,⟨1807,by decide⟩,⟨1710,by decide⟩] | 3 => ![⟨1806,by decide⟩,⟨1808,by decide⟩,⟨160,by decide⟩] | 4 => ![⟨1809,by decide⟩,⟨1808,by decide⟩,⟨1810,by decide⟩] | 5 => ![⟨1811,by decide⟩,⟨1626,by decide⟩,⟨1812,by decide⟩] | 6 => ![⟨50,by decide⟩,⟨1813,by decide⟩,⟨1742,by decide⟩] | _ => ![⟨9,by decide⟩,⟨1656,by decide⟩,⟨1814,by decide⟩]

def ntree10LRRLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨13,by decide⟩,⟨1658,by decide⟩,⟨1815,by decide⟩] | 1 => ![⟨48,by decide⟩,⟨1816,by decide⟩,⟨1817,by decide⟩] | 2 => ![⟨50,by decide⟩,⟨1818,by decide⟩,⟨1819,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1661,by decide⟩,⟨1820,by decide⟩] | 4 => ![⟨54,by decide⟩,⟨1821,by decide⟩,⟨1822,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1663,by decide⟩,⟨1815,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨1823,by decide⟩,⟨1819,by decide⟩] | _ => ![⟨15,by decide⟩,⟨1663,by decide⟩,⟨1824,by decide⟩]

def ntree10LRRLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLRRRLL i else ntree10LRRLRRRLR (i - 8)

def ntree10LRRLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨13,by decide⟩,⟨1658,by decide⟩,⟨1824,by decide⟩] | 1 => ![⟨1825,by decide⟩,⟨1806,by decide⟩,⟨54,by decide⟩] | 2 => ![⟨1806,by decide⟩,⟨1806,by decide⟩,⟨1711,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨72,by decide⟩,⟨1826,by decide⟩] | 4 => ![⟨1806,by decide⟩,⟨1806,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1672,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨1827,by decide⟩,⟨1742,by decide⟩] | _ => ![⟨50,by decide⟩,⟨1784,by decide⟩,⟨1764,by decide⟩]

def ntree10LRRLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨50,by decide⟩,⟨1828,by decide⟩,⟨1766,by decide⟩] | 1 => ![⟨1708,by decide⟩,⟨1681,by decide⟩,⟨1815,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨1623,by decide⟩,⟨1829,by decide⟩] | 3 => ![⟨1785,by decide⟩,⟨1683,by decide⟩,⟨1830,by decide⟩] | 4 => ![⟨1762,by decide⟩,⟨1831,by decide⟩,⟨1819,by decide⟩] | 5 => ![⟨50,by decide⟩,⟨1791,by decide⟩,⟨1832,by decide⟩] | 6 => ![⟨1833,by decide⟩,⟨1834,by decide⟩,⟨1835,by decide⟩] | _ => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩]

def ntree10LRRLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRLRRRRL i else ntree10LRRLRRRRR (i - 8)

def ntree10LRRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRLRRRL i else ntree10LRRLRRRR (i - 16)

def ntree10LRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRLRRL i else ntree10LRRLRRR (i - 31)

def ntree10LRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRRLRL i else ntree10LRRLRR (i - 63)

def ntree10LRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LRRLL i else ntree10LRRLR (i - 126)

def ntree10LRRRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1836,by decide⟩,⟨1663,by decide⟩,⟨1663,by decide⟩] | 1 => ![⟨1837,by decide⟩,⟨1712,by decide⟩,⟨1712,by decide⟩] | 2 => ![⟨1708,by decide⟩,⟨1693,by decide⟩,⟨1826,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨177,by decide⟩,⟨1838,by decide⟩,⟨1631,by decide⟩] | 5 => ![⟨180,by decide⟩,⟨1839,by decide⟩,⟨1634,by decide⟩] | _ => ![⟨3,by decide⟩,⟨1840,by decide⟩,⟨1840,by decide⟩]

def ntree10LRRRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1841,by decide⟩,⟨1625,by decide⟩,⟨1841,by decide⟩] | 1 => ![⟨1842,by decide⟩,⟨1843,by decide⟩,⟨1844,by decide⟩] | 2 => ![⟨1845,by decide⟩,⟨1626,by decide⟩,⟨1845,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1846,by decide⟩,⟨1846,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1847,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨1848,by decide⟩,⟨1626,by decide⟩,⟨1848,by decide⟩] | 6 => ![⟨1849,by decide⟩,⟨1839,by decide⟩,⟨1850,by decide⟩] | _ => ![⟨1851,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩]

def ntree10LRRRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRRLLLLL i else ntree10LRRRLLLLR (i - 7)

def ntree10LRRRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨1852,by decide⟩,⟨1852,by decide⟩] | 1 => ![⟨188,by decide⟩,⟨1631,by decide⟩,⟨1853,by decide⟩] | 2 => ![⟨191,by decide⟩,⟨1854,by decide⟩,⟨1855,by decide⟩] | 3 => ![⟨191,by decide⟩,⟨1634,by decide⟩,⟨1856,by decide⟩] | 4 => ![⟨195,by decide⟩,⟨195,by decide⟩,⟨1857,by decide⟩] | 5 => ![⟨1635,by decide⟩,⟨1858,by decide⟩,⟨1858,by decide⟩] | 6 => ![⟨1859,by decide⟩,⟨1635,by decide⟩,⟨1859,by decide⟩] | _ => ![⟨1860,by decide⟩,⟨1861,by decide⟩,⟨1862,by decide⟩]

def ntree10LRRRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1860,by decide⟩,⟨1637,by decide⟩,⟨1860,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨1863,by decide⟩,⟨1863,by decide⟩] | 2 => ![⟨1864,by decide⟩,⟨1637,by decide⟩,⟨1864,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1642,by decide⟩,⟨1865,by decide⟩] | 4 => ![⟨1637,by decide⟩,⟨1642,by decide⟩,⟨1642,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1866,by decide⟩,⟨1866,by decide⟩] | 6 => ![⟨1867,by decide⟩,⟨1867,by decide⟩,⟨15,by decide⟩] | _ => ![⟨15,by decide⟩,⟨1868,by decide⟩,⟨15,by decide⟩]

def ntree10LRRRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRLLLRL i else ntree10LRRRLLLRR (i - 8)

def ntree10LRRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRRLLLL i else ntree10LRRRLLLR (i - 15)

def ntree10LRRRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨191,by decide⟩,⟨1626,by decide⟩,⟨191,by decide⟩] | 1 => ![⟨1869,by decide⟩,⟨1870,by decide⟩,⟨1871,by decide⟩] | 2 => ![⟨1872,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨195,by decide⟩,⟨1873,by decide⟩,⟨195,by decide⟩] | 4 => ![⟨1860,by decide⟩,⟨1648,by decide⟩,⟨1860,by decide⟩] | 5 => ![⟨1874,by decide⟩,⟨1648,by decide⟩,⟨1637,by decide⟩] | 6 => ![⟨1875,by decide⟩,⟨3,by decide⟩,⟨1875,by decide⟩] | _ => ![⟨1876,by decide⟩,⟨1876,by decide⟩,⟨1627,by decide⟩]

def ntree10LRRRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1877,by decide⟩,⟨15,by decide⟩,⟨1878,by decide⟩] | 1 => ![⟨1879,by decide⟩,⟨1663,by decide⟩,⟨1663,by decide⟩] | 2 => ![⟨1880,by decide⟩,⟨1663,by decide⟩,⟨1881,by decide⟩] | 3 => ![⟨231,by decide⟩,⟨1655,by decide⟩,⟨1882,by decide⟩] | 4 => ![⟨234,by decide⟩,⟨1883,by decide⟩,⟨1884,by decide⟩] | 5 => ![⟨1885,by decide⟩,⟨1635,by decide⟩,⟨1885,by decide⟩] | 6 => ![⟨1886,by decide⟩,⟨1637,by decide⟩,⟨1887,by decide⟩] | _ => ![⟨1888,by decide⟩,⟨1666,by decide⟩,⟨1889,by decide⟩]

def ntree10LRRRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRLLRLL i else ntree10LRRRLLRLR (i - 8)

def ntree10LRRRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1890,by decide⟩,⟨1867,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨252,by decide⟩,⟨1671,by decide⟩,⟨1671,by decide⟩] | 2 => ![⟨248,by decide⟩,⟨1671,by decide⟩,⟨1891,by decide⟩] | 3 => ![⟨1892,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 4 => ![⟨1886,by decide⟩,⟨1637,by decide⟩,⟨1886,by decide⟩] | 5 => ![⟨1893,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 6 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | _ => ![⟨1875,by decide⟩,⟨1625,by decide⟩,⟨1875,by decide⟩]

def ntree10LRRRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1894,by decide⟩,⟨1895,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨1896,by decide⟩,⟨1895,by decide⟩,⟨1878,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨1847,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨1897,by decide⟩,⟨1681,by decide⟩,⟨1881,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨1852,by decide⟩,⟨1898,by decide⟩] | 5 => ![⟨188,by decide⟩,⟨1655,by decide⟩,⟨1899,by decide⟩] | 6 => ![⟨261,by decide⟩,⟨1900,by decide⟩,⟨1901,by decide⟩] | _ => ![⟨51,by decide⟩,⟨1866,by decide⟩,⟨1902,by decide⟩]

def ntree10LRRRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRLLRRL i else ntree10LRRRLLRRR (i - 8)

def ntree10LRRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRRLLRL i else ntree10LRRRLLRR (i - 16)

def ntree10LRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRRLLL i else ntree10LRRRLLR (i - 31)

def ntree10LRRRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨202,by decide⟩,⟨1663,by decide⟩,⟨1903,by decide⟩] | 1 => ![⟨1904,by decide⟩,⟨1687,by decide⟩,⟨1905,by decide⟩] | 2 => ![⟨261,by decide⟩,⟨1906,by decide⟩,⟨261,by decide⟩] | 3 => ![⟨1907,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨1877,by decide⟩,⟨1626,by decide⟩,⟨1877,by decide⟩] | _ => ![⟨252,by decide⟩,⟨1626,by decide⟩,⟨1908,by decide⟩]

def ntree10LRRRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1909,by decide⟩,⟨1724,by decide⟩] | 1 => ![⟨1910,by decide⟩,⟨1910,by decide⟩,⟨1703,by decide⟩] | 2 => ![⟨1911,by decide⟩,⟨1912,by decide⟩,⟨1913,by decide⟩] | 3 => ![⟨1914,by decide⟩,⟨1915,by decide⟩,⟨1916,by decide⟩] | 4 => ![⟨1917,by decide⟩,⟨1917,by decide⟩,⟨1719,by decide⟩] | 5 => ![⟨1918,by decide⟩,⟨1919,by decide⟩,⟨1919,by decide⟩] | 6 => ![⟨1918,by decide⟩,⟨1920,by decide⟩,⟨1719,by decide⟩] | _ => ![⟨1921,by decide⟩,⟨1915,by decide⟩,⟨1922,by decide⟩]

def ntree10LRRRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRRLRLLL i else ntree10LRRRLRLLR (i - 7)

def ntree10LRRRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1917,by decide⟩,⟨1915,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨1918,by decide⟩,⟨1626,by decide⟩,⟨288,by decide⟩] | 2 => ![⟨188,by decide⟩,⟨3,by decide⟩,⟨1923,by decide⟩] | 3 => ![⟨191,by decide⟩,⟨15,by decide⟩,⟨1924,by decide⟩] | 4 => ![⟨191,by decide⟩,⟨1724,by decide⟩,⟨1925,by decide⟩] | 5 => ![⟨195,by decide⟩,⟨195,by decide⟩,⟨1926,by decide⟩] | 6 => ![⟨1859,by decide⟩,⟨1635,by decide⟩,⟨1927,by decide⟩] | _ => ![⟨1860,by decide⟩,⟨1637,by decide⟩,⟨1928,by decide⟩]

def ntree10LRRRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1864,by decide⟩,⟨1637,by decide⟩,⟨1929,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨1930,by decide⟩] | 2 => ![⟨299,by decide⟩,⟨299,by decide⟩,⟨1711,by decide⟩] | 3 => ![⟨300,by decide⟩,⟨1724,by decide⟩,⟨1724,by decide⟩] | 4 => ![⟨300,by decide⟩,⟨1931,by decide⟩,⟨1711,by decide⟩] | 5 => ![⟨1932,by decide⟩,⟨1933,by decide⟩,⟨1924,by decide⟩] | 6 => ![⟨1934,by decide⟩,⟨1909,by decide⟩,⟨1925,by decide⟩] | _ => ![⟨1935,by decide⟩,⟨1936,by decide⟩,⟨1926,by decide⟩]

def ntree10LRRRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRLRLRL i else ntree10LRRRLRLRR (i - 8)

def ntree10LRRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRRLRLL i else ntree10LRRRLRLR (i - 15)

def ntree10LRRRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1937,by decide⟩,⟨1937,by decide⟩,⟨1726,by decide⟩] | 1 => ![⟨1938,by decide⟩,⟨1939,by decide⟩,⟨1928,by decide⟩] | 2 => ![⟨1937,by decide⟩,⟨1937,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨1940,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 4 => ![⟨1937,by decide⟩,⟨1939,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨1940,by decide⟩,⟨1648,by decide⟩,⟨1930,by decide⟩] | 6 => ![⟨1875,by decide⟩,⟨306,by decide⟩,⟨1941,by decide⟩] | _ => ![⟨1917,by decide⟩,⟨1917,by decide⟩,⟨1711,by decide⟩]

def ntree10LRRRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1877,by decide⟩,⟨308,by decide⟩,⟨1942,by decide⟩] | 1 => ![⟨1943,by decide⟩,⟨1944,by decide⟩,⟨1750,by decide⟩] | 2 => ![⟨1880,by decide⟩,⟨308,by decide⟩,⟨1945,by decide⟩] | 3 => ![⟨1943,by decide⟩,⟨1917,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨3,by decide⟩,⟨1946,by decide⟩,⟨1946,by decide⟩] | 5 => ![⟨231,by decide⟩,⟨1946,by decide⟩,⟨1947,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨1948,by decide⟩,⟨1949,by decide⟩] | _ => ![⟨234,by decide⟩,⟨1950,by decide⟩,⟨1951,by decide⟩]

def ntree10LRRRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRLRRLL i else ntree10LRRRLRRLR (i - 8)

def ntree10LRRRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1635,by decide⟩,⟨1952,by decide⟩,⟨1952,by decide⟩] | 1 => ![⟨1885,by decide⟩,⟨1952,by decide⟩,⟨1953,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨1954,by decide⟩,⟨1954,by decide⟩] | 3 => ![⟨1886,by decide⟩,⟨1954,by decide⟩,⟨1955,by decide⟩] | 4 => ![⟨1888,by decide⟩,⟨1954,by decide⟩,⟨1956,by decide⟩] | 5 => ![⟨1664,by decide⟩,⟨1954,by decide⟩,⟨1957,by decide⟩] | 6 => ![⟨327,by decide⟩,⟨1958,by decide⟩,⟨1742,by decide⟩] | _ => ![⟨15,by decide⟩,⟨1948,by decide⟩,⟨1948,by decide⟩]

def ntree10LRRRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨248,by decide⟩,⟨1948,by decide⟩,⟨1959,by decide⟩] | 1 => ![⟨1960,by decide⟩,⟨1937,by decide⟩,⟨1664,by decide⟩] | 2 => ![⟨1961,by decide⟩,⟨1961,by decide⟩,⟨3,by decide⟩] | 3 => ![⟨1961,by decide⟩,⟨1961,by decide⟩,⟨1703,by decide⟩] | 4 => ![⟨1961,by decide⟩,⟨1962,by decide⟩,⟨306,by decide⟩] | 5 => ![⟨1963,by decide⟩,⟨1962,by decide⟩,⟨1941,by decide⟩] | 6 => ![⟨1964,by decide⟩,⟨1965,by decide⟩,⟨308,by decide⟩] | _ => ![⟨1966,by decide⟩,⟨1965,by decide⟩,⟨1942,by decide⟩]

def ntree10LRRRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRLRRRL i else ntree10LRRRLRRRR (i - 8)

def ntree10LRRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRRLRRL i else ntree10LRRRLRRR (i - 16)

def ntree10LRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRRLRL i else ntree10LRRRLRR (i - 31)

def ntree10LRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRRRLL i else ntree10LRRRLR (i - 63)

def ntree10LRRRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1967,by decide⟩,⟨1964,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨1967,by decide⟩,⟨1968,by decide⟩,⟨1750,by decide⟩] | 2 => ![⟨1969,by decide⟩,⟨1965,by decide⟩,⟨1945,by decide⟩] | 3 => ![⟨1967,by decide⟩,⟨1965,by decide⟩,⟨311,by decide⟩] | 4 => ![⟨261,by decide⟩,⟨1970,by decide⟩,⟨1971,by decide⟩] | 5 => ![⟨202,by decide⟩,⟨15,by decide⟩,⟨1972,by decide⟩] | _ => ![⟨1973,by decide⟩,⟨1974,by decide⟩,⟨1971,by decide⟩]

def ntree10LRRRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1964,by decide⟩,⟨1964,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨1964,by decide⟩,⟨1964,by decide⟩,⟨1711,by decide⟩] | 2 => ![⟨1975,by decide⟩,⟨1965,by decide⟩,⟨340,by decide⟩] | 3 => ![⟨299,by decide⟩,⟨1933,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨327,by decide⟩,⟨1933,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨180,by decide⟩,⟨1976,by decide⟩,⟨1724,by decide⟩] | 6 => ![⟨180,by decide⟩,⟨1977,by decide⟩,⟨1801,by decide⟩] | _ => ![⟨1978,by decide⟩,⟨1979,by decide⟩,⟨1980,by decide⟩]

def ntree10LRRRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRRRLLLL i else ntree10LRRRRLLLR (i - 7)

def ntree10LRRRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1981,by decide⟩,⟨1793,by decide⟩,⟨1981,by decide⟩] | 1 => ![⟨1982,by decide⟩,⟨1983,by decide⟩,⟨1984,by decide⟩] | 2 => ![⟨1985,by decide⟩,⟨1794,by decide⟩,⟨1985,by decide⟩] | 3 => ![⟨1978,by decide⟩,⟨1917,by decide⟩,⟨1981,by decide⟩] | 4 => ![⟨1986,by decide⟩,⟨180,by decide⟩,⟨1981,by decide⟩] | 5 => ![⟨1987,by decide⟩,⟨1988,by decide⟩,⟨1988,by decide⟩] | 6 => ![⟨1988,by decide⟩,⟨1989,by decide⟩,⟨1988,by decide⟩] | _ => ![⟨1978,by decide⟩,⟨1915,by decide⟩,⟨1990,by decide⟩]

def ntree10LRRRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1986,by decide⟩,⟨1839,by decide⟩,⟨1991,by decide⟩] | 1 => ![⟨1987,by decide⟩,⟨1989,by decide⟩,⟨1992,by decide⟩] | 2 => ![⟨360,by decide⟩,⟨1866,by decide⟩,⟨1993,by decide⟩] | 3 => ![⟨360,by decide⟩,⟨1724,by decide⟩,⟨1994,by decide⟩] | 4 => ![⟨363,by decide⟩,⟨363,by decide⟩,⟨1995,by decide⟩] | 5 => ![⟨202,by decide⟩,⟨15,by decide⟩,⟨1996,by decide⟩] | 6 => ![⟨202,by decide⟩,⟨1634,by decide⟩,⟨1997,by decide⟩] | _ => ![⟨15,by decide⟩,⟨1801,by decide⟩,⟨1801,by decide⟩]

def ntree10LRRRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRRLLRL i else ntree10LRRRRLLRR (i - 8)

def ntree10LRRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRRRLLL i else ntree10LRRRRLLR (i - 15)

def ntree10LRRRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1998,by decide⟩,⟨1999,by decide⟩,⟨2000,by decide⟩] | 1 => ![⟨1998,by decide⟩,⟨1802,by decide⟩,⟨1998,by decide⟩] | 2 => ![⟨2001,by decide⟩,⟨1802,by decide⟩,⟨2002,by decide⟩] | 3 => ![⟨2001,by decide⟩,⟨1802,by decide⟩,⟨2001,by decide⟩] | 4 => ![⟨1985,by decide⟩,⟨2003,by decide⟩,⟨1984,by decide⟩] | 5 => ![⟨1985,by decide⟩,⟨15,by decide⟩,⟨1985,by decide⟩] | 6 => ![⟨1981,by decide⟩,⟨1866,by decide⟩,⟨2004,by decide⟩] | _ => ![⟨1981,by decide⟩,⟨109,by decide⟩,⟨2005,by decide⟩]

def ntree10LRRRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1988,by decide⟩,⟨1988,by decide⟩,⟨2006,by decide⟩] | 1 => ![⟨1981,by decide⟩,⟨15,by decide⟩,⟨1990,by decide⟩] | 2 => ![⟨1981,by decide⟩,⟨1634,by decide⟩,⟨1991,by decide⟩] | 3 => ![⟨1988,by decide⟩,⟨1988,by decide⟩,⟨1992,by decide⟩] | 4 => ![⟨2007,by decide⟩,⟨2008,by decide⟩,⟨1995,by decide⟩] | 5 => ![⟨2009,by decide⟩,⟨2010,by decide⟩,⟨1993,by decide⟩] | 6 => ![⟨1917,by decide⟩,⟨2010,by decide⟩,⟨1866,by decide⟩] | _ => ![⟨1918,by decide⟩,⟨159,by decide⟩,⟨15,by decide⟩]

def ntree10LRRRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRRLRLL i else ntree10LRRRRLRLR (i - 8)

def ntree10LRRRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2011,by decide⟩,⟨15,by decide⟩,⟨2012,by decide⟩] | 1 => ![⟨2013,by decide⟩,⟨2013,by decide⟩,⟨1795,by decide⟩] | 2 => ![⟨2014,by decide⟩,⟨308,by decide⟩,⟨2015,by decide⟩] | 3 => ![⟨2016,by decide⟩,⟨1988,by decide⟩,⟨2016,by decide⟩] | 4 => ![⟨1917,by decide⟩,⟨2017,by decide⟩,⟨1663,by decide⟩] | 5 => ![⟨1988,by decide⟩,⟨2018,by decide⟩,⟨2018,by decide⟩] | 6 => ![⟨1943,by decide⟩,⟨2017,by decide⟩,⟨1659,by decide⟩] | _ => ![⟨2016,by decide⟩,⟨2018,by decide⟩,⟨2019,by decide⟩]

def ntree10LRRRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨380,by decide⟩,⟨2020,by decide⟩,⟨2021,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨2022,by decide⟩,⟨2022,by decide⟩] | 2 => ![⟨383,by decide⟩,⟨2023,by decide⟩,⟨2024,by decide⟩] | 3 => ![⟨1802,by decide⟩,⟨1802,by decide⟩,⟨1802,by decide⟩] | 4 => ![⟨2025,by decide⟩,⟨1802,by decide⟩,⟨2026,by decide⟩] | 5 => ![⟨1802,by decide⟩,⟨2027,by decide⟩,⟨2027,by decide⟩] | 6 => ![⟨2028,by decide⟩,⟨2027,by decide⟩,⟨2029,by decide⟩] | _ => ![⟨2016,by decide⟩,⟨2030,by decide⟩,⟨2031,by decide⟩]

def ntree10LRRRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRRLRRL i else ntree10LRRRRLRRR (i - 8)

def ntree10LRRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRRRLRL i else ntree10LRRRRLRR (i - 16)

def ntree10LRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRRRLL i else ntree10LRRRRLR (i - 31)

def ntree10LRRRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2032,by decide⟩,⟨2018,by decide⟩,⟨2033,by decide⟩] | 1 => ![⟨252,by decide⟩,⟨2034,by decide⟩,⟨1711,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2035,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2036,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨393,by decide⟩,⟨15,by decide⟩,⟨2037,by decide⟩] | 5 => ![⟨2038,by decide⟩,⟨1917,by decide⟩,⟨15,by decide⟩] | _ => ![⟨51,by decide⟩,⟨1793,by decide⟩,⟨51,by decide⟩]

def ntree10LRRRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨1794,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨1964,by decide⟩,⟨2039,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2040,by decide⟩,⟨2039,by decide⟩,⟨2012,by decide⟩] | 4 => ![⟨2041,by decide⟩,⟨2042,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨2043,by decide⟩,⟨2042,by decide⟩,⟨2015,by decide⟩] | 6 => ![⟨2044,by decide⟩,⟨2045,by decide⟩,⟨2016,by decide⟩] | _ => ![⟨2045,by decide⟩,⟨2046,by decide⟩,⟨2018,by decide⟩]

def ntree10LRRRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LRRRRRLLL i else ntree10LRRRRRLLR (i - 7)

def ntree10LRRRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2044,by decide⟩,⟨2046,by decide⟩,⟨2019,by decide⟩] | 1 => ![⟨396,by decide⟩,⟨2047,by decide⟩,⟨2048,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨2049,by decide⟩,⟨2050,by decide⟩] | 3 => ![⟨2051,by decide⟩,⟨2052,by decide⟩,⟨2053,by decide⟩] | 4 => ![⟨397,by decide⟩,⟨2054,by decide⟩,⟨397,by decide⟩] | 5 => ![⟨2055,by decide⟩,⟨1964,by decide⟩,⟨360,by decide⟩] | 6 => ![⟨9,by decide⟩,⟨2056,by decide⟩,⟨9,by decide⟩] | _ => ![⟨11,by decide⟩,⟨2057,by decide⟩,⟨1644,by decide⟩]

def ntree10LRRRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨13,by decide⟩,⟨2058,by decide⟩,⟨1646,by decide⟩] | 1 => ![⟨1845,by decide⟩,⟨2059,by decide⟩,⟨1845,by decide⟩] | 2 => ![⟨2060,by decide⟩,⟨2058,by decide⟩,⟨2061,by decide⟩] | 3 => ![⟨1842,by decide⟩,⟨1876,by decide⟩,⟨1845,by decide⟩] | 4 => ![⟨2060,by decide⟩,⟨13,by decide⟩,⟨1845,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨2062,by decide⟩,⟨2062,by decide⟩] | 6 => ![⟨13,by decide⟩,⟨2063,by decide⟩,⟨2064,by decide⟩] | _ => ![⟨191,by decide⟩,⟨2065,by decide⟩,⟨191,by decide⟩]

def ntree10LRRRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRRRLRL i else ntree10LRRRRRLRR (i - 8)

def ntree10LRRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LRRRRRLL i else ntree10LRRRRRLR (i - 15)

def ntree10LRRRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨418,by decide⟩,⟨2066,by decide⟩,⟨1871,by decide⟩] | 1 => ![⟨2067,by decide⟩,⟨1639,by decide⟩,⟨1860,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨2068,by decide⟩,⟨2068,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨2069,by decide⟩,⟨2069,by decide⟩] | 4 => ![⟨426,by decide⟩,⟨1644,by decide⟩,⟨2070,by decide⟩] | 5 => ![⟨429,by decide⟩,⟨1646,by decide⟩,⟨2071,by decide⟩] | 6 => ![⟨1860,by decide⟩,⟨1650,by decide⟩,⟨2072,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1650,by decide⟩,⟨1650,by decide⟩]

def ntree10LRRRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1651,by decide⟩,⟨2073,by decide⟩,⟨2073,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨2074,by decide⟩,⟨2074,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨2075,by decide⟩,⟨1671,by decide⟩] | 3 => ![⟨2076,by decide⟩,⟨2077,by decide⟩,⟨2077,by decide⟩] | 4 => ![⟨2078,by decide⟩,⟨13,by decide⟩,⟨1877,by decide⟩] | 5 => ![⟨2079,by decide⟩,⟨1876,by decide⟩,⟨54,by decide⟩] | 6 => ![⟨454,by decide⟩,⟨1671,by decide⟩,⟨1671,by decide⟩] | _ => ![⟨456,by decide⟩,⟨2075,by decide⟩,⟨1891,by decide⟩]

def ntree10LRRRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRRRRLL i else ntree10LRRRRRRLR (i - 8)

def ntree10LRRRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2080,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 1 => ![⟨2081,by decide⟩,⟨1639,by decide⟩,⟨1886,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2082,by decide⟩,⟨1671,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨2083,by decide⟩,⟨1689,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2084,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨2084,by decide⟩] | 6 => ![⟨2076,by decide⟩,⟨2059,by decide⟩,⟨2085,by decide⟩] | _ => ![⟨2078,by decide⟩,⟨2058,by decide⟩,⟨2086,by decide⟩]

def ntree10LRRRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2087,by decide⟩,⟨2088,by decide⟩,⟨2088,by decide⟩] | 1 => ![⟨2089,by decide⟩,⟨2089,by decide⟩,⟨2088,by decide⟩] | 2 => ![⟨2090,by decide⟩,⟨2089,by decide⟩,⟨2091,by decide⟩] | 3 => ![⟨51,by decide⟩,⟨2064,by decide⟩,⟨2092,by decide⟩] | 4 => ![⟨50,by decide⟩,⟨2063,by decide⟩,⟨2092,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2093,by decide⟩] | 6 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨2093,by decide⟩] | _ => ![⟨191,by decide⟩,⟨1671,by decide⟩,⟨1905,by decide⟩]

def ntree10LRRRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LRRRRRRRL i else ntree10LRRRRRRRR (i - 8)

def ntree10LRRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LRRRRRRL i else ntree10LRRRRRRR (i - 16)

def ntree10LRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LRRRRRL i else ntree10LRRRRRR (i - 31)

def ntree10LRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LRRRRL i else ntree10LRRRRR (i - 63)

def ntree10LRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LRRRL i else ntree10LRRRR (i - 126)

def ntree10LRR (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10LRRL i else ntree10LRRR (i - 252)

def ntree10LR (i : Nat) : Fin 3 → Fin 3959 := if i < 504 then ntree10LRL i else ntree10LRR (i - 504)

def ntree10L (i : Nat) : Fin 3 → Fin 3959 := if i < 1008 then ntree10LL i else ntree10LR (i - 1008)

def ntree10RLLLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2094,by decide⟩,⟨15,by decide⟩,⟨191,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1908,by decide⟩] | 2 => ![⟨191,by decide⟩,⟨1646,by decide⟩,⟨2095,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1689,by decide⟩,⟨1689,by decide⟩] | 4 => ![⟨1691,by decide⟩,⟨1866,by decide⟩,⟨2096,by decide⟩] | 5 => ![⟨191,by decide⟩,⟨72,by decide⟩,⟨2097,by decide⟩] | _ => ![⟨1877,by decide⟩,⟨1646,by decide⟩,⟨2086,by decide⟩]

def ntree10RLLLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2098,by decide⟩,⟨2088,by decide⟩,⟨2098,by decide⟩] | 1 => ![⟨2091,by decide⟩,⟨2088,by decide⟩,⟨2091,by decide⟩] | 2 => ![⟨1694,by decide⟩,⟨2099,by decide⟩,⟨2100,by decide⟩] | 3 => ![⟨1695,by decide⟩,⟨1695,by decide⟩,⟨2101,by decide⟩] | 4 => ![⟨1695,by decide⟩,⟨1695,by decide⟩,⟨1695,by decide⟩] | 5 => ![⟨2102,by decide⟩,⟨2056,by decide⟩,⟨1705,by decide⟩] | 6 => ![⟨2103,by decide⟩,⟨2059,by decide⟩,⟨1711,by decide⟩] | _ => ![⟨2104,by decide⟩,⟨2104,by decide⟩,⟨1711,by decide⟩]

def ntree10RLLLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLLLLLLL i else ntree10RLLLLLLLR (i - 7)

def ntree10RLLLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2105,by decide⟩,⟨1712,by decide⟩,⟨1712,by decide⟩] | 1 => ![⟨2106,by decide⟩,⟨2107,by decide⟩,⟨1916,by decide⟩] | 2 => ![⟨1845,by decide⟩,⟨15,by decide⟩,⟨1916,by decide⟩] | 3 => ![⟨1845,by decide⟩,⟨1712,by decide⟩,⟨2108,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨2109,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2110,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 6 => ![⟨2111,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨2112,by decide⟩,⟨2112,by decide⟩,⟨1711,by decide⟩]

def ntree10RLLLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨497,by decide⟩,⟨1724,by decide⟩,⟨1724,by decide⟩] | 1 => ![⟨2113,by decide⟩,⟨2114,by decide⟩,⟨1924,by decide⟩] | 2 => ![⟨2115,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨2116,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 4 => ![⟨426,by decide⟩,⟨9,by decide⟩,⟨2117,by decide⟩] | 5 => ![⟨429,by decide⟩,⟨15,by decide⟩,⟨2118,by decide⟩] | 6 => ![⟨426,by decide⟩,⟨1707,by decide⟩,⟨2119,by decide⟩] | _ => ![⟨430,by decide⟩,⟨2120,by decide⟩,⟨2121,by decide⟩]

def ntree10RLLLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLLLLRL i else ntree10RLLLLLLRR (i - 8)

def ntree10RLLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLLLLLL i else ntree10RLLLLLLR (i - 15)

def ntree10RLLLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1860,by decide⟩,⟨1730,by decide⟩,⟨2122,by decide⟩] | 1 => ![⟨1651,by decide⟩,⟨1651,by decide⟩,⟨2123,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2124,by decide⟩,⟨1711,by decide⟩] | 3 => ![⟨2125,by decide⟩,⟨2126,by decide⟩,⟨1746,by decide⟩] | 4 => ![⟨2127,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩] | 5 => ![⟨2128,by decide⟩,⟨2129,by decide⟩,⟨1742,by decide⟩] | 6 => ![⟨2130,by decide⟩,⟨2131,by decide⟩,⟨1959,by decide⟩] | _ => ![⟨2132,by decide⟩,⟨1637,by decide⟩,⟨1726,by decide⟩]

def ntree10RLLLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨9,by decide⟩,⟨2133,by decide⟩,⟨2133,by decide⟩] | 1 => ![⟨48,by decide⟩,⟨2133,by decide⟩,⟨2134,by decide⟩] | 2 => ![⟨1673,by decide⟩,⟨1954,by decide⟩,⟨2135,by decide⟩] | 3 => ![⟨1651,by decide⟩,⟨2136,by decide⟩,⟨2136,by decide⟩] | 4 => ![⟨1676,by decide⟩,⟨2136,by decide⟩,⟨2137,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2059,by decide⟩,⟨1776,by decide⟩] | 6 => ![⟨2103,by decide⟩,⟨2138,by decide⟩,⟨1777,by decide⟩] | _ => ![⟨2139,by decide⟩,⟨2140,by decide⟩,⟨1712,by decide⟩]

def ntree10RLLLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLLLRLL i else ntree10RLLLLLRLR (i - 8)

def ntree10RLLLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2141,by decide⟩,⟨2140,by decide⟩,⟨1710,by decide⟩] | 1 => ![⟨2139,by decide⟩,⟨2142,by decide⟩,⟨308,by decide⟩] | 2 => ![⟨2143,by decide⟩,⟨2142,by decide⟩,⟨1942,by decide⟩] | 3 => ![⟨2088,by decide⟩,⟨2088,by decide⟩,⟨2144,by decide⟩] | 4 => ![⟨2088,by decide⟩,⟨2145,by decide⟩,⟨2145,by decide⟩] | 5 => ![⟨2091,by decide⟩,⟨2145,by decide⟩,⟨2146,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨2109,by decide⟩,⟨51,by decide⟩] | _ => ![⟨2147,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩]

def ntree10RLLLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2148,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨191,by decide⟩,⟨2149,by decide⟩,⟨2150,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1777,by decide⟩] | 3 => ![⟨261,by decide⟩,⟨2151,by decide⟩,⟨2152,by decide⟩] | 4 => ![⟨2098,by decide⟩,⟨2153,by decide⟩,⟨2154,by decide⟩] | 5 => ![⟨2098,by decide⟩,⟨2145,by decide⟩,⟨2155,by decide⟩] | 6 => ![⟨1695,by decide⟩,⟨2156,by decide⟩,⟨2156,by decide⟩] | _ => ![⟨1694,by decide⟩,⟨2156,by decide⟩,⟨2157,by decide⟩]

def ntree10RLLLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLLLRRL i else ntree10RLLLLLRRR (i - 8)

def ntree10RLLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLLLLRL i else ntree10RLLLLLRR (i - 16)

def ntree10RLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLLLLL i else ntree10RLLLLLR (i - 31)

def ntree10RLLLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1842,by decide⟩,⟨2158,by decide⟩,⟨1916,by decide⟩] | 1 => ![⟨2060,by decide⟩,⟨1784,by decide⟩,⟨2108,by decide⟩] | 2 => ![⟨2159,by decide⟩,⟨2160,by decide⟩,⟨1993,by decide⟩] | 3 => ![⟨545,by decide⟩,⟨1798,by decide⟩,⟨1994,by decide⟩] | 4 => ![⟨2161,by decide⟩,⟨2161,by decide⟩,⟨1995,by decide⟩] | 5 => ![⟨547,by decide⟩,⟨2068,by decide⟩,⟨2162,by decide⟩] | _ => ![⟨547,by decide⟩,⟨1707,by decide⟩,⟨2163,by decide⟩]

def ntree10RLLLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨550,by decide⟩,⟨2164,by decide⟩,⟨2165,by decide⟩] | 1 => ![⟨360,by decide⟩,⟨1712,by decide⟩,⟨2166,by decide⟩] | 2 => ![⟨1845,by decide⟩,⟨160,by decide⟩,⟨2167,by decide⟩] | 3 => ![⟨2168,by decide⟩,⟨160,by decide⟩,⟨1810,by decide⟩] | 4 => ![⟨2169,by decide⟩,⟨15,by decide⟩,⟨2170,by decide⟩] | 5 => ![⟨2076,by decide⟩,⟨567,by decide⟩,⟨1711,by decide⟩] | 6 => ![⟨2078,by decide⟩,⟨555,by decide⟩,⟨1942,by decide⟩] | _ => ![⟨2079,by decide⟩,⟨2171,by decide⟩,⟨1746,by decide⟩]

def ntree10RLLLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLLLRLLL i else ntree10RLLLLRLLR (i - 7)

def ntree10RLLLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2172,by decide⟩,⟨2173,by decide⟩,⟨2021,by decide⟩] | 1 => ![⟨2174,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩] | 2 => ![⟨2175,by decide⟩,⟨13,by decide⟩,⟨2037,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1776,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨1777,by decide⟩] | 6 => ![⟨2087,by decide⟩,⟨2176,by decide⟩,⟨2144,by decide⟩] | _ => ![⟨2089,by decide⟩,⟨2177,by decide⟩,⟨2145,by decide⟩]

def ntree10RLLLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2090,by decide⟩,⟨2177,by decide⟩,⟨2146,by decide⟩] | 1 => ![⟨397,by decide⟩,⟨397,by decide⟩,⟨2053,by decide⟩] | 2 => ![⟨2178,by decide⟩,⟨567,by decide⟩,⟨1908,by decide⟩] | 3 => ![⟨396,by decide⟩,⟨2179,by decide⟩,⟨2180,by decide⟩] | 4 => ![⟨397,by decide⟩,⟨397,by decide⟩,⟨2181,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨2182,by decide⟩] | 6 => ![⟨3,by decide⟩,⟨2183,by decide⟩,⟨2183,by decide⟩] | _ => ![⟨2,by decide⟩,⟨2184,by decide⟩,⟨2183,by decide⟩]

def ntree10RLLLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLLRLRL i else ntree10RLLLLRLRR (i - 8)

def ntree10RLLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLLLRLL i else ntree10RLLLLRLR (i - 15)

def ntree10RLLLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨580,by decide⟩,⟨2185,by decide⟩,⟨2186,by decide⟩] | 1 => ![⟨582,by decide⟩,⟨2187,by decide⟩,⟨2188,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2186,by decide⟩,⟨2186,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨2189,by decide⟩,⟨2186,by decide⟩] | 4 => ![⟨2190,by decide⟩,⟨1626,by decide⟩,⟨2190,by decide⟩] | 5 => ![⟨2191,by decide⟩,⟨1623,by decide⟩,⟨2192,by decide⟩] | 6 => ![⟨2193,by decide⟩,⟨2185,by decide⟩,⟨2194,by decide⟩] | _ => ![⟨1635,by decide⟩,⟨2195,by decide⟩,⟨2195,by decide⟩]

def ntree10RLLLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1636,by decide⟩,⟨2196,by decide⟩,⟨2195,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨2197,by decide⟩,⟨2197,by decide⟩] | 2 => ![⟨1639,by decide⟩,⟨2198,by decide⟩,⟨2197,by decide⟩] | 3 => ![⟨2199,by decide⟩,⟨1626,by decide⟩,⟨2199,by decide⟩] | 4 => ![⟨2200,by decide⟩,⟨1645,by decide⟩,⟨2201,by decide⟩] | 5 => ![⟨2202,by decide⟩,⟨2203,by decide⟩,⟨595,by decide⟩] | 6 => ![⟨2204,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩] | _ => ![⟨1647,by decide⟩,⟨2205,by decide⟩,⟨2197,by decide⟩]

def ntree10RLLLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLLRRLL i else ntree10RLLLLRRLR (i - 8)

def ntree10RLLLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2206,by decide⟩,⟨2207,by decide⟩,⟨2197,by decide⟩] | 1 => ![⟨2208,by decide⟩,⟨1648,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨1661,by decide⟩,⟨2209,by decide⟩] | 3 => ![⟨580,by decide⟩,⟨2210,by decide⟩,⟨1661,by decide⟩] | 4 => ![⟨641,by decide⟩,⟨1661,by decide⟩,⟨1661,by decide⟩] | 5 => ![⟨643,by decide⟩,⟨2210,by decide⟩,⟨2209,by decide⟩] | 6 => ![⟨2211,by decide⟩,⟨2077,by decide⟩,⟨2077,by decide⟩] | _ => ![⟨2212,by decide⟩,⟨31,by decide⟩,⟨2213,by decide⟩]

def ntree10RLLLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2214,by decide⟩,⟨2202,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨2206,by decide⟩,⟨2206,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨2215,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨2216,by decide⟩,⟨2206,by decide⟩,⟨1664,by decide⟩] | 4 => ![⟨646,by decide⟩,⟨2217,by decide⟩,⟨646,by decide⟩] | 5 => ![⟨648,by decide⟩,⟨2218,by decide⟩,⟨2219,by decide⟩] | 6 => ![⟨2220,by decide⟩,⟨2217,by decide⟩,⟨2220,by decide⟩] | _ => ![⟨2221,by decide⟩,⟨2218,by decide⟩,⟨2222,by decide⟩]

def ntree10RLLLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLLRRRL i else ntree10RLLLLRRRR (i - 8)

def ntree10RLLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLLLRRL i else ntree10RLLLLRRR (i - 16)

def ntree10RLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLLLRL i else ntree10RLLLLRR (i - 31)

def ntree10RLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLLLLL i else ntree10RLLLLR (i - 63)

def ntree10RLLLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2211,by decide⟩,⟨1626,by decide⟩,⟨660,by decide⟩] | 1 => ![⟨2212,by decide⟩,⟨1645,by decide⟩,⟨2223,by decide⟩] | 2 => ![⟨2214,by decide⟩,⟨2203,by decide⟩,⟨655,by decide⟩] | 3 => ![⟨668,by decide⟩,⟨2224,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨2225,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2226,by decide⟩,⟨2224,by decide⟩,⟨51,by decide⟩] | _ => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨2227,by decide⟩]

def ntree10RLLLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2228,by decide⟩,⟨1625,by decide⟩,⟨2227,by decide⟩] | 1 => ![⟨2229,by decide⟩,⟨1626,by decide⟩,⟨2230,by decide⟩] | 2 => ![⟨675,by decide⟩,⟨2231,by decide⟩,⟨1699,by decide⟩] | 3 => ![⟨675,by decide⟩,⟨2232,by decide⟩,⟨3,by decide⟩] | 4 => ![⟨679,by decide⟩,⟨2233,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨681,by decide⟩,⟨2234,by decide⟩,⟨2235,by decide⟩] | 6 => ![⟨685,by decide⟩,⟨685,by decide⟩,⟨2236,by decide⟩] | _ => ![⟨707,by decide⟩,⟨1715,by decide⟩,⟨1715,by decide⟩]

def ntree10RLLLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLLRLLLL i else ntree10RLLLRLLLR (i - 7)

def ntree10RLLLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨685,by decide⟩,⟨2237,by decide⟩,⟨1715,by decide⟩] | 1 => ![⟨2238,by decide⟩,⟨2239,by decide⟩,⟨2240,by decide⟩] | 2 => ![⟨685,by decide⟩,⟨2239,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨615,by decide⟩,⟨2241,by decide⟩,⟨615,by decide⟩] | 4 => ![⟨2242,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨2243,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2244,by decide⟩] | _ => ![⟨1635,by decide⟩,⟨2245,by decide⟩,⟨1635,by decide⟩]

def ntree10RLLLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨2246,by decide⟩,⟨1637,by decide⟩] | 1 => ![⟨2247,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨2248,by decide⟩,⟨2248,by decide⟩,⟨2230,by decide⟩] | 3 => ![⟨2249,by decide⟩,⟨1712,by decide⟩,⟨1712,by decide⟩] | 4 => ![⟨2248,by decide⟩,⟨2250,by decide⟩,⟨1712,by decide⟩] | 5 => ![⟨2251,by decide⟩,⟨2252,by decide⟩,⟨2253,by decide⟩] | 6 => ![⟨2248,by decide⟩,⟨2252,by decide⟩,⟨15,by decide⟩] | _ => ![⟨2254,by decide⟩,⟨2254,by decide⟩,⟨1637,by decide⟩]

def ntree10RLLLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLRLLRL i else ntree10RLLLRLLRR (i - 8)

def ntree10RLLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLLRLLL i else ntree10RLLLRLLR (i - 15)

def ntree10RLLLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2254,by decide⟩,⟨2255,by decide⟩,⟨1730,by decide⟩] | 1 => ![⟨2254,by decide⟩,⟨2256,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨2257,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨1743,by decide⟩,⟨2258,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨1745,by decide⟩,⟨2259,by decide⟩] | 5 => ![⟨675,by decide⟩,⟨2260,by decide⟩,⟨1743,by decide⟩] | 6 => ![⟨3,by decide⟩,⟨2261,by decide⟩,⟨2261,by decide⟩] | _ => ![⟨679,by decide⟩,⟨2262,by decide⟩,⟨1745,by decide⟩]

def ntree10RLLLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨2263,by decide⟩,⟨2263,by decide⟩] | 1 => ![⟨717,by decide⟩,⟨2264,by decide⟩,⟨2265,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2266,by decide⟩,⟨2266,by decide⟩] | 3 => ![⟨3,by decide⟩,⟨2267,by decide⟩,⟨2267,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨2268,by decide⟩,⟨2269,by decide⟩] | 5 => ![⟨1635,by decide⟩,⟨2270,by decide⟩,⟨2270,by decide⟩] | 6 => ![⟨1637,by decide⟩,⟨2271,by decide⟩,⟨2271,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨2272,by decide⟩,⟨2272,by decide⟩]

def ntree10RLLLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLRLRLL i else ntree10RLLLRLRLR (i - 8)

def ntree10RLLLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2273,by decide⟩,⟨2274,by decide⟩,⟨2259,by decide⟩] | 1 => ![⟨2273,by decide⟩,⟨2248,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2275,by decide⟩,⟨2275,by decide⟩] | 3 => ![⟨2276,by decide⟩,⟨2248,by decide⟩,⟨2213,by decide⟩] | 4 => ![⟨2254,by decide⟩,⟨2277,by decide⟩,⟨1754,by decide⟩] | 5 => ![⟨1637,by decide⟩,⟨1754,by decide⟩,⟨1754,by decide⟩] | 6 => ![⟨2278,by decide⟩,⟨2254,by decide⟩,⟨1664,by decide⟩] | _ => ![⟨737,by decide⟩,⟨2279,by decide⟩,⟨1699,by decide⟩]

def ntree10RLLLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨737,by decide⟩,⟨2280,by decide⟩,⟨2261,by decide⟩] | 1 => ![⟨740,by decide⟩,⟨2281,by decide⟩,⟨2282,by decide⟩] | 2 => ![⟨749,by decide⟩,⟨2283,by decide⟩,⟨1767,by decide⟩] | 3 => ![⟨2284,by decide⟩,⟨2285,by decide⟩,⟨2286,by decide⟩] | 4 => ![⟨2287,by decide⟩,⟨2288,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2289,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨2273,by decide⟩,⟨2250,by decide⟩,⟨1764,by decide⟩] | _ => ![⟨2276,by decide⟩,⟨2252,by decide⟩,⟨2290,by decide⟩]

def ntree10RLLLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLRLRRL i else ntree10RLLLRLRRR (i - 8)

def ntree10RLLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLLRLRL i else ntree10RLLLRLRR (i - 16)

def ntree10RLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLLRLL i else ntree10RLLLRLR (i - 31)

def ntree10RLLLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2248,by decide⟩,⟨2291,by decide⟩,⟨148,by decide⟩] | 1 => ![⟨747,by decide⟩,⟨2292,by decide⟩,⟨1712,by decide⟩] | 2 => ![⟨747,by decide⟩,⟨2285,by decide⟩,⟨2266,by decide⟩] | 3 => ![⟨2293,by decide⟩,⟨1781,by decide⟩,⟨148,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨1793,by decide⟩,⟨2230,by decide⟩] | 5 => ![⟨2229,by decide⟩,⟨1794,by decide⟩,⟨2294,by decide⟩] | _ => ![⟨685,by decide⟩,⟨2295,by decide⟩,⟨2296,by decide⟩]

def ntree10RLLLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨752,by decide⟩,⟨2297,by decide⟩,⟨2298,by decide⟩] | 1 => ![⟨752,by decide⟩,⟨2299,by decide⟩,⟨2300,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨1794,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2301,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨2244,by decide⟩] | 5 => ![⟨1802,by decide⟩,⟨2302,by decide⟩,⟨2302,by decide⟩] | 6 => ![⟨1804,by decide⟩,⟨2303,by decide⟩,⟨2302,by decide⟩] | _ => ![⟨2304,by decide⟩,⟨595,by decide⟩,⟨2305,by decide⟩]

def ntree10RLLLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLLRRLLL i else ntree10RLLLRRLLR (i - 7)

def ntree10RLLLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2304,by decide⟩,⟨1712,by decide⟩,⟨2306,by decide⟩] | 1 => ![⟨2307,by decide⟩,⟨2308,by decide⟩,⟨2308,by decide⟩] | 2 => ![⟨2307,by decide⟩,⟨2309,by decide⟩,⟨2307,by decide⟩] | 3 => ![⟨2310,by decide⟩,⟨2203,by decide⟩,⟨2305,by decide⟩] | 4 => ![⟨2311,by decide⟩,⟨1709,by decide⟩,⟨2306,by decide⟩] | 5 => ![⟨2312,by decide⟩,⟨2313,by decide⟩,⟨2308,by decide⟩] | 6 => ![⟨2314,by decide⟩,⟨2315,by decide⟩,⟨2308,by decide⟩] | _ => ![⟨2314,by decide⟩,⟨2316,by decide⟩,⟨2317,by decide⟩]

def ntree10RLLLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1661,by decide⟩,⟨2318,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨1821,by decide⟩,⟨2319,by decide⟩] | 2 => ![⟨685,by decide⟩,⟨2320,by decide⟩,⟨1745,by decide⟩] | 3 => ![⟨685,by decide⟩,⟨2321,by decide⟩,⟨1661,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨2322,by decide⟩,⟨2266,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1821,by decide⟩,⟨1821,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨2323,by decide⟩,⟨15,by decide⟩] | _ => ![⟨13,by decide⟩,⟨2324,by decide⟩,⟨2268,by decide⟩]

def ntree10RLLLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLRRLRL i else ntree10RLLLRRLRR (i - 8)

def ntree10RLLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLLRRLL i else ntree10RLLLRRLR (i - 15)

def ntree10RLLLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨2323,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨50,by decide⟩,⟨2324,by decide⟩,⟨2269,by decide⟩] | 2 => ![⟨1802,by decide⟩,⟨2325,by decide⟩,⟨1802,by decide⟩] | 3 => ![⟨1804,by decide⟩,⟨2326,by decide⟩,⟨2327,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨2328,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2329,by decide⟩,⟨2307,by decide⟩,⟨2329,by decide⟩] | 6 => ![⟨2211,by decide⟩,⟨2330,by decide⟩,⟨2230,by decide⟩] | _ => ![⟨15,by decide⟩,⟨2331,by decide⟩,⟨15,by decide⟩]

def ntree10RLLLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2332,by decide⟩,⟨2307,by decide⟩,⟨2307,by decide⟩] | 1 => ![⟨2214,by decide⟩,⟨2333,by decide⟩,⟨2259,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨2331,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨2334,by decide⟩,⟨2312,by decide⟩,⟨2329,by decide⟩] | 4 => ![⟨2314,by decide⟩,⟨2314,by decide⟩,⟨2307,by decide⟩] | 5 => ![⟨685,by decide⟩,⟨2335,by decide⟩,⟨72,by decide⟩] | 6 => ![⟨1806,by decide⟩,⟨2336,by decide⟩,⟨2266,by decide⟩] | _ => ![⟨2202,by decide⟩,⟨2333,by decide⟩,⟨1745,by decide⟩]

def ntree10RLLLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLRRRLL i else ntree10RLLLRRRLR (i - 8)

def ntree10RLLLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2312,by decide⟩,⟨2312,by decide⟩,⟨2307,by decide⟩] | 1 => ![⟨2337,by decide⟩,⟨685,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨794,by decide⟩,⟨2338,by decide⟩,⟨794,by decide⟩] | 3 => ![⟨796,by decide⟩,⟨2339,by decide⟩,⟨2340,by decide⟩] | 4 => ![⟨794,by decide⟩,⟨2341,by decide⟩,⟨794,by decide⟩] | 5 => ![⟨796,by decide⟩,⟨2342,by decide⟩,⟨2343,by decide⟩] | 6 => ![⟨2344,by decide⟩,⟨2328,by decide⟩,⟨660,by decide⟩] | _ => ![⟨2329,by decide⟩,⟨2308,by decide⟩,⟨2345,by decide⟩]

def ntree10RLLLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2332,by decide⟩,⟨2309,by decide⟩,⟨2346,by decide⟩] | 1 => ![⟨2334,by decide⟩,⟨2313,by decide⟩,⟨2345,by decide⟩] | 2 => ![⟨2347,by decide⟩,⟨2347,by decide⟩,⟨2347,by decide⟩] | 3 => ![⟨2347,by decide⟩,⟨2348,by decide⟩,⟨2347,by decide⟩] | 4 => ![⟨2349,by decide⟩,⟨2350,by decide⟩,⟨2349,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨2347,by decide⟩,⟨2351,by decide⟩,⟨2351,by decide⟩] | _ => ![⟨2352,by decide⟩,⟨2353,by decide⟩,⟨2354,by decide⟩]

def ntree10RLLLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLLRRRRL i else ntree10RLLLRRRRR (i - 8)

def ntree10RLLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLLRRRL i else ntree10RLLLRRRR (i - 16)

def ntree10RLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLLRRL i else ntree10RLLLRRR (i - 31)

def ntree10RLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLLLRL i else ntree10RLLLRR (i - 63)

def ntree10RLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RLLLL i else ntree10RLLLR (i - 126)

def ntree10RLLRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2355,by decide⟩,⟨2356,by decide⟩,⟨2356,by decide⟩] | 1 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨2357,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨2358,by decide⟩,⟨2357,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨2347,by decide⟩,⟨2359,by decide⟩,⟨2359,by decide⟩] | 5 => ![⟨2349,by decide⟩,⟨2360,by decide⟩,⟨2360,by decide⟩] | _ => ![⟨2349,by decide⟩,⟨2349,by decide⟩,⟨2349,by decide⟩]

def ntree10RLLRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2361,by decide⟩,⟨2362,by decide⟩,⟨2362,by decide⟩] | 1 => ![⟨2361,by decide⟩,⟨2361,by decide⟩,⟨2361,by decide⟩] | 2 => ![⟨2363,by decide⟩,⟨2364,by decide⟩,⟨2364,by decide⟩] | 3 => ![⟨2363,by decide⟩,⟨2363,by decide⟩,⟨2363,by decide⟩] | 4 => ![⟨2365,by decide⟩,⟨2366,by decide⟩,⟨2366,by decide⟩] | 5 => ![⟨2365,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | 6 => ![⟨2355,by decide⟩,⟨2367,by decide⟩,⟨2367,by decide⟩] | _ => ![⟨2368,by decide⟩,⟨2357,by decide⟩,⟨2355,by decide⟩]

def ntree10RLLRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLRLLLLL i else ntree10RLLRLLLLR (i - 7)

def ntree10RLLRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2365,by decide⟩,⟨2369,by decide⟩,⟨2365,by decide⟩] | 1 => ![⟨2370,by decide⟩,⟨2369,by decide⟩,⟨2365,by decide⟩] | 2 => ![⟨2371,by decide⟩,⟨2347,by decide⟩,⟨2371,by decide⟩] | 3 => ![⟨2372,by decide⟩,⟨2349,by decide⟩,⟨2372,by decide⟩] | 4 => ![⟨2352,by decide⟩,⟨2352,by decide⟩,⟨2349,by decide⟩] | 5 => ![⟨2373,by decide⟩,⟨2355,by decide⟩,⟨2373,by decide⟩] | 6 => ![⟨2374,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨2375,by decide⟩,⟨2365,by decide⟩,⟨2375,by decide⟩]

def ntree10RLLRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2376,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨2211,by decide⟩,⟨845,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨2377,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨2378,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | 4 => ![⟨2215,by decide⟩,⟨2377,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨2372,by decide⟩,⟨2350,by decide⟩,⟨2372,by decide⟩] | 6 => ![⟨2379,by decide⟩,⟨2380,by decide⟩,⟨2349,by decide⟩] | _ => ![⟨2371,by decide⟩,⟨2359,by decide⟩,⟨2381,by decide⟩]

def ntree10RLLRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRLLLRL i else ntree10RLLRLLLRR (i - 8)

def ntree10RLLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLRLLLL i else ntree10RLLRLLLR (i - 15)

def ntree10RLLRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2347,by decide⟩,⟨2347,by decide⟩,⟨2382,by decide⟩] | 1 => ![⟨2372,by decide⟩,⟨2360,by decide⟩,⟨2383,by decide⟩] | 2 => ![⟨2373,by decide⟩,⟨2367,by decide⟩,⟨2384,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2385,by decide⟩] | 4 => ![⟨2376,by decide⟩,⟨2357,by decide⟩,⟨2385,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2386,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨2387,by decide⟩,⟨2386,by decide⟩,⟨660,by decide⟩] | _ => ![⟨2388,by decide⟩,⟨2388,by decide⟩,⟨2347,by decide⟩]

def ntree10RLLRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2388,by decide⟩,⟨2389,by decide⟩,⟨2347,by decide⟩] | 1 => ![⟨2390,by decide⟩,⟨2391,by decide⟩,⟨2349,by decide⟩] | 2 => ![⟨2392,by decide⟩,⟨2392,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨2393,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨2394,by decide⟩,⟨685,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2392,by decide⟩,⟨2395,by decide⟩,⟨2355,by decide⟩] | 6 => ![⟨2349,by decide⟩,⟨2349,by decide⟩,⟨2396,by decide⟩] | _ => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2397,by decide⟩]

def ntree10RLLRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRLLRLL i else ntree10RLLRLLRLR (i - 8)

def ntree10RLLRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2398,by decide⟩,⟨2398,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨2399,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 2 => ![⟨2400,by decide⟩,⟨2248,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2398,by decide⟩,⟨2401,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨300,by decide⟩,⟨1626,by decide⟩,⟨2397,by decide⟩] | 5 => ![⟨2402,by decide⟩,⟨2402,by decide⟩,⟨2365,by decide⟩] | 6 => ![⟨2402,by decide⟩,⟨2403,by decide⟩,⟨2365,by decide⟩] | _ => ![⟨2404,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩]

def ntree10RLLRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2405,by decide⟩,⟨2254,by decide⟩,⟨1637,by decide⟩] | 1 => ![⟨2347,by decide⟩,⟨2406,by decide⟩,⟨2406,by decide⟩] | 2 => ![⟨2390,by decide⟩,⟨2390,by decide⟩,⟨2349,by decide⟩] | 3 => ![⟨2349,by decide⟩,⟨2407,by decide⟩,⟨2407,by decide⟩] | 4 => ![⟨2408,by decide⟩,⟨2392,by decide⟩,⟨2373,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨2409,by decide⟩,⟨2409,by decide⟩] | 6 => ![⟨2347,by decide⟩,⟨2410,by decide⟩,⟨2410,by decide⟩] | _ => ![⟨2372,by decide⟩,⟨2411,by decide⟩,⟨2412,by decide⟩]

def ntree10RLLRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRLLRRL i else ntree10RLLRLLRRR (i - 8)

def ntree10RLLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLRLLRL i else ntree10RLLRLLRR (i - 16)

def ntree10RLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLRLLL i else ntree10RLLRLLR (i - 31)

def ntree10RLLRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2361,by decide⟩,⟨2413,by decide⟩,⟨2413,by decide⟩] | 1 => ![⟨2363,by decide⟩,⟨2414,by decide⟩,⟨2414,by decide⟩] | 2 => ![⟨2365,by decide⟩,⟨2415,by decide⟩,⟨2415,by decide⟩] | 3 => ![⟨2416,by decide⟩,⟨2398,by decide⟩,⟨2373,by decide⟩] | 4 => ![⟨2355,by decide⟩,⟨2417,by decide⟩,⟨2417,by decide⟩] | 5 => ![⟨2248,by decide⟩,⟨2418,by decide⟩,⟨1948,by decide⟩] | _ => ![⟨2254,by decide⟩,⟨2419,by decide⟩,⟨1954,by decide⟩]

def ntree10RLLRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2420,by decide⟩,⟨2402,by decide⟩,⟨2375,by decide⟩] | 1 => ![⟨2421,by decide⟩,⟨2421,by decide⟩,⟨2347,by decide⟩] | 2 => ![⟨2421,by decide⟩,⟨2422,by decide⟩,⟨2406,by decide⟩] | 3 => ![⟨2423,by decide⟩,⟨2424,by decide⟩,⟨2407,by decide⟩] | 4 => ![⟨2425,by decide⟩,⟨2426,by decide⟩,⟨2373,by decide⟩] | 5 => ![⟨2426,by decide⟩,⟨2427,by decide⟩,⟨2409,by decide⟩] | 6 => ![⟨2426,by decide⟩,⟨2426,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨2428,by decide⟩,⟨2428,by decide⟩,⟨15,by decide⟩]

def ntree10RLLRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLRLRLLL i else ntree10RLLRLRLLR (i - 7)

def ntree10RLLRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2428,by decide⟩,⟨2429,by decide⟩,⟨308,by decide⟩] | 1 => ![⟨2430,by decide⟩,⟨2428,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨2431,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1793,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨2432,by decide⟩,⟨1626,by decide⟩,⟨2433,by decide⟩] | 5 => ![⟨2392,by decide⟩,⟨2434,by decide⟩,⟨2435,by decide⟩] | 6 => ![⟨2013,by decide⟩,⟨1983,by decide⟩,⟨2003,by decide⟩] | _ => ![⟨2436,by decide⟩,⟨15,by decide⟩,⟨2437,by decide⟩]

def ntree10RLLRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2438,by decide⟩,⟨2439,by decide⟩,⟨2439,by decide⟩] | 1 => ![⟨2438,by decide⟩,⟨2438,by decide⟩,⟨2438,by decide⟩] | 2 => ![⟨2440,by decide⟩,⟨2441,by decide⟩,⟨2441,by decide⟩] | 3 => ![⟨2440,by decide⟩,⟨2440,by decide⟩,⟨2440,by decide⟩] | 4 => ![⟨2442,by decide⟩,⟨15,by decide⟩,⟨930,by decide⟩] | 5 => ![⟨2392,by decide⟩,⟨2443,by decide⟩,⟨2367,by decide⟩] | 6 => ![⟨2355,by decide⟩,⟨2444,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨2445,by decide⟩,⟨2446,by decide⟩,⟨595,by decide⟩]

def ntree10RLLRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRLRLRL i else ntree10RLLRLRLRR (i - 8)

def ntree10RLLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLRLRLL i else ntree10RLLRLRLR (i - 15)

def ntree10RLLRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨2447,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨2393,by decide⟩,⟨2444,by decide⟩,⟨2355,by decide⟩] | 2 => ![⟨2394,by decide⟩,⟨768,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨2448,by decide⟩,⟨2239,by decide⟩,⟨930,by decide⟩] | 4 => ![⟨2449,by decide⟩,⟨2447,by decide⟩,⟨288,by decide⟩] | 5 => ![⟨2450,by decide⟩,⟨2203,by decide⟩,⟨932,by decide⟩] | 6 => ![⟨2013,by decide⟩,⟨2013,by decide⟩,⟨15,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2451,by decide⟩,⟨2451,by decide⟩]

def ntree10RLLRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2438,by decide⟩,⟨2452,by decide⟩,⟨2452,by decide⟩] | 1 => ![⟨2440,by decide⟩,⟨2453,by decide⟩,⟨2453,by decide⟩] | 2 => ![⟨685,by decide⟩,⟨2454,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2445,by decide⟩,⟨2445,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨2202,by decide⟩,⟨2455,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨717,by decide⟩,⟨2454,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨2456,by decide⟩,⟨2392,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨2337,by decide⟩,⟨896,by decide⟩,⟨308,by decide⟩]

def ntree10RLLRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRLRRLL i else ntree10RLLRLRRLR (i - 8)

def ntree10RLLRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2457,by decide⟩,⟨2445,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨2214,by decide⟩,⟨2455,by decide⟩,⟨311,by decide⟩] | 2 => ![⟨2373,by decide⟩,⟨2431,by decide⟩,⟨2373,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2357,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨2426,by decide⟩,⟨2458,by decide⟩,⟨2355,by decide⟩] | 5 => ![⟨1964,by decide⟩,⟨2459,by decide⟩,⟨595,by decide⟩] | 6 => ![⟨2460,by decide⟩,⟨2461,by decide⟩,⟨979,by decide⟩] | _ => ![⟨1967,by decide⟩,⟨2459,by decide⟩,⟨655,by decide⟩]

def ntree10RLLRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2462,by decide⟩,⟨1965,by decide⟩,⟨981,by decide⟩] | 1 => ![⟨2463,by decide⟩,⟨2461,by decide⟩,⟨983,by decide⟩] | 2 => ![⟨2464,by decide⟩,⟨2464,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2465,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨2464,by decide⟩,⟨2466,by decide⟩,⟨2467,by decide⟩] | 5 => ![⟨1876,by decide⟩,⟨2468,by decide⟩,⟨2186,by decide⟩] | 6 => ![⟨2469,by decide⟩,⟨2469,by decide⟩,⟨2365,by decide⟩] | _ => ![⟨2470,by decide⟩,⟨2355,by decide⟩,⟨2470,by decide⟩]

def ntree10RLLRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRLRRRL i else ntree10RLLRLRRRR (i - 8)

def ntree10RLLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLRLRRL i else ntree10RLLRLRRR (i - 16)

def ntree10RLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLRLRL i else ntree10RLLRLRR (i - 31)

def ntree10RLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLLRLL i else ntree10RLLRLR (i - 63)

def ntree10RLLRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2470,by decide⟩,⟨2467,by decide⟩,⟨2471,by decide⟩] | 1 => ![⟨2365,by decide⟩,⟨2472,by decide⟩,⟨2472,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨2473,by decide⟩,⟨2473,by decide⟩] | 3 => ![⟨2474,by decide⟩,⟨2464,by decide⟩,⟨2373,by decide⟩] | 4 => ![⟨2355,by decide⟩,⟨2475,by decide⟩,⟨2475,by decide⟩] | 5 => ![⟨1876,by decide⟩,⟨2476,by decide⟩,⟨1028,by decide⟩] | _ => ![⟨2477,by decide⟩,⟨2469,by decide⟩,⟨2375,by decide⟩]

def ntree10RLLRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2213,by decide⟩,⟨1028,by decide⟩,⟨2478,by decide⟩] | 1 => ![⟨2365,by decide⟩,⟨2479,by decide⟩,⟨2479,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨2480,by decide⟩,⟨2480,by decide⟩] | 3 => ![⟨2088,by decide⟩,⟨2481,by decide⟩,⟨2088,by decide⟩] | 4 => ![⟨2089,by decide⟩,⟨2482,by decide⟩,⟨2483,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨2467,by decide⟩,⟨2467,by decide⟩] | 6 => ![⟨2213,by decide⟩,⟨1646,by decide⟩,⟨2223,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2484,by decide⟩,⟨2484,by decide⟩]

def ntree10RLLRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLRRLLLL i else ntree10RLLRRLLLR (i - 7)

def ntree10RLLRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨2485,by decide⟩,⟨2485,by decide⟩] | 1 => ![⟨2088,by decide⟩,⟨2486,by decide⟩,⟨2486,by decide⟩] | 2 => ![⟨2088,by decide⟩,⟨2483,by decide⟩,⟨2483,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2487,by decide⟩] | 4 => ![⟨2355,by decide⟩,⟨2488,by decide⟩,⟨2488,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1712,by decide⟩,⟨2489,by decide⟩] | 6 => ![⟨2490,by decide⟩,⟨2465,by decide⟩,⟨2487,by decide⟩] | _ => ![⟨2491,by decide⟩,⟨2059,by decide⟩,⟨1056,by decide⟩]

def ntree10RLLRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2492,by decide⟩,⟨805,by decide⟩,⟨2230,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨2493,by decide⟩,⟨1712,by decide⟩] | 2 => ![⟨2494,by decide⟩,⟨1712,by decide⟩,⟨1712,by decide⟩] | 3 => ![⟨2495,by decide⟩,⟨2495,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨679,by decide⟩,⟨2496,by decide⟩,⟨1712,by decide⟩] | 5 => ![⟨2495,by decide⟩,⟨2497,by decide⟩,⟨2355,by decide⟩] | 6 => ![⟨679,by decide⟩,⟨2498,by decide⟩,⟨15,by decide⟩] | _ => ![⟨15,by decide⟩,⟨2499,by decide⟩,⟨15,by decide⟩]

def ntree10RLLRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRRLLRL i else ntree10RLLRRLLRR (i - 8)

def ntree10RLLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLRRLLL i else ntree10RLLRRLLR (i - 15)

def ntree10RLLRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2500,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨2501,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨2502,by decide⟩,⟨2499,by decide⟩,⟨288,by decide⟩] | 3 => ![⟨2503,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨2504,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2505,by decide⟩,⟨692,by decide⟩,⟨2397,by decide⟩] | 6 => ![⟨2506,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | _ => ![⟨2507,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩]

def ntree10RLLRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2508,by decide⟩,⟨2246,by decide⟩,⟨1930,by decide⟩] | 1 => ![⟨2470,by decide⟩,⟨2355,by decide⟩,⟨2509,by decide⟩] | 2 => ![⟨429,by decide⟩,⟨15,by decide⟩,⟨2510,by decide⟩] | 3 => ![⟨429,by decide⟩,⟨1712,by decide⟩,⟨2511,by decide⟩] | 4 => ![⟨2365,by decide⟩,⟨2512,by decide⟩,⟨2512,by decide⟩] | 5 => ![⟨2373,by decide⟩,⟨2513,by decide⟩,⟨2514,by decide⟩] | 6 => ![⟨2495,by decide⟩,⟨2515,by decide⟩,⟨2513,by decide⟩] | _ => ![⟨2213,by decide⟩,⟨1948,by decide⟩,⟨2516,by decide⟩]

def ntree10RLLRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRRLRLL i else ntree10RLLRRLRLR (i - 8)

def ntree10RLLRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2365,by decide⟩,⟨2517,by decide⟩,⟨2517,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨2518,by decide⟩,⟨2518,by decide⟩] | 2 => ![⟨2373,by decide⟩,⟨2488,by decide⟩,⟨2519,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2465,by decide⟩,⟨2520,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨2493,by decide⟩,⟨1764,by decide⟩] | 5 => ![⟨2521,by decide⟩,⟨2522,by decide⟩,⟨2488,by decide⟩] | 6 => ![⟨2521,by decide⟩,⟨2523,by decide⟩,⟨2409,by decide⟩] | _ => ![⟨2524,by decide⟩,⟨2525,by decide⟩,⟨2145,by decide⟩]

def ntree10RLLRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2526,by decide⟩,⟨1112,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨2527,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 2 => ![⟨2528,by decide⟩,⟨1112,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2520,by decide⟩] | 4 => ![⟨2213,by decide⟩,⟨15,by decide⟩,⟨2290,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨2529,by decide⟩,⟨2529,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨2530,by decide⟩,⟨2530,by decide⟩] | _ => ![⟨2088,by decide⟩,⟨2153,by decide⟩,⟨2153,by decide⟩]

def ntree10RLLRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRRLRRL i else ntree10RLLRRLRRR (i - 8)

def ntree10RLLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLRRLRL i else ntree10RLLRRLRR (i - 16)

def ntree10RLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLRRLL i else ntree10RLLRRLR (i - 31)

def ntree10RLLRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2355,by decide⟩,⟨2431,by decide⟩,⟨2487,by decide⟩] | 1 => ![⟨2464,by decide⟩,⟨2531,by decide⟩,⟨2488,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨1784,by decide⟩,⟨2489,by decide⟩] | 3 => ![⟨1876,by decide⟩,⟨2158,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨2532,by decide⟩,⟨13,by decide⟩,⟨930,by decide⟩] | 5 => ![⟨2533,by decide⟩,⟨2367,by decide⟩,⟨2534,by decide⟩] | _ => ![⟨2533,by decide⟩,⟨2488,by decide⟩,⟨2535,by decide⟩]

def ntree10RLLRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2536,by decide⟩,⟨2308,by decide⟩,⟨2537,by decide⟩] | 1 => ![⟨2307,by decide⟩,⟨2307,by decide⟩,⟨2538,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨2539,by decide⟩,⟨2539,by decide⟩] | 3 => ![⟨2307,by decide⟩,⟨2317,by decide⟩,⟨2317,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨2540,by decide⟩,⟨2540,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨2513,by decide⟩,⟨2513,by decide⟩] | 6 => ![⟨2355,by decide⟩,⟨2541,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨2464,by decide⟩,⟨2542,by decide⟩,⟨2409,by decide⟩]

def ntree10RLLRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLLRRRLLL i else ntree10RLLRRRLLR (i - 7)

def ntree10RLLRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1876,by decide⟩,⟨2171,by decide⟩,⟨1745,by decide⟩] | 1 => ![⟨2329,by decide⟩,⟨2543,by decide⟩,⟨2544,by decide⟩] | 2 => ![⟨2307,by decide⟩,⟨2543,by decide⟩,⟨2543,by decide⟩] | 3 => ![⟨2307,by decide⟩,⟨2545,by decide⟩,⟨2545,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨2546,by decide⟩,⟨2546,by decide⟩] | 5 => ![⟨2474,by decide⟩,⟨2531,by decide⟩,⟨2519,by decide⟩] | 6 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨2464,by decide⟩,⟨2464,by decide⟩,⟨2520,by decide⟩]

def ntree10RLLRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2088,by decide⟩,⟨2176,by decide⟩,⟨2088,by decide⟩] | 1 => ![⟨2547,by decide⟩,⟨2541,by decide⟩,⟨2385,by decide⟩] | 2 => ![⟨2307,by decide⟩,⟨2307,by decide⟩,⟨2346,by decide⟩] | 3 => ![⟨2548,by decide⟩,⟨2549,by decide⟩,⟨2549,by decide⟩] | 4 => ![⟨1167,by decide⟩,⟨1626,by decide⟩,⟨1167,by decide⟩] | 5 => ![⟨1168,by decide⟩,⟨1623,by decide⟩,⟨2550,by decide⟩] | 6 => ![⟨9,by decide⟩,⟨2551,by decide⟩,⟨2551,by decide⟩] | _ => ![⟨1165,by decide⟩,⟨2552,by decide⟩,⟨2551,by decide⟩]

def ntree10RLLRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRRRLRL i else ntree10RLLRRRLRR (i - 8)

def ntree10RLLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLLRRRLL i else ntree10RLLRRRLR (i - 15)

def ntree10RLLRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2553,by decide⟩,⟨1632,by decide⟩,⟨2553,by decide⟩] | 1 => ![⟨2554,by decide⟩,⟨1633,by decide⟩,⟨2555,by decide⟩] | 2 => ![⟨2554,by decide⟩,⟨13,by decide⟩,⟨2553,by decide⟩] | 3 => ![⟨2556,by decide⟩,⟨2557,by decide⟩,⟨595,by decide⟩] | 4 => ![⟨2558,by decide⟩,⟨1637,by decide⟩,⟨2558,by decide⟩] | 5 => ![⟨2559,by decide⟩,⟨1639,by decide⟩,⟨2558,by decide⟩] | 6 => ![⟨2560,by decide⟩,⟨2561,by decide⟩,⟨2197,by decide⟩] | _ => ![⟨2562,by decide⟩,⟨1619,by decide⟩,⟨2562,by decide⟩]

def ntree10RLLRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2553,by decide⟩,⟨1626,by decide⟩,⟨2553,by decide⟩] | 1 => ![⟨2563,by decide⟩,⟨2564,by decide⟩,⟨1172,by decide⟩] | 2 => ![⟨2558,by decide⟩,⟨1648,by decide⟩,⟨2558,by decide⟩] | 3 => ![⟨1651,by decide⟩,⟨2565,by decide⟩,⟨2565,by decide⟩] | 4 => ![⟨2566,by decide⟩,⟨2567,by decide⟩,⟨2565,by decide⟩] | 5 => ![⟨2568,by decide⟩,⟨15,by decide⟩,⟨2568,by decide⟩] | 6 => ![⟨2569,by decide⟩,⟨13,by decide⟩,⟨2568,by decide⟩] | _ => ![⟨1194,by decide⟩,⟨1661,by decide⟩,⟨1661,by decide⟩]

def ntree10RLLRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRRRRLL i else ntree10RLLRRRRLR (i - 8)

def ntree10RLLRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1165,by decide⟩,⟨2570,by decide⟩,⟨1656,by decide⟩] | 1 => ![⟨582,by decide⟩,⟨2571,by decide⟩,⟨2572,by decide⟩] | 2 => ![⟨2573,by decide⟩,⟨1663,by decide⟩,⟨1663,by decide⟩] | 3 => ![⟨2556,by decide⟩,⟨2574,by decide⟩,⟨1663,by decide⟩] | 4 => ![⟨2575,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨2560,by decide⟩,⟨2576,by decide⟩,⟨1666,by decide⟩] | 6 => ![⟨2213,by decide⟩,⟨1672,by decide⟩,⟨2213,by decide⟩] | _ => ![⟨2563,by decide⟩,⟨2563,by decide⟩,⟨9,by decide⟩]

def ntree10RLLRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2202,by decide⟩,⟨2577,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨2566,by decide⟩,⟨2566,by decide⟩,⟨1651,by decide⟩] | 2 => ![⟨2206,by decide⟩,⟨2578,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2579,by decide⟩] | 4 => ![⟨1194,by decide⟩,⟨1626,by decide⟩,⟨2580,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2581,by decide⟩,⟨2581,by decide⟩] | 6 => ![⟨1214,by decide⟩,⟨2582,by decide⟩,⟨2583,by decide⟩] | _ => ![⟨2553,by decide⟩,⟨1663,by decide⟩,⟨2584,by decide⟩]

def ntree10RLLRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLLRRRRRL i else ntree10RLLRRRRRR (i - 8)

def ntree10RLLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLLRRRRL i else ntree10RLLRRRRR (i - 16)

def ntree10RLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLLRRRL i else ntree10RLLRRRR (i - 31)

def ntree10RLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLLRRL i else ntree10RLLRRR (i - 63)

def ntree10RLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RLLRL i else ntree10RLLRR (i - 126)

def ntree10RLL (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10RLLL i else ntree10RLLR (i - 252)

def ntree10RLRLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2554,by decide⟩,⟨1658,by decide⟩,⟨2584,by decide⟩] | 1 => ![⟨2585,by decide⟩,⟨2586,by decide⟩,⟨2586,by decide⟩] | 2 => ![⟨2587,by decide⟩,⟨2587,by decide⟩,⟨2585,by decide⟩] | 3 => ![⟨2587,by decide⟩,⟨2588,by decide⟩,⟨2586,by decide⟩] | 4 => ![⟨2589,by decide⟩,⟨15,by decide⟩,⟨2553,by decide⟩] | 5 => ![⟨2590,by decide⟩,⟨2591,by decide⟩,⟨2586,by decide⟩] | _ => ![⟨2587,by decide⟩,⟨2592,by decide⟩,⟨2593,by decide⟩]

def ntree10RLRLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2594,by decide⟩,⟨1690,by decide⟩,⟨2594,by decide⟩] | 1 => ![⟨2595,by decide⟩,⟨2596,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨2597,by decide⟩,⟨2598,by decide⟩,⟨595,by decide⟩] | 3 => ![⟨1695,by decide⟩,⟨2599,by decide⟩,⟨2599,by decide⟩] | 4 => ![⟨2600,by decide⟩,⟨2601,by decide⟩,⟨2599,by decide⟩] | 5 => ![⟨2602,by decide⟩,⟨2603,by decide⟩,⟨1695,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨1715,by decide⟩,⟨2604,by decide⟩] | _ => ![⟨685,by decide⟩,⟨685,by decide⟩,⟨1711,by decide⟩]

def ntree10RLRLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRLLLLLL i else ntree10RLRLLLLLR (i - 7)

def ntree10RLRLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1236,by decide⟩,⟨1715,by decide⟩,⟨1715,by decide⟩] | 1 => ![⟨2605,by decide⟩,⟨2237,by decide⟩,⟨2604,by decide⟩] | 2 => ![⟨2606,by decide⟩,⟨2239,by decide⟩,⟨2607,by decide⟩] | 3 => ![⟨1236,by decide⟩,⟨1626,by decide⟩,⟨2608,by decide⟩] | 4 => ![⟨2609,by decide⟩,⟨2241,by decide⟩,⟨2610,by decide⟩] | 5 => ![⟨1229,by decide⟩,⟨2611,by decide⟩,⟨9,by decide⟩] | 6 => ![⟨2612,by decide⟩,⟨2612,by decide⟩,⟨1711,by decide⟩] | _ => ![⟨2613,by decide⟩,⟨1919,by decide⟩,⟨1919,by decide⟩]

def ntree10RLRLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2613,by decide⟩,⟨692,by decide⟩,⟨1711,by decide⟩] | 1 => ![⟨2614,by decide⟩,⟨2615,by decide⟩,⟨2616,by decide⟩] | 2 => ![⟨2553,by decide⟩,⟨15,by decide⟩,⟨2616,by decide⟩] | 3 => ![⟨2613,by decide⟩,⟨1632,by decide⟩,⟨2617,by decide⟩] | 4 => ![⟨2618,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨2618,by decide⟩,⟨2246,by decide⟩,⟨1726,by decide⟩] | 6 => ![⟨2558,by decide⟩,⟨1637,by decide⟩,⟨2619,by decide⟩] | _ => ![⟨2620,by decide⟩,⟨2620,by decide⟩,⟨1637,by decide⟩]

def ntree10RLRLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLLLLRL i else ntree10RLRLLLLRR (i - 8)

def ntree10RLRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRLLLLL i else ntree10RLRLLLLR (i - 15)

def ntree10RLRLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2620,by decide⟩,⟨2621,by decide⟩,⟨1637,by decide⟩] | 1 => ![⟨2622,by decide⟩,⟨2622,by decide⟩,⟨1705,by decide⟩] | 2 => ![⟨2248,by decide⟩,⟨2248,by decide⟩,⟨1711,by decide⟩] | 3 => ![⟨2623,by decide⟩,⟨2624,by decide⟩,⟨2625,by decide⟩] | 4 => ![⟨2626,by decide⟩,⟨2252,by decide⟩,⟨2616,by decide⟩] | 5 => ![⟨2254,by decide⟩,⟨2254,by decide⟩,⟨1726,by decide⟩] | 6 => ![⟨2627,by decide⟩,⟨2256,by decide⟩,⟨2619,by decide⟩] | _ => ![⟨2628,by decide⟩,⟨2628,by decide⟩,⟨1651,by decide⟩]

def ntree10RLRLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2628,by decide⟩,⟨2629,by decide⟩,⟨1651,by decide⟩] | 1 => ![⟨1177,by decide⟩,⟨1747,by decide⟩,⟨2630,by decide⟩] | 2 => ![⟨1180,by decide⟩,⟨1749,by decide⟩,⟨2631,by decide⟩] | 3 => ![⟨2632,by decide⟩,⟨2264,by decide⟩,⟨2633,by decide⟩] | 4 => ![⟨2634,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2635,by decide⟩] | 6 => ![⟨615,by decide⟩,⟨615,by decide⟩,⟨2636,by decide⟩] | _ => ![⟨1229,by decide⟩,⟨2637,by decide⟩,⟨1747,by decide⟩]

def ntree10RLRLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLLLRLL i else ntree10RLRLLLRLR (i - 8)

def ntree10RLRLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨685,by decide⟩,⟨2638,by decide⟩,⟨1749,by decide⟩] | 1 => ![⟨9,by decide⟩,⟨2639,by decide⟩,⟨2639,by decide⟩] | 2 => ![⟨685,by decide⟩,⟨2640,by decide⟩,⟨2641,by decide⟩] | 3 => ![⟨615,by decide⟩,⟨2642,by decide⟩,⟨615,by decide⟩] | 4 => ![⟨2643,by decide⟩,⟨2644,by decide⟩,⟨2631,by decide⟩] | 5 => ![⟨2645,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2646,by decide⟩] | _ => ![⟨2647,by decide⟩,⟨1637,by decide⟩,⟨1726,by decide⟩]

def ntree10RLRLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2620,by decide⟩,⟨2648,by decide⟩,⟨1752,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨1752,by decide⟩,⟨1752,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨2649,by decide⟩,⟨2649,by decide⟩] | 3 => ![⟨2276,by decide⟩,⟨2650,by decide⟩,⟨2651,by decide⟩] | 4 => ![⟨1651,by decide⟩,⟨2652,by decide⟩,⟨2652,by decide⟩] | 5 => ![⟨2254,by decide⟩,⟨2653,by decide⟩,⟨2654,by decide⟩] | 6 => ![⟨1180,by decide⟩,⟨1715,by decide⟩,⟨2655,by decide⟩] | _ => ![⟨1180,by decide⟩,⟨1768,by decide⟩,⟨2656,by decide⟩]

end Paper2.Certificates.Q6.Coverage

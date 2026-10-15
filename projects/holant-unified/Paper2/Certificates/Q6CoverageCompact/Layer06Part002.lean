import Paper2.Certificates.Q6CoverageCompact.Layer06Part001

namespace Paper2.Certificates.Q6.Coverage

def ntree6RLRL (i : Nat) : Fin 3 → Fin 729 := if i < 7 then ntree6RLRLL i else ntree6RLRLR (i - 7)

def ntree6RLRRL (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨498,by decide⟩,⟨499,by decide⟩,⟨500,by decide⟩] | 1 => ![⟨501,by decide⟩,⟨502,by decide⟩,⟨503,by decide⟩] | 2 => ![⟨504,by decide⟩,⟨505,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨507,by decide⟩,⟨508,by decide⟩,⟨509,by decide⟩] | 4 => ![⟨510,by decide⟩,⟨511,by decide⟩,⟨512,by decide⟩] | 5 => ![⟨513,by decide⟩,⟨514,by decide⟩,⟨515,by decide⟩] | 6 => ![⟨516,by decide⟩,⟨517,by decide⟩,⟨518,by decide⟩] | _ => ![⟨519,by decide⟩,⟨520,by decide⟩,⟨521,by decide⟩]

def ntree6RLRRR (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨522,by decide⟩,⟨523,by decide⟩,⟨524,by decide⟩] | 1 => ![⟨525,by decide⟩,⟨526,by decide⟩,⟨527,by decide⟩] | 2 => ![⟨528,by decide⟩,⟨529,by decide⟩,⟨530,by decide⟩] | 3 => ![⟨531,by decide⟩,⟨532,by decide⟩,⟨533,by decide⟩] | 4 => ![⟨534,by decide⟩,⟨535,by decide⟩,⟨536,by decide⟩] | 5 => ![⟨537,by decide⟩,⟨538,by decide⟩,⟨539,by decide⟩] | 6 => ![⟨540,by decide⟩,⟨541,by decide⟩,⟨542,by decide⟩] | _ => ![⟨543,by decide⟩,⟨544,by decide⟩,⟨545,by decide⟩]

def ntree6RLRR (i : Nat) : Fin 3 → Fin 729 := if i < 8 then ntree6RLRRL i else ntree6RLRRR (i - 8)

def ntree6RLR (i : Nat) : Fin 3 → Fin 729 := if i < 15 then ntree6RLRL i else ntree6RLRR (i - 15)

def ntree6RL (i : Nat) : Fin 3 → Fin 729 := if i < 30 then ntree6RLL i else ntree6RLR (i - 30)

def ntree6RRLLL (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨546,by decide⟩,⟨547,by decide⟩,⟨548,by decide⟩] | 1 => ![⟨549,by decide⟩,⟨550,by decide⟩,⟨551,by decide⟩] | 2 => ![⟨552,by decide⟩,⟨553,by decide⟩,⟨554,by decide⟩] | 3 => ![⟨555,by decide⟩,⟨556,by decide⟩,⟨557,by decide⟩] | 4 => ![⟨558,by decide⟩,⟨559,by decide⟩,⟨560,by decide⟩] | 5 => ![⟨561,by decide⟩,⟨562,by decide⟩,⟨563,by decide⟩] | _ => ![⟨564,by decide⟩,⟨565,by decide⟩,⟨566,by decide⟩]

def ntree6RRLLR (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨567,by decide⟩,⟨568,by decide⟩,⟨569,by decide⟩] | 1 => ![⟨570,by decide⟩,⟨571,by decide⟩,⟨572,by decide⟩] | 2 => ![⟨573,by decide⟩,⟨574,by decide⟩,⟨575,by decide⟩] | 3 => ![⟨576,by decide⟩,⟨577,by decide⟩,⟨578,by decide⟩] | 4 => ![⟨579,by decide⟩,⟨580,by decide⟩,⟨581,by decide⟩] | 5 => ![⟨582,by decide⟩,⟨583,by decide⟩,⟨584,by decide⟩] | 6 => ![⟨585,by decide⟩,⟨586,by decide⟩,⟨587,by decide⟩] | _ => ![⟨588,by decide⟩,⟨589,by decide⟩,⟨590,by decide⟩]

def ntree6RRLL (i : Nat) : Fin 3 → Fin 729 := if i < 7 then ntree6RRLLL i else ntree6RRLLR (i - 7)

def ntree6RRLRL (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨591,by decide⟩,⟨592,by decide⟩,⟨593,by decide⟩] | 1 => ![⟨594,by decide⟩,⟨595,by decide⟩,⟨596,by decide⟩] | 2 => ![⟨597,by decide⟩,⟨598,by decide⟩,⟨599,by decide⟩] | 3 => ![⟨600,by decide⟩,⟨601,by decide⟩,⟨602,by decide⟩] | 4 => ![⟨603,by decide⟩,⟨604,by decide⟩,⟨605,by decide⟩] | 5 => ![⟨606,by decide⟩,⟨607,by decide⟩,⟨608,by decide⟩] | _ => ![⟨609,by decide⟩,⟨610,by decide⟩,⟨611,by decide⟩]

def ntree6RRLRR (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨612,by decide⟩,⟨613,by decide⟩,⟨614,by decide⟩] | 1 => ![⟨615,by decide⟩,⟨616,by decide⟩,⟨617,by decide⟩] | 2 => ![⟨618,by decide⟩,⟨619,by decide⟩,⟨620,by decide⟩] | 3 => ![⟨621,by decide⟩,⟨622,by decide⟩,⟨623,by decide⟩] | 4 => ![⟨624,by decide⟩,⟨625,by decide⟩,⟨626,by decide⟩] | 5 => ![⟨627,by decide⟩,⟨628,by decide⟩,⟨629,by decide⟩] | 6 => ![⟨630,by decide⟩,⟨631,by decide⟩,⟨632,by decide⟩] | _ => ![⟨633,by decide⟩,⟨634,by decide⟩,⟨635,by decide⟩]

def ntree6RRLR (i : Nat) : Fin 3 → Fin 729 := if i < 7 then ntree6RRLRL i else ntree6RRLRR (i - 7)

def ntree6RRL (i : Nat) : Fin 3 → Fin 729 := if i < 15 then ntree6RRLL i else ntree6RRLR (i - 15)

def ntree6RRRLL (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨636,by decide⟩,⟨637,by decide⟩,⟨638,by decide⟩] | 1 => ![⟨639,by decide⟩,⟨640,by decide⟩,⟨641,by decide⟩] | 2 => ![⟨642,by decide⟩,⟨643,by decide⟩,⟨644,by decide⟩] | 3 => ![⟨645,by decide⟩,⟨646,by decide⟩,⟨647,by decide⟩] | 4 => ![⟨648,by decide⟩,⟨649,by decide⟩,⟨650,by decide⟩] | 5 => ![⟨651,by decide⟩,⟨652,by decide⟩,⟨653,by decide⟩] | _ => ![⟨654,by decide⟩,⟨655,by decide⟩,⟨656,by decide⟩]

def ntree6RRRLR (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨657,by decide⟩,⟨658,by decide⟩,⟨659,by decide⟩] | 1 => ![⟨660,by decide⟩,⟨661,by decide⟩,⟨662,by decide⟩] | 2 => ![⟨663,by decide⟩,⟨664,by decide⟩,⟨665,by decide⟩] | 3 => ![⟨666,by decide⟩,⟨667,by decide⟩,⟨668,by decide⟩] | 4 => ![⟨669,by decide⟩,⟨670,by decide⟩,⟨671,by decide⟩] | 5 => ![⟨672,by decide⟩,⟨673,by decide⟩,⟨674,by decide⟩] | 6 => ![⟨675,by decide⟩,⟨676,by decide⟩,⟨677,by decide⟩] | _ => ![⟨678,by decide⟩,⟨679,by decide⟩,⟨680,by decide⟩]

def ntree6RRRL (i : Nat) : Fin 3 → Fin 729 := if i < 7 then ntree6RRRLL i else ntree6RRRLR (i - 7)

def ntree6RRRRL (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨681,by decide⟩,⟨682,by decide⟩,⟨683,by decide⟩] | 1 => ![⟨684,by decide⟩,⟨685,by decide⟩,⟨686,by decide⟩] | 2 => ![⟨687,by decide⟩,⟨688,by decide⟩,⟨689,by decide⟩] | 3 => ![⟨690,by decide⟩,⟨691,by decide⟩,⟨692,by decide⟩] | 4 => ![⟨693,by decide⟩,⟨694,by decide⟩,⟨695,by decide⟩] | 5 => ![⟨696,by decide⟩,⟨697,by decide⟩,⟨698,by decide⟩] | 6 => ![⟨699,by decide⟩,⟨700,by decide⟩,⟨701,by decide⟩] | _ => ![⟨702,by decide⟩,⟨703,by decide⟩,⟨704,by decide⟩]

def ntree6RRRRR (i : Nat) : Fin 3 → Fin 729 := match i with | 0 => ![⟨705,by decide⟩,⟨706,by decide⟩,⟨707,by decide⟩] | 1 => ![⟨708,by decide⟩,⟨709,by decide⟩,⟨710,by decide⟩] | 2 => ![⟨711,by decide⟩,⟨712,by decide⟩,⟨713,by decide⟩] | 3 => ![⟨714,by decide⟩,⟨715,by decide⟩,⟨716,by decide⟩] | 4 => ![⟨717,by decide⟩,⟨718,by decide⟩,⟨719,by decide⟩] | 5 => ![⟨720,by decide⟩,⟨721,by decide⟩,⟨722,by decide⟩] | 6 => ![⟨723,by decide⟩,⟨724,by decide⟩,⟨725,by decide⟩] | _ => ![⟨726,by decide⟩,⟨727,by decide⟩,⟨728,by decide⟩]

def ntree6RRRR (i : Nat) : Fin 3 → Fin 729 := if i < 8 then ntree6RRRRL i else ntree6RRRRR (i - 8)

def ntree6RRR (i : Nat) : Fin 3 → Fin 729 := if i < 15 then ntree6RRRL i else ntree6RRRR (i - 15)

def ntree6RR (i : Nat) : Fin 3 → Fin 729 := if i < 30 then ntree6RRL i else ntree6RRR (i - 30)

def ntree6R (i : Nat) : Fin 3 → Fin 729 := if i < 61 then ntree6RL i else ntree6RR (i - 61)

def ntree6 (i : Nat) : Fin 3 → Fin 729 := if i < 121 then ntree6L i else ntree6R (i - 121)

def layer6 : Fin 729 → State := fun i => stree6 i.val

def next6 : Fin 243 → Fin 3 → Fin 729 := fun i => ntree6 i.val

end Paper2.Certificates.Q6.Coverage

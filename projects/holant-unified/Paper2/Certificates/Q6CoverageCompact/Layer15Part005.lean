import Paper2.Certificates.Q6CoverageCompact.Layer15Part004

namespace Paper2.Certificates.Q6.Coverage

def ntree15LRLRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨707,by decide⟩,⟨716,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨717,by decide⟩,⟨706,by decide⟩,⟨481,by decide⟩] | 2 => ![⟨718,by decide⟩,⟨707,by decide⟩,⟨132,by decide⟩] | 3 => ![⟨132,by decide⟩,⟨638,by decide⟩,⟨719,by decide⟩] | 4 => ![⟨481,by decide⟩,⟨639,by decide⟩,⟨720,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨661,by decide⟩] | 6 => ![⟨707,by decide⟩,⟨721,by decide⟩,⟨60,by decide⟩] | _ => ![⟨722,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRLRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLRRRLL i else ntree15LRLRRRLR (i - 7)

def ntree15LRLRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨723,by decide⟩,⟨723,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨724,by decide⟩,⟨725,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨725,by decide⟩,⟨725,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨726,by decide⟩,⟨726,by decide⟩,⟨374,by decide⟩] | 4 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨727,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 6 => ![⟨728,by decide⟩,⟨726,by decide⟩,⟨384,by decide⟩] | _ => ![⟨729,by decide⟩,⟨167,by decide⟩,⟨502,by decide⟩]

def ntree15LRLRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨730,by decide⟩,⟨730,by decide⟩] | 1 => ![⟨503,by decide⟩,⟨730,by decide⟩,⟨731,by decide⟩] | 2 => ![⟨723,by decide⟩,⟨732,by decide⟩,⟨730,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨733,by decide⟩,⟨733,by decide⟩] | 4 => ![⟨734,by decide⟩,⟨189,by decide⟩,⟨504,by decide⟩] | 5 => ![⟨189,by decide⟩,⟨735,by decide⟩,⟨730,by decide⟩] | 6 => ![⟨389,by decide⟩,⟨389,by decide⟩,⟨736,by decide⟩] | _ => ![⟨194,by decide⟩,⟨737,by decide⟩,⟨194,by decide⟩]

def ntree15LRLRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LRLRRRRL i else ntree15LRLRRRRR (i - 8)

def ntree15LRLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLRRRL i else ntree15LRLRRRR (i - 15)

def ntree15LRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRLRRL i else ntree15LRLRRR (i - 30)

def ntree15LRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LRLRL i else ntree15LRLRR (i - 60)

def ntree15LRL (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15LRLL i else ntree15LRLR (i - 121)

def ntree15LRRLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨498,by decide⟩,⟨738,by decide⟩,⟨738,by decide⟩] | 1 => ![⟨739,by decide⟩,⟨725,by decide⟩,⟨400,by decide⟩] | 2 => ![⟨400,by decide⟩,⟨730,by decide⟩,⟨740,by decide⟩] | 3 => ![⟨498,by decide⟩,⟨741,by decide⟩,⟨741,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨742,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨733,by decide⟩,⟨743,by decide⟩] | _ => ![⟨167,by decide⟩,⟨744,by decide⟩,⟨733,by decide⟩]

def ntree15LRRLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨745,by decide⟩,⟨745,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨746,by decide⟩,⟨746,by decide⟩,⟨389,by decide⟩] | 2 => ![⟨747,by decide⟩,⟨747,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨748,by decide⟩,⟨748,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨749,by decide⟩,⟨749,by decide⟩,⟨374,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨750,by decide⟩,⟨750,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨751,by decide⟩] | _ => ![⟨752,by decide⟩,⟨752,by decide⟩,⟨498,by decide⟩]

def ntree15LRRLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRLLLLL i else ntree15LRRLLLLR (i - 7)

def ntree15LRRLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨753,by decide⟩,⟨753,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨754,by decide⟩,⟨754,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨755,by decide⟩,⟨755,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨756,by decide⟩,⟨756,by decide⟩,⟨437,by decide⟩] | 4 => ![⟨757,by decide⟩,⟨755,by decide⟩,⟨432,by decide⟩] | 5 => ![⟨758,by decide⟩,⟨752,by decide⟩,⟨499,by decide⟩] | _ => ![⟨759,by decide⟩,⟨76,by decide⟩,⟨500,by decide⟩]

def ntree15LRRLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨760,by decide⟩,⟨753,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨761,by decide⟩,⟨754,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨762,by decide⟩,⟨167,by decide⟩,⟨432,by decide⟩] | 3 => ![⟨763,by decide⟩,⟨756,by decide⟩,⟨436,by decide⟩] | 4 => ![⟨764,by decide⟩,⟨76,by decide⟩,⟨501,by decide⟩] | 5 => ![⟨765,by decide⟩,⟨216,by decide⟩,⟨516,by decide⟩] | 6 => ![⟨766,by decide⟩,⟨167,by decide⟩,⟨432,by decide⟩] | _ => ![⟨767,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRRLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRLLLRL i else ntree15LRRLLLRR (i - 7)

def ntree15LRRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRLLLL i else ntree15LRRLLLR (i - 15)

def ntree15LRRLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨768,by decide⟩,⟨76,by decide⟩,⟨504,by decide⟩] | 1 => ![⟨769,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 2 => ![⟨770,by decide⟩,⟨226,by decide⟩,⟨518,by decide⟩] | 3 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨771,by decide⟩] | 4 => ![⟨772,by decide⟩,⟨772,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨0,by decide⟩]

def ntree15LRRLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨773,by decide⟩,⟨733,by decide⟩] | 2 => ![⟨432,by decide⟩,⟨733,by decide⟩,⟨774,by decide⟩] | 3 => ![⟨775,by decide⟩,⟨775,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨776,by decide⟩,⟨776,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨777,by decide⟩,⟨777,by decide⟩,⟨556,by decide⟩] | 6 => ![⟨778,by decide⟩,⟨778,by decide⟩,⟨557,by decide⟩] | _ => ![⟨725,by decide⟩,⟨779,by decide⟩,⟨2,by decide⟩]

def ntree15LRRLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRLLRLL i else ntree15LRRLLRLR (i - 7)

def ntree15LRRLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨725,by decide⟩,⟨780,by decide⟩,⟨638,by decide⟩] | 1 => ![⟨726,by decide⟩,⟨781,by decide⟩,⟨639,by decide⟩] | 2 => ![⟨782,by decide⟩,⟨725,by decide⟩,⟨385,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩] | 4 => ![⟨194,by decide⟩,⟨316,by decide⟩,⟨316,by decide⟩] | 5 => ![⟨783,by decide⟩,⟨167,by decide⟩,⟨385,by decide⟩] | _ => ![⟨784,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩]

def ntree15LRRLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨785,by decide⟩,⟨726,by decide⟩,⟨416,by decide⟩] | 1 => ![⟨786,by decide⟩,⟨745,by decide⟩,⟨385,by decide⟩] | 2 => ![⟨787,by decide⟩,⟨746,by decide⟩,⟨388,by decide⟩] | 3 => ![⟨788,by decide⟩,⟨747,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨789,by decide⟩,⟨167,by decide⟩,⟨385,by decide⟩] | 5 => ![⟨790,by decide⟩,⟨748,by decide⟩,⟨5,by decide⟩] | 6 => ![⟨791,by decide⟩,⟨749,by decide⟩,⟨377,by decide⟩] | _ => ![⟨792,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩]

def ntree15LRRLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRLLRRL i else ntree15LRRLLRRR (i - 7)

def ntree15LRRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRLLRL i else ntree15LRRLLRR (i - 15)

def ntree15LRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRRLLL i else ntree15LRRLLR (i - 30)

def ntree15LRRLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨604,by decide⟩,⟨2,by decide⟩,⟨793,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨670,by decide⟩,⟨670,by decide⟩] | 2 => ![⟨437,by decide⟩,⟨672,by decide⟩,⟨672,by decide⟩] | 3 => ![⟨794,by decide⟩,⟨167,by decide⟩,⟨604,by decide⟩] | 4 => ![⟨604,by decide⟩,⟨336,by decide⟩,⟨795,by decide⟩] | 5 => ![⟨615,by decide⟩,⟨337,by decide⟩,⟨796,by decide⟩] | _ => ![⟨797,by decide⟩,⟨167,by decide⟩,⟨621,by decide⟩]

def ntree15LRRLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨798,by decide⟩,⟨216,by decide⟩,⟨622,by decide⟩] | 1 => ![⟨799,by decide⟩,⟨76,by decide⟩,⟨623,by decide⟩] | 2 => ![⟨800,by decide⟩,⟨167,by decide⟩,⟨385,by decide⟩] | 3 => ![⟨801,by decide⟩,⟨167,by decide⟩,⟨385,by decide⟩] | 4 => ![⟨802,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨803,by decide⟩,⟨249,by decide⟩,⟨615,by decide⟩] | 6 => ![⟨804,by decide⟩,⟨76,by decide⟩,⟨624,by decide⟩] | _ => ![⟨805,by decide⟩,⟨226,by decide⟩,⟨625,by decide⟩]

def ntree15LRRLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRLRLLL i else ntree15LRRLRLLR (i - 7)

def ntree15LRRLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨806,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 1 => ![⟨807,by decide⟩,⟨723,by decide⟩,⟨599,by decide⟩] | 2 => ![⟨599,by decide⟩,⟨638,by decide⟩,⟨808,by decide⟩] | 3 => ![⟨723,by decide⟩,⟨809,by decide⟩,⟨336,by decide⟩] | 4 => ![⟨810,by decide⟩,⟨76,by decide⟩,⟨628,by decide⟩] | 5 => ![⟨811,by decide⟩,⟨706,by decide⟩,⟨629,by decide⟩] | _ => ![⟨812,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩]

def ntree15LRRLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨813,by decide⟩,⟨775,by decide⟩,⟨5,by decide⟩] | 1 => ![⟨814,by decide⟩,⟨776,by decide⟩,⟨354,by decide⟩] | 2 => ![⟨815,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 3 => ![⟨816,by decide⟩,⟨777,by decide⟩,⟨630,by decide⟩] | 4 => ![⟨817,by decide⟩,⟨778,by decide⟩,⟨631,by decide⟩] | 5 => ![⟨818,by decide⟩,⟨557,by decide⟩,⟨557,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨819,by decide⟩,⟨0,by decide⟩] | _ => ![⟨5,by decide⟩,⟨819,by decide⟩,⟨5,by decide⟩]

def ntree15LRRLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRLRLRL i else ntree15LRRLRLRR (i - 7)

def ntree15LRRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRLRLL i else ntree15LRRLRLR (i - 15)

def ntree15LRRLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨820,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨821,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨822,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨821,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨821,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | _ => ![⟨0,by decide⟩,⟨823,by decide⟩,⟨0,by decide⟩]

def ntree15LRRLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨824,by decide⟩,⟨825,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨820,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨820,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨826,by decide⟩,⟨827,by decide⟩,⟨827,by decide⟩] | 6 => ![⟨828,by decide⟩,⟨826,by decide⟩,⟨828,by decide⟩] | _ => ![⟨829,by decide⟩,⟨0,by decide⟩,⟨829,by decide⟩]

def ntree15LRRLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRLRRLL i else ntree15LRRLRRLR (i - 7)

def ntree15LRRLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨829,by decide⟩,⟨1,by decide⟩,⟨830,by decide⟩] | 1 => ![⟨828,by decide⟩,⟨827,by decide⟩,⟨831,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨832,by decide⟩,⟨826,by decide⟩] | 3 => ![⟨833,by decide⟩,⟨35,by decide⟩,⟨829,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨834,by decide⟩] | 5 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨835,by decide⟩] | 6 => ![⟨826,by decide⟩,⟨836,by decide⟩,⟨836,by decide⟩] | _ => ![⟨0,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩]

def ntree15LRRLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨838,by decide⟩,⟨839,by decide⟩,⟨839,by decide⟩] | 1 => ![⟨840,by decide⟩,⟨841,by decide⟩,⟨841,by decide⟩] | 2 => ![⟨842,by decide⟩,⟨843,by decide⟩,⟨843,by decide⟩] | 3 => ![⟨5,by decide⟩,⟨837,by decide⟩,⟨844,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨845,by decide⟩] | 5 => ![⟨846,by decide⟩,⟨1,by decide⟩,⟨847,by decide⟩] | 6 => ![⟨848,by decide⟩,⟨839,by decide⟩,⟨849,by decide⟩] | _ => ![⟨46,by decide⟩,⟨850,by decide⟩,⟨837,by decide⟩]

def ntree15LRRLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LRRLRRRL i else ntree15LRRLRRRR (i - 8)

def ntree15LRRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRLRRL i else ntree15LRRLRRR (i - 15)

def ntree15LRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRRLRL i else ntree15LRRLRR (i - 30)

def ntree15LRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LRRLL i else ntree15LRRLR (i - 60)

def ntree15LRRRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨851,by decide⟩,⟨852,by decide⟩,⟨841,by decide⟩] | 1 => ![⟨840,by decide⟩,⟨840,by decide⟩,⟨840,by decide⟩] | 2 => ![⟨840,by decide⟩,⟨853,by decide⟩,⟨853,by decide⟩] | 3 => ![⟨840,by decide⟩,⟨854,by decide⟩,⟨840,by decide⟩] | 4 => ![⟨855,by decide⟩,⟨855,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨856,by decide⟩,⟨856,by decide⟩,⟨0,by decide⟩] | _ => ![⟨857,by decide⟩,⟨855,by decide⟩,⟨828,by decide⟩]

def ntree15LRRRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨858,by decide⟩,⟨46,by decide⟩,⟨829,by decide⟩] | 1 => ![⟨859,by decide⟩,⟨856,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨860,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨861,by decide⟩,⟨861,by decide⟩] | 4 => ![⟨828,by decide⟩,⟨861,by decide⟩,⟨862,by decide⟩] | 5 => ![⟨829,by decide⟩,⟨56,by decide⟩,⟨863,by decide⟩] | 6 => ![⟨855,by decide⟩,⟨864,by decide⟩,⟨861,by decide⟩] | _ => ![⟨856,by decide⟩,⟨865,by decide⟩,⟨56,by decide⟩]

def ntree15LRRRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRRLLLL i else ntree15LRRRLLLR (i - 7)

def ntree15LRRRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨838,by decide⟩,⟨838,by decide⟩,⟨838,by decide⟩] | 1 => ![⟨838,by decide⟩,⟨866,by decide⟩,⟨866,by decide⟩] | 2 => ![⟨838,by decide⟩,⟨838,by decide⟩,⟨867,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨868,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨826,by decide⟩,⟨869,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨870,by decide⟩,⟨870,by decide⟩]

def ntree15LRRRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨856,by decide⟩,⟨871,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨855,by decide⟩,⟨872,by decide⟩,⟨836,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨873,by decide⟩] | 3 => ![⟨821,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨874,by decide⟩] | 5 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨874,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨875,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨876,by decide⟩,⟨0,by decide⟩]

def ntree15LRRRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRRLLRL i else ntree15LRRRLLRR (i - 7)

def ntree15LRRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRRLLL i else ntree15LRRRLLR (i - 15)

def ntree15LRRRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨877,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨46,by decide⟩,⟨878,by decide⟩,⟨879,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨879,by decide⟩,⟨879,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨880,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩] | _ => ![⟨882,by decide⟩,⟨883,by decide⟩,⟨883,by decide⟩]

def ntree15LRRRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨884,by decide⟩,⟨885,by decide⟩,⟨885,by decide⟩] | 1 => ![⟨886,by decide⟩,⟨887,by decide⟩,⟨887,by decide⟩] | 2 => ![⟨888,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨882,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨889,by decide⟩,⟨889,by decide⟩] | 5 => ![⟨884,by decide⟩,⟨884,by decide⟩,⟨884,by decide⟩] | 6 => ![⟨884,by decide⟩,⟨890,by decide⟩,⟨890,by decide⟩] | _ => ![⟨0,by decide⟩,⟨891,by decide⟩,⟨891,by decide⟩]

def ntree15LRRRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRRLRLL i else ntree15LRRRLRLR (i - 7)

def ntree15LRRRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨826,by decide⟩,⟨892,by decide⟩,⟨892,by decide⟩] | 2 => ![⟨893,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 3 => ![⟨894,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨895,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨896,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRRRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨897,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨898,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨899,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨880,by decide⟩] | 4 => ![⟨898,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨898,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨897,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨897,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩]

def ntree15LRRRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRRLRRL i else ntree15LRRRLRRR (i - 7)

def ntree15LRRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRRLRL i else ntree15LRRRLRR (i - 15)

def ntree15LRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRRRLL i else ntree15LRRRLR (i - 30)

def ntree15LRRRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨900,by decide⟩,⟨856,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨46,by decide⟩,⟨901,by decide⟩,⟨881,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨902,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨903,by decide⟩,⟨904,by decide⟩,⟨883,by decide⟩] | 5 => ![⟨905,by decide⟩,⟨906,by decide⟩,⟨1,by decide⟩] | _ => ![⟨898,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩]

def ntree15LRRRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨907,by decide⟩,⟨46,by decide⟩,⟨908,by decide⟩] | 1 => ![⟨909,by decide⟩,⟨0,by decide⟩,⟨910,by decide⟩] | 2 => ![⟨909,by decide⟩,⟨881,by decide⟩,⟨911,by decide⟩] | 3 => ![⟨903,by decide⟩,⟨903,by decide⟩,⟨882,by decide⟩] | 4 => ![⟨905,by decide⟩,⟨905,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨119,by decide⟩,⟨912,by decide⟩,⟨881,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRRRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRRRLLL i else ntree15LRRRRLLR (i - 7)

def ntree15LRRRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨913,by decide⟩] | 2 => ![⟨914,by decide⟩,⟨2,by decide⟩,⟨915,by decide⟩] | 3 => ![⟨5,by decide⟩,⟨881,by decide⟩,⟨916,by decide⟩] | 4 => ![⟨917,by decide⟩,⟨885,by decide⟩,⟨918,by decide⟩] | 5 => ![⟨919,by decide⟩,⟨920,by decide⟩,⟨5,by decide⟩] | _ => ![⟨921,by decide⟩,⟨922,by decide⟩,⟨0,by decide⟩]

def ntree15LRRRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨820,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩] | 1 => ![⟨921,by decide⟩,⟨923,by decide⟩,⟨881,by decide⟩] | 2 => ![⟨914,by decide⟩,⟨0,by decide⟩,⟨914,by decide⟩] | 3 => ![⟨917,by decide⟩,⟨884,by decide⟩,⟨917,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨924,by decide⟩,⟨924,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨925,by decide⟩] | 6 => ![⟨5,by decide⟩,⟨924,by decide⟩,⟨926,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨927,by decide⟩]

def ntree15LRRRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRRRLRL i else ntree15LRRRRLRR (i - 7)

def ntree15LRRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRRRLL i else ntree15LRRRRLR (i - 15)

def ntree15LRRRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨928,by decide⟩] | 1 => ![⟨132,by decide⟩,⟨881,by decide⟩,⟨929,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨930,by decide⟩,⟨0,by decide⟩] | _ => ![⟨5,by decide⟩,⟨930,by decide⟩,⟨5,by decide⟩]

def ntree15LRRRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨897,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 1 => ![⟨921,by decide⟩,⟨931,by decide⟩,⟨837,by decide⟩] | 2 => ![⟨909,by decide⟩,⟨837,by decide⟩,⟨932,by decide⟩] | 3 => ![⟨933,by decide⟩,⟨934,by decide⟩,⟨935,by decide⟩] | 4 => ![⟨936,by decide⟩,⟨937,by decide⟩,⟨938,by decide⟩] | 5 => ![⟨939,by decide⟩,⟨940,by decide⟩,⟨941,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨942,by decide⟩,⟨0,by decide⟩] | _ => ![⟨943,by decide⟩,⟨943,by decide⟩,⟨0,by decide⟩]

def ntree15LRRRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRRRRRLL i else ntree15LRRRRRLR (i - 7)

def ntree15LRRRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨943,by decide⟩,⟨944,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨945,by decide⟩,⟨945,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨946,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨947,by decide⟩,⟨947,by decide⟩,⟨947,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨948,by decide⟩,⟨948,by decide⟩] | 5 => ![⟨947,by decide⟩,⟨949,by decide⟩,⟨949,by decide⟩] | 6 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨950,by decide⟩,⟨950,by decide⟩]

def ntree15LRRRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨951,by decide⟩,⟨951,by decide⟩] | 1 => ![⟨167,by decide⟩,⟨952,by decide⟩,⟨950,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨953,by decide⟩,⟨826,by decide⟩] | 3 => ![⟨954,by decide⟩,⟨954,by decide⟩,⟨826,by decide⟩] | 4 => ![⟨954,by decide⟩,⟨955,by decide⟩,⟨827,by decide⟩] | 5 => ![⟨956,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 6 => ![⟨957,by decide⟩,⟨0,by decide⟩,⟨957,by decide⟩] | _ => ![⟨0,by decide⟩,⟨958,by decide⟩,⟨958,by decide⟩]

def ntree15LRRRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LRRRRRRL i else ntree15LRRRRRRR (i - 8)

def ntree15LRRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRRRRRL i else ntree15LRRRRRR (i - 15)

def ntree15LRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRRRRL i else ntree15LRRRRR (i - 30)

def ntree15LRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LRRRL i else ntree15LRRRR (i - 60)

def ntree15LRR (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15LRRL i else ntree15LRRR (i - 121)

def ntree15LR (i : Nat) : Fin 3 → Fin 1868 := if i < 242 then ntree15LRL i else ntree15LRR (i - 242)

def ntree15L (i : Nat) : Fin 3 → Fin 1868 := if i < 484 then ntree15LL i else ntree15LR (i - 484)

def ntree15RLLLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨959,by decide⟩] | 3 => ![⟨960,by decide⟩,⟨960,by decide⟩,⟨947,by decide⟩] | 4 => ![⟨961,by decide⟩,⟨961,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨46,by decide⟩,⟨962,by decide⟩,⟨948,by decide⟩] | _ => ![⟨960,by decide⟩,⟨963,by decide⟩,⟨949,by decide⟩]

def ntree15RLLLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨961,by decide⟩,⟨964,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨965,by decide⟩,⟨965,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨966,by decide⟩,⟨967,by decide⟩,⟨837,by decide⟩] | 3 => ![⟨167,by decide⟩,⟨968,by decide⟩,⟨837,by decide⟩] | 4 => ![⟨965,by decide⟩,⟨969,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨970,by decide⟩,⟨971,by decide⟩,⟨839,by decide⟩] | 6 => ![⟨205,by decide⟩,⟨972,by decide⟩,⟨972,by decide⟩] | _ => ![⟨204,by decide⟩,⟨973,by decide⟩,⟨972,by decide⟩]

def ntree15RLLLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLLLLLL i else ntree15RLLLLLLR (i - 7)

def ntree15RLLLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨46,by decide⟩,⟨974,by decide⟩,⟨951,by decide⟩] | 1 => ![⟨167,by decide⟩,⟨975,by decide⟩,⟨837,by decide⟩] | 2 => ![⟨966,by decide⟩,⟨966,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨970,by decide⟩,⟨970,by decide⟩,⟨838,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨976,by decide⟩] | 5 => ![⟨977,by decide⟩,⟨0,by decide⟩,⟨977,by decide⟩] | _ => ![⟨977,by decide⟩,⟨1,by decide⟩,⟨978,by decide⟩]

def ntree15RLLLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨979,by decide⟩,⟨979,by decide⟩] | 1 => ![⟨980,by decide⟩,⟨980,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨981,by decide⟩,⟨981,by decide⟩,⟨884,by decide⟩] | 3 => ![⟨982,by decide⟩,⟨982,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨983,by decide⟩,⟨983,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨984,by decide⟩,⟨984,by decide⟩,⟨826,by decide⟩] | 6 => ![⟨985,by decide⟩,⟨167,by decide⟩,⟨977,by decide⟩] | _ => ![⟨986,by decide⟩,⟨46,by decide⟩,⟨977,by decide⟩]

def ntree15RLLLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLLLLRL i else ntree15RLLLLLRR (i - 7)

def ntree15RLLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLLLLL i else ntree15RLLLLLR (i - 15)

def ntree15RLLLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨987,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨988,by decide⟩,⟨988,by decide⟩] | 2 => ![⟨989,by decide⟩,⟨989,by decide⟩,⟨989,by decide⟩] | 3 => ![⟨989,by decide⟩,⟨990,by decide⟩,⟨990,by decide⟩] | 4 => ![⟨991,by decide⟩,⟨991,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨992,by decide⟩,⟨992,by decide⟩,⟨989,by decide⟩] | _ => ![⟨826,by decide⟩,⟨993,by decide⟩,⟨993,by decide⟩]

def ntree15RLLLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨994,by decide⟩,⟨994,by decide⟩,⟨994,by decide⟩] | 1 => ![⟨994,by decide⟩,⟨995,by decide⟩,⟨995,by decide⟩] | 2 => ![⟨996,by decide⟩,⟨996,by decide⟩,⟨223,by decide⟩] | 3 => ![⟨997,by decide⟩,⟨997,by decide⟩,⟨994,by decide⟩] | 4 => ![⟨998,by decide⟩,⟨998,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨884,by decide⟩,⟨884,by decide⟩,⟨999,by decide⟩] | _ => ![⟨1000,by decide⟩,⟨0,by decide⟩,⟨1000,by decide⟩]

def ntree15RLLLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLLLRLL i else ntree15RLLLLRLR (i - 7)

def ntree15RLLLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1001,by decide⟩,⟨945,by decide⟩,⟨1000,by decide⟩] | 1 => ![⟨1000,by decide⟩,⟨979,by decide⟩,⟨1002,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1003,by decide⟩,⟨1003,by decide⟩] | 3 => ![⟨1004,by decide⟩,⟨213,by decide⟩,⟨1000,by decide⟩] | 4 => ![⟨213,by decide⟩,⟨1005,by decide⟩,⟨1003,by decide⟩] | 5 => ![⟨1000,by decide⟩,⟨924,by decide⟩,⟨1006,by decide⟩] | _ => ![⟨1007,by decide⟩,⟨947,by decide⟩,⟨1007,by decide⟩]

def ntree15RLLLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨943,by decide⟩,⟨1008,by decide⟩,⟨924,by decide⟩] | 1 => ![⟨1009,by decide⟩,⟨258,by decide⟩,⟨258,by decide⟩] | 2 => ![⟨1010,by decide⟩,⟨947,by decide⟩,⟨1010,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1011,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨1012,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨46,by decide⟩,⟨1013,by decide⟩,⟨1003,by decide⟩] | 6 => ![⟨977,by decide⟩,⟨837,by decide⟩,⟨1014,by decide⟩] | _ => ![⟨223,by decide⟩,⟨1015,by decide⟩,⟨1015,by decide⟩]

def ntree15RLLLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLLLRRL i else ntree15RLLLLRRR (i - 7)

def ntree15RLLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLLLRL i else ntree15RLLLLRR (i - 15)

def ntree15RLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLLLLL i else ntree15RLLLLR (i - 30)

def ntree15RLLLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨230,by decide⟩,⟨1016,by decide⟩,⟨1015,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1017,by decide⟩,⟨1017,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1018,by decide⟩,⟨1018,by decide⟩] | 3 => ![⟨258,by decide⟩,⟨1019,by decide⟩,⟨1019,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1020,by decide⟩,⟨1020,by decide⟩] | 5 => ![⟨223,by decide⟩,⟨1021,by decide⟩,⟨1021,by decide⟩] | _ => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1022,by decide⟩]

def ntree15RLLLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 1 => ![⟨1023,by decide⟩,⟨943,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨1024,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1025,by decide⟩,⟨954,by decide⟩,⟨828,by decide⟩] | 4 => ![⟨1026,by decide⟩,⟨943,by decide⟩,⟨829,by decide⟩] | 5 => ![⟨1027,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1028,by decide⟩,⟨1028,by decide⟩] | _ => ![⟨947,by decide⟩,⟨1029,by decide⟩,⟨1029,by decide⟩]

def ntree15RLLLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLLRLLL i else ntree15RLLLRLLR (i - 7)

def ntree15RLLLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1030,by decide⟩,⟨1030,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1031,by decide⟩,⟨1031,by decide⟩] | 2 => ![⟨846,by decide⟩,⟨0,by decide⟩,⟨846,by decide⟩] | 3 => ![⟨848,by decide⟩,⟨838,by decide⟩,⟨848,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1032,by decide⟩,⟨1032,by decide⟩] | 5 => ![⟨945,by decide⟩,⟨1033,by decide⟩,⟨1032,by decide⟩] | _ => ![⟨829,by decide⟩,⟨1032,by decide⟩,⟨1034,by decide⟩]

def ntree15RLLLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1035,by decide⟩,⟨1035,by decide⟩] | 1 => ![⟨5,by decide⟩,⟨1035,by decide⟩,⟨1036,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨1037,by decide⟩,⟨1035,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1038,by decide⟩,⟨1038,by decide⟩] | 4 => ![⟨943,by decide⟩,⟨1039,by decide⟩,⟨881,by decide⟩] | 5 => ![⟨328,by decide⟩,⟨0,by decide⟩,⟨328,by decide⟩] | 6 => ![⟨167,by decide⟩,⟨1040,by decide⟩,⟨881,by decide⟩] | _ => ![⟨980,by decide⟩,⟨1041,by decide⟩,⟨881,by decide⟩]

def ntree15RLLLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLLRLRL i else ntree15RLLLRLRR (i - 7)

def ntree15RLLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLLRLL i else ntree15RLLLRLR (i - 15)

def ntree15RLLLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨981,by decide⟩,⟨1042,by decide⟩,⟨885,by decide⟩] | 1 => ![⟨982,by decide⟩,⟨1043,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩] | 3 => ![⟨954,by decide⟩,⟨1044,by decide⟩,⟨892,by decide⟩] | 4 => ![⟨167,by decide⟩,⟨1045,by decide⟩,⟨881,by decide⟩] | 5 => ![⟨826,by decide⟩,⟨1046,by decide⟩,⟨826,by decide⟩] | _ => ![⟨826,by decide⟩,⟨1047,by decide⟩,⟨826,by decide⟩]

def ntree15RLLLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨983,by decide⟩,⟨1048,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨984,by decide⟩,⟨1049,by decide⟩,⟨836,by decide⟩] | 2 => ![⟨1050,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1051,by decide⟩,⟨1051,by decide⟩] | 4 => ![⟨989,by decide⟩,⟨1052,by decide⟩,⟨1052,by decide⟩] | 5 => ![⟨46,by decide⟩,⟨1053,by decide⟩,⟨1051,by decide⟩] | 6 => ![⟨991,by decide⟩,⟨1054,by decide⟩,⟨2,by decide⟩] | _ => ![⟨992,by decide⟩,⟨1055,by decide⟩,⟨1052,by decide⟩]

def ntree15RLLLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLLRRLL i else ntree15RLLLRRLR (i - 7)

def ntree15RLLLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨826,by decide⟩,⟨1056,by decide⟩,⟨826,by decide⟩] | 1 => ![⟨223,by decide⟩,⟨1057,by decide⟩,⟨223,by decide⟩] | 2 => ![⟨994,by decide⟩,⟨1058,by decide⟩,⟨994,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨1059,by decide⟩,⟨1059,by decide⟩] | 4 => ![⟨994,by decide⟩,⟨1060,by decide⟩,⟨1060,by decide⟩] | 5 => ![⟨855,by decide⟩,⟨1061,by decide⟩,⟨1059,by decide⟩] | 6 => ![⟨996,by decide⟩,⟨1062,by decide⟩,⟨337,by decide⟩] | _ => ![⟨997,by decide⟩,⟨1063,by decide⟩,⟨1060,by decide⟩]

def ntree15RLLLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨223,by decide⟩,⟨1064,by decide⟩,⟨1064,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1065,by decide⟩,⟨1065,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1066,by decide⟩,⟨1066,by decide⟩] | 3 => ![⟨167,by decide⟩,⟨1067,by decide⟩,⟨1065,by decide⟩] | 4 => ![⟨205,by decide⟩,⟨1068,by decide⟩,⟨1068,by decide⟩] | 5 => ![⟨204,by decide⟩,⟨1069,by decide⟩,⟨1068,by decide⟩] | 6 => ![⟨167,by decide⟩,⟨1070,by decide⟩,⟨881,by decide⟩] | _ => ![⟨46,by decide⟩,⟨1071,by decide⟩,⟨1066,by decide⟩]

def ntree15RLLLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RLLLRRRL i else ntree15RLLLRRRR (i - 8)

def ntree15RLLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLLRRL i else ntree15RLLLRRR (i - 15)

def ntree15RLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLLLRL i else ntree15RLLLRR (i - 30)

def ntree15RLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15RLLLL i else ntree15RLLLR (i - 60)

def ntree15RLLRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨167,by decide⟩,⟨1072,by decide⟩,⟨881,by decide⟩] | 1 => ![⟨249,by decide⟩,⟨1073,by decide⟩,⟨1064,by decide⟩] | 2 => ![⟨223,by decide⟩,⟨1074,by decide⟩,⟨223,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1075,by decide⟩,⟨1075,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨1076,by decide⟩,⟨1076,by decide⟩] | 5 => ![⟨46,by decide⟩,⟨1077,by decide⟩,⟨1075,by decide⟩] | _ => ![⟨223,by decide⟩,⟨1078,by decide⟩,⟨223,by decide⟩]

def ntree15RLLRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨230,by decide⟩,⟨1079,by decide⟩,⟨1076,by decide⟩] | 1 => ![⟨349,by decide⟩,⟨258,by decide⟩,⟨349,by decide⟩] | 2 => ![⟨258,by decide⟩,⟨1080,by decide⟩,⟨1080,by decide⟩] | 3 => ![⟨1081,by decide⟩,⟨945,by decide⟩,⟨351,by decide⟩] | 4 => ![⟨351,by decide⟩,⟨1035,by decide⟩,⟨1082,by decide⟩] | 5 => ![⟨354,by decide⟩,⟨1064,by decide⟩,⟨1083,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩] | _ => ![⟨824,by decide⟩,⟨824,by decide⟩,⟨0,by decide⟩]

def ntree15RLLRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLRLLLL i else ntree15RLLRLLLR (i - 7)

def ntree15RLLRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1084,by decide⟩,⟨1084,by decide⟩,⟨1084,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1085,by decide⟩,⟨1085,by decide⟩] | 2 => ![⟨1084,by decide⟩,⟨1086,by decide⟩,⟨1086,by decide⟩] | 3 => ![⟨1087,by decide⟩,⟨0,by decide⟩,⟨1087,by decide⟩] | 4 => ![⟨1088,by decide⟩,⟨1084,by decide⟩,⟨1088,by decide⟩] | 5 => ![⟨5,by decide⟩,⟨1085,by decide⟩,⟨1089,by decide⟩] | _ => ![⟨1087,by decide⟩,⟨1,by decide⟩,⟨1090,by decide⟩]

def ntree15RLLRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1088,by decide⟩,⟨1086,by decide⟩,⟨1091,by decide⟩] | 1 => ![⟨373,by decide⟩,⟨373,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1092,by decide⟩,⟨1092,by decide⟩,⟨1092,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨1093,by decide⟩,⟨1093,by decide⟩] | 4 => ![⟨1092,by decide⟩,⟨1094,by decide⟩,⟨1094,by decide⟩] | 5 => ![⟨1095,by decide⟩,⟨374,by decide⟩,⟨1095,by decide⟩] | 6 => ![⟨1096,by decide⟩,⟨1092,by decide⟩,⟨1096,by decide⟩] | _ => ![⟨828,by decide⟩,⟨1093,by decide⟩,⟨1097,by decide⟩]

def ntree15RLLRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLRLLRL i else ntree15RLLRLLRR (i - 7)

def ntree15RLLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLRLLL i else ntree15RLLRLLR (i - 15)

def ntree15RLLRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1095,by decide⟩,⟨376,by decide⟩,⟨1098,by decide⟩] | 1 => ![⟨1096,by decide⟩,⟨1094,by decide⟩,⟨1099,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1100,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1101,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1102,by decide⟩] | 5 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1103,by decide⟩] | _ => ![⟨1092,by decide⟩,⟨1092,by decide⟩,⟨1104,by decide⟩]

def ntree15RLLRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨851,by decide⟩,⟨851,by decide⟩,⟨840,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1105,by decide⟩,⟨1105,by decide⟩] | 2 => ![⟨1106,by decide⟩,⟨0,by decide⟩,⟨1106,by decide⟩] | 3 => ![⟨1106,by decide⟩,⟨1105,by decide⟩,⟨1107,by decide⟩] | 4 => ![⟨856,by decide⟩,⟨1108,by decide⟩,⟨1105,by decide⟩] | 5 => ![⟨408,by decide⟩,⟨408,by decide⟩,⟨403,by decide⟩] | 6 => ![⟨1109,by decide⟩,⟨413,by decide⟩,⟨1106,by decide⟩] | _ => ![⟨1110,by decide⟩,⟨881,by decide⟩,⟨1111,by decide⟩]

def ntree15RLLRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLRLRLL i else ntree15RLLRLRLR (i - 7)

def ntree15RLLRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1112,by decide⟩,⟨0,by decide⟩,⟨1112,by decide⟩] | 1 => ![⟨432,by decide⟩,⟨881,by decide⟩,⟨1113,by decide⟩] | 2 => ![⟨1114,by decide⟩,⟨883,by decide⟩,⟨1115,by decide⟩] | 3 => ![⟨1112,by decide⟩,⟨1,by decide⟩,⟨1116,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩] | 5 => ![⟨1110,by decide⟩,⟨0,by decide⟩,⟨1110,by decide⟩] | _ => ![⟨1114,by decide⟩,⟨882,by decide⟩,⟨1114,by decide⟩]

def ntree15RLLRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1117,by decide⟩,⟨0,by decide⟩,⟨1117,by decide⟩] | 1 => ![⟨1118,by decide⟩,⟨826,by decide⟩,⟨1118,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1119,by decide⟩] | 3 => ![⟨1117,by decide⟩,⟨1,by decide⟩,⟨1120,by decide⟩] | 4 => ![⟨1118,by decide⟩,⟨827,by decide⟩,⟨1121,by decide⟩] | 5 => ![⟨1122,by decide⟩,⟨0,by decide⟩,⟨1122,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1123,by decide⟩,⟨1123,by decide⟩] | _ => ![⟨1122,by decide⟩,⟨881,by decide⟩,⟨1124,by decide⟩]

def ntree15RLLRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLRLRRL i else ntree15RLLRLRRR (i - 7)

def ntree15RLLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLRLRL i else ntree15RLLRLRR (i - 15)

def ntree15RLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLLRLL i else ntree15RLLRLR (i - 30)

def ntree15RLLRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1125,by decide⟩,⟨826,by decide⟩,⟨1125,by decide⟩] | 1 => ![⟨1125,by decide⟩,⟨892,by decide⟩,⟨1126,by decide⟩] | 2 => ![⟨432,by decide⟩,⟨881,by decide⟩,⟨1127,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1128,by decide⟩] | 4 => ![⟨432,by decide⟩,⟨0,by decide⟩,⟨432,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1129,by decide⟩,⟨1129,by decide⟩] | _ => ![⟨1130,by decide⟩,⟨1130,by decide⟩,⟨1130,by decide⟩]

def ntree15RLLRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1130,by decide⟩,⟨1131,by decide⟩,⟨1131,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1132,by decide⟩,⟨1132,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1133,by decide⟩,⟨1133,by decide⟩] | 3 => ![⟨1134,by decide⟩,⟨46,by decide⟩,⟨1122,by decide⟩] | 4 => ![⟨1135,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1136,by decide⟩,⟨855,by decide⟩,⟨1125,by decide⟩] | 6 => ![⟨1137,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | _ => ![⟨1138,by decide⟩,⟨856,by decide⟩,⟨1122,by decide⟩]

def ntree15RLLRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLRRLLL i else ntree15RLLRRLLR (i - 7)

def ntree15RLLRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨403,by decide⟩,⟨1139,by decide⟩,⟨1139,by decide⟩] | 1 => ![⟨432,by decide⟩,⟨1140,by decide⟩,⟨1141,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1142,by decide⟩,⟨1142,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1140,by decide⟩,⟨1140,by decide⟩] | 4 => ![⟨469,by decide⟩,⟨1143,by decide⟩,⟨1144,by decide⟩] | 5 => ![⟨432,by decide⟩,⟨881,by decide⟩,⟨1145,by decide⟩] | _ => ![⟨5,by decide⟩,⟨1142,by decide⟩,⟨1146,by decide⟩]

def ntree15RLLRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨470,by decide⟩,⟨1143,by decide⟩,⟨1143,by decide⟩] | 1 => ![⟨432,by decide⟩,⟨0,by decide⟩,⟨432,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1147,by decide⟩,⟨1147,by decide⟩] | 3 => ![⟨374,by decide⟩,⟨1148,by decide⟩,⟨1148,by decide⟩] | 4 => ![⟨5,by decide⟩,⟨1147,by decide⟩,⟨1149,by decide⟩] | 5 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1150,by decide⟩] | 6 => ![⟨377,by decide⟩,⟨1148,by decide⟩,⟨1151,by decide⟩] | _ => ![⟨1152,by decide⟩,⟨0,by decide⟩,⟨1152,by decide⟩]

def ntree15RLLRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLRRLRL i else ntree15RLLRRLRR (i - 7)

def ntree15RLLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLRRLL i else ntree15RLLRRLR (i - 15)

def ntree15RLLRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1153,by decide⟩,⟨1153,by decide⟩] | 1 => ![⟨374,by decide⟩,⟨1154,by decide⟩,⟨1154,by decide⟩] | 2 => ![⟨432,by decide⟩,⟨1153,by decide⟩,⟨1155,by decide⟩] | 3 => ![⟨432,by decide⟩,⟨881,by decide⟩,⟨1156,by decide⟩] | 4 => ![⟨481,by decide⟩,⟨1154,by decide⟩,⟨1157,by decide⟩] | 5 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1158,by decide⟩] | _ => ![⟨1159,by decide⟩,⟨0,by decide⟩,⟨1159,by decide⟩]

def ntree15RLLRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1160,by decide⟩,⟨0,by decide⟩,⟨1160,by decide⟩] | 1 => ![⟨1161,by decide⟩,⟨840,by decide⟩,⟨1161,by decide⟩] | 2 => ![⟨1162,by decide⟩,⟨1130,by decide⟩,⟨1162,by decide⟩] | 3 => ![⟨1163,by decide⟩,⟨0,by decide⟩,⟨1163,by decide⟩] | 4 => ![⟨46,by decide⟩,⟨1164,by decide⟩,⟨1153,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1165,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩] | _ => ![⟨410,by decide⟩,⟨1166,by decide⟩,⟨1154,by decide⟩]

def ntree15RLLRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLLRRRLL i else ntree15RLLRRRLR (i - 7)

def ntree15RLLRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨374,by decide⟩,⟨1167,by decide⟩,⟨374,by decide⟩] | 1 => ![⟨413,by decide⟩,⟨1168,by decide⟩,⟨1153,by decide⟩] | 2 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨1170,by decide⟩,⟨1170,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1171,by decide⟩,⟨1171,by decide⟩] | 5 => ![⟨945,by decide⟩,⟨1172,by decide⟩,⟨1171,by decide⟩] | 6 => ![⟨1173,by decide⟩,⟨1173,by decide⟩,⟨1084,by decide⟩] | _ => ![⟨1174,by decide⟩,⟨1174,by decide⟩,⟨1174,by decide⟩]

def ntree15RLLRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1169,by decide⟩,⟨1175,by decide⟩,⟨1175,by decide⟩] | 1 => ![⟨1174,by decide⟩,⟨1176,by decide⟩,⟨1176,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1177,by decide⟩,⟨1177,by decide⟩] | 3 => ![⟨374,by decide⟩,⟨1178,by decide⟩,⟨1178,by decide⟩] | 4 => ![⟨1179,by decide⟩,⟨1179,by decide⟩,⟨1179,by decide⟩] | 5 => ![⟨1180,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1181,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1182,by decide⟩,⟨1182,by decide⟩,⟨1169,by decide⟩]

def ntree15RLLRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RLLRRRRL i else ntree15RLLRRRRR (i - 8)

def ntree15RLLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLLRRRL i else ntree15RLLRRRR (i - 15)

def ntree15RLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLLRRL i else ntree15RLLRRR (i - 30)

def ntree15RLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15RLLRL i else ntree15RLLRR (i - 60)

def ntree15RLL (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15RLLL i else ntree15RLLR (i - 121)

def ntree15RLRLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1183,by decide⟩,⟨1183,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1182,by decide⟩,⟨1184,by decide⟩,⟨1170,by decide⟩] | 2 => ![⟨1183,by decide⟩,⟨1185,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨1186,by decide⟩,⟨1171,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1187,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1188,by decide⟩,⟨1188,by decide⟩,⟨1179,by decide⟩] | _ => ![⟨1189,by decide⟩,⟨1189,by decide⟩,⟨826,by decide⟩]

def ntree15RLRLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1190,by decide⟩,⟨1190,by decide⟩,⟨1169,by decide⟩] | 1 => ![⟨1191,by decide⟩,⟨1191,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1192,by decide⟩,⟨0,by decide⟩,⟨1192,by decide⟩] | 3 => ![⟨1193,by decide⟩,⟨826,by decide⟩,⟨1193,by decide⟩] | 4 => ![⟨1194,by decide⟩,⟨1194,by decide⟩,⟨1174,by decide⟩] | 5 => ![⟨1195,by decide⟩,⟨1195,by decide⟩,⟨374,by decide⟩] | 6 => ![⟨1182,by decide⟩,⟨1196,by decide⟩,⟨1175,by decide⟩] | _ => ![⟨1194,by decide⟩,⟨1197,by decide⟩,⟨1176,by decide⟩]

def ntree15RLRLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRLLLLL i else ntree15RLRLLLLR (i - 7)

def ntree15RLRLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1195,by decide⟩,⟨1198,by decide⟩,⟨376,by decide⟩] | 1 => ![⟨1199,by decide⟩,⟨1199,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨1200,by decide⟩,⟨1200,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨1201,by decide⟩,⟨1169,by decide⟩] | 4 => ![⟨1199,by decide⟩,⟨1202,by decide⟩,⟨1170,by decide⟩] | 5 => ![⟨1200,by decide⟩,⟨1203,by decide⟩,⟨1,by decide⟩] | _ => ![⟨46,by decide⟩,⟨1204,by decide⟩,⟨1177,by decide⟩]

def ntree15RLRLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨410,by decide⟩,⟨1205,by decide⟩,⟨1178,by decide⟩] | 1 => ![⟨374,by decide⟩,⟨1206,by decide⟩,⟨374,by decide⟩] | 2 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1207,by decide⟩] | 3 => ![⟨1208,by decide⟩,⟨1169,by decide⟩,⟨1208,by decide⟩] | 4 => ![⟨1208,by decide⟩,⟨1170,by decide⟩,⟨1209,by decide⟩] | 5 => ![⟨977,by decide⟩,⟨1171,by decide⟩,⟨1210,by decide⟩] | 6 => ![⟨432,by decide⟩,⟨1181,by decide⟩,⟨432,by decide⟩] | _ => ![⟨1169,by decide⟩,⟨1211,by decide⟩,⟨1211,by decide⟩]

def ntree15RLRLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRLLLRL i else ntree15RLRLLLRR (i - 7)

def ntree15RLRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRLLLL i else ntree15RLRLLLR (i - 15)

def ntree15RLRLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1212,by decide⟩,⟨1212,by decide⟩,⟨1212,by decide⟩] | 1 => ![⟨1212,by decide⟩,⟨1213,by decide⟩,⟨1213,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1214,by decide⟩,⟨1214,by decide⟩] | 3 => ![⟨223,by decide⟩,⟨1215,by decide⟩,⟨1215,by decide⟩] | 4 => ![⟨1216,by decide⟩,⟨1182,by decide⟩,⟨1208,by decide⟩] | 5 => ![⟨1217,by decide⟩,⟨1183,by decide⟩,⟨977,by decide⟩] | _ => ![⟨1218,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩]

def ntree15RLRLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1219,by decide⟩,⟨989,by decide⟩,⟨1219,by decide⟩] | 1 => ![⟨1220,by decide⟩,⟨223,by decide⟩,⟨1220,by decide⟩] | 2 => ![⟨1221,by decide⟩,⟨994,by decide⟩,⟨1221,by decide⟩] | 3 => ![⟨1183,by decide⟩,⟨1222,by decide⟩,⟨979,by decide⟩] | 4 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1223,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1224,by decide⟩,⟨1169,by decide⟩,⟨1224,by decide⟩] | _ => ![⟨1225,by decide⟩,⟨0,by decide⟩,⟨1225,by decide⟩]

def ntree15RLRLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRLLRLL i else ntree15RLRLLRLR (i - 7)

def ntree15RLRLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1226,by decide⟩,⟨1174,by decide⟩,⟨1226,by decide⟩] | 1 => ![⟨1227,by decide⟩,⟨374,by decide⟩,⟨1227,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1228,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨432,by decide⟩,⟨1228,by decide⟩,⟨432,by decide⟩] | 4 => ![⟨556,by decide⟩,⟨1229,by decide⟩,⟨1229,by decide⟩] | 5 => ![⟨1230,by decide⟩,⟨1169,by decide⟩,⟨1230,by decide⟩] | _ => ![⟨1231,by decide⟩,⟨0,by decide⟩,⟨1231,by decide⟩]

def ntree15RLRLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1232,by decide⟩,⟨492,by decide⟩,⟨1231,by decide⟩] | 1 => ![⟨1233,by decide⟩,⟨1179,by decide⟩,⟨1233,by decide⟩] | 2 => ![⟨1234,by decide⟩,⟨1169,by decide⟩,⟨1234,by decide⟩] | 3 => ![⟨1235,by decide⟩,⟨826,by decide⟩,⟨1235,by decide⟩] | 4 => ![⟨1236,by decide⟩,⟨0,by decide⟩,⟨1236,by decide⟩] | 5 => ![⟨1169,by decide⟩,⟨1237,by decide⟩,⟨1169,by decide⟩] | 6 => ![⟨1238,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1239,by decide⟩,⟨1182,by decide⟩,⟨1230,by decide⟩]

def ntree15RLRLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRLLRRL i else ntree15RLRLLRRR (i - 7)

def ntree15RLRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRLLRL i else ntree15RLRLLRR (i - 15)

def ntree15RLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLRLLL i else ntree15RLRLLR (i - 30)

def ntree15RLRLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1240,by decide⟩,⟨1183,by decide⟩,⟨5,by decide⟩] | 1 => ![⟨1241,by decide⟩,⟨46,by decide⟩,⟨1231,by decide⟩] | 2 => ![⟨1242,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1243,by decide⟩,⟨1188,by decide⟩,⟨1233,by decide⟩] | 4 => ![⟨1244,by decide⟩,⟨1182,by decide⟩,⟨1234,by decide⟩] | 5 => ![⟨1245,by decide⟩,⟨1189,by decide⟩,⟨828,by decide⟩] | _ => ![⟨1246,by decide⟩,⟨1190,by decide⟩,⟨1230,by decide⟩]

def ntree15RLRLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1247,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 1 => ![⟨1248,by decide⟩,⟨1191,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨1249,by decide⟩,⟨855,by decide⟩,⟨1235,by decide⟩] | 3 => ![⟨1250,by decide⟩,⟨46,by decide⟩,⟨1236,by decide⟩] | 4 => ![⟨1251,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1252,by decide⟩,⟨1252,by decide⟩] | 6 => ![⟨374,by decide⟩,⟨1253,by decide⟩,⟨1253,by decide⟩] | _ => ![⟨1169,by decide⟩,⟨1254,by decide⟩,⟨1254,by decide⟩]

def ntree15RLRLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRLRLLL i else ntree15RLRLRLLR (i - 7)

def ntree15RLRLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1179,by decide⟩,⟨1255,by decide⟩,⟨1255,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨1256,by decide⟩,⟨1256,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨1257,by decide⟩,⟨1257,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1258,by decide⟩,⟨1258,by decide⟩] | 5 => ![⟨1259,by decide⟩,⟨1183,by decide⟩,⟨599,by decide⟩] | _ => ![⟨1260,by decide⟩,⟨989,by decide⟩,⟨1260,by decide⟩]

def ntree15RLRLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1261,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1182,by decide⟩,⟨1262,by decide⟩,⟨1254,by decide⟩] | 2 => ![⟨1183,by decide⟩,⟨1263,by decide⟩,⟨600,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨1264,by decide⟩,⟨1169,by decide⟩] | 4 => ![⟨1261,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩] | 5 => ![⟨1230,by decide⟩,⟨1254,by decide⟩,⟨1265,by decide⟩] | 6 => ![⟨1231,by decide⟩,⟨600,by decide⟩,⟨1266,by decide⟩] | _ => ![⟨1238,by decide⟩,⟨881,by decide⟩,⟨881,by decide⟩]

def ntree15RLRLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRLRLRL i else ntree15RLRLRLRR (i - 7)

def ntree15RLRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRLRLL i else ntree15RLRLRLR (i - 15)

def ntree15RLRLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1267,by decide⟩,⟨1169,by decide⟩,⟨1267,by decide⟩] | 1 => ![⟨1268,by decide⟩,⟨0,by decide⟩,⟨1268,by decide⟩] | 2 => ![⟨1269,by decide⟩,⟨1212,by decide⟩,⟨1269,by decide⟩] | 3 => ![⟨1270,by decide⟩,⟨223,by decide⟩,⟨1270,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨1271,by decide⟩,⟨1271,by decide⟩] | 5 => ![⟨556,by decide⟩,⟨1272,by decide⟩,⟨1272,by decide⟩] | _ => ![⟨557,by decide⟩,⟨1273,by decide⟩,⟨1273,by decide⟩]

def ntree15RLRLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1274,by decide⟩,⟨1274,by decide⟩] | 1 => ![⟨1084,by decide⟩,⟨1275,by decide⟩,⟨1275,by decide⟩] | 2 => ![⟨1276,by decide⟩,⟨1276,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1277,by decide⟩,⟨1276,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨1278,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1279,by decide⟩,⟨1279,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1276,by decide⟩,⟨1280,by decide⟩,⟨2,by decide⟩] | _ => ![⟨826,by decide⟩,⟨1281,by decide⟩,⟨1281,by decide⟩]

def ntree15RLRLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRLRRLL i else ntree15RLRLRRLR (i - 7)

def ntree15RLRLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1092,by decide⟩,⟨1282,by decide⟩,⟨1282,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1283,by decide⟩,⟨1283,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1284,by decide⟩,⟨1284,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1285,by decide⟩,⟨1285,by decide⟩] | 5 => ![⟨403,by decide⟩,⟨1286,by decide⟩,⟨1286,by decide⟩] | 6 => ![⟨1276,by decide⟩,⟨1287,by decide⟩,⟨837,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1288,by decide⟩,⟨1288,by decide⟩]

def ntree15RLRLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨374,by decide⟩,⟨1289,by decide⟩,⟨1289,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1290,by decide⟩] | 2 => ![⟨5,by decide⟩,⟨1288,by decide⟩,⟨1291,by decide⟩] | 3 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1292,by decide⟩] | 4 => ![⟨377,by decide⟩,⟨1289,by decide⟩,⟨1293,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1294,by decide⟩,⟨1294,by decide⟩] | 6 => ![⟨374,by decide⟩,⟨1295,by decide⟩,⟨1295,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1296,by decide⟩]

def ntree15RLRLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RLRLRRRL i else ntree15RLRLRRRR (i - 8)

def ntree15RLRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRLRRL i else ntree15RLRLRRR (i - 15)

def ntree15RLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLRLRL i else ntree15RLRLRR (i - 30)

def ntree15RLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15RLRLL i else ntree15RLRLR (i - 60)

def ntree15RLRRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1297,by decide⟩,⟨1297,by decide⟩] | 1 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1298,by decide⟩] | 2 => ![⟨1122,by decide⟩,⟨2,by decide⟩,⟨1299,by decide⟩] | 3 => ![⟨1300,by decide⟩,⟨1276,by decide⟩,⟨432,by decide⟩] | 4 => ![⟨1125,by decide⟩,⟨836,by decide⟩,⟨1301,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1302,by decide⟩,⟨1302,by decide⟩] | _ => ![⟨1130,by decide⟩,⟨1303,by decide⟩,⟨1303,by decide⟩]

def ntree15RLRRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨432,by decide⟩,⟨1304,by decide⟩,⟨1305,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1306,by decide⟩,⟨1306,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1304,by decide⟩,⟨1304,by decide⟩] | 3 => ![⟨1307,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1308,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨882,by decide⟩,⟨1309,by decide⟩,⟨882,by decide⟩] | 6 => ![⟨1310,by decide⟩,⟨403,by decide⟩,⟨403,by decide⟩] | _ => ![⟨1311,by decide⟩,⟨1311,by decide⟩,⟨0,by decide⟩]

def ntree15RLRRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRRLLLL i else ntree15RLRRLLLR (i - 7)

def ntree15RLRRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1311,by decide⟩,⟨1312,by decide⟩,⟨1297,by decide⟩] | 1 => ![⟨1313,by decide⟩,⟨1311,by decide⟩,⟨443,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨1288,by decide⟩,⟨1314,by decide⟩] | 3 => ![⟨1315,by decide⟩,⟨1315,by decide⟩,⟨1130,by decide⟩] | 4 => ![⟨1316,by decide⟩,⟨1316,by decide⟩,⟨1130,by decide⟩] | 5 => ![⟨1317,by decide⟩,⟨1311,by decide⟩,⟨1106,by decide⟩] | _ => ![⟨1122,by decide⟩,⟨879,by decide⟩,⟨1318,by decide⟩]

def ntree15RLRRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1311,by decide⟩,⟨1319,by decide⟩,⟨879,by decide⟩] | 1 => ![⟨432,by decide⟩,⟨837,by decide⟩,⟨1320,by decide⟩] | 2 => ![⟨1159,by decide⟩,⟨2,by decide⟩,⟨1321,by decide⟩] | 3 => ![⟨1160,by decide⟩,⟨837,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1161,by decide⟩,⟨841,by decide⟩,⟨1323,by decide⟩] | 5 => ![⟨5,by decide⟩,⟨1302,by decide⟩,⟨1324,by decide⟩] | 6 => ![⟨1162,by decide⟩,⟨1303,by decide⟩,⟨1325,by decide⟩] | _ => ![⟨1163,by decide⟩,⟨2,by decide⟩,⟨1326,by decide⟩]

def ntree15RLRRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRRLLRL i else ntree15RLRRLLRR (i - 7)

def ntree15RLRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRRLLL i else ntree15RLRRLLR (i - 15)

def ntree15RLRRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨469,by decide⟩,⟨1327,by decide⟩,⟨1328,by decide⟩] | 1 => ![⟨5,by decide⟩,⟨1306,by decide⟩,⟨1329,by decide⟩] | 2 => ![⟨432,by decide⟩,⟨837,by decide⟩,⟨1330,by decide⟩] | 3 => ![⟨470,by decide⟩,⟨1327,by decide⟩,⟨1327,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 5 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1331,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1332,by decide⟩]

def ntree15RLRRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1333,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1334,by decide⟩] | 2 => ![⟨1335,by decide⟩,⟨1335,by decide⟩,⟨1084,by decide⟩] | 3 => ![⟨1336,by decide⟩,⟨1336,by decide⟩,⟨1169,by decide⟩] | 4 => ![⟨1337,by decide⟩,⟨1337,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1338,by decide⟩,⟨1338,by decide⟩,⟨826,by decide⟩] | 6 => ![⟨1339,by decide⟩,⟨1339,by decide⟩,⟨374,by decide⟩] | _ => ![⟨1340,by decide⟩,⟨1340,by decide⟩,⟨1092,by decide⟩]

def ntree15RLRRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRRLRLL i else ntree15RLRRLRLR (i - 7)

def ntree15RLRRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1341,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1169,by decide⟩,⟨1342,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1343,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1169,by decide⟩,⟨1344,by decide⟩,⟨1344,by decide⟩] | _ => ![⟨504,by decide⟩,⟨837,by decide⟩,⟨1345,by decide⟩]

def ntree15RLRRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1346,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1347,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨725,by decide⟩,⟨1348,by decide⟩,⟨837,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1179,by decide⟩,⟨1349,by decide⟩,⟨1349,by decide⟩] | 5 => ![⟨1169,by decide⟩,⟨1350,by decide⟩,⟨1350,by decide⟩] | 6 => ![⟨826,by decide⟩,⟨1351,by decide⟩,⟨1351,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1352,by decide⟩,⟨1352,by decide⟩]

def ntree15RLRRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRRLRRL i else ntree15RLRRLRRR (i - 7)

def ntree15RLRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRRLRL i else ntree15RLRRLRR (i - 15)

def ntree15RLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLRRLL i else ntree15RLRRLR (i - 30)

def ntree15RLRRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1169,by decide⟩,⟨1353,by decide⟩,⟨1169,by decide⟩] | 1 => ![⟨1174,by decide⟩,⟨1354,by decide⟩,⟨1174,by decide⟩] | 2 => ![⟨374,by decide⟩,⟨1355,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨1336,by decide⟩,⟨1356,by decide⟩,⟨1344,by decide⟩] | 4 => ![⟨1169,by decide⟩,⟨1357,by decide⟩,⟨1169,by decide⟩] | 5 => ![⟨167,by decide⟩,⟨1358,by decide⟩,⟨837,by decide⟩] | _ => ![⟨167,by decide⟩,⟨1359,by decide⟩,⟨1288,by decide⟩]

def ntree15RLRRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨167,by decide⟩,⟨1360,by decide⟩,⟨837,by decide⟩] | 1 => ![⟨374,by decide⟩,⟨1361,by decide⟩,⟨374,by decide⟩] | 2 => ![⟨726,by decide⟩,⟨1362,by decide⟩,⟨1289,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1363,by decide⟩] | 4 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨1363,by decide⟩] | 5 => ![⟨1341,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 6 => ![⟨1364,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | _ => ![⟨1365,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15RLRRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRRRLLL i else ntree15RLRRRLLR (i - 7)

def ntree15RLRRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1366,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1367,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1368,by decide⟩,⟨943,by decide⟩,⟨432,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1369,by decide⟩] | 4 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨1369,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1370,by decide⟩,⟨1370,by decide⟩] | _ => ![⟨1371,by decide⟩,⟨167,by decide⟩,⟨1122,by decide⟩]

def ntree15RLRRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1372,by decide⟩,⟨1179,by decide⟩,⟨1179,by decide⟩] | 1 => ![⟨1373,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨1374,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 3 => ![⟨1375,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 4 => ![⟨1376,by decide⟩,⟨1336,by decide⟩,⟨1208,by decide⟩] | 5 => ![⟨1377,by decide⟩,⟨167,by decide⟩,⟨432,by decide⟩] | 6 => ![⟨1378,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | _ => ![⟨1379,by decide⟩,⟨167,by decide⟩,⟨432,by decide⟩]

def ntree15RLRRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRRRLRL i else ntree15RLRRRLRR (i - 7)

def ntree15RLRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRRRLL i else ntree15RLRRRLR (i - 15)

def ntree15RLRRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1380,by decide⟩,⟨954,by decide⟩,⟨1125,by decide⟩] | 1 => ![⟨1381,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1382,by decide⟩,⟨1382,by decide⟩,⟨1169,by decide⟩] | _ => ![⟨1383,by decide⟩,⟨1383,by decide⟩,⟨0,by decide⟩]

def ntree15RLRRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1384,by decide⟩,⟨1384,by decide⟩,⟨1212,by decide⟩] | 1 => ![⟨1385,by decide⟩,⟨1385,by decide⟩,⟨223,by decide⟩] | 2 => ![⟨223,by decide⟩,⟨1386,by decide⟩,⟨1386,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨432,by decide⟩,⟨1003,by decide⟩,⟨1387,by decide⟩] | 6 => ![⟨374,by decide⟩,⟨1388,by decide⟩,⟨1388,by decide⟩] | _ => ![⟨1208,by decide⟩,⟨1344,by decide⟩,⟨1389,by decide⟩]

def ntree15RLRRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RLRRRRLL i else ntree15RLRRRRLR (i - 7)

def ntree15RLRRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1390,by decide⟩] | 1 => ![⟨432,by decide⟩,⟨837,by decide⟩,⟨1391,by decide⟩] | 2 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1392,by decide⟩] | 3 => ![⟨1212,by decide⟩,⟨1212,by decide⟩,⟨1393,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1394,by decide⟩] | 5 => ![⟨432,by decide⟩,⟨837,by decide⟩,⟨1395,by decide⟩] | 6 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1396,by decide⟩] | _ => ![⟨518,by decide⟩,⟨1015,by decide⟩,⟨1397,by decide⟩]

def ntree15RLRRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1381,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | 1 => ![⟨556,by decide⟩,⟨1398,by decide⟩,⟨1398,by decide⟩] | 2 => ![⟨557,by decide⟩,⟨1399,by decide⟩,⟨1399,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨1400,by decide⟩,⟨1400,by decide⟩] | 4 => ![⟨1230,by decide⟩,⟨1400,by decide⟩,⟨1401,by decide⟩] | 5 => ![⟨1231,by decide⟩,⟨2,by decide⟩,⟨1402,by decide⟩] | 6 => ![⟨5,by decide⟩,⟨1403,by decide⟩,⟨1404,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1403,by decide⟩,⟨1403,by decide⟩]

def ntree15RLRRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RLRRRRRL i else ntree15RLRRRRRR (i - 8)

def ntree15RLRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RLRRRRL i else ntree15RLRRRRR (i - 15)

def ntree15RLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RLRRRL i else ntree15RLRRRR (i - 30)

def ntree15RLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15RLRRL i else ntree15RLRRR (i - 60)

def ntree15RLR (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15RLRL i else ntree15RLRR (i - 121)

def ntree15RL (i : Nat) : Fin 3 → Fin 1868 := if i < 242 then ntree15RLL i else ntree15RLR (i - 242)

def ntree15RRLLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1405,by decide⟩] | 1 => ![⟨1406,by decide⟩,⟨1336,by decide⟩,⟨1230,by decide⟩] | 2 => ![⟨1407,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 3 => ![⟨1408,by decide⟩,⟨1276,by decide⟩,⟨1231,by decide⟩] | 4 => ![⟨1169,by decide⟩,⟨1409,by decide⟩,⟨1409,by decide⟩] | 5 => ![⟨1174,by decide⟩,⟨1410,by decide⟩,⟨1410,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1411,by decide⟩,⟨1411,by decide⟩]

def ntree15RRLLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨374,by decide⟩,⟨1412,by decide⟩,⟨1412,by decide⟩] | 1 => ![⟨1336,by decide⟩,⟨1413,by decide⟩,⟨1400,by decide⟩] | 2 => ![⟨1276,by decide⟩,⟨1414,by decide⟩,⟨1403,by decide⟩] | 3 => ![⟨1106,by decide⟩,⟨1403,by decide⟩,⟨1415,by decide⟩] | 4 => ![⟨1416,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 5 => ![⟨1169,by decide⟩,⟨1417,by decide⟩,⟨1417,by decide⟩] | 6 => ![⟨1212,by decide⟩,⟨1418,by decide⟩,⟨1418,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1419,by decide⟩,⟨1419,by decide⟩]

def ntree15RRLLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLLLLLL i else ntree15RRLLLLLR (i - 7)

def ntree15RRLLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨223,by decide⟩,⟨1420,by decide⟩,⟨1420,by decide⟩] | 1 => ![⟨1231,by decide⟩,⟨1297,by decide⟩,⟨1421,by decide⟩] | 2 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1422,by decide⟩] | 3 => ![⟨1267,by decide⟩,⟨1400,by decide⟩,⟨1423,by decide⟩] | 4 => ![⟨1268,by decide⟩,⟨2,by decide⟩,⟨1424,by decide⟩] | 5 => ![⟨1230,by decide⟩,⟨1417,by decide⟩,⟨1425,by decide⟩] | _ => ![⟨1269,by decide⟩,⟨1418,by decide⟩,⟨1426,by decide⟩]

def ntree15RRLLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1270,by decide⟩,⟨337,by decide⟩,⟨1427,by decide⟩] | 1 => ![⟨5,by decide⟩,⟨1419,by decide⟩,⟨1428,by decide⟩] | 2 => ![⟨354,by decide⟩,⟨1420,by decide⟩,⟨1429,by decide⟩] | 3 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1430,by decide⟩] | 4 => ![⟨556,by decide⟩,⟨1431,by decide⟩,⟨1431,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1432,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1433,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1434,by decide⟩,⟨1435,by decide⟩,⟨1,by decide⟩]

def ntree15RRLLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLLLLRL i else ntree15RRLLLLRR (i - 7)

def ntree15RRLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLLLLL i else ntree15RRLLLLR (i - 15)

def ntree15RRLLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨10,by decide⟩,⟨1432,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1436,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1437,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨1438,by decide⟩,⟨826,by decide⟩] | 4 => ![⟨1439,by decide⟩,⟨826,by decide⟩,⟨1439,by decide⟩] | 5 => ![⟨1440,by decide⟩,⟨0,by decide⟩,⟨1440,by decide⟩] | _ => ![⟨1441,by decide⟩,⟨32,by decide⟩,⟨1440,by decide⟩]

def ntree15RRLLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1440,by decide⟩,⟨2,by decide⟩,⟨1442,by decide⟩] | 1 => ![⟨1439,by decide⟩,⟨836,by decide⟩,⟨1443,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1444,by decide⟩] | 3 => ![⟨1445,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1446,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨1447,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1448,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1449,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15RRLLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLLLRLL i else ntree15RRLLLRLR (i - 7)

def ntree15RRLLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1450,by decide⟩] | 1 => ![⟨1451,by decide⟩,⟨1,by decide⟩,⟨1452,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨837,by decide⟩,⟨1453,by decide⟩] | 3 => ![⟨1454,by decide⟩,⟨839,by decide⟩,⟨1455,by decide⟩] | 4 => ![⟨1456,by decide⟩,⟨1457,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1458,by decide⟩,⟨1459,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1458,by decide⟩,⟨1460,by decide⟩,⟨837,by decide⟩]

def ntree15RRLLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1461,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1462,by decide⟩] | 3 => ![⟨70,by decide⟩,⟨837,by decide⟩,⟨1463,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1451,by decide⟩,⟨0,by decide⟩,⟨1451,by decide⟩] | _ => ![⟨1454,by decide⟩,⟨838,by decide⟩,⟨1454,by decide⟩]

def ntree15RRLLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLLLRRL i else ntree15RRLLLRRR (i - 7)

def ntree15RRLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLLLRL i else ntree15RRLLLRR (i - 15)

def ntree15RRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRLLLL i else ntree15RRLLLR (i - 30)

def ntree15RRLLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1464,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨879,by decide⟩,⟨1465,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨1466,by decide⟩,⟨881,by decide⟩] | 3 => ![⟨1467,by decide⟩,⟨1468,by decide⟩,⟨883,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨881,by decide⟩,⟨1469,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1470,by decide⟩] | _ => ![⟨1471,by decide⟩,⟨2,by decide⟩,⟨1472,by decide⟩]

def ntree15RRLLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1473,by decide⟩,⟨885,by decide⟩,⟨1474,by decide⟩] | 1 => ![⟨882,by decide⟩,⟨1475,by decide⟩,⟨882,by decide⟩] | 2 => ![⟨884,by decide⟩,⟨884,by decide⟩,⟨1476,by decide⟩] | 3 => ![⟨1477,by decide⟩,⟨1477,by decide⟩,⟨826,by decide⟩] | 4 => ![⟨1478,by decide⟩,⟨1478,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1478,by decide⟩,⟨1479,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨1477,by decide⟩,⟨1480,by decide⟩,⟨827,by decide⟩] | _ => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1481,by decide⟩]

def ntree15RRLLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLLRLLL i else ntree15RRLLRLLR (i - 7)

def ntree15RRLLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1482,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨826,by decide⟩,⟨1483,by decide⟩,⟨826,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1477,by decide⟩,⟨1484,by decide⟩,⟨892,by decide⟩] | 4 => ![⟨1478,by decide⟩,⟨1485,by decide⟩,⟨90,by decide⟩] | 5 => ![⟨1486,by decide⟩,⟨1477,by decide⟩,⟨1439,by decide⟩] | _ => ![⟨1487,by decide⟩,⟨76,by decide⟩,⟨1440,by decide⟩]

def ntree15RRLLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1488,by decide⟩,⟨1478,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1489,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1439,by decide⟩,⟨892,by decide⟩,⟨1490,by decide⟩] | 3 => ![⟨1440,by decide⟩,⟨90,by decide⟩,⟨1491,by decide⟩] | 4 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨1444,by decide⟩] | 5 => ![⟨1492,by decide⟩,⟨1478,by decide⟩,⟨59,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1493,by decide⟩,⟨0,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1493,by decide⟩,⟨10,by decide⟩]

def ntree15RRLLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLLRLRL i else ntree15RRLLRLRR (i - 7)

def ntree15RRLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLLRLL i else ntree15RRLLRLR (i - 15)

def ntree15RRLLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1494,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨1494,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1495,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨76,by decide⟩,⟨1496,by decide⟩,⟨924,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1497,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1498,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1499,by decide⟩,⟨76,by decide⟩,⟨1500,by decide⟩]

def ntree15RRLLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1501,by decide⟩,⟨0,by decide⟩,⟨1502,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨1503,by decide⟩,⟨837,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1504,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1505,by decide⟩,⟨1506,by decide⟩,⟨841,by decide⟩] | 4 => ![⟨1507,by decide⟩,⟨1508,by decide⟩,⟨2,by decide⟩] | 5 => ![⟨1501,by decide⟩,⟨837,by decide⟩,⟨1509,by decide⟩] | 6 => ![⟨1505,by decide⟩,⟨1505,by decide⟩,⟨840,by decide⟩] | _ => ![⟨1507,by decide⟩,⟨1507,by decide⟩,⟨0,by decide⟩]

def ntree15RRLLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLLRRLL i else ntree15RRLLRRLR (i - 7)

def ntree15RRLLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨141,by decide⟩,⟨1510,by decide⟩,⟨837,by decide⟩] | 4 => ![⟨1501,by decide⟩,⟨881,by decide⟩,⟨1511,by decide⟩] | 5 => ![⟨1458,by decide⟩,⟨1512,by decide⟩,⟨881,by decide⟩] | 6 => ![⟨1513,by decide⟩,⟨1514,by decide⟩,⟨1515,by decide⟩] | _ => ![⟨1516,by decide⟩,⟨1517,by decide⟩,⟨1518,by decide⟩]

def ntree15RRLLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1519,by decide⟩,⟨1520,by decide⟩,⟨1521,by decide⟩] | 1 => ![⟨1522,by decide⟩,⟨1522,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1523,by decide⟩,⟨1523,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1524,by decide⟩,⟨1522,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1525,by decide⟩,⟨1525,by decide⟩,⟨826,by decide⟩] | 6 => ![⟨1526,by decide⟩,⟨1525,by decide⟩,⟨1439,by decide⟩] | _ => ![⟨1527,by decide⟩,⟨1522,by decide⟩,⟨1440,by decide⟩]

def ntree15RRLLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RRLLRRRL i else ntree15RRLLRRRR (i - 8)

def ntree15RRLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLLRRL i else ntree15RRLLRRR (i - 15)

def ntree15RRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRLLRL i else ntree15RRLLRR (i - 30)

def ntree15RRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15RRLLL i else ntree15RRLLR (i - 60)

def ntree15RRLRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1528,by decide⟩] | 1 => ![⟨1522,by decide⟩,⟨1529,by decide⟩,⟨837,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨1530,by decide⟩,⟨837,by decide⟩] | 3 => ![⟨1531,by decide⟩,⟨1532,by decide⟩,⟨837,by decide⟩] | 4 => ![⟨1533,by decide⟩,⟨1534,by decide⟩,⟨839,by decide⟩] | 5 => ![⟨1535,by decide⟩,⟨1535,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1535,by decide⟩,⟨1536,by decide⟩,⟨1,by decide⟩]

def ntree15RRLRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨826,by decide⟩,⟨1537,by decide⟩,⟨826,by decide⟩] | 1 => ![⟨1538,by decide⟩,⟨1538,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1538,by decide⟩,⟨1539,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨1540,by decide⟩,⟨1540,by decide⟩,⟨826,by decide⟩] | 4 => ![⟨1540,by decide⟩,⟨1541,by decide⟩,⟨827,by decide⟩] | 5 => ![⟨1525,by decide⟩,⟨1542,by decide⟩,⟨861,by decide⟩] | 6 => ![⟨163,by decide⟩,⟨1543,by decide⟩,⟨837,by decide⟩] | _ => ![⟨826,by decide⟩,⟨1544,by decide⟩,⟨826,by decide⟩]

def ntree15RRLRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLRLLLL i else ntree15RRLRLLLR (i - 7)

def ntree15RRLRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨202,by decide⟩,⟨0,by decide⟩,⟨202,by decide⟩] | 1 => ![⟨1531,by decide⟩,⟨1531,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1533,by decide⟩,⟨1533,by decide⟩,⟨838,by decide⟩] | 3 => ![⟨207,by decide⟩,⟨205,by decide⟩,⟨207,by decide⟩] | 4 => ![⟨1471,by decide⟩,⟨0,by decide⟩,⟨1471,by decide⟩] | 5 => ![⟨1473,by decide⟩,⟨884,by decide⟩,⟨1473,by decide⟩] | _ => ![⟨1523,by decide⟩,⟨1545,by decide⟩,⟨979,by decide⟩]

def ntree15RRLRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1440,by decide⟩,⟨979,by decide⟩,⟨1546,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨1547,by decide⟩,⟨988,by decide⟩] | 2 => ![⟨1548,by decide⟩,⟨1548,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1548,by decide⟩,⟨1549,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨1550,by decide⟩,⟨1550,by decide⟩,⟨989,by decide⟩] | 5 => ![⟨1550,by decide⟩,⟨1551,by decide⟩,⟨990,by decide⟩] | 6 => ![⟨1477,by decide⟩,⟨1552,by decide⟩,⟨993,by decide⟩] | _ => ![⟨1553,by decide⟩,⟨1553,by decide⟩,⟨223,by decide⟩]

def ntree15RRLRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLRLLRL i else ntree15RRLRLLRR (i - 7)

def ntree15RRLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLRLLL i else ntree15RRLRLLR (i - 15)

def ntree15RRLRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1553,by decide⟩,⟨1554,by decide⟩,⟨224,by decide⟩] | 1 => ![⟨1555,by decide⟩,⟨1555,by decide⟩,⟨994,by decide⟩] | 2 => ![⟨1555,by decide⟩,⟨1556,by decide⟩,⟨995,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨1557,by decide⟩,⟨826,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨1558,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨994,by decide⟩,⟨1559,by decide⟩,⟨994,by decide⟩] | _ => ![⟨1560,by decide⟩,⟨1523,by decide⟩,⟨236,by decide⟩]

def ntree15RRLRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨10,by decide⟩,⟨1003,by decide⟩,⟨1561,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1562,by decide⟩] | 2 => ![⟨1563,by decide⟩,⟨1563,by decide⟩,⟨947,by decide⟩] | 3 => ![⟨1564,by decide⟩,⟨1564,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1565,by decide⟩,⟨1565,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1566,by decide⟩,⟨1566,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1567,by decide⟩,⟨1567,by decide⟩,⟨884,by decide⟩] | _ => ![⟨163,by decide⟩,⟨1568,by decide⟩,⟨1003,by decide⟩]

def ntree15RRLRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLRLRLL i else ntree15RRLRLRLR (i - 7)

def ntree15RRLRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1569,by decide⟩,⟨1569,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨1570,by decide⟩,⟨1017,by decide⟩] | 3 => ![⟨257,by decide⟩,⟨1571,by decide⟩,⟨1019,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨1572,by decide⟩,⟨837,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨1573,by decide⟩,⟨1018,by decide⟩] | _ => ![⟨76,by decide⟩,⟨1574,by decide⟩,⟨1020,by decide⟩]

def ntree15RRLRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨223,by decide⟩,⟨1575,by decide⟩,⟨223,by decide⟩] | 1 => ![⟨226,by decide⟩,⟨1576,by decide⟩,⟨1021,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨1577,by decide⟩,⟨837,by decide⟩] | 3 => ![⟨273,by decide⟩,⟨1578,by decide⟩,⟨1015,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨1579,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨236,by decide⟩,⟨1003,by decide⟩,⟨1580,by decide⟩] | 6 => ![⟨239,by decide⟩,⟨1015,by decide⟩,⟨1581,by decide⟩] | _ => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1582,by decide⟩]

def ntree15RRLRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLRLRRL i else ntree15RRLRLRRR (i - 7)

def ntree15RRLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLRLRL i else ntree15RRLRLRR (i - 15)

def ntree15RRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRLRLL i else ntree15RRLRLR (i - 30)

def ntree15RRLRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1583,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1522,by decide⟩,⟨1584,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨1585,by decide⟩,⟨1030,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨1586,by decide⟩,⟨826,by decide⟩] | 4 => ![⟨1525,by decide⟩,⟨1587,by decide⟩,⟨836,by decide⟩] | 5 => ![⟨1588,by decide⟩,⟨0,by decide⟩,⟨1588,by decide⟩] | _ => ![⟨1588,by decide⟩,⟨2,by decide⟩,⟨1589,by decide⟩]

def ntree15RRLRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1590,by decide⟩,⟨163,by decide⟩,⟨1588,by decide⟩] | 1 => ![⟨838,by decide⟩,⟨838,by decide⟩,⟨1591,by decide⟩] | 2 => ![⟨1592,by decide⟩,⟨0,by decide⟩,⟨1592,by decide⟩] | 3 => ![⟨1592,by decide⟩,⟨1032,by decide⟩,⟨1593,by decide⟩] | 4 => ![⟨1594,by decide⟩,⟨189,by decide⟩,⟨1592,by decide⟩] | 5 => ![⟨189,by decide⟩,⟨1595,by decide⟩,⟨1035,by decide⟩] | 6 => ![⟨1596,by decide⟩,⟨1523,by decide⟩,⟨1592,by decide⟩] | _ => ![⟨1597,by decide⟩,⟨205,by decide⟩,⟨205,by decide⟩]

def ntree15RRLRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLRRLLL i else ntree15RRLRRLLR (i - 7)

def ntree15RRLRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1598,by decide⟩,⟨947,by decide⟩,⟨1598,by decide⟩] | 1 => ![⟨1599,by decide⟩,⟨947,by decide⟩,⟨1599,by decide⟩] | 2 => ![⟨1592,by decide⟩,⟨879,by decide⟩,⟨1600,by decide⟩] | 3 => ![⟨1522,by decide⟩,⟨1601,by decide⟩,⟨879,by decide⟩] | 4 => ![⟨1602,by decide⟩,⟨0,by decide⟩,⟨1602,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1603,by decide⟩,⟨76,by decide⟩,⟨1588,by decide⟩]

def ntree15RRLRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1588,by decide⟩,⟨881,by decide⟩,⟨1604,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1605,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨1606,by decide⟩,⟨1035,by decide⟩] | 3 => ![⟨223,by decide⟩,⟨1607,by decide⟩,⟨223,by decide⟩] | 4 => ![⟨226,by decide⟩,⟨1608,by decide⟩,⟨1064,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨1609,by decide⟩,⟨1028,by decide⟩] | 6 => ![⟨1563,by decide⟩,⟨1610,by decide⟩,⟨1029,by decide⟩] | _ => ![⟨1564,by decide⟩,⟨1611,by decide⟩,⟨2,by decide⟩]

def ntree15RRLRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLRRLRL i else ntree15RRLRRLRR (i - 7)

def ntree15RRLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLRRLL i else ntree15RRLRRLR (i - 15)

def ntree15RRLRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1566,by decide⟩,⟨1612,by decide⟩,⟨881,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨1613,by decide⟩,⟨881,by decide⟩] | 2 => ![⟨1565,by decide⟩,⟨1614,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨1567,by decide⟩,⟨1615,by decide⟩,⟨885,by decide⟩] | 4 => ![⟨257,by decide⟩,⟨1616,by decide⟩,⟨1080,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨1617,by decide⟩,⟨1031,by decide⟩] | _ => ![⟨163,by decide⟩,⟨1618,by decide⟩,⟨881,by decide⟩]

def ntree15RRLRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1619,by decide⟩,⟨0,by decide⟩,⟨1619,by decide⟩] | 1 => ![⟨1620,by decide⟩,⟨1084,by decide⟩,⟨1620,by decide⟩] | 2 => ![⟨1621,by decide⟩,⟨1621,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1622,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1621,by decide⟩,⟨1623,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨1624,by decide⟩,⟨1624,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1625,by decide⟩,⟨1621,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1626,by decide⟩,⟨374,by decide⟩,⟨1626,by decide⟩]

def ntree15RRLRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRLRRRLL i else ntree15RRLRRRLR (i - 7)

def ntree15RRLRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1627,by decide⟩,⟨1092,by decide⟩,⟨1627,by decide⟩] | 1 => ![⟨1628,by decide⟩,⟨0,by decide⟩,⟨1628,by decide⟩] | 2 => ![⟨1629,by decide⟩,⟨0,by decide⟩,⟨1629,by decide⟩] | 3 => ![⟨1630,by decide⟩,⟨840,by decide⟩,⟨1630,by decide⟩] | 4 => ![⟨1631,by decide⟩,⟨0,by decide⟩,⟨1631,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1632,by decide⟩] | 6 => ![⟨1631,by decide⟩,⟨1,by decide⟩,⟨1633,by decide⟩] | _ => ![⟨1634,by decide⟩,⟨826,by decide⟩,⟨1634,by decide⟩]

def ntree15RRLRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1635,by decide⟩] | 1 => ![⟨1634,by decide⟩,⟨827,by decide⟩,⟨1636,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨1621,by decide⟩,⟨385,by decide⟩] | 3 => ![⟨1638,by decide⟩,⟨0,by decide⟩,⟨1638,by decide⟩] | 4 => ![⟨1639,by decide⟩,⟨826,by decide⟩,⟨1639,by decide⟩] | 5 => ![⟨385,by decide⟩,⟨0,by decide⟩,⟨385,by decide⟩] | 6 => ![⟨1640,by decide⟩,⟨0,by decide⟩,⟨1640,by decide⟩] | _ => ![⟨1641,by decide⟩,⟨0,by decide⟩,⟨1641,by decide⟩]

def ntree15RRLRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RRLRRRRL i else ntree15RRLRRRRR (i - 8)

def ntree15RRLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRLRRRL i else ntree15RRLRRRR (i - 15)

def ntree15RRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRLRRL i else ntree15RRLRRR (i - 30)

def ntree15RRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15RRLRL i else ntree15RRLRR (i - 60)

def ntree15RRL (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15RRLL i else ntree15RRLR (i - 121)

def ntree15RRRLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨385,by decide⟩,⟨0,by decide⟩,⟨385,by decide⟩] | 1 => ![⟨385,by decide⟩,⟨1132,by decide⟩,⟨1642,by decide⟩] | 2 => ![⟨385,by decide⟩,⟨881,by decide⟩,⟨1643,by decide⟩] | 3 => ![⟨1644,by decide⟩,⟨0,by decide⟩,⟨1644,by decide⟩] | 4 => ![⟨1644,by decide⟩,⟨1,by decide⟩,⟨1645,by decide⟩] | 5 => ![⟨1646,by decide⟩,⟨881,by decide⟩,⟨1647,by decide⟩] | _ => ![⟨1648,by decide⟩,⟨883,by decide⟩,⟨1649,by decide⟩]

def ntree15RRRLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨10,by decide⟩,⟨1129,by decide⟩,⟨1650,by decide⟩] | 1 => ![⟨1651,by decide⟩,⟨1130,by decide⟩,⟨1651,by decide⟩] | 2 => ![⟨1651,by decide⟩,⟨1131,by decide⟩,⟨1652,by decide⟩] | 3 => ![⟨1653,by decide⟩,⟨0,by decide⟩,⟨1653,by decide⟩] | 4 => ![⟨1653,by decide⟩,⟨1,by decide⟩,⟨1654,by decide⟩] | 5 => ![⟨402,by decide⟩,⟨1139,by decide⟩,⟨1655,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1133,by decide⟩,⟨1656,by decide⟩] | _ => ![⟨385,by decide⟩,⟨881,by decide⟩,⟨1657,by decide⟩]

def ntree15RRRLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRLLLLL i else ntree15RRRLLLLR (i - 7)

def ntree15RRRLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1646,by decide⟩,⟨0,by decide⟩,⟨1646,by decide⟩] | 1 => ![⟨1648,by decide⟩,⟨882,by decide⟩,⟨1648,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1658,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1659,by decide⟩] | 4 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1660,by decide⟩] | 5 => ![⟨1621,by decide⟩,⟨1661,by decide⟩,⟨881,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1153,by decide⟩,⟨1662,by decide⟩]

def ntree15RRRLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨384,by decide⟩,⟨1154,by decide⟩,⟨1663,by decide⟩] | 1 => ![⟨840,by decide⟩,⟨1664,by decide⟩,⟨840,by decide⟩] | 2 => ![⟨1665,by decide⟩,⟨470,by decide⟩,⟨470,by decide⟩] | 3 => ![⟨1666,by decide⟩,⟨1666,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1667,by decide⟩,⟨1666,by decide⟩,⟨1641,by decide⟩] | 5 => ![⟨1631,by decide⟩,⟨924,by decide⟩,⟨1668,by decide⟩] | 6 => ![⟨1666,by decide⟩,⟨1669,by decide⟩,⟨924,by decide⟩] | _ => ![⟨1670,by decide⟩,⟨1670,by decide⟩,⟨1130,by decide⟩]

def ntree15RRRLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRLLLRL i else ntree15RRRLLLRR (i - 7)

def ntree15RRRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRLLLL i else ntree15RRRLLLR (i - 15)

def ntree15RRRLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1671,by decide⟩,⟨1671,by decide⟩,⟨1130,by decide⟩] | 1 => ![⟨1666,by decide⟩,⟨1672,by decide⟩,⟨1105,by decide⟩] | 2 => ![⟨1673,by decide⟩,⟨1666,by decide⟩,⟨400,by decide⟩] | 3 => ![⟨400,by decide⟩,⟨1153,by decide⟩,⟨1674,by decide⟩] | 4 => ![⟨374,by decide⟩,⟨1675,by decide⟩,⟨374,by decide⟩] | 5 => ![⟨1676,by decide⟩,⟨1169,by decide⟩,⟨1676,by decide⟩] | _ => ![⟨1676,by decide⟩,⟨1170,by decide⟩,⟨1677,by decide⟩]

def ntree15RRRLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1678,by decide⟩,⟨0,by decide⟩,⟨1678,by decide⟩] | 1 => ![⟨1678,by decide⟩,⟨1,by decide⟩,⟨1679,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1171,by decide⟩,⟨1680,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1681,by decide⟩] | 4 => ![⟨1682,by decide⟩,⟨1682,by decide⟩,⟨1084,by decide⟩] | 5 => ![⟨1683,by decide⟩,⟨1683,by decide⟩,⟨1169,by decide⟩] | 6 => ![⟨1169,by decide⟩,⟨1684,by decide⟩,⟨1169,by decide⟩] | _ => ![⟨1683,by decide⟩,⟨1685,by decide⟩,⟨1170,by decide⟩]

def ntree15RRRLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRLLRLL i else ntree15RRRLLRLR (i - 7)

def ntree15RRRLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1621,by decide⟩,⟨1686,by decide⟩,⟨1171,by decide⟩] | 1 => ![⟨1687,by decide⟩,⟨1687,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1688,by decide⟩,⟨1688,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨1689,by decide⟩,⟨1689,by decide⟩,⟨826,by decide⟩] | 4 => ![⟨1690,by decide⟩,⟨1690,by decide⟩,⟨1092,by decide⟩] | 5 => ![⟨1691,by decide⟩,⟨1683,by decide⟩,⟨1676,by decide⟩] | _ => ![⟨1692,by decide⟩,⟨1621,by decide⟩,⟨1678,by decide⟩]

def ntree15RRRLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1693,by decide⟩,⟨1179,by decide⟩,⟨1693,by decide⟩] | 1 => ![⟨1694,by decide⟩,⟨1169,by decide⟩,⟨1694,by decide⟩] | 2 => ![⟨1695,by decide⟩,⟨826,by decide⟩,⟨1695,by decide⟩] | 3 => ![⟨1696,by decide⟩,⟨0,by decide⟩,⟨1696,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1697,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨1697,by decide⟩] | 6 => ![⟨1678,by decide⟩,⟨1105,by decide⟩,⟨1698,by decide⟩] | _ => ![⟨1641,by decide⟩,⟨1171,by decide⟩,⟨1699,by decide⟩]

def ntree15RRRLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRLLRRL i else ntree15RRRLLRRR (i - 7)

def ntree15RRRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRLLRL i else ntree15RRRLLRR (i - 15)

def ntree15RRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRRLLL i else ntree15RRRLLR (i - 30)

def ntree15RRRLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1700,by decide⟩,⟨989,by decide⟩,⟨1700,by decide⟩] | 1 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1701,by decide⟩] | 2 => ![⟨1702,by decide⟩,⟨1169,by decide⟩,⟨1702,by decide⟩] | 3 => ![⟨1702,by decide⟩,⟨1170,by decide⟩,⟨1703,by decide⟩] | 4 => ![⟨1704,by decide⟩,⟨0,by decide⟩,⟨1704,by decide⟩] | 5 => ![⟨1704,by decide⟩,⟨1,by decide⟩,⟨1705,by decide⟩] | _ => ![⟨1676,by decide⟩,⟨1211,by decide⟩,⟨1706,by decide⟩]

def ntree15RRRLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1707,by decide⟩,⟨1212,by decide⟩,⟨1707,by decide⟩] | 1 => ![⟨1707,by decide⟩,⟨1213,by decide⟩,⟨1708,by decide⟩] | 2 => ![⟨1709,by decide⟩,⟨223,by decide⟩,⟨1709,by decide⟩] | 3 => ![⟨1709,by decide⟩,⟨224,by decide⟩,⟨1710,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1214,by decide⟩,⟨1711,by decide⟩] | 5 => ![⟨239,by decide⟩,⟨1215,by decide⟩,⟨1712,by decide⟩] | 6 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1713,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1714,by decide⟩]

def ntree15RRRLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRLRLLL i else ntree15RRRLRLLR (i - 7)

def ntree15RRRLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨1714,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1169,by decide⟩,⟨1715,by decide⟩,⟨1169,by decide⟩] | 3 => ![⟨1716,by decide⟩,⟨1716,by decide⟩,⟨1169,by decide⟩] | 4 => ![⟨1717,by decide⟩,⟨1717,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1718,by decide⟩,⟨1718,by decide⟩,⟨1212,by decide⟩] | _ => ![⟨1719,by decide⟩,⟨1719,by decide⟩,⟨223,by decide⟩]

def ntree15RRRLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1720,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1721,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1722,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1723,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1724,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1725,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 6 => ![⟨1726,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1727,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15RRRLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRLRLRL i else ntree15RRRLRLRR (i - 7)

def ntree15RRRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRLRLL i else ntree15RRRLRLR (i - 15)

def ntree15RRRLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1728,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1729,by decide⟩,⟨1169,by decide⟩,⟨1729,by decide⟩] | 2 => ![⟨1730,by decide⟩,⟨1522,by decide⟩,⟨385,by decide⟩] | 3 => ![⟨1731,by decide⟩,⟨163,by decide⟩,⟨1631,by decide⟩] | 4 => ![⟨385,by decide⟩,⟨1724,by decide⟩,⟨385,by decide⟩] | 5 => ![⟨1732,by decide⟩,⟨1179,by decide⟩,⟨1179,by decide⟩] | _ => ![⟨1733,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩]

def ntree15RRRLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1734,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 1 => ![⟨1735,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨1736,by decide⟩,⟨1683,by decide⟩,⟨1729,by decide⟩] | 3 => ![⟨1737,by decide⟩,⟨163,by decide⟩,⟨385,by decide⟩] | 4 => ![⟨1738,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨1739,by decide⟩,⟨163,by decide⟩,⟨385,by decide⟩] | 6 => ![⟨1740,by decide⟩,⟨1525,by decide⟩,⟨1634,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15RRRLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRLRRLL i else ntree15RRRLRRLR (i - 7)

def ntree15RRRLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨385,by decide⟩,⟨1035,by decide⟩,⟨1741,by decide⟩] | 3 => ![⟨1742,by decide⟩,⟨1169,by decide⟩,⟨1742,by decide⟩] | 4 => ![⟨1743,by decide⟩,⟨1174,by decide⟩,⟨1743,by decide⟩] | 5 => ![⟨1744,by decide⟩,⟨0,by decide⟩,⟨1744,by decide⟩] | 6 => ![⟨1745,by decide⟩,⟨374,by decide⟩,⟨1745,by decide⟩] | _ => ![⟨1169,by decide⟩,⟨1746,by decide⟩,⟨1169,by decide⟩]

def ntree15RRRLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨1747,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1748,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1749,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨490,by decide⟩,⟨1750,by decide⟩,⟨881,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨604,by decide⟩,⟨881,by decide⟩,⟨1751,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1752,by decide⟩,⟨0,by decide⟩,⟨1752,by decide⟩]

def ntree15RRRLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RRRLRRRL i else ntree15RRRLRRRR (i - 8)

def ntree15RRRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRLRRL i else ntree15RRRLRRR (i - 15)

def ntree15RRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRRLRL i else ntree15RRRLRR (i - 30)

def ntree15RRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15RRRLL i else ntree15RRRLR (i - 60)

def ntree15RRRRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1753,by decide⟩,⟨826,by decide⟩,⟨1753,by decide⟩] | 1 => ![⟨1754,by decide⟩,⟨989,by decide⟩,⟨1754,by decide⟩] | 2 => ![⟨1755,by decide⟩,⟨223,by decide⟩,⟨1755,by decide⟩] | 3 => ![⟨1756,by decide⟩,⟨994,by decide⟩,⟨1756,by decide⟩] | 4 => ![⟨1729,by decide⟩,⟨1254,by decide⟩,⟨1757,by decide⟩] | 5 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1758,by decide⟩] | _ => ![⟨385,by decide⟩,⟨881,by decide⟩,⟨1759,by decide⟩]

def ntree15RRRRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1760,by decide⟩] | 1 => ![⟨1212,by decide⟩,⟨1212,by decide⟩,⟨1761,by decide⟩] | 2 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1762,by decide⟩] | 3 => ![⟨385,by decide⟩,⟨881,by decide⟩,⟨1763,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨1764,by decide⟩] | 5 => ![⟨615,by decide⟩,⟨1064,by decide⟩,⟨1765,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1766,by decide⟩,⟨0,by decide⟩] | _ => ![⟨385,by decide⟩,⟨1766,by decide⟩,⟨385,by decide⟩]

def ntree15RRRRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRRLLLL i else ntree15RRRRLLLR (i - 7)

def ntree15RRRRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1169,by decide⟩,⟨1767,by decide⟩,⟨1169,by decide⟩] | 1 => ![⟨1174,by decide⟩,⟨1768,by decide⟩,⟨1174,by decide⟩] | 2 => ![⟨374,by decide⟩,⟨1769,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨1683,by decide⟩,⟨1770,by decide⟩,⟨1254,by decide⟩] | 4 => ![⟨1169,by decide⟩,⟨1771,by decide⟩,⟨1169,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨1772,by decide⟩,⟨881,by decide⟩] | _ => ![⟨163,by decide⟩,⟨1773,by decide⟩,⟨1153,by decide⟩]

def ntree15RRRRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨163,by decide⟩,⟨1774,by decide⟩,⟨881,by decide⟩] | 1 => ![⟨374,by decide⟩,⟨1775,by decide⟩,⟨374,by decide⟩] | 2 => ![⟨494,by decide⟩,⟨1776,by decide⟩,⟨1154,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1434,by decide⟩,⟨1434,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨634,by decide⟩,⟨634,by decide⟩,⟨0,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1274,by decide⟩,⟨1777,by decide⟩]

def ntree15RRRRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRRLLRL i else ntree15RRRRLLRR (i - 7)

def ntree15RRRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRRLLL i else ntree15RRRRLLR (i - 15)

def ntree15RRRRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1619,by decide⟩,⟨2,by decide⟩,⟨1778,by decide⟩] | 1 => ![⟨1620,by decide⟩,⟨1275,by decide⟩,⟨1779,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1780,by decide⟩] | 3 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1781,by decide⟩] | 4 => ![⟨1092,by decide⟩,⟨1092,by decide⟩,⟨1782,by decide⟩] | 5 => ![⟨1439,by decide⟩,⟨1281,by decide⟩,⟨1783,by decide⟩] | _ => ![⟨1626,by decide⟩,⟨639,by decide⟩,⟨1784,by decide⟩]

def ntree15RRRRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1627,by decide⟩,⟨1282,by decide⟩,⟨1785,by decide⟩] | 1 => ![⟨1628,by decide⟩,⟨837,by decide⟩,⟨1786,by decide⟩] | 2 => ![⟨385,by decide⟩,⟨837,by decide⟩,⟨1787,by decide⟩] | 3 => ![⟨1630,by decide⟩,⟨841,by decide⟩,⟨1788,by decide⟩] | 4 => ![⟨1629,by decide⟩,⟨2,by decide⟩,⟨1789,by decide⟩] | 5 => ![⟨1631,by decide⟩,⟨837,by decide⟩,⟨1790,by decide⟩] | 6 => ![⟨1634,by decide⟩,⟨861,by decide⟩,⟨1791,by decide⟩] | _ => ![⟨385,by decide⟩,⟨837,by decide⟩,⟨1792,by decide⟩]

def ntree15RRRRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRRLRLL i else ntree15RRRRLRLR (i - 7)

def ntree15RRRRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1793,by decide⟩] | 1 => ![⟨826,by decide⟩,⟨826,by decide⟩,⟨1794,by decide⟩] | 2 => ![⟨1638,by decide⟩,⟨2,by decide⟩,⟨1795,by decide⟩] | 3 => ![⟨1639,by decide⟩,⟨836,by decide⟩,⟨1796,by decide⟩] | 4 => ![⟨385,by decide⟩,⟨1284,by decide⟩,⟨1797,by decide⟩] | 5 => ![⟨402,by decide⟩,⟨1286,by decide⟩,⟨1798,by decide⟩] | 6 => ![⟨385,by decide⟩,⟨837,by decide⟩,⟨1799,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1285,by decide⟩,⟨1800,by decide⟩]

def ntree15RRRRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨385,by decide⟩,⟨1288,by decide⟩,⟨1801,by decide⟩] | 1 => ![⟨385,by decide⟩,⟨837,by decide⟩,⟨1802,by decide⟩] | 2 => ![⟨416,by decide⟩,⟨1289,by decide⟩,⟨1803,by decide⟩] | 3 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1804,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1294,by decide⟩,⟨1805,by decide⟩] | 5 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨1806,by decide⟩] | 6 => ![⟨384,by decide⟩,⟨1295,by decide⟩,⟨1807,by decide⟩] | _ => ![⟨1467,by decide⟩,⟨1467,by decide⟩,⟨882,by decide⟩]

def ntree15RRRRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RRRRLRRL i else ntree15RRRRLRRR (i - 8)

def ntree15RRRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRRLRL i else ntree15RRRRLRR (i - 15)

def ntree15RRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRRRLL i else ntree15RRRRLR (i - 30)

def ntree15RRRRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1641,by decide⟩,⟨1297,by decide⟩,⟨1808,by decide⟩] | 1 => ![⟨1478,by decide⟩,⟨1809,by decide⟩,⟨1297,by decide⟩] | 2 => ![⟨1810,by decide⟩,⟨76,by decide⟩,⟨1631,by decide⟩] | 3 => ![⟨1811,by decide⟩,⟨1477,by decide⟩,⟨1634,by decide⟩] | 4 => ![⟨1812,by decide⟩,⟨1478,by decide⟩,⟨1631,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨1813,by decide⟩,⟨1288,by decide⟩] | _ => ![⟨704,by decide⟩,⟨704,by decide⟩,⟨470,by decide⟩]

def ntree15RRRRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1814,by decide⟩,⟨707,by decide⟩,⟨1641,by decide⟩] | 1 => ![⟨706,by decide⟩,⟨1815,by decide⟩,⟨1289,by decide⟩] | 2 => ![⟨707,by decide⟩,⟨1816,by decide⟩,⟨1288,by decide⟩] | 3 => ![⟨1817,by decide⟩,⟨723,by decide⟩,⟨1678,by decide⟩] | 4 => ![⟨1818,by decide⟩,⟨1818,by decide⟩,⟨1084,by decide⟩] | 5 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1819,by decide⟩] | 6 => ![⟨1169,by decide⟩,⟨1169,by decide⟩,⟨1820,by decide⟩] | _ => ![⟨1676,by decide⟩,⟨1344,by decide⟩,⟨1821,by decide⟩]

def ntree15RRRRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRRRLLL i else ntree15RRRRRLLR (i - 7)

def ntree15RRRRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1678,by decide⟩,⟨733,by decide⟩,⟨1822,by decide⟩] | 1 => ![⟨1823,by decide⟩,⟨1823,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨1824,by decide⟩,⟨1824,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1825,by decide⟩,⟨1823,by decide⟩,⟨1676,by decide⟩] | 4 => ![⟨1826,by decide⟩,⟨1824,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1827,by decide⟩,⟨76,by decide⟩,⟨1678,by decide⟩] | _ => ![⟨1828,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15RRRRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1829,by decide⟩,⟨1829,by decide⟩,⟨1179,by decide⟩] | 1 => ![⟨1830,by decide⟩,⟨1830,by decide⟩,⟨826,by decide⟩] | 2 => ![⟨1831,by decide⟩,⟨1831,by decide⟩,⟨1169,by decide⟩] | 3 => ![⟨1832,by decide⟩,⟨1832,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1833,by decide⟩,⟨1829,by decide⟩,⟨1693,by decide⟩] | 5 => ![⟨1834,by decide⟩,⟨1823,by decide⟩,⟨1694,by decide⟩] | 6 => ![⟨1835,by decide⟩,⟨1830,by decide⟩,⟨1439,by decide⟩] | _ => ![⟨1836,by decide⟩,⟨1831,by decide⟩,⟨1676,by decide⟩]

def ntree15RRRRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRRRLRL i else ntree15RRRRRLRR (i - 7)

def ntree15RRRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRRRLL i else ntree15RRRRRLR (i - 15)

def ntree15RRRRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1837,by decide⟩,⟨1169,by decide⟩,⟨1169,by decide⟩] | 1 => ![⟨1838,by decide⟩,⟨1832,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1839,by decide⟩,⟨1477,by decide⟩,⟨1695,by decide⟩] | 3 => ![⟨1840,by decide⟩,⟨76,by decide⟩,⟨1696,by decide⟩] | 4 => ![⟨1841,by decide⟩,⟨826,by decide⟩,⟨826,by decide⟩] | 5 => ![⟨1842,by decide⟩,⟨1824,by decide⟩,⟨503,by decide⟩] | _ => ![⟨1843,by decide⟩,⟨1843,by decide⟩,⟨1174,by decide⟩]

def ntree15RRRRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1844,by decide⟩,⟨1844,by decide⟩,⟨374,by decide⟩] | 1 => ![⟨1845,by decide⟩,⟨1845,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨1846,by decide⟩,⟨1846,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1823,by decide⟩,⟨1847,by decide⟩,⟨1344,by decide⟩] | 4 => ![⟨1824,by decide⟩,⟨1848,by decide⟩,⟨733,by decide⟩] | 5 => ![⟨1523,by decide⟩,⟨1849,by decide⟩,⟨1403,by decide⟩] | 6 => ![⟨1729,by decide⟩,⟨1400,by decide⟩,⟨1850,by decide⟩] | _ => ![⟨1588,by decide⟩,⟨1403,by decide⟩,⟨1851,by decide⟩]

def ntree15RRRRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15RRRRRRLL i else ntree15RRRRRRLR (i - 7)

def ntree15RRRRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1823,by decide⟩,⟨1852,by decide⟩,⟨1400,by decide⟩] | 1 => ![⟨1824,by decide⟩,⟨1853,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨1854,by decide⟩,⟨1403,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1855,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1856,by decide⟩,⟨1823,by decide⟩,⟨1729,by decide⟩] | 5 => ![⟨1857,by decide⟩,⟨1824,by decide⟩,⟨1588,by decide⟩] | 6 => ![⟨1823,by decide⟩,⟨1858,by decide⟩,⟨1409,by decide⟩] | _ => ![⟨1843,by decide⟩,⟨1859,by decide⟩,⟨1410,by decide⟩]

def ntree15RRRRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨1844,by decide⟩,⟨1860,by decide⟩,⟨639,by decide⟩] | 1 => ![⟨1169,by decide⟩,⟨1861,by decide⟩,⟨1169,by decide⟩] | 2 => ![⟨1845,by decide⟩,⟨1862,by decide⟩,⟨1400,by decide⟩] | 3 => ![⟨1846,by decide⟩,⟨1863,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨76,by decide⟩,⟨1864,by decide⟩,⟨1411,by decide⟩] | 5 => ![⟨706,by decide⟩,⟨1865,by decide⟩,⟨1412,by decide⟩] | 6 => ![⟨374,by decide⟩,⟨1866,by decide⟩,⟨374,by decide⟩] | _ => ![⟨1824,by decide⟩,⟨1867,by decide⟩,⟨1032,by decide⟩]

def ntree15RRRRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15RRRRRRRL i else ntree15RRRRRRRR (i - 8)

def ntree15RRRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15RRRRRRL i else ntree15RRRRRRR (i - 15)

def ntree15RRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15RRRRRL i else ntree15RRRRRR (i - 30)

def ntree15RRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 61 then ntree15RRRRL i else ntree15RRRRR (i - 61)

def ntree15RRR (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15RRRL i else ntree15RRRR (i - 121)

def ntree15RR (i : Nat) : Fin 3 → Fin 1868 := if i < 242 then ntree15RRL i else ntree15RRR (i - 242)

def ntree15R (i : Nat) : Fin 3 → Fin 1868 := if i < 484 then ntree15RL i else ntree15RR (i - 484)

def ntree15 (i : Nat) : Fin 3 → Fin 1868 := if i < 968 then ntree15L i else ntree15R (i - 968)

def layer15 : Fin 1868 → State := fun i => stree15 i.val

def next15 : Fin 1937 → Fin 3 → Fin 1868 := fun i => ntree15 i.val

end Paper2.Certificates.Q6.Coverage

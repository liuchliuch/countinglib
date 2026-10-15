import Paper2.Certificates.Q6CoverageCompact.Layer11Part009

namespace Paper2.Certificates.Q6.Coverage

def ntree11RRRRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2470,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨3032,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 2 => ![⟨3035,by decide⟩,⟨3035,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨3035,by decide⟩,⟨3036,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨3037,by decide⟩,⟨10,by decide⟩,⟨2396,by decide⟩] | 5 => ![⟨3038,by decide⟩,⟨8,by decide⟩,⟨2390,by decide⟩] | 6 => ![⟨3039,by decide⟩,⟨1067,by decide⟩,⟨3039,by decide⟩] | _ => ![⟨3040,by decide⟩,⟨1069,by decide⟩,⟨3040,by decide⟩]

def ntree11RRRRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRRLLLL i else ntree11RRRRRLLLR (i - 7)

def ntree11RRRRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨3041,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨3042,by decide⟩,⟨1864,by decide⟩,⟨2347,by decide⟩] | 2 => ![⟨3043,by decide⟩,⟨2817,by decide⟩,⟨2343,by decide⟩] | 3 => ![⟨3044,by decide⟩,⟨2483,by decide⟩,⟨1748,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨3045,by decide⟩,⟨166,by decide⟩] | 5 => ![⟨2159,by decide⟩,⟨3045,by decide⟩,⟨2487,by decide⟩] | 6 => ![⟨1864,by decide⟩,⟨3046,by decide⟩,⟨706,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2182,by decide⟩]

def ntree11RRRRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2183,by decide⟩] | 1 => ![⟨3047,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨706,by decide⟩,⟨3048,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2182,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2183,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨3049,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨3049,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨3050,by decide⟩]

def ntree11RRRRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRRLLRL i else ntree11RRRRRLLRR (i - 8)

def ntree11RRRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRRLLL i else ntree11RRRRRLLR (i - 15)

def ntree11RRRRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3051,by decide⟩,⟨3051,by decide⟩,⟨968,by decide⟩] | 1 => ![⟨3052,by decide⟩,⟨3051,by decide⟩,⟨2975,by decide⟩] | 2 => ![⟨2978,by decide⟩,⟨968,by decide⟩,⟨2978,by decide⟩] | 3 => ![⟨2975,by decide⟩,⟨968,by decide⟩,⟨2975,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨3053,by decide⟩,⟨716,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨3054,by decide⟩,⟨166,by decide⟩] | _ => ![⟨1338,by decide⟩,⟨166,by decide⟩,⟨2499,by decide⟩]

def ntree11RRRRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨3055,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨3055,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2507,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨3056,by decide⟩] | 4 => ![⟨1872,by decide⟩,⟨3057,by decide⟩,⟨3058,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨1139,by decide⟩,⟨3058,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1141,by decide⟩,⟨3059,by decide⟩] | _ => ![⟨3060,by decide⟩,⟨1864,by decide⟩,⟨2396,by decide⟩]

def ntree11RRRRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRRLRLL i else ntree11RRRRRLRLR (i - 7)

def ntree11RRRRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3061,by decide⟩,⟨2817,by decide⟩,⟨2390,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨3062,by decide⟩,⟨227,by decide⟩] | 2 => ![⟨1874,by decide⟩,⟨3063,by decide⟩,⟨727,by decide⟩] | 3 => ![⟨2178,by decide⟩,⟨3062,by decide⟩,⟨2513,by decide⟩] | 4 => ![⟨2049,by decide⟩,⟨227,by decide⟩,⟨3064,by decide⟩] | 5 => ![⟨2050,by decide⟩,⟨727,by decide⟩,⟨3065,by decide⟩] | 6 => ![⟨2049,by decide⟩,⟨706,by decide⟩,⟨3066,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1149,by decide⟩,⟨1149,by decide⟩]

def ntree11RRRRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1864,by decide⟩,⟨3057,by decide⟩,⟨1139,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨1158,by decide⟩,⟨1158,by decide⟩] | 2 => ![⟨3067,by decide⟩,⟨3067,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨3068,by decide⟩,⟨3068,by decide⟩,⟨83,by decide⟩] | 4 => ![⟨2483,by decide⟩,⟨3069,by decide⟩,⟨1162,by decide⟩] | 5 => ![⟨2739,by decide⟩,⟨1162,by decide⟩,⟨3070,by decide⟩] | 6 => ![⟨3071,by decide⟩,⟨3067,by decide⟩,⟨2418,by decide⟩] | _ => ![⟨3072,by decide⟩,⟨3068,by decide⟩,⟨2423,by decide⟩]

def ntree11RRRRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRRLRRL i else ntree11RRRRRLRRR (i - 8)

def ntree11RRRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRRLRL i else ntree11RRRRRLRR (i - 15)

def ntree11RRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRRRRLL i else ntree11RRRRRLR (i - 31)

def ntree11RRRRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3067,by decide⟩,⟨3073,by decide⟩,⟨1177,by decide⟩] | 1 => ![⟨3051,by decide⟩,⟨3074,by decide⟩,⟨1186,by decide⟩] | 2 => ![⟨2739,by decide⟩,⟨706,by decide⟩,⟨2845,by decide⟩] | 3 => ![⟨3018,by decide⟩,⟨1177,by decide⟩,⟨3075,by decide⟩] | 4 => ![⟨1092,by decide⟩,⟨10,by decide⟩,⟨1608,by decide⟩] | 5 => ![⟨1094,by decide⟩,⟨8,by decide⟩,⟨2549,by decide⟩] | _ => ![⟨3076,by decide⟩,⟨3076,by decide⟩,⟨1067,by decide⟩]

def ntree11RRRRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3077,by decide⟩,⟨3077,by decide⟩,⟨1069,by decide⟩] | 1 => ![⟨3078,by decide⟩,⟨3067,by decide⟩,⟨2458,by decide⟩] | 2 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2561,by decide⟩] | 3 => ![⟨2178,by decide⟩,⟨1864,by decide⟩,⟨2562,by decide⟩] | 4 => ![⟨3042,by decide⟩,⟨1914,by decide⟩,⟨2563,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1608,by decide⟩] | 6 => ![⟨3047,by decide⟩,⟨270,by decide⟩,⟨1622,by decide⟩] | _ => ![⟨85,by decide⟩,⟨1208,by decide⟩,⟨1208,by decide⟩]

def ntree11RRRRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRRRLLL i else ntree11RRRRRRLLR (i - 7)

def ntree11RRRRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1864,by decide⟩,⟨3079,by decide⟩,⟨1217,by decide⟩] | 1 => ![⟨3042,by decide⟩,⟨2277,by decide⟩,⟨2348,by decide⟩] | 2 => ![⟨1092,by decide⟩,⟨2282,by decide⟩,⟨2349,by decide⟩] | 3 => ![⟨3080,by decide⟩,⟨1864,by decide⟩,⟨1647,by decide⟩] | 4 => ![⟨2483,by decide⟩,⟨3081,by decide⟩,⟨510,by decide⟩] | 5 => ![⟨3044,by decide⟩,⟨3081,by decide⟩,⟨2685,by decide⟩] | 6 => ![⟨3082,by decide⟩,⟨3082,by decide⟩,⟨370,by decide⟩] | _ => ![⟨3083,by decide⟩,⟨3082,by decide⟩,⟨1650,by decide⟩]

def ntree11RRRRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1654,by decide⟩,⟨529,by decide⟩,⟨3084,by decide⟩] | 1 => ![⟨3051,by decide⟩,⟨3085,by decide⟩,⟨969,by decide⟩] | 2 => ![⟨3052,by decide⟩,⟨3085,by decide⟩,⟨2976,by decide⟩] | 3 => ![⟨968,by decide⟩,⟨3086,by decide⟩,⟨968,by decide⟩] | 4 => ![⟨1125,by decide⟩,⟨3086,by decide⟩,⟨2977,by decide⟩] | 5 => ![⟨391,by decide⟩,⟨391,by decide⟩,⟨3087,by decide⟩] | 6 => ![⟨1658,by decide⟩,⟨1233,by decide⟩,⟨3088,by decide⟩] | _ => ![⟨3089,by decide⟩,⟨2282,by decide⟩,⟨2507,by decide⟩]

def ntree11RRRRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRRRLRL i else ntree11RRRRRRLRR (i - 8)

def ntree11RRRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRRRLL i else ntree11RRRRRRLR (i - 15)

def ntree11RRRRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2900,by decide⟩,⟨10,by decide⟩,⟨2900,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2902,by decide⟩] | 2 => ![⟨3060,by decide⟩,⟨2891,by decide⟩,⟨2989,by decide⟩] | 3 => ![⟨3090,by decide⟩,⟨2965,by decide⟩,⟨1654,by decide⟩] | 4 => ![⟨370,by decide⟩,⟨1245,by decide⟩,⟨3091,by decide⟩] | 5 => ![⟨1654,by decide⟩,⟨1151,by decide⟩,⟨3092,by decide⟩] | _ => ![⟨3093,by decide⟩,⟨10,by decide⟩,⟨3093,by decide⟩]

def ntree11RRRRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3093,by decide⟩,⟨10,by decide⟩,⟨3094,by decide⟩] | 1 => ![⟨3067,by decide⟩,⟨3095,by decide⟩,⟨86,by decide⟩] | 2 => ![⟨85,by decide⟩,⟨3096,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨3067,by decide⟩,⟨3097,by decide⟩,⟨1026,by decide⟩] | 4 => ![⟨3067,by decide⟩,⟨3067,by decide⟩,⟨3011,by decide⟩] | 5 => ![⟨3071,by decide⟩,⟨3097,by decide⟩,⟨3012,by decide⟩] | 6 => ![⟨3098,by decide⟩,⟨3096,by decide⟩,⟨2534,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨2891,by decide⟩,⟨3020,by decide⟩]

def ntree11RRRRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRRRRLL i else ntree11RRRRRRRLR (i - 7)

def ntree11RRRRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨2635,by decide⟩,⟨3002,by decide⟩] | 1 => ![⟨652,by decide⟩,⟨2282,by decide⟩,⟨2656,by decide⟩] | 2 => ![⟨1291,by decide⟩,⟨2282,by decide⟩,⟨2657,by decide⟩] | 3 => ![⟨1647,by decide⟩,⟨10,by decide⟩,⟨2323,by decide⟩] | 4 => ![⟨3076,by decide⟩,⟨3099,by decide⟩,⟨1077,by decide⟩] | 5 => ![⟨3077,by decide⟩,⟨3100,by decide⟩,⟨1078,by decide⟩] | 6 => ![⟨1067,by decide⟩,⟨3101,by decide⟩,⟨1067,by decide⟩] | _ => ![⟨3102,by decide⟩,⟨3067,by decide⟩,⟨2664,by decide⟩]

def ntree11RRRRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2951,by decide⟩,⟨2277,by decide⟩,⟨2668,by decide⟩] | 1 => ![⟨3103,by decide⟩,⟨2307,by decide⟩,⟨2670,by decide⟩] | 2 => ![⟨2665,by decide⟩,⟨2282,by decide⟩,⟨2665,by decide⟩] | 3 => ![⟨3104,by decide⟩,⟨2309,by decide⟩,⟨2666,by decide⟩] | 4 => ![⟨2664,by decide⟩,⟨85,by decide⟩,⟨3105,by decide⟩] | 5 => ![⟨3106,by decide⟩,⟨1864,by decide⟩,⟨2674,by decide⟩] | 6 => ![⟨2665,by decide⟩,⟨1213,by decide⟩,⟨3107,by decide⟩] | _ => ![⟨2664,by decide⟩,⟨1215,by decide⟩,⟨3108,by decide⟩]

def ntree11RRRRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRRRRRL i else ntree11RRRRRRRRR (i - 8)

def ntree11RRRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRRRRL i else ntree11RRRRRRRR (i - 15)

def ntree11RRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRRRRRL i else ntree11RRRRRRR (i - 31)

def ntree11RRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RRRRRL i else ntree11RRRRRR (i - 62)

def ntree11RRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 124 then ntree11RRRRL i else ntree11RRRRR (i - 124)

def ntree11RRR (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11RRRL i else ntree11RRRR (i - 247)

def ntree11RR (i : Nat) : Fin 3 → Fin 3109 := if i < 495 then ntree11RRL i else ntree11RRR (i - 495)

def ntree11R (i : Nat) : Fin 3 → Fin 3109 := if i < 990 then ntree11RL i else ntree11RR (i - 990)

def ntree11 (i : Nat) : Fin 3 → Fin 3109 := if i < 1979 then ntree11L i else ntree11R (i - 1979)

def layer11 : Fin 3109 → State := fun i => stree11 i.val

def next11 : Fin 3959 → Fin 3 → Fin 3109 := fun i => ntree11 i.val

end Paper2.Certificates.Q6.Coverage

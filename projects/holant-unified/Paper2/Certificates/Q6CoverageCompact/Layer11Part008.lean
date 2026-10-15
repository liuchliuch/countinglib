import Paper2.Certificates.Q6CoverageCompact.Layer11Part007

namespace Paper2.Certificates.Q6.Coverage

def stree11RRRRRLLLL (i : Nat) : State := match i with | 0 => state11_3011 | 1 => state11_3012 | 2 => state11_3013 | 3 => state11_3014 | 4 => state11_3015 | _ => state11_3016

def stree11RRRRRLLLR (i : Nat) : State := match i with | 0 => state11_3017 | 1 => state11_3018 | 2 => state11_3019 | 3 => state11_3020 | 4 => state11_3021 | _ => state11_3022

def stree11RRRRRLLL (i : Nat) : State := if i < 6 then stree11RRRRRLLLL i else stree11RRRRRLLLR (i - 6)

def stree11RRRRRLLRL (i : Nat) : State := match i with | 0 => state11_3023 | 1 => state11_3024 | 2 => state11_3025 | 3 => state11_3026 | 4 => state11_3027 | _ => state11_3028

def stree11RRRRRLLRR (i : Nat) : State := match i with | 0 => state11_3029 | 1 => state11_3030 | 2 => state11_3031 | 3 => state11_3032 | 4 => state11_3033 | _ => state11_3034

def stree11RRRRRLLR (i : Nat) : State := if i < 6 then stree11RRRRRLLRL i else stree11RRRRRLLRR (i - 6)

def stree11RRRRRLL (i : Nat) : State := if i < 12 then stree11RRRRRLLL i else stree11RRRRRLLR (i - 12)

def stree11RRRRRLRLL (i : Nat) : State := match i with | 0 => state11_3035 | 1 => state11_3036 | 2 => state11_3037 | 3 => state11_3038 | 4 => state11_3039 | _ => state11_3040

def stree11RRRRRLRLR (i : Nat) : State := match i with | 0 => state11_3041 | 1 => state11_3042 | 2 => state11_3043 | 3 => state11_3044 | 4 => state11_3045 | _ => state11_3046

def stree11RRRRRLRL (i : Nat) : State := if i < 6 then stree11RRRRRLRLL i else stree11RRRRRLRLR (i - 6)

def stree11RRRRRLRRL (i : Nat) : State := match i with | 0 => state11_3047 | 1 => state11_3048 | 2 => state11_3049 | 3 => state11_3050 | 4 => state11_3051 | _ => state11_3052

def stree11RRRRRLRRR (i : Nat) : State := match i with | 0 => state11_3053 | 1 => state11_3054 | 2 => state11_3055 | 3 => state11_3056 | 4 => state11_3057 | 5 => state11_3058 | _ => state11_3059

def stree11RRRRRLRR (i : Nat) : State := if i < 6 then stree11RRRRRLRRL i else stree11RRRRRLRRR (i - 6)

def stree11RRRRRLR (i : Nat) : State := if i < 12 then stree11RRRRRLRL i else stree11RRRRRLRR (i - 12)

def stree11RRRRRL (i : Nat) : State := if i < 24 then stree11RRRRRLL i else stree11RRRRRLR (i - 24)

def stree11RRRRRRLLL (i : Nat) : State := match i with | 0 => state11_3060 | 1 => state11_3061 | 2 => state11_3062 | 3 => state11_3063 | 4 => state11_3064 | _ => state11_3065

def stree11RRRRRRLLR (i : Nat) : State := match i with | 0 => state11_3066 | 1 => state11_3067 | 2 => state11_3068 | 3 => state11_3069 | 4 => state11_3070 | _ => state11_3071

def stree11RRRRRRLL (i : Nat) : State := if i < 6 then stree11RRRRRRLLL i else stree11RRRRRRLLR (i - 6)

def stree11RRRRRRLRL (i : Nat) : State := match i with | 0 => state11_3072 | 1 => state11_3073 | 2 => state11_3074 | 3 => state11_3075 | 4 => state11_3076 | _ => state11_3077

def stree11RRRRRRLRR (i : Nat) : State := match i with | 0 => state11_3078 | 1 => state11_3079 | 2 => state11_3080 | 3 => state11_3081 | 4 => state11_3082 | _ => state11_3083

def stree11RRRRRRLR (i : Nat) : State := if i < 6 then stree11RRRRRRLRL i else stree11RRRRRRLRR (i - 6)

def stree11RRRRRRL (i : Nat) : State := if i < 12 then stree11RRRRRRLL i else stree11RRRRRRLR (i - 12)

def stree11RRRRRRRLL (i : Nat) : State := match i with | 0 => state11_3084 | 1 => state11_3085 | 2 => state11_3086 | 3 => state11_3087 | 4 => state11_3088 | _ => state11_3089

def stree11RRRRRRRLR (i : Nat) : State := match i with | 0 => state11_3090 | 1 => state11_3091 | 2 => state11_3092 | 3 => state11_3093 | 4 => state11_3094 | _ => state11_3095

def stree11RRRRRRRL (i : Nat) : State := if i < 6 then stree11RRRRRRRLL i else stree11RRRRRRRLR (i - 6)

def stree11RRRRRRRRL (i : Nat) : State := match i with | 0 => state11_3096 | 1 => state11_3097 | 2 => state11_3098 | 3 => state11_3099 | 4 => state11_3100 | _ => state11_3101

def stree11RRRRRRRRR (i : Nat) : State := match i with | 0 => state11_3102 | 1 => state11_3103 | 2 => state11_3104 | 3 => state11_3105 | 4 => state11_3106 | 5 => state11_3107 | _ => state11_3108

def stree11RRRRRRRR (i : Nat) : State := if i < 6 then stree11RRRRRRRRL i else stree11RRRRRRRRR (i - 6)

def stree11RRRRRRR (i : Nat) : State := if i < 12 then stree11RRRRRRRL i else stree11RRRRRRRR (i - 12)

def stree11RRRRRR (i : Nat) : State := if i < 24 then stree11RRRRRRL i else stree11RRRRRRR (i - 24)

def stree11RRRRR (i : Nat) : State := if i < 49 then stree11RRRRRL i else stree11RRRRRR (i - 49)

def stree11RRRR (i : Nat) : State := if i < 97 then stree11RRRRL i else stree11RRRRR (i - 97)

def stree11RRR (i : Nat) : State := if i < 194 then stree11RRRL i else stree11RRRR (i - 194)

def stree11RR (i : Nat) : State := if i < 389 then stree11RRL i else stree11RRR (i - 389)

def stree11R (i : Nat) : State := if i < 777 then stree11RL i else stree11RR (i - 777)

def stree11 (i : Nat) : State := if i < 1554 then stree11L i else stree11R (i - 1554)

def ntree11LLLLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨3,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨4,by decide⟩,⟨5,by decide⟩,⟨5,by decide⟩] | 5 => ![⟨6,by decide⟩,⟨7,by decide⟩,⟨5,by decide⟩] | _ => ![⟨6,by decide⟩,⟨6,by decide⟩,⟨4,by decide⟩]

def ntree11LLLLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 3 => ![⟨12,by decide⟩,⟨13,by decide⟩,⟨9,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨15,by decide⟩,⟨11,by decide⟩] | 5 => ![⟨12,by decide⟩,⟨12,by decide⟩,⟨8,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨10,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11LLLLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLLLLLL i else ntree11LLLLLLLLR (i - 7)

def ntree11LLLLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨16,by decide⟩,⟨16,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨17,by decide⟩,⟨16,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨19,by decide⟩,⟨18,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩] | _ => ![⟨21,by decide⟩,⟨10,by decide⟩,⟨21,by decide⟩]

def ntree11LLLLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨22,by decide⟩,⟨22,by decide⟩] | 1 => ![⟨21,by decide⟩,⟨22,by decide⟩,⟨23,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨24,by decide⟩] | 3 => ![⟨25,by decide⟩,⟨25,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨26,by decide⟩,⟨26,by decide⟩,⟨27,by decide⟩] | 5 => ![⟨27,by decide⟩,⟨28,by decide⟩,⟨28,by decide⟩] | 6 => ![⟨25,by decide⟩,⟨25,by decide⟩,⟨24,by decide⟩] | _ => ![⟨21,by decide⟩,⟨18,by decide⟩,⟨29,by decide⟩]

def ntree11LLLLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLLLLRL i else ntree11LLLLLLLRR (i - 7)

def ntree11LLLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLLLLL i else ntree11LLLLLLLR (i - 15)

def ntree11LLLLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨30,by decide⟩,⟨31,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨32,by decide⟩,⟨33,by decide⟩,⟨9,by decide⟩] | 3 => ![⟨32,by decide⟩,⟨32,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨34,by decide⟩,⟨10,by decide⟩,⟨34,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | _ => ![⟨36,by decide⟩,⟨30,by decide⟩,⟨34,by decide⟩]

def ntree11LLLLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨34,by decide⟩,⟨35,by decide⟩,⟨37,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨38,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨39,by decide⟩,⟨40,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨41,by decide⟩,⟨41,by decide⟩] | 4 => ![⟨42,by decide⟩,⟨38,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨42,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨25,by decide⟩,⟨43,by decide⟩,⟨11,by decide⟩] | _ => ![⟨44,by decide⟩,⟨1,by decide⟩,⟨45,by decide⟩]

def ntree11LLLLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLLLRLL i else ntree11LLLLLLRLR (i - 7)

def ntree11LLLLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨46,by decide⟩,⟨3,by decide⟩,⟨45,by decide⟩] | 1 => ![⟨46,by decide⟩,⟨2,by decide⟩,⟨44,by decide⟩] | 2 => ![⟨44,by decide⟩,⟨0,by decide⟩,⟨44,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨11,by decide⟩,⟨48,by decide⟩] | 4 => ![⟨49,by decide⟩,⟨15,by decide⟩,⟨48,by decide⟩] | 5 => ![⟨49,by decide⟩,⟨14,by decide⟩,⟨47,by decide⟩] | 6 => ![⟨47,by decide⟩,⟨10,by decide⟩,⟨47,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨50,by decide⟩]

def ntree11LLLLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨50,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨52,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨22,by decide⟩,⟨53,by decide⟩] | 6 => ![⟨54,by decide⟩,⟨54,by decide⟩,⟨54,by decide⟩] | _ => ![⟨55,by decide⟩,⟨55,by decide⟩,⟨54,by decide⟩]

def ntree11LLLLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLLLLRRL i else ntree11LLLLLLRRR (i - 8)

def ntree11LLLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLLLRL i else ntree11LLLLLLRR (i - 15)

def ntree11LLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11LLLLLLL i else ntree11LLLLLLR (i - 30)

def ntree11LLLLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨54,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨54,by decide⟩,⟨54,by decide⟩,⟨54,by decide⟩] | 2 => ![⟨57,by decide⟩,⟨54,by decide⟩,⟨57,by decide⟩] | 3 => ![⟨55,by decide⟩,⟨55,by decide⟩,⟨58,by decide⟩] | 4 => ![⟨57,by decide⟩,⟨56,by decide⟩,⟨59,by decide⟩] | 5 => ![⟨60,by decide⟩,⟨31,by decide⟩,⟨48,by decide⟩] | _ => ![⟨60,by decide⟩,⟨30,by decide⟩,⟨47,by decide⟩]

def ntree11LLLLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨61,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨62,by decide⟩,⟨30,by decide⟩,⟨63,by decide⟩] | 3 => ![⟨63,by decide⟩,⟨35,by decide⟩,⟨64,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨65,by decide⟩,⟨65,by decide⟩] | 5 => ![⟨61,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 6 => ![⟨66,by decide⟩,⟨66,by decide⟩,⟨10,by decide⟩] | _ => ![⟨66,by decide⟩,⟨66,by decide⟩,⟨10,by decide⟩]

def ntree11LLLLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLLRLLL i else ntree11LLLLLRLLR (i - 7)

def ntree11LLLLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨67,by decide⟩,⟨8,by decide⟩,⟨67,by decide⟩] | 1 => ![⟨68,by decide⟩,⟨10,by decide⟩,⟨68,by decide⟩] | 2 => ![⟨69,by decide⟩,⟨12,by decide⟩,⟨67,by decide⟩] | 3 => ![⟨70,by decide⟩,⟨14,by decide⟩,⟨68,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨71,by decide⟩,⟨71,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨72,by decide⟩,⟨72,by decide⟩] | 6 => ![⟨73,by decide⟩,⟨10,by decide⟩,⟨73,by decide⟩] | _ => ![⟨47,by decide⟩,⟨72,by decide⟩,⟨74,by decide⟩]

def ntree11LLLLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨27,by decide⟩,⟨27,by decide⟩,⟨27,by decide⟩] | 1 => ![⟨75,by decide⟩,⟨27,by decide⟩,⟨75,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨76,by decide⟩,⟨76,by decide⟩] | 3 => ![⟨63,by decide⟩,⟨10,by decide⟩,⟨63,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨77,by decide⟩,⟨77,by decide⟩] | 5 => ![⟨78,by decide⟩,⟨25,by decide⟩,⟨68,by decide⟩] | 6 => ![⟨79,by decide⟩,⟨80,by decide⟩,⟨80,by decide⟩] | _ => ![⟨79,by decide⟩,⟨79,by decide⟩,⟨79,by decide⟩]

def ntree11LLLLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLLLRLRL i else ntree11LLLLLRLRR (i - 8)

def ntree11LLLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLLRLL i else ntree11LLLLLRLR (i - 15)

def ntree11LLLLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨81,by decide⟩,⟨82,by decide⟩,⟨82,by decide⟩] | 1 => ![⟨81,by decide⟩,⟨81,by decide⟩,⟨81,by decide⟩] | 2 => ![⟨83,by decide⟩,⟨84,by decide⟩,⟨84,by decide⟩] | 3 => ![⟨85,by decide⟩,⟨86,by decide⟩,⟨86,by decide⟩] | 4 => ![⟨83,by decide⟩,⟨83,by decide⟩,⟨83,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | _ => ![⟨87,by decide⟩,⟨88,by decide⟩,⟨88,by decide⟩]

def ntree11LLLLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨87,by decide⟩,⟨87,by decide⟩,⟨87,by decide⟩] | 1 => ![⟨89,by decide⟩,⟨90,by decide⟩,⟨90,by decide⟩] | 2 => ![⟨89,by decide⟩,⟨89,by decide⟩,⟨89,by decide⟩] | 3 => ![⟨79,by decide⟩,⟨91,by decide⟩,⟨91,by decide⟩] | 4 => ![⟨85,by decide⟩,⟨92,by decide⟩,⟨92,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨93,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨94,by decide⟩,⟨10,by decide⟩] | _ => ![⟨95,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLLLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLLRRLL i else ntree11LLLLLRRLR (i - 7)

def ntree11LLLLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨95,by decide⟩,⟨94,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨96,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨87,by decide⟩,⟨97,by decide⟩,⟨97,by decide⟩] | 4 => ![⟨98,by decide⟩,⟨98,by decide⟩,⟨87,by decide⟩] | 5 => ![⟨99,by decide⟩,⟨100,by decide⟩,⟨18,by decide⟩] | 6 => ![⟨101,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨102,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩]

def ntree11LLLLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨101,by decide⟩,⟨94,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨85,by decide⟩,⟨103,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨104,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨101,by decide⟩,⟨38,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨105,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨102,by decide⟩,⟨103,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨105,by decide⟩,⟨104,by decide⟩,⟨8,by decide⟩] | _ => ![⟨106,by decide⟩,⟨80,by decide⟩,⟨107,by decide⟩]

def ntree11LLLLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLLLRRRL i else ntree11LLLLLRRRR (i - 8)

def ntree11LLLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLLRRL i else ntree11LLLLLRRR (i - 15)

def ntree11LLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLLLLRL i else ntree11LLLLLRR (i - 31)

def ntree11LLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11LLLLLL i else ntree11LLLLLR (i - 61)

def ntree11LLLLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨106,by decide⟩,⟨79,by decide⟩,⟨106,by decide⟩] | 1 => ![⟨108,by decide⟩,⟨86,by decide⟩,⟨109,by decide⟩] | 2 => ![⟨108,by decide⟩,⟨85,by decide⟩,⟨108,by decide⟩] | 3 => ![⟨79,by decide⟩,⟨79,by decide⟩,⟨110,by decide⟩] | 4 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨111,by decide⟩] | 5 => ![⟨112,by decide⟩,⟨88,by decide⟩,⟨113,by decide⟩] | _ => ![⟨112,by decide⟩,⟨87,by decide⟩,⟨112,by decide⟩]

def ntree11LLLLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨87,by decide⟩,⟨87,by decide⟩,⟨87,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨96,by decide⟩,⟨47,by decide⟩] | 2 => ![⟨114,by decide⟩,⟨114,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨115,by decide⟩,⟨115,by decide⟩,⟨87,by decide⟩] | 4 => ![⟨114,by decide⟩,⟨116,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨117,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨118,by decide⟩,⟨94,by decide⟩,⟨51,by decide⟩] | _ => ![⟨10,by decide⟩,⟨119,by decide⟩,⟨10,by decide⟩]

def ntree11LLLLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLRLLLL i else ntree11LLLLRLLLR (i - 7)

def ntree11LLLLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨61,by decide⟩,⟨119,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨95,by decide⟩,⟨119,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨120,by decide⟩,⟨83,by decide⟩,⟨120,by decide⟩] | 3 => ![⟨121,by decide⟩,⟨85,by decide⟩,⟨121,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨122,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨123,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨124,by decide⟩,⟨10,by decide⟩] | _ => ![⟨47,by decide⟩,⟨125,by decide⟩,⟨47,by decide⟩]

def ntree11LLLLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨99,by decide⟩,⟨99,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨125,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨118,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨126,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨127,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨128,by decide⟩,⟨128,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨129,by decide⟩,⟨129,by decide⟩,⟨10,by decide⟩] | _ => ![⟨130,by decide⟩,⟨130,by decide⟩,⟨83,by decide⟩]

def ntree11LLLLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLLRLLRL i else ntree11LLLLRLLRR (i - 8)

def ntree11LLLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLRLLL i else ntree11LLLLRLLR (i - 15)

def ntree11LLLLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨131,by decide⟩,⟨131,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨129,by decide⟩,⟨132,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨133,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨133,by decide⟩] | 4 => ![⟨134,by decide⟩,⟨85,by decide⟩,⟨134,by decide⟩] | 5 => ![⟨135,by decide⟩,⟨10,by decide⟩,⟨135,by decide⟩] | _ => ![⟨10,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩]

def ntree11LLLLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨136,by decide⟩,⟨136,by decide⟩] | 1 => ![⟨135,by decide⟩,⟨11,by decide⟩,⟨137,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨138,by decide⟩,⟨138,by decide⟩] | 3 => ![⟨139,by decide⟩,⟨128,by decide⟩,⟨108,by decide⟩] | 4 => ![⟨140,by decide⟩,⟨129,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨141,by decide⟩] | _ => ![⟨142,by decide⟩,⟨142,by decide⟩,⟨142,by decide⟩]

def ntree11LLLLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLRLRLL i else ntree11LLLLRLRLR (i - 7)

def ntree11LLLLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨143,by decide⟩,⟨143,by decide⟩,⟨142,by decide⟩] | 1 => ![⟨85,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨145,by decide⟩,⟨145,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨141,by decide⟩] | 4 => ![⟨142,by decide⟩,⟨146,by decide⟩,⟨146,by decide⟩] | 5 => ![⟨147,by decide⟩,⟨130,by decide⟩,⟨120,by decide⟩] | 6 => ![⟨148,by decide⟩,⟨128,by decide⟩,⟨121,by decide⟩] | _ => ![⟨149,by decide⟩,⟨131,by decide⟩,⟨67,by decide⟩]

def ntree11LLLLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨0,by decide⟩,⟨150,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨151,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨152,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨153,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨154,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨155,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨156,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | _ => ![⟨157,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLLLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLLRLRRL i else ntree11LLLLRLRRR (i - 8)

def ntree11LLLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLRLRL i else ntree11LLLLRLRR (i - 15)

def ntree11LLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLLLRLL i else ntree11LLLLRLR (i - 31)

def ntree11LLLLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨158,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨159,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨160,by decide⟩,⟨160,by decide⟩] | 3 => ![⟨161,by decide⟩,⟨161,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨161,by decide⟩,⟨162,by decide⟩,⟨160,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨164,by decide⟩] | _ => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩]

def ntree11LLLLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨163,by decide⟩,⟨165,by decide⟩,⟨166,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨166,by decide⟩,⟨166,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨166,by decide⟩,⟨166,by decide⟩] | 3 => ![⟨167,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨168,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨169,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨170,by decide⟩,⟨163,by decide⟩,⟨21,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨171,by decide⟩]

def ntree11LLLLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLRRLLL i else ntree11LLLLRRLLR (i - 7)

def ntree11LLLLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨172,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 2 => ![⟨174,by decide⟩,⟨174,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨174,by decide⟩,⟨175,by decide⟩,⟨173,by decide⟩] | 4 => ![⟨27,by decide⟩,⟨176,by decide⟩,⟨176,by decide⟩] | 5 => ![⟨177,by decide⟩,⟨177,by decide⟩,⟨27,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨178,by decide⟩,⟨10,by decide⟩] | _ => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨171,by decide⟩]

def ntree11LLLLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨179,by decide⟩,⟨180,by decide⟩,⟨173,by decide⟩] | 2 => ![⟨181,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 3 => ![⟨181,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨182,by decide⟩,⟨182,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨182,by decide⟩,⟨183,by decide⟩,⟨184,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨184,by decide⟩,⟨184,by decide⟩] | _ => ![⟨185,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11LLLLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLLRRLRL i else ntree11LLLLRRLRR (i - 8)

def ntree11LLLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLRRLL i else ntree11LLLLRRLR (i - 15)

def ntree11LLLLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨186,by decide⟩,⟨179,by decide⟩,⟨34,by decide⟩] | 1 => ![⟨179,by decide⟩,⟨187,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨188,by decide⟩,⟨173,by decide⟩] | 3 => ![⟨44,by decide⟩,⟨150,by decide⟩,⟨44,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨153,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨189,by decide⟩,⟨189,by decide⟩]

def ntree11LLLLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨190,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨191,by decide⟩,⟨191,by decide⟩] | 3 => ![⟨192,by decide⟩,⟨193,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨192,by decide⟩,⟨192,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨194,by decide⟩,⟨194,by decide⟩] | 6 => ![⟨44,by decide⟩,⟨160,by decide⟩,⟨195,by decide⟩] | _ => ![⟨196,by decide⟩,⟨197,by decide⟩,⟨160,by decide⟩]

def ntree11LLLLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLLRRRLL i else ntree11LLLLRRRLR (i - 7)

def ntree11LLLLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨196,by decide⟩,⟨196,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨166,by decide⟩,⟨198,by decide⟩] | 2 => ![⟨199,by decide⟩,⟨200,by decide⟩,⟨198,by decide⟩] | 3 => ![⟨199,by decide⟩,⟨201,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨202,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨203,by decide⟩] | 6 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨203,by decide⟩] | _ => ![⟨204,by decide⟩,⟨201,by decide⟩,⟨21,by decide⟩]

def ntree11LLLLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨47,by decide⟩,⟨173,by decide⟩,⟨205,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 2 => ![⟨206,by decide⟩,⟨207,by decide⟩,⟨173,by decide⟩] | 3 => ![⟨54,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩] | 4 => ![⟨209,by decide⟩,⟨209,by decide⟩,⟨54,by decide⟩] | 5 => ![⟨210,by decide⟩,⟨179,by decide⟩,⟨47,by decide⟩] | 6 => ![⟨210,by decide⟩,⟨180,by decide⟩,⟨205,by decide⟩] | _ => ![⟨179,by decide⟩,⟨211,by decide⟩,⟨212,by decide⟩]

def ntree11LLLLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLLRRRRL i else ntree11LLLLRRRRR (i - 8)

def ntree11LLLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLLRRRL i else ntree11LLLLRRRR (i - 15)

def ntree11LLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLLLRRL i else ntree11LLLLRRR (i - 31)

def ntree11LLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LLLLRL i else ntree11LLLLRR (i - 62)

def ntree11LLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11LLLLL i else ntree11LLLLR (i - 123)

def ntree11LLLRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨201,by decide⟩,⟨213,by decide⟩,⟨173,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨214,by decide⟩] | 3 => ![⟨215,by decide⟩,⟨179,by decide⟩,⟨63,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨214,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨212,by decide⟩,⟨212,by decide⟩] | _ => ![⟨216,by decide⟩,⟨217,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨218,by decide⟩,⟨218,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨219,by decide⟩] | 2 => ![⟨44,by decide⟩,⟨220,by decide⟩,⟨221,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨220,by decide⟩,⟨220,by decide⟩] | 4 => ![⟨161,by decide⟩,⟨222,by decide⟩,⟨220,by decide⟩] | 5 => ![⟨223,by decide⟩,⟨224,by decide⟩,⟨225,by decide⟩] | 6 => ![⟨226,by decide⟩,⟨227,by decide⟩,⟨227,by decide⟩] | _ => ![⟨223,by decide⟩,⟨163,by decide⟩,⟨47,by decide⟩]

def ntree11LLLRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRLLLLL i else ntree11LLLRLLLLR (i - 7)

def ntree11LLLRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨226,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨228,by decide⟩,⟨163,by decide⟩,⟨73,by decide⟩] | 2 => ![⟨47,by decide⟩,⟨229,by decide⟩,⟨230,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨229,by decide⟩,⟨229,by decide⟩] | 4 => ![⟨174,by decide⟩,⟨231,by decide⟩,⟨229,by decide⟩] | 5 => ![⟨210,by decide⟩,⟨232,by decide⟩,⟨230,by decide⟩] | _ => ![⟨179,by decide⟩,⟨232,by decide⟩,⟨229,by decide⟩]

def ntree11LLLRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨182,by decide⟩,⟨233,by decide⟩,⟨234,by decide⟩] | 1 => ![⟨235,by decide⟩,⟨182,by decide⟩,⟨67,by decide⟩] | 2 => ![⟨236,by decide⟩,⟨179,by decide⟩,⟨68,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨234,by decide⟩,⟨234,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨237,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨238,by decide⟩] | 6 => ![⟨87,by decide⟩,⟨87,by decide⟩,⟨239,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨240,by decide⟩]

def ntree11LLLRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRLLLRL i else ntree11LLLRLLLRR (i - 7)

def ntree11LLLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRLLLL i else ntree11LLLRLLLR (i - 15)

def ntree11LLLRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨241,by decide⟩] | 1 => ![⟨242,by decide⟩,⟨242,by decide⟩,⟨79,by decide⟩] | 2 => ![⟨243,by decide⟩,⟨243,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨244,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨245,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨246,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | _ => ![⟨161,by decide⟩,⟨247,by decide⟩,⟨0,by decide⟩]

def ntree11LLLRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨163,by decide⟩,⟨248,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨249,by decide⟩,⟨249,by decide⟩,⟨87,by decide⟩] | 2 => ![⟨174,by decide⟩,⟨250,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨251,by decide⟩,⟨251,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨252,by decide⟩] | 5 => ![⟨253,by decide⟩,⟨253,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨254,by decide⟩,⟨179,by decide⟩,⟨10,by decide⟩] | _ => ![⟨255,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩]

def ntree11LLLRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRLLRLL i else ntree11LLLRLLRLR (i - 7)

def ntree11LLLRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨256,by decide⟩,⟨256,by decide⟩,⟨83,by decide⟩] | 1 => ![⟨257,by decide⟩,⟨182,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨258,by decide⟩,⟨179,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨259,by decide⟩,⟨83,by decide⟩,⟨83,by decide⟩] | 4 => ![⟨179,by decide⟩,⟨260,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨253,by decide⟩,⟨261,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨182,by decide⟩,⟨262,by decide⟩,⟨8,by decide⟩] | _ => ![⟨263,by decide⟩,⟨263,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨264,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨237,by decide⟩] | 2 => ![⟨265,by decide⟩,⟨265,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨263,by decide⟩,⟨266,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨267,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨245,by decide⟩,⟨38,by decide⟩,⟨240,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨268,by decide⟩,⟨268,by decide⟩] | _ => ![⟨79,by decide⟩,⟨269,by decide⟩,⟨269,by decide⟩]

def ntree11LLLRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLRLLRRL i else ntree11LLLRLLRRR (i - 8)

def ntree11LLLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRLLRL i else ntree11LLLRLLRR (i - 15)

def ntree11LLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11LLLRLLL i else ntree11LLLRLLR (i - 30)

def ntree11LLLRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 1 => ![⟨85,by decide⟩,⟨271,by decide⟩,⟨271,by decide⟩] | 2 => ![⟨87,by decide⟩,⟨272,by decide⟩,⟨272,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨270,by decide⟩,⟨273,by decide⟩] | 4 => ![⟨274,by decide⟩,⟨274,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨275,by decide⟩,⟨275,by decide⟩,⟨79,by decide⟩] | _ => ![⟨276,by decide⟩,⟨277,by decide⟩,⟨47,by decide⟩]

def ntree11LLLRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨278,by decide⟩,⟨279,by decide⟩,⟨108,by decide⟩] | 1 => ![⟨196,by decide⟩,⟨280,by decide⟩,⟨268,by decide⟩] | 2 => ![⟨277,by decide⟩,⟨277,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨279,by decide⟩,⟨279,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨201,by decide⟩,⟨281,by decide⟩,⟨270,by decide⟩] | 5 => ![⟨282,by decide⟩,⟨282,by decide⟩,⟨87,by decide⟩] | 6 => ![⟨206,by decide⟩,⟨283,by decide⟩,⟨270,by decide⟩] | _ => ![⟨245,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩]

def ntree11LLLRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRLRLLL i else ntree11LLLRLRLLR (i - 7)

def ntree11LLLRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨284,by decide⟩,⟨253,by decide⟩,⟨108,by decide⟩] | 1 => ![⟨285,by decide⟩,⟨285,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨286,by decide⟩,⟨285,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨287,by decide⟩,⟨270,by decide⟩] | 4 => ![⟨288,by decide⟩,⟨263,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨263,by decide⟩,⟨263,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨289,by decide⟩,⟨289,by decide⟩] | _ => ![⟨4,by decide⟩,⟨290,by decide⟩,⟨290,by decide⟩]

def ntree11LLLRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨8,by decide⟩,⟨291,by decide⟩,⟨291,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨292,by decide⟩] | 2 => ![⟨47,by decide⟩,⟨293,by decide⟩,⟨294,by decide⟩] | 3 => ![⟨87,by decide⟩,⟨87,by decide⟩,⟨295,by decide⟩] | 4 => ![⟨68,by decide⟩,⟨270,by decide⟩,⟨296,by decide⟩] | 5 => ![⟨67,by decide⟩,⟨291,by decide⟩,⟨297,by decide⟩] | 6 => ![⟨298,by decide⟩,⟨243,by decide⟩,⟨108,by decide⟩] | _ => ![⟨299,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩]

def ntree11LLLRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLRLRLRL i else ntree11LLLRLRLRR (i - 8)

def ntree11LLLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRLRLL i else ntree11LLLRLRLR (i - 15)

def ntree11LLLRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨161,by decide⟩,⟨300,by decide⟩,⟨268,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨301,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨174,by decide⟩,⟨302,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨303,by decide⟩,⟨251,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨304,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨305,by decide⟩,⟨256,by decide⟩,⟨120,by decide⟩] | _ => ![⟨306,by decide⟩,⟨253,by decide⟩,⟨121,by decide⟩]

def ntree11LLLRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨179,by decide⟩,⟨307,by decide⟩,⟨293,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨293,by decide⟩,⟨293,by decide⟩] | 2 => ![⟨182,by decide⟩,⟨308,by decide⟩,⟨291,by decide⟩] | 3 => ![⟨309,by decide⟩,⟨265,by decide⟩,⟨67,by decide⟩] | 4 => ![⟨310,by decide⟩,⟨263,by decide⟩,⟨68,by decide⟩] | 5 => ![⟨311,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨155,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨312,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRLRRLL i else ntree11LLLRLRRLR (i - 7)

def ntree11LLLRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨311,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 1 => ![⟨156,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨312,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨312,by decide⟩,⟨153,by decide⟩,⟨237,by decide⟩] | 4 => ![⟨313,by decide⟩,⟨153,by decide⟩,⟨240,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨314,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨315,by decide⟩] | _ => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨316,by decide⟩]

def ntree11LLLRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨317,by decide⟩,⟨317,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨318,by decide⟩,⟨318,by decide⟩] | 2 => ![⟨319,by decide⟩,⟨319,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨320,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨321,by decide⟩,⟨96,by decide⟩,⟨315,by decide⟩] | 5 => ![⟨322,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨323,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨324,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLRLRRRL i else ntree11LLLRLRRRR (i - 8)

def ntree11LLLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRLRRL i else ntree11LLLRLRRR (i - 15)

def ntree11LLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLLRLRL i else ntree11LLLRLRR (i - 31)

def ntree11LLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11LLLRLL i else ntree11LLLRLR (i - 61)

def ntree11LLLRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨325,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 1 => ![⟨326,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨83,by decide⟩,⟨327,by decide⟩,⟨327,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨328,by decide⟩,⟨328,by decide⟩] | 4 => ![⟨34,by decide⟩,⟨10,by decide⟩,⟨329,by decide⟩] | 5 => ![⟨135,by decide⟩,⟨173,by decide⟩,⟨330,by decide⟩] | _ => ![⟨190,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨331,by decide⟩,⟨332,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨333,by decide⟩,⟨334,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨108,by decide⟩,⟨317,by decide⟩,⟨335,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨318,by decide⟩,⟨336,by decide⟩] | 4 => ![⟨337,by decide⟩,⟨338,by decide⟩,⟨173,by decide⟩] | 5 => ![⟨339,by decide⟩,⟨340,by decide⟩,⟨317,by decide⟩] | 6 => ![⟨206,by decide⟩,⟨341,by decide⟩,⟨318,by decide⟩] | _ => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨342,by decide⟩]

def ntree11LLLRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRRLLLL i else ntree11LLLRRLLLR (i - 7)

def ntree11LLLRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨96,by decide⟩,⟨343,by decide⟩] | 1 => ![⟨337,by decide⟩,⟨337,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨339,by decide⟩,⟨339,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 4 => ![⟨142,by decide⟩,⟨344,by decide⟩,⟨344,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨346,by decide⟩,⟨346,by decide⟩] | _ => ![⟨10,by decide⟩,⟨347,by decide⟩,⟨347,by decide⟩]

def ntree11LLLRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨343,by decide⟩] | 1 => ![⟨108,by decide⟩,⟨348,by decide⟩,⟨349,by decide⟩] | 2 => ![⟨85,by decide⟩,⟨348,by decide⟩,⟨348,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨350,by decide⟩,⟨351,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨350,by decide⟩,⟨350,by decide⟩] | 5 => ![⟨319,by decide⟩,⟨352,by decide⟩,⟨348,by decide⟩] | 6 => ![⟨174,by decide⟩,⟨353,by decide⟩,⟨350,by decide⟩] | _ => ![⟨10,by decide⟩,⟨125,by decide⟩,⟨315,by decide⟩]

def ntree11LLLRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLRRLLRL i else ntree11LLLRRLLRR (i - 8)

def ntree11LLLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRRLLL i else ntree11LLLRRLLR (i - 15)

def ntree11LLLRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨83,by decide⟩,⟨354,by decide⟩,⟨354,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨355,by decide⟩,⟨355,by decide⟩] | 2 => ![⟨63,by decide⟩,⟨293,by decide⟩,⟨356,by decide⟩] | 3 => ![⟨357,by decide⟩,⟨358,by decide⟩,⟨358,by decide⟩] | 4 => ![⟨359,by decide⟩,⟨360,by decide⟩,⟨358,by decide⟩] | 5 => ![⟨359,by decide⟩,⟨359,by decide⟩,⟨357,by decide⟩] | _ => ![⟨357,by decide⟩,⟨357,by decide⟩,⟨357,by decide⟩]

def ntree11LLLRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨157,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨158,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨361,by decide⟩,⟨171,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨361,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨362,by decide⟩,⟨173,by decide⟩] | 6 => ![⟨163,by decide⟩,⟨363,by decide⟩,⟨364,by decide⟩] | _ => ![⟨365,by decide⟩,⟨366,by decide⟩,⟨367,by decide⟩]

def ntree11LLLRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRRLRLL i else ntree11LLLRRLRLR (i - 7)

def ntree11LLLRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨368,by decide⟩,⟨163,by decide⟩,⟨369,by decide⟩] | 1 => ![⟨369,by decide⟩,⟨10,by decide⟩,⟨369,by decide⟩] | 2 => ![⟨365,by decide⟩,⟨365,by decide⟩,⟨370,by decide⟩] | 3 => ![⟨371,by decide⟩,⟨14,by decide⟩,⟨369,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨372,by decide⟩,⟨22,by decide⟩] | 5 => ![⟨172,by decide⟩,⟨361,by decide⟩,⟨24,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨373,by decide⟩,⟨22,by decide⟩] | _ => ![⟨374,by decide⟩,⟨11,by decide⟩,⟨375,by decide⟩]

def ntree11LLLRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨376,by decide⟩,⟨377,by decide⟩,⟨377,by decide⟩] | 1 => ![⟨374,by decide⟩,⟨173,by decide⟩,⟨378,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨379,by decide⟩,⟨11,by decide⟩] | 3 => ![⟨380,by decide⟩,⟨381,by decide⟩,⟨377,by decide⟩] | 4 => ![⟨382,by decide⟩,⟨383,by decide⟩,⟨173,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨384,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨167,by decide⟩,⟨384,by decide⟩,⟨10,by decide⟩] | _ => ![⟨376,by decide⟩,⟨376,by decide⟩,⟨376,by decide⟩]

def ntree11LLLRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLRRLRRL i else ntree11LLLRRLRRR (i - 8)

def ntree11LLLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRRLRL i else ntree11LLLRRLRR (i - 15)

def ntree11LLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLLRRLL i else ntree11LLLRRLR (i - 31)

def ntree11LLLRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨380,by decide⟩,⟨380,by decide⟩,⟨376,by decide⟩] | 1 => ![⟨376,by decide⟩,⟨385,by decide⟩,⟨385,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨386,by decide⟩,⟨40,by decide⟩] | 3 => ![⟨382,by decide⟩,⟨382,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨172,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 5 => ![⟨42,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨387,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨388,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨389,by decide⟩,⟨191,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨390,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨190,by decide⟩,⟨388,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨361,by decide⟩,⟨47,by decide⟩] | 6 => ![⟨49,by decide⟩,⟨362,by decide⟩,⟨205,by decide⟩] | _ => ![⟨391,by decide⟩,⟨392,by decide⟩,⟨391,by decide⟩]

def ntree11LLLRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRRRLLL i else ntree11LLLRRRLLR (i - 7)

def ntree11LLLRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨393,by decide⟩,⟨394,by decide⟩,⟨395,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨396,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨397,by decide⟩,⟨391,by decide⟩,⟨397,by decide⟩] | 3 => ![⟨398,by decide⟩,⟨393,by decide⟩,⟨397,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨214,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨22,by decide⟩,⟨22,by decide⟩] | _ => ![⟨391,by decide⟩,⟨391,by decide⟩,⟨391,by decide⟩]

def ntree11LLLRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨399,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨393,by decide⟩,⟨393,by decide⟩,⟨391,by decide⟩] | 2 => ![⟨201,by decide⟩,⟨400,by decide⟩,⟨22,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨361,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨362,by decide⟩,⟨401,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨373,by decide⟩,⟨53,by decide⟩] | 6 => ![⟨402,by decide⟩,⟨377,by decide⟩,⟨403,by decide⟩] | _ => ![⟨376,by decide⟩,⟨376,by decide⟩,⟨404,by decide⟩]

def ntree11LLLRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLRRRLRL i else ntree11LLLRRRLRR (i - 8)

def ntree11LLLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRRRLL i else ntree11LLLRRRLR (i - 15)

def ntree11LLLRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨405,by decide⟩,⟨376,by decide⟩,⟨376,by decide⟩] | 1 => ![⟨405,by decide⟩,⟨377,by decide⟩,⟨377,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨406,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨407,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨357,by decide⟩,⟨408,by decide⟩,⟨357,by decide⟩] | 5 => ![⟨357,by decide⟩,⟨409,by decide⟩,⟨357,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨47,by decide⟩,⟨406,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨219,by decide⟩] | 2 => ![⟨47,by decide⟩,⟨407,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨410,by decide⟩,⟨229,by decide⟩] | 4 => ![⟨411,by decide⟩,⟨365,by decide⟩,⟨412,by decide⟩] | 5 => ![⟨413,by decide⟩,⟨14,by decide⟩,⟨414,by decide⟩] | 6 => ![⟨163,by decide⟩,⟨415,by decide⟩,⟨72,by decide⟩] | _ => ![⟨10,by decide⟩,⟨229,by decide⟩,⟨416,by decide⟩]

def ntree11LLLRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLLRRRRLL i else ntree11LLLRRRRLR (i - 7)

def ntree11LLLRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨402,by decide⟩,⟨376,by decide⟩,⟨402,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨417,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨418,by decide⟩,⟨65,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨419,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨61,by decide⟩,⟨229,by decide⟩,⟨229,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨420,by decide⟩,⟨47,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨420,by decide⟩,⟨10,by decide⟩]

def ntree11LLLRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨421,by decide⟩,⟨422,by decide⟩,⟨422,by decide⟩] | 1 => ![⟨421,by decide⟩,⟨421,by decide⟩,⟨421,by decide⟩] | 2 => ![⟨423,by decide⟩,⟨10,by decide⟩,⟨423,by decide⟩] | 3 => ![⟨423,by decide⟩,⟨10,by decide⟩,⟨424,by decide⟩] | 4 => ![⟨425,by decide⟩,⟨10,by decide⟩,⟨426,by decide⟩] | 5 => ![⟨427,by decide⟩,⟨428,by decide⟩,⟨428,by decide⟩] | 6 => ![⟨427,by decide⟩,⟨427,by decide⟩,⟨427,by decide⟩] | _ => ![⟨429,by decide⟩,⟨11,by decide⟩,⟨430,by decide⟩]

def ntree11LLLRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLLRRRRRL i else ntree11LLLRRRRRR (i - 8)

def ntree11LLLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLLRRRRL i else ntree11LLLRRRRR (i - 15)

def ntree11LLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLLRRRL i else ntree11LLLRRRR (i - 31)

def ntree11LLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LLLRRL i else ntree11LLLRRR (i - 62)

def ntree11LLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11LLLRL i else ntree11LLLRR (i - 123)

def ntree11LLL (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11LLLL i else ntree11LLLR (i - 247)

def ntree11LLRLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨431,by decide⟩,⟨85,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨361,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨243,by decide⟩,⟨432,by decide⟩,⟨433,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨434,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨435,by decide⟩,⟨10,by decide⟩,⟨436,by decide⟩] | _ => ![⟨251,by decide⟩,⟨437,by decide⟩,⟨438,by decide⟩]

def ntree11LLRLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨99,by decide⟩,⟨439,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨243,by decide⟩,⟨440,by decide⟩,⟨86,by decide⟩] | 2 => ![⟨85,by decide⟩,⟨441,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨244,by decide⟩,⟨379,by decide⟩,⟨11,by decide⟩] | 4 => ![⟨245,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 5 => ![⟨246,by decide⟩,⟨441,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | _ => ![⟨101,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLRLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLLLLLL i else ntree11LLRLLLLLR (i - 7)

def ntree11LLRLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨442,by decide⟩,⟨163,by decide⟩,⟨426,by decide⟩] | 1 => ![⟨251,by decide⟩,⟨443,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨444,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨245,by decide⟩,⟨444,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨445,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨446,by decide⟩,⟨270,by decide⟩,⟨447,by decide⟩] | _ => ![⟨448,by decide⟩,⟨449,by decide⟩,⟨449,by decide⟩]

def ntree11LLRLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨450,by decide⟩,⟨449,by decide⟩,⟨451,by decide⟩] | 1 => ![⟨108,by decide⟩,⟨431,by decide⟩,⟨108,by decide⟩] | 2 => ![⟨277,by decide⟩,⟨452,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨279,by decide⟩,⟨453,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨94,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨114,by decide⟩,⟨454,by decide⟩,⟨270,by decide⟩] | _ => ![⟨277,by decide⟩,⟨455,by decide⟩,⟨11,by decide⟩]

def ntree11LLRLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLLLLRL i else ntree11LLRLLLLRR (i - 7)

def ntree11LLRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLLLLL i else ntree11LLRLLLLR (i - 15)

def ntree11LLRLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨276,by decide⟩,⟨455,by decide⟩,⟨48,by decide⟩] | 1 => ![⟨277,by decide⟩,⟨277,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨61,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨456,by decide⟩,⟨449,by decide⟩,⟨449,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨457,by decide⟩,⟨457,by decide⟩] | 5 => ![⟨357,by decide⟩,⟨458,by decide⟩,⟨458,by decide⟩] | _ => ![⟨47,by decide⟩,⟨459,by decide⟩,⟨47,by decide⟩]

def ntree11LLRLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨459,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨460,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨461,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨223,by decide⟩,⟨461,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨226,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨462,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨463,by decide⟩,⟨10,by decide⟩] | _ => ![⟨464,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLRLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLLLRLL i else ntree11LLRLLLRLR (i - 7)

def ntree11LLRLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨47,by decide⟩,⟨463,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨85,by decide⟩,⟨431,by decide⟩,⟨314,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨361,by decide⟩,⟨315,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨362,by decide⟩,⟨316,by decide⟩] | 4 => ![⟨128,by decide⟩,⟨465,by decide⟩,⟨317,by decide⟩] | 5 => ![⟨129,by decide⟩,⟨466,by decide⟩,⟨318,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨315,by decide⟩] | _ => ![⟨467,by decide⟩,⟨86,by decide⟩,⟨468,by decide⟩]

def ntree11LLRLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨469,by decide⟩,⟨11,by decide⟩,⟨470,by decide⟩] | 1 => ![⟨471,by decide⟩,⟨377,by decide⟩,⟨472,by decide⟩] | 2 => ![⟨467,by decide⟩,⟨317,by decide⟩,⟨473,by decide⟩] | 3 => ![⟨469,by decide⟩,⟨318,by decide⟩,⟨474,by decide⟩] | 4 => ![⟨376,by decide⟩,⟨376,by decide⟩,⟨475,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨476,by decide⟩,⟨476,by decide⟩] | 6 => ![⟨85,by decide⟩,⟨477,by decide⟩,⟨85,by decide⟩] | _ => ![⟨10,by decide⟩,⟨478,by decide⟩,⟨10,by decide⟩]

def ntree11LLRLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRLLLRRL i else ntree11LLRLLLRRR (i - 8)

def ntree11LLRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLLLRL i else ntree11LLRLLLRR (i - 15)

def ntree11LLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11LLRLLLL i else ntree11LLRLLLR (i - 30)

def ntree11LLRLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨479,by decide⟩,⟨270,by decide⟩] | 1 => ![⟨128,by decide⟩,⟨480,by decide⟩,⟨271,by decide⟩] | 2 => ![⟨129,by decide⟩,⟨481,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨482,by decide⟩,⟨478,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨483,by decide⟩,⟨484,by decide⟩,⟨11,by decide⟩] | 5 => ![⟨485,by decide⟩,⟨486,by decide⟩,⟨449,by decide⟩] | _ => ![⟨139,by decide⟩,⟨465,by decide⟩,⟨335,by decide⟩]

def ntree11LLRLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨140,by decide⟩,⟨466,by decide⟩,⟨336,by decide⟩] | 1 => ![⟨128,by decide⟩,⟨128,by decide⟩,⟨342,by decide⟩] | 2 => ![⟨129,by decide⟩,⟨129,by decide⟩,⟨343,by decide⟩] | 3 => ![⟨142,by decide⟩,⟨487,by decide⟩,⟨142,by decide⟩] | 4 => ![⟨143,by decide⟩,⟨488,by decide⟩,⟨344,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨489,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨376,by decide⟩,⟨490,by decide⟩,⟨490,by decide⟩] | _ => ![⟨491,by decide⟩,⟨492,by decide⟩,⟨492,by decide⟩]

def ntree11LLRLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLLRLLL i else ntree11LLRLLRLLR (i - 7)

def ntree11LLRLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨49,by decide⟩,⟨493,by decide⟩,⟨351,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨493,by decide⟩,⟨350,by decide⟩] | 2 => ![⟨99,by decide⟩,⟨494,by decide⟩,⟨229,by decide⟩] | 3 => ![⟨402,by decide⟩,⟨495,by decide⟩,⟨496,by decide⟩] | 4 => ![⟨376,by decide⟩,⟨495,by decide⟩,⟨495,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨497,by decide⟩,⟨497,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨498,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2,by decide⟩,⟨499,by decide⟩,⟨500,by decide⟩]

def ntree11LLRLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨0,by decide⟩,⟨500,by decide⟩,⟨500,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨501,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨502,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨12,by decide⟩,⟨503,by decide⟩,⟨504,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨505,by decide⟩,⟨506,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨504,by decide⟩,⟨504,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨507,by decide⟩,⟨508,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨508,by decide⟩]

def ntree11LLRLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRLLRLRL i else ntree11LLRLLRLRR (i - 8)

def ntree11LLRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLLRLL i else ntree11LLRLLRLR (i - 15)

def ntree11LLRLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨508,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨509,by decide⟩,⟨510,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨510,by decide⟩,⟨510,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨511,by decide⟩] | 4 => ![⟨12,by decide⟩,⟨12,by decide⟩,⟨511,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨501,by decide⟩,⟨511,by decide⟩] | _ => ![⟨10,by decide⟩,⟨502,by decide⟩,⟨508,by decide⟩]

def ntree11LLRLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨512,by decide⟩,⟨512,by decide⟩,⟨512,by decide⟩] | 1 => ![⟨513,by decide⟩,⟨513,by decide⟩,⟨512,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 3 => ![⟨515,by decide⟩,⟨515,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨512,by decide⟩,⟨516,by decide⟩,⟨516,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨507,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨514,by decide⟩,⟨517,by decide⟩,⟨517,by decide⟩] | _ => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨518,by decide⟩]

def ntree11LLRLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLLRRLL i else ntree11LLRLLRRLR (i - 7)

def ntree11LLRLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨22,by decide⟩,⟨519,by decide⟩] | 1 => ![⟨520,by decide⟩,⟨520,by decide⟩,⟨514,by decide⟩] | 2 => ![⟨521,by decide⟩,⟨521,by decide⟩,⟨521,by decide⟩] | 3 => ![⟨30,by decide⟩,⟨522,by decide⟩,⟨523,by decide⟩] | 4 => ![⟨514,by decide⟩,⟨524,by decide⟩,⟨524,by decide⟩] | 5 => ![⟨514,by decide⟩,⟨525,by decide⟩,⟨514,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11LLRLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨38,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨526,by decide⟩,⟨526,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨527,by decide⟩,⟨526,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨528,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨530,by decide⟩,⟨529,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | _ => ![⟨47,by decide⟩,⟨529,by decide⟩,⟨531,by decide⟩]

def ntree11LLRLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRLLRRRL i else ntree11LLRLLRRRR (i - 8)

def ntree11LLRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLLRRL i else ntree11LLRLLRRR (i - 15)

def ntree11LLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLRLLRL i else ntree11LLRLLRR (i - 31)

def ntree11LLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11LLRLLL i else ntree11LLRLLR (i - 61)

def ntree11LLRLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨49,by decide⟩,⟨530,by decide⟩,⟨531,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨508,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨532,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨532,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨528,by decide⟩,⟨531,by decide⟩] | 5 => ![⟨49,by decide⟩,⟨505,by decide⟩,⟨533,by decide⟩] | _ => ![⟨47,by decide⟩,⟨506,by decide⟩,⟨533,by decide⟩]

def ntree11LLRLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨0,by decide⟩,⟨534,by decide⟩,⟨534,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨535,by decide⟩,⟨535,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨508,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨536,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨535,by decide⟩,⟨537,by decide⟩] | 5 => ![⟨538,by decide⟩,⟨10,by decide⟩,⟨538,by decide⟩] | 6 => ![⟨539,by decide⟩,⟨10,by decide⟩,⟨539,by decide⟩] | _ => ![⟨540,by decide⟩,⟨30,by decide⟩,⟨538,by decide⟩]

def ntree11LLRLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLRLLLL i else ntree11LLRLRLLLR (i - 7)

def ntree11LLRLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨541,by decide⟩,⟨10,by decide⟩,⟨541,by decide⟩] | 1 => ![⟨542,by decide⟩,⟨543,by decide⟩,⟨542,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨544,by decide⟩,⟨544,by decide⟩] | 3 => ![⟨30,by decide⟩,⟨545,by decide⟩,⟨544,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨546,by decide⟩,⟨546,by decide⟩] | 5 => ![⟨543,by decide⟩,⟨543,by decide⟩,⟨543,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨547,by decide⟩,⟨10,by decide⟩] | _ => ![⟨47,by decide⟩,⟨547,by decide⟩,⟨47,by decide⟩]

def ntree11LLRLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨538,by decide⟩,⟨10,by decide⟩,⟨538,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨502,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨541,by decide⟩,⟨502,by decide⟩,⟨541,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨548,by decide⟩,⟨548,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨549,by decide⟩,⟨549,by decide⟩] | _ => ![⟨12,by decide⟩,⟨550,by decide⟩,⟨548,by decide⟩]

def ntree11LLRLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRLRLLRL i else ntree11LLRLRLLRR (i - 8)

def ntree11LLRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLRLLL i else ntree11LLRLRLLR (i - 15)

def ntree11LLRLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨551,by decide⟩,⟨549,by decide⟩] | 1 => ![⟨67,by decide⟩,⟨548,by decide⟩,⟨552,by decide⟩] | 2 => ![⟨68,by decide⟩,⟨549,by decide⟩,⟨553,by decide⟩] | 3 => ![⟨69,by decide⟩,⟨550,by decide⟩,⟨552,by decide⟩] | 4 => ![⟨70,by decide⟩,⟨551,by decide⟩,⟨553,by decide⟩] | 5 => ![⟨554,by decide⟩,⟨512,by decide⟩,⟨554,by decide⟩] | _ => ![⟨555,by decide⟩,⟨0,by decide⟩,⟨555,by decide⟩]

def ntree11LLRLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨556,by decide⟩,⟨514,by decide⟩,⟨556,by decide⟩] | 1 => ![⟨512,by decide⟩,⟨557,by decide⟩,⟨557,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨558,by decide⟩,⟨558,by decide⟩] | 3 => ![⟨556,by decide⟩,⟨558,by decide⟩,⟨559,by decide⟩] | 4 => ![⟨560,by decide⟩,⟨72,by decide⟩,⟨561,by decide⟩] | 5 => ![⟨560,by decide⟩,⟨10,by decide⟩,⟨560,by decide⟩] | 6 => ![⟨562,by decide⟩,⟨10,by decide⟩,⟨562,by decide⟩] | _ => ![⟨563,by decide⟩,⟨8,by decide⟩,⟨563,by decide⟩]

def ntree11LLRLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLRLRLL i else ntree11LLRLRLRLR (i - 7)

def ntree11LLRLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨564,by decide⟩,⟨30,by decide⟩,⟨562,by decide⟩] | 1 => ![⟨565,by decide⟩,⟨514,by decide⟩,⟨565,by decide⟩] | 2 => ![⟨566,by decide⟩,⟨521,by decide⟩,⟨566,by decide⟩] | 3 => ![⟨514,by decide⟩,⟨567,by decide⟩,⟨567,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨568,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨569,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨67,by decide⟩,⟨568,by decide⟩,⟨67,by decide⟩] | _ => ![⟨68,by decide⟩,⟨569,by decide⟩,⟨68,by decide⟩]

def ntree11LLRLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨0,by decide⟩,⟨570,by decide⟩,⟨570,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨571,by decide⟩,⟨571,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨572,by decide⟩,⟨572,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨573,by decide⟩,⟨573,by decide⟩] | 4 => ![⟨574,by decide⟩,⟨0,by decide⟩,⟨574,by decide⟩] | 5 => ![⟨574,by decide⟩,⟨500,by decide⟩,⟨575,by decide⟩] | 6 => ![⟨576,by decide⟩,⟨4,by decide⟩,⟨576,by decide⟩] | _ => ![⟨577,by decide⟩,⟨8,by decide⟩,⟨577,by decide⟩]

def ntree11LLRLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRLRLRRL i else ntree11LLRLRLRRR (i - 8)

def ntree11LLRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLRLRL i else ntree11LLRLRLRR (i - 15)

def ntree11LLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLRLRLL i else ntree11LLRLRLR (i - 31)

def ntree11LLRLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨578,by decide⟩,⟨10,by decide⟩,⟨578,by decide⟩] | 1 => ![⟨577,by decide⟩,⟨504,by decide⟩,⟨579,by decide⟩] | 2 => ![⟨578,by decide⟩,⟨506,by decide⟩,⟨580,by decide⟩] | 3 => ![⟨581,by decide⟩,⟨582,by decide⟩,⟨583,by decide⟩] | 4 => ![⟨584,by decide⟩,⟨584,by decide⟩,⟨585,by decide⟩] | 5 => ![⟨581,by decide⟩,⟨510,by decide⟩,⟨586,by decide⟩] | _ => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩]

def ntree11LLRLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨587,by decide⟩,⟨588,by decide⟩,⟨589,by decide⟩] | 1 => ![⟨587,by decide⟩,⟨8,by decide⟩,⟨587,by decide⟩] | 2 => ![⟨590,by decide⟩,⟨590,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨591,by decide⟩,⟨591,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨592,by decide⟩,⟨592,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨593,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨594,by decide⟩,⟨594,by decide⟩,⟨10,by decide⟩] | _ => ![⟨595,by decide⟩,⟨0,by decide⟩,⟨595,by decide⟩]

def ntree11LLRLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLRRLLL i else ntree11LLRLRRLLR (i - 7)

def ntree11LLRLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨596,by decide⟩,⟨10,by decide⟩,⟨596,by decide⟩] | 1 => ![⟨596,by decide⟩,⟨510,by decide⟩,⟨597,by decide⟩] | 2 => ![⟨95,by decide⟩,⟨510,by decide⟩,⟨510,by decide⟩] | 3 => ![⟨598,by decide⟩,⟨438,by decide⟩,⟨599,by decide⟩] | 4 => ![⟨99,by decide⟩,⟨99,by decide⟩,⟨508,by decide⟩] | 5 => ![⟨598,by decide⟩,⟨10,by decide⟩,⟨598,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨600,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨601,by decide⟩,⟨10,by decide⟩]

def ntree11LLRLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨602,by decide⟩,⟨602,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨523,by decide⟩,⟨603,by decide⟩] | 2 => ![⟨604,by decide⟩,⟨602,by decide⟩,⟨581,by decide⟩] | 3 => ![⟨101,by decide⟩,⟨523,by decide⟩,⟨523,by decide⟩] | 4 => ![⟨581,by decide⟩,⟨38,by decide⟩,⟨581,by decide⟩] | 5 => ![⟨584,by decide⟩,⟨584,by decide⟩,⟨584,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨605,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨606,by decide⟩,⟨10,by decide⟩]

def ntree11LLRLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRLRRLRL i else ntree11LLRLRRLRR (i - 8)

def ntree11LLRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLRRLL i else ntree11LLRLRRLR (i - 15)

def ntree11LLRLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨44,by decide⟩,⟨570,by decide⟩,⟨607,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨573,by decide⟩,⟨608,by decide⟩] | 2 => ![⟨574,by decide⟩,⟨526,by decide⟩,⟨609,by decide⟩] | 3 => ![⟨610,by decide⟩,⟨0,by decide⟩,⟨610,by decide⟩] | 4 => ![⟨578,by decide⟩,⟨529,by decide⟩,⟨611,by decide⟩] | 5 => ![⟨612,by decide⟩,⟨529,by decide⟩,⟨613,by decide⟩] | _ => ![⟨614,by decide⟩,⟨615,by decide⟩,⟨616,by decide⟩]

def ntree11LLRLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨614,by decide⟩,⟨617,by decide⟩,⟨614,by decide⟩] | 1 => ![⟨618,by decide⟩,⟨10,by decide⟩,⟨619,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨620,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨593,by decide⟩,⟨47,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLRLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRLRRRLL i else ntree11LLRLRRRLR (i - 7)

def ntree11LLRLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨95,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 1 => ![⟨114,by decide⟩,⟨114,by decide⟩,⟨508,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨621,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨581,by decide⟩,⟨544,by decide⟩,⟨622,by decide⟩] | 5 => ![⟨623,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 6 => ![⟨118,by decide⟩,⟨544,by decide⟩,⟨544,by decide⟩] | _ => ![⟨618,by decide⟩,⟨10,by decide⟩,⟨618,by decide⟩]

def ntree11LLRLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨624,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 3 => ![⟨625,by decide⟩,⟨526,by decide⟩,⟨626,by decide⟩] | 4 => ![⟨625,by decide⟩,⟨0,by decide⟩,⟨625,by decide⟩] | 5 => ![⟨627,by decide⟩,⟨4,by decide⟩,⟨627,by decide⟩] | 6 => ![⟨628,by decide⟩,⟨548,by decide⟩,⟨629,by decide⟩] | _ => ![⟨630,by decide⟩,⟨549,by decide⟩,⟨631,by decide⟩]

def ntree11LLRLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRLRRRRL i else ntree11LLRLRRRRR (i - 8)

def ntree11LLRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRLRRRL i else ntree11LLRLRRRR (i - 15)

def ntree11LLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLRLRRL i else ntree11LLRLRRR (i - 31)

def ntree11LLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LLRLRL i else ntree11LLRLRR (i - 62)

def ntree11LLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11LLRLL i else ntree11LLRLR (i - 123)

def ntree11LLRRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨632,by decide⟩,⟨633,by decide⟩,⟨634,by decide⟩] | 1 => ![⟨635,by decide⟩,⟨10,by decide⟩,⟨636,by decide⟩] | 2 => ![⟨637,by decide⟩,⟨8,by decide⟩,⟨638,by decide⟩] | 3 => ![⟨123,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨639,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨635,by decide⟩,⟨544,by decide⟩,⟨640,by decide⟩] | _ => ![⟨635,by decide⟩,⟨10,by decide⟩,⟨635,by decide⟩]

def ntree11LLRRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨637,by decide⟩,⟨8,by decide⟩,⟨637,by decide⟩] | 1 => ![⟨632,by decide⟩,⟨584,by decide⟩,⟨632,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨641,by decide⟩,⟨581,by decide⟩] | 3 => ![⟨642,by decide⟩,⟨643,by decide⟩,⟨603,by decide⟩] | 4 => ![⟨642,by decide⟩,⟨14,by decide⟩,⟨581,by decide⟩] | 5 => ![⟨644,by decide⟩,⟨523,by decide⟩,⟨523,by decide⟩] | 6 => ![⟨645,by decide⟩,⟨12,by decide⟩,⟨587,by decide⟩] | _ => ![⟨646,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11LLRRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRLLLLL i else ntree11LLRRLLLLR (i - 7)

def ntree11LLRRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨647,by decide⟩,⟨648,by decide⟩,⟨581,by decide⟩] | 1 => ![⟨648,by decide⟩,⟨648,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨649,by decide⟩,⟨649,by decide⟩,⟨584,by decide⟩] | 3 => ![⟨644,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨650,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨641,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨643,by decide⟩,⟨523,by decide⟩] | _ => ![⟨651,by decide⟩,⟨14,by decide⟩,⟨598,by decide⟩]

def ntree11LLRRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨652,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨652,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨653,by decide⟩,⟨653,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨654,by decide⟩,⟨654,by decide⟩] | 4 => ![⟨655,by decide⟩,⟨514,by decide⟩,⟨655,by decide⟩] | 5 => ![⟨581,by decide⟩,⟨40,by decide⟩,⟨656,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨657,by decide⟩,⟨544,by decide⟩] | _ => ![⟨658,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩]

def ntree11LLRRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRLLLRL i else ntree11LLRRLLLRR (i - 8)

def ntree11LLRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRLLLL i else ntree11LLRRLLLR (i - 15)

def ntree11LLRRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨659,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨660,by decide⟩,⟨14,by decide⟩,⟨618,by decide⟩] | 2 => ![⟨661,by decide⟩,⟨662,by decide⟩,⟨614,by decide⟩] | 3 => ![⟨663,by decide⟩,⟨664,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨665,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨665,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLRRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨666,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨666,by decide⟩] | 2 => ![⟨47,by decide⟩,⟨650,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨667,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨668,by decide⟩] | 5 => ![⟨659,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨669,by decide⟩,⟨114,by decide⟩,⟨10,by decide⟩]

def ntree11LLRRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRLLRLL i else ntree11LLRRLLRLR (i - 7)

def ntree11LLRRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨538,by decide⟩,⟨573,by decide⟩,⟨670,by decide⟩] | 1 => ![⟨541,by decide⟩,⟨573,by decide⟩,⟨671,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨65,by decide⟩,⟨672,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨668,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨673,by decide⟩] | 5 => ![⟨674,by decide⟩,⟨142,by decide⟩,⟨674,by decide⟩] | 6 => ![⟨675,by decide⟩,⟨544,by decide⟩,⟨544,by decide⟩] | _ => ![⟨675,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLRRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨676,by decide⟩,⟨657,by decide⟩,⟨640,by decide⟩] | 1 => ![⟨676,by decide⟩,⟨14,by decide⟩,⟨635,by decide⟩] | 2 => ![⟨677,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨678,by decide⟩,⟨12,by decide⟩,⟨637,by decide⟩] | 4 => ![⟨679,by decide⟩,⟨648,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨680,by decide⟩,⟨649,by decide⟩,⟨632,by decide⟩] | 6 => ![⟨659,by decide⟩,⟨76,by decide⟩,⟨76,by decide⟩] | _ => ![⟨681,by decide⟩,⟨99,by decide⟩,⟨560,by decide⟩]

def ntree11LLRRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRLLRRL i else ntree11LLRRLLRRR (i - 8)

def ntree11LLRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRLLRL i else ntree11LLRRLLRR (i - 15)

def ntree11LLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLRRLLL i else ntree11LLRRLLR (i - 31)

def ntree11LLRRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨0,by decide⟩,⟨682,by decide⟩,⟨682,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨683,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨684,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨685,by decide⟩,⟨685,by decide⟩] | 4 => ![⟨686,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨687,by decide⟩,⟨502,by decide⟩,⟨684,by decide⟩] | _ => ![⟨688,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11LLRRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨689,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨690,by decide⟩,⟨690,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨691,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨691,by decide⟩] | 4 => ![⟨512,by decide⟩,⟨692,by decide⟩,⟨692,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨164,by decide⟩] | 6 => ![⟨514,by decide⟩,⟨693,by decide⟩,⟨693,by decide⟩] | _ => ![⟨694,by decide⟩,⟨498,by decide⟩,⟨159,by decide⟩]

def ntree11LLRRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRLRLLL i else ntree11LLRRLRLLR (i - 7)

def ntree11LLRRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨695,by decide⟩,⟨512,by decide⟩,⟨512,by decide⟩] | 1 => ![⟨694,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨696,by decide⟩,⟨507,by decide⟩,⟨164,by decide⟩] | 3 => ![⟨697,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨696,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨698,by decide⟩,⟨507,by decide⟩,⟨171,by decide⟩] | 6 => ![⟨699,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | _ => ![⟨698,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩]

def ntree11LLRRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨698,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨700,by decide⟩,⟨173,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨701,by decide⟩,⟨701,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨702,by decide⟩] | 4 => ![⟨703,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨698,by decide⟩,⟨38,by decide⟩,⟨691,by decide⟩] | 6 => ![⟨703,by decide⟩,⟨184,by decide⟩,⟨184,by decide⟩] | _ => ![⟨698,by decide⟩,⟨188,by decide⟩,⟨702,by decide⟩]

def ntree11LLRRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRLRLRL i else ntree11LLRRLRLRR (i - 8)

def ntree11LLRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRLRLL i else ntree11LLRRLRLR (i - 15)

def ntree11LLRRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨0,by decide⟩,⟨704,by decide⟩,⟨704,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨705,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨706,by decide⟩,⟨706,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨707,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨708,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨709,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨502,by decide⟩,⟨707,by decide⟩]

def ntree11LLRRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨710,by decide⟩,⟨710,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨710,by decide⟩,⟨710,by decide⟩] | 2 => ![⟨711,by decide⟩,⟨712,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨713,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨714,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨715,by decide⟩,⟨715,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨716,by decide⟩,⟨716,by decide⟩] | _ => ![⟨694,by decide⟩,⟨708,by decide⟩,⟨202,by decide⟩]

def ntree11LLRRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRLRRLL i else ntree11LLRRLRRLR (i - 7)

def ntree11LLRRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨696,by decide⟩,⟨547,by decide⟩,⟨203,by decide⟩] | 1 => ![⟨717,by decide⟩,⟨718,by decide⟩,⟨47,by decide⟩] | 2 => ![⟨698,by decide⟩,⟨710,by decide⟩,⟨710,by decide⟩] | 3 => ![⟨717,by decide⟩,⟨719,by decide⟩,⟨205,by decide⟩] | 4 => ![⟨698,by decide⟩,⟨720,by decide⟩,⟨720,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨720,by decide⟩,⟨720,by decide⟩] | 6 => ![⟨538,by decide⟩,⟨10,by decide⟩,⟨721,by decide⟩] | _ => ![⟨538,by decide⟩,⟨173,by decide⟩,⟨722,by decide⟩]

def ntree11LLRRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨698,by decide⟩,⟨547,by decide⟩,⟨214,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨212,by decide⟩,⟨212,by decide⟩] | 2 => ![⟨723,by decide⟩,⟨217,by decide⟩,⟨721,by decide⟩] | 3 => ![⟨724,by decide⟩,⟨218,by decide⟩,⟨539,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 5 => ![⟨538,by decide⟩,⟨173,by decide⟩,⟨722,by decide⟩] | 6 => ![⟨68,by decide⟩,⟨706,by decide⟩,⟨725,by decide⟩] | _ => ![⟨10,by decide⟩,⟨569,by decide⟩,⟨684,by decide⟩]

def ntree11LLRRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRLRRRL i else ntree11LLRRLRRRR (i - 8)

def ntree11LLRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRLRRL i else ntree11LLRRLRRR (i - 15)

def ntree11LLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLRRLRL i else ntree11LLRRLRR (i - 31)

def ntree11LLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LLRRLL i else ntree11LLRRLR (i - 62)

def ntree11LLRRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨512,by decide⟩,⟨726,by decide⟩,⟨726,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨227,by decide⟩,⟨225,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨727,by decide⟩,⟨727,by decide⟩] | 3 => ![⟨514,by decide⟩,⟨728,by decide⟩,⟨728,by decide⟩] | 4 => ![⟨562,by decide⟩,⟨229,by decide⟩,⟨729,by decide⟩] | 5 => ![⟨574,by decide⟩,⟨0,by decide⟩,⟨730,by decide⟩] | _ => ![⟨578,by decide⟩,⟨10,by decide⟩,⟨731,by decide⟩]

def ntree11LLRRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨732,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨690,by decide⟩,⟨733,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨734,by decide⟩] | 3 => ![⟨735,by decide⟩,⟨735,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨736,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨245,by decide⟩,⟨685,by decide⟩,⟨685,by decide⟩] | 6 => ![⟨737,by decide⟩,⟨735,by decide⟩,⟨595,by decide⟩] | _ => ![⟨738,by decide⟩,⟨251,by decide⟩,⟨596,by decide⟩]

def ntree11LLRRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRRLLLL i else ntree11LLRRRLLLR (i - 7)

def ntree11LLRRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨739,by decide⟩,⟨251,by decide⟩,⟨598,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨740,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨741,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨263,by decide⟩,⟨263,by decide⟩,⟨691,by decide⟩] | 4 => ![⟨742,by decide⟩,⟨263,by decide⟩,⟨581,by decide⟩] | 5 => ![⟨743,by decide⟩,⟨265,by decide⟩,⟨587,by decide⟩] | 6 => ![⟨742,by decide⟩,⟨266,by decide⟩,⟨734,by decide⟩] | _ => ![⟨744,by decide⟩,⟨584,by decide⟩,⟨584,by decide⟩]

def ntree11LLRRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨698,by decide⟩,⟨740,by decide⟩,⟨732,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨745,by decide⟩,⟨238,by decide⟩] | 2 => ![⟨746,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 3 => ![⟨581,by decide⟩,⟨690,by decide⟩,⟨733,by decide⟩] | 4 => ![⟨574,by decide⟩,⟨268,by decide⟩,⟨747,by decide⟩] | 5 => ![⟨612,by decide⟩,⟨10,by decide⟩,⟨612,by decide⟩] | 6 => ![⟨578,by decide⟩,⟨270,by decide⟩,⟨748,by decide⟩] | _ => ![⟨581,by decide⟩,⟨710,by decide⟩,⟨749,by decide⟩]

def ntree11LLRRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRRLLRL i else ntree11LLRRRLLRR (i - 8)

def ntree11LLRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRRLLL i else ntree11LLRRRLLR (i - 15)

def ntree11LLRRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨581,by decide⟩,⟨270,by decide⟩,⟨750,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨245,by decide⟩,⟨706,by decide⟩,⟨706,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨751,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨752,by decide⟩,⟨274,by decide⟩,⟨610,by decide⟩] | 5 => ![⟨694,by decide⟩,⟨268,by decide⟩,⟨268,by decide⟩] | _ => ![⟨753,by decide⟩,⟨277,by decide⟩,⟨612,by decide⟩]

def ntree11LLRRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨696,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 1 => ![⟨754,by decide⟩,⟨277,by decide⟩,⟨618,by decide⟩] | 2 => ![⟨698,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨263,by decide⟩,⟨755,by decide⟩,⟨710,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨756,by decide⟩,⟨277,by decide⟩,⟨581,by decide⟩] | 6 => ![⟨757,by decide⟩,⟨758,by decide⟩,⟨614,by decide⟩] | _ => ![⟨742,by decide⟩,⟨755,by decide⟩,⟨749,by decide⟩]

def ntree11LLRRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRRLRLL i else ntree11LLRRRLRLR (i - 7)

def ntree11LLRRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨625,by decide⟩,⟨268,by decide⟩,⟨759,by decide⟩] | 1 => ![⟨628,by decide⟩,⟨8,by decide⟩,⟨628,by decide⟩] | 2 => ![⟨630,by decide⟩,⟨270,by decide⟩,⟨760,by decide⟩] | 3 => ![⟨635,by decide⟩,⟨710,by decide⟩,⟨761,by decide⟩] | 4 => ![⟨635,by decide⟩,⟨270,by decide⟩,⟨762,by decide⟩] | 5 => ![⟨304,by decide⟩,⟨706,by decide⟩,⟨706,by decide⟩] | 6 => ![⟨763,by decide⟩,⟨763,by decide⟩,⟨10,by decide⟩] | _ => ![⟨764,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLRRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨765,by decide⟩,⟨763,by decide⟩,⟨581,by decide⟩] | 1 => ![⟨766,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨767,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨768,by decide⟩,⟨768,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨764,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 5 => ![⟨769,by decide⟩,⟨641,by decide⟩,⟨171,by decide⟩] | 6 => ![⟨770,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | _ => ![⟨769,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LLRRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRRLRRL i else ntree11LLRRRLRRR (i - 8)

def ntree11LLRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRRLRL i else ntree11LLRRRLRR (i - 15)

def ntree11LLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLRRRLL i else ntree11LLRRRLR (i - 31)

def ntree11LLRRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨771,by decide⟩,⟨768,by decide⟩,⟨598,by decide⟩] | 1 => ![⟨772,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨598,by decide⟩,⟨173,by decide⟩,⟨773,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨774,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨775,by decide⟩] | 5 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨776,by decide⟩] | _ => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨777,by decide⟩]

def ntree11LLRRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨584,by decide⟩,⟨778,by decide⟩,⟨778,by decide⟩] | 1 => ![⟨135,by decide⟩,⟨173,by decide⟩,⟨779,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨173,by decide⟩,⟨780,by decide⟩] | 3 => ![⟨655,by decide⟩,⟨701,by decide⟩,⟨781,by decide⟩] | 4 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨782,by decide⟩] | 5 => ![⟨587,by decide⟩,⟨184,by decide⟩,⟨783,by decide⟩] | 6 => ![⟨581,by decide⟩,⟨173,by decide⟩,⟨784,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨785,by decide⟩]

def ntree11LLRRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRRRLLL i else ntree11LLRRRRLLR (i - 7)

def ntree11LLRRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨786,by decide⟩] | 1 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨787,by decide⟩] | 2 => ![⟨521,by decide⟩,⟨521,by decide⟩,⟨788,by decide⟩] | 3 => ![⟨789,by decide⟩,⟨789,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨790,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨791,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨792,by decide⟩,⟨789,by decide⟩,⟨581,by decide⟩] | _ => ![⟨790,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩]

def ntree11LLRRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨769,by decide⟩,⟨791,by decide⟩,⟨214,by decide⟩] | 3 => ![⟨793,by decide⟩,⟨337,by decide⟩,⟨618,by decide⟩] | 4 => ![⟨769,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 5 => ![⟨794,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨618,by decide⟩,⟨173,by decide⟩,⟨795,by decide⟩] | _ => ![⟨581,by decide⟩,⟨796,by decide⟩,⟨797,by decide⟩]

def ntree11LLRRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRRRLRL i else ntree11LLRRRRLRR (i - 8)

def ntree11LLRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRRRLL i else ntree11LLRRRRLR (i - 15)

def ntree11LLRRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨798,by decide⟩,⟨798,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨799,by decide⟩,⟨799,by decide⟩] | 2 => ![⟨543,by decide⟩,⟨800,by decide⟩,⟨800,by decide⟩] | 3 => ![⟨614,by decide⟩,⟨801,by decide⟩,⟨802,by decide⟩] | 4 => ![⟨581,by decide⟩,⟨173,by decide⟩,⟨803,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨798,by decide⟩,⟨804,by decide⟩] | _ => ![⟨581,by decide⟩,⟨212,by decide⟩,⟨805,by decide⟩]

def ntree11LLRRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨674,by decide⟩,⟨142,by decide⟩,⟨806,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨173,by decide⟩,⟨807,by decide⟩] | 2 => ![⟨674,by decide⟩,⟨344,by decide⟩,⟨808,by decide⟩] | 3 => ![⟨539,by decide⟩,⟨270,by decide⟩,⟨809,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨799,by decide⟩,⟨810,by decide⟩] | 5 => ![⟨541,by decide⟩,⟨270,by decide⟩,⟨811,by decide⟩] | 6 => ![⟨542,by decide⟩,⟨800,by decide⟩,⟨812,by decide⟩] | _ => ![⟨763,by decide⟩,⟨813,by decide⟩,⟨710,by decide⟩]

def ntree11LLRRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LLRRRRRLL i else ntree11LLRRRRRLR (i - 7)

def ntree11LLRRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨790,by decide⟩,⟨10,by decide⟩,⟨691,by decide⟩] | 1 => ![⟨635,by decide⟩,⟨791,by decide⟩,⟨635,by decide⟩] | 2 => ![⟨814,by decide⟩,⟨763,by decide⟩,⟨635,by decide⟩] | 3 => ![⟨768,by decide⟩,⟨815,by decide⟩,⟨229,by decide⟩] | 4 => ![⟨790,by decide⟩,⟨229,by decide⟩,⟨229,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨816,by decide⟩,⟨816,by decide⟩] | 6 => ![⟨514,by decide⟩,⟨817,by decide⟩,⟨817,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨818,by decide⟩]

def ntree11LLRRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨560,by decide⟩,⟨270,by decide⟩,⟨819,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨816,by decide⟩,⟨820,by decide⟩] | 2 => ![⟨556,by decide⟩,⟨817,by decide⟩,⟨821,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨822,by decide⟩,⟨822,by decide⟩] | 4 => ![⟨514,by decide⟩,⟨823,by decide⟩,⟨823,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨824,by decide⟩,⟨824,by decide⟩] | 6 => ![⟨521,by decide⟩,⟨825,by decide⟩,⟨825,by decide⟩] | _ => ![⟨47,by decide⟩,⟨822,by decide⟩,⟨826,by decide⟩]

def ntree11LLRRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LLRRRRRRL i else ntree11LLRRRRRRR (i - 8)

def ntree11LLRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LLRRRRRL i else ntree11LLRRRRRR (i - 15)

def ntree11LLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LLRRRRL i else ntree11LLRRRRR (i - 31)

def ntree11LLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LLRRRL i else ntree11LLRRRR (i - 62)

def ntree11LLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 124 then ntree11LLRRL i else ntree11LLRRR (i - 124)

def ntree11LLR (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11LLRL i else ntree11LLRR (i - 247)

def ntree11LL (i : Nat) : Fin 3 → Fin 3109 := if i < 494 then ntree11LLL i else ntree11LLR (i - 494)

def ntree11LRLLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨827,by decide⟩] | 1 => ![⟨556,by decide⟩,⟨823,by decide⟩,⟨828,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨829,by decide⟩] | 3 => ![⟨562,by decide⟩,⟨270,by decide⟩,⟨830,by decide⟩] | 4 => ![⟨563,by decide⟩,⟨291,by decide⟩,⟨831,by decide⟩] | 5 => ![⟨67,by decide⟩,⟨824,by decide⟩,⟨832,by decide⟩] | _ => ![⟨565,by decide⟩,⟨817,by decide⟩,⟨833,by decide⟩]

def ntree11LRLLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨566,by decide⟩,⟨825,by decide⟩,⟨834,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨835,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨836,by decide⟩,⟨690,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨684,by decide⟩] | 5 => ![⟨357,by decide⟩,⟨357,by decide⟩,⟨357,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨837,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRLLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLLLLLL i else ntree11LRLLLLLLR (i - 7)

def ntree11LRLLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨838,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨689,by decide⟩,⟨835,by decide⟩,⟨508,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨508,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨839,by decide⟩,⟨510,by decide⟩] | 4 => ![⟨514,by decide⟩,⟨840,by decide⟩,⟨514,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨361,by decide⟩,⟨10,by decide⟩] | _ => ![⟨515,by decide⟩,⟨841,by decide⟩,⟨701,by decide⟩]

def ntree11LRLLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨842,by decide⟩,⟨14,by decide⟩,⟨843,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨22,by decide⟩,⟨22,by decide⟩] | 2 => ![⟨698,by decide⟩,⟨844,by decide⟩,⟨845,by decide⟩] | 3 => ![⟨699,by decide⟩,⟨840,by decide⟩,⟨518,by decide⟩] | 4 => ![⟨842,by decide⟩,⟨362,by decide⟩,⟨846,by decide⟩] | 5 => ![⟨698,by decide⟩,⟨373,by decide⟩,⟨519,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨847,by decide⟩,⟨848,by decide⟩] | _ => ![⟨514,by decide⟩,⟨849,by decide⟩,⟨517,by decide⟩]

def ntree11LRLLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLLLLRL i else ntree11LRLLLLLRR (i - 7)

def ntree11LRLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLLLLL i else ntree11LRLLLLLR (i - 15)

def ntree11LRLLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨698,by decide⟩,⟨361,by decide⟩,⟨508,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨384,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨514,by decide⟩,⟨850,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨851,by decide⟩,⟨382,by decide⟩,⟨852,by decide⟩] | 5 => ![⟨698,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩] | _ => ![⟨853,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRLLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨854,by decide⟩,⟨710,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨855,by decide⟩,⟨47,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨707,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨837,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 6 => ![⟨856,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | _ => ![⟨10,by decide⟩,⟨710,by decide⟩,⟨857,by decide⟩]

def ntree11LRLLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLLLRLL i else ntree11LRLLLLRLR (i - 7)

def ntree11LRLLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨854,by decide⟩,⟨857,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨858,by decide⟩,⟨531,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨859,by decide⟩,⟨710,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨860,by decide⟩,⟨720,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨861,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨698,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 6 => ![⟨842,by decide⟩,⟨530,by decide⟩,⟨862,by decide⟩] | _ => ![⟨698,by decide⟩,⟨535,by decide⟩,⟨535,by decide⟩]

def ntree11LRLLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨717,by decide⟩,⟨863,by decide⟩,⟨531,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨859,by decide⟩,⟨857,by decide⟩] | 2 => ![⟨864,by decide⟩,⟨865,by decide⟩,⟨866,by decide⟩] | 3 => ![⟨842,by decide⟩,⟨860,by decide⟩,⟨867,by decide⟩] | 4 => ![⟨717,by decide⟩,⟨868,by decide⟩,⟨537,by decide⟩] | 5 => ![⟨869,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 6 => ![⟨698,by decide⟩,⟨65,by decide⟩,⟨65,by decide⟩] | _ => ![⟨47,by decide⟩,⟨870,by decide⟩,⟨47,by decide⟩]

def ntree11LRLLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLLLLRRL i else ntree11LRLLLLRRR (i - 8)

def ntree11LRLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLLLRL i else ntree11LRLLLLRR (i - 15)

def ntree11LRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11LRLLLLL i else ntree11LRLLLLR (i - 30)

def ntree11LRLLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨871,by decide⟩] | 2 => ![⟨47,by decide⟩,⟨872,by decide⟩,⟨873,by decide⟩] | 3 => ![⟨514,by decide⟩,⟨728,by decide⟩,⟨874,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨229,by decide⟩,⟨875,by decide⟩] | 5 => ![⟨876,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨877,by decide⟩,⟨10,by decide⟩,⟨877,by decide⟩]

def ntree11LRLLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨878,by decide⟩,⟨878,by decide⟩,⟨878,by decide⟩] | 1 => ![⟨357,by decide⟩,⟨879,by decide⟩,⟨879,by decide⟩] | 2 => ![⟨880,by decide⟩,⟨573,by decide⟩,⟨881,by decide⟩] | 3 => ![⟨882,by decide⟩,⟨357,by decide⟩,⟨882,by decide⟩] | 4 => ![⟨880,by decide⟩,⟨10,by decide⟩,⟨880,by decide⟩] | 5 => ![⟨883,by decide⟩,⟨883,by decide⟩,⟨883,by decide⟩] | 6 => ![⟨578,by decide⟩,⟨510,by decide⟩,⟨884,by decide⟩] | _ => ![⟨885,by decide⟩,⟨357,by decide⟩,⟨885,by decide⟩]

def ntree11LRLLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLLRLLL i else ntree11LRLLLRLLR (i - 7)

def ntree11LRLLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨880,by decide⟩,⟨10,by decide⟩,⟨886,by decide⟩] | 1 => ![⟨883,by decide⟩,⟨883,by decide⟩,⟨887,by decide⟩] | 2 => ![⟨880,by decide⟩,⟨510,by decide⟩,⟨888,by decide⟩] | 3 => ![⟨594,by decide⟩,⟨889,by decide⟩,⟨690,by decide⟩] | 4 => ![⟨880,by decide⟩,⟨361,by decide⟩,⟨880,by decide⟩] | 5 => ![⟨890,by decide⟩,⟨594,by decide⟩,⟨880,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨891,by decide⟩,⟨510,by decide⟩] | _ => ![⟨739,by decide⟩,⟨437,by decide⟩,⟨599,by decide⟩]

def ntree11LRLLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨892,by decide⟩,⟨439,by decide⟩,⟨886,by decide⟩] | 1 => ![⟨598,by decide⟩,⟨361,by decide⟩,⟨598,by decide⟩] | 2 => ![⟨251,by decide⟩,⟨251,by decide⟩,⟨508,by decide⟩] | 3 => ![⟨245,by decide⟩,⟨10,by decide⟩,⟨508,by decide⟩] | 4 => ![⟨245,by decide⟩,⟨510,by decide⟩,⟨510,by decide⟩] | 5 => ![⟨251,by decide⟩,⟨893,by decide⟩,⟨573,by decide⟩] | 6 => ![⟨877,by decide⟩,⟨384,by decide⟩,⟨877,by decide⟩] | _ => ![⟨245,by decide⟩,⟨384,by decide⟩,⟨10,by decide⟩]

def ntree11LRLLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLLLRLRL i else ntree11LRLLLRLRR (i - 8)

def ntree11LRLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLLRLL i else ntree11LRLLLRLR (i - 15)

def ntree11LRLLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨894,by decide⟩,⟨878,by decide⟩,⟨878,by decide⟩] | 1 => ![⟨895,by decide⟩,⟨896,by decide⟩,⟨896,by decide⟩] | 2 => ![⟨897,by decide⟩,⟨895,by decide⟩,⟨897,by decide⟩] | 3 => ![⟨895,by decide⟩,⟨895,by decide⟩,⟨895,by decide⟩] | 4 => ![⟨898,by decide⟩,⟨10,by decide⟩,⟨898,by decide⟩] | 5 => ![⟨899,by decide⟩,⟨883,by decide⟩,⟨899,by decide⟩] | _ => ![⟨900,by decide⟩,⟨895,by decide⟩,⟨900,by decide⟩]

def ntree11LRLLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨895,by decide⟩,⟨901,by decide⟩,⟨901,by decide⟩] | 1 => ![⟨883,by decide⟩,⟨902,by decide⟩,⟨902,by decide⟩] | 2 => ![⟨898,by decide⟩,⟨270,by decide⟩,⟨903,by decide⟩] | 3 => ![⟨899,by decide⟩,⟨902,by decide⟩,⟨904,by decide⟩] | 4 => ![⟨898,by decide⟩,⟨361,by decide⟩,⟨898,by decide⟩] | 5 => ![⟨905,by decide⟩,⟨10,by decide⟩,⟨898,by decide⟩] | 6 => ![⟨277,by decide⟩,⟨906,by decide⟩,⟨529,by decide⟩] | _ => ![⟨754,by decide⟩,⟨452,by decide⟩,⟨619,by decide⟩]

def ntree11LRLLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLLRRLL i else ntree11LRLLLRRLR (i - 7)

def ntree11LRLLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨907,by decide⟩,⟨454,by decide⟩,⟨903,by decide⟩] | 1 => ![⟨276,by decide⟩,⟨906,by decide⟩,⟨531,by decide⟩] | 2 => ![⟨905,by decide⟩,⟨270,by decide⟩,⟨903,by decide⟩] | 3 => ![⟨908,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨698,by decide⟩,⟨909,by decide⟩,⟨624,by decide⟩] | 5 => ![⟨910,by decide⟩,⟨895,by decide⟩,⟨895,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨911,by decide⟩,⟨10,by decide⟩] | _ => ![⟨878,by decide⟩,⟨912,by decide⟩,⟨912,by decide⟩]

def ntree11LRLLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨913,by decide⟩,⟨878,by decide⟩,⟨913,by decide⟩] | 1 => ![⟨898,by decide⟩,⟨10,by decide⟩,⟨914,by decide⟩] | 2 => ![⟨915,by decide⟩,⟨357,by decide⟩,⟨915,by decide⟩] | 3 => ![⟨630,by decide⟩,⟨529,by decide⟩,⟨916,by decide⟩] | 4 => ![⟨917,by decide⟩,⟨878,by decide⟩,⟨917,by decide⟩] | 5 => ![⟨878,by decide⟩,⟨918,by decide⟩,⟨918,by decide⟩] | 6 => ![⟨919,by decide⟩,⟨357,by decide⟩,⟨919,by decide⟩] | _ => ![⟨251,by decide⟩,⟨920,by decide⟩,⟨529,by decide⟩]

def ntree11LRLLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLLLRRRL i else ntree11LRLLLRRRR (i - 8)

def ntree11LRLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLLRRL i else ntree11LRLLLRRR (i - 15)

def ntree11LRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRLLLRL i else ntree11LRLLLRR (i - 31)

def ntree11LRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11LRLLLL i else ntree11LRLLLR (i - 61)

def ntree11LRLLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨921,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨922,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨594,by decide⟩,⟨923,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨251,by decide⟩,⟨251,by decide⟩,⟨508,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨303,by decide⟩,⟨920,by decide⟩,⟨531,by decide⟩] | _ => ![⟨304,by decide⟩,⟨921,by decide⟩,⟨508,by decide⟩]

def ntree11LRLLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨47,by decide⟩,⟨922,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨924,by decide⟩,⟨10,by decide⟩,⟨924,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨925,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨763,by decide⟩,⟨926,by decide⟩,⟨573,by decide⟩] | 4 => ![⟨877,by decide⟩,⟨835,by decide⟩,⟨877,by decide⟩] | 5 => ![⟨927,by decide⟩,⟨927,by decide⟩,⟨878,by decide⟩] | 6 => ![⟨878,by decide⟩,⟨878,by decide⟩,⟨878,by decide⟩] | _ => ![⟨598,by decide⟩,⟨361,by decide⟩,⟨598,by decide⟩]

def ntree11LRLLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLRLLLL i else ntree11LRLLRLLLR (i - 7)

def ntree11LRLLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨651,by decide⟩,⟨362,by decide⟩,⟨773,by decide⟩] | 1 => ![⟨652,by decide⟩,⟨361,by decide⟩,⟨774,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨775,by decide⟩] | 4 => ![⟨469,by decide⟩,⟨573,by decide⟩,⟨928,by decide⟩] | 5 => ![⟨929,by decide⟩,⟨514,by decide⟩,⟨929,by decide⟩] | 6 => ![⟨469,by decide⟩,⟨173,by decide⟩,⟨930,by decide⟩] | _ => ![⟨878,by decide⟩,⟨931,by decide⟩,⟨931,by decide⟩]

def ntree11LRLLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨932,by decide⟩,⟨878,by decide⟩,⟨932,by decide⟩] | 1 => ![⟨852,by decide⟩,⟨10,by decide⟩,⟨852,by decide⟩] | 2 => ![⟨933,by decide⟩,⟨933,by decide⟩,⟨895,by decide⟩] | 3 => ![⟨659,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 4 => ![⟨934,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨659,by decide⟩,⟨361,by decide⟩,⟨10,by decide⟩] | _ => ![⟨660,by decide⟩,⟨362,by decide⟩,⟨795,by decide⟩]

def ntree11LRLLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLLRLLRL i else ntree11LRLLRLLRR (i - 8)

def ntree11LRLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLRLLL i else ntree11LRLLRLLR (i - 15)

def ntree11LRLLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨669,by decide⟩,⟨454,by decide⟩,⟨270,by decide⟩] | 1 => ![⟨895,by decide⟩,⟨935,by decide⟩,⟨935,by decide⟩] | 2 => ![⟨927,by decide⟩,⟨936,by decide⟩,⟨912,by decide⟩] | 3 => ![⟨913,by decide⟩,⟨937,by decide⟩,⟨913,by decide⟩] | 4 => ![⟨924,by decide⟩,⟨10,by decide⟩,⟨924,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨938,by decide⟩,⟨10,by decide⟩] | _ => ![⟨514,by decide⟩,⟨939,by decide⟩,⟨514,by decide⟩]

def ntree11LRLLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨940,by decide⟩,⟨816,by decide⟩] | 1 => ![⟨515,by decide⟩,⟨941,by decide⟩,⟨817,by decide⟩] | 2 => ![⟨659,by decide⟩,⟨229,by decide⟩,⟨229,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨818,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨938,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨49,by decide⟩,⟨940,by decide⟩,⟨820,by decide⟩] | 6 => ![⟨942,by decide⟩,⟨507,by decide⟩,⟨942,by decide⟩] | _ => ![⟨942,by decide⟩,⟨10,by decide⟩,⟨942,by decide⟩]

def ntree11LRLLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLRLRLL i else ntree11LRLLRLRLR (i - 7)

def ntree11LRLLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨943,by decide⟩,⟨14,by decide⟩,⟨942,by decide⟩] | 1 => ![⟨943,by decide⟩,⟨509,by decide⟩,⟨944,by decide⟩] | 2 => ![⟨942,by decide⟩,⟨510,by decide⟩,⟨944,by decide⟩] | 3 => ![⟨945,by decide⟩,⟨8,by decide⟩,⟨945,by decide⟩] | 4 => ![⟨946,by decide⟩,⟨12,by decide⟩,⟨945,by decide⟩] | 5 => ![⟨947,by decide⟩,⟨948,by decide⟩,⟨11,by decide⟩] | 6 => ![⟨949,by decide⟩,⟨950,by decide⟩,⟨9,by decide⟩] | _ => ![⟨951,by decide⟩,⟨952,by decide⟩,⟨11,by decide⟩]

def ntree11LRLLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨514,by decide⟩,⟨953,by decide⟩,⟨953,by decide⟩] | 1 => ![⟨954,by decide⟩,⟨10,by decide⟩,⟨954,by decide⟩] | 2 => ![⟨955,by decide⟩,⟨14,by decide⟩,⟨954,by decide⟩] | 3 => ![⟨954,by decide⟩,⟨22,by decide⟩,⟨956,by decide⟩] | 4 => ![⟨951,by decide⟩,⟨957,by decide⟩,⟨18,by decide⟩] | 5 => ![⟨958,by decide⟩,⟨958,by decide⟩,⟨514,by decide⟩] | 6 => ![⟨514,by decide⟩,⟨959,by decide⟩,⟨959,by decide⟩] | _ => ![⟨521,by decide⟩,⟨960,by decide⟩,⟨960,by decide⟩]

def ntree11LRLLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLLRLRRL i else ntree11LRLLRLRRR (i - 8)

def ntree11LRLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLRLRL i else ntree11LRLLRLRR (i - 15)

def ntree11LRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRLLRLL i else ntree11LRLLRLR (i - 31)

def ntree11LRLLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨961,by decide⟩,⟨514,by decide⟩,⟨961,by decide⟩] | 1 => ![⟨942,by decide⟩,⟨38,by decide⟩,⟨942,by decide⟩] | 2 => ![⟨958,by decide⟩,⟨962,by decide⟩,⟨959,by decide⟩] | 3 => ![⟨963,by decide⟩,⟨11,by decide⟩,⟨964,by decide⟩] | 4 => ![⟨965,by decide⟩,⟨15,by decide⟩,⟨964,by decide⟩] | 5 => ![⟨965,by decide⟩,⟨14,by decide⟩,⟨963,by decide⟩] | _ => ![⟨963,by decide⟩,⟨10,by decide⟩,⟨963,by decide⟩]

def ntree11LRLLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨942,by decide⟩,⟨529,by decide⟩,⟨966,by decide⟩] | 1 => ![⟨943,by decide⟩,⟨530,by decide⟩,⟨966,by decide⟩] | 2 => ![⟨967,by decide⟩,⟨10,by decide⟩,⟨942,by decide⟩] | 3 => ![⟨968,by decide⟩,⟨969,by decide⟩,⟨969,by decide⟩] | 4 => ![⟨970,by decide⟩,⟨971,by decide⟩,⟨969,by decide⟩] | 5 => ![⟨970,by decide⟩,⟨970,by decide⟩,⟨968,by decide⟩] | 6 => ![⟨968,by decide⟩,⟨968,by decide⟩,⟨968,by decide⟩] | _ => ![⟨972,by decide⟩,⟨973,by decide⟩,⟨969,by decide⟩]

def ntree11LRLLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLRRLLL i else ntree11LRLLRRLLR (i - 7)

def ntree11LRLLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨970,by decide⟩,⟨974,by decide⟩,⟨975,by decide⟩] | 1 => ![⟨968,by decide⟩,⟨975,by decide⟩,⟨975,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨976,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨977,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨978,by decide⟩,⟨978,by decide⟩] | 5 => ![⟨979,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨980,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨981,by decide⟩]

def ntree11LRLLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨951,by decide⟩,⟨982,by decide⟩,⟨529,by decide⟩] | 1 => ![⟨983,by decide⟩,⟨983,by decide⟩,⟨54,by decide⟩] | 2 => ![⟨54,by decide⟩,⟨984,by decide⟩,⟨984,by decide⟩] | 3 => ![⟨985,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 4 => ![⟨985,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨543,by decide⟩,⟨986,by decide⟩,⟨986,by decide⟩] | 6 => ![⟨942,by decide⟩,⟨547,by decide⟩,⟨942,by decide⟩] | _ => ![⟨987,by decide⟩,⟨10,by decide⟩,⟨987,by decide⟩]

def ntree11LRLLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLLRRLRL i else ntree11LRLLRRLRR (i - 8)

def ntree11LRLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLRRLL i else ntree11LRLLRRLR (i - 15)

def ntree11LRLLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨988,by decide⟩,⟨989,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨988,by decide⟩,⟨988,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨988,by decide⟩,⟨990,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨66,by decide⟩,⟨991,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨992,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨992,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨993,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11LRLLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨947,by decide⟩,⟨994,by decide⟩,⟨529,by decide⟩] | 1 => ![⟨949,by decide⟩,⟨995,by decide⟩,⟨548,by decide⟩] | 2 => ![⟨951,by decide⟩,⟨996,by decide⟩,⟨549,by decide⟩] | 3 => ![⟨997,by decide⟩,⟨514,by decide⟩,⟨997,by decide⟩] | 4 => ![⟨998,by decide⟩,⟨10,by decide⟩,⟨998,by decide⟩] | 5 => ![⟨27,by decide⟩,⟨999,by decide⟩,⟨999,by decide⟩] | 6 => ![⟨947,by decide⟩,⟨947,by decide⟩,⟨10,by decide⟩] | _ => ![⟨949,by decide⟩,⟨949,by decide⟩,⟨8,by decide⟩]

def ntree11LRLLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLLRRRLL i else ntree11LRLLRRRLR (i - 7)

def ntree11LRLLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨25,by decide⟩,⟨1000,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1001,by decide⟩,⟨85,by decide⟩,⟨1001,by decide⟩] | 2 => ![⟨942,by decide⟩,⟨1002,by decide⟩,⟨1003,by decide⟩] | 3 => ![⟨1001,by decide⟩,⟨1004,by decide⟩,⟨1005,by decide⟩] | 4 => ![⟨1006,by decide⟩,⟨83,by decide⟩,⟨1006,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨1007,by decide⟩,⟨1007,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1008,by decide⟩,⟨1008,by decide⟩] | _ => ![⟨83,by decide⟩,⟨1009,by decide⟩,⟨1009,by decide⟩]

def ntree11LRLLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨1010,by decide⟩,⟨1010,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨11,by decide⟩,⟨1011,by decide⟩] | 2 => ![⟨587,by decide⟩,⟨9,by decide⟩,⟨1012,by decide⟩] | 3 => ![⟨1013,by decide⟩,⟨1013,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1014,by decide⟩,⟨1014,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1015,by decide⟩,⟨1015,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨1016,by decide⟩,⟨1016,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1014,by decide⟩,⟨1017,by decide⟩,⟨18,by decide⟩]

def ntree11LRLLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLLRRRRL i else ntree11LRLLRRRRR (i - 8)

def ntree11LRLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLLRRRL i else ntree11LRLLRRRR (i - 15)

def ntree11LRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRLLRRL i else ntree11LRLLRRR (i - 31)

def ntree11LRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LRLLRL i else ntree11LRLLRR (i - 62)

def ntree11LRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11LRLLL i else ntree11LRLLR (i - 123)

def ntree11LRLRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1002,by decide⟩,⟨1002,by decide⟩] | 1 => ![⟨1014,by decide⟩,⟨1018,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨85,by decide⟩,⟨1004,by decide⟩,⟨1004,by decide⟩] | 3 => ![⟨1016,by decide⟩,⟨1019,by decide⟩,⟨510,by decide⟩] | 4 => ![⟨1020,by decide⟩,⟨85,by decide⟩,⟨1020,by decide⟩] | 5 => ![⟨954,by decide⟩,⟨94,by decide⟩,⟨954,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1021,by decide⟩]

def ntree11LRLRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨598,by decide⟩,⟨18,by decide⟩,⟨1022,by decide⟩] | 1 => ![⟨25,by decide⟩,⟨25,by decide⟩,⟨1021,by decide⟩] | 2 => ![⟨942,by decide⟩,⟨94,by decide⟩,⟨942,by decide⟩] | 3 => ![⟨1001,by decide⟩,⟨103,by decide⟩,⟨1001,by decide⟩] | 4 => ![⟨945,by decide⟩,⟨104,by decide⟩,⟨945,by decide⟩] | 5 => ![⟨1023,by decide⟩,⟨43,by decide⟩,⟨1011,by decide⟩] | 6 => ![⟨1024,by decide⟩,⟨86,by decide⟩,⟨1025,by decide⟩] | _ => ![⟨1024,by decide⟩,⟨85,by decide⟩,⟨1024,by decide⟩]

def ntree11LRLRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRLLLLL i else ntree11LRLRLLLLR (i - 7)

def ntree11LRLRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1001,by decide⟩,⟨1026,by decide⟩,⟨1027,by decide⟩] | 1 => ![⟨1028,by decide⟩,⟨10,by decide⟩,⟨1028,by decide⟩] | 2 => ![⟨85,by decide⟩,⟨1026,by decide⟩,⟨1026,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1029,by decide⟩,⟨1029,by decide⟩] | 4 => ![⟨1030,by decide⟩,⟨969,by decide⟩,⟨1031,by decide⟩] | 5 => ![⟨1030,by decide⟩,⟨968,by decide⟩,⟨1030,by decide⟩] | 6 => ![⟨618,by decide⟩,⟨11,by decide⟩,⟨1032,by decide⟩] | _ => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨1033,by decide⟩]

def ntree11LRLRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1034,by decide⟩,⟨529,by decide⟩] | 1 => ![⟨1035,by decide⟩,⟨529,by decide⟩,⟨1036,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1021,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨1035,by decide⟩,⟨10,by decide⟩,⟨1035,by decide⟩] | 5 => ![⟨1037,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 6 => ![⟨1038,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | _ => ![⟨1039,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRLRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRLLLRL i else ntree11LRLRLLLRR (i - 8)

def ntree11LRLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRLLLL i else ntree11LRLRLLLR (i - 15)

def ntree11LRLRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨942,by decide⟩,⟨119,by decide⟩,⟨942,by decide⟩] | 1 => ![⟨1040,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨1041,by decide⟩,⟨66,by decide⟩,⟨581,by decide⟩] | 3 => ![⟨1042,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨635,by decide⟩,⟨529,by decide⟩,⟨1043,by decide⟩] | 5 => ![⟨83,by decide⟩,⟨1044,by decide⟩,⟨1044,by decide⟩] | _ => ![⟨85,by decide⟩,⟨1045,by decide⟩,⟨1045,by decide⟩]

def ntree11LRLRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1046,by decide⟩] | 1 => ![⟨1047,by decide⟩,⟨1014,by decide⟩,⟨963,by decide⟩] | 2 => ![⟨1048,by decide⟩,⟨1016,by decide⟩,⟨963,by decide⟩] | 3 => ![⟨1049,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1050,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1014,by decide⟩,⟨1051,by decide⟩,⟨529,by decide⟩] | 6 => ![⟨1052,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | _ => ![⟨1053,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRLRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRLLRLL i else ntree11LRLRLLRLR (i - 7)

def ntree11LRLRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1054,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1055,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1056,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨1057,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨1058,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨635,by decide⟩,⟨119,by decide⟩,⟨635,by decide⟩] | 6 => ![⟨1059,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1060,by decide⟩,⟨25,by decide⟩,⟨635,by decide⟩]

def ntree11LRLRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1061,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨1062,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1063,by decide⟩,⟨128,by decide⟩,⟨1001,by decide⟩] | 3 => ![⟨1064,by decide⟩,⟨129,by decide⟩,⟨942,by decide⟩] | 4 => ![⟨1065,by decide⟩,⟨130,by decide⟩,⟨1006,by decide⟩] | 5 => ![⟨1066,by decide⟩,⟨131,by decide⟩,⟨945,by decide⟩] | 6 => ![⟨1067,by decide⟩,⟨1067,by decide⟩,⟨1067,by decide⟩] | _ => ![⟨1068,by decide⟩,⟨1068,by decide⟩,⟨1069,by decide⟩]

def ntree11LRLRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRLLRRL i else ntree11LRLRLLRRR (i - 8)

def ntree11LRLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRLLRL i else ntree11LRLRLLRR (i - 15)

def ntree11LRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRLRLLL i else ntree11LRLRLLR (i - 31)

def ntree11LRLRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1070,by decide⟩,⟨1070,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1071,by decide⟩,⟨1071,by decide⟩,⟨1067,by decide⟩] | 2 => ![⟨1072,by decide⟩,⟨1072,by decide⟩,⟨514,by decide⟩] | 3 => ![⟨1070,by decide⟩,⟨1073,by decide⟩,⟨18,by decide⟩] | 4 => ![⟨1074,by decide⟩,⟨128,by decide⟩,⟨1020,by decide⟩] | 5 => ![⟨1075,by decide⟩,⟨129,by decide⟩,⟨954,by decide⟩] | _ => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨1076,by decide⟩]

def ntree11LRLRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1067,by decide⟩,⟨1077,by decide⟩,⟨1077,by decide⟩] | 1 => ![⟨1069,by decide⟩,⟨1078,by decide⟩,⟨1078,by decide⟩] | 2 => ![⟨1079,by decide⟩,⟨1067,by decide⟩,⟨1079,by decide⟩] | 3 => ![⟨1080,by decide⟩,⟨1069,by decide⟩,⟨1080,by decide⟩] | 4 => ![⟨1069,by decide⟩,⟨1069,by decide⟩,⟨1069,by decide⟩] | 5 => ![⟨655,by decide⟩,⟨959,by decide⟩,⟨1081,by decide⟩] | 6 => ![⟨1082,by decide⟩,⟨85,by decide⟩,⟨1001,by decide⟩] | _ => ![⟨1083,by decide⟩,⟨10,by decide⟩,⟨942,by decide⟩]

def ntree11LRLRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRLRLLL i else ntree11LRLRLRLLR (i - 7)

def ntree11LRLRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1084,by decide⟩,⟨14,by decide⟩,⟨1028,by decide⟩] | 1 => ![⟨658,by decide⟩,⟨11,by decide⟩,⟨1011,by decide⟩] | 2 => ![⟨659,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 3 => ![⟨660,by decide⟩,⟨15,by decide⟩,⟨1032,by decide⟩] | 4 => ![⟨642,by decide⟩,⟨14,by decide⟩,⟨1033,by decide⟩] | 5 => ![⟨644,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1085,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | _ => ![⟨659,by decide⟩,⟨10,by decide⟩,⟨1021,by decide⟩]

def ntree11LRLRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨1086,by decide⟩] | 1 => ![⟨1087,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨1088,by decide⟩,⟨83,by decide⟩,⟨83,by decide⟩] | 3 => ![⟨675,by decide⟩,⟨10,by decide⟩,⟨1021,by decide⟩] | 4 => ![⟨677,by decide⟩,⟨8,by decide⟩,⟨1046,by decide⟩] | 5 => ![⟨1089,by decide⟩,⟨1069,by decide⟩,⟨1089,by decide⟩] | 6 => ![⟨635,by decide⟩,⟨10,by decide⟩,⟨1090,by decide⟩] | _ => ![⟨1091,by decide⟩,⟨1091,by decide⟩,⟨10,by decide⟩]

def ntree11LRLRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRLRLRL i else ntree11LRLRLRLRR (i - 8)

def ntree11LRLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRLRLL i else ntree11LRLRLRLR (i - 15)

def ntree11LRLRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1092,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1093,by decide⟩,⟨153,by decide⟩,⟨691,by decide⟩] | 2 => ![⟨1094,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨1093,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1095,by decide⟩,⟨1095,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨1096,by decide⟩,⟨1091,by decide⟩,⟨942,by decide⟩] | _ => ![⟨942,by decide⟩,⟨10,by decide⟩,⟨1097,by decide⟩]

def ntree11LRLRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1091,by decide⟩,⟨1098,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1099,by decide⟩] | 2 => ![⟨1093,by decide⟩,⟨166,by decide⟩,⟨166,by decide⟩] | 3 => ![⟨1100,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1101,by decide⟩,⟨1101,by decide⟩,⟨514,by decide⟩] | 5 => ![⟨1102,by decide⟩,⟨163,by decide⟩,⟨954,by decide⟩] | 6 => ![⟨163,by decide⟩,⟨1103,by decide⟩,⟨10,by decide⟩] | _ => ![⟨698,by decide⟩,⟨178,by decide⟩,⟨1104,by decide⟩]

def ntree11LRLRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRLRRLL i else ntree11LRLRLRRLR (i - 7)

def ntree11LRLRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1105,by decide⟩,⟨27,by decide⟩,⟨27,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1106,by decide⟩] | 2 => ![⟨1107,by decide⟩,⟨1107,by decide⟩,⟨514,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨691,by decide⟩] | 4 => ![⟨1108,by decide⟩,⟨1108,by decide⟩,⟨521,by decide⟩] | 5 => ![⟨1109,by decide⟩,⟨1110,by decide⟩,⟨1111,by decide⟩] | 6 => ![⟨1112,by decide⟩,⟨1107,by decide⟩,⟨961,by decide⟩] | _ => ![⟨1109,by decide⟩,⟨179,by decide⟩,⟨942,by decide⟩]

def ntree11LRLRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1113,by decide⟩,⟨182,by decide⟩,⟨945,by decide⟩] | 1 => ![⟨1109,by decide⟩,⟨187,by decide⟩,⟨1097,by decide⟩] | 2 => ![⟨182,by decide⟩,⟨1114,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨1107,by decide⟩,⟨1115,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨963,by decide⟩,⟨153,by decide⟩,⟨963,by decide⟩] | 5 => ![⟨1116,by decide⟩,⟨1117,by decide⟩,⟨706,by decide⟩] | 6 => ![⟨1118,by decide⟩,⟨1116,by decide⟩,⟨963,by decide⟩] | _ => ![⟨1116,by decide⟩,⟨1116,by decide⟩,⟨10,by decide⟩]

def ntree11LRLRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRLRRRL i else ntree11LRLRLRRRR (i - 8)

def ntree11LRLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRLRRL i else ntree11LRLRLRRR (i - 15)

def ntree11LRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRLRLRL i else ntree11LRLRLRR (i - 31)

def ntree11LRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LRLRLL i else ntree11LRLRLR (i - 62)

def ntree11LRLRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1119,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1120,by decide⟩,⟨1120,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1121,by decide⟩,⟨1116,by decide⟩,⟨942,by decide⟩] | 3 => ![⟨942,by decide⟩,⟨191,by decide⟩,⟨1122,by decide⟩] | 4 => ![⟨1116,by decide⟩,⟨1123,by decide⟩,⟨191,by decide⟩] | 5 => ![⟨968,by decide⟩,⟨1124,by decide⟩,⟨968,by decide⟩] | _ => ![⟨1125,by decide⟩,⟨968,by decide⟩,⟨968,by decide⟩]

def ntree11LRLRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨968,by decide⟩,⟨1126,by decide⟩,⟨968,by decide⟩] | 1 => ![⟨963,by decide⟩,⟨166,by decide⟩,⟨1127,by decide⟩] | 2 => ![⟨201,by decide⟩,⟨200,by decide⟩,⟨166,by decide⟩] | 3 => ![⟨1128,by decide⟩,⟨54,by decide⟩,⟨54,by decide⟩] | 4 => ![⟨1129,by decide⟩,⟨1129,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1130,by decide⟩,⟨1130,by decide⟩,⟨543,by decide⟩] | 6 => ![⟨1131,by decide⟩,⟨1131,by decide⟩,⟨543,by decide⟩] | _ => ![⟨1109,by decide⟩,⟨1132,by decide⟩,⟨1133,by decide⟩]

def ntree11LRLRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRRLLLL i else ntree11LRLRRLLLR (i - 7)

def ntree11LRLRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1134,by decide⟩,⟨1129,by decide⟩,⟨987,by decide⟩] | 1 => ![⟨942,by decide⟩,⟨1135,by decide⟩,⟨1136,by decide⟩] | 2 => ![⟨1137,by decide⟩,⟨201,by decide⟩,⟨942,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨1138,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨179,by decide⟩,⟨1132,by decide⟩,⟨1139,by decide⟩] | 5 => ![⟨201,by decide⟩,⟨1140,by decide⟩,⟨1141,by decide⟩] | 6 => ![⟨1091,by decide⟩,⟨1142,by decide⟩,⟨706,by decide⟩] | _ => ![⟨1143,by decide⟩,⟨1091,by decide⟩,⟨963,by decide⟩]

def ntree11LRLRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1119,by decide⟩,⟨10,by decide⟩,⟨691,by decide⟩] | 1 => ![⟨1144,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨1145,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨963,by decide⟩,⟨227,by decide⟩,⟨1146,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨224,by decide⟩,⟨227,by decide⟩] | 5 => ![⟨1119,by decide⟩,⟨227,by decide⟩,⟨227,by decide⟩] | 6 => ![⟨1147,by decide⟩,⟨163,by decide⟩,⟨998,by decide⟩] | _ => ![⟨163,by decide⟩,⟨1148,by decide⟩,⟨1149,by decide⟩]

def ntree11LRLRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRRLLRL i else ntree11LRLRRLLRR (i - 8)

def ntree11LRLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRRLLL i else ntree11LRLRRLLR (i - 15)

def ntree11LRLRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1150,by decide⟩,⟨1150,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1151,by decide⟩,⟨1151,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨1152,by decide⟩,⟨1152,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1153,by decide⟩] | 4 => ![⟨179,by decide⟩,⟨1154,by decide⟩,⟨1155,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1156,by decide⟩,⟨1156,by decide⟩] | _ => ![⟨182,by decide⟩,⟨1157,by decide⟩,⟨1158,by decide⟩]

def ntree11LRLRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨179,by decide⟩,⟨1159,by decide⟩,⟨1150,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨1160,by decide⟩,⟨1160,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1161,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1162,by decide⟩,⟨1162,by decide⟩] | 4 => ![⟨85,by decide⟩,⟨1163,by decide⟩,⟨1163,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨1164,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1165,by decide⟩] | _ => ![⟨8,by decide⟩,⟨1166,by decide⟩,⟨1166,by decide⟩]

def ntree11LRLRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRRLRLL i else ntree11LRLRRLRLR (i - 7)

def ntree11LRLRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨942,by decide⟩,⟨10,by decide⟩,⟨1167,by decide⟩] | 1 => ![⟨1001,by decide⟩,⟨85,by decide⟩,⟨1168,by decide⟩] | 2 => ![⟨945,by decide⟩,⟨8,by decide⟩,⟨1169,by decide⟩] | 3 => ![⟨581,by decide⟩,⟨1162,by decide⟩,⟨1170,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨1161,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨1171,by decide⟩,⟨1162,by decide⟩] | 6 => ![⟨1172,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | _ => ![⟨698,by decide⟩,⟨94,by decide⟩,⟨1161,by decide⟩]

def ntree11LRLRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1173,by decide⟩,⟨243,by decide⟩,⟨1020,by decide⟩] | 1 => ![⟨1102,by decide⟩,⟨248,by decide⟩,⟨1174,by decide⟩] | 2 => ![⟨698,by decide⟩,⟨1162,by decide⟩,⟨1162,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1161,by decide⟩] | 4 => ![⟨253,by decide⟩,⟨253,by decide⟩,⟨1164,by decide⟩] | 5 => ![⟨182,by decide⟩,⟨182,by decide⟩,⟨1165,by decide⟩] | 6 => ![⟨1175,by decide⟩,⟨253,by decide⟩,⟨1001,by decide⟩] | _ => ![⟨1109,by decide⟩,⟨260,by decide⟩,⟨1167,by decide⟩]

def ntree11LRLRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRRLRRL i else ntree11LRLRRLRRR (i - 8)

def ntree11LRLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRRLRL i else ntree11LRLRRLRR (i - 15)

def ntree11LRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRLRRLL i else ntree11LRLRRLR (i - 31)

def ntree11LRLRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1176,by decide⟩,⟨256,by decide⟩,⟨1006,by decide⟩] | 1 => ![⟨1175,by decide⟩,⟨261,by decide⟩,⟨1168,by decide⟩] | 2 => ![⟨1113,by decide⟩,⟨262,by decide⟩,⟨1169,by decide⟩] | 3 => ![⟨85,by decide⟩,⟨1177,by decide⟩,⟨1177,by decide⟩] | 4 => ![⟨963,by decide⟩,⟨1178,by decide⟩,⟨1179,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1180,by decide⟩] | _ => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨1181,by decide⟩]

def ntree11LRLRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1178,by decide⟩,⟨1178,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1182,by decide⟩,⟨1182,by decide⟩] | 2 => ![⟨942,by decide⟩,⟨270,by decide⟩,⟨1183,by decide⟩] | 3 => ![⟨1001,by decide⟩,⟨271,by decide⟩,⟨1184,by decide⟩] | 4 => ![⟨581,by decide⟩,⟨1178,by decide⟩,⟨1185,by decide⟩] | 5 => ![⟨968,by decide⟩,⟨1186,by decide⟩,⟨1186,by decide⟩] | 6 => ![⟨968,by decide⟩,⟨1187,by decide⟩,⟨1187,by decide⟩] | _ => ![⟨10,by decide⟩,⟨751,by decide⟩,⟨10,by decide⟩]

def ntree11LRLRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRRRLLL i else ntree11LRLRRRLLR (i - 7)

def ntree11LRLRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1188,by decide⟩,⟨1189,by decide⟩,⟨1035,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨1178,by decide⟩,⟨1178,by decide⟩] | 2 => ![⟨1189,by decide⟩,⟨1189,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1180,by decide⟩] | 4 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨1180,by decide⟩] | 5 => ![⟨1190,by decide⟩,⟨285,by decide⟩,⟨1028,by decide⟩] | 6 => ![⟨1109,by decide⟩,⟨287,by decide⟩,⟨1183,by decide⟩] | _ => ![⟨1191,by decide⟩,⟨279,by decide⟩,⟨1001,by decide⟩]

def ntree11LRLRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1137,by decide⟩,⟨281,by decide⟩,⟨1183,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨1192,by decide⟩,⟨1192,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1193,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨1194,by decide⟩,⟨1178,by decide⟩] | 4 => ![⟨1195,by decide⟩,⟨163,by decide⟩,⟨618,by decide⟩] | 5 => ![⟨1196,by decide⟩,⟨179,by decide⟩,⟨635,by decide⟩] | 6 => ![⟨1197,by decide⟩,⟨182,by decide⟩,⟨637,by decide⟩] | _ => ![⟨1196,by decide⟩,⟨287,by decide⟩,⟨762,by decide⟩]

def ntree11LRLRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRRRLRL i else ntree11LRLRRRLRR (i - 8)

def ntree11LRLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRRRLL i else ntree11LRLRRRLR (i - 15)

def ntree11LRLRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1198,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 1 => ![⟨1199,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨1200,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1201,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨954,by decide⟩,⟨10,by decide⟩,⟨1174,by decide⟩] | 5 => ![⟨1001,by decide⟩,⟨85,by decide⟩,⟨1202,by decide⟩] | _ => ![⟨961,by decide⟩,⟨514,by decide⟩,⟨1203,by decide⟩]

def ntree11LRLRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨942,by decide⟩,⟨10,by decide⟩,⟨1204,by decide⟩] | 1 => ![⟨1205,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨1119,by decide⟩,⟨10,by decide⟩,⟨1161,by decide⟩] | 3 => ![⟨790,by decide⟩,⟨153,by decide⟩,⟨1180,by decide⟩] | 4 => ![⟨1092,by decide⟩,⟨10,by decide⟩,⟨1180,by decide⟩] | 5 => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 6 => ![⟨1206,by decide⟩,⟨332,by decide⟩,⟨581,by decide⟩] | _ => ![⟨1119,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRLRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRLRRRRLL i else ntree11LRLRRRRLR (i - 7)

def ntree11LRLRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨618,by decide⟩,⟨153,by decide⟩,⟨618,by decide⟩] | 1 => ![⟨1092,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨1207,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨942,by decide⟩,⟨1139,by decide⟩,⟨1133,by decide⟩] | 4 => ![⟨1001,by decide⟩,⟨1208,by decide⟩,⟨1209,by decide⟩] | 5 => ![⟨942,by decide⟩,⟨798,by decide⟩,⟨1210,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1211,by decide⟩,⟨1211,by decide⟩] | _ => ![⟨85,by decide⟩,⟨1212,by decide⟩,⟨1212,by decide⟩]

def ntree11LRLRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1145,by decide⟩,⟨10,by decide⟩,⟨1161,by decide⟩] | 1 => ![⟨1205,by decide⟩,⟨85,by decide⟩,⟨1164,by decide⟩] | 2 => ![⟨1144,by decide⟩,⟨8,by decide⟩,⟨1165,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1213,by decide⟩,⟨1213,by decide⟩] | 4 => ![⟨1069,by decide⟩,⟨1214,by decide⟩,⟨1214,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨1215,by decide⟩,⟨1215,by decide⟩] | 6 => ![⟨1067,by decide⟩,⟨1216,by decide⟩,⟨1216,by decide⟩] | _ => ![⟨635,by decide⟩,⟨1217,by decide⟩,⟨1218,by decide⟩]

def ntree11LRLRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRLRRRRRL i else ntree11LRLRRRRRR (i - 8)

def ntree11LRLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRLRRRRL i else ntree11LRLRRRRR (i - 15)

def ntree11LRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRLRRRL i else ntree11LRLRRRR (i - 31)

def ntree11LRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LRLRRL i else ntree11LRLRRR (i - 62)

def ntree11LRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 124 then ntree11LRLRL i else ntree11LRLRR (i - 124)

def ntree11LRL (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11LRLL i else ntree11LRLR (i - 247)

def ntree11LRRLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨1219,by decide⟩,⟨1219,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨1220,by decide⟩,⟨1220,by decide⟩] | 2 => ![⟨83,by decide⟩,⟨1221,by decide⟩,⟨1221,by decide⟩] | 3 => ![⟨1092,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 4 => ![⟨1120,by decide⟩,⟨1222,by decide⟩,⟨11,by decide⟩] | 5 => ![⟨954,by decide⟩,⟨10,by decide⟩,⟨954,by decide⟩] | _ => ![⟨689,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩]

def ntree11LRRLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1223,by decide⟩] | 1 => ![⟨1092,by decide⟩,⟨510,by decide⟩,⟨510,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1224,by decide⟩,⟨365,by decide⟩,⟨1225,by decide⟩] | 4 => ![⟨1102,by decide⟩,⟨372,by decide⟩,⟨956,by decide⟩] | 5 => ![⟨374,by decide⟩,⟨10,by decide⟩,⟨374,by decide⟩] | 6 => ![⟨1101,by decide⟩,⟨1226,by decide⟩,⟨959,by decide⟩] | _ => ![⟨1227,by decide⟩,⟨948,by decide⟩,⟨375,by decide⟩]

def ntree11LRRLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLLLLLL i else ntree11LRRLLLLLR (i - 7)

def ntree11LRRLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨699,by decide⟩,⟨959,by decide⟩,⟨959,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨374,by decide⟩,⟨507,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨388,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1120,by decide⟩,⟨1228,by decide⟩,⟨529,by decide⟩]

def ntree11LRRLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1125,by decide⟩,⟨969,by decide⟩,⟨969,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1229,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1230,by decide⟩] | 3 => ![⟨1231,by decide⟩,⟨391,by decide⟩,⟨391,by decide⟩] | 4 => ![⟨698,by decide⟩,⟨387,by decide⟩,⟨1232,by decide⟩] | 5 => ![⟨698,by decide⟩,⟨399,by decide⟩,⟨981,by decide⟩] | 6 => ![⟨391,by decide⟩,⟨1233,by decide⟩,⟨1233,by decide⟩] | _ => ![⟨1120,by decide⟩,⟨1234,by decide⟩,⟨529,by decide⟩]

def ntree11LRRLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLLLLRL i else ntree11LRRLLLLRR (i - 7)

def ntree11LRRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLLLLL i else ntree11LRRLLLLR (i - 15)

def ntree11LRRLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1235,by decide⟩,⟨11,by decide⟩,⟨1236,by decide⟩] | 1 => ![⟨1237,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨201,by decide⟩,⟨1238,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1239,by decide⟩,⟨989,by decide⟩,⟨1236,by decide⟩] | 4 => ![⟨988,by decide⟩,⟨988,by decide⟩,⟨214,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨870,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRRLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1145,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1240,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨415,by decide⟩,⟨72,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨1241,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨514,by decide⟩,⟨1242,by decide⟩,⟨514,by decide⟩] | 6 => ![⟨1101,by decide⟩,⟨1243,by decide⟩,⟨558,by decide⟩] | _ => ![⟨365,by decide⟩,⟨1244,by decide⟩,⟨1245,by decide⟩]

def ntree11LRRLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLLLRLL i else ntree11LRRLLLRLR (i - 7)

def ntree11LRRLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨1246,by decide⟩,⟨1150,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨1247,by decide⟩,⟨529,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨1248,by decide⟩,⟨1151,by decide⟩] | 3 => ![⟨515,by decide⟩,⟨1249,by decide⟩,⟨1152,by decide⟩] | 4 => ![⟨514,by decide⟩,⟨1250,by decide⟩,⟨514,by decide⟩] | 5 => ![⟨1235,by decide⟩,⟨10,by decide⟩,⟨1235,by decide⟩] | 6 => ![⟨163,by decide⟩,⟨1251,by decide⟩,⟨10,by decide⟩] | _ => ![⟨947,by decide⟩,⟨947,by decide⟩,⟨171,by decide⟩]

def ntree11LRRLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 1 => ![⟨1235,by decide⟩,⟨547,by decide⟩,⟨1235,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨877,by decide⟩,⟨11,by decide⟩,⟨1252,by decide⟩] | 5 => ![⟨883,by decide⟩,⟨1253,by decide⟩,⟨1253,by decide⟩] | 6 => ![⟨1254,by decide⟩,⟨10,by decide⟩,⟨1254,by decide⟩] | _ => ![⟨1255,by decide⟩,⟨10,by decide⟩,⟨1256,by decide⟩]

def ntree11LRRLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRLLLRRL i else ntree11LRRLLLRRR (i - 8)

def ntree11LRRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLLLRL i else ntree11LRRLLLRR (i - 15)

def ntree11LRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11LRRLLLL i else ntree11LRRLLLR (i - 30)

def ntree11LRRLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1223,by decide⟩] | 1 => ![⟨598,by decide⟩,⟨11,by decide⟩,⟨1257,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1258,by decide⟩,⟨1258,by decide⟩] | 3 => ![⟨1014,by decide⟩,⟨1014,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1259,by decide⟩,⟨1259,by decide⟩,⟨883,by decide⟩] | 5 => ![⟨698,by decide⟩,⟨1002,by decide⟩,⟨1002,by decide⟩] | _ => ![⟨1260,by decide⟩,⟨1013,by decide⟩,⟨1254,by decide⟩]

def ntree11LRRLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1261,by decide⟩,⟨1018,by decide⟩,⟨1256,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨1262,by decide⟩,⟨1002,by decide⟩] | 2 => ![⟨1259,by decide⟩,⟨1263,by decide⟩,⟨883,by decide⟩] | 3 => ![⟨1264,by decide⟩,⟨379,by decide⟩,⟨1252,by decide⟩] | 4 => ![⟨739,by decide⟩,⟨443,by decide⟩,⟨1257,by decide⟩] | 5 => ![⟨598,by decide⟩,⟨444,by decide⟩,⟨598,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨1265,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1266,by decide⟩]

def ntree11LRRLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLLRLLL i else ntree11LRRLLRLLR (i - 7)

def ntree11LRRLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1267,by decide⟩,⟨1268,by decide⟩,⟨1268,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1161,by decide⟩] | 2 => ![⟨1172,by decide⟩,⟨1026,by decide⟩,⟨1026,by decide⟩] | 3 => ![⟨698,by decide⟩,⟨1034,by decide⟩,⟨1265,by decide⟩] | 4 => ![⟨1269,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 5 => ![⟨1270,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨1271,by decide⟩,⟨201,by decide⟩,⟨877,by decide⟩] | _ => ![⟨754,by decide⟩,⟨455,by decide⟩,⟨1032,by decide⟩]

def ntree11LRRLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1272,by decide⟩,⟨449,by decide⟩,⟨449,by decide⟩] | 1 => ![⟨277,by decide⟩,⟨277,by decide⟩,⟨1266,by decide⟩] | 2 => ![⟨1273,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1274,by decide⟩,⟨1274,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1275,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1276,by decide⟩,⟨1276,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | _ => ![⟨1014,by decide⟩,⟨1051,by decide⟩,⟨529,by decide⟩]

def ntree11LRRLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRLLRLRL i else ntree11LRRLLRLRR (i - 8)

def ntree11LRRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLLRLL i else ntree11LRRLLRLR (i - 15)

def ntree11LRRLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨243,by decide⟩,⟨1277,by decide⟩,⟨1026,by decide⟩] | 1 => ![⟨85,by decide⟩,⟨1278,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨1279,by decide⟩,⟨529,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨1280,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨1013,by decide⟩,⟨1281,by decide⟩,⟨270,by decide⟩] | 5 => ![⟨1259,by decide⟩,⟨1282,by decide⟩,⟨902,by decide⟩] | _ => ![⟨85,by decide⟩,⟨1283,by decide⟩,⟨85,by decide⟩]

def ntree11LRRLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1015,by decide⟩,⟨1284,by decide⟩,⟨271,by decide⟩] | 1 => ![⟨1016,by decide⟩,⟨1285,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨1286,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1287,by decide⟩,⟨163,by decide⟩,⟨924,by decide⟩] | 4 => ![⟨1288,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨251,by decide⟩,⟨251,by decide⟩,⟨1275,by decide⟩] | 6 => ![⟨618,by decide⟩,⟨463,by decide⟩,⟨618,by decide⟩] | _ => ![⟨1289,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩]

def ntree11LRRLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLLRRLL i else ntree11LRRLLRRLR (i - 7)

def ntree11LRRLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1290,by decide⟩,⟨129,by decide⟩,⟨877,by decide⟩] | 2 => ![⟨1291,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1070,by decide⟩,⟨1070,by decide⟩,⟨315,by decide⟩] | 4 => ![⟨929,by decide⟩,⟨959,by decide⟩,⟨1292,by decide⟩] | 5 => ![⟨467,by decide⟩,⟨85,by decide⟩,⟨467,by decide⟩] | 6 => ![⟨659,by decide⟩,⟨478,by decide⟩,⟨1161,by decide⟩] | _ => ![⟨1293,by decide⟩,⟨449,by decide⟩,⟨449,by decide⟩]

def ntree11LRRLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1266,by decide⟩] | 1 => ![⟨877,by decide⟩,⟨10,by decide⟩,⟨1294,by decide⟩] | 2 => ![⟨659,by decide⟩,⟨10,by decide⟩,⟨1275,by decide⟩] | 3 => ![⟨1295,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨85,by decide⟩,⟨1296,by decide⟩,⟨85,by decide⟩] | 5 => ![⟨1067,by decide⟩,⟨1297,by decide⟩,⟨1067,by decide⟩] | 6 => ![⟨514,by decide⟩,⟨1298,by decide⟩,⟨514,by decide⟩] | _ => ![⟨14,by decide⟩,⟨1299,by decide⟩,⟨1213,by decide⟩]

def ntree11LRRLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRLLRRRL i else ntree11LRRLLRRRR (i - 8)

def ntree11LRRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLLRRL i else ntree11LRRLLRRR (i - 15)

def ntree11LRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRRLLRL i else ntree11LRRLLRR (i - 31)

def ntree11LRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11LRRLLL i else ntree11LRRLLR (i - 61)

def ntree11LRRLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1068,by decide⟩,⟨1300,by decide⟩,⟨1214,by decide⟩] | 1 => ![⟨1070,by decide⟩,⟨1301,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨128,by decide⟩,⟨1302,by decide⟩,⟨1215,by decide⟩] | 3 => ![⟨1071,by decide⟩,⟨1303,by decide⟩,⟨1216,by decide⟩] | 4 => ![⟨1072,by decide⟩,⟨1304,by decide⟩,⟨817,by decide⟩] | 5 => ![⟨1235,by decide⟩,⟨10,by decide⟩,⟨1305,by decide⟩] | _ => ![⟨924,by decide⟩,⟨10,by decide⟩,⟨1306,by decide⟩]

def ntree11LRRLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1307,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨1308,by decide⟩,⟨3,by decide⟩,⟨1309,by decide⟩] | 2 => ![⟨1310,by decide⟩,⟨1,by decide⟩,⟨1309,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1311,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1311,by decide⟩] | 5 => ![⟨1312,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 6 => ![⟨1313,by decide⟩,⟨1314,by decide⟩,⟨1314,by decide⟩] | _ => ![⟨1315,by decide⟩,⟨15,by decide⟩,⟨1316,by decide⟩]

def ntree11LRRLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLRLLLL i else ntree11LRRLRLLLR (i - 7)

def ntree11LRRLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1317,by decide⟩,⟨11,by decide⟩,⟨1316,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1318,by decide⟩] | 2 => ![⟨1313,by decide⟩,⟨1313,by decide⟩,⟨1319,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1313,by decide⟩,⟨1313,by decide⟩,⟨1313,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1318,by decide⟩] | _ => ![⟨1307,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree11LRRLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1308,by decide⟩,⟨2,by decide⟩,⟨1310,by decide⟩] | 1 => ![⟨1310,by decide⟩,⟨0,by decide⟩,⟨1310,by decide⟩] | 2 => ![⟨1312,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1315,by decide⟩,⟨14,by decide⟩,⟨1317,by decide⟩] | 4 => ![⟨1317,by decide⟩,⟨10,by decide⟩,⟨1317,by decide⟩] | 5 => ![⟨1320,by decide⟩,⟨0,by decide⟩,⟨1320,by decide⟩] | 6 => ![⟨1321,by decide⟩,⟨2,by decide⟩,⟨1320,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨10,by decide⟩,⟨1322,by decide⟩]

def ntree11LRRLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRLRLLRL i else ntree11LRRLRLLRR (i - 8)

def ntree11LRRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLRLLL i else ntree11LRRLRLLR (i - 15)

def ntree11LRRLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1323,by decide⟩,⟨1313,by decide⟩,⟨1323,by decide⟩] | 1 => ![⟨1324,by decide⟩,⟨14,by decide⟩,⟨1322,by decide⟩] | 2 => ![⟨1325,by decide⟩,⟨25,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨1326,by decide⟩,⟨26,by decide⟩,⟨1327,by decide⟩] | 4 => ![⟨1327,by decide⟩,⟨27,by decide⟩,⟨1327,by decide⟩] | 5 => ![⟨1328,by decide⟩,⟨31,by decide⟩,⟨1329,by decide⟩] | _ => ![⟨1330,by decide⟩,⟨11,by decide⟩,⟨1329,by decide⟩]

def ntree11LRRLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨1331,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1331,by decide⟩] | 2 => ![⟨1332,by decide⟩,⟨30,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨38,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1332,by decide⟩,⟨39,by decide⟩,⟨1333,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨40,by decide⟩,⟨1333,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨11,by decide⟩,⟨1334,by decide⟩] | _ => ![⟨1325,by decide⟩,⟨43,by decide⟩,⟨1334,by decide⟩]

def ntree11LRRLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLRLRLL i else ntree11LRRLRLRLR (i - 7)

def ntree11LRRLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1335,by decide⟩,⟨1,by decide⟩,⟨1336,by decide⟩] | 1 => ![⟨1337,by decide⟩,⟨2,by decide⟩,⟨1335,by decide⟩] | 2 => ![⟨1335,by decide⟩,⟨0,by decide⟩,⟨1335,by decide⟩] | 3 => ![⟨1338,by decide⟩,⟨11,by decide⟩,⟨1339,by decide⟩] | 4 => ![⟨1340,by decide⟩,⟨1314,by decide⟩,⟨1341,by decide⟩] | 5 => ![⟨1342,by decide⟩,⟨14,by decide⟩,⟨1338,by decide⟩] | 6 => ![⟨1340,by decide⟩,⟨1313,by decide⟩,⟨1340,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1343,by decide⟩]

def ntree11LRRLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1344,by decide⟩] | 1 => ![⟨1313,by decide⟩,⟨1313,by decide⟩,⟨1345,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 3 => ![⟨1346,by decide⟩,⟨1347,by decide⟩,⟨1346,by decide⟩] | 4 => ![⟨1348,by decide⟩,⟨1349,by decide⟩,⟨1346,by decide⟩] | 5 => ![⟨1350,by decide⟩,⟨54,by decide⟩,⟨1350,by decide⟩] | 6 => ![⟨1351,by decide⟩,⟨55,by decide⟩,⟨1350,by decide⟩] | _ => ![⟨1352,by decide⟩,⟨1353,by decide⟩,⟨1352,by decide⟩]

def ntree11LRRLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRLRLRRL i else ntree11LRRLRLRRR (i - 8)

def ntree11LRRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLRLRL i else ntree11LRRLRLRR (i - 15)

def ntree11LRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRRLRLL i else ntree11LRRLRLR (i - 31)

def ntree11LRRLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1354,by decide⟩,⟨11,by decide⟩,⟨1355,by decide⟩] | 1 => ![⟨1356,by decide⟩,⟨30,by decide⟩,⟨1354,by decide⟩] | 2 => ![⟨1354,by decide⟩,⟨10,by decide⟩,⟨1354,by decide⟩] | 3 => ![⟨1357,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨1358,by decide⟩,⟨1359,by decide⟩] | 5 => ![⟨1332,by decide⟩,⟨1360,by decide⟩,⟨1359,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨65,by decide⟩,⟨1361,by decide⟩]

def ntree11LRRLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1346,by decide⟩,⟨1362,by decide⟩,⟨1363,by decide⟩] | 1 => ![⟨1364,by decide⟩,⟨66,by decide⟩,⟨1322,by decide⟩] | 2 => ![⟨1335,by decide⟩,⟨0,by decide⟩,⟨1335,by decide⟩] | 3 => ![⟨1337,by decide⟩,⟨2,by decide⟩,⟨1365,by decide⟩] | 4 => ![⟨1335,by decide⟩,⟨0,by decide⟩,⟨1365,by decide⟩] | 5 => ![⟨1338,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 6 => ![⟨47,by decide⟩,⟨1366,by decide⟩,⟨1367,by decide⟩] | _ => ![⟨1342,by decide⟩,⟨14,by decide⟩,⟨1368,by decide⟩]

def ntree11LRRLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLRRLLL i else ntree11LRRLRRLLR (i - 7)

def ntree11LRRLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1340,by decide⟩,⟨1369,by decide⟩,⟨1370,by decide⟩] | 1 => ![⟨1338,by decide⟩,⟨10,by decide⟩,⟨1368,by decide⟩] | 2 => ![⟨1371,by decide⟩,⟨25,by decide⟩,⟨1338,by decide⟩] | 3 => ![⟨1354,by decide⟩,⟨10,by decide⟩,⟨1354,by decide⟩] | 4 => ![⟨1356,by decide⟩,⟨30,by decide⟩,⟨1372,by decide⟩] | 5 => ![⟨1354,by decide⟩,⟨10,by decide⟩,⟨1372,by decide⟩] | 6 => ![⟨1357,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1373,by decide⟩,⟨1374,by decide⟩]

def ntree11LRRLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨30,by decide⟩,⟨1375,by decide⟩,⟨1374,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨65,by decide⟩,⟨65,by decide⟩] | 2 => ![⟨47,by decide⟩,⟨1376,by decide⟩,⟨1377,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1378,by decide⟩] | 4 => ![⟨25,by decide⟩,⟨25,by decide⟩,⟨1378,by decide⟩] | 5 => ![⟨1379,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨1380,by decide⟩,⟨1381,by decide⟩,⟨1,by decide⟩] | _ => ![⟨1380,by decide⟩,⟨1380,by decide⟩,⟨0,by decide⟩]

def ntree11LRRLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRLRRLRL i else ntree11LRRLRRLRR (i - 8)

def ntree11LRRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLRRLL i else ntree11LRRLRRLR (i - 15)

def ntree11LRRLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1380,by decide⟩,⟨1380,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1382,by decide⟩,⟨1383,by decide⟩,⟨1383,by decide⟩] | 2 => ![⟨1382,by decide⟩,⟨1382,by decide⟩,⟨1382,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1384,by decide⟩,⟨1385,by decide⟩,⟨1385,by decide⟩] | 5 => ![⟨1386,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | _ => ![⟨1387,by decide⟩,⟨1388,by decide⟩,⟨11,by decide⟩]

def ntree11LRRLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1389,by decide⟩,⟨1388,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨1384,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1390,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | _ => ![⟨1391,by decide⟩,⟨1392,by decide⟩,⟨11,by decide⟩]

def ntree11LRRLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRLRRRLL i else ntree11LRRLRRRLR (i - 7)

def ntree11LRRLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1391,by decide⟩,⟨1391,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1391,by decide⟩,⟨1391,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1393,by decide⟩,⟨1394,by decide⟩,⟨1394,by decide⟩] | 3 => ![⟨1393,by decide⟩,⟨1393,by decide⟩,⟨1393,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1395,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1396,by decide⟩,⟨1396,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1397,by decide⟩,⟨1397,by decide⟩]

def ntree11LRRLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1312,by decide⟩,⟨1398,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1398,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1320,by decide⟩,⟨93,by decide⟩,⟨1320,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨94,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨96,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨1399,by decide⟩,⟨1322,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1400,by decide⟩,⟨1401,by decide⟩] | _ => ![⟨1402,by decide⟩,⟨1389,by decide⟩,⟨1322,by decide⟩]

def ntree11LRRLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRLRRRRL i else ntree11LRRLRRRRR (i - 8)

def ntree11LRRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRLRRRL i else ntree11LRRLRRRR (i - 15)

def ntree11LRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRRLRRL i else ntree11LRRLRRR (i - 31)

def ntree11LRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LRRLRL i else ntree11LRRLRR (i - 62)

def ntree11LRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11LRRLL i else ntree11LRRLR (i - 123)

def ntree11LRRRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1402,by decide⟩,⟨1403,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨1404,by decide⟩,⟨1384,by decide⟩,⟨1404,by decide⟩] | 2 => ![⟨1402,by decide⟩,⟨1405,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨1406,by decide⟩,⟨1407,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨1408,by decide⟩,⟨1407,by decide⟩,⟨45,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1409,by decide⟩,⟨0,by decide⟩] | _ => ![⟨44,by decide⟩,⟨1409,by decide⟩,⟨44,by decide⟩]

def ntree11LRRRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1410,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1411,by decide⟩,⟨1412,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨1413,by decide⟩,⟨1412,by decide⟩,⟨48,by decide⟩] | 3 => ![⟨1357,by decide⟩,⟨1414,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨1414,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨1406,by decide⟩,⟨1406,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1406,by decide⟩,⟨1406,by decide⟩,⟨50,by decide⟩] | _ => ![⟨1411,by decide⟩,⟨1411,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRLLLLL i else ntree11LRRRLLLLR (i - 7)

def ntree11LRRRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1411,by decide⟩,⟨1411,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨1415,by decide⟩,⟨1416,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨1417,by decide⟩,⟨1416,by decide⟩,⟨48,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1418,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨1418,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1414,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1418,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨1346,by decide⟩,⟨1419,by decide⟩,⟨1346,by decide⟩]

def ntree11LRRRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1420,by decide⟩,⟨1411,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨1420,by decide⟩,⟨1421,by decide⟩,⟨1359,by decide⟩] | 2 => ![⟨1422,by decide⟩,⟨1380,by decide⟩,⟨44,by decide⟩] | 3 => ![⟨1380,by decide⟩,⟨1423,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1422,by decide⟩,⟨1423,by decide⟩,⟨44,by decide⟩] | 5 => ![⟨1424,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1410,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1424,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree11LRRRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRLLLRL i else ntree11LRRRLLLRR (i - 8)

def ntree11LRRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRLLLL i else ntree11LRRRLLLR (i - 15)

def ntree11LRRRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1425,by decide⟩,⟨1384,by decide⟩,⟨1425,by decide⟩] | 1 => ![⟨1426,by decide⟩,⟨1414,by decide⟩,⟨1426,by decide⟩] | 2 => ![⟨1427,by decide⟩,⟨1389,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨1428,by decide⟩,⟨1429,by decide⟩,⟨1426,by decide⟩] | 4 => ![⟨1427,by decide⟩,⟨1429,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨1430,by decide⟩,⟨1391,by decide⟩,⟨47,by decide⟩] | _ => ![⟨1391,by decide⟩,⟨1431,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1430,by decide⟩,⟨1431,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨1432,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1432,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1433,by decide⟩,⟨1434,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1435,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1436,by decide⟩] | 6 => ![⟨1389,by decide⟩,⟨1429,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1437,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRLLRLL i else ntree11LRRRLLRLR (i - 7)

def ntree11LRRRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1437,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨118,by decide⟩,⟨1438,by decide⟩,⟨1374,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨1439,by decide⟩,⟨1374,by decide⟩] | 3 => ![⟨1384,by decide⟩,⟨1440,by decide⟩,⟨1441,by decide⟩] | 4 => ![⟨118,by decide⟩,⟨1442,by decide⟩,⟨1443,by decide⟩] | 5 => ![⟨1444,by decide⟩,⟨1445,by decide⟩,⟨1445,by decide⟩] | 6 => ![⟨1446,by decide⟩,⟨1447,by decide⟩,⟨1445,by decide⟩] | _ => ![⟨1446,by decide⟩,⟨1446,by decide⟩,⟨1444,by decide⟩]

def ntree11LRRRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1448,by decide⟩,⟨1448,by decide⟩,⟨1384,by decide⟩] | 1 => ![⟨1449,by decide⟩,⟨1449,by decide⟩,⟨1318,by decide⟩] | 2 => ![⟨1450,by decide⟩,⟨1445,by decide⟩,⟨1445,by decide⟩] | 3 => ![⟨1451,by decide⟩,⟨1314,by decide⟩,⟨1314,by decide⟩] | 4 => ![⟨1452,by decide⟩,⟨1447,by decide⟩,⟨1453,by decide⟩] | 5 => ![⟨1454,by decide⟩,⟨1388,by decide⟩,⟨1316,by decide⟩] | 6 => ![⟨1446,by decide⟩,⟨1446,by decide⟩,⟨1455,by decide⟩] | _ => ![⟨1456,by decide⟩,⟨1456,by decide⟩,⟨1319,by decide⟩]

def ntree11LRRRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRLLRRL i else ntree11LRRRLLRRR (i - 8)

def ntree11LRRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRLLRL i else ntree11LRRRLLRR (i - 15)

def ntree11LRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRRRLLL i else ntree11LRRRLLR (i - 31)

def ntree11LRRRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1444,by decide⟩,⟨1444,by decide⟩,⟨1444,by decide⟩] | 1 => ![⟨1444,by decide⟩,⟨1444,by decide⟩,⟨1444,by decide⟩] | 2 => ![⟨1313,by decide⟩,⟨1313,by decide⟩,⟨1313,by decide⟩] | 3 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨1318,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1457,by decide⟩,⟨1457,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨1458,by decide⟩,⟨1457,by decide⟩] | _ => ![⟨1312,by decide⟩,⟨1457,by decide⟩,⟨1457,by decide⟩]

def ntree11LRRRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1315,by decide⟩,⟨1458,by decide⟩,⟨1459,by decide⟩] | 1 => ![⟨1317,by decide⟩,⟨1398,by decide⟩,⟨1317,by decide⟩] | 2 => ![⟨1460,by decide⟩,⟨10,by decide⟩,⟨1460,by decide⟩] | 3 => ![⟨1460,by decide⟩,⟨96,by decide⟩,⟨1460,by decide⟩] | 4 => ![⟨1461,by decide⟩,⟨14,by decide⟩,⟨1460,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1462,by decide⟩] | 6 => ![⟨1463,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1464,by decide⟩,⟨1389,by decide⟩,⟨135,by decide⟩]

def ntree11LRRRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRLRLLL i else ntree11LRRRLRLLR (i - 7)

def ntree11LRRRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1463,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩] | 1 => ![⟨1465,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 2 => ![⟨1466,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩] | 3 => ![⟨1467,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨1468,by decide⟩,⟨1469,by decide⟩] | 6 => ![⟨1470,by decide⟩,⟨11,by decide⟩,⟨1339,by decide⟩] | _ => ![⟨1338,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩]

def ntree11LRRRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1471,by decide⟩,⟨1412,by decide⟩,⟨1339,by decide⟩] | 1 => ![⟨1472,by decide⟩,⟨1473,by decide⟩,⟨1341,by decide⟩] | 2 => ![⟨1342,by decide⟩,⟨1468,by decide⟩,⟨1474,by decide⟩] | 3 => ![⟨1340,by decide⟩,⟨1475,by decide⟩,⟨1340,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1344,by decide⟩] | 5 => ![⟨1411,by decide⟩,⟨1411,by decide⟩,⟨1344,by decide⟩] | 6 => ![⟨1476,by decide⟩,⟨1476,by decide⟩,⟨1345,by decide⟩] | _ => ![⟨1338,by decide⟩,⟨1414,by decide⟩,⟨1338,by decide⟩]

def ntree11LRRRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRLRLRL i else ntree11LRRRLRLRR (i - 8)

def ntree11LRRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRLRLL i else ntree11LRRRLRLR (i - 15)

def ntree11LRRRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1338,by decide⟩,⟨96,by decide⟩,⟨1338,by decide⟩] | 1 => ![⟨1463,by decide⟩,⟨1477,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨65,by decide⟩,⟨65,by decide⟩] | 3 => ![⟨1444,by decide⟩,⟨1478,by decide⟩,⟨1444,by decide⟩] | 4 => ![⟨1446,by decide⟩,⟨1479,by decide⟩,⟨1480,by decide⟩] | 5 => ![⟨1437,by decide⟩,⟨10,by decide⟩,⟨1318,by decide⟩] | _ => ![⟨1481,by decide⟩,⟨1449,by decide⟩,⟨1368,by decide⟩]

def ntree11LRRRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1482,by decide⟩,⟨1478,by decide⟩,⟨1482,by decide⟩] | 1 => ![⟨1427,by decide⟩,⟨1483,by decide⟩,⟨1367,by decide⟩] | 2 => ![⟨1484,by decide⟩,⟨1448,by decide⟩,⟨1425,by decide⟩] | 3 => ![⟨1485,by decide⟩,⟨1479,by decide⟩,⟨1486,by decide⟩] | 4 => ![⟨1487,by decide⟩,⟨1488,by decide⟩,⟨1370,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1489,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1490,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1310,by decide⟩,⟨150,by decide⟩,⟨1310,by decide⟩]

def ntree11LRRRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRLRRLL i else ntree11LRRRLRRLR (i - 7)

def ntree11LRRRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1317,by decide⟩,⟨153,by decide⟩,⟨1317,by decide⟩] | 1 => ![⟨1491,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1492,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1493,by decide⟩,⟨1494,by decide⟩,⟨1494,by decide⟩] | 4 => ![⟨1495,by decide⟩,⟨1494,by decide⟩,⟨1494,by decide⟩] | 5 => ![⟨1496,by decide⟩,⟨1313,by decide⟩,⟨1313,by decide⟩] | 6 => ![⟨1493,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1497,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1498,by decide⟩] | 1 => ![⟨1499,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1499,by decide⟩,⟨153,by decide⟩,⟨1500,by decide⟩] | 3 => ![⟨1501,by decide⟩,⟨10,by decide⟩,⟨1317,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1500,by decide⟩] | 5 => ![⟨1502,by decide⟩,⟨1502,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1503,by decide⟩,⟨161,by decide⟩,⟨1310,by decide⟩] | _ => ![⟨1504,by decide⟩,⟨1504,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRLRRRL i else ntree11LRRRLRRRR (i - 8)

def ntree11LRRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRLRRL i else ntree11LRRRLRRR (i - 15)

def ntree11LRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRRRLRL i else ntree11LRRRLRR (i - 31)

def ntree11LRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LRRRLL i else ntree11LRRRLR (i - 62)

end Paper2.Certificates.Q6.Coverage

import Paper2.Certificates.Q6CoverageCompact.Layer14Part004

namespace Paper2.Certificates.Q6.Coverage

def ntree14LLRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRRLLL i else ntree14LLRRLLR (i - 16)

def ntree14LLRRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨47,by decide⟩,⟨379,by decide⟩,⟨375,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨380,by decide⟩,⟨345,by decide⟩] | 2 => ![⟨381,by decide⟩,⟨382,by decide⟩,⟨347,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨383,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨384,by decide⟩,⟨385,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨50,by decide⟩,⟨386,by decide⟩,⟨386,by decide⟩] | 6 => ![⟨387,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩] | _ => ![⟨53,by decide⟩,⟨389,by decide⟩,⟨386,by decide⟩]

def ntree14LLRRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨50,by decide⟩,⟨390,by decide⟩,⟨50,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨391,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨392,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨393,by decide⟩,⟨391,by decide⟩,⟨24,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨394,by decide⟩,⟨345,by decide⟩] | 5 => ![⟨46,by decide⟩,⟨395,by decide⟩,⟨355,by decide⟩] | 6 => ![⟨357,by decide⟩,⟨396,by decide⟩,⟨396,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨397,by decide⟩]

def ntree14LLRRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRLRLL i else ntree14LLRRLRLR (i - 8)

def ntree14LLRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨398,by decide⟩] | 1 => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨399,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨400,by decide⟩,⟨400,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨401,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨402,by decide⟩,⟨403,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨401,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨404,by decide⟩,⟨403,by decide⟩,⟨1,by decide⟩] | _ => ![⟨8,by decide⟩,⟨405,by decide⟩,⟨8,by decide⟩]

def ntree14LLRRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨406,by decide⟩,⟨407,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨336,by decide⟩,⟨401,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨408,by decide⟩,⟨408,by decide⟩]

def ntree14LLRRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨402,by decide⟩,⟨409,by decide⟩,⟨408,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨343,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨404,by decide⟩,⟨402,by decide⟩,⟨0,by decide⟩] | _ => ![⟨406,by decide⟩,⟨406,by decide⟩,⟨8,by decide⟩]

def ntree14LLRRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLRRLRRRL i else ntree14LLRRLRRRR (i - 4)

def ntree14LLRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRLRRL i else ntree14LLRRLRRR (i - 8)

def ntree14LLRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRRLRL i else ntree14LLRRLRR (i - 16)

def ntree14LLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LLRRLL i else ntree14LLRRLR (i - 32)

def ntree14LLRRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨410,by decide⟩] | 1 => ![⟨411,by decide⟩,⟨1,by decide⟩,⟨412,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨413,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨414,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨415,by decide⟩,⟨416,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨415,by decide⟩,⟨415,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨417,by decide⟩,⟨0,by decide⟩,⟨417,by decide⟩] | _ => ![⟨417,by decide⟩,⟨0,by decide⟩,⟨418,by decide⟩]

def ntree14LLRRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨419,by decide⟩,⟨0,by decide⟩,⟨420,by decide⟩] | 1 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨421,by decide⟩,⟨402,by decide⟩,⟨420,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨422,by decide⟩] | 4 => ![⟨423,by decide⟩,⟨423,by decide⟩,⟨399,by decide⟩] | 5 => ![⟨423,by decide⟩,⟨424,by decide⟩,⟨400,by decide⟩] | 6 => ![⟨425,by decide⟩,⟨426,by decide⟩,⟨356,by decide⟩] | _ => ![⟨427,by decide⟩,⟨428,by decide⟩,⟨358,by decide⟩]

def ntree14LLRRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRRLLL i else ntree14LLRRRLLR (i - 8)

def ntree14LLRRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨429,by decide⟩] | 1 => ![⟨430,by decide⟩,⟨1,by decide⟩,⟨431,by decide⟩] | 2 => ![⟨430,by decide⟩,⟨0,by decide⟩,⟨430,by decide⟩] | 3 => ![⟨432,by decide⟩,⟨432,by decide⟩,⟨433,by decide⟩] | 4 => ![⟨433,by decide⟩,⟨433,by decide⟩,⟨433,by decide⟩] | 5 => ![⟨433,by decide⟩,⟨434,by decide⟩,⟨434,by decide⟩] | 6 => ![⟨432,by decide⟩,⟨435,by decide⟩,⟨434,by decide⟩] | _ => ![⟨368,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LLRRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨425,by decide⟩,⟨425,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨427,by decide⟩,⟨427,by decide⟩,⟨357,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨436,by decide⟩] | _ => ![⟨0,by decide⟩,⟨356,by decide⟩,⟨437,by decide⟩]

def ntree14LLRRRLRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨438,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨436,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | 3 => ![⟨30,by decide⟩,⟨363,by decide⟩,⟨437,by decide⟩] | _ => ![⟨0,by decide⟩,⟨343,by decide⟩,⟨436,by decide⟩]

def ntree14LLRRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLRRRLRRL i else ntree14LLRRRLRRR (i - 4)

def ntree14LLRRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRRLRL i else ntree14LLRRRLRR (i - 8)

def ntree14LLRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRRRLL i else ntree14LLRRRLR (i - 16)

def ntree14LLRRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨368,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨439,by decide⟩,⟨402,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨440,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨441,by decide⟩,⟨406,by decide⟩,⟨12,by decide⟩] | 4 => ![⟨442,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨443,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨4,by decide⟩,⟨443,by decide⟩,⟨4,by decide⟩] | _ => ![⟨444,by decide⟩,⟨415,by decide⟩,⟨4,by decide⟩]

def ntree14LLRRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨445,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨446,by decide⟩,⟨446,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨447,by decide⟩,⟨447,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨449,by decide⟩,⟨449,by decide⟩] | 5 => ![⟨402,by decide⟩,⟨450,by decide⟩,⟨345,by decide⟩] | 6 => ![⟨360,by decide⟩,⟨357,by decide⟩,⟨360,by decide⟩] | _ => ![⟨0,by decide⟩,⟨451,by decide⟩,⟨451,by decide⟩]

def ntree14LLRRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRRRLL i else ntree14LLRRRRLR (i - 8)

def ntree14LLRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨402,by decide⟩,⟨452,by decide⟩,⟨451,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨451,by decide⟩,⟨453,by decide⟩] | 2 => ![⟨454,by decide⟩,⟨432,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨433,by decide⟩,⟨455,by decide⟩] | 4 => ![⟨456,by decide⟩,⟨30,by decide⟩,⟨457,by decide⟩] | 5 => ![⟨457,by decide⟩,⟨0,by decide⟩,⟨457,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨458,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LLRRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨459,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨460,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨402,by decide⟩,⟨461,by decide⟩,⟨102,by decide⟩] | _ => ![⟨0,by decide⟩,⟨462,by decide⟩,⟨462,by decide⟩]

def ntree14LLRRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨4,by decide⟩,⟨462,by decide⟩,⟨463,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨464,by decide⟩,⟨464,by decide⟩] | 2 => ![⟨12,by decide⟩,⟨464,by decide⟩,⟨465,by decide⟩] | 3 => ![⟨30,by decide⟩,⟨466,by decide⟩,⟨462,by decide⟩] | _ => ![⟨34,by decide⟩,⟨466,by decide⟩,⟨463,by decide⟩]

def ntree14LLRRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLRRRRRRL i else ntree14LLRRRRRRR (i - 4)

def ntree14LLRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRRRRL i else ntree14LLRRRRRR (i - 8)

def ntree14LLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRRRRL i else ntree14LLRRRRR (i - 16)

def ntree14LLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 33 then ntree14LLRRRL i else ntree14LLRRRR (i - 33)

def ntree14LLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LLRRL i else ntree14LLRRR (i - 65)

def ntree14LLR (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14LLRL i else ntree14LLRR (i - 130)

def ntree14LL (i : Nat) : Fin 3 → Fin 1937 := if i < 260 then ntree14LLL i else ntree14LLR (i - 260)

def ntree14LRLLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨65,by decide⟩,⟨467,by decide⟩,⟨451,by decide⟩] | 1 => ![⟨468,by decide⟩,⟨468,by decide⟩,⟨468,by decide⟩] | 2 => ![⟨468,by decide⟩,⟨469,by decide⟩,⟨469,by decide⟩] | 3 => ![⟨470,by decide⟩,⟨0,by decide⟩,⟨470,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨471,by decide⟩,⟨471,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨468,by decide⟩,⟨472,by decide⟩,⟨472,by decide⟩] | _ => ![⟨473,by decide⟩,⟨474,by decide⟩,⟨474,by decide⟩]

def ntree14LRLLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨119,by decide⟩,⟨475,by decide⟩,⟨475,by decide⟩] | 1 => ![⟨476,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨333,by decide⟩,⟨477,by decide⟩,⟨118,by decide⟩] | 3 => ![⟨478,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨479,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨480,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨481,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨482,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRLLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLLLLL i else ntree14LRLLLLLR (i - 8)

def ntree14LRLLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨482,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨483,by decide⟩,⟨483,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨483,by decide⟩,⟨484,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨485,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨486,by decide⟩,⟨1,by decide⟩,⟨487,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨482,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩]

def ntree14LRLLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨488,by decide⟩,⟨30,by decide⟩,⟨489,by decide⟩] | 1 => ![⟨490,by decide⟩,⟨0,by decide⟩,⟨491,by decide⟩] | 2 => ![⟨490,by decide⟩,⟨118,by decide⟩,⟨492,by decide⟩] | 3 => ![⟨483,by decide⟩,⟨493,by decide⟩,⟨118,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨494,by decide⟩,⟨47,by decide⟩,⟨470,by decide⟩] | 6 => ![⟨482,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩] | _ => ![⟨495,by decide⟩,⟨347,by decide⟩,⟨347,by decide⟩]

def ntree14LRLLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLLLRL i else ntree14LRLLLLRR (i - 8)

def ntree14LRLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLLLLL i else ntree14LRLLLLR (i - 16)

def ntree14LRLLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨158,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩] | 1 => ![⟨470,by decide⟩,⟨401,by decide⟩,⟨470,by decide⟩] | 2 => ![⟨496,by decide⟩,⟨496,by decide⟩,⟨468,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨497,by decide⟩] | 4 => ![⟨176,by decide⟩,⟨1,by decide⟩,⟨498,by decide⟩] | 5 => ![⟨499,by decide⟩,⟨402,by decide⟩,⟨176,by decide⟩] | 6 => ![⟨483,by decide⟩,⟨500,by decide⟩,⟨178,by decide⟩] | _ => ![⟨501,by decide⟩,⟨502,by decide⟩,⟨180,by decide⟩]

def ntree14LRLLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨179,by decide⟩,⟨503,by decide⟩,⟨179,by decide⟩] | 1 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨501,by decide⟩,⟨501,by decide⟩,⟨179,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨402,by decide⟩,⟨504,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨470,by decide⟩,⟨178,by decide⟩,⟨505,by decide⟩] | 6 => ![⟨506,by decide⟩,⟨0,by decide⟩,⟨506,by decide⟩] | _ => ![⟨0,by decide⟩,⟨507,by decide⟩,⟨507,by decide⟩]

def ntree14LRLLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLLRLL i else ntree14LRLLLRLR (i - 8)

def ntree14LRLLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨508,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨415,by decide⟩,⟨509,by decide⟩,⟨118,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨510,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨511,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨169,by decide⟩,⟨512,by decide⟩,⟨345,by decide⟩] | 5 => ![⟨513,by decide⟩,⟨402,by decide⟩,⟨116,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | _ => ![⟨402,by decide⟩,⟨514,by decide⟩,⟨118,by decide⟩]

def ntree14LRLLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨496,by decide⟩,⟨515,by decide⟩,⟨472,by decide⟩] | 1 => ![⟨166,by decide⟩,⟨516,by decide⟩,⟨345,by decide⟩] | 2 => ![⟨402,by decide⟩,⟨517,by decide⟩,⟨135,by decide⟩] | _ => ![⟨406,by decide⟩,⟨518,by decide⟩,⟨134,by decide⟩]

def ntree14LRLLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨402,by decide⟩,⟨519,by decide⟩,⟨118,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨520,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨521,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨167,by decide⟩,⟨522,by decide⟩,⟨345,by decide⟩] | _ => ![⟨168,by decide⟩,⟨523,by decide⟩,⟨355,by decide⟩]

def ntree14LRLLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRLLLRRRL i else ntree14LRLLLRRRR (i - 4)

def ntree14LRLLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLLRRL i else ntree14LRLLLRRR (i - 8)

def ntree14LRLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLLLRL i else ntree14LRLLLRR (i - 16)

def ntree14LRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LRLLLL i else ntree14LRLLLR (i - 32)

def ntree14LRLLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨524,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨525,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨486,by decide⟩,⟨0,by decide⟩,⟨486,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨526,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨527,by decide⟩,⟨527,by decide⟩] | 5 => ![⟨402,by decide⟩,⟨528,by decide⟩,⟨527,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | _ => ![⟨0,by decide⟩,⟨530,by decide⟩,⟨530,by decide⟩]

def ntree14LRLLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨179,by decide⟩,⟨531,by decide⟩,⟨531,by decide⟩] | 1 => ![⟨433,by decide⟩,⟨532,by decide⟩,⟨532,by decide⟩] | 2 => ![⟨432,by decide⟩,⟨533,by decide⟩,⟨532,by decide⟩] | 3 => ![⟨402,by decide⟩,⟨534,by decide⟩,⟨118,by decide⟩] | 4 => ![⟨30,by decide⟩,⟨535,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨402,by decide⟩,⟨536,by decide⟩,⟨118,by decide⟩] | 6 => ![⟨501,by decide⟩,⟨537,by decide⟩,⟨237,by decide⟩] | _ => ![⟨179,by decide⟩,⟨538,by decide⟩,⟨179,by decide⟩]

def ntree14LRLLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLRLLL i else ntree14LRLLRLLR (i - 8)

def ntree14LRLLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨30,by decide⟩,⟨539,by decide⟩,⟨530,by decide⟩] | 1 => ![⟨179,by decide⟩,⟨540,by decide⟩,⟨179,by decide⟩] | 2 => ![⟨186,by decide⟩,⟨541,by decide⟩,⟨531,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨542,by decide⟩,⟨542,by decide⟩] | 4 => ![⟨179,by decide⟩,⟨543,by decide⟩,⟨543,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨544,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨179,by decide⟩,⟨545,by decide⟩,⟨179,by decide⟩] | _ => ![⟨30,by decide⟩,⟨546,by decide⟩,⟨542,by decide⟩]

def ntree14LRLLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨186,by decide⟩,⟨547,by decide⟩,⟨543,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨548,by decide⟩,⟨548,by decide⟩] | 2 => ![⟨196,by decide⟩,⟨549,by decide⟩,⟨549,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨550,by decide⟩,⟨550,by decide⟩] | 4 => ![⟨199,by decide⟩,⟨551,by decide⟩,⟨551,by decide⟩] | 5 => ![⟨30,by decide⟩,⟨552,by decide⟩,⟨548,by decide⟩] | 6 => ![⟨201,by decide⟩,⟨553,by decide⟩,⟨345,by decide⟩] | _ => ![⟨202,by decide⟩,⟨554,by decide⟩,⟨549,by decide⟩]

def ntree14LRLLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLRLRL i else ntree14LRLLRLRR (i - 8)

def ntree14LRLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLLRLL i else ntree14LRLLRLR (i - 16)

def ntree14LRLLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨8,by decide⟩,⟨555,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨179,by decide⟩,⟨556,by decide⟩,⟨179,by decide⟩] | 2 => ![⟨199,by decide⟩,⟨557,by decide⟩,⟨199,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨558,by decide⟩,⟨550,by decide⟩] | 4 => ![⟨204,by decide⟩,⟨559,by decide⟩,⟨543,by decide⟩] | 5 => ![⟨205,by decide⟩,⟨560,by decide⟩,⟨551,by decide⟩] | 6 => ![⟨561,by decide⟩,⟨0,by decide⟩,⟨561,by decide⟩] | _ => ![⟨562,by decide⟩,⟨468,by decide⟩,⟨562,by decide⟩]

def ntree14LRLLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨563,by decide⟩] | 1 => ![⟨561,by decide⟩,⟨345,by decide⟩,⟨564,by decide⟩] | 2 => ![⟨562,by decide⟩,⟨472,by decide⟩,⟨565,by decide⟩] | 3 => ![⟨566,by decide⟩,⟨567,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨568,by decide⟩,⟨569,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨333,by decide⟩,⟨333,by decide⟩,⟨249,by decide⟩] | 6 => ![⟨116,by decide⟩,⟨343,by decide⟩,⟨116,by decide⟩] | _ => ![⟨568,by decide⟩,⟨570,by decide⟩,⟨118,by decide⟩]

def ntree14LRLLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLRRLL i else ntree14LRLLRRLR (i - 8)

def ntree14LRLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨335,by decide⟩,⟨477,by decide⟩,⟨250,by decide⟩] | 1 => ![⟨336,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | 2 => ![⟨336,by decide⟩,⟨0,by decide⟩,⟨249,by decide⟩] | 3 => ![⟨263,by decide⟩,⟨345,by decide⟩,⟨571,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨4,by decide⟩,⟨572,by decide⟩,⟨4,by decide⟩]

def ntree14LRLLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨572,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨568,by decide⟩,⟨573,by decide⟩,⟨356,by decide⟩] | 2 => ![⟨490,by decide⟩,⟨356,by decide⟩,⟨574,by decide⟩] | _ => ![⟨575,by decide⟩,⟨576,by decide⟩,⟨577,by decide⟩]

def ntree14LRLLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨578,by decide⟩,⟨579,by decide⟩,⟨580,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨582,by decide⟩,⟨583,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨584,by decide⟩,⟨584,by decide⟩,⟨0,by decide⟩] | _ => ![⟨116,by decide⟩,⟨356,by decide⟩,⟨585,by decide⟩]

def ntree14LRLLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRLLRRRRL i else ntree14LRLLRRRRR (i - 4)

def ntree14LRLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLLRRRL i else ntree14LRLLRRRR (i - 8)

def ntree14LRLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLLRRL i else ntree14LRLLRRR (i - 16)

def ntree14LRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LRLLRL i else ntree14LRLLRR (i - 32)

def ntree14LRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LRLLL i else ntree14LRLLR (i - 65)

def ntree14LRLRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨158,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | 1 => ![⟨159,by decide⟩,⟨363,by decide⟩,⟨585,by decide⟩] | 2 => ![⟨158,by decide⟩,⟨343,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨586,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨587,by decide⟩] | 5 => ![⟨588,by decide⟩,⟨588,by decide⟩,⟨588,by decide⟩] | 6 => ![⟨589,by decide⟩,⟨0,by decide⟩,⟨589,by decide⟩] | _ => ![⟨590,by decide⟩,⟨399,by decide⟩,⟨590,by decide⟩]

def ntree14LRLRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨589,by decide⟩,⟨245,by decide⟩,⟨591,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨592,by decide⟩,⟨592,by decide⟩] | 2 => ![⟨415,by decide⟩,⟨593,by decide⟩,⟨245,by decide⟩] | 3 => ![⟨589,by decide⟩,⟨343,by decide⟩,⟨589,by decide⟩] | 4 => ![⟨169,by decide⟩,⟨594,by decide⟩,⟨592,by decide⟩] | 5 => ![⟨595,by decide⟩,⟨169,by decide⟩,⟨589,by decide⟩] | 6 => ![⟨468,by decide⟩,⟨468,by decide⟩,⟨596,by decide⟩] | _ => ![⟨589,by decide⟩,⟨173,by decide⟩,⟨597,by decide⟩]

def ntree14LRLRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRLLLL i else ntree14LRLRLLLR (i - 8)

def ntree14LRLRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨598,by decide⟩,⟨65,by decide⟩,⟨589,by decide⟩] | 1 => ![⟨599,by decide⟩,⟨399,by decide⟩,⟨599,by decide⟩] | 2 => ![⟨600,by decide⟩,⟨588,by decide⟩,⟨588,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨587,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨601,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨30,by decide⟩,⟨602,by decide⟩,⟨592,by decide⟩] | _ => ![⟨0,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩]

def ntree14LRLRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨179,by decide⟩,⟨603,by decide⟩,⟨603,by decide⟩] | 1 => ![⟨179,by decide⟩,⟨604,by decide⟩,⟨179,by decide⟩] | 2 => ![⟨186,by decide⟩,⟨605,by decide⟩,⟨603,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨606,by decide⟩,⟨356,by decide⟩] | 4 => ![⟨607,by decide⟩,⟨607,by decide⟩,⟨588,by decide⟩] | 5 => ![⟨608,by decide⟩,⟨608,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨588,by decide⟩,⟨609,by decide⟩,⟨609,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨610,by decide⟩]

def ntree14LRLRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRLLRL i else ntree14LRLRLLRR (i - 8)

def ntree14LRLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLRLLL i else ntree14LRLRLLR (i - 16)

def ntree14LRLRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨176,by decide⟩,⟨356,by decide⟩,⟨611,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨612,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨613,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨614,by decide⟩] | 4 => ![⟨615,by decide⟩,⟨588,by decide⟩,⟨615,by decide⟩] | 5 => ![⟨588,by decide⟩,⟨616,by decide⟩,⟨616,by decide⟩] | 6 => ![⟨4,by decide⟩,⟨524,by decide⟩,⟨4,by decide⟩] | _ => ![⟨617,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRLRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨618,by decide⟩] | 2 => ![⟨314,by decide⟩,⟨345,by decide⟩,⟨619,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨542,by decide⟩,⟨620,by decide⟩] | 4 => ![⟨317,by decide⟩,⟨543,by decide⟩,⟨621,by decide⟩] | 5 => ![⟨622,by decide⟩,⟨622,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨623,by decide⟩,⟨622,by decide⟩,⟨4,by decide⟩] | _ => ![⟨624,by decide⟩,⟨624,by decide⟩,⟨0,by decide⟩]

def ntree14LRLRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRLRLL i else ntree14LRLRLRLR (i - 8)

def ntree14LRLRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨625,by decide⟩,⟨625,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨626,by decide⟩,⟨626,by decide⟩] | 2 => ![⟨16,by decide⟩,⟨627,by decide⟩,⟨627,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨628,by decide⟩,⟨628,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨629,by decide⟩,⟨629,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨630,by decide⟩,⟨630,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨631,by decide⟩,⟨631,by decide⟩] | _ => ![⟨622,by decide⟩,⟨632,by decide⟩,⟨345,by decide⟩]

def ntree14LRLRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨338,by decide⟩,⟨633,by decide⟩,⟨628,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨634,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨635,by decide⟩,⟨2,by decide⟩] | _ => ![⟨4,by decide⟩,⟨634,by decide⟩,⟨4,by decide⟩]

def ntree14LRLRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨636,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨622,by decide⟩,⟨637,by decide⟩,⟨356,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨638,by decide⟩,⟨638,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨639,by decide⟩,⟨639,by decide⟩] | _ => ![⟨4,by decide⟩,⟨638,by decide⟩,⟨640,by decide⟩]

def ntree14LRLRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRLRLRRRL i else ntree14LRLRLRRRR (i - 4)

def ntree14LRLRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRLRRL i else ntree14LRLRLRRR (i - 8)

def ntree14LRLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLRLRL i else ntree14LRLRLRR (i - 16)

def ntree14LRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LRLRLL i else ntree14LRLRLR (i - 32)

def ntree14LRLRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨6,by decide⟩,⟨639,by decide⟩,⟨641,by decide⟩] | 1 => ![⟨642,by decide⟩,⟨642,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨642,by decide⟩,⟨643,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨644,by decide⟩,⟨644,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨645,by decide⟩,⟨645,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨646,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨38,by decide⟩,⟨647,by decide⟩,⟨647,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRLRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨648,by decide⟩,⟨648,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨649,by decide⟩,⟨649,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨650,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨651,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨652,by decide⟩,⟨652,by decide⟩] | 5 => ![⟨653,by decide⟩,⟨654,by decide⟩,⟨345,by decide⟩] | 6 => ![⟨655,by decide⟩,⟨656,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩]

def ntree14LRLRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRRLLL i else ntree14LRLRRLLR (i - 8)

def ntree14LRLRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨657,by decide⟩,⟨657,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨658,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨659,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 3 => ![⟨660,by decide⟩,⟨660,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨661,by decide⟩,⟨661,by decide⟩,⟨2,by decide⟩] | 5 => ![⟨662,by decide⟩,⟨662,by decide⟩,⟨8,by decide⟩] | 6 => ![⟨663,by decide⟩,⟨663,by decide⟩,⟨10,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨664,by decide⟩]

def ntree14LRLRRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨665,by decide⟩] | 1 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨666,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨667,by decide⟩] | 3 => ![⟨668,by decide⟩,⟨668,by decide⟩,⟨16,by decide⟩] | 4 => ![⟨56,by decide⟩,⟨669,by decide⟩,⟨56,by decide⟩] | 5 => ![⟨58,by decide⟩,⟨670,by decide⟩,⟨58,by decide⟩] | 6 => ![⟨56,by decide⟩,⟨671,by decide⟩,⟨671,by decide⟩] | _ => ![⟨0,by decide⟩,⟨672,by decide⟩,⟨672,by decide⟩]

def ntree14LRLRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRRLRL i else ntree14LRLRRLRR (i - 8)

def ntree14LRLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLRRLL i else ntree14LRLRRLR (i - 16)

def ntree14LRLRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨402,by decide⟩,⟨673,by decide⟩,⟨672,by decide⟩] | 1 => ![⟨657,by decide⟩,⟨674,by decide⟩,⟨671,by decide⟩] | 2 => ![⟨658,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨675,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨402,by decide⟩,⟨676,by decide⟩,⟨638,by decide⟩] | 5 => ![⟨660,by decide⟩,⟨677,by decide⟩,⟨356,by decide⟩] | 6 => ![⟨661,by decide⟩,⟨678,by decide⟩,⟨639,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨679,by decide⟩]

def ntree14LRLRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨680,by decide⟩] | 1 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨679,by decide⟩] | 2 => ![⟨60,by decide⟩,⟨681,by decide⟩,⟨681,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨682,by decide⟩,⟨682,by decide⟩] | 4 => ![⟨56,by decide⟩,⟨683,by decide⟩,⟨683,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨684,by decide⟩,⟨684,by decide⟩] | 6 => ![⟨685,by decide⟩,⟨634,by decide⟩,⟨665,by decide⟩] | _ => ![⟨686,by decide⟩,⟨634,by decide⟩,⟨667,by decide⟩]

def ntree14LRLRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRRRLL i else ntree14LRLRRRLR (i - 8)

def ntree14LRLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨685,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨685,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨84,by decide⟩,⟨356,by decide⟩,⟨687,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨688,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨689,by decide⟩,⟨657,by decide⟩,⟨89,by decide⟩] | 6 => ![⟨690,by decide⟩,⟨622,by decide⟩,⟨90,by decide⟩] | _ => ![⟨56,by decide⟩,⟨691,by decide⟩,⟨691,by decide⟩]

def ntree14LRLRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨4,by decide⟩,⟨692,by decide⟩,⟨693,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨692,by decide⟩,⟨692,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨694,by decide⟩] | _ => ![⟨89,by decide⟩,⟨691,by decide⟩,⟨695,by decide⟩]

def ntree14LRLRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨90,by decide⟩,⟨345,by decide⟩,⟨696,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨697,by decide⟩] | 2 => ![⟨660,by decide⟩,⟨698,by decide⟩,⟨345,by decide⟩] | 3 => ![⟨56,by decide⟩,⟨699,by decide⟩,⟨699,by decide⟩] | _ => ![⟨58,by decide⟩,⟨700,by decide⟩,⟨700,by decide⟩]

def ntree14LRLRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRLRRRRRL i else ntree14LRLRRRRRR (i - 4)

def ntree14LRLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRLRRRRL i else ntree14LRLRRRRR (i - 8)

def ntree14LRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRLRRRL i else ntree14LRLRRRR (i - 16)

def ntree14LRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LRLRRL i else ntree14LRLRRR (i - 32)

def ntree14LRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LRLRL i else ntree14LRLRR (i - 65)

def ntree14LRL (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14LRLL i else ntree14LRLR (i - 130)

def ntree14LRRLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨701,by decide⟩,⟨701,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨702,by decide⟩,⟨702,by decide⟩] | 2 => ![⟨657,by decide⟩,⟨703,by decide⟩,⟨691,by decide⟩] | 3 => ![⟨622,by decide⟩,⟨704,by decide⟩,⟨692,by decide⟩] | 4 => ![⟨660,by decide⟩,⟨705,by decide⟩,⟨628,by decide⟩] | 5 => ![⟨661,by decide⟩,⟨706,by decide⟩,⟨629,by decide⟩] | 6 => ![⟨56,by decide⟩,⟨707,by decide⟩,⟨707,by decide⟩] | _ => ![⟨42,by decide⟩,⟨692,by decide⟩,⟨708,by decide⟩]

def ntree14LRRLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨709,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨710,by decide⟩,⟨710,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨711,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨712,by decide⟩] | 4 => ![⟨338,by decide⟩,⟨338,by decide⟩,⟨709,by decide⟩] | 5 => ![⟨122,by decide⟩,⟨345,by decide⟩,⟨713,by decide⟩] | 6 => ![⟨714,by decide⟩,⟨333,by decide⟩,⟨122,by decide⟩] | _ => ![⟨129,by decide⟩,⟨345,by decide⟩,⟨715,by decide⟩]

def ntree14LRRLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLLLLL i else ntree14LRRLLLLR (i - 8)

def ntree14LRRLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨133,by decide⟩,⟨355,by decide⟩,⟨716,by decide⟩] | 1 => ![⟨717,by decide⟩,⟨622,by decide⟩,⟨122,by decide⟩] | 2 => ![⟨718,by decide⟩,⟨718,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨719,by decide⟩,⟨718,by decide⟩,⟨109,by decide⟩] | 4 => ![⟨718,by decide⟩,⟨720,by decide⟩,⟨710,by decide⟩] | 5 => ![⟨721,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨722,by decide⟩,⟨722,by decide⟩,⟨140,by decide⟩] | _ => ![⟨723,by decide⟩,⟨723,by decide⟩,⟨140,by decide⟩]

def ntree14LRRLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨109,by decide⟩,⟨638,by decide⟩,⟨724,by decide⟩] | 1 => ![⟨119,by decide⟩,⟨725,by decide⟩,⟨119,by decide⟩] | 2 => ![⟨726,by decide⟩,⟨38,by decide⟩,⟨38,by decide⟩] | 3 => ![⟨129,by decide⟩,⟨371,by decide⟩,⟨727,by decide⟩] | 4 => ![⟨718,by decide⟩,⟨728,by decide⟩,⟨371,by decide⟩] | 5 => ![⟨729,by decide⟩,⟨718,by decide⟩,⟨42,by decide⟩] | 6 => ![⟨730,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨730,by decide⟩,⟨634,by decide⟩,⟨709,by decide⟩]

def ntree14LRRLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLLLRL i else ntree14LRRLLLRR (i - 8)

def ntree14LRRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRLLLL i else ntree14LRRLLLR (i - 16)

def ntree14LRRLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨731,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨116,by decide⟩,⟨634,by decide⟩,⟨116,by decide⟩] | 2 => ![⟨732,by decide⟩,⟨656,by decide⟩,⟨122,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨733,by decide⟩,⟨734,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨733,by decide⟩,⟨733,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨735,by decide⟩,⟨735,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨736,by decide⟩,⟨736,by decide⟩] | _ => ![⟨140,by decide⟩,⟨737,by decide⟩,⟨737,by decide⟩]

def ntree14LRRLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨738,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨739,by decide⟩,⟨739,by decide⟩] | 2 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨738,by decide⟩] | 3 => ![⟨740,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 4 => ![⟨741,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨742,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨743,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨744,by decide⟩,⟨415,by decide⟩,⟨122,by decide⟩]

def ntree14LRRLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLLRLL i else ntree14LRRLLRLR (i - 8)

def ntree14LRRLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨745,by decide⟩,⟨402,by decide⟩,⟨129,by decide⟩] | 1 => ![⟨746,by decide⟩,⟨60,by decide⟩,⟨60,by decide⟩] | 2 => ![⟨747,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 3 => ![⟨748,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨749,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨750,by decide⟩,⟨402,by decide⟩,⟨122,by decide⟩] | 6 => ![⟨751,by decide⟩,⟨406,by decide⟩,⟨133,by decide⟩] | _ => ![⟨752,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩]

def ntree14LRRLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨753,by decide⟩,⟨657,by decide⟩,⟨171,by decide⟩] | 1 => ![⟨754,by decide⟩,⟨402,by decide⟩,⟨122,by decide⟩] | 2 => ![⟨755,by decide⟩,⟨755,by decide⟩,⟨0,by decide⟩] | _ => ![⟨756,by decide⟩,⟨756,by decide⟩,⟨56,by decide⟩]

def ntree14LRRLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨757,by decide⟩,⟨757,by decide⟩,⟨179,by decide⟩] | 1 => ![⟨758,by decide⟩,⟨758,by decide⟩,⟨182,by decide⟩] | 2 => ![⟨179,by decide⟩,⟨759,by decide⟩,⟨759,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRRLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRRLLRRRL i else ntree14LRRLLRRRR (i - 4)

def ntree14LRRLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLLRRL i else ntree14LRRLLRRR (i - 8)

def ntree14LRRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRLLRL i else ntree14LRRLLRR (i - 16)

def ntree14LRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LRRLLL i else ntree14LRRLLR (i - 32)

def ntree14LRRLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨760,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨761,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨0,by decide⟩,⟨762,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨763,by decide⟩] | 5 => ![⟨764,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 6 => ![⟨765,by decide⟩,⟨402,by decide⟩,⟨229,by decide⟩] | _ => ![⟨0,by decide⟩,⟨766,by decide⟩,⟨766,by decide⟩]

def ntree14LRRLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨179,by decide⟩,⟨767,by decide⟩,⟨767,by decide⟩] | 1 => ![⟨56,by decide⟩,⟨768,by decide⟩,⟨768,by decide⟩] | 2 => ![⟨182,by decide⟩,⟨769,by decide⟩,⟨769,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨770,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨263,by decide⟩,⟨628,by decide⟩,⟨771,by decide⟩] | 6 => ![⟨264,by decide⟩,⟨629,by decide⟩,⟨772,by decide⟩] | _ => ![⟨270,by decide⟩,⟨356,by decide⟩,⟨773,by decide⟩]

def ntree14LRRLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLRLLL i else ntree14LRRLRLLR (i - 8)

def ntree14LRRLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨774,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨775,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨356,by decide⟩,⟨776,by decide⟩] | 4 => ![⟨269,by decide⟩,⟨345,by decide⟩,⟨777,by decide⟩] | 5 => ![⟨282,by decide⟩,⟨386,by decide⟩,⟨778,by decide⟩] | 6 => ![⟨253,by decide⟩,⟨779,by decide⟩,⟨780,by decide⟩] | _ => ![⟨254,by decide⟩,⟨779,by decide⟩,⟨779,by decide⟩]

def ntree14LRRLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨4,by decide⟩,⟨735,by decide⟩,⟨781,by decide⟩] | 1 => ![⟨122,by decide⟩,⟨356,by decide⟩,⟨782,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨736,by decide⟩,⟨783,by decide⟩] | 3 => ![⟨271,by decide⟩,⟨737,by decide⟩,⟨784,by decide⟩] | 4 => ![⟨272,by decide⟩,⟨345,by decide⟩,⟨785,by decide⟩] | 5 => ![⟨2,by decide⟩,⟨786,by decide⟩,⟨786,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨787,by decide⟩,⟨787,by decide⟩,⟨0,by decide⟩]

def ntree14LRRLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLRLRL i else ntree14LRRLRLRR (i - 8)

def ntree14LRRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRLRLL i else ntree14LRRLRLR (i - 16)

def ntree14LRRLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨788,by decide⟩,⟨788,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨122,by decide⟩,⟨592,by decide⟩,⟨789,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨299,by decide⟩,⟨790,by decide⟩,⟨790,by decide⟩] | 4 => ![⟨300,by decide⟩,⟨791,by decide⟩,⟨791,by decide⟩] | 5 => ![⟨760,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | 6 => ![⟨122,by decide⟩,⟨672,by decide⟩,⟨792,by decide⟩] | _ => ![⟨171,by decide⟩,⟨671,by decide⟩,⟨793,by decide⟩]

def ntree14LRRLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨794,by decide⟩] | 1 => ![⟨122,by decide⟩,⟨356,by decide⟩,⟨795,by decide⟩] | 2 => ![⟨122,by decide⟩,⟨356,by decide⟩,⟨796,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨797,by decide⟩] | 4 => ![⟨209,by decide⟩,⟨603,by decide⟩,⟨798,by decide⟩] | 5 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨799,by decide⟩] | 6 => ![⟨182,by decide⟩,⟨182,by decide⟩,⟨800,by decide⟩] | _ => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨801,by decide⟩]

def ntree14LRRLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLRRLL i else ntree14LRRLRRLR (i - 8)

def ntree14LRRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨90,by decide⟩,⟨710,by decide⟩,⟨802,by decide⟩] | 1 => ![⟨218,by decide⟩,⟨628,by decide⟩,⟨803,by decide⟩] | 2 => ![⟨299,by decide⟩,⟨804,by decide⟩,⟨804,by decide⟩] | 3 => ![⟨730,by decide⟩,⟨451,by decide⟩,⟨451,by decide⟩] | 4 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨805,by decide⟩] | 5 => ![⟨315,by decide⟩,⟨691,by decide⟩,⟨806,by decide⟩] | 6 => ![⟨316,by decide⟩,⟨345,by decide⟩,⟨807,by decide⟩] | _ => ![⟨4,by decide⟩,⟨766,by decide⟩,⟨808,by decide⟩]

def ntree14LRRLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨317,by decide⟩,⟨767,by decide⟩,⟨809,by decide⟩] | 1 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨810,by decide⟩] | 2 => ![⟨89,by decide⟩,⟨768,by decide⟩,⟨811,by decide⟩] | _ => ![⟨318,by decide⟩,⟨769,by decide⟩,⟨812,by decide⟩]

def ntree14LRRLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨319,by decide⟩,⟨543,by decide⟩,⟨813,by decide⟩] | 1 => ![⟨814,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨814,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨815,by decide⟩,⟨816,by decide⟩,⟨4,by decide⟩] | _ => ![⟨815,by decide⟩,⟨817,by decide⟩,⟨5,by decide⟩]

def ntree14LRRLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRRLRRRRL i else ntree14LRRLRRRRR (i - 4)

def ntree14LRRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRLRRRL i else ntree14LRRLRRRR (i - 8)

def ntree14LRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRLRRL i else ntree14LRRLRRR (i - 16)

def ntree14LRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LRRLRL i else ntree14LRRLRR (i - 32)

def ntree14LRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LRRLL i else ntree14LRRLR (i - 65)

def ntree14LRRRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨816,by decide⟩,⟨816,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨818,by decide⟩,⟨818,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨816,by decide⟩,⟨817,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨818,by decide⟩,⟨819,by decide⟩,⟨3,by decide⟩] | 4 => ![⟨820,by decide⟩,⟨820,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨820,by decide⟩,⟨821,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨822,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRRRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨823,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨824,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨824,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨825,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨826,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨827,by decide⟩,⟨0,by decide⟩,⟨827,by decide⟩] | 6 => ![⟨827,by decide⟩,⟨1,by decide⟩,⟨828,by decide⟩] | _ => ![⟨829,by decide⟩,⟨830,by decide⟩,⟨829,by decide⟩]

def ntree14LRRRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRLLLL i else ntree14LRRRLLLR (i - 8)

def ntree14LRRRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨829,by decide⟩,⟨831,by decide⟩,⟨832,by decide⟩] | 1 => ![⟨833,by decide⟩,⟨21,by decide⟩,⟨827,by decide⟩] | 2 => ![⟨827,by decide⟩,⟨23,by decide⟩,⟨827,by decide⟩] | 3 => ![⟨829,by decide⟩,⟨834,by decide⟩,⟨829,by decide⟩] | 4 => ![⟨827,by decide⟩,⟨824,by decide⟩,⟨827,by decide⟩] | 5 => ![⟨816,by decide⟩,⟨816,by decide⟩,⟨24,by decide⟩] | 6 => ![⟨827,by decide⟩,⟨835,by decide⟩,⟨836,by decide⟩] | _ => ![⟨837,by decide⟩,⟨2,by decide⟩,⟨837,by decide⟩]

def ntree14LRRRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨838,by decide⟩,⟨0,by decide⟩,⟨838,by decide⟩] | 1 => ![⟨838,by decide⟩,⟨1,by decide⟩,⟨839,by decide⟩] | 2 => ![⟨840,by decide⟩,⟨2,by decide⟩,⟨840,by decide⟩] | 3 => ![⟨840,by decide⟩,⟨3,by decide⟩,⟨841,by decide⟩] | 4 => ![⟨842,by decide⟩,⟨843,by decide⟩,⟨842,by decide⟩] | 5 => ![⟨842,by decide⟩,⟨844,by decide⟩,⟨845,by decide⟩] | 6 => ![⟨846,by decide⟩,⟨30,by decide⟩,⟨838,by decide⟩] | _ => ![⟨847,by decide⟩,⟨32,by decide⟩,⟨840,by decide⟩]

def ntree14LRRRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRLLRL i else ntree14LRRRLLRR (i - 8)

def ntree14LRRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRRLLL i else ntree14LRRRLLR (i - 16)

def ntree14LRRRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨848,by decide⟩,⟨0,by decide⟩,⟨848,by decide⟩] | 1 => ![⟨848,by decide⟩,⟨1,by decide⟩,⟨849,by decide⟩] | 2 => ![⟨850,by decide⟩,⟨35,by decide⟩,⟨848,by decide⟩] | 3 => ![⟨851,by decide⟩,⟨30,by decide⟩,⟨827,by decide⟩] | 4 => ![⟨852,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨853,by decide⟩,⟨854,by decide⟩,⟨829,by decide⟩] | 6 => ![⟨855,by decide⟩,⟨856,by decide⟩,⟨4,by decide⟩] | _ => ![⟨857,by decide⟩,⟨38,by decide⟩,⟨857,by decide⟩]

def ntree14LRRRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨858,by decide⟩,⟨859,by decide⟩,⟨858,by decide⟩] | 1 => ![⟨860,by decide⟩,⟨40,by decide⟩,⟨857,by decide⟩] | 2 => ![⟨861,by decide⟩,⟨38,by decide⟩,⟨38,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨862,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨863,by decide⟩] | 5 => ![⟨843,by decide⟩,⟨843,by decide⟩,⟨843,by decide⟩] | 6 => ![⟨843,by decide⟩,⟨843,by decide⟩,⟨864,by decide⟩] | _ => ![⟨865,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRRRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRLRLL i else ntree14LRRRLRLR (i - 8)

def ntree14LRRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨866,by decide⟩,⟨35,by decide⟩,⟨827,by decide⟩] | 1 => ![⟨865,by decide⟩,⟨867,by decide⟩,⟨24,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨868,by decide⟩] | 3 => ![⟨869,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨870,by decide⟩,⟨32,by decide⟩,⟨837,by decide⟩] | 5 => ![⟨871,by decide⟩,⟨843,by decide⟩,⟨871,by decide⟩] | 6 => ![⟨872,by decide⟩,⟨820,by decide⟩,⟨838,by decide⟩] | _ => ![⟨0,by decide⟩,⟨873,by decide⟩,⟨873,by decide⟩]

def ntree14LRRRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨30,by decide⟩,⟨874,by decide⟩,⟨873,by decide⟩] | 1 => ![⟨838,by decide⟩,⟨23,by decide⟩,⟨838,by decide⟩] | 2 => ![⟨875,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨876,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRRRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨875,by decide⟩,⟨877,by decide⟩,⟨24,by decide⟩] | 1 => ![⟨878,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨879,by decide⟩,⟨30,by decide⟩,⟨880,by decide⟩] | 3 => ![⟨880,by decide⟩,⟨0,by decide⟩,⟨880,by decide⟩] | _ => ![⟨881,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRRRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRRRLRRRL i else ntree14LRRRLRRRR (i - 4)

def ntree14LRRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRLRRL i else ntree14LRRRLRRR (i - 8)

def ntree14LRRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRRLRL i else ntree14LRRRLRR (i - 16)

def ntree14LRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LRRRLL i else ntree14LRRRLR (i - 32)

def ntree14LRRRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨881,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨882,by decide⟩,⟨883,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨884,by decide⟩,⟨884,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨884,by decide⟩,⟨885,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨886,by decide⟩,⟨886,by decide⟩,⟨886,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨0,by decide⟩]

def ntree14LRRRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨887,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨888,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨889,by decide⟩,⟨889,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨889,by decide⟩,⟨890,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨891,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨892,by decide⟩] | 6 => ![⟨893,by decide⟩,⟨882,by decide⟩,⟨827,by decide⟩] | _ => ![⟨894,by decide⟩,⟨886,by decide⟩,⟨894,by decide⟩]

def ntree14LRRRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRRLLL i else ntree14LRRRRLLR (i - 8)

def ntree14LRRRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨895,by decide⟩,⟨0,by decide⟩,⟨895,by decide⟩] | 1 => ![⟨896,by decide⟩,⟨0,by decide⟩,⟨896,by decide⟩] | 2 => ![⟨897,by decide⟩,⟨0,by decide⟩,⟨897,by decide⟩] | 3 => ![⟨898,by decide⟩,⟨0,by decide⟩,⟨898,by decide⟩] | 4 => ![⟨898,by decide⟩,⟨1,by decide⟩,⟨899,by decide⟩] | 5 => ![⟨900,by decide⟩,⟨2,by decide⟩,⟨900,by decide⟩] | 6 => ![⟨900,by decide⟩,⟨3,by decide⟩,⟨901,by decide⟩] | _ => ![⟨902,by decide⟩,⟨30,by decide⟩,⟨898,by decide⟩]

def ntree14LRRRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨902,by decide⟩,⟨31,by decide⟩,⟨899,by decide⟩] | 1 => ![⟨903,by decide⟩,⟨0,by decide⟩,⟨903,by decide⟩] | 2 => ![⟨903,by decide⟩,⟨1,by decide⟩,⟨904,by decide⟩] | _ => ![⟨843,by decide⟩,⟨844,by decide⟩,⟨844,by decide⟩]

def ntree14LRRRRLRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨905,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨906,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨905,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨907,by decide⟩] | _ => ![⟨908,by decide⟩,⟨63,by decide⟩,⟨903,by decide⟩]

def ntree14LRRRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRRRRLRRL i else ntree14LRRRRLRRR (i - 4)

def ntree14LRRRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRRLRL i else ntree14LRRRRLRR (i - 8)

def ntree14LRRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRRRLL i else ntree14LRRRRLR (i - 16)

def ntree14LRRRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨909,by decide⟩,⟨909,by decide⟩,⟨910,by decide⟩] | 1 => ![⟨909,by decide⟩,⟨911,by decide⟩,⟨912,by decide⟩] | 2 => ![⟨913,by decide⟩,⟨882,by decide⟩,⟨903,by decide⟩] | 3 => ![⟨910,by decide⟩,⟨910,by decide⟩,⟨910,by decide⟩] | 4 => ![⟨910,by decide⟩,⟨912,by decide⟩,⟨912,by decide⟩] | 5 => ![⟨914,by decide⟩,⟨914,by decide⟩,⟨886,by decide⟩] | 6 => ![⟨915,by decide⟩,⟨915,by decide⟩,⟨0,by decide⟩] | _ => ![⟨916,by decide⟩,⟨916,by decide⟩,⟨843,by decide⟩]

def ntree14LRRRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨30,by decide⟩,⟨917,by decide⟩,⟨918,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨918,by decide⟩,⟨918,by decide⟩] | 2 => ![⟨919,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨920,by decide⟩,⟨882,by decide⟩,⟨84,by decide⟩] | 5 => ![⟨921,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨922,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨923,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRRRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRRRLL i else ntree14LRRRRRLR (i - 8)

def ntree14LRRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨924,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨925,by decide⟩,⟨882,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨926,by decide⟩,⟨884,by decide⟩,⟨6,by decide⟩] | 3 => ![⟨927,by decide⟩,⟨886,by decide⟩,⟨927,by decide⟩] | 4 => ![⟨928,by decide⟩,⟨0,by decide⟩,⟨928,by decide⟩] | 5 => ![⟨923,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨822,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨925,by decide⟩,⟨929,by decide⟩,⟨4,by decide⟩]

def ntree14LRRRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨923,by decide⟩,⟨824,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨882,by decide⟩,⟨929,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨930,by decide⟩,⟨882,by decide⟩,⟨928,by decide⟩] | _ => ![⟨931,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LRRRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨932,by decide⟩,⟨889,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨933,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨934,by decide⟩,⟨935,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨936,by decide⟩,⟨937,by decide⟩] | _ => ![⟨882,by decide⟩,⟨938,by decide⟩,⟨937,by decide⟩]

def ntree14LRRRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LRRRRRRRL i else ntree14LRRRRRRRR (i - 4)

def ntree14LRRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LRRRRRRL i else ntree14LRRRRRRR (i - 8)

def ntree14LRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LRRRRRL i else ntree14LRRRRRR (i - 16)

def ntree14LRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 33 then ntree14LRRRRL i else ntree14LRRRRR (i - 33)

def ntree14LRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LRRRL i else ntree14LRRRR (i - 65)

def ntree14LRR (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14LRRL i else ntree14LRRR (i - 130)

def ntree14LR (i : Nat) : Fin 3 → Fin 1937 := if i < 260 then ntree14LRL i else ntree14LRR (i - 260)

def ntree14L (i : Nat) : Fin 3 → Fin 1937 := if i < 521 then ntree14LL i else ntree14LR (i - 521)

def ntree14RLLLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨939,by decide⟩,⟨940,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨939,by decide⟩,⟨939,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨941,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨942,by decide⟩,⟨943,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨942,by decide⟩,⟨942,by decide⟩] | 5 => ![⟨838,by decide⟩,⟨0,by decide⟩,⟨838,by decide⟩] | 6 => ![⟨838,by decide⟩,⟨0,by decide⟩,⟨944,by decide⟩] | _ => ![⟨846,by decide⟩,⟨30,by decide⟩,⟨944,by decide⟩]

def ntree14RLLLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨822,by decide⟩,⟨0,by decide⟩,⟨905,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨877,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨945,by decide⟩,⟨910,by decide⟩,⟨945,by decide⟩] | 3 => ![⟨946,by decide⟩,⟨915,by decide⟩,⟨838,by decide⟩] | 4 => ![⟨947,by decide⟩,⟨914,by decide⟩,⟨927,by decide⟩] | 5 => ![⟨948,by decide⟩,⟨916,by decide⟩,⟨842,by decide⟩] | 6 => ![⟨949,by decide⟩,⟨909,by decide⟩,⟨945,by decide⟩] | _ => ![⟨0,by decide⟩,⟨877,by decide⟩,⟨0,by decide⟩]

def ntree14RLLLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLLLLL i else ntree14RLLLLLLR (i - 8)

def ntree14RLLLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨950,by decide⟩,⟨950,by decide⟩] | 1 => ![⟨951,by decide⟩,⟨952,by decide⟩,⟨952,by decide⟩] | 2 => ![⟨951,by decide⟩,⟨951,by decide⟩,⟨951,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨953,by decide⟩,⟨953,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨954,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨955,by decide⟩,⟨0,by decide⟩] | _ => ![⟨956,by decide⟩,⟨957,by decide⟩,⟨1,by decide⟩]

def ntree14RLLLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨816,by decide⟩,⟨816,by decide⟩,⟨121,by decide⟩] | 1 => ![⟨958,by decide⟩,⟨817,by decide⟩,⟨123,by decide⟩] | 2 => ![⟨959,by decide⟩,⟨960,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨961,by decide⟩,⟨960,by decide⟩,⟨122,by decide⟩] | 4 => ![⟨122,by decide⟩,⟨824,by decide⟩,⟨122,by decide⟩] | 5 => ![⟨822,by decide⟩,⟨128,by decide⟩,⟨128,by decide⟩] | 6 => ![⟨827,by decide⟩,⟨950,by decide⟩,⟨962,by decide⟩] | _ => ![⟨963,by decide⟩,⟨952,by decide⟩,⟨964,by decide⟩]

def ntree14RLLLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLLLRL i else ntree14RLLLLLRR (i - 8)

def ntree14RLLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLLLLL i else ntree14RLLLLLR (i - 16)

def ntree14RLLLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨963,by decide⟩,⟨951,by decide⟩,⟨963,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨824,by decide⟩,⟨121,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨958,by decide⟩,⟨816,by decide⟩,⟨122,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨827,by decide⟩,⟨135,by decide⟩,⟨965,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RLLLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨966,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨967,by decide⟩,⟨967,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨966,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨838,by decide⟩,⟨149,by decide⟩,⟨838,by decide⟩] | 4 => ![⟨838,by decide⟩,⟨128,by decide⟩,⟨968,by decide⟩] | 5 => ![⟨846,by decide⟩,⟨151,by decide⟩,⟨968,by decide⟩] | 6 => ![⟨822,by decide⟩,⟨149,by decide⟩,⟨0,by decide⟩] | _ => ![⟨827,by decide⟩,⟨149,by decide⟩,⟨827,by decide⟩]

def ntree14RLLLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLLRLL i else ntree14RLLLLRLR (i - 8)

def ntree14RLLLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨969,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨970,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨971,by decide⟩,⟨972,by decide⟩] | 3 => ![⟨973,by decide⟩,⟨974,by decide⟩,⟨975,by decide⟩] | 4 => ![⟨838,by decide⟩,⟨976,by decide⟩,⟨977,by decide⟩] | 5 => ![⟨978,by decide⟩,⟨979,by decide⟩,⟨980,by decide⟩] | 6 => ![⟨981,by decide⟩,⟨960,by decide⟩,⟨838,by decide⟩] | _ => ![⟨982,by decide⟩,⟨983,by decide⟩,⟨984,by decide⟩]

def ntree14RLLLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨976,by decide⟩,⟨985,by decide⟩] | 1 => ![⟨122,by decide⟩,⟨976,by decide⟩,⟨986,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨987,by decide⟩,⟨987,by decide⟩]

def ntree14RLLLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨988,by decide⟩,⟨989,by decide⟩,⟨989,by decide⟩] | 1 => ![⟨988,by decide⟩,⟨988,by decide⟩,⟨988,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨990,by decide⟩] | 3 => ![⟨991,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨992,by decide⟩,⟨889,by decide⟩,⟨122,by decide⟩]

def ntree14RLLLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLLLLRRRL i else ntree14RLLLLRRRR (i - 4)

def ntree14RLLLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLLRRL i else ntree14RLLLLRRR (i - 8)

def ntree14RLLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLLLRL i else ntree14RLLLLRR (i - 16)

def ntree14RLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RLLLLL i else ntree14RLLLLR (i - 32)

def ntree14RLLLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨993,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨994,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨995,by decide⟩,⟨169,by decide⟩,⟨827,by decide⟩] | 3 => ![⟨996,by decide⟩,⟨988,by decide⟩,⟨996,by decide⟩] | 4 => ![⟨997,by decide⟩,⟨997,by decide⟩,⟨988,by decide⟩] | 5 => ![⟨998,by decide⟩,⟨998,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨999,by decide⟩] | _ => ![⟨1000,by decide⟩,⟨1,by decide⟩,⟨1001,by decide⟩]

def ntree14RLLLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1000,by decide⟩,⟨0,by decide⟩,⟨1000,by decide⟩] | 1 => ![⟨1002,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1003,by decide⟩,⟨30,by decide⟩,⟨1000,by decide⟩] | 3 => ![⟨827,by decide⟩,⟨178,by decide⟩,⟨1004,by decide⟩] | 4 => ![⟨1005,by decide⟩,⟨180,by decide⟩,⟨1006,by decide⟩] | 5 => ![⟨1005,by decide⟩,⟨179,by decide⟩,⟨1005,by decide⟩] | 6 => ![⟨1007,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | _ => ![⟨1008,by decide⟩,⟨186,by decide⟩,⟨1005,by decide⟩]

def ntree14RLLLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLRLLL i else ntree14RLLLRLLR (i - 8)

def ntree14RLLLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1009,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨990,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨0,by decide⟩,⟨1010,by decide⟩] | 4 => ![⟨122,by decide⟩,⟨0,by decide⟩,⟨122,by decide⟩] | 5 => ![⟨1011,by decide⟩,⟨889,by decide⟩,⟨109,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1012,by decide⟩,⟨1012,by decide⟩] | _ => ![⟨886,by decide⟩,⟨1013,by decide⟩,⟨1013,by decide⟩]

def ntree14RLLLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨923,by decide⟩,⟨953,by decide⟩,⟨953,by decide⟩] | 1 => ![⟨822,by decide⟩,⟨1012,by decide⟩,⟨1012,by decide⟩] | 2 => ![⟨109,by decide⟩,⟨1012,by decide⟩,⟨1014,by decide⟩] | 3 => ![⟨1015,by decide⟩,⟨0,by decide⟩,⟨1015,by decide⟩] | 4 => ![⟨169,by decide⟩,⟨1016,by decide⟩,⟨1012,by decide⟩] | 5 => ![⟨1017,by decide⟩,⟨169,by decide⟩,⟨1015,by decide⟩] | 6 => ![⟨218,by decide⟩,⟨1012,by decide⟩,⟨1018,by decide⟩] | _ => ![⟨63,by decide⟩,⟨1019,by decide⟩,⟨1012,by decide⟩]

def ntree14RLLLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLRLRL i else ntree14RLLLRLRR (i - 8)

def ntree14RLLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLLRLL i else ntree14RLLLRLR (i - 16)

def ntree14RLLLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨951,by decide⟩,⟨951,by decide⟩,⟨1020,by decide⟩] | 1 => ![⟨886,by decide⟩,⟨1021,by decide⟩,⟨1021,by decide⟩] | 2 => ![⟨988,by decide⟩,⟨1022,by decide⟩,⟨988,by decide⟩] | 3 => ![⟨1023,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1024,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 5 => ![⟨1025,by decide⟩,⟨30,by decide⟩,⟨1015,by decide⟩] | 6 => ![⟨1026,by decide⟩,⟨988,by decide⟩,⟨1026,by decide⟩] | _ => ![⟨1027,by decide⟩,⟨179,by decide⟩,⟨1027,by decide⟩]

def ntree14RLLLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1028,by decide⟩,⟨186,by decide⟩,⟨1027,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1029,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1030,by decide⟩] | 3 => ![⟨838,by decide⟩,⟨222,by decide⟩,⟨1031,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1032,by decide⟩] | 5 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1033,by decide⟩] | 6 => ![⟨1034,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | _ => ![⟨838,by decide⟩,⟨0,by decide⟩,⟨838,by decide⟩]

def ntree14RLLLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLRRLL i else ntree14RLLLRRLR (i - 8)

def ntree14RLLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1035,by decide⟩,⟨0,by decide⟩,⟨838,by decide⟩] | 1 => ![⟨1036,by decide⟩,⟨951,by decide⟩,⟨1036,by decide⟩] | 2 => ![⟨1037,by decide⟩,⟨0,by decide⟩,⟨1037,by decide⟩] | 3 => ![⟨1038,by decide⟩,⟨1039,by decide⟩,⟨1038,by decide⟩] | 4 => ![⟨1040,by decide⟩,⟨254,by decide⟩,⟨1040,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1041,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨2,by decide⟩,⟨1042,by decide⟩,⟨2,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1043,by decide⟩,⟨0,by decide⟩]

def ntree14RLLLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨1044,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨1045,by decide⟩,⟨1046,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1047,by decide⟩,⟨0,by decide⟩] | _ => ![⟨4,by decide⟩,⟨1047,by decide⟩,⟨4,by decide⟩]

def ntree14RLLLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨35,by decide⟩,⟨1048,by decide⟩,⟨953,by decide⟩] | 1 => ![⟨827,by decide⟩,⟨1047,by decide⟩,⟨827,by decide⟩] | 2 => ![⟨829,by decide⟩,⟨1049,by decide⟩,⟨829,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1050,by decide⟩,⟨1050,by decide⟩,⟨0,by decide⟩]

def ntree14RLLLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLLLRRRRL i else ntree14RLLLRRRRR (i - 4)

def ntree14RLLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLLRRRL i else ntree14RLLLRRRR (i - 8)

def ntree14RLLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLLRRL i else ntree14RLLLRRR (i - 16)

def ntree14RLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RLLLRL i else ntree14RLLLRR (i - 32)

def ntree14RLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RLLLL i else ntree14RLLLR (i - 65)

def ntree14RLLRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1051,by decide⟩,⟨1050,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨122,by decide⟩,⟨1047,by decide⟩,⟨122,by decide⟩] | 2 => ![⟨1052,by decide⟩,⟨1050,by decide⟩,⟨122,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1053,by decide⟩,⟨0,by decide⟩,⟨1053,by decide⟩] | 5 => ![⟨1054,by decide⟩,⟨1054,by decide⟩,⟨951,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1055,by decide⟩] | _ => ![⟨122,by decide⟩,⟨0,by decide⟩,⟨122,by decide⟩]

def ntree14RLLRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1056,by decide⟩,⟨882,by decide⟩,⟨122,by decide⟩] | 1 => ![⟨1057,by decide⟩,⟨882,by decide⟩,⟨263,by decide⟩] | 2 => ![⟨1058,by decide⟩,⟨884,by decide⟩,⟨264,by decide⟩] | 3 => ![⟨1059,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨1060,by decide⟩,⟨128,by decide⟩] | 5 => ![⟨1061,by decide⟩,⟨1054,by decide⟩,⟨963,by decide⟩] | 6 => ![⟨1062,by decide⟩,⟨882,by decide⟩,⟨122,by decide⟩] | _ => ![⟨1063,by decide⟩,⟨287,by decide⟩,⟨827,by decide⟩]

def ntree14RLLRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRLLLL i else ntree14RLLRLLLR (i - 8)

def ntree14RLLRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1064,by decide⟩,⟨288,by decide⟩,⟨827,by decide⟩] | 1 => ![⟨1065,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨1066,by decide⟩,⟨289,by decide⟩,⟨837,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1045,by decide⟩,⟨1045,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1067,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1068,by decide⟩,⟨0,by decide⟩,⟨1068,by decide⟩] | 6 => ![⟨1069,by decide⟩,⟨2,by decide⟩,⟨1069,by decide⟩] | _ => ![⟨1070,by decide⟩,⟨30,by decide⟩,⟨1068,by decide⟩]

def ntree14RLLRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1071,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨1072,by decide⟩,⟨32,by decide⟩,⟨1069,by decide⟩] | 2 => ![⟨1073,by decide⟩,⟨297,by decide⟩,⟨827,by decide⟩] | 3 => ![⟨1074,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 4 => ![⟨1075,by decide⟩,⟨298,by decide⟩,⟨1005,by decide⟩] | 5 => ![⟨1076,by decide⟩,⟨299,by decide⟩,⟨1076,by decide⟩] | 6 => ![⟨1077,by decide⟩,⟨300,by decide⟩,⟨1077,by decide⟩] | _ => ![⟨1078,by decide⟩,⟨301,by decide⟩,⟨1076,by decide⟩]

def ntree14RLLRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRLLRL i else ntree14RLLRLLRR (i - 8)

def ntree14RLLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLRLLL i else ntree14RLLRLLR (i - 16)

def ntree14RLLRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1079,by decide⟩,⟨300,by decide⟩,⟨300,by decide⟩] | 1 => ![⟨1080,by decide⟩,⟨302,by decide⟩,⟨1077,by decide⟩] | 2 => ![⟨1009,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1081,by decide⟩,⟨1081,by decide⟩,⟨179,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1082,by decide⟩,⟨0,by decide⟩,⟨1082,by decide⟩] | 6 => ![⟨1083,by decide⟩,⟨0,by decide⟩,⟨1083,by decide⟩] | _ => ![⟨1084,by decide⟩,⟨910,by decide⟩,⟨1084,by decide⟩]

def ntree14RLLRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1085,by decide⟩,⟨882,by decide⟩,⟨1082,by decide⟩] | 1 => ![⟨1086,by decide⟩,⟨909,by decide⟩,⟨1084,by decide⟩] | 2 => ![⟨1087,by decide⟩,⟨882,by decide⟩,⟨122,by decide⟩] | 3 => ![⟨1088,by decide⟩,⟨30,by decide⟩,⟨1083,by decide⟩] | 4 => ![⟨1089,by decide⟩,⟨882,by decide⟩,⟨122,by decide⟩] | 5 => ![⟨1090,by decide⟩,⟨1081,by decide⟩,⟨209,by decide⟩] | 6 => ![⟨1091,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | _ => ![⟨1092,by decide⟩,⟨0,by decide⟩,⟨1092,by decide⟩]

def ntree14RLLRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRLRLL i else ntree14RLLRLRLR (i - 8)

def ntree14RLLRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1093,by decide⟩,⟨179,by decide⟩,⟨1093,by decide⟩] | 1 => ![⟨1094,by decide⟩,⟨30,by decide⟩,⟨1092,by decide⟩] | 2 => ![⟨1095,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 3 => ![⟨1096,by decide⟩,⟨186,by decide⟩,⟨1093,by decide⟩] | 4 => ![⟨4,by decide⟩,⟨222,by decide⟩,⟨1097,by decide⟩] | 5 => ![⟨882,by decide⟩,⟨1098,by decide⟩,⟨222,by decide⟩] | 6 => ![⟨314,by decide⟩,⟨953,by decide⟩,⟨1099,by decide⟩] | _ => ![⟨1100,by decide⟩,⟨1050,by decide⟩,⟨314,by decide⟩]

def ntree14RLLRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1101,by decide⟩,⟨1081,by decide⟩,⟨317,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1102,by decide⟩,⟨882,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1103,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RLLRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1104,by decide⟩] | 1 => ![⟨1105,by decide⟩,⟨1,by decide⟩,⟨1106,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨1107,by decide⟩,⟨1108,by decide⟩] | 3 => ![⟨1109,by decide⟩,⟨1110,by decide⟩,⟨1111,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1112,by decide⟩,⟨0,by decide⟩]

def ntree14RLLRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLLRLRRRL i else ntree14RLLRLRRRR (i - 4)

def ntree14RLLRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRLRRL i else ntree14RLLRLRRR (i - 8)

def ntree14RLLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLRLRL i else ntree14RLLRLRR (i - 16)

def ntree14RLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RLLRLL i else ntree14RLLRLR (i - 32)

def ntree14RLLRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨827,by decide⟩,⟨345,by decide⟩,⟨1113,by decide⟩] | 1 => ![⟨1114,by decide⟩,⟨347,by decide⟩,⟨1115,by decide⟩] | 2 => ![⟨829,by decide⟩,⟨1116,by decide⟩,⟨1117,by decide⟩] | 3 => ![⟨1118,by decide⟩,⟨1119,by decide⟩,⟨1120,by decide⟩] | 4 => ![⟨1121,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1122,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1121,by decide⟩,⟨1122,by decide⟩,⟨24,by decide⟩] | _ => ![⟨1123,by decide⟩,⟨1124,by decide⟩,⟨1125,by decide⟩]

def ntree14RLLRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1126,by decide⟩,⟨30,by decide⟩,⟨848,by decide⟩] | 1 => ![⟨1127,by decide⟩,⟨0,by decide⟩,⟨1127,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1128,by decide⟩,⟨1128,by decide⟩] | 3 => ![⟨1127,by decide⟩,⟨1128,by decide⟩,⟨1129,by decide⟩] | 4 => ![⟨1130,by decide⟩,⟨338,by decide⟩,⟨1127,by decide⟩] | 5 => ![⟨30,by decide⟩,⟨1131,by decide⟩,⟨375,by decide⟩] | 6 => ![⟨820,by decide⟩,⟨1132,by decide⟩,⟨1128,by decide⟩] | _ => ![⟨882,by decide⟩,⟨1133,by decide⟩,⟨1134,by decide⟩]

def ntree14RLLRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRRLLL i else ntree14RLLRRLLR (i - 8)

def ntree14RLLRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1135,by decide⟩,⟨1136,by decide⟩,⟨1137,by decide⟩] | 1 => ![⟨1138,by decide⟩,⟨882,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1139,by decide⟩,⟨1134,by decide⟩] | 3 => ![⟨402,by decide⟩,⟨1140,by decide⟩,⟨1134,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨827,by decide⟩,⟨1141,by decide⟩,⟨1142,by decide⟩] | 6 => ![⟨1143,by decide⟩,⟨1144,by decide⟩,⟨1145,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RLLRRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1146,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1147,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1148,by decide⟩,⟨882,by decide⟩,⟨420,by decide⟩] | 3 => ![⟨1149,by decide⟩,⟨402,by decide⟩,⟨827,by decide⟩] | 4 => ![⟨1150,by decide⟩,⟨1151,by decide⟩,⟨1152,by decide⟩] | 5 => ![⟨827,by decide⟩,⟨1147,by decide⟩,⟨827,by decide⟩] | 6 => ![⟨898,by decide⟩,⟨401,by decide⟩,⟨898,by decide⟩] | _ => ![⟨1153,by decide⟩,⟨403,by decide⟩,⟨899,by decide⟩]

def ntree14RLLRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRRLRL i else ntree14RLLRRLRR (i - 8)

def ntree14RLLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLRRLL i else ntree14RLLRRLR (i - 16)

def ntree14RLLRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨1154,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1155,by decide⟩,⟨1156,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨401,by decide⟩,⟨905,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1157,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1158,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1153,by decide⟩,⟨402,by decide⟩,⟨898,by decide⟩] | 6 => ![⟨1155,by decide⟩,⟨1155,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1159,by decide⟩,⟨30,by decide⟩,⟨1160,by decide⟩]

def ntree14RLLRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨905,by decide⟩] | 1 => ![⟨1161,by decide⟩,⟨432,by decide⟩,⟨1162,by decide⟩] | 2 => ![⟨1163,by decide⟩,⟨433,by decide⟩,⟨433,by decide⟩] | 3 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨436,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨1164,by decide⟩,⟨375,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1165,by decide⟩,⟨402,by decide⟩,⟨1166,by decide⟩]

def ntree14RLLRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRRRLL i else ntree14RLLRRRLR (i - 8)

def ntree14RLLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1167,by decide⟩,⟨0,by decide⟩,⟨1166,by decide⟩] | 1 => ![⟨1168,by decide⟩,⟨1169,by decide⟩,⟨1170,by decide⟩] | 2 => ![⟨1171,by decide⟩,⟨882,by decide⟩,⟨1166,by decide⟩] | 3 => ![⟨402,by decide⟩,⟨1172,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1173,by decide⟩,⟨345,by decide⟩,⟨1174,by decide⟩] | 5 => ![⟨1175,by decide⟩,⟨1176,by decide⟩,⟨1177,by decide⟩] | 6 => ![⟨1178,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1178,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩]

def ntree14RLLRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨1179,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨882,by decide⟩,⟨1180,by decide⟩,⟨345,by decide⟩] | 2 => ![⟨402,by decide⟩,⟨1181,by decide⟩,⟨937,by decide⟩] | _ => ![⟨1182,by decide⟩,⟨1183,by decide⟩,⟨1184,by decide⟩]

def ntree14RLLRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1185,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1186,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1187,by decide⟩,⟨402,by decide⟩,⟨848,by decide⟩] | 3 => ![⟨1188,by decide⟩,⟨1155,by decide⟩,⟨4,by decide⟩] | _ => ![⟨1189,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RLLRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLLRRRRRL i else ntree14RLLRRRRRR (i - 4)

def ntree14RLLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLLRRRRL i else ntree14RLLRRRRR (i - 8)

def ntree14RLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLLRRRL i else ntree14RLLRRRR (i - 16)

def ntree14RLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RLLRRL i else ntree14RLLRRR (i - 32)

def ntree14RLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RLLRL i else ntree14RLLRR (i - 65)

def ntree14RLL (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14RLLL i else ntree14RLLR (i - 130)

def ntree14RLRLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨1190,by decide⟩,⟨1191,by decide⟩] | 3 => ![⟨923,by decide⟩,⟨462,by decide⟩,⟨462,by decide⟩] | 4 => ![⟨925,by decide⟩,⟨1192,by decide⟩,⟨463,by decide⟩] | 5 => ![⟨923,by decide⟩,⟨0,by decide⟩,⟨436,by decide⟩] | 6 => ![⟨882,by decide⟩,⟨1192,by decide⟩,⟨462,by decide⟩] | _ => ![⟨909,by decide⟩,⟨1193,by decide⟩,⟨1194,by decide⟩]

def ntree14RLRLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨910,by decide⟩,⟨1195,by decide⟩,⟨910,by decide⟩] | 1 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1196,by decide⟩,⟨1197,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1198,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨338,by decide⟩,⟨1199,by decide⟩,⟨953,by decide⟩] | 5 => ![⟨470,by decide⟩,⟨953,by decide⟩,⟨1200,by decide⟩] | 6 => ![⟨1196,by decide⟩,⟨1201,by decide⟩,⟨345,by decide⟩] | _ => ![⟨1202,by decide⟩,⟨1203,by decide⟩,⟨347,by decide⟩]

def ntree14RLRLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLLLLL i else ntree14RLRLLLLR (i - 8)

def ntree14RLRLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1204,by decide⟩,⟨1205,by decide⟩,⟨345,by decide⟩] | 1 => ![⟨1206,by decide⟩,⟨1196,by decide⟩,⟨827,by decide⟩] | 2 => ![⟨1196,by decide⟩,⟨1207,by decide⟩,⟨135,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1208,by decide⟩,⟨1208,by decide⟩] | 4 => ![⟨1209,by decide⟩,⟨1209,by decide⟩,⟨1210,by decide⟩] | 5 => ![⟨1209,by decide⟩,⟨1211,by decide⟩,⟨1212,by decide⟩] | 6 => ![⟨30,by decide⟩,⟨1213,by decide⟩,⟨1214,by decide⟩] | _ => ![⟨1215,by decide⟩,⟨1209,by decide⟩,⟨1216,by decide⟩]

def ntree14RLRLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1217,by decide⟩,⟨1196,by decide⟩,⟨1218,by decide⟩] | 1 => ![⟨1219,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1220,by decide⟩,⟨483,by decide⟩,⟨827,by decide⟩] | 3 => ![⟨1209,by decide⟩,⟨1221,by decide⟩,⟨1222,by decide⟩] | 4 => ![⟨1223,by decide⟩,⟨1224,by decide⟩,⟨1225,by decide⟩] | 5 => ![⟨1196,by decide⟩,⟨1226,by decide⟩,⟨1227,by decide⟩] | 6 => ![⟨1228,by decide⟩,⟨1229,by decide⟩,⟨1230,by decide⟩] | _ => ![⟨1231,by decide⟩,⟨1232,by decide⟩,⟨1233,by decide⟩]

def ntree14RLRLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLLLRL i else ntree14RLRLLLRR (i - 8)

def ntree14RLRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRLLLL i else ntree14RLRLLLR (i - 16)

def ntree14RLRLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1196,by decide⟩,⟨1234,by decide⟩,⟨987,by decide⟩] | 1 => ![⟨1235,by decide⟩,⟨1236,by decide⟩,⟨989,by decide⟩] | 2 => ![⟨988,by decide⟩,⟨1237,by decide⟩,⟨988,by decide⟩] | 3 => ![⟨1235,by decide⟩,⟨1235,by decide⟩,⟨988,by decide⟩] | 4 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨990,by decide⟩] | 5 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨990,by decide⟩] | 6 => ![⟨402,by decide⟩,⟨1238,by decide⟩,⟨1208,by decide⟩] | _ => ![⟨1196,by decide⟩,⟨1239,by decide⟩,⟨178,by decide⟩]

def ntree14RLRLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1240,by decide⟩,⟨1241,by decide⟩,⟨180,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1242,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨179,by decide⟩,⟨1243,by decide⟩,⟨179,by decide⟩] | 3 => ![⟨1244,by decide⟩,⟨1244,by decide⟩,⟨1245,by decide⟩] | 4 => ![⟨1246,by decide⟩,⟨1246,by decide⟩,⟨433,by decide⟩] | 5 => ![⟨1240,by decide⟩,⟨1240,by decide⟩,⟨179,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1247,by decide⟩,⟨483,by decide⟩,⟨1000,by decide⟩]

def ntree14RLRLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLLRLL i else ntree14RLRLLRLR (i - 8)

def ntree14RLRLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1248,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 1 => ![⟨1249,by decide⟩,⟨501,by decide⟩,⟨1005,by decide⟩] | 2 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨436,by decide⟩] | 3 => ![⟨1209,by decide⟩,⟨1209,by decide⟩,⟨1250,by decide⟩] | 4 => ![⟨1251,by decide⟩,⟨1196,by decide⟩,⟨506,by decide⟩] | 5 => ![⟨1252,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RLRLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1196,by decide⟩,⟨1253,by decide⟩,⟨1254,by decide⟩] | 2 => ![⟨1235,by decide⟩,⟨1255,by decide⟩,⟨1256,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1254,by decide⟩,⟨1254,by decide⟩]

def ntree14RLRLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨988,by decide⟩,⟨1256,by decide⟩,⟨1256,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1122,by decide⟩,⟨990,by decide⟩] | 2 => ![⟨1257,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1258,by decide⟩,⟨402,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1257,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩]

def ntree14RLRLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLRLLRRRL i else ntree14RLRLLRRRR (i - 4)

def ntree14RLRLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLLRRL i else ntree14RLRLLRRR (i - 8)

def ntree14RLRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRLLRL i else ntree14RLRLLRR (i - 16)

def ntree14RLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RLRLLL i else ntree14RLRLLR (i - 32)

def ntree14RLRLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1127,by decide⟩,⟨542,by decide⟩,⟨1259,by decide⟩] | 1 => ![⟨1260,by decide⟩,⟨1196,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨1261,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1262,by decide⟩,⟨820,by decide⟩,⟨470,by decide⟩] | 4 => ![⟨1263,by decide⟩,⟨1264,by decide⟩,⟨829,by decide⟩] | 5 => ![⟨1265,by decide⟩,⟨1266,by decide⟩,⟨827,by decide⟩] | 6 => ![⟨1267,by decide⟩,⟨1196,by decide⟩,⟨263,by decide⟩] | _ => ![⟨1268,by decide⟩,⟨0,by decide⟩,⟨1268,by decide⟩]

def ntree14RLRLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1269,by decide⟩,⟨1209,by decide⟩,⟨1270,by decide⟩] | 1 => ![⟨1271,by decide⟩,⟨30,by decide⟩,⟨1272,by decide⟩] | 2 => ![⟨1273,by decide⟩,⟨1274,by decide⟩,⟨1275,by decide⟩] | 3 => ![⟨1276,by decide⟩,⟨1277,by decide⟩,⟨1278,by decide⟩] | 4 => ![⟨1279,by decide⟩,⟨1280,by decide⟩,⟨1281,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1282,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1050,by decide⟩,⟨1283,by decide⟩,⟨345,by decide⟩] | _ => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨587,by decide⟩]

def ntree14RLRLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLRLLL i else ntree14RLRLRLLR (i - 8)

def ntree14RLRLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1284,by decide⟩,⟨1284,by decide⟩,⟨588,by decide⟩] | 1 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨587,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1285,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1121,by decide⟩,⟨0,by decide⟩,⟨587,by decide⟩] | _ => ![⟨1286,by decide⟩,⟨1284,by decide⟩,⟨1287,by decide⟩]

def ntree14RLRLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1288,by decide⟩,⟨1196,by decide⟩,⟨1289,by decide⟩] | 1 => ![⟨1287,by decide⟩,⟨588,by decide⟩,⟨1287,by decide⟩] | 2 => ![⟨1289,by decide⟩,⟨0,by decide⟩,⟨1289,by decide⟩] | 3 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨905,by decide⟩] | 4 => ![⟨1209,by decide⟩,⟨1209,by decide⟩,⟨1290,by decide⟩] | 5 => ![⟨1000,by decide⟩,⟨1128,by decide⟩,⟨1291,by decide⟩] | 6 => ![⟨827,by decide⟩,⟨1292,by decide⟩,⟨827,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1292,by decide⟩,⟨0,by decide⟩]

def ntree14RLRLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLRLRL i else ntree14RLRLRLRR (i - 8)

def ntree14RLRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRLRLL i else ntree14RLRLRLR (i - 16)

def ntree14RLRLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1293,by decide⟩,⟨1293,by decide⟩,⟨1294,by decide⟩] | 1 => ![⟨1295,by decide⟩,⟨1295,by decide⟩,⟨910,by decide⟩] | 2 => ![⟨882,by decide⟩,⟨1296,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1297,by decide⟩,⟨1284,by decide⟩,⟨615,by decide⟩] | 4 => ![⟨1298,by decide⟩,⟨588,by decide⟩,⟨588,by decide⟩] | 5 => ![⟨1299,by decide⟩,⟨882,by decide⟩,⟨1268,by decide⟩] | 6 => ![⟨1300,by decide⟩,⟨1196,by decide⟩,⟨314,by decide⟩] | _ => ![⟨1301,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RLRLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1302,by decide⟩,⟨1240,by decide⟩,⟨317,by decide⟩] | 1 => ![⟨1303,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 2 => ![⟨179,by decide⟩,⟨1304,by decide⟩,⟨179,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1050,by decide⟩,⟨1305,by decide⟩,⟨542,by decide⟩] | 5 => ![⟨1081,by decide⟩,⟨1306,by decide⟩,⟨543,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1307,by decide⟩] | _ => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1308,by decide⟩]

def ntree14RLRLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLRRLL i else ntree14RLRLRRLR (i - 8)

def ntree14RLRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1309,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1310,by decide⟩,⟨1311,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨1312,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1312,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩] | 4 => ![⟨1313,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 5 => ![⟨827,by decide⟩,⟨628,by decide⟩,⟨1314,by decide⟩] | 6 => ![⟨837,by decide⟩,⟨629,by decide⟩,⟨1315,by decide⟩] | _ => ![⟨1316,by decide⟩,⟨0,by decide⟩,⟨838,by decide⟩]

def ntree14RLRLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1317,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RLRLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1318,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1319,by decide⟩] | 2 => ![⟨838,by decide⟩,⟨375,by decide⟩,⟨1320,by decide⟩] | 3 => ![⟨1321,by decide⟩,⟨656,by decide⟩,⟨838,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1322,by decide⟩]

def ntree14RLRLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLRLRRRRL i else ntree14RLRLRRRRR (i - 4)

def ntree14RLRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRLRRRL i else ntree14RLRLRRRR (i - 8)

def ntree14RLRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRLRRL i else ntree14RLRLRRR (i - 16)

def ntree14RLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RLRLRL i else ntree14RLRLRR (i - 32)

def ntree14RLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RLRLL i else ntree14RLRLR (i - 65)

def ntree14RLRRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨838,by decide⟩,⟨345,by decide⟩,⟨1323,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨1324,by decide⟩,⟨1325,by decide⟩] | 2 => ![⟨842,by decide⟩,⟨1326,by decide⟩,⟨1327,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1324,by decide⟩,⟨1324,by decide⟩] | 4 => ![⟨843,by decide⟩,⟨1326,by decide⟩,⟨1326,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1328,by decide⟩] | 6 => ![⟨880,by decide⟩,⟨345,by decide⟩,⟨1329,by decide⟩] | _ => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨0,by decide⟩]

def ntree14RLRRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1330,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1331,by decide⟩,⟨1331,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1332,by decide⟩,⟨660,by decide⟩,⟨827,by decide⟩] | 3 => ![⟨1330,by decide⟩,⟨23,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1333,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 5 => ![⟨1334,by decide⟩,⟨402,by decide⟩,⟨897,by decide⟩] | 6 => ![⟨1335,by decide⟩,⟨661,by decide⟩,⟨837,by decide⟩] | _ => ![⟨898,by decide⟩,⟨634,by decide⟩,⟨898,by decide⟩]

def ntree14RLRRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRLLLL i else ntree14RLRRLLLR (i - 8)

def ntree14RLRRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1336,by decide⟩,⟨1336,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1337,by decide⟩,⟨1337,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨1338,by decide⟩,⟨843,by decide⟩] | 3 => ![⟨1339,by decide⟩,⟨1339,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1340,by decide⟩,⟨1340,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1341,by decide⟩] | 6 => ![⟨1330,by decide⟩,⟨634,by decide⟩,⟨1341,by decide⟩] | _ => ![⟨827,by decide⟩,⟨672,by decide⟩,⟨1342,by decide⟩]

def ntree14RLRRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨910,by decide⟩,⟨1343,by decide⟩,⟨910,by decide⟩] | 1 => ![⟨886,by decide⟩,⟨1344,by decide⟩,⟨1344,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1345,by decide⟩,⟨1345,by decide⟩] | 3 => ![⟨1331,by decide⟩,⟨1346,by decide⟩,⟨1345,by decide⟩] | 4 => ![⟨903,by decide⟩,⟨1345,by decide⟩,⟨1347,by decide⟩] | 5 => ![⟨843,by decide⟩,⟨843,by decide⟩,⟨1348,by decide⟩] | 6 => ![⟨1349,by decide⟩,⟨1155,by decide⟩,⟨84,by decide⟩] | _ => ![⟨1155,by decide⟩,⟨1350,by decide⟩,⟨1345,by decide⟩]

def ntree14RLRRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRLLRL i else ntree14RLRRLLRR (i - 8)

def ntree14RLRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRRLLL i else ntree14RLRRLLR (i - 16)

def ntree14RLRRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨886,by decide⟩,⟨1351,by decide⟩,⟨1351,by decide⟩] | 1 => ![⟨1352,by decide⟩,⟨660,by decide⟩,⟨880,by decide⟩] | 2 => ![⟨880,by decide⟩,⟨1345,by decide⟩,⟨1353,by decide⟩] | 3 => ![⟨1354,by decide⟩,⟨402,by decide⟩,⟨838,by decide⟩] | 4 => ![⟨1355,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 5 => ![⟨1356,by decide⟩,⟨660,by decide⟩,⟨838,by decide⟩] | 6 => ![⟨1357,by decide⟩,⟨661,by decide⟩,⟨840,by decide⟩] | _ => ![⟨1358,by decide⟩,⟨1336,by decide⟩,⟨4,by decide⟩]

def ntree14RLRRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1359,by decide⟩,⟨1337,by decide⟩,⟨6,by decide⟩] | 1 => ![⟨1360,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨1361,by decide⟩,⟨1338,by decide⟩,⟨842,by decide⟩] | 3 => ![⟨1362,by decide⟩,⟨1339,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨1363,by decide⟩,⟨402,by decide⟩,⟨838,by decide⟩] | 5 => ![⟨1364,by decide⟩,⟨1340,by decide⟩,⟨838,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1191,by decide⟩,⟨1191,by decide⟩] | _ => ![⟨838,by decide⟩,⟨462,by decide⟩,⟨1365,by decide⟩]

def ntree14RLRRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRLRLL i else ntree14RLRRLRLR (i - 8)

def ntree14RLRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨910,by decide⟩,⟨1194,by decide⟩,⟨1194,by decide⟩] | 1 => ![⟨1366,by decide⟩,⟨1196,by decide⟩,⟨109,by decide⟩] | 2 => ![⟨1367,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1368,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1369,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨951,by decide⟩,⟨951,by decide⟩,⟨1370,by decide⟩] | 6 => ![⟨1371,by decide⟩,⟨1196,by decide⟩,⟨122,by decide⟩] | _ => ![⟨827,by decide⟩,⟨1372,by decide⟩,⟨1373,by decide⟩]

def ntree14RLRRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨963,by decide⟩,⟨1374,by decide⟩,⟨1375,by decide⟩] | 1 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨1376,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1376,by decide⟩] | _ => ![⟨1196,by decide⟩,⟨1377,by decide⟩,⟨1378,by decide⟩]

def ntree14RLRRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1367,by decide⟩,⟨634,by decide⟩,⟨1379,by decide⟩] | 1 => ![⟨1369,by decide⟩,⟨634,by decide⟩,⟨1380,by decide⟩] | 2 => ![⟨1381,by decide⟩,⟨1196,by decide⟩,⟨838,by decide⟩] | 3 => ![⟨1382,by decide⟩,⟨483,by decide⟩,⟨838,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1383,by decide⟩,⟨1384,by decide⟩]

def ntree14RLRRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLRRLRRRL i else ntree14RLRRLRRRR (i - 4)

def ntree14RLRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRLRRL i else ntree14RLRRLRRR (i - 8)

def ntree14RLRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRRLRL i else ntree14RLRRLRR (i - 16)

def ntree14RLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RLRRLL i else ntree14RLRRLR (i - 32)

def ntree14RLRRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨838,by decide⟩,⟨1383,by decide⟩,⟨1385,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1380,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1380,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1386,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1387,by decide⟩,⟨1388,by decide⟩,⟨857,by decide⟩] | 6 => ![⟨1389,by decide⟩,⟨1390,by decide⟩,⟨827,by decide⟩] | _ => ![⟨1388,by decide⟩,⟨1388,by decide⟩,⟨38,by decide⟩]

def ntree14RLRRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1390,by decide⟩,⟨1390,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1391,by decide⟩,⟨1392,by decide⟩,⟨1393,by decide⟩] | 2 => ![⟨1394,by decide⟩,⟨1395,by decide⟩,⟨1396,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨1383,by decide⟩,⟨1397,by decide⟩] | 4 => ![⟨1398,by decide⟩,⟨1399,by decide⟩,⟨1400,by decide⟩] | 5 => ![⟨1401,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1402,by decide⟩,⟨0,by decide⟩,⟨122,by decide⟩] | _ => ![⟨1401,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩]

def ntree14RLRRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRRLLL i else ntree14RLRRRLLR (i - 8)

def ntree14RLRRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨838,by decide⟩,⟨0,by decide⟩,⟨1403,by decide⟩] | 1 => ![⟨1404,by decide⟩,⟨1404,by decide⟩,⟨886,by decide⟩] | 2 => ![⟨1405,by decide⟩,⟨1405,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1406,by decide⟩,⟨1406,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1407,by decide⟩,⟨1407,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1408,by decide⟩,⟨1408,by decide⟩,⟨951,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1409,by decide⟩,⟨1409,by decide⟩] | _ => ![⟨122,by decide⟩,⟨1409,by decide⟩,⟨1410,by decide⟩]

def ntree14RLRRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1411,by decide⟩] | 1 => ![⟨1412,by decide⟩,⟨1407,by decide⟩,⟨122,by decide⟩] | 2 => ![⟨1413,by decide⟩,⟨1404,by decide⟩,⟨894,by decide⟩] | _ => ![⟨1414,by decide⟩,⟨1196,by decide⟩,⟨895,by decide⟩]

def ntree14RLRRRLRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1415,by decide⟩,⟨1405,by decide⟩,⟨827,by decide⟩] | 1 => ![⟨1416,by decide⟩,⟨1196,by decide⟩,⟨896,by decide⟩] | 2 => ![⟨1417,by decide⟩,⟨1235,by decide⟩,⟨996,by decide⟩] | 3 => ![⟨1418,by decide⟩,⟨402,by decide⟩,⟨122,by decide⟩] | _ => ![⟨1419,by decide⟩,⟨1406,by decide⟩,⟨827,by decide⟩]

def ntree14RLRRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLRRRLRRL i else ntree14RLRRRLRRR (i - 4)

def ntree14RLRRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRRLRL i else ntree14RLRRRLRR (i - 8)

def ntree14RLRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRRRLL i else ntree14RLRRRLR (i - 16)

def ntree14RLRRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1420,by decide⟩,⟨402,by decide⟩,⟨122,by decide⟩] | 1 => ![⟨1421,by decide⟩,⟨1408,by decide⟩,⟨963,by decide⟩] | 2 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1422,by decide⟩,⟨1422,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1423,by decide⟩,⟨1424,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1424,by decide⟩,⟨1424,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1425,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1426,by decide⟩,⟨1196,by decide⟩,⟨84,by decide⟩]

def ntree14RLRRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1427,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1428,by decide⟩,⟨1240,by decide⟩,⟨209,by decide⟩] | 2 => ![⟨1429,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1430,by decide⟩] | 4 => ![⟨1431,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1432,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1433,by decide⟩,⟨402,by decide⟩,⟨1015,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1372,by decide⟩,⟨1372,by decide⟩]

def ntree14RLRRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRRRLL i else ntree14RLRRRRLR (i - 8)

def ntree14RLRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨951,by decide⟩,⟨1374,by decide⟩,⟨1374,by decide⟩] | 1 => ![⟨1015,by decide⟩,⟨345,by decide⟩,⟨1434,by decide⟩] | 2 => ![⟨1435,by decide⟩,⟨1235,by decide⟩,⟨1026,by decide⟩] | 3 => ![⟨1436,by decide⟩,⟨1196,by decide⟩,⟨230,by decide⟩] | 4 => ![⟨1437,by decide⟩,⟨402,by decide⟩,⟨838,by decide⟩] | 5 => ![⟨1438,by decide⟩,⟨1196,by decide⟩,⟨231,by decide⟩] | 6 => ![⟨1439,by decide⟩,⟨1240,by decide⟩,⟨232,by decide⟩] | _ => ![⟨1440,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩]

def ntree14RLRRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1441,by decide⟩,⟨402,by decide⟩,⟨838,by decide⟩] | 1 => ![⟨1442,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 2 => ![⟨1443,by decide⟩,⟨501,by decide⟩,⟨1027,by decide⟩] | _ => ![⟨1444,by decide⟩,⟨1422,by decide⟩,⟨838,by decide⟩]

def ntree14RLRRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1015,by decide⟩,⟨542,by decide⟩,⟨1445,by decide⟩] | 1 => ![⟨1027,by decide⟩,⟨543,by decide⟩,⟨1446,by decide⟩] | 2 => ![⟨1447,by decide⟩,⟨1447,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨1448,by decide⟩,⟨1447,by decide⟩,⟨6,by decide⟩] | _ => ![⟨1449,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩]

def ntree14RLRRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RLRRRRRRL i else ntree14RLRRRRRRR (i - 4)

def ntree14RLRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RLRRRRRL i else ntree14RLRRRRRR (i - 8)

def ntree14RLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RLRRRRL i else ntree14RLRRRRR (i - 16)

def ntree14RLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 33 then ntree14RLRRRL i else ntree14RLRRRR (i - 33)

def ntree14RLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RLRRL i else ntree14RLRRR (i - 65)

def ntree14RLR (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14RLRL i else ntree14RLRR (i - 130)

def ntree14RL (i : Nat) : Fin 3 → Fin 1937 := if i < 260 then ntree14RLL i else ntree14RLR (i - 260)

def ntree14RRLLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1450,by decide⟩,⟨1451,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨1452,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1451,by decide⟩,⟨1451,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1453,by decide⟩,⟨1454,by decide⟩,⟨253,by decide⟩] | 5 => ![⟨1455,by decide⟩,⟨254,by decide⟩,⟨254,by decide⟩] | 6 => ![⟨1196,by decide⟩,⟨1456,by decide⟩,⟨628,by decide⟩] | _ => ![⟨1447,by decide⟩,⟨1457,by decide⟩,⟨629,by decide⟩]

def ntree14RRLLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨1458,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1451,by decide⟩,⟨1459,by decide⟩,⟨345,by decide⟩] | 2 => ![⟨1460,by decide⟩,⟨1447,by decide⟩,⟨264,by decide⟩] | 3 => ![⟨1461,by decide⟩,⟨1451,by decide⟩,⟨263,by decide⟩] | 4 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨1317,by decide⟩] | 5 => ![⟨1451,by decide⟩,⟨1462,by decide⟩,⟨1128,by decide⟩] | 6 => ![⟨1196,by decide⟩,⟨1463,by decide⟩,⟨672,by decide⟩] | _ => ![⟨1464,by decide⟩,⟨1464,by decide⟩,⟨299,by decide⟩]

def ntree14RRLLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLLLLL i else ntree14RRLLLLLR (i - 8)

def ntree14RRLLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1465,by decide⟩,⟨1465,by decide⟩,⟨300,by decide⟩] | 1 => ![⟨1466,by decide⟩,⟨1466,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1467,by decide⟩,⟨1467,by decide⟩,⟨179,by decide⟩] | 3 => ![⟨1468,by decide⟩,⟨1331,by decide⟩,⟨218,by decide⟩] | 4 => ![⟨1469,by decide⟩,⟨1196,by decide⟩,⟨321,by decide⟩] | 5 => ![⟨1470,by decide⟩,⟨1447,by decide⟩,⟨322,by decide⟩] | 6 => ![⟨1471,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | _ => ![⟨1472,by decide⟩,⟨1464,by decide⟩,⟨323,by decide⟩]

def ntree14RRLLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1473,by decide⟩,⟨1465,by decide⟩,⟨324,by decide⟩] | 1 => ![⟨1474,by decide⟩,⟨300,by decide⟩,⟨300,by decide⟩] | 2 => ![⟨1475,by decide⟩,⟨1466,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨1476,by decide⟩,⟨1467,by decide⟩,⟨317,by decide⟩] | 4 => ![⟨1477,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1047,by decide⟩,⟨1341,by decide⟩] | 6 => ![⟨1331,by decide⟩,⟨1478,by decide⟩,⟨542,by decide⟩] | _ => ![⟨1479,by decide⟩,⟨1479,by decide⟩,⟨0,by decide⟩]

def ntree14RRLLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLLLRL i else ntree14RRLLLLRR (i - 8)

def ntree14RRLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLLLLL i else ntree14RRLLLLR (i - 16)

def ntree14RRLLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1480,by decide⟩,⟨1480,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1480,by decide⟩,⟨1481,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨1482,by decide⟩,⟨1482,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨1483,by decide⟩,⟨0,by decide⟩,⟨1483,by decide⟩] | 4 => ![⟨1484,by decide⟩,⟨16,by decide⟩,⟨1484,by decide⟩] | 5 => ![⟨1485,by decide⟩,⟨1480,by decide⟩,⟨827,by decide⟩] | 6 => ![⟨1486,by decide⟩,⟨8,by decide⟩,⟨1486,by decide⟩] | _ => ![⟨1487,by decide⟩,⟨0,by decide⟩,⟨1487,by decide⟩]

def ntree14RRLLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1488,by decide⟩,⟨820,by decide⟩,⟨1487,by decide⟩] | 1 => ![⟨1489,by decide⟩,⟨2,by decide⟩,⟨1489,by decide⟩] | 2 => ![⟨1490,by decide⟩,⟨10,by decide⟩,⟨1490,by decide⟩] | 3 => ![⟨1491,by decide⟩,⟨0,by decide⟩,⟨1491,by decide⟩] | 4 => ![⟨1492,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1492,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨1493,by decide⟩,⟨1494,by decide⟩,⟨827,by decide⟩] | _ => ![⟨1495,by decide⟩,⟨1496,by decide⟩,⟨0,by decide⟩]

def ntree14RRLLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLLRLL i else ntree14RRLLLRLR (i - 8)

def ntree14RRLLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨838,by decide⟩,⟨0,by decide⟩,⟨838,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1497,by decide⟩,⟨0,by decide⟩,⟨1497,by decide⟩] | 3 => ![⟨1497,by decide⟩,⟨1,by decide⟩,⟨1498,by decide⟩] | 4 => ![⟨1499,by decide⟩,⟨8,by decide⟩,⟨1499,by decide⟩] | 5 => ![⟨1499,by decide⟩,⟨9,by decide⟩,⟨1500,by decide⟩] | 6 => ![⟨1501,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | _ => ![⟨1502,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RRLLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1503,by decide⟩,⟨1480,by decide⟩,⟨838,by decide⟩] | 1 => ![⟨1504,by decide⟩,⟨1504,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1505,by decide⟩,⟨0,by decide⟩,⟨1505,by decide⟩] | _ => ![⟨1506,by decide⟩,⟨0,by decide⟩,⟨1506,by decide⟩]

def ntree14RRLLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1507,by decide⟩,⟨50,by decide⟩,⟨1507,by decide⟩] | 1 => ![⟨1508,by decide⟩,⟨1504,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1509,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1510,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1511,by decide⟩]

def ntree14RRLLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRLLLRRRL i else ntree14RRLLLRRRR (i - 4)

def ntree14RRLLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLLRRL i else ntree14RRLLLRRR (i - 8)

def ntree14RRLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLLLRL i else ntree14RRLLLRR (i - 16)

def ntree14RRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RRLLLL i else ntree14RRLLLR (i - 32)

def ntree14RRLLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1512,by decide⟩,⟨0,by decide⟩,⟨1512,by decide⟩] | 1 => ![⟨1513,by decide⟩,⟨8,by decide⟩,⟨1513,by decide⟩] | 2 => ![⟨1514,by decide⟩,⟨1514,by decide⟩,⟨56,by decide⟩] | 3 => ![⟨1514,by decide⟩,⟨1515,by decide⟩,⟨57,by decide⟩] | 4 => ![⟨1516,by decide⟩,⟨1516,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨1517,by decide⟩,⟨1517,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1518,by decide⟩,⟨1518,by decide⟩,⟨2,by decide⟩] | _ => ![⟨1519,by decide⟩,⟨1519,by decide⟩,⟨10,by decide⟩]

def ntree14RRLLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1480,by decide⟩,⟨1520,by decide⟩,⟨61,by decide⟩] | 1 => ![⟨1521,by decide⟩,⟨1521,by decide⟩,⟨16,by decide⟩] | 2 => ![⟨1522,by decide⟩,⟨56,by decide⟩,⟨1522,by decide⟩] | 3 => ![⟨1523,by decide⟩,⟨1,by decide⟩,⟨1524,by decide⟩] | 4 => ![⟨1522,by decide⟩,⟨57,by decide⟩,⟨1525,by decide⟩] | 5 => ![⟨1523,by decide⟩,⟨0,by decide⟩,⟨1523,by decide⟩] | 6 => ![⟨1526,by decide⟩,⟨1517,by decide⟩,⟨827,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1527,by decide⟩]

def ntree14RRLLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLRLLL i else ntree14RRLLRLLR (i - 8)

def ntree14RRLLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨827,by decide⟩,⟨61,by decide⟩,⟨1528,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1529,by decide⟩] | 2 => ![⟨1530,by decide⟩,⟨1514,by decide⟩,⟨1522,by decide⟩] | 3 => ![⟨1531,by decide⟩,⟨1480,by decide⟩,⟨1523,by decide⟩] | 4 => ![⟨1532,by decide⟩,⟨60,by decide⟩,⟨1532,by decide⟩] | 5 => ![⟨1533,by decide⟩,⟨56,by decide⟩,⟨1533,by decide⟩] | 6 => ![⟨1534,by decide⟩,⟨8,by decide⟩,⟨1534,by decide⟩] | _ => ![⟨1535,by decide⟩,⟨0,by decide⟩,⟨1535,by decide⟩]

def ntree14RRLLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1536,by decide⟩,⟨1516,by decide⟩,⟨1486,by decide⟩] | 1 => ![⟨1537,by decide⟩,⟨1517,by decide⟩,⟨1487,by decide⟩] | 2 => ![⟨1538,by decide⟩,⟨56,by decide⟩,⟨1538,by decide⟩] | 3 => ![⟨1523,by decide⟩,⟨41,by decide⟩,⟨1539,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1540,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1541,by decide⟩] | 6 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨1540,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1542,by decide⟩,⟨0,by decide⟩]

def ntree14RRLLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLRLRL i else ntree14RRLLRLRR (i - 8)

def ntree14RRLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLLRLL i else ntree14RRLLRLR (i - 16)

def ntree14RRLLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨56,by decide⟩,⟨1543,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1544,by decide⟩] | 2 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨1545,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1546,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1547,by decide⟩] | 5 => ![⟨1548,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 6 => ![⟨1549,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1550,by decide⟩,⟨56,by decide⟩,⟨1550,by decide⟩]

def ntree14RRLLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1551,by decide⟩,⟨0,by decide⟩,⟨1551,by decide⟩] | 1 => ![⟨1552,by decide⟩,⟨58,by decide⟩,⟨1552,by decide⟩] | 2 => ![⟨1553,by decide⟩,⟨2,by decide⟩,⟨1553,by decide⟩] | 3 => ![⟨1554,by decide⟩,⟨1517,by decide⟩,⟨838,by decide⟩] | 4 => ![⟨1555,by decide⟩,⟨56,by decide⟩,⟨1555,by decide⟩] | 5 => ![⟨1556,by decide⟩,⟨0,by decide⟩,⟨1556,by decide⟩] | 6 => ![⟨1492,by decide⟩,⟨1557,by decide⟩,⟨1546,by decide⟩] | _ => ![⟨1492,by decide⟩,⟨1558,by decide⟩,⟨1547,by decide⟩]

def ntree14RRLLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLRRLL i else ntree14RRLLRRLR (i - 8)

def ntree14RRLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨1557,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1557,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1559,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨838,by decide⟩,⟨102,by decide⟩,⟨1560,by decide⟩] | 5 => ![⟨1561,by decide⟩,⟨882,by decide⟩,⟨1497,by decide⟩] | 6 => ![⟨838,by decide⟩,⟨1542,by decide⟩,⟨838,by decide⟩] | _ => ![⟨1562,by decide⟩,⟨882,by decide⟩,⟨1551,by decide⟩]

def ntree14RRLLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1563,by decide⟩,⟨60,by decide⟩,⟨60,by decide⟩] | 1 => ![⟨1564,by decide⟩,⟨1514,by decide⟩,⟨1550,by decide⟩] | 2 => ![⟨1565,by decide⟩,⟨1516,by decide⟩,⟨1499,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RRLLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1566,by decide⟩] | 1 => ![⟨1567,by decide⟩,⟨0,by decide⟩,⟨1567,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1568,by decide⟩] | 3 => ![⟨816,by decide⟩,⟨1569,by decide⟩,⟨118,by decide⟩] | _ => ![⟨827,by decide⟩,⟨118,by decide⟩,⟨1570,by decide⟩]

def ntree14RRLLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRLLRRRRL i else ntree14RRLLRRRRR (i - 4)

def ntree14RRLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLLRRRL i else ntree14RRLLRRRR (i - 8)

def ntree14RRLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLLRRL i else ntree14RRLLRRR (i - 16)

def ntree14RRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RRLLRL i else ntree14RRLLRR (i - 32)

def ntree14RRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RRLLL i else ntree14RRLLR (i - 65)

def ntree14RRLRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1486,by decide⟩,⟨134,by decide⟩,⟨1571,by decide⟩] | 1 => ![⟨1487,by decide⟩,⟨135,by decide⟩,⟨1572,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1573,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨838,by decide⟩,⟨144,by decide⟩,⟨1574,by decide⟩] | 4 => ![⟨838,by decide⟩,⟨118,by decide⟩,⟨1575,by decide⟩] | 5 => ![⟨1576,by decide⟩,⟨120,by decide⟩,⟨1577,by decide⟩] | 6 => ![⟨1578,by decide⟩,⟨1,by decide⟩,⟨1579,by decide⟩] | _ => ![⟨1576,by decide⟩,⟨119,by decide⟩,⟨1576,by decide⟩]

def ntree14RRLRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1578,by decide⟩,⟨0,by decide⟩,⟨1578,by decide⟩] | 1 => ![⟨827,by decide⟩,⟨139,by decide⟩,⟨1580,by decide⟩] | 2 => ![⟨1581,by decide⟩,⟨1,by decide⟩,⟨1582,by decide⟩] | 3 => ![⟨1583,by decide⟩,⟨141,by decide⟩,⟨1584,by decide⟩] | 4 => ![⟨1581,by decide⟩,⟨0,by decide⟩,⟨1581,by decide⟩] | 5 => ![⟨1583,by decide⟩,⟨140,by decide⟩,⟨1583,by decide⟩] | 6 => ![⟨857,by decide⟩,⟨155,by decide⟩,⟨1585,by decide⟩] | _ => ![⟨838,by decide⟩,⟨118,by decide⟩,⟨1586,by decide⟩]

def ntree14RRLRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRLLLL i else ntree14RRLRLLLR (i - 8)

def ntree14RRLRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨827,by decide⟩,⟨145,by decide⟩,⟨1587,by decide⟩] | 1 => ![⟨1588,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1589,by decide⟩,⟨118,by decide⟩,⟨1590,by decide⟩] | 3 => ![⟨1589,by decide⟩,⟨0,by decide⟩,⟨1589,by decide⟩] | 4 => ![⟨838,by decide⟩,⟨0,by decide⟩,⟨838,by decide⟩] | 5 => ![⟨1591,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 6 => ![⟨1592,by decide⟩,⟨1592,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1593,by decide⟩,⟨1593,by decide⟩,⟨8,by decide⟩]

def ntree14RRLRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1567,by decide⟩,⟨61,by decide⟩,⟨1594,by decide⟩] | 1 => ![⟨1487,by decide⟩,⟨173,by decide⟩,⟨1595,by decide⟩] | 2 => ![⟨903,by decide⟩,⟨1573,by decide⟩,⟨903,by decide⟩] | 3 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨1596,by decide⟩] | 4 => ![⟨1597,by decide⟩,⟨1,by decide⟩,⟨1598,by decide⟩] | 5 => ![⟨1599,by decide⟩,⟨57,by decide⟩,⟨1600,by decide⟩] | 6 => ![⟨1597,by decide⟩,⟨0,by decide⟩,⟨1597,by decide⟩] | _ => ![⟨1599,by decide⟩,⟨56,by decide⟩,⟨1599,by decide⟩]

def ntree14RRLRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRLLRL i else ntree14RRLRLLRR (i - 8)

def ntree14RRLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLRLLL i else ntree14RRLRLLR (i - 16)

def ntree14RRLRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1522,by decide⟩,⟨181,by decide⟩,⟨1601,by decide⟩] | 1 => ![⟨1602,by decide⟩,⟨180,by decide⟩,⟨1603,by decide⟩] | 2 => ![⟨1604,by decide⟩,⟨183,by decide⟩,⟨1605,by decide⟩] | 3 => ![⟨1602,by decide⟩,⟨179,by decide⟩,⟨1602,by decide⟩] | 4 => ![⟨1604,by decide⟩,⟨182,by decide⟩,⟨1604,by decide⟩] | 5 => ![⟨827,by decide⟩,⟨184,by decide⟩,⟨1606,by decide⟩] | 6 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1607,by decide⟩] | _ => ![⟨1005,by decide⟩,⟨185,by decide⟩,⟨1608,by decide⟩]

def ntree14RRLRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1609,by decide⟩,⟨196,by decide⟩,⟨1609,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1610,by decide⟩,⟨8,by decide⟩,⟨1610,by decide⟩] | 3 => ![⟨1611,by decide⟩,⟨0,by decide⟩,⟨1611,by decide⟩] | 4 => ![⟨56,by decide⟩,⟨1612,by decide⟩,⟨56,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨1613,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1614,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1615,by decide⟩,⟨0,by decide⟩]

def ntree14RRLRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRLRLL i else ntree14RRLRLRLR (i - 8)

def ntree14RRLRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨889,by decide⟩,⟨1616,by decide⟩,⟨118,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1015,by decide⟩,⟨118,by decide⟩,⟨1617,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1618,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨838,by decide⟩,⟨1618,by decide⟩,⟨838,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨1619,by decide⟩] | 6 => ![⟨1551,by decide⟩,⟨118,by decide⟩,⟨1620,by decide⟩] | _ => ![⟨1550,by decide⟩,⟨221,by decide⟩,⟨1621,by decide⟩]

def ntree14RRLRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨838,by decide⟩,⟨118,by decide⟩,⟨1622,by decide⟩] | 1 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨1623,by decide⟩] | 2 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨1624,by decide⟩] | _ => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1625,by decide⟩]

def ntree14RRLRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨182,by decide⟩,⟨182,by decide⟩,⟨1626,by decide⟩] | 1 => ![⟨838,by decide⟩,⟨118,by decide⟩,⟨1627,by decide⟩] | 2 => ![⟨1027,by decide⟩,⟨237,by decide⟩,⟨1628,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1629,by decide⟩] | _ => ![⟨1630,by decide⟩,⟨196,by decide⟩,⟨1630,by decide⟩]

def ntree14RRLRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRLRLRRRL i else ntree14RRLRLRRRR (i - 4)

def ntree14RRLRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRLRRL i else ntree14RRLRLRRR (i - 8)

def ntree14RRLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLRLRL i else ntree14RRLRLRR (i - 16)

def ntree14RRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RRLRLL i else ntree14RRLRLR (i - 32)

def ntree14RRLRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1631,by decide⟩,⟨199,by decide⟩,⟨1631,by decide⟩] | 1 => ![⟨1632,by decide⟩,⟨179,by decide⟩,⟨1632,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1633,by decide⟩] | 3 => ![⟨820,by decide⟩,⟨820,by decide⟩,⟨1633,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1634,by decide⟩] | 5 => ![⟨1480,by decide⟩,⟨1635,by decide⟩,⟨118,by decide⟩] | 6 => ![⟨827,by decide⟩,⟨261,by decide⟩,⟨1636,by decide⟩] | _ => ![⟨837,by decide⟩,⟨262,by decide⟩,⟨1637,by decide⟩]

def ntree14RRLRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨1638,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨1639,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨1492,by decide⟩,⟨1573,by decide⟩,⟨1633,by decide⟩] | 3 => ![⟨1492,by decide⟩,⟨128,by decide⟩,⟨128,by decide⟩] | 4 => ![⟨1495,by decide⟩,⟨1640,by decide⟩,⟨118,by decide⟩] | 5 => ![⟨1497,by decide⟩,⟨245,by decide⟩,⟨1641,by decide⟩] | 6 => ![⟨1642,by decide⟩,⟨1642,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1642,by decide⟩,⟨1643,by decide⟩,⟨245,by decide⟩]

def ntree14RRLRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRRLLL i else ntree14RRLRRLLR (i - 8)

def ntree14RRLRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1644,by decide⟩,⟨1644,by decide⟩,⟨140,by decide⟩] | 1 => ![⟨1645,by decide⟩,⟨1645,by decide⟩,⟨140,by decide⟩] | 2 => ![⟨1646,by decide⟩,⟨1642,by decide⟩,⟨1567,by decide⟩] | 3 => ![⟨1647,by decide⟩,⟨254,by decide⟩,⟨254,by decide⟩] | 4 => ![⟨50,by decide⟩,⟨1648,by decide⟩,⟨50,by decide⟩] | 5 => ![⟨1642,by decide⟩,⟨1649,by decide⟩,⟨41,by decide⟩] | 6 => ![⟨1650,by decide⟩,⟨1642,by decide⟩,⟨880,by decide⟩] | _ => ![⟨880,by decide⟩,⟨261,by decide⟩,⟨1651,by decide⟩]

def ntree14RRLRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1652,by decide⟩] | 1 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨1652,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1653,by decide⟩] | _ => ![⟨56,by decide⟩,⟨1654,by decide⟩,⟨56,by decide⟩]

def ntree14RRLRRLRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨882,by decide⟩,⟨1655,by decide⟩,⟨307,by decide⟩] | 1 => ![⟨1656,by decide⟩,⟨1656,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1657,by decide⟩,⟨1657,by decide⟩,⟨56,by decide⟩] | 3 => ![⟨1658,by decide⟩,⟨1658,by decide⟩,⟨179,by decide⟩] | _ => ![⟨1659,by decide⟩,⟨1659,by decide⟩,⟨182,by decide⟩]

def ntree14RRLRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRLRRLRRL i else ntree14RRLRRLRRR (i - 4)

def ntree14RRLRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRRLRL i else ntree14RRLRRLRR (i - 8)

def ntree14RRLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLRRLL i else ntree14RRLRRLR (i - 16)

def ntree14RRLRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨56,by decide⟩,⟨1660,by decide⟩,⟨56,by decide⟩] | 2 => ![⟨58,by decide⟩,⟨1661,by decide⟩,⟨58,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨1662,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨1663,by decide⟩,⟨261,by decide⟩] | 5 => ![⟨882,by decide⟩,⟨1664,by decide⟩,⟨118,by decide⟩] | 6 => ![⟨2,by decide⟩,⟨1665,by decide⟩,⟨2,by decide⟩] | _ => ![⟨884,by decide⟩,⟨1666,by decide⟩,⟨262,by decide⟩]

def ntree14RRLRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1514,by decide⟩,⟨1667,by decide⟩,⟨221,by decide⟩] | 1 => ![⟨56,by decide⟩,⟨1668,by decide⟩,⟨56,by decide⟩] | 2 => ![⟨882,by decide⟩,⟨1669,by decide⟩,⟨118,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1670,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1671,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1672,by decide⟩,⟨0,by decide⟩]

def ntree14RRLRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRRRLL i else ntree14RRLRRRLR (i - 8)

def ntree14RRLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1673,by decide⟩,⟨1674,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1675,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨827,by decide⟩,⟨1675,by decide⟩,⟨827,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨1676,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨1487,by decide⟩,⟨345,by decide⟩,⟨1677,by decide⟩] | 5 => ![⟨1486,by decide⟩,⟨355,by decide⟩,⟨1678,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1679,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1680,by decide⟩]

def ntree14RRLRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨848,by decide⟩,⟨356,by decide⟩,⟨1681,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14RRLRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1682,by decide⟩] | 1 => ![⟨1683,by decide⟩,⟨1,by decide⟩,⟨1684,by decide⟩] | 2 => ![⟨827,by decide⟩,⟨356,by decide⟩,⟨1685,by decide⟩] | 3 => ![⟨1686,by decide⟩,⟨358,by decide⟩,⟨1687,by decide⟩] | _ => ![⟨1495,by decide⟩,⟨1688,by decide⟩,⟨356,by decide⟩]

def ntree14RRLRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRLRRRRRL i else ntree14RRLRRRRRR (i - 4)

def ntree14RRLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRLRRRRL i else ntree14RRLRRRRR (i - 8)

def ntree14RRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRLRRRL i else ntree14RRLRRRR (i - 16)

def ntree14RRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 33 then ntree14RRLRRL i else ntree14RRLRRR (i - 33)

def ntree14RRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RRLRL i else ntree14RRLRR (i - 65)

def ntree14RRL (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14RRLL i else ntree14RRLR (i - 130)

def ntree14RRRLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1683,by decide⟩,⟨0,by decide⟩,⟨1683,by decide⟩] | 1 => ![⟨1686,by decide⟩,⟨357,by decide⟩,⟨1686,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1689,by decide⟩] | 3 => ![⟨827,by decide⟩,⟨371,by decide⟩,⟨1690,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1691,by decide⟩,⟨356,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1692,by decide⟩] | 6 => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1693,by decide⟩,⟨1693,by decide⟩,⟨0,by decide⟩]

def ntree14RRRLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨898,by decide⟩,⟨356,by decide⟩,⟨1694,by decide⟩] | 1 => ![⟨1517,by decide⟩,⟨1695,by decide⟩,⟨356,by decide⟩] | 2 => ![⟨1160,by decide⟩,⟨0,by decide⟩,⟨1160,by decide⟩] | 3 => ![⟨1162,by decide⟩,⟨433,by decide⟩,⟨1162,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨1696,by decide⟩,⟨356,by decide⟩] | 5 => ![⟨1697,by decide⟩,⟨1698,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨1699,by decide⟩,⟨1700,by decide⟩,⟨358,by decide⟩] | _ => ![⟨8,by decide⟩,⟨1701,by decide⟩,⟨8,by decide⟩]

def ntree14RRRLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLLLLL i else ntree14RRRLLLLR (i - 8)

def ntree14RRRLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1702,by decide⟩,⟨1703,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨1704,by decide⟩,⟨1705,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨1516,by decide⟩,⟨1706,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨1707,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨1708,by decide⟩,⟨356,by decide⟩] | 5 => ![⟨1697,by decide⟩,⟨1697,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1709,by decide⟩,⟨1710,by decide⟩,⟨356,by decide⟩] | _ => ![⟨1702,by decide⟩,⟨1702,by decide⟩,⟨8,by decide⟩]

def ntree14RRRLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1704,by decide⟩,⟨1704,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1711,by decide⟩] | 2 => ![⟨1699,by decide⟩,⟨1699,by decide⟩,⟨357,by decide⟩] | 3 => ![⟨1709,by decide⟩,⟨1709,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1712,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1517,by decide⟩,⟨1713,by decide⟩,⟨345,by decide⟩] | 6 => ![⟨20,by decide⟩,⟨1712,by decide⟩,⟨0,by decide⟩] | _ => ![⟨882,by decide⟩,⟨1714,by decide⟩,⟨448,by decide⟩]

def ntree14RRRLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLLLRL i else ntree14RRRLLLRR (i - 8)

def ntree14RRRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRLLLL i else ntree14RRRLLLR (i - 16)

def ntree14RRRLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨8,by decide⟩,⟨1715,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨1516,by decide⟩,⟨1716,by decide⟩,⟨355,by decide⟩] | 2 => ![⟨1717,by decide⟩,⟨399,by decide⟩,⟨1717,by decide⟩] | 3 => ![⟨1718,by decide⟩,⟨433,by decide⟩,⟨433,by decide⟩] | 4 => ![⟨1719,by decide⟩,⟨0,by decide⟩,⟨1719,by decide⟩] | 5 => ![⟨1720,by decide⟩,⟨1693,by decide⟩,⟨1719,by decide⟩] | 6 => ![⟨357,by decide⟩,⟨357,by decide⟩,⟨1721,by decide⟩] | _ => ![⟨1719,by decide⟩,⟨451,by decide⟩,⟨1722,by decide⟩]

def ntree14RRRLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1723,by decide⟩,⟨1155,by decide⟩,⟨1719,by decide⟩] | 1 => ![⟨1155,by decide⟩,⟨1724,by decide⟩,⟨102,by decide⟩] | 2 => ![⟨1725,by decide⟩,⟨399,by decide⟩,⟨1725,by decide⟩] | 3 => ![⟨1719,by decide⟩,⟨371,by decide⟩,⟨1726,by decide⟩] | 4 => ![⟨1517,by decide⟩,⟨1727,by decide⟩,⟨371,by decide⟩] | 5 => ![⟨1492,by decide⟩,⟨462,by decide⟩,⟨462,by decide⟩] | 6 => ![⟨1551,by decide⟩,⟨345,by decide⟩,⟨1728,by decide⟩] | _ => ![⟨1492,by decide⟩,⟨1712,by decide⟩,⟨1711,by decide⟩]

def ntree14RRRLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLLRLL i else ntree14RRRLLRLR (i - 8)

def ntree14RRRLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1729,by decide⟩,⟨1729,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨1729,by decide⟩,⟨1730,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨1731,by decide⟩,⟨1732,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨1733,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1734,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨468,by decide⟩,⟨468,by decide⟩,⟨1735,by decide⟩] | _ => ![⟨1731,by decide⟩,⟨1731,by decide⟩,⟨0,by decide⟩]

def ntree14RRRLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1196,by decide⟩,⟨1736,by decide⟩,⟨118,by decide⟩] | 1 => ![⟨1737,by decide⟩,⟨1738,by decide⟩,⟨120,by decide⟩] | 2 => ![⟨119,by decide⟩,⟨1739,by decide⟩,⟨119,by decide⟩] | _ => ![⟨1740,by decide⟩,⟨345,by decide⟩,⟨1741,by decide⟩]

def ntree14RRRLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1742,by decide⟩,⟨472,by decide⟩,⟨1743,by decide⟩] | 1 => ![⟨1729,by decide⟩,⟨1744,by decide⟩,⟨134,by decide⟩] | 2 => ![⟨1731,by decide⟩,⟨1745,by decide⟩,⟨135,by decide⟩] | 3 => ![⟨1746,by decide⟩,⟨1729,by decide⟩,⟨1486,by decide⟩] | _ => ![⟨1747,by decide⟩,⟨1196,by decide⟩,⟨1487,by decide⟩]

def ntree14RRRLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRRLLRRRL i else ntree14RRRLLRRRR (i - 4)

def ntree14RRRLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLLRRL i else ntree14RRRLLRRR (i - 8)

def ntree14RRRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRLLRL i else ntree14RRRLLRR (i - 16)

def ntree14RRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RRRLLL i else ntree14RRRLLR (i - 32)

def ntree14RRRLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1748,by decide⟩,⟨1731,by decide⟩,⟨827,by decide⟩] | 1 => ![⟨1749,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1750,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨827,by decide⟩,⟨1750,by decide⟩,⟨827,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1751,by decide⟩,⟨118,by decide⟩] | 5 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨1692,by decide⟩] | 6 => ![⟨1752,by decide⟩,⟨1731,by decide⟩,⟨1127,by decide⟩] | _ => ![⟨1693,by decide⟩,⟨1753,by decide⟩,⟨173,by decide⟩]

def ntree14RRRLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1740,by decide⟩,⟨0,by decide⟩,⟨1740,by decide⟩] | 1 => ![⟨1742,by decide⟩,⟨468,by decide⟩,⟨1742,by decide⟩] | 2 => ![⟨1754,by decide⟩,⟨1693,by decide⟩,⟨1000,by decide⟩] | 3 => ![⟨1196,by decide⟩,⟨1755,by decide⟩,⟨195,by decide⟩] | 4 => ![⟨1756,by decide⟩,⟨1757,by decide⟩,⟨197,by decide⟩] | 5 => ![⟨1758,by decide⟩,⟨1759,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨1729,by decide⟩,⟨1760,by decide⟩,⟨198,by decide⟩] | _ => ![⟨1761,by decide⟩,⟨1762,by decide⟩,⟨200,by decide⟩]

def ntree14RRRLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLRLLL i else ntree14RRRLRLLR (i - 8)

def ntree14RRRLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1763,by decide⟩,⟨1764,by decide⟩,⟨180,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨1765,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨199,by decide⟩,⟨1766,by decide⟩,⟨199,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨1767,by decide⟩,⟨179,by decide⟩] | 4 => ![⟨1756,by decide⟩,⟨1756,by decide⟩,⟨196,by decide⟩] | 5 => ![⟨1758,by decide⟩,⟨1758,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1761,by decide⟩,⟨1761,by decide⟩,⟨199,by decide⟩] | _ => ![⟨1763,by decide⟩,⟨1763,by decide⟩,⟨179,by decide⟩]

def ntree14RRRLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨482,by decide⟩,⟨0,by decide⟩,⟨1711,by decide⟩] | 1 => ![⟨1768,by decide⟩,⟨0,by decide⟩,⟨1768,by decide⟩] | 2 => ![⟨1768,by decide⟩,⟨118,by decide⟩,⟨1769,by decide⟩] | 3 => ![⟨1770,by decide⟩,⟨0,by decide⟩,⟨1770,by decide⟩] | 4 => ![⟨1771,by decide⟩,⟨1196,by decide⟩,⟨1551,by decide⟩] | 5 => ![⟨1196,by decide⟩,⟨1772,by decide⟩,⟨102,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨1773,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1240,by decide⟩,⟨1774,by decide⟩,⟨237,by decide⟩]

def ntree14RRRLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLRLRL i else ntree14RRRLRLRR (i - 8)

def ntree14RRRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRLRLL i else ntree14RRRLRLR (i - 16)

def ntree14RRRLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨179,by decide⟩,⟨1775,by decide⟩,⟨179,by decide⟩] | 1 => ![⟨1196,by decide⟩,⟨1776,by decide⟩,⟨245,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1777,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1778,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1779,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1196,by decide⟩,⟨1196,by decide⟩,⟨1780,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1780,by decide⟩] | _ => ![⟨1781,by decide⟩,⟨1196,by decide⟩,⟨1782,by decide⟩]

def ntree14RRRLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1783,by decide⟩,⟨0,by decide⟩,⟨1784,by decide⟩] | 1 => ![⟨1196,by decide⟩,⟨1785,by decide⟩,⟨356,by decide⟩] | 2 => ![⟨1783,by decide⟩,⟨356,by decide⟩,⟨1786,by decide⟩] | 3 => ![⟨1783,by decide⟩,⟨118,by decide⟩,⟨1787,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨356,by decide⟩,⟨1788,by decide⟩] | 5 => ![⟨1789,by decide⟩,⟨1790,by decide⟩,⟨1791,by decide⟩] | 6 => ![⟨1792,by decide⟩,⟨1793,by decide⟩,⟨1794,by decide⟩] | _ => ![⟨1795,by decide⟩,⟨1796,by decide⟩,⟨1797,by decide⟩]

def ntree14RRRLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLRRLL i else ntree14RRRLRRLR (i - 8)

def ntree14RRRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1492,by decide⟩,⟨1778,by decide⟩,⟨1798,by decide⟩] | 1 => ![⟨1492,by decide⟩,⟨1779,by decide⟩,⟨1799,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1799,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1799,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1800,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1050,by decide⟩,⟨1801,by decide⟩,⟨356,by decide⟩] | _ => ![⟨1802,by decide⟩,⟨1803,by decide⟩,⟨386,by decide⟩]

def ntree14RRRLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1804,by decide⟩,⟨1805,by decide⟩,⟨345,by decide⟩] | 1 => ![⟨1802,by decide⟩,⟨1802,by decide⟩,⟨50,by decide⟩] | 2 => ![⟨1804,by decide⟩,⟨1804,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1806,by decide⟩,⟨1806,by decide⟩,⟨399,by decide⟩]

def ntree14RRRLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1807,by decide⟩,⟨1807,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1808,by decide⟩,⟨1808,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1809,by decide⟩,⟨1809,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1810,by decide⟩,⟨1810,by decide⟩,⟨468,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1811,by decide⟩,⟨0,by decide⟩]

def ntree14RRRLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRRLRRRRL i else ntree14RRRLRRRRR (i - 4)

def ntree14RRRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRLRRRL i else ntree14RRRLRRRR (i - 8)

def ntree14RRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRLRRL i else ntree14RRRLRRR (i - 16)

def ntree14RRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RRRLRL i else ntree14RRRLRR (i - 32)

def ntree14RRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RRRLL i else ntree14RRRLR (i - 65)

def ntree14RRRRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨882,by decide⟩,⟨1812,by decide⟩,⟨592,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1813,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1814,by decide⟩] | 3 => ![⟨827,by decide⟩,⟨592,by decide⟩,⟨1815,by decide⟩] | 4 => ![⟨1000,by decide⟩,⟨592,by decide⟩,⟨1816,by decide⟩] | 5 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨1817,by decide⟩] | 6 => ![⟨1005,by decide⟩,⟨603,by decide⟩,⟨1818,by decide⟩] | _ => ![⟨882,by decide⟩,⟨882,by decide⟩,⟨0,by decide⟩]

def ntree14RRRRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1284,by decide⟩,⟨1819,by decide⟩,⟨609,by decide⟩] | 1 => ![⟨1196,by decide⟩,⟨1820,by decide⟩,⟨308,by decide⟩] | 2 => ![⟨882,by decide⟩,⟨1821,by decide⟩,⟨356,by decide⟩] | 3 => ![⟨1196,by decide⟩,⟨1822,by decide⟩,⟨309,by decide⟩] | 4 => ![⟨1240,by decide⟩,⟨1823,by decide⟩,⟨310,by decide⟩] | 5 => ![⟨179,by decide⟩,⟨1824,by decide⟩,⟨179,by decide⟩] | 6 => ![⟨882,by decide⟩,⟨1825,by decide⟩,⟨356,by decide⟩] | _ => ![⟨179,by decide⟩,⟨1826,by decide⟩,⟨179,by decide⟩]

def ntree14RRRRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRLLLL i else ntree14RRRRLLLR (i - 8)

def ntree14RRRRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1081,by decide⟩,⟨1827,by decide⟩,⟨603,by decide⟩] | 1 => ![⟨1828,by decide⟩,⟨1828,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1828,by decide⟩,⟨1829,by decide⟩,⟨356,by decide⟩] | 3 => ![⟨1196,by decide⟩,⟨1830,by decide⟩,⟨446,by decide⟩] | 4 => ![⟨1806,by decide⟩,⟨1831,by decide⟩,⟨447,by decide⟩] | 5 => ![⟨1807,by decide⟩,⟨1832,by decide⟩,⟨345,by decide⟩] | 6 => ![⟨1284,by decide⟩,⟨1833,by decide⟩,⟨616,by decide⟩] | _ => ![⟨1196,by decide⟩,⟨1834,by decide⟩,⟨449,by decide⟩]

def ntree14RRRRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨882,by decide⟩,⟨1835,by decide⟩,⟨118,by decide⟩] | 1 => ![⟨1809,by decide⟩,⟨1836,by decide⟩,⟨118,by decide⟩] | 2 => ![⟨882,by decide⟩,⟨1837,by decide⟩,⟨118,by decide⟩] | 3 => ![⟨1808,by decide⟩,⟨1838,by decide⟩,⟨345,by decide⟩] | 4 => ![⟨1810,by decide⟩,⟨1839,by decide⟩,⟨472,by decide⟩] | 5 => ![⟨1840,by decide⟩,⟨0,by decide⟩,⟨1770,by decide⟩] | 6 => ![⟨1841,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1842,by decide⟩,⟨0,by decide⟩]

def ntree14RRRRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRLLRL i else ntree14RRRRLLRR (i - 8)

def ntree14RRRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRRLLL i else ntree14RRRRLLR (i - 16)

def ntree14RRRRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1843,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1844,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1845,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1846,by decide⟩] | 4 => ![⟨1673,by decide⟩,⟨1673,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1311,by decide⟩,⟨1311,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨827,by decide⟩,⟨626,by decide⟩,⟨1847,by decide⟩] | _ => ![⟨1483,by decide⟩,⟨345,by decide⟩,⟨1848,by decide⟩]

def ntree14RRRRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1484,by decide⟩,⟨627,by decide⟩,⟨1849,by decide⟩] | 1 => ![⟨1486,by decide⟩,⟨630,by decide⟩,⟨1850,by decide⟩] | 2 => ![⟨1489,by decide⟩,⟨629,by decide⟩,⟨1851,by decide⟩] | 3 => ![⟨1490,by decide⟩,⟨631,by decide⟩,⟨1852,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨838,by decide⟩,⟨638,by decide⟩,⟨1853,by decide⟩] | 6 => ![⟨838,by decide⟩,⟨356,by decide⟩,⟨1854,by decide⟩] | _ => ![⟨840,by decide⟩,⟨639,by decide⟩,⟨1855,by decide⟩]

def ntree14RRRRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRLRLL i else ntree14RRRRLRLR (i - 8)

def ntree14RRRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1856,by decide⟩] | 1 => ![⟨838,by decide⟩,⟨644,by decide⟩,⟨1857,by decide⟩] | 2 => ![⟨857,by decide⟩,⟨647,by decide⟩,⟨1858,by decide⟩] | 3 => ![⟨838,by decide⟩,⟨356,by decide⟩,⟨1859,by decide⟩] | 4 => ![⟨827,by decide⟩,⟨645,by decide⟩,⟨1860,by decide⟩] | 5 => ![⟨827,by decide⟩,⟨648,by decide⟩,⟨1861,by decide⟩] | 6 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1862,by decide⟩] | _ => ![⟨837,by decide⟩,⟨649,by decide⟩,⟨1863,by decide⟩]

def ntree14RRRRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1497,by decide⟩,⟨356,by decide⟩,⟨1864,by decide⟩] | 1 => ![⟨1499,by decide⟩,⟨374,by decide⟩,⟨1865,by decide⟩] | 2 => ![⟨838,by decide⟩,⟨356,by decide⟩,⟨1866,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1867,by decide⟩]

def ntree14RRRRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1505,by decide⟩,⟨356,by decide⟩,⟨1868,by decide⟩] | 1 => ![⟨838,by decide⟩,⟨356,by decide⟩,⟨1869,by decide⟩] | 2 => ![⟨1507,by decide⟩,⟨386,by decide⟩,⟨1870,by decide⟩] | 3 => ![⟨1506,by decide⟩,⟨345,by decide⟩,⟨1871,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨1872,by decide⟩]

def ntree14RRRRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRRRLRRRL i else ntree14RRRRLRRRR (i - 4)

def ntree14RRRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRLRRL i else ntree14RRRRLRRR (i - 8)

def ntree14RRRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRRLRL i else ntree14RRRRLRR (i - 16)

def ntree14RRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14RRRRLL i else ntree14RRRRLR (i - 32)

def ntree14RRRRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1512,by decide⟩,⟨345,by decide⟩,⟨1873,by decide⟩] | 1 => ![⟨1513,by decide⟩,⟨355,by decide⟩,⟨1874,by decide⟩] | 2 => ![⟨56,by decide⟩,⟨1875,by decide⟩,⟨56,by decide⟩] | 3 => ![⟨1876,by decide⟩,⟨1876,by decide⟩,⟨16,by decide⟩] | 4 => ![⟨1877,by decide⟩,⟨1331,by decide⟩,⟨1523,by decide⟩] | 5 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨1878,by decide⟩] | 6 => ![⟨1522,by decide⟩,⟨671,by decide⟩,⟨1879,by decide⟩] | _ => ![⟨1523,by decide⟩,⟨672,by decide⟩,⟨1880,by decide⟩]

def ntree14RRRRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨1881,by decide⟩] | 1 => ![⟨1882,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 2 => ![⟨1693,by decide⟩,⟨1883,by decide⟩,⟨692,by decide⟩] | 3 => ![⟨1550,by decide⟩,⟨691,by decide⟩,⟨1884,by decide⟩] | 4 => ![⟨1551,by decide⟩,⟨692,by decide⟩,⟨1885,by decide⟩] | 5 => ![⟨1731,by decide⟩,⟨1886,by decide⟩,⟨710,by decide⟩] | 6 => ![⟨1567,by decide⟩,⟨710,by decide⟩,⟨1887,by decide⟩] | _ => ![⟨1737,by decide⟩,⟨1737,by decide⟩,⟨119,by decide⟩]

def ntree14RRRRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRRLLL i else ntree14RRRRRLLR (i - 8)

def ntree14RRRRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1196,by decide⟩,⟨1888,by decide⟩,⟨638,by decide⟩] | 1 => ![⟨1889,by decide⟩,⟨1196,by decide⟩,⟨1497,by decide⟩] | 2 => ![⟨1890,by decide⟩,⟨1729,by decide⟩,⟨1499,by decide⟩] | 3 => ![⟨1891,by decide⟩,⟨1731,by decide⟩,⟨1497,by decide⟩] | 4 => ![⟨1892,by decide⟩,⟨1892,by decide⟩,⟨56,by decide⟩] | 5 => ![⟨1893,by decide⟩,⟨1893,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1894,by decide⟩,⟨1894,by decide⟩,⟨60,by decide⟩] | _ => ![⟨1895,by decide⟩,⟨1895,by decide⟩,⟨8,by decide⟩]

def ntree14RRRRRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1896,by decide⟩,⟨1896,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨1897,by decide⟩,⟨1897,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1898,by decide⟩,⟨1892,by decide⟩,⟨1522,by decide⟩] | _ => ![⟨1899,by decide⟩,⟨1893,by decide⟩,⟨827,by decide⟩]

def ntree14RRRRRLRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1900,by decide⟩,⟨1196,by decide⟩,⟨1523,by decide⟩] | 1 => ![⟨1901,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1902,by decide⟩,⟨1894,by decide⟩,⟨1532,by decide⟩] | 3 => ![⟨1903,by decide⟩,⟨1892,by decide⟩,⟨1533,by decide⟩] | _ => ![⟨1904,by decide⟩,⟨1895,by decide⟩,⟨1486,by decide⟩]

def ntree14RRRRRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRRRRLRRL i else ntree14RRRRRLRRR (i - 4)

def ntree14RRRRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRRLRL i else ntree14RRRRRLRR (i - 8)

def ntree14RRRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRRRLL i else ntree14RRRRRLR (i - 16)

def ntree14RRRRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1905,by decide⟩,⟨1729,by decide⟩,⟨1534,by decide⟩] | 1 => ![⟨1906,by decide⟩,⟨1196,by decide⟩,⟨1535,by decide⟩] | 2 => ![⟨1907,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨1908,by decide⟩,⟨1896,by decide⟩,⟨1522,by decide⟩] | 4 => ![⟨1909,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 5 => ![⟨1910,by decide⟩,⟨1897,by decide⟩,⟨827,by decide⟩] | 6 => ![⟨1911,by decide⟩,⟨1893,by decide⟩,⟨903,by decide⟩] | _ => ![⟨1892,by decide⟩,⟨1912,by decide⟩,⟨691,by decide⟩]

def ntree14RRRRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1893,by decide⟩,⟨1913,by decide⟩,⟨345,by decide⟩] | 1 => ![⟨1196,by decide⟩,⟨1914,by decide⟩,⟨692,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1915,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1916,by decide⟩,⟨1892,by decide⟩,⟨1550,by decide⟩] | 4 => ![⟨1917,by decide⟩,⟨1893,by decide⟩,⟨1551,by decide⟩] | 5 => ![⟨1918,by decide⟩,⟨1451,by decide⟩,⟨1567,by decide⟩] | 6 => ![⟨1454,by decide⟩,⟨1454,by decide⟩,⟨254,by decide⟩] | _ => ![⟨1447,by decide⟩,⟨1919,by decide⟩,⟨639,by decide⟩]

def ntree14RRRRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRRRLL i else ntree14RRRRRRLR (i - 8)

def ntree14RRRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1451,by decide⟩,⟨1920,by decide⟩,⟨638,by decide⟩] | 1 => ![⟨1921,by decide⟩,⟨1921,by decide⟩,⟨58,by decide⟩] | 2 => ![⟨1922,by decide⟩,⟨1922,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨1923,by decide⟩,⟨1923,by decide⟩,⟨56,by decide⟩] | 4 => ![⟨1924,by decide⟩,⟨1924,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1892,by decide⟩,⟨1925,by decide⟩,⟨671,by decide⟩] | 6 => ![⟨1893,by decide⟩,⟨1926,by decide⟩,⟨672,by decide⟩] | _ => ![⟨1892,by decide⟩,⟨1927,by decide⟩,⟨699,by decide⟩]

def ntree14RRRRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨1921,by decide⟩,⟨1928,by decide⟩,⟨700,by decide⟩] | 1 => ![⟨1922,by decide⟩,⟨1929,by decide⟩,⟨629,by decide⟩] | 2 => ![⟨1196,by decide⟩,⟨1930,by decide⟩,⟨701,by decide⟩] | _ => ![⟨1447,by decide⟩,⟨1931,by decide⟩,⟨702,by decide⟩]

def ntree14RRRRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨2,by decide⟩,⟨1932,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨56,by decide⟩,⟨1933,by decide⟩,⟨56,by decide⟩] | 2 => ![⟨1923,by decide⟩,⟨1934,by decide⟩,⟨691,by decide⟩] | 3 => ![⟨1924,by decide⟩,⟨1935,by decide⟩,⟨345,by decide⟩] | _ => ![⟨1893,by decide⟩,⟨1936,by decide⟩,⟨451,by decide⟩]

def ntree14RRRRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14RRRRRRRRL i else ntree14RRRRRRRRR (i - 4)

def ntree14RRRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14RRRRRRRL i else ntree14RRRRRRRR (i - 8)

def ntree14RRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14RRRRRRL i else ntree14RRRRRRR (i - 16)

def ntree14RRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 33 then ntree14RRRRRL i else ntree14RRRRRR (i - 33)

def ntree14RRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14RRRRL i else ntree14RRRRR (i - 65)

def ntree14RRR (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14RRRL i else ntree14RRRR (i - 130)

def ntree14RR (i : Nat) : Fin 3 → Fin 1937 := if i < 261 then ntree14RRL i else ntree14RRR (i - 261)

def ntree14R (i : Nat) : Fin 3 → Fin 1937 := if i < 521 then ntree14RL i else ntree14RR (i - 521)

def ntree14 (i : Nat) : Fin 3 → Fin 1937 := if i < 1042 then ntree14L i else ntree14R (i - 1042)

def layer14 : Fin 1937 → State := fun i => stree14 i.val

def next14 : Fin 2085 → Fin 3 → Fin 1937 := fun i => ntree14 i.val

end Paper2.Certificates.Q6.Coverage

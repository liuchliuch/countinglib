import Paper2.Certificates.Q6CoverageCompact.Layer12Part006

namespace Paper2.Certificates.Q6.Coverage

def ntree12LLRLRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨4,by decide⟩,⟨440,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨441,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨442,by decide⟩,⟨8,by decide⟩,⟨439,by decide⟩] | 3 => ![⟨443,by decide⟩,⟨444,by decide⟩,⟨444,by decide⟩] | 4 => ![⟨445,by decide⟩,⟨446,by decide⟩,⟨446,by decide⟩] | _ => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨443,by decide⟩]

def ntree12LLRLRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨445,by decide⟩,⟨445,by decide⟩,⟨445,by decide⟩] | 1 => ![⟨447,by decide⟩,⟨448,by decide⟩,⟨444,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨449,by decide⟩,⟨443,by decide⟩] | 3 => ![⟨450,by decide⟩,⟨443,by decide⟩,⟨450,by decide⟩] | 4 => ![⟨439,by decide⟩,⟨23,by decide⟩,⟨439,by decide⟩] | _ => ![⟨443,by decide⟩,⟨451,by decide⟩,⟨451,by decide⟩]

def ntree12LLRLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRLRLL i else ntree12LLRLRLRLR (i - 6)

def ntree12LLRLRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨452,by decide⟩,⟨452,by decide⟩,⟨443,by decide⟩] | 1 => ![⟨430,by decide⟩,⟨453,by decide⟩,⟨30,by decide⟩] | 2 => ![⟨430,by decide⟩,⟨430,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨447,by decide⟩,⟨447,by decide⟩,⟨443,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨454,by decide⟩,⟨454,by decide⟩] | _ => ![⟨455,by decide⟩,⟨1,by decide⟩,⟨456,by decide⟩]

def ntree12LLRLRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨457,by decide⟩,⟨5,by decide⟩,⟨458,by decide⟩] | 1 => ![⟨455,by decide⟩,⟨433,by decide⟩,⟨459,by decide⟩] | 2 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨457,by decide⟩,⟨4,by decide⟩,⟨457,by decide⟩] | 4 => ![⟨460,by decide⟩,⟨42,by decide⟩,⟨460,by decide⟩] | _ => ![⟨0,by decide⟩,⟨461,by decide⟩,⟨461,by decide⟩]

def ntree12LLRLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRLRRL i else ntree12LLRLRLRRR (i - 6)

def ntree12LLRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLRLRL i else ntree12LLRLRLRR (i - 12)

def ntree12LLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRLRLL i else ntree12LLRLRLR (i - 24)

def ntree12LLRLRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨462,by decide⟩,⟨462,by decide⟩] | 1 => ![⟨463,by decide⟩,⟨21,by decide⟩,⟨456,by decide⟩] | 2 => ![⟨455,by decide⟩,⟨23,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨439,by decide⟩,⟨50,by decide⟩,⟨439,by decide⟩] | 4 => ![⟨460,by decide⟩,⟨51,by decide⟩,⟨460,by decide⟩] | _ => ![⟨464,by decide⟩,⟨464,by decide⟩,⟨0,by decide⟩]

def ntree12LLRLRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨465,by decide⟩,⟨465,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨464,by decide⟩,⟨466,by decide⟩,⟨30,by decide⟩] | 2 => ![⟨467,by decide⟩,⟨467,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨468,by decide⟩,⟨468,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨469,by decide⟩,⟨469,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨470,by decide⟩]

def ntree12LLRLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRRLLL i else ntree12LLRLRRLLR (i - 6)

def ntree12LLRLRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨471,by decide⟩,⟨30,by decide⟩,⟨472,by decide⟩] | 1 => ![⟨20,by decide⟩,⟨20,by decide⟩,⟨470,by decide⟩] | 2 => ![⟨471,by decide⟩,⟨0,by decide⟩,⟨471,by decide⟩] | 3 => ![⟨473,by decide⟩,⟨8,by decide⟩,⟨455,by decide⟩] | 4 => ![⟨474,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨475,by decide⟩,⟨12,by decide⟩,⟨457,by decide⟩]

def ntree12LLRLRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨476,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨477,by decide⟩,⟨61,by decide⟩,⟨460,by decide⟩] | 2 => ![⟨478,by decide⟩,⟨62,by decide⟩,⟨439,by decide⟩] | 3 => ![⟨479,by decide⟩,⟨480,by decide⟩,⟨480,by decide⟩] | 4 => ![⟨481,by decide⟩,⟨482,by decide⟩,⟨482,by decide⟩] | _ => ![⟨479,by decide⟩,⟨479,by decide⟩,⟨479,by decide⟩]

def ntree12LLRLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRRLRL i else ntree12LLRLRRLRR (i - 6)

def ntree12LLRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLRRLL i else ntree12LLRLRRLR (i - 12)

def ntree12LLRLRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨483,by decide⟩,⟨444,by decide⟩,⟨484,by decide⟩] | 1 => ![⟨483,by decide⟩,⟨443,by decide⟩,⟨483,by decide⟩] | 2 => ![⟨485,by decide⟩,⟨479,by decide⟩,⟨485,by decide⟩] | 3 => ![⟨481,by decide⟩,⟨481,by decide⟩,⟨481,by decide⟩] | 4 => ![⟨486,by decide⟩,⟨481,by decide⟩,⟨486,by decide⟩] | _ => ![⟨487,by decide⟩,⟨487,by decide⟩,⟨0,by decide⟩]

def ntree12LLRLRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨488,by decide⟩,⟨488,by decide⟩,⟨481,by decide⟩] | 1 => ![⟨487,by decide⟩,⟨489,by decide⟩,⟨30,by decide⟩] | 2 => ![⟨490,by decide⟩,⟨490,by decide⟩,⟨443,by decide⟩] | 3 => ![⟨491,by decide⟩,⟨491,by decide⟩,⟨479,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨492,by decide⟩] | _ => ![⟨493,by decide⟩,⟨8,by decide⟩,⟨471,by decide⟩]

def ntree12LLRLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRRRLL i else ntree12LLRLRRRLR (i - 6)

def ntree12LLRLRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨494,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨495,by decide⟩,⟨1,by decide⟩,⟨496,by decide⟩] | 2 => ![⟨497,by decide⟩,⟨9,by decide⟩,⟨496,by decide⟩] | 3 => ![⟨497,by decide⟩,⟨8,by decide⟩,⟨495,by decide⟩] | 4 => ![⟨495,by decide⟩,⟨0,by decide⟩,⟨495,by decide⟩] | _ => ![⟨498,by decide⟩,⟨499,by decide⟩,⟨499,by decide⟩]

def ntree12LLRLRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨500,by decide⟩,⟨501,by decide⟩,⟨499,by decide⟩] | 1 => ![⟨502,by decide⟩,⟨503,by decide⟩,⟨499,by decide⟩] | 2 => ![⟨502,by decide⟩,⟨502,by decide⟩,⟨498,by decide⟩] | 3 => ![⟨498,by decide⟩,⟨498,by decide⟩,⟨498,by decide⟩] | 4 => ![⟨502,by decide⟩,⟨504,by decide⟩,⟨505,by decide⟩] | 5 => ![⟨498,by decide⟩,⟨505,by decide⟩,⟨505,by decide⟩] | _ => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩]

def ntree12LLRLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRRRRL i else ntree12LLRLRRRRR (i - 6)

def ntree12LLRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLRRRL i else ntree12LLRLRRRR (i - 12)

def ntree12LLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRLRRL i else ntree12LLRLRRR (i - 24)

def ntree12LLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LLRLRL i else ntree12LLRLRR (i - 48)

def ntree12LLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LLRLL i else ntree12LLRLR (i - 97)

def ntree12LLRRLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨507,by decide⟩] | 1 => ![⟨439,by decide⟩,⟨506,by decide⟩,⟨508,by decide⟩] | 2 => ![⟨509,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨510,by decide⟩,⟨0,by decide⟩,⟨439,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨511,by decide⟩,⟨506,by decide⟩] | _ => ![⟨8,by decide⟩,⟨512,by decide⟩,⟨506,by decide⟩]

def ntree12LLRRLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨507,by decide⟩] | 1 => ![⟨442,by decide⟩,⟨512,by decide⟩,⟨508,by decide⟩] | 2 => ![⟨513,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 3 => ![⟨515,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨515,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨516,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLLLLL i else ntree12LLRRLLLLR (i - 6)

def ntree12LLRRLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨513,by decide⟩,⟨513,by decide⟩,⟨513,by decide⟩] | 1 => ![⟨517,by decide⟩,⟨518,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨517,by decide⟩,⟨517,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨517,by decide⟩,⟨519,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨520,by decide⟩,⟨0,by decide⟩] | _ => ![⟨439,by decide⟩,⟨520,by decide⟩,⟨439,by decide⟩]

def ntree12LLRRLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨521,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨522,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨523,by decide⟩,⟨523,by decide⟩] | 3 => ![⟨430,by decide⟩,⟨524,by decide⟩,⟨506,by decide⟩] | 4 => ![⟨86,by decide⟩,⟨525,by decide⟩,⟨525,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨526,by decide⟩]

def ntree12LLRRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLLLRL i else ntree12LLRRLLLRR (i - 6)

def ntree12LLRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRLLLL i else ntree12LLRRLLLR (i - 12)

def ntree12LLRRLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨527,by decide⟩,⟨43,by decide⟩,⟨528,by decide⟩] | 2 => ![⟨527,by decide⟩,⟨42,by decide⟩,⟨527,by decide⟩] | 3 => ![⟨529,by decide⟩,⟨499,by decide⟩,⟨530,by decide⟩] | 4 => ![⟨531,by decide⟩,⟨1,by decide⟩,⟨532,by decide⟩] | _ => ![⟨529,by decide⟩,⟨498,by decide⟩,⟨529,by decide⟩]

def ntree12LLRRLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨533,by decide⟩] | 1 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨534,by decide⟩] | 2 => ![⟨42,by decide⟩,⟨535,by decide⟩,⟨535,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨536,by decide⟩,⟨537,by decide⟩] | 4 => ![⟨460,by decide⟩,⟨535,by decide⟩,⟨538,by decide⟩] | _ => ![⟨0,by decide⟩,⟨536,by decide⟩,⟨536,by decide⟩]

def ntree12LLRRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLLRLL i else ntree12LLRRLLRLR (i - 6)

def ntree12LLRRLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨531,by decide⟩,⟨0,by decide⟩,⟨531,by decide⟩] | 1 => ![⟨539,by decide⟩,⟨0,by decide⟩,⟨539,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨540,by decide⟩,⟨540,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨541,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨542,by decide⟩,⟨506,by decide⟩,⟨543,by decide⟩] | _ => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩]

def ntree12LLRRLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨542,by decide⟩,⟨0,by decide⟩,⟨542,by decide⟩] | 1 => ![⟨544,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨545,by decide⟩,⟨1,by decide⟩,⟨456,by decide⟩] | 3 => ![⟨546,by decide⟩,⟨9,by decide⟩,⟨532,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨533,by decide⟩] | _ => ![⟨473,by decide⟩,⟨8,by decide⟩,⟨534,by decide⟩]

def ntree12LLRRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLLRRL i else ntree12LLRRLLRRR (i - 6)

def ntree12LLRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRLLRL i else ntree12LLRRLLRR (i - 12)

def ntree12LLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRRLLL i else ntree12LLRRLLR (i - 24)

def ntree12LLRRLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨474,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨547,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 3 => ![⟨548,by decide⟩,⟨0,by decide⟩,⟨455,by decide⟩] | 4 => ![⟨549,by decide⟩,⟨42,by decide⟩,⟨460,by decide⟩] | _ => ![⟨544,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨550,by decide⟩,⟨0,by decide⟩,⟨439,by decide⟩] | 1 => ![⟨546,by decide⟩,⟨8,by decide⟩,⟨531,by decide⟩] | 2 => ![⟨551,by decide⟩,⟨8,by decide⟩,⟨539,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨552,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨544,by decide⟩,⟨0,by decide⟩,⟨470,by decide⟩] | _ => ![⟨426,by decide⟩,⟨426,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLRLLL i else ntree12LLRRLRLLR (i - 6)

def ntree12LLRRLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨4,by decide⟩,⟨553,by decide⟩,⟨553,by decide⟩] | 1 => ![⟨428,by decide⟩,⟨428,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨554,by decide⟩,⟨554,by decide⟩] | 3 => ![⟨12,by decide⟩,⟨555,by decide⟩,⟨553,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨556,by decide⟩,⟨554,by decide⟩] | _ => ![⟨557,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩]

def ntree12LLRRLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨557,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨558,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨559,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨560,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨561,by decide⟩,⟨0,by decide⟩] | _ => ![⟨562,by decide⟩,⟨443,by decide⟩,⟨562,by decide⟩]

def ntree12LLRRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLRLRL i else ntree12LLRRLRLRR (i - 6)

def ntree12LLRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRLRLL i else ntree12LLRRLRLR (i - 12)

def ntree12LLRRLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨563,by decide⟩,⟨0,by decide⟩,⟨563,by decide⟩] | 1 => ![⟨443,by decide⟩,⟨564,by decide⟩,⟨564,by decide⟩] | 2 => ![⟨38,by decide⟩,⟨565,by decide⟩,⟨565,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨566,by decide⟩] | 4 => ![⟨567,by decide⟩,⟨506,by decide⟩,⟨568,by decide⟩] | _ => ![⟨567,by decide⟩,⟨0,by decide⟩,⟨567,by decide⟩]

def ntree12LLRRLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨569,by decide⟩,⟨4,by decide⟩,⟨569,by decide⟩] | 1 => ![⟨46,by decide⟩,⟨570,by decide⟩,⟨570,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨571,by decide⟩,⟨571,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨572,by decide⟩,⟨572,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨573,by decide⟩,⟨573,by decide⟩] | _ => ![⟨574,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLRRLL i else ntree12LLRRLRRLR (i - 6)

def ntree12LLRRLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨575,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨576,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨567,by decide⟩,⟨99,by decide⟩,⟨567,by decide⟩] | 4 => ![⟨577,by decide⟩,⟨464,by decide⟩,⟨495,by decide⟩] | _ => ![⟨578,by decide⟩,⟨467,by decide⟩,⟨495,by decide⟩]

def ntree12LLRRLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨579,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨580,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨464,by decide⟩,⟨581,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨582,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨583,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 5 => ![⟨584,by decide⟩,⟨8,by decide⟩,⟨567,by decide⟩] | _ => ![⟨585,by decide⟩,⟨12,by decide⟩,⟨569,by decide⟩]

def ntree12LLRRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRLRRRL i else ntree12LLRRLRRRR (i - 6)

def ntree12LLRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRLRRL i else ntree12LLRRLRRR (i - 12)

def ntree12LLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRRLRL i else ntree12LLRRLRR (i - 24)

def ntree12LLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LLRRLL i else ntree12LLRRLR (i - 48)

def ntree12LLRRRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨586,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 1 => ![⟨587,by decide⟩,⟨46,by decide⟩,⟨46,by decide⟩] | 2 => ![⟨588,by decide⟩,⟨481,by decide⟩,⟨588,by decide⟩] | 3 => ![⟨589,by decide⟩,⟨590,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨591,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | _ => ![⟨591,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨592,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨593,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨594,by decide⟩] | 4 => ![⟨593,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨589,by decide⟩,⟨589,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRLLLL i else ntree12LLRRRLLLR (i - 6)

def ntree12LLRRRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨595,by decide⟩,⟨596,by decide⟩,⟨444,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨597,by decide⟩,⟨443,by decide⟩] | 3 => ![⟨598,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨599,by decide⟩,⟨444,by decide⟩,⟨444,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨443,by decide⟩] | 1 => ![⟨598,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨599,by decide⟩,⟨443,by decide⟩,⟨443,by decide⟩] | 3 => ![⟨138,by decide⟩,⟨600,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨595,by decide⟩,⟨595,by decide⟩,⟨443,by decide⟩] | _ => ![⟨138,by decide⟩,⟨138,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRLLRL i else ntree12LLRRRLLRR (i - 6)

def ntree12LLRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRRLLL i else ntree12LLRRRLLR (i - 12)

def ntree12LLRRRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨601,by decide⟩,⟨8,by decide⟩,⟨602,by decide⟩] | 1 => ![⟨603,by decide⟩,⟨1,by decide⟩,⟨604,by decide⟩] | 2 => ![⟨605,by decide⟩,⟨606,by decide⟩,⟨606,by decide⟩] | 3 => ![⟨603,by decide⟩,⟨0,by decide⟩,⟨603,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨607,by decide⟩,⟨607,by decide⟩] | _ => ![⟨471,by decide⟩,⟨1,by decide⟩,⟨608,by decide⟩]

def ntree12LLRRRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨594,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨609,by decide⟩] | 2 => ![⟨610,by decide⟩,⟨0,by decide⟩,⟨610,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨186,by decide⟩] | 4 => ![⟨611,by decide⟩,⟨0,by decide⟩,⟨611,by decide⟩] | _ => ![⟨605,by decide⟩,⟨605,by decide⟩,⟨605,by decide⟩]

def ntree12LLRRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRLRLL i else ntree12LLRRRLRLR (i - 6)

def ntree12LLRRRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨612,by decide⟩,⟨139,by decide⟩,⟨604,by decide⟩] | 1 => ![⟨603,by decide⟩,⟨147,by decide⟩,⟨603,by decide⟩] | 2 => ![⟨613,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 3 => ![⟨614,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨615,by decide⟩,⟨138,by decide⟩,⟨471,by decide⟩] | _ => ![⟨138,by decide⟩,⟨138,by decide⟩,⟨609,by decide⟩]

def ntree12LLRRRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨464,by decide⟩,⟨464,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨616,by decide⟩,⟨616,by decide⟩,⟨605,by decide⟩] | 2 => ![⟨617,by decide⟩,⟨464,by decide⟩,⟨610,by decide⟩] | 3 => ![⟨618,by decide⟩,⟨465,by decide⟩,⟨611,by decide⟩] | 4 => ![⟨619,by decide⟩,⟨62,by decide⟩,⟨603,by decide⟩] | 5 => ![⟨620,by decide⟩,⟨444,by decide⟩,⟨621,by decide⟩] | _ => ![⟨620,by decide⟩,⟨443,by decide⟩,⟨620,by decide⟩]

def ntree12LLRRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRLRRL i else ntree12LLRRRLRRR (i - 6)

def ntree12LLRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRRLRL i else ntree12LLRRRLRR (i - 12)

def ntree12LLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRRRLL i else ntree12LLRRRLR (i - 24)

def ntree12LLRRRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨622,by decide⟩] | 1 => ![⟨487,by decide⟩,⟨487,by decide⟩,⟨198,by decide⟩] | 2 => ![⟨623,by decide⟩,⟨499,by decide⟩,⟨499,by decide⟩] | 3 => ![⟨623,by decide⟩,⟨498,by decide⟩,⟨498,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨204,by decide⟩,⟨0,by decide⟩] | _ => ![⟨589,by decide⟩,⟨624,by decide⟩,⟨506,by decide⟩]

def ntree12LLRRRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨625,by decide⟩,⟨1,by decide⟩,⟨626,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨627,by decide⟩,⟨518,by decide⟩,⟨626,by decide⟩] | 4 => ![⟨517,by decide⟩,⟨517,by decide⟩,⟨217,by decide⟩] | _ => ![⟨598,by decide⟩,⟨520,by decide⟩,⟨217,by decide⟩]

def ntree12LLRRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRRLLL i else ntree12LLRRRRLLR (i - 6)

def ntree12LLRRRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨526,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨598,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨601,by decide⟩,⟨512,by decide⟩,⟨628,by decide⟩] | 4 => ![⟨629,by decide⟩,⟨218,by decide⟩,⟨218,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨218,by decide⟩,⟨630,by decide⟩,⟨630,by decide⟩] | 1 => ![⟨631,by decide⟩,⟨632,by decide⟩,⟨632,by decide⟩] | 2 => ![⟨498,by decide⟩,⟨633,by decide⟩,⟨633,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨634,by decide⟩] | 4 => ![⟨605,by decide⟩,⟨635,by decide⟩,⟨635,by decide⟩] | _ => ![⟨636,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRRLRL i else ntree12LLRRRRLRR (i - 6)

def ntree12LLRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRRRLL i else ntree12LLRRRRLR (i - 12)

def ntree12LLRRRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨637,by decide⟩,⟨237,by decide⟩,⟨532,by decide⟩] | 1 => ![⟨236,by decide⟩,⟨236,by decide⟩,⟨533,by decide⟩] | 2 => ![⟨637,by decide⟩,⟨236,by decide⟩,⟨531,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨609,by decide⟩] | 4 => ![⟨236,by decide⟩,⟨638,by decide⟩,⟨506,by decide⟩] | _ => ![⟨613,by decide⟩,⟨535,by decide⟩,⟨535,by decide⟩]

def ntree12LLRRRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨614,by decide⟩,⟨536,by decide⟩,⟨536,by decide⟩] | 1 => ![⟨639,by decide⟩,⟨228,by decide⟩,⟨228,by decide⟩] | 2 => ![⟨591,by decide⟩,⟨231,by decide⟩,⟨231,by decide⟩] | 3 => ![⟨544,by decide⟩,⟨250,by decide⟩,⟨609,by decide⟩] | 4 => ![⟨544,by decide⟩,⟨231,by decide⟩,⟨231,by decide⟩] | _ => ![⟨640,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRRRLL i else ntree12LLRRRRRLR (i - 6)

def ntree12LLRRRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨641,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨640,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨625,by decide⟩,⟨0,by decide⟩,⟨625,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRRRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨443,by decide⟩] | 1 => ![⟨625,by decide⟩,⟨520,by decide⟩,⟨625,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨138,by decide⟩,⟨642,by decide⟩,⟨643,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨644,by decide⟩,⟨644,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨645,by decide⟩,⟨645,by decide⟩] | _ => ![⟨443,by decide⟩,⟨646,by decide⟩,⟨646,by decide⟩]

def ntree12LLRRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRRRRRRL i else ntree12LLRRRRRRR (i - 6)

def ntree12LLRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRRRRRL i else ntree12LLRRRRRR (i - 12)

def ntree12LLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRRRRL i else ntree12LLRRRRR (i - 24)

def ntree12LLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 49 then ntree12LLRRRL i else ntree12LLRRRR (i - 49)

def ntree12LLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LLRRL i else ntree12LLRRR (i - 97)

def ntree12LLR (i : Nat) : Fin 3 → Fin 2396 := if i < 194 then ntree12LLRL i else ntree12LLRR (i - 194)

def ntree12LL (i : Nat) : Fin 3 → Fin 2396 := if i < 388 then ntree12LLL i else ntree12LLR (i - 388)

def ntree12LRLLLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨647,by decide⟩] | 1 => ![⟨648,by decide⟩,⟨138,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨138,by decide⟩,⟨281,by decide⟩,⟨114,by decide⟩] | 3 => ![⟨138,by decide⟩,⟨649,by decide⟩,⟨506,by decide⟩] | 4 => ![⟨595,by decide⟩,⟨650,by decide⟩,⟨564,by decide⟩] | _ => ![⟨443,by decide⟩,⟨651,by decide⟩,⟨443,by decide⟩]

def ntree12LRLLLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨158,by decide⟩,⟨652,by decide⟩,⟨653,by decide⟩] | 1 => ![⟨138,by decide⟩,⟨654,by decide⟩,⟨506,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨655,by decide⟩,⟨644,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨656,by decide⟩,⟨645,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨657,by decide⟩,⟨443,by decide⟩] | _ => ![⟨452,by decide⟩,⟨658,by decide⟩,⟨646,by decide⟩]

def ntree12LRLLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLLLLL i else ntree12LRLLLLLLR (i - 6)

def ntree12LRLLLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨659,by decide⟩,⟨659,by decide⟩] | 1 => ![⟨660,by decide⟩,⟨0,by decide⟩,⟨660,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨661,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨662,by decide⟩,⟨662,by decide⟩] | 4 => ![⟨531,by decide⟩,⟨288,by decide⟩,⟨531,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LRLLLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨663,by decide⟩,⟨138,by decide⟩,⟨531,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨664,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨178,by decide⟩,⟨665,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨666,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨667,by decide⟩,⟨0,by decide⟩] | _ => ![⟨469,by decide⟩,⟨668,by decide⟩,⟨231,by decide⟩]

def ntree12LRLLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLLLRL i else ntree12LRLLLLLRR (i - 6)

def ntree12LRLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLLLLL i else ntree12LRLLLLLR (i - 12)

def ntree12LRLLLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨138,by decide⟩,⟨669,by decide⟩,⟨536,by decide⟩] | 1 => ![⟨172,by decide⟩,⟨670,by decide⟩,⟨535,by decide⟩] | 2 => ![⟨138,by decide⟩,⟨671,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨672,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | _ => ![⟨464,by decide⟩,⟨581,by decide⟩,⟨506,by decide⟩]

def ntree12LRLLLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨138,by decide⟩,⟨673,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨616,by decide⟩,⟨674,by decide⟩,⟨635,by decide⟩] | 2 => ![⟨465,by decide⟩,⟨675,by decide⟩,⟨231,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨676,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨467,by decide⟩,⟨677,by decide⟩,⟨231,by decide⟩] | _ => ![⟨468,by decide⟩,⟨678,by decide⟩,⟨235,by decide⟩]

def ntree12LRLLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLLRLL i else ntree12LRLLLLRLR (i - 6)

def ntree12LRLLLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨640,by decide⟩,⟨0,by decide⟩,⟨609,by decide⟩] | 1 => ![⟨679,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨625,by decide⟩,⟨0,by decide⟩,⟨680,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨681,by decide⟩,⟨681,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨682,by decide⟩,⟨682,by decide⟩] | _ => ![⟨0,by decide⟩,⟨683,by decide⟩,⟨683,by decide⟩]

def ntree12LRLLLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨481,by decide⟩,⟨684,by decide⟩,⟨684,by decide⟩] | 1 => ![⟨42,by decide⟩,⟨685,by decide⟩,⟨685,by decide⟩] | 2 => ![⟨479,by decide⟩,⟨686,by decide⟩,⟨686,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨687,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨688,by decide⟩,⟨443,by decide⟩] | _ => ![⟨8,by decide⟩,⟨689,by decide⟩,⟨681,by decide⟩]

def ntree12LRLLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLLRRL i else ntree12LRLLLLRRR (i - 6)

def ntree12LRLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLLLRL i else ntree12LRLLLLRR (i - 12)

def ntree12LRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLLLLL i else ntree12LRLLLLR (i - 24)

def ntree12LRLLLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨452,by decide⟩,⟨690,by decide⟩,⟨682,by decide⟩] | 1 => ![⟨42,by decide⟩,⟨691,by decide⟩,⟨42,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨692,by decide⟩,⟨443,by decide⟩] | 3 => ![⟨479,by decide⟩,⟨693,by decide⟩,⟨479,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨694,by decide⟩,⟨683,by decide⟩] | _ => ![⟨487,by decide⟩,⟨695,by decide⟩,⟨231,by decide⟩]

def ntree12LRLLLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨488,by decide⟩,⟨696,by decide⟩,⟨684,by decide⟩] | 1 => ![⟨61,by decide⟩,⟨697,by decide⟩,⟨685,by decide⟩] | 2 => ![⟨490,by decide⟩,⟨698,by decide⟩,⟨682,by decide⟩] | 3 => ![⟨491,by decide⟩,⟨699,by decide⟩,⟨686,by decide⟩] | 4 => ![⟨700,by decide⟩,⟨700,by decide⟩,⟨0,by decide⟩] | _ => ![⟨701,by decide⟩,⟨701,by decide⟩,⟨4,by decide⟩]

def ntree12LRLLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLRLLL i else ntree12LRLLLRLLR (i - 6)

def ntree12LRLLLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨702,by decide⟩,⟨702,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨703,by decide⟩] | 2 => ![⟨700,by decide⟩,⟨704,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨705,by decide⟩,⟨705,by decide⟩,⟨443,by decide⟩] | 4 => ![⟨706,by decide⟩,⟨706,by decide⟩,⟨445,by decide⟩] | _ => ![⟨707,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩]

def ntree12LRLLLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨708,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨307,by decide⟩,⟨709,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨439,by decide⟩,⟨0,by decide⟩,⟨710,by decide⟩] | 3 => ![⟨711,by decide⟩,⟨138,by decide⟩,⟨439,by decide⟩] | 4 => ![⟨308,by decide⟩,⟨712,by decide⟩,⟨4,by decide⟩] | _ => ![⟨138,by decide⟩,⟨713,by decide⟩,⟨0,by decide⟩]

def ntree12LRLLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLRLRL i else ntree12LRLLLRLRR (i - 6)

def ntree12LRLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLLRLL i else ntree12LRLLLRLR (i - 12)

def ntree12LRLLLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨705,by decide⟩,⟨714,by decide⟩,⟨443,by decide⟩] | 1 => ![⟨443,by decide⟩,⟨715,by decide⟩,⟨715,by decide⟩] | 2 => ![⟨598,by decide⟩,⟨326,by decide⟩,⟨716,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨717,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨718,by decide⟩] | _ => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨719,by decide⟩]

def ntree12LRLLLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨720,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨703,by decide⟩] | 2 => ![⟨439,by decide⟩,⟨0,by decide⟩,⟨721,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨722,by decide⟩] | 4 => ![⟨307,by decide⟩,⟨307,by decide⟩,⟨609,by decide⟩] | _ => ![⟨308,by decide⟩,⟨308,by decide⟩,⟨719,by decide⟩]

def ntree12LRLLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLRRLL i else ntree12LRLLLRRLR (i - 6)

def ntree12LRLLLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨307,by decide⟩,⟨307,by decide⟩,⟨720,by decide⟩] | 1 => ![⟨723,by decide⟩,⟨178,by decide⟩,⟨455,by decide⟩] | 2 => ![⟨724,by decide⟩,⟨307,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨725,by decide⟩,⟨46,by decide⟩,⟨46,by decide⟩] | 4 => ![⟨726,by decide⟩,⟨308,by decide⟩,⟨457,by decide⟩] | _ => ![⟨727,by decide⟩,⟨172,by decide⟩,⟨460,by decide⟩]

def ntree12LRLLLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨711,by decide⟩,⟨343,by decide⟩,⟨721,by decide⟩] | 1 => ![⟨724,by decide⟩,⟨318,by decide⟩,⟨722,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨728,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨729,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨730,by decide⟩] | 5 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨731,by decide⟩] | _ => ![⟨460,by decide⟩,⟨42,by decide⟩,⟨732,by decide⟩]

def ntree12LRLLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLLRRRL i else ntree12LRLLLRRRR (i - 6)

def ntree12LRLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLLRRL i else ntree12LRLLLRRR (i - 12)

def ntree12LRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLLLRL i else ntree12LRLLLRR (i - 24)

def ntree12LRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LRLLLL i else ntree12LRLLLR (i - 48)

def ntree12LRLLRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨450,by decide⟩,⟨443,by decide⟩,⟨733,by decide⟩] | 1 => ![⟨439,by decide⟩,⟨0,by decide⟩,⟨734,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨735,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨736,by decide⟩,⟨736,by decide⟩] | 4 => ![⟨737,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨495,by decide⟩,⟨303,by decide⟩,⟨495,by decide⟩]

def ntree12LRLLRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨738,by decide⟩,⟨738,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨739,by decide⟩,⟨738,by decide⟩,⟨495,by decide⟩] | 2 => ![⟨738,by decide⟩,⟨740,by decide⟩,⟨736,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨741,by decide⟩] | 4 => ![⟨498,by decide⟩,⟨742,by decide⟩,⟨498,by decide⟩] | _ => ![⟨498,by decide⟩,⟨743,by decide⟩,⟨498,by decide⟩]

def ntree12LRLLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRLLLL i else ntree12LRLLRLLLR (i - 6)

def ntree12LRLLRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨744,by decide⟩,⟨738,by decide⟩,⟨439,by decide⟩] | 1 => ![⟨439,by decide⟩,⟨208,by decide⟩,⟨745,by decide⟩] | 2 => ![⟨738,by decide⟩,⟨746,by decide⟩,⟨208,by decide⟩] | 3 => ![⟨747,by decide⟩,⟨747,by decide⟩,⟨513,by decide⟩] | 4 => ![⟨748,by decide⟩,⟨748,by decide⟩,⟨513,by decide⟩] | _ => ![⟨307,by decide⟩,⟨749,by decide⟩,⟨0,by decide⟩]

def ntree12LRLLRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨750,by decide⟩,⟨738,by decide⟩,⟨83,by decide⟩] | 1 => ![⟨495,by decide⟩,⟨328,by decide⟩,⟨751,by decide⟩] | 2 => ![⟨752,by decide⟩,⟨86,by decide⟩,⟨86,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨753,by decide⟩,⟨753,by decide⟩] | 4 => ![⟨495,by decide⟩,⟨753,by decide⟩,⟨754,by decide⟩] | _ => ![⟨42,by decide⟩,⟨755,by decide⟩,⟨755,by decide⟩]

def ntree12LRLLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRLLRL i else ntree12LRLLRLLRR (i - 6)

def ntree12LRLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLRLLL i else ntree12LRLLRLLR (i - 12)

def ntree12LRLLRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨756,by decide⟩] | 1 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨757,by decide⟩] | 2 => ![⟨498,by decide⟩,⟨758,by decide⟩,⟨758,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨753,by decide⟩,⟨759,by decide⟩] | 4 => ![⟨455,by decide⟩,⟨231,by decide⟩,⟨760,by decide⟩] | _ => ![⟨439,by decide⟩,⟨231,by decide⟩,⟨761,by decide⟩]

def ntree12LRLLRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨460,by decide⟩,⟨235,by decide⟩,⟨762,by decide⟩] | 1 => ![⟨212,by decide⟩,⟨212,by decide⟩,⟨756,by decide⟩] | 2 => ![⟨763,by decide⟩,⟨236,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨598,by decide⟩,⟨99,by decide⟩,⟨756,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨764,by decide⟩,⟨0,by decide⟩] | _ => ![⟨765,by decide⟩,⟨766,by decide⟩,⟨0,by decide⟩]

def ntree12LRLLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRLRLL i else ntree12LRLLRLRLR (i - 6)

def ntree12LRLLRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨598,by decide⟩,⟨753,by decide⟩,⟨753,by decide⟩] | 1 => ![⟨766,by decide⟩,⟨766,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨737,by decide⟩,⟨0,by decide⟩,⟨609,by decide⟩] | 3 => ![⟨767,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨591,by decide⟩,⟨0,by decide⟩,⟨756,by decide⟩] | _ => ![⟨768,by decide⟩,⟨303,by decide⟩,⟨756,by decide⟩]

def ntree12LRLLRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨455,by decide⟩] | 1 => ![⟨737,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨769,by decide⟩,⟨388,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨531,by decide⟩,⟨303,by decide⟩,⟨531,by decide⟩] | 4 => ![⟨455,by decide⟩,⟨770,by decide⟩,⟨771,by decide⟩] | _ => ![⟨0,by decide⟩,⟨772,by decide⟩,⟨772,by decide⟩]

def ntree12LRLLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRLRRL i else ntree12LRLLRLRRR (i - 6)

def ntree12LRLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLRLRL i else ntree12LRLLRLRR (i - 12)

def ntree12LRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLLRLL i else ntree12LRLLRLR (i - 24)

def ntree12LRLLRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨773,by decide⟩,⟨773,by decide⟩] | 1 => ![⟨513,by decide⟩,⟨774,by decide⟩,⟨774,by decide⟩] | 2 => ![⟨768,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨775,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨776,by decide⟩,⟨700,by decide⟩,⟨495,by decide⟩] | _ => ![⟨777,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩]

def ntree12LRLLRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨495,by decide⟩,⟨397,by decide⟩,⟨778,by decide⟩] | 1 => ![⟨443,by decide⟩,⟨779,by decide⟩,⟨779,by decide⟩] | 2 => ![⟨138,by decide⟩,⟨403,by decide⟩,⟨397,by decide⟩] | 3 => ![⟨780,by decide⟩,⟨138,by decide⟩,⟨563,by decide⟩] | 4 => ![⟨737,by decide⟩,⟨397,by decide⟩,⟨397,by decide⟩] | _ => ![⟨4,by decide⟩,⟨781,by decide⟩,⟨781,by decide⟩]

def ntree12LRLLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRRLLL i else ntree12LRLLRRLLR (i - 6)

def ntree12LRLLRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨782,by decide⟩] | 1 => ![⟨138,by decide⟩,⟨783,by decide⟩,⟨753,by decide⟩] | 2 => ![⟨777,by decide⟩,⟨4,by decide⟩,⟨719,by decide⟩] | 3 => ![⟨737,by decide⟩,⟨0,by decide⟩,⟨720,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨784,by decide⟩,⟨784,by decide⟩] | _ => ![⟨443,by decide⟩,⟨785,by decide⟩,⟨785,by decide⟩]

def ntree12LRLLRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨4,by decide⟩,⟨786,by decide⟩,⟨786,by decide⟩] | 1 => ![⟨445,by decide⟩,⟨787,by decide⟩,⟨787,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨788,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨789,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨441,by decide⟩,⟨788,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨788,by decide⟩]

def ntree12LRLLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRRLRL i else ntree12LRLLRRLRR (i - 6)

def ntree12LRLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLRRLL i else ntree12LRLLRRLR (i - 12)

def ntree12LRLLRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨12,by decide⟩,⟨12,by decide⟩,⟨789,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨790,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨791,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨792,by decide⟩,⟨793,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨794,by decide⟩,⟨795,by decide⟩] | _ => ![⟨0,by decide⟩,⟨793,by decide⟩,⟨793,by decide⟩]

def ntree12LRLLRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨2,by decide⟩,⟨795,by decide⟩,⟨795,by decide⟩] | 1 => ![⟨796,by decide⟩,⟨796,by decide⟩,⟨443,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨23,by decide⟩,⟨0,by decide⟩] | _ => ![⟨16,by decide⟩,⟨797,by decide⟩,⟨793,by decide⟩]

def ntree12LRLLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRRRLL i else ntree12LRLLRRRLR (i - 6)

def ntree12LRLLRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨443,by decide⟩,⟨798,by decide⟩,⟨798,by decide⟩] | 1 => ![⟨799,by decide⟩,⟨799,by decide⟩,⟨799,by decide⟩] | 2 => ![⟨800,by decide⟩,⟨800,by decide⟩,⟨799,by decide⟩] | 3 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨801,by decide⟩] | 4 => ![⟨799,by decide⟩,⟨802,by decide⟩,⟨802,by decide⟩] | _ => ![⟨0,by decide⟩,⟨803,by decide⟩,⟨803,by decide⟩]

def ntree12LRLLRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨2,by decide⟩,⟨804,by decide⟩,⟨804,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨805,by decide⟩,⟨805,by decide⟩] | 2 => ![⟨455,by decide⟩,⟨806,by decide⟩,⟨807,by decide⟩] | 3 => ![⟨808,by decide⟩,⟨808,by decide⟩,⟨809,by decide⟩] | 4 => ![⟨810,by decide⟩,⟨0,by decide⟩,⟨810,by decide⟩] | 5 => ![⟨811,by decide⟩,⟨2,by decide⟩,⟨811,by decide⟩] | _ => ![⟨812,by decide⟩,⟨4,by decide⟩,⟨812,by decide⟩]

def ntree12LRLLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLLRRRRL i else ntree12LRLLRRRRR (i - 6)

def ntree12LRLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLLRRRL i else ntree12LRLLRRRR (i - 12)

def ntree12LRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLLRRL i else ntree12LRLLRRR (i - 24)

def ntree12LRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LRLLRL i else ntree12LRLLRR (i - 48)

def ntree12LRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LRLLL i else ntree12LRLLR (i - 97)

def ntree12LRLRLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨813,by decide⟩,⟨6,by decide⟩,⟨813,by decide⟩] | 1 => ![⟨810,by decide⟩,⟨793,by decide⟩,⟨814,by decide⟩] | 2 => ![⟨811,by decide⟩,⟨795,by decide⟩,⟨815,by decide⟩] | 3 => ![⟨812,by decide⟩,⟨435,by decide⟩,⟨816,by decide⟩] | 4 => ![⟨810,by decide⟩,⟨437,by decide⟩,⟨817,by decide⟩] | _ => ![⟨0,by decide⟩,⟨818,by decide⟩,⟨0,by decide⟩]

def ntree12LRLRLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨819,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨820,by decide⟩,⟨820,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨808,by decide⟩,⟨808,by decide⟩,⟨808,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨821,by decide⟩,⟨0,by decide⟩] | _ => ![⟨455,by decide⟩,⟨793,by decide⟩,⟨822,by decide⟩]

def ntree12LRLRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLLLLL i else ntree12LRLRLLLLR (i - 6)

def ntree12LRLRLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨52,by decide⟩,⟨793,by decide⟩,⟨793,by decide⟩] | 1 => ![⟨823,by decide⟩,⟨820,by decide⟩,⟨455,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨824,by decide⟩,⟨824,by decide⟩] | 3 => ![⟨825,by decide⟩,⟨825,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨57,by decide⟩,⟨57,by decide⟩,⟨788,by decide⟩] | _ => ![⟨826,by decide⟩,⟨0,by decide⟩,⟨826,by decide⟩]

def ntree12LRLRLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨827,by decide⟩,⟨2,by decide⟩,⟨827,by decide⟩] | 1 => ![⟨826,by decide⟩,⟨433,by decide⟩,⟨828,by decide⟩] | 2 => ![⟨60,by decide⟩,⟨433,by decide⟩,⟨433,by decide⟩] | 3 => ![⟨829,by decide⟩,⟨829,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨830,by decide⟩,⟨830,by decide⟩,⟨808,by decide⟩] | _ => ![⟨455,by decide⟩,⟨790,by decide⟩,⟨455,by decide⟩]

def ntree12LRLRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLLLRL i else ntree12LRLRLLLRR (i - 6)

def ntree12LRLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRLLLL i else ntree12LRLRLLLR (i - 12)

def ntree12LRLRLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨473,by decide⟩,⟨792,by decide⟩,⟨822,by decide⟩] | 1 => ![⟨474,by decide⟩,⟨793,by decide⟩,⟨793,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨831,by decide⟩,⟨831,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨832,by decide⟩,⟨832,by decide⟩] | 4 => ![⟨455,by decide⟩,⟨27,by decide⟩,⟨833,by decide⟩] | _ => ![⟨494,by decide⟩,⟨25,by decide⟩,⟨25,by decide⟩]

def ntree12LRLRLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨72,by decide⟩,⟨506,by decide⟩,⟨834,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨788,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨441,by decide⟩,⟨72,by decide⟩] | 4 => ![⟨72,by decide⟩,⟨511,by decide⟩,⟨834,by decide⟩] | _ => ![⟨76,by decide⟩,⟨512,by decide⟩,⟨834,by decide⟩]

def ntree12LRLRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLLRLL i else ntree12LRLRLLRLR (i - 6)

def ntree12LRLRLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨835,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨835,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨436,by decide⟩,⟨836,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨437,by decide⟩,⟨836,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨837,by decide⟩,⟨837,by decide⟩] | _ => ![⟨10,by decide⟩,⟨838,by decide⟩,⟨837,by decide⟩]

def ntree12LRLRLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨839,by decide⟩,⟨0,by decide⟩,⟨839,by decide⟩] | 1 => ![⟨840,by decide⟩,⟨0,by decide⟩,⟨840,by decide⟩] | 2 => ![⟨841,by decide⟩,⟨513,by decide⟩,⟨841,by decide⟩] | 3 => ![⟨842,by decide⟩,⟨0,by decide⟩,⟨842,by decide⟩] | 4 => ![⟨843,by decide⟩,⟨16,by decide⟩,⟨840,by decide⟩] | _ => ![⟨840,by decide⟩,⟨0,by decide⟩,⟨840,by decide⟩]

def ntree12LRLRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLLRRL i else ntree12LRLRLLRRR (i - 6)

def ntree12LRLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRLLRL i else ntree12LRLRLLRR (i - 12)

def ntree12LRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLRLLL i else ntree12LRLRLLR (i - 24)

def ntree12LRLRLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨842,by decide⟩,⟨441,by decide⟩,⟨842,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨520,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨844,by decide⟩,⟨844,by decide⟩] | 3 => ![⟨16,by decide⟩,⟨845,by decide⟩,⟨844,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨846,by decide⟩,⟨846,by decide⟩] | _ => ![⟨72,by decide⟩,⟨803,by decide⟩,⟨847,by decide⟩]

def ntree12LRLRLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨74,by decide⟩,⟨804,by decide⟩,⟨848,by decide⟩] | 1 => ![⟨849,by decide⟩,⟨850,by decide⟩,⟨849,by decide⟩] | 2 => ![⟨849,by decide⟩,⟨851,by decide⟩,⟨852,by decide⟩] | 3 => ![⟨531,by decide⟩,⟨0,by decide⟩,⟨853,by decide⟩] | 4 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨854,by decide⟩] | _ => ![⟨810,by decide⟩,⟨506,by decide⟩,⟨855,by decide⟩]

def ntree12LRLRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLRLLL i else ntree12LRLRLRLLR (i - 6)

def ntree12LRLRLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨811,by decide⟩,⟨837,by decide⟩,⟨856,by decide⟩] | 1 => ![⟨857,by decide⟩,⟨2,by decide⟩,⟨857,by decide⟩] | 2 => ![⟨858,by decide⟩,⟨506,by decide⟩,⟨859,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨0,by decide⟩,⟨455,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨860,by decide⟩] | _ => ![⟨455,by decide⟩,⟨844,by decide⟩,⟨861,by decide⟩]

def ntree12LRLRLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨541,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨60,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LRLRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLRLRL i else ntree12LRLRLRLRR (i - 6)

def ntree12LRLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRLRLL i else ntree12LRLRLRLR (i - 12)

def ntree12LRLRLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨545,by decide⟩,⟨0,by decide⟩,⟨455,by decide⟩] | 1 => ![⟨862,by decide⟩,⟨863,by decide⟩,⟨849,by decide⟩] | 2 => ![⟨864,by decide⟩,⟨865,by decide⟩,⟨72,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨866,by decide⟩,⟨844,by decide⟩] | 4 => ![⟨840,by decide⟩,⟨803,by decide⟩,⟨867,by decide⟩] | _ => ![⟨842,by decide⟩,⟨803,by decide⟩,⟨868,by decide⟩]

def ntree12LRLRLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨869,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨870,by decide⟩] | 2 => ![⟨871,by decide⟩,⟨103,by decide⟩,⟨871,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨872,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨873,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨874,by decide⟩]

def ntree12LRLRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLRRLL i else ntree12LRLRLRRLR (i - 6)

def ntree12LRLRLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨869,by decide⟩] | 2 => ![⟨72,by decide⟩,⟨552,by decide⟩,⟨72,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨870,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨544,by decide⟩,⟨25,by decide⟩,⟨25,by decide⟩]

def ntree12LRLRLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨874,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨108,by decide⟩,⟨553,by decide⟩,⟨875,by decide⟩] | 3 => ![⟨109,by decide⟩,⟨554,by decide⟩,⟨876,by decide⟩] | 4 => ![⟨110,by decide⟩,⟨555,by decide⟩,⟨875,by decide⟩] | 5 => ![⟨111,by decide⟩,⟨556,by decide⟩,⟨876,by decide⟩] | _ => ![⟨877,by decide⟩,⟨443,by decide⟩,⟨877,by decide⟩]

def ntree12LRLRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRLRRRL i else ntree12LRLRLRRRR (i - 6)

def ntree12LRLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRLRRL i else ntree12LRLRLRRR (i - 12)

def ntree12LRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLRLRL i else ntree12LRLRLRR (i - 24)

def ntree12LRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LRLRLL i else ntree12LRLRLR (i - 48)

def ntree12LRLRRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨878,by decide⟩,⟨4,by decide⟩,⟨878,by decide⟩] | 1 => ![⟨879,by decide⟩,⟨0,by decide⟩,⟨879,by decide⟩] | 2 => ![⟨880,by decide⟩,⟨0,by decide⟩,⟨880,by decide⟩] | 3 => ![⟨881,by decide⟩,⟨445,by decide⟩,⟨881,by decide⟩] | 4 => ![⟨882,by decide⟩,⟨443,by decide⟩,⟨882,by decide⟩] | _ => ![⟨883,by decide⟩,⟨16,by decide⟩,⟨880,by decide⟩]

def ntree12LRLRRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨108,by decide⟩,⟨560,by decide⟩,⟨108,by decide⟩] | 1 => ![⟨109,by decide⟩,⟨561,by decide⟩,⟨109,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨884,by decide⟩,⟨884,by decide⟩] | 3 => ![⟨885,by decide⟩,⟨799,by decide⟩,⟨885,by decide⟩] | 4 => ![⟨886,by decide⟩,⟨2,by decide⟩,⟨886,by decide⟩] | _ => ![⟨877,by decide⟩,⟨564,by decide⟩,⟨887,by decide⟩]

def ntree12LRLRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRLLLL i else ntree12LRLRRLLLR (i - 6)

def ntree12LRLRRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨879,by decide⟩,⟨114,by decide⟩,⟨888,by decide⟩] | 1 => ![⟨799,by decide⟩,⟨889,by decide⟩,⟨889,by decide⟩] | 2 => ![⟨890,by decide⟩,⟨891,by decide⟩,⟨892,by decide⟩] | 3 => ![⟨567,by decide⟩,⟨0,by decide⟩,⟨893,by decide⟩] | 4 => ![⟨569,by decide⟩,⟨4,by decide⟩,⟨894,by decide⟩] | _ => ![⟨890,by decide⟩,⟨808,by decide⟩,⟨890,by decide⟩]

def ntree12LRLRRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨121,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨895,by decide⟩,⟨829,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨896,by decide⟩,⟨830,by decide⟩,⟨890,by decide⟩] | 3 => ![⟨897,by decide⟩,⟨57,by decide⟩,⟨879,by decide⟩] | 4 => ![⟨544,by decide⟩,⟨113,by decide⟩,⟨113,by decide⟩] | _ => ![⟨0,by decide⟩,⟨898,by decide⟩,⟨0,by decide⟩]

def ntree12LRLRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRLLRL i else ntree12LRLRRLLRR (i - 6)

def ntree12LRLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRRLLL i else ntree12LRLRRLLR (i - 12)

def ntree12LRLRRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨899,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨899,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨900,by decide⟩,⟨901,by decide⟩] | 4 => ![⟨593,by decide⟩,⟨898,by decide⟩,⟨788,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨788,by decide⟩]

def ntree12LRLRRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨902,by decide⟩,⟨433,by decide⟩] | 1 => ![⟨903,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 3 => ![⟨443,by decide⟩,⟨904,by decide⟩,⟨904,by decide⟩] | 4 => ![⟨598,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | _ => ![⟨0,by decide⟩,⟨905,by decide⟩,⟨144,by decide⟩]

def ntree12LRLRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRLRLL i else ntree12LRLRRLRLR (i - 6)

def ntree12LRLRRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨906,by decide⟩,⟨0,by decide⟩,⟨907,by decide⟩] | 1 => ![⟨598,by decide⟩,⟨27,by decide⟩,⟨27,by decide⟩] | 2 => ![⟨908,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨443,by decide⟩,⟨909,by decide⟩,⟨443,by decide⟩] | 4 => ![⟨452,by decide⟩,⟨910,by decide⟩,⟨904,by decide⟩] | _ => ![⟨598,by decide⟩,⟨153,by decide⟩,⟨788,by decide⟩]

def ntree12LRLRRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨911,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨912,by decide⟩] | 2 => ![⟨599,by decide⟩,⟨909,by decide⟩,⟨801,by decide⟩] | 3 => ![⟨601,by decide⟩,⟨157,by decide⟩,⟨913,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨914,by decide⟩,⟨915,by decide⟩] | _ => ![⟨443,by decide⟩,⟨916,by decide⟩,⟨454,by decide⟩]

def ntree12LRLRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRLRRL i else ntree12LRLRRLRRR (i - 6)

def ntree12LRLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRRLRL i else ntree12LRLRRLRR (i - 12)

def ntree12LRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLRRLL i else ntree12LRLRRLR (i - 24)

def ntree12LRLRRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨917,by decide⟩,⟨0,by decide⟩,⟨917,by decide⟩] | 1 => ![⟨918,by decide⟩,⟨129,by decide⟩,⟨918,by decide⟩] | 2 => ![⟨917,by decide⟩,⟨803,by decide⟩,⟨919,by decide⟩] | 3 => ![⟨920,by decide⟩,⟨920,by decide⟩,⟨920,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨901,by decide⟩,⟨901,by decide⟩] | _ => ![⟨917,by decide⟩,⟨0,by decide⟩,⟨921,by decide⟩]

def ntree12LRLRRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨605,by decide⟩,⟨605,by decide⟩,⟨922,by decide⟩] | 1 => ![⟨917,by decide⟩,⟨433,by decide⟩,⟨923,by decide⟩] | 2 => ![⟨924,by decide⟩,⟨129,by decide⟩,⟨924,by decide⟩] | 3 => ![⟨810,by decide⟩,⟨0,by decide⟩,⟨925,by decide⟩] | 4 => ![⟨810,by decide⟩,⟨433,by decide⟩,⟨926,by decide⟩] | _ => ![⟨178,by decide⟩,⟨927,by decide⟩,⟨803,by decide⟩]

def ntree12LRLRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRRLLL i else ntree12LRLRRRLLR (i - 6)

def ntree12LRLRRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨928,by decide⟩,⟨920,by decide⟩,⟨920,by decide⟩] | 1 => ![⟨917,by decide⟩,⟨153,by decide⟩,⟨917,by decide⟩] | 2 => ![⟨469,by decide⟩,⟨929,by decide⟩,⟨901,by decide⟩] | 3 => ![⟨930,by decide⟩,⟨469,by decide⟩,⟨917,by decide⟩] | 4 => ![⟨471,by decide⟩,⟨153,by decide⟩,⟨471,by decide⟩] | _ => ![⟨178,by decide⟩,⟨178,by decide⟩,⟨788,by decide⟩]

def ntree12LRLRRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨931,by decide⟩,⟨184,by decide⟩,⟨921,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨178,by decide⟩,⟨178,by decide⟩,⟨788,by decide⟩] | 3 => ![⟨174,by decide⟩,⟨0,by decide⟩,⟨788,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨932,by decide⟩,⟨433,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LRLRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRRLRL i else ntree12LRLRRRLRR (i - 6)

def ntree12LRLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRRRLL i else ntree12LRLRRRLR (i - 12)

def ntree12LRLRRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨174,by decide⟩,⟨433,by decide⟩,⟨433,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨603,by decide⟩,⟨898,by decide⟩,⟨603,by decide⟩] | 3 => ![⟨933,by decide⟩,⟨934,by decide⟩,⟨803,by decide⟩] | 4 => ![⟨935,by decide⟩,⟨935,by decide⟩,⟨920,by decide⟩] | _ => ![⟨933,by decide⟩,⟨933,by decide⟩,⟨0,by decide⟩]

def ntree12LRLRRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨188,by decide⟩,⟨803,by decide⟩,⟨936,by decide⟩] | 1 => ![⟨920,by decide⟩,⟨937,by decide⟩,⟨937,by decide⟩] | 2 => ![⟨471,by decide⟩,⟨144,by decide⟩,⟨938,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨939,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨940,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨941,by decide⟩]

def ntree12LRLRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRRRLL i else ntree12LRLRRRRLR (i - 6)

def ntree12LRLRRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨942,by decide⟩] | 1 => ![⟨907,by decide⟩,⟨0,by decide⟩,⟨907,by decide⟩] | 2 => ![⟨471,by decide⟩,⟨153,by decide⟩,⟨471,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨493,by decide⟩,⟨157,by decide⟩,⟨938,by decide⟩]

def ntree12LRLRRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨939,by decide⟩] | 1 => ![⟨494,by decide⟩,⟨153,by decide⟩,⟨940,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨941,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨943,by decide⟩,⟨943,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨72,by decide⟩,⟨592,by decide⟩,⟨72,by decide⟩] | _ => ![⟨72,by decide⟩,⟨944,by decide⟩,⟨72,by decide⟩]

def ntree12LRLRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRLRRRRRL i else ntree12LRLRRRRRR (i - 6)

def ntree12LRLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRLRRRRL i else ntree12LRLRRRRR (i - 12)

def ntree12LRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRLRRRL i else ntree12LRLRRRR (i - 24)

def ntree12LRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LRLRRL i else ntree12LRLRRR (i - 48)

def ntree12LRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LRLRL i else ntree12LRLRR (i - 97)

def ntree12LRL (i : Nat) : Fin 3 → Fin 2396 := if i < 194 then ntree12LRLL i else ntree12LRLR (i - 194)

def ntree12LRRLLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨8,by decide⟩,⟨945,by decide⟩,⟨943,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨946,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨943,by decide⟩,⟨947,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨948,by decide⟩,⟨834,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨945,by decide⟩,⟨947,by decide⟩] | _ => ![⟨903,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩]

def ntree12LRRLLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨949,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨950,by decide⟩,⟨951,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨950,by decide⟩,⟨952,by decide⟩,⟨211,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨943,by decide⟩,⟨943,by decide⟩] | 4 => ![⟨950,by decide⟩,⟨953,by decide⟩,⟨834,by decide⟩] | _ => ![⟨954,by decide⟩,⟨955,by decide⟩,⟨956,by decide⟩]

def ntree12LRRLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLLLLL i else ntree12LRRLLLLLR (i - 6)

def ntree12LRRLLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨957,by decide⟩,⟨958,by decide⟩,⟨957,by decide⟩] | 1 => ![⟨958,by decide⟩,⟨958,by decide⟩,⟨958,by decide⟩] | 2 => ![⟨958,by decide⟩,⟨959,by decide⟩,⟨959,by decide⟩] | 3 => ![⟨960,by decide⟩,⟨0,by decide⟩,⟨960,by decide⟩] | 4 => ![⟨961,by decide⟩,⟨605,by decide⟩,⟨961,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨946,by decide⟩]

def ntree12LRRLLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨960,by decide⟩,⟨231,by decide⟩,⟨962,by decide⟩] | 1 => ![⟨961,by decide⟩,⟨635,by decide⟩,⟨963,by decide⟩] | 2 => ![⟨958,by decide⟩,⟨964,by decide⟩,⟨964,by decide⟩] | 3 => ![⟨965,by decide⟩,⟨958,by decide⟩,⟨965,by decide⟩] | 4 => ![⟨810,by decide⟩,⟨231,by decide⟩,⟨966,by decide⟩] | _ => ![⟨598,by decide⟩,⟨967,by decide⟩,⟨860,by decide⟩]

def ntree12LRRLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLLLRL i else ntree12LRRLLLLRR (i - 6)

def ntree12LRRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLLLLL i else ntree12LRRLLLLR (i - 12)

def ntree12LRRLLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨968,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨637,by decide⟩,⟨242,by decide⟩,⟨853,by decide⟩] | 2 => ![⟨238,by decide⟩,⟨638,by decide⟩,⟨834,by decide⟩] | 3 => ![⟨969,by decide⟩,⟨969,by decide⟩,⟨958,by decide⟩] | 4 => ![⟨970,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨958,by decide⟩,⟨971,by decide⟩,⟨971,by decide⟩]

def ntree12LRRLLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨531,by decide⟩,⟨144,by decide⟩,⟨972,by decide⟩] | 1 => ![⟨544,by decide⟩,⟨153,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨546,by decide⟩,⟨157,by decide⟩,⟨972,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨641,by decide⟩,⟨72,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | _ => ![⟨443,by decide⟩,⟨973,by decide⟩,⟨973,by decide⟩]

def ntree12LRRLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLLRLL i else ntree12LRRLLLRLR (i - 6)

def ntree12LRRLLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨974,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨975,by decide⟩,⟨976,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨973,by decide⟩,⟨977,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨268,by decide⟩,⟨978,by decide⟩] | 4 => ![⟨979,by decide⟩,⟨920,by decide⟩,⟨979,by decide⟩] | _ => ![⟨920,by decide⟩,⟨980,by decide⟩,⟨980,by decide⟩]

def ntree12LRRLLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨981,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨664,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨290,by decide⟩,⟨665,by decide⟩,⟨834,by decide⟩] | 3 => ![⟨291,by decide⟩,⟨666,by decide⟩,⟨788,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨72,by decide⟩,⟨667,by decide⟩,⟨72,by decide⟩]

def ntree12LRRLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLLRRL i else ntree12LRRLLLRRR (i - 6)

def ntree12LRRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLLLRL i else ntree12LRRLLLRR (i - 12)

def ntree12LRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRLLLL i else ntree12LRRLLLR (i - 24)

def ntree12LRRLLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨982,by decide⟩] | 1 => ![⟨879,by decide⟩,⟨231,by decide⟩,⟨983,by decide⟩] | 2 => ![⟨72,by decide⟩,⟨681,by decide⟩,⟨984,by decide⟩] | 3 => ![⟨877,by decide⟩,⟨682,by decide⟩,⟨985,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨544,by decide⟩,⟨268,by decide⟩,⟨268,by decide⟩]

def ntree12LRRLLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨72,by decide⟩,⟨687,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨982,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨689,by decide⟩,⟨984,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨986,by decide⟩,⟨986,by decide⟩] | 4 => ![⟨987,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨707,by decide⟩,⟨311,by decide⟩,⟨311,by decide⟩]

def ntree12LRRLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLRLLL i else ntree12LRRLLRLLR (i - 6)

def ntree12LRRLLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨708,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩] | 1 => ![⟨799,by decide⟩,⟨988,by decide⟩,⟨988,by decide⟩] | 2 => ![⟨598,by decide⟩,⟨790,by decide⟩,⟨319,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨901,by decide⟩,⟨989,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨821,by decide⟩,⟨0,by decide⟩]

def ntree12LRRLLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨990,by decide⟩,⟨808,by decide⟩,⟨808,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨991,by decide⟩,⟨0,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨901,by decide⟩,⟨989,by decide⟩] | 4 => ![⟨992,by decide⟩,⟨992,by decide⟩,⟨0,by decide⟩] | _ => ![⟨993,by decide⟩,⟨993,by decide⟩,⟨2,by decide⟩]

def ntree12LRRLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLRLRL i else ntree12LRRLLRLRR (i - 6)

def ntree12LRRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLLRLL i else ntree12LRRLLRLR (i - 12)

def ntree12LRRLLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨174,by decide⟩,⟨702,by decide⟩,⟨702,by decide⟩] | 2 => ![⟨994,by decide⟩,⟨992,by decide⟩,⟨826,by decide⟩] | 3 => ![⟨808,by decide⟩,⟨995,by decide⟩,⟨995,by decide⟩] | 4 => ![⟨455,by decide⟩,⟨144,by decide⟩,⟨996,by decide⟩] | _ => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨997,by decide⟩]

def ntree12LRRLLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨483,by decide⟩,⟨904,by decide⟩,⟨998,by decide⟩] | 1 => ![⟨457,by decide⟩,⟨311,by decide⟩,⟨999,by decide⟩] | 2 => ![⟨455,by decide⟩,⟨314,by decide⟩,⟨1000,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨1001,by decide⟩] | 4 => ![⟨455,by decide⟩,⟨144,by decide⟩,⟨1002,by decide⟩] | _ => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨1003,by decide⟩]

def ntree12LRRLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLRRLL i else ntree12LRRLLRRLR (i - 6)

def ntree12LRRLLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨445,by decide⟩,⟨445,by decide⟩,⟨1004,by decide⟩] | 1 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨1005,by decide⟩] | 2 => ![⟨729,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨1006,by decide⟩,⟨1006,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1007,by decide⟩] | _ => ![⟨1008,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LRRLLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1009,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1009,by decide⟩,⟨368,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨1010,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨441,by decide⟩,⟨946,by decide⟩] | 4 => ![⟨840,by decide⟩,⟨144,by decide⟩,⟨1011,by decide⟩] | 5 => ![⟨1012,by decide⟩,⟨366,by decide⟩,⟨839,by decide⟩] | _ => ![⟨1013,by decide⟩,⟨367,by decide⟩,⟨840,by decide⟩]

def ntree12LRRLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLLRRRL i else ntree12LRRLLRRRR (i - 6)

def ntree12LRRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLLRRL i else ntree12LRRLLRRR (i - 12)

def ntree12LRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRLLRL i else ntree12LRRLLRR (i - 24)

def ntree12LRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LRRLLL i else ntree12LRRLLR (i - 48)

def ntree12LRRLRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨840,by decide⟩,⟨144,by decide⟩,⟨1011,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1014,by decide⟩,⟨1014,by decide⟩] | 3 => ![⟨455,by decide⟩,⟨943,by decide⟩,⟨1015,by decide⟩] | 4 => ![⟨858,by decide⟩,⟨0,by decide⟩,⟨858,by decide⟩] | _ => ![⟨810,by decide⟩,⟨378,by decide⟩,⟨1016,by decide⟩]

def ntree12LRRLRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨811,by decide⟩,⟨379,by decide⟩,⟨1017,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨72,by decide⟩,⟨764,by decide⟩,⟨72,by decide⟩] | 3 => ![⟨174,by decide⟩,⟨736,by decide⟩,⟨736,by decide⟩] | 4 => ![⟨598,by decide⟩,⟨378,by decide⟩,⟨378,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LRRLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRLLLL i else ntree12LRRLRLLLR (i - 6)

def ntree12LRRLRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1018,by decide⟩,⟨1018,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1019,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1020,by decide⟩,⟨1018,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨849,by decide⟩,⟨1021,by decide⟩,⟨1022,by decide⟩] | 4 => ![⟨72,by decide⟩,⟨772,by decide⟩,⟨1023,by decide⟩] | _ => ![⟨455,by decide⟩,⟨144,by decide⟩,⟨1024,by decide⟩]

def ntree12LRRLRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨455,by decide⟩,⟨144,by decide⟩,⟨1025,by decide⟩] | 1 => ![⟨839,by decide⟩,⟨231,by decide⟩,⟨1026,by decide⟩] | 2 => ![⟨871,by decide⟩,⟨260,by decide⟩,⟨1027,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨773,by decide⟩,⟨1028,by decide⟩] | 4 => ![⟨841,by decide⟩,⟨774,by decide⟩,⟨1029,by decide⟩] | _ => ![⟨842,by decide⟩,⟨231,by decide⟩,⟨1030,by decide⟩]

def ntree12LRRLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRLLRL i else ntree12LRRLRLLRR (i - 6)

def ntree12LRRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLRLLL i else ntree12LRRLRLLR (i - 12)

def ntree12LRRLRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨768,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨109,by decide⟩,⟨736,by decide⟩,⟨1031,by decide⟩] | _ => ![⟨0,by decide⟩,⟨561,by decide⟩,⟨899,by decide⟩]

def ntree12LRRLRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨799,by decide⟩,⟨1032,by decide⟩,⟨1032,by decide⟩] | 1 => ![⟨567,by decide⟩,⟨378,by decide⟩,⟨1033,by decide⟩] | 2 => ![⟨291,by decide⟩,⟨736,by decide⟩,⟨736,by decide⟩] | 3 => ![⟨1034,by decide⟩,⟨933,by decide⟩,⟨567,by decide⟩] | 4 => ![⟨72,by decide⟩,⟨784,by decide⟩,⟨1035,by decide⟩] | _ => ![⟨877,by decide⟩,⟨785,by decide⟩,⟨1036,by decide⟩]

def ntree12LRRLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRLRLL i else ntree12LRRLRLRLR (i - 6)

def ntree12LRRLRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨1037,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨1038,by decide⟩] | 2 => ![⟨878,by decide⟩,⟨409,by decide⟩,⟨1039,by decide⟩] | 3 => ![⟨880,by decide⟩,⟨231,by decide⟩,⟨1040,by decide⟩] | 4 => ![⟨108,by decide⟩,⟨786,by decide⟩,⟨1041,by decide⟩] | _ => ![⟨881,by decide⟩,⟨787,by decide⟩,⟨1042,by decide⟩]

def ntree12LRRLRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨882,by decide⟩,⟨682,by decide⟩,⟨1043,by decide⟩] | 1 => ![⟨992,by decide⟩,⟨1044,by decide⟩,⟨268,by decide⟩] | 2 => ![⟨768,by decide⟩,⟨268,by decide⟩,⟨268,by decide⟩] | 3 => ![⟨1045,by decide⟩,⟨1,by decide⟩,⟨1046,by decide⟩] | 4 => ![⟨1047,by decide⟩,⟨5,by decide⟩,⟨1048,by decide⟩] | _ => ![⟨1049,by decide⟩,⟨3,by decide⟩,⟨1050,by decide⟩]

def ntree12LRRLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRLRRL i else ntree12LRRLRLRRR (i - 6)

def ntree12LRRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLRLRL i else ntree12LRRLRLRR (i - 12)

def ntree12LRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRLRLL i else ntree12LRRLRLR (i - 24)

def ntree12LRRLRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1051,by decide⟩,⟨1,by decide⟩,⟨1052,by decide⟩] | 1 => ![⟨1053,by decide⟩,⟨1,by decide⟩,⟨1054,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1055,by decide⟩] | 3 => ![⟨1056,by decide⟩,⟨1056,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1057,by decide⟩,⟨1057,by decide⟩,⟨2,by decide⟩] | _ => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨1058,by decide⟩]

def ntree12LRRLRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1059,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1060,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1061,by decide⟩] | 3 => ![⟨1056,by decide⟩,⟨1056,by decide⟩,⟨1061,by decide⟩] | 4 => ![⟨1062,by decide⟩,⟨1,by decide⟩,⟨1063,by decide⟩] | _ => ![⟨1064,by decide⟩,⟨5,by decide⟩,⟨1065,by decide⟩]

def ntree12LRRLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRRLLL i else ntree12LRRLRRLLR (i - 6)

def ntree12LRRLRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1062,by decide⟩,⟨0,by decide⟩,⟨1062,by decide⟩] | 1 => ![⟨1066,by decide⟩,⟨1056,by decide⟩,⟨1062,by decide⟩] | 2 => ![⟨1064,by decide⟩,⟨4,by decide⟩,⟨1064,by decide⟩] | 3 => ![⟨1062,by decide⟩,⟨25,by decide⟩,⟨1067,by decide⟩] | 4 => ![⟨1064,by decide⟩,⟨26,by decide⟩,⟨1068,by decide⟩] | _ => ![⟨1062,by decide⟩,⟨27,by decide⟩,⟨1069,by decide⟩]

def ntree12LRRLRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1051,by decide⟩,⟨30,by decide⟩,⟨1070,by decide⟩] | 1 => ![⟨1049,by decide⟩,⟨2,by decide⟩,⟨1049,by decide⟩] | 2 => ![⟨1051,by decide⟩,⟨0,by decide⟩,⟨1051,by decide⟩] | 3 => ![⟨1053,by decide⟩,⟨0,by decide⟩,⟨1053,by decide⟩] | 4 => ![⟨1062,by decide⟩,⟨30,by decide⟩,⟨1071,by decide⟩] | _ => ![⟨1072,by decide⟩,⟨38,by decide⟩,⟨1072,by decide⟩]

def ntree12LRRLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRRLRL i else ntree12LRRLRRLRR (i - 6)

def ntree12LRRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLRRLL i else ntree12LRRLRRLR (i - 12)

def ntree12LRRLRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1073,by decide⟩,⟨2,by decide⟩,⟨1073,by decide⟩] | 1 => ![⟨1074,by decide⟩,⟨1075,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨1076,by decide⟩,⟨1077,by decide⟩,⟨3,by decide⟩] | 3 => ![⟨1078,by decide⟩,⟨1079,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨1074,by decide⟩,⟨1074,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1076,by decide⟩,⟨1076,by decide⟩,⟨2,by decide⟩]

def ntree12LRRLRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1080,by decide⟩,⟨1080,by decide⟩,⟨42,by decide⟩] | 1 => ![⟨1081,by decide⟩,⟨1081,by decide⟩,⟨44,by decide⟩] | 2 => ![⟨1078,by decide⟩,⟨1078,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨1082,by decide⟩,⟨1083,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨1082,by decide⟩,⟨1082,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1084,by decide⟩,⟨1084,by decide⟩,⟨48,by decide⟩]

def ntree12LRRLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRRRLL i else ntree12LRRLRRRLR (i - 6)

def ntree12LRRLRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1085,by decide⟩,⟨42,by decide⟩,⟨1085,by decide⟩] | 1 => ![⟨1086,by decide⟩,⟨0,by decide⟩,⟨1086,by decide⟩] | 2 => ![⟨1087,by decide⟩,⟨46,by decide⟩,⟨1087,by decide⟩] | 3 => ![⟨1088,by decide⟩,⟨4,by decide⟩,⟨1088,by decide⟩] | 4 => ![⟨1089,by decide⟩,⟨1074,by decide⟩,⟨1062,by decide⟩] | _ => ![⟨1090,by decide⟩,⟨1078,by decide⟩,⟨1064,by decide⟩]

def ntree12LRRLRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1091,by decide⟩,⟨1080,by decide⟩,⟨1085,by decide⟩] | 1 => ![⟨1092,by decide⟩,⟨1056,by decide⟩,⟨1086,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1093,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨1094,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨1095,by decide⟩,⟨1096,by decide⟩,⟨30,by decide⟩] | 5 => ![⟨1095,by decide⟩,⟨1095,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1097,by decide⟩,⟨0,by decide⟩,⟨1097,by decide⟩]

def ntree12LRRLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRLRRRRL i else ntree12LRRLRRRRR (i - 6)

def ntree12LRRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRLRRRL i else ntree12LRRLRRRR (i - 12)

def ntree12LRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRLRRL i else ntree12LRRLRRR (i - 24)

def ntree12LRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LRRLRL i else ntree12LRRLRR (i - 48)

def ntree12LRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LRRLL i else ntree12LRRLR (i - 97)

def ntree12LRRRLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1098,by decide⟩,⟨48,by decide⟩,⟨1098,by decide⟩] | 1 => ![⟨1097,by decide⟩,⟨30,by decide⟩,⟨1099,by decide⟩] | 2 => ![⟨1062,by decide⟩,⟨1100,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨1101,by decide⟩,⟨2,by decide⟩,⟨1101,by decide⟩] | 4 => ![⟨1102,by decide⟩,⟨44,by decide⟩,⟨1102,by decide⟩] | _ => ![⟨1103,by decide⟩,⟨1095,by decide⟩,⟨1062,by decide⟩]

def ntree12LRRRLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1104,by decide⟩,⟨1075,by decide⟩,⟨1054,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1105,by decide⟩] | 2 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨1106,by decide⟩] | 3 => ![⟨1074,by decide⟩,⟨1074,by decide⟩,⟨1061,by decide⟩] | 4 => ![⟨1056,by decide⟩,⟨1056,by decide⟩,⟨1105,by decide⟩] | _ => ![⟨1080,by decide⟩,⟨1080,by decide⟩,⟨1106,by decide⟩]

def ntree12LRRRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLLLLL i else ntree12LRRRLLLLR (i - 6)

def ntree12LRRRLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1074,by decide⟩,⟨1107,by decide⟩,⟨25,by decide⟩] | 1 => ![⟨1053,by decide⟩,⟨1093,by decide⟩,⟨1053,by decide⟩] | 2 => ![⟨1108,by decide⟩,⟨0,by decide⟩,⟨1108,by decide⟩] | 3 => ![⟨1109,by decide⟩,⟨0,by decide⟩,⟨1109,by decide⟩] | 4 => ![⟨1108,by decide⟩,⟨30,by decide⟩,⟨1110,by decide⟩] | _ => ![⟨1111,by decide⟩,⟨0,by decide⟩,⟨1111,by decide⟩]

def ntree12LRRRLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1112,by decide⟩,⟨42,by decide⟩,⟨1112,by decide⟩] | 1 => ![⟨1113,by decide⟩,⟨0,by decide⟩,⟨1113,by decide⟩] | 2 => ![⟨1114,by decide⟩,⟨1115,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨1116,by decide⟩,⟨1,by decide⟩,⟨1117,by decide⟩] | 4 => ![⟨1118,by decide⟩,⟨3,by decide⟩,⟨1119,by decide⟩] | _ => ![⟨1120,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩]

def ntree12LRRRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLLLRL i else ntree12LRRRLLLRR (i - 6)

def ntree12LRRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRLLLL i else ntree12LRRRLLLR (i - 12)

def ntree12LRRRLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1121,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨1120,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1121,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1122,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1123,by decide⟩] | _ => ![⟨1118,by decide⟩,⟨2,by decide⟩,⟨1118,by decide⟩]

def ntree12LRRRLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1116,by decide⟩] | 1 => ![⟨1114,by decide⟩,⟨1114,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1124,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1125,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩]

def ntree12LRRRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLLRLL i else ntree12LRRRLLRLR (i - 6)

def ntree12LRRRLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1126,by decide⟩,⟨1,by decide⟩,⟨1127,by decide⟩] | 1 => ![⟨1128,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨1128,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1126,by decide⟩,⟨0,by decide⟩,⟨1126,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1129,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1062,by decide⟩,⟨1130,by decide⟩,⟨1062,by decide⟩] | 1 => ![⟨1131,by decide⟩,⟨86,by decide⟩,⟨1131,by decide⟩] | 2 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1116,by decide⟩] | 3 => ![⟨1132,by decide⟩,⟨1133,by decide⟩,⟨1062,by decide⟩] | 4 => ![⟨1116,by decide⟩,⟨37,by decide⟩,⟨1134,by decide⟩] | _ => ![⟨1135,by decide⟩,⟨1136,by decide⟩,⟨1,by decide⟩]

def ntree12LRRRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLLRRL i else ntree12LRRRLLRRR (i - 6)

def ntree12LRRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRLLRL i else ntree12LRRRLLRR (i - 12)

def ntree12LRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRRLLL i else ntree12LRRRLLR (i - 24)

def ntree12LRRRLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1137,by decide⟩,⟨1138,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨1139,by decide⟩,⟨1140,by decide⟩,⟨43,by decide⟩] | 2 => ![⟨1141,by decide⟩,⟨1142,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨1095,by decide⟩,⟨1143,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1144,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2,by decide⟩,⟨1145,by decide⟩,⟨2,by decide⟩]

def ntree12LRRRLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨1146,by decide⟩,⟨42,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1147,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1135,by decide⟩,⟨1135,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1137,by decide⟩,⟨1137,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨1139,by decide⟩,⟨1139,by decide⟩,⟨42,by decide⟩] | _ => ![⟨1141,by decide⟩,⟨1141,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLRLLL i else ntree12LRRRLRLLR (i - 6)

def ntree12LRRRLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1148,by decide⟩,⟨1141,by decide⟩,⟨1086,by decide⟩] | 1 => ![⟨1062,by decide⟩,⟨1144,by decide⟩,⟨1062,by decide⟩] | 2 => ![⟨1097,by decide⟩,⟨1144,by decide⟩,⟨1097,by decide⟩] | 3 => ![⟨1149,by decide⟩,⟨43,by decide⟩,⟨1150,by decide⟩] | 4 => ![⟨1151,by decide⟩,⟨1142,by decide⟩,⟨1117,by decide⟩] | _ => ![⟨1152,by decide⟩,⟨1,by decide⟩,⟨1153,by decide⟩]

def ntree12LRRRLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1154,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 1 => ![⟨1155,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1149,by decide⟩,⟨42,by decide⟩,⟨1149,by decide⟩] | 3 => ![⟨1156,by decide⟩,⟨1095,by decide⟩,⟨1116,by decide⟩] | 4 => ![⟨1116,by decide⟩,⟨1147,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨1157,by decide⟩]

def ntree12LRRRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLRLRL i else ntree12LRRRLRLRR (i - 6)

def ntree12LRRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRLRLL i else ntree12LRRRLRLR (i - 12)

def ntree12LRRRLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1141,by decide⟩,⟨1141,by decide⟩,⟨1124,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1158,by decide⟩] | 2 => ![⟨1159,by decide⟩,⟨1159,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1160,by decide⟩,⟨1160,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1161,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1130,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1152,by decide⟩,⟨0,by decide⟩,⟨1152,by decide⟩] | 1 => ![⟨1108,by decide⟩,⟨0,by decide⟩,⟨1108,by decide⟩] | 2 => ![⟨1162,by decide⟩,⟨103,by decide⟩,⟨1162,by decide⟩] | 3 => ![⟨1163,by decide⟩,⟨1159,by decide⟩,⟨1108,by decide⟩] | 4 => ![⟨1164,by decide⟩,⟨1160,by decide⟩,⟨1109,by decide⟩] | _ => ![⟨1165,by decide⟩,⟨1161,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLRRLL i else ntree12LRRRLRRLR (i - 6)

def ntree12LRRRLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1166,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1167,by decide⟩,⟨0,by decide⟩,⟨1167,by decide⟩] | 2 => ![⟨1168,by decide⟩,⟨2,by decide⟩,⟨1168,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨4,by decide⟩,⟨1169,by decide⟩] | 4 => ![⟨1170,by decide⟩,⟨6,by decide⟩,⟨1170,by decide⟩] | _ => ![⟨1171,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩]

def ntree12LRRRLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1172,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1167,by decide⟩,⟨0,by decide⟩,⟨1173,by decide⟩] | 2 => ![⟨1056,by decide⟩,⟨1174,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨4,by decide⟩,⟨1175,by decide⟩] | 4 => ![⟨1168,by decide⟩,⟨2,by decide⟩,⟨1176,by decide⟩] | 5 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1177,by decide⟩] | _ => ![⟨1167,by decide⟩,⟨0,by decide⟩,⟨1178,by decide⟩]

def ntree12LRRRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRLRRRL i else ntree12LRRRLRRRR (i - 6)

def ntree12LRRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRLRRL i else ntree12LRRRLRRR (i - 12)

def ntree12LRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRRLRL i else ntree12LRRRLRR (i - 24)

def ntree12LRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LRRRLL i else ntree12LRRRLR (i - 48)

def ntree12LRRRRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1179,by decide⟩,⟨1056,by decide⟩,⟨1116,by decide⟩] | 1 => ![⟨1180,by decide⟩,⟨0,by decide⟩,⟨1180,by decide⟩] | 2 => ![⟨1181,by decide⟩,⟨4,by decide⟩,⟨1181,by decide⟩] | 3 => ![⟨1180,by decide⟩,⟨0,by decide⟩,⟨1182,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1183,by decide⟩] | _ => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨1184,by decide⟩]

def ntree12LRRRRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1185,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1186,by decide⟩] | 2 => ![⟨1116,by decide⟩,⟨114,by decide⟩,⟨1187,by decide⟩] | 3 => ![⟨1120,by decide⟩,⟨1188,by decide⟩,⟨1186,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1189,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1190,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRLLLL i else ntree12LRRRRLLLR (i - 6)

def ntree12LRRRRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨4,by decide⟩,⟨1191,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1192,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1074,by decide⟩,⟨1193,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1074,by decide⟩,⟨1194,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1080,by decide⟩,⟨1195,by decide⟩,⟨42,by decide⟩] | _ => ![⟨1057,by decide⟩,⟨1196,by decide⟩,⟨2,by decide⟩]

def ntree12LRRRRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1074,by decide⟩,⟨1197,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1056,by decide⟩,⟨1198,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1056,by decide⟩,⟨1199,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1200,by decide⟩] | 4 => ![⟨1167,by decide⟩,⟨1147,by decide⟩,⟨1167,by decide⟩] | _ => ![⟨1169,by decide⟩,⟨1191,by decide⟩,⟨1169,by decide⟩]

def ntree12LRRRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRLLRL i else ntree12LRRRRLLRR (i - 6)

def ntree12LRRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRRLLL i else ntree12LRRRRLLR (i - 12)

def ntree12LRRRRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1167,by decide⟩,⟨1192,by decide⟩,⟨1167,by decide⟩] | 1 => ![⟨1201,by decide⟩,⟨1074,by decide⟩,⟨1152,by decide⟩] | 2 => ![⟨1202,by decide⟩,⟨1074,by decide⟩,⟨1167,by decide⟩] | 3 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1203,by decide⟩] | 4 => ![⟨1204,by decide⟩,⟨46,by decide⟩,⟨46,by decide⟩] | _ => ![⟨1205,by decide⟩,⟨1078,by decide⟩,⟨1169,by decide⟩]

def ntree12LRRRRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1202,by decide⟩,⟨1197,by decide⟩,⟨1178,by decide⟩] | 1 => ![⟨1206,by decide⟩,⟨1080,by decide⟩,⟨1149,by decide⟩] | 2 => ![⟨1179,by decide⟩,⟨1198,by decide⟩,⟨1203,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1185,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1207,by decide⟩] | _ => ![⟨1208,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩]

def ntree12LRRRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRLRLL i else ntree12LRRRRLRLR (i - 6)

def ntree12LRRRRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1209,by decide⟩,⟨1,by decide⟩,⟨1210,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1211,by decide⟩] | 2 => ![⟨1212,by decide⟩,⟨1212,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1056,by decide⟩,⟨1056,by decide⟩,⟨1211,by decide⟩] | _ => ![⟨1208,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1213,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1209,by decide⟩,⟨0,by decide⟩,⟨1209,by decide⟩] | 2 => ![⟨1214,by decide⟩,⟨0,by decide⟩,⟨1214,by decide⟩] | 3 => ![⟨1209,by decide⟩,⟨0,by decide⟩,⟨1215,by decide⟩] | 4 => ![⟨1216,by decide⟩,⟨1217,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨1218,by decide⟩,⟨141,by decide⟩,⟨1219,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1220,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRLRRL i else ntree12LRRRRLRRR (i - 6)

def ntree12LRRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRRLRL i else ntree12LRRRRLRR (i - 12)

def ntree12LRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRRRLL i else ntree12LRRRRLR (i - 24)

def ntree12LRRRRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1056,by decide⟩,⟨1221,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨1222,by decide⟩] | 2 => ![⟨1223,by decide⟩,⟨1056,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1224,by decide⟩,⟨1217,by decide⟩,⟨1063,by decide⟩] | 4 => ![⟨1225,by decide⟩,⟨141,by decide⟩,⟨1226,by decide⟩] | _ => ![⟨1062,by decide⟩,⟨144,by decide⟩,⟨1227,by decide⟩]

def ntree12LRRRRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1062,by decide⟩,⟨1220,by decide⟩,⟨1062,by decide⟩] | 1 => ![⟨1066,by decide⟩,⟨1221,by decide⟩,⟨1227,by decide⟩] | 2 => ![⟨1224,by decide⟩,⟨1216,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨1216,by decide⟩,⟨1216,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1225,by decide⟩,⟨140,by decide⟩,⟨1225,by decide⟩] | _ => ![⟨1225,by decide⟩,⟨152,by decide⟩,⟨1228,by decide⟩]

def ntree12LRRRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRRLLL i else ntree12LRRRRRLLR (i - 6)

def ntree12LRRRRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨155,by decide⟩,⟨155,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1229,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1230,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨161,by decide⟩,⟨160,by decide⟩,⟨160,by decide⟩] | 4 => ![⟨161,by decide⟩,⟨161,by decide⟩,⟨161,by decide⟩] | _ => ![⟨1051,by decide⟩,⟨144,by decide⟩,⟨1231,by decide⟩]

def ntree12LRRRRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1232,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1233,by decide⟩,⟨161,by decide⟩,⟨1233,by decide⟩] | 3 => ![⟨1234,by decide⟩,⟨1235,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨1234,by decide⟩,⟨1234,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1236,by decide⟩,⟨1236,by decide⟩,⟨0,by decide⟩]

def ntree12LRRRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRRLRL i else ntree12LRRRRRLRR (i - 6)

def ntree12LRRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRRRLL i else ntree12LRRRRRLR (i - 12)

def ntree12LRRRRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1237,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1238,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1074,by decide⟩,⟨1239,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1240,by decide⟩,⟨1075,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨1241,by decide⟩,⟨1074,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1242,by decide⟩,⟨1080,by decide⟩,⟨42,by decide⟩]

def ntree12LRRRRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1243,by decide⟩,⟨1056,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1244,by decide⟩,⟨1235,by decide⟩,⟨1063,by decide⟩] | 2 => ![⟨1244,by decide⟩,⟨1234,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨1245,by decide⟩,⟨1236,by decide⟩,⟨1062,by decide⟩] | 4 => ![⟨1062,by decide⟩,⟨1238,by decide⟩,⟨1062,by decide⟩] | _ => ![⟨1089,by decide⟩,⟨1239,by decide⟩,⟨1062,by decide⟩]

def ntree12LRRRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRRRLL i else ntree12LRRRRRRLR (i - 6)

def ntree12LRRRRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨174,by decide⟩,⟨1093,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1246,by decide⟩] | 2 => ![⟨1062,by decide⟩,⟨1237,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1247,by decide⟩] | 4 => ![⟨1248,by decide⟩,⟨1249,by decide⟩,⟨43,by decide⟩] | _ => ![⟨1250,by decide⟩,⟨1251,by decide⟩,⟨141,by decide⟩]

def ntree12LRRRRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1074,by decide⟩,⟨1252,by decide⟩,⟨196,by decide⟩] | 1 => ![⟨1080,by decide⟩,⟨1253,by decide⟩,⟨194,by decide⟩] | 2 => ![⟨1248,by decide⟩,⟨1248,by decide⟩,⟨42,by decide⟩] | 3 => ![⟨1250,by decide⟩,⟨1250,by decide⟩,⟨140,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 5 => ![⟨1254,by decide⟩,⟨1255,by decide⟩,⟨144,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1256,by decide⟩]

def ntree12LRRRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LRRRRRRRL i else ntree12LRRRRRRRR (i - 6)

def ntree12LRRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LRRRRRRL i else ntree12LRRRRRRR (i - 12)

def ntree12LRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LRRRRRL i else ntree12LRRRRRR (i - 24)

def ntree12LRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 49 then ntree12LRRRRL i else ntree12LRRRRR (i - 49)

def ntree12LRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LRRRL i else ntree12LRRRR (i - 97)

def ntree12LRR (i : Nat) : Fin 3 → Fin 2396 := if i < 194 then ntree12LRRL i else ntree12LRRR (i - 194)

def ntree12LR (i : Nat) : Fin 3 → Fin 2396 := if i < 388 then ntree12LRL i else ntree12LRR (i - 388)

def ntree12L (i : Nat) : Fin 3 → Fin 2396 := if i < 777 then ntree12LL i else ntree12LR (i - 777)

def ntree12RLLLLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1254,by decide⟩,⟨1254,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1257,by decide⟩,⟨1258,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨1259,by decide⟩,⟨1258,by decide⟩,⟨1210,by decide⟩] | 3 => ![⟨1120,by decide⟩,⟨1260,by decide⟩,⟨1211,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1260,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1261,by decide⟩,⟨0,by decide⟩,⟨1261,by decide⟩]

def ntree12RLLLLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1209,by decide⟩,⟨1260,by decide⟩,⟨1209,by decide⟩] | 2 => ![⟨1126,by decide⟩,⟨144,by decide⟩,⟨1262,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1263,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1264,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1265,by decide⟩]

def ntree12RLLLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLLLLL i else ntree12RLLLLLLLR (i - 6)

def ntree12RLLLLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1062,by decide⟩,⟨208,by decide⟩,⟨1266,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1232,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1120,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 4 => ![⟨218,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | _ => ![⟨1267,by decide⟩,⟨218,by decide⟩,⟨218,by decide⟩]

def ntree12RLLLLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1062,by decide⟩,⟨1260,by decide⟩,⟨1062,by decide⟩] | 2 => ![⟨1132,by decide⟩,⟨1268,by decide⟩,⟨1227,by decide⟩] | 3 => ![⟨1269,by decide⟩,⟨218,by decide⟩,⟨1269,by decide⟩] | 4 => ![⟨42,by decide⟩,⟨1270,by decide⟩,⟨42,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1271,by decide⟩,⟨0,by decide⟩]

def ntree12RLLLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLLLRL i else ntree12RLLLLLLRR (i - 6)

def ntree12RLLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLLLLL i else ntree12RLLLLLLR (i - 12)

def ntree12RLLLLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1272,by decide⟩,⟨1,by decide⟩,⟨1273,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1274,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1275,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨1276,by decide⟩] | 4 => ![⟨174,by decide⟩,⟨1147,by decide⟩,⟨1275,by decide⟩] | _ => ![⟨1277,by decide⟩,⟨228,by decide⟩,⟨1278,by decide⟩]

def ntree12RLLLLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1062,by decide⟩,⟨231,by decide⟩,⟨1279,by decide⟩] | 1 => ![⟨1086,by decide⟩,⟨231,by decide⟩,⟨1280,by decide⟩] | 2 => ![⟨1085,by decide⟩,⟨235,by decide⟩,⟨1281,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1147,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1085,by decide⟩,⟨1270,by decide⟩,⟨1085,by decide⟩] | _ => ![⟨1086,by decide⟩,⟨1271,by decide⟩,⟨1086,by decide⟩]

def ntree12RLLLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLLRLL i else ntree12RLLLLLRLR (i - 6)

def ntree12RLLLLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1282,by decide⟩,⟨1,by decide⟩,⟨1283,by decide⟩] | 1 => ![⟨1284,by decide⟩,⟨1235,by decide⟩,⟨1283,by decide⟩] | 2 => ![⟨1282,by decide⟩,⟨0,by decide⟩,⟨1282,by decide⟩] | 3 => ![⟨1284,by decide⟩,⟨1234,by decide⟩,⟨1282,by decide⟩] | 4 => ![⟨1285,by decide⟩,⟨42,by decide⟩,⟨1285,by decide⟩] | _ => ![⟨1282,by decide⟩,⟨1238,by decide⟩,⟨1282,by decide⟩]

def ntree12RLLLLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1286,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨1154,by decide⟩,⟨194,by decide⟩,⟨194,by decide⟩] | 2 => ![⟨1155,by decide⟩,⟨196,by decide⟩,⟨196,by decide⟩] | 3 => ![⟨1282,by decide⟩,⟨144,by decide⟩,⟨1287,by decide⟩] | 4 => ![⟨1288,by decide⟩,⟨129,by decide⟩,⟨1288,by decide⟩] | _ => ![⟨1167,by decide⟩,⟨0,by decide⟩,⟨1289,by decide⟩]

def ntree12RLLLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLLRRL i else ntree12RLLLLLRRR (i - 6)

def ntree12RLLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLLLRL i else ntree12RLLLLLRR (i - 12)

def ntree12RLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLLLLL i else ntree12RLLLLLR (i - 24)

def ntree12RLLLLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1290,by decide⟩,⟨0,by decide⟩,⟨1290,by decide⟩] | 1 => ![⟨1167,by decide⟩,⟨1260,by decide⟩,⟨1167,by decide⟩] | 2 => ![⟨1291,by decide⟩,⟨1212,by decide⟩,⟨1290,by decide⟩] | 3 => ![⟨1292,by decide⟩,⟨1212,by decide⟩,⟨1167,by decide⟩] | 4 => ![⟨1293,by decide⟩,⟨1056,by decide⟩,⟨1290,by decide⟩] | _ => ![⟨1294,by decide⟩,⟨129,by decide⟩,⟨1294,by decide⟩]

def ntree12RLLLLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1295,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1290,by decide⟩,⟨208,by decide⟩,⟨1296,by decide⟩] | 2 => ![⟨1056,by decide⟩,⟨1297,by decide⟩,⟨208,by decide⟩] | 3 => ![⟨140,by decide⟩,⟨140,by decide⟩,⟨1298,by decide⟩] | 4 => ![⟨1290,by decide⟩,⟨268,by decide⟩,⟨1299,by decide⟩] | _ => ![⟨1216,by decide⟩,⟨1216,by decide⟩,⟨1183,by decide⟩]

def ntree12RLLLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLRLLL i else ntree12RLLLLRLLR (i - 6)

def ntree12RLLLLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1300,by decide⟩,⟨1216,by decide⟩,⟨1290,by decide⟩] | 1 => ![⟨140,by decide⟩,⟨140,by decide⟩,⟨1301,by decide⟩] | 2 => ![⟨1302,by decide⟩,⟨161,by decide⟩,⟨161,by decide⟩] | 3 => ![⟨1216,by decide⟩,⟨1303,by decide⟩,⟨114,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1304,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1056,by decide⟩,⟨1305,by decide⟩,⟨231,by decide⟩]

def ntree12RLLLLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨1306,by decide⟩,⟨42,by decide⟩] | 1 => ![⟨1074,by decide⟩,⟨1307,by decide⟩,⟨282,by decide⟩] | 2 => ![⟨1074,by decide⟩,⟨1308,by decide⟩,⟨231,by decide⟩] | 3 => ![⟨1080,by decide⟩,⟨1309,by decide⟩,⟨235,by decide⟩] | 4 => ![⟨272,by decide⟩,⟨1147,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1310,by decide⟩,⟨0,by decide⟩,⟨1311,by decide⟩]

def ntree12RLLLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLRLRL i else ntree12RLLLLRLRR (i - 6)

def ntree12RLLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLLRLL i else ntree12RLLLLRLR (i - 12)

def ntree12RLLLLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1312,by decide⟩,⟨1074,by decide⟩,⟨1311,by decide⟩] | 1 => ![⟨1074,by decide⟩,⟨1074,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨291,by decide⟩,⟨1304,by decide⟩,⟨1183,by decide⟩] | 3 => ![⟨81,by decide⟩,⟨1304,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1313,by decide⟩,⟨231,by decide⟩,⟨1314,by decide⟩] | _ => ![⟨1234,by decide⟩,⟨1234,by decide⟩,⟨1183,by decide⟩]

def ntree12RLLLLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1315,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1316,by decide⟩,⟨0,by decide⟩,⟨1316,by decide⟩] | 2 => ![⟨1167,by decide⟩,⟨231,by decide⟩,⟨1317,by decide⟩] | 3 => ![⟨1120,by decide⟩,⟨1304,by decide⟩,⟨1247,by decide⟩] | 4 => ![⟨1261,by decide⟩,⟨1304,by decide⟩,⟨1261,by decide⟩] | _ => ![⟨1318,by decide⟩,⟨1074,by decide⟩,⟨1282,by decide⟩]

def ntree12RLLLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLRRLL i else ntree12RLLLLRRLR (i - 6)

def ntree12RLLLLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1216,by decide⟩,⟨1319,by decide⟩,⟨295,by decide⟩] | 1 => ![⟨1074,by decide⟩,⟨1320,by decide⟩,⟨295,by decide⟩] | 2 => ![⟨1120,by decide⟩,⟨295,by decide⟩,⟨295,by decide⟩] | 3 => ![⟨1321,by decide⟩,⟨0,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨0,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1323,by decide⟩]

def ntree12RLLLLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1045,by decide⟩,⟨0,by decide⟩,⟨1045,by decide⟩] | 1 => ![⟨1047,by decide⟩,⟨4,by decide⟩,⟨1047,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨1324,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1325,by decide⟩] | 4 => ![⟨1326,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1064,by decide⟩,⟨311,by decide⟩,⟨1327,by decide⟩] | _ => ![⟨1062,by decide⟩,⟨314,by decide⟩,⟨1328,by decide⟩]

def ntree12RLLLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLLRRRL i else ntree12RLLLLRRRR (i - 6)

def ntree12RLLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLLRRL i else ntree12RLLLLRRR (i - 12)

def ntree12RLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLLLRL i else ntree12RLLLLRR (i - 24)

def ntree12RLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12RLLLLL i else ntree12RLLLLR (i - 48)

def ntree12RLLLRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1329,by decide⟩,⟨1329,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨1330,by decide⟩,⟨1330,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨1331,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨1332,by decide⟩,⟨1332,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1100,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1333,by decide⟩,⟨1333,by decide⟩,⟨4,by decide⟩]

def ntree12RLLLRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1334,by decide⟩,⟨1334,by decide⟩,⟨48,by decide⟩] | 1 => ![⟨1335,by decide⟩,⟨1332,by decide⟩,⟨1062,by decide⟩] | 2 => ![⟨1336,by decide⟩,⟨1333,by decide⟩,⟨1064,by decide⟩] | 3 => ![⟨1337,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1338,by decide⟩]

def ntree12RLLLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRLLLL i else ntree12RLLLRLLLR (i - 6)

def ntree12RLLLRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨1339,by decide⟩] | 1 => ![⟨1332,by decide⟩,⟨1332,by decide⟩,⟨1247,by decide⟩] | 2 => ![⟨1340,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1332,by decide⟩,⟨1341,by decide⟩,⟨144,by decide⟩] | 4 => ![⟨1342,by decide⟩,⟨1216,by decide⟩,⟨1108,by decide⟩] | _ => ![⟨1108,by decide⟩,⟨144,by decide⟩,⟨1343,by decide⟩]

def ntree12RLLLRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1344,by decide⟩,⟨1216,by decide⟩,⟨1111,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨1257,by decide⟩,⟨1257,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1345,by decide⟩] | _ => ![⟨1257,by decide⟩,⟨1257,by decide⟩,⟨1211,by decide⟩]

def ntree12RLLLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRLLRL i else ntree12RLLLRLLRR (i - 6)

def ntree12RLLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLRLLL i else ntree12RLLLRLLR (i - 12)

def ntree12RLLLRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1116,by decide⟩,⟨361,by decide⟩,⟨1346,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1347,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1347,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12RLLLRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1348,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨1116,by decide⟩,⟨144,by decide⟩,⟨1349,by decide⟩] | 2 => ![⟨1118,by decide⟩,⟨323,by decide⟩,⟨1350,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1351,by decide⟩] | 4 => ![⟨1352,by decide⟩,⟨0,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨1116,by decide⟩,⟨328,by decide⟩,⟨1353,by decide⟩]

def ntree12RLLLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRLRLL i else ntree12RLLLRLRLR (i - 6)

def ntree12RLLLRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1131,by decide⟩,⟨372,by decide⟩,⟨1354,by decide⟩] | 1 => ![⟨1116,by decide⟩,⟨144,by decide⟩,⟨1355,by decide⟩] | 2 => ![⟨1062,by decide⟩,⟨362,by decide⟩,⟨1356,by decide⟩] | 3 => ![⟨1062,by decide⟩,⟨363,by decide⟩,⟨1357,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1358,by decide⟩] | _ => ![⟨1073,by decide⟩,⟨364,by decide⟩,⟨1359,by decide⟩]

def ntree12RLLLRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1360,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1361,by decide⟩,⟨1361,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1257,by decide⟩,⟨1362,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1347,by decide⟩,⟨1147,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1363,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1364,by decide⟩]

def ntree12RLLLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRLRRL i else ntree12RLLLRLRRR (i - 6)

def ntree12RLLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLRLRL i else ntree12RLLLRLRR (i - 12)

def ntree12RLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLLRLL i else ntree12RLLLRLR (i - 24)

def ntree12RLLLRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1365,by decide⟩] | 1 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨1366,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨1367,by decide⟩] | 3 => ![⟨44,by decide⟩,⟨44,by decide⟩,⟨1368,by decide⟩] | 4 => ![⟨1062,by decide⟩,⟨376,by decide⟩,⟨1369,by decide⟩] | _ => ![⟨1097,by decide⟩,⟨231,by decide⟩,⟨1370,by decide⟩]

def ntree12RLLLRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1098,by decide⟩,⟨377,by decide⟩,⟨1371,by decide⟩] | 1 => ![⟨1062,by decide⟩,⟨378,by decide⟩,⟨1372,by decide⟩] | 2 => ![⟨1073,by decide⟩,⟨379,by decide⟩,⟨1373,by decide⟩] | 3 => ![⟨1085,by decide⟩,⟨380,by decide⟩,⟨1374,by decide⟩] | 4 => ![⟨1101,by decide⟩,⟨379,by decide⟩,⟨1375,by decide⟩] | _ => ![⟨1102,by decide⟩,⟨381,by decide⟩,⟨1376,by decide⟩]

def ntree12RLLLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRRLLL i else ntree12RLLLRRLLR (i - 6)

def ntree12RLLLRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1377,by decide⟩] | 1 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1378,by decide⟩] | 2 => ![⟨1234,by decide⟩,⟨1234,by decide⟩,⟨1377,by decide⟩] | 3 => ![⟨1116,by decide⟩,⟨231,by decide⟩,⟨1379,by decide⟩] | 4 => ![⟨1380,by decide⟩,⟨1234,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12RLLLRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1381,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1382,by decide⟩] | 2 => ![⟨1152,by decide⟩,⟨144,by decide⟩,⟨1383,by decide⟩] | 3 => ![⟨1116,by decide⟩,⟨196,by decide⟩,⟨1384,by decide⟩] | 4 => ![⟨1149,by decide⟩,⟨194,by decide⟩,⟨1385,by decide⟩] | _ => ![⟨1116,by decide⟩,⟨144,by decide⟩,⟨1386,by decide⟩]

def ntree12RLLLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRRLRL i else ntree12RLLLRRLRR (i - 6)

def ntree12RLLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLRRLL i else ntree12RLLLRRLR (i - 12)

def ntree12RLLLRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨1387,by decide⟩] | 1 => ![⟨1108,by decide⟩,⟨144,by decide⟩,⟨1343,by decide⟩] | 2 => ![⟨1116,by decide⟩,⟨144,by decide⟩,⟨1388,by decide⟩] | 3 => ![⟨1162,by decide⟩,⟨260,by decide⟩,⟨1389,by decide⟩] | 4 => ![⟨1109,by decide⟩,⟨231,by decide⟩,⟨1390,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1391,by decide⟩]

def ntree12RLLLRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1113,by decide⟩,⟨231,by decide⟩,⟨1392,by decide⟩] | 1 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨1393,by decide⟩] | 2 => ![⟨1111,by decide⟩,⟨231,by decide⟩,⟨1394,by decide⟩] | 3 => ![⟨1112,by decide⟩,⟨235,by decide⟩,⟨1395,by decide⟩] | 4 => ![⟨1396,by decide⟩,⟨1216,by decide⟩,⟨1180,by decide⟩] | _ => ![⟨1397,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩]

def ntree12RLLLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRRRLL i else ntree12RLLLRRRLR (i - 6)

def ntree12RLLLRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1216,by decide⟩,⟨1398,by decide⟩,⟨397,by decide⟩] | 1 => ![⟨1116,by decide⟩,⟨397,by decide⟩,⟨1399,by decide⟩] | 2 => ![⟨1400,by decide⟩,⟨1330,by decide⟩,⟨1116,by decide⟩] | 3 => ![⟨1212,by decide⟩,⟨1401,by decide⟩,⟨406,by decide⟩] | 4 => ![⟨1397,by decide⟩,⟨1191,by decide⟩,⟨4,by decide⟩] | _ => ![⟨272,by decide⟩,⟨1192,by decide⟩,⟨0,by decide⟩]

def ntree12RLLLRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1167,by decide⟩,⟨406,by decide⟩,⟨1402,by decide⟩] | 1 => ![⟨1169,by decide⟩,⟨409,by decide⟩,⟨1403,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1404,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1116,by decide⟩,⟨295,by decide⟩,⟨1405,by decide⟩] | 4 => ![⟨1406,by decide⟩,⟨1406,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1407,by decide⟩,⟨1,by decide⟩,⟨1408,by decide⟩] | _ => ![⟨1409,by decide⟩,⟨5,by decide⟩,⟨1410,by decide⟩]

def ntree12RLLLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLLRRRRL i else ntree12RLLLRRRRR (i - 6)

def ntree12RLLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLLRRRL i else ntree12RLLLRRRR (i - 12)

def ntree12RLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLLRRL i else ntree12RLLLRRR (i - 24)

def ntree12RLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12RLLLRL i else ntree12RLLLRR (i - 48)

def ntree12RLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12RLLLL i else ntree12RLLLR (i - 97)

def ntree12RLLRLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1407,by decide⟩,⟨0,by decide⟩,⟨1407,by decide⟩] | 1 => ![⟨1409,by decide⟩,⟨4,by decide⟩,⟨1409,by decide⟩] | 2 => ![⟨1407,by decide⟩,⟨437,by decide⟩,⟨1411,by decide⟩] | 3 => ![⟨1412,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1412,by decide⟩,⟨0,by decide⟩,⟨1061,by decide⟩] | _ => ![⟨1413,by decide⟩,⟨1406,by decide⟩,⟨1407,by decide⟩]

def ntree12RLLRLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1414,by decide⟩,⟨444,by decide⟩,⟨1415,by decide⟩] | 1 => ![⟨1416,by decide⟩,⟨446,by decide⟩,⟨1417,by decide⟩] | 2 => ![⟨1414,by decide⟩,⟨443,by decide⟩,⟨1414,by decide⟩] | 3 => ![⟨1416,by decide⟩,⟨445,by decide⟩,⟨1416,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1418,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1419,by decide⟩,⟨1420,by decide⟩,⟨30,by decide⟩]

def ntree12RLLRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLLLLL i else ntree12RLLRLLLLR (i - 6)

def ntree12RLLRLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1053,by decide⟩,⟨1418,by decide⟩,⟨1053,by decide⟩] | 1 => ![⟨1419,by decide⟩,⟨1419,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1414,by decide⟩,⟨451,by decide⟩,⟨1421,by decide⟩] | 3 => ![⟨1422,by decide⟩,⟨1422,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1423,by decide⟩] | _ => ![⟨1424,by decide⟩,⟨30,by decide⟩,⟨1425,by decide⟩]

def ntree12RLLRLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1424,by decide⟩,⟨0,by decide⟩,⟨1424,by decide⟩] | 1 => ![⟨1086,by decide⟩,⟨433,by decide⟩,⟨1426,by decide⟩] | 2 => ![⟨474,by decide⟩,⟨0,by decide⟩,⟨1061,by decide⟩] | 3 => ![⟨1427,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨474,by decide⟩,⟨0,by decide⟩,⟨1105,by decide⟩] | _ => ![⟨1427,by decide⟩,⟨42,by decide⟩,⟨1106,by decide⟩]

def ntree12RLLRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLLLRL i else ntree12RLLRLLLRR (i - 6)

def ntree12RLLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRLLLL i else ntree12RLLRLLLR (i - 12)

def ntree12RLLRLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1428,by decide⟩,⟨481,by decide⟩,⟨1428,by decide⟩] | 1 => ![⟨1429,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨1429,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1430,by decide⟩,⟨499,by decide⟩,⟨1431,by decide⟩] | 4 => ![⟨1430,by decide⟩,⟨498,by decide⟩,⟨1430,by decide⟩] | _ => ![⟨1116,by decide⟩,⟨437,by decide⟩,⟨1432,by decide⟩]

def ntree12RLLRLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1433,by decide⟩,⟨506,by decide⟩,⟨1434,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1412,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨1433,by decide⟩,⟨0,by decide⟩,⟨1433,by decide⟩] | 4 => ![⟨1435,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | _ => ![⟨1435,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12RLLRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLLRLL i else ntree12RLLRLLRLR (i - 6)

def ntree12RLLRLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1436,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1437,by decide⟩,⟨514,by decide⟩,⟨1438,by decide⟩] | 2 => ![⟨1437,by decide⟩,⟨513,by decide⟩,⟨1437,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1062,by decide⟩,⟨1439,by decide⟩,⟨1062,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1440,by decide⟩]

def ntree12RLLRLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1441,by decide⟩,⟨1441,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1116,by decide⟩,⟨523,by decide⟩,⟨1442,by decide⟩] | 2 => ![⟨1429,by decide⟩,⟨1418,by decide⟩,⟨1440,by decide⟩] | 3 => ![⟨1062,by decide⟩,⟨506,by decide⟩,⟨1443,by decide⟩] | 4 => ![⟨1131,by decide⟩,⟨525,by decide⟩,⟨1444,by decide⟩] | _ => ![⟨0,by decide⟩,⟨37,by decide⟩,⟨1445,by decide⟩]

def ntree12RLLRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLLRRL i else ntree12RLLRLLRRR (i - 6)

def ntree12RLLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRLLRL i else ntree12RLLRLLRR (i - 12)

def ntree12RLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLRLLL i else ntree12RLLRLLR (i - 24)

def ntree12RLLRLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1446,by decide⟩,⟨1441,by decide⟩,⟨1062,by decide⟩] | 1 => ![⟨1447,by decide⟩,⟨1448,by decide⟩,⟨499,by decide⟩] | 2 => ![⟨1449,by decide⟩,⟨1450,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨498,by decide⟩,⟨1451,by decide⟩,⟨498,by decide⟩] | 4 => ![⟨1452,by decide⟩,⟨1453,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1135,by decide⟩,⟨1454,by decide⟩,⟨506,by decide⟩]

def ntree12RLLRLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1455,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1436,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨1456,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1144,by decide⟩,⟨1440,by decide⟩] | 4 => ![⟨1424,by decide⟩,⟨0,by decide⟩,⟨1457,by decide⟩] | _ => ![⟨1062,by decide⟩,⟨1458,by decide⟩,⟨1443,by decide⟩]

def ntree12RLLRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLRLLL i else ntree12RLLRLRLLR (i - 6)

def ntree12RLLRLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1085,by decide⟩,⟨535,by decide⟩,⟨1459,by decide⟩] | 1 => ![⟨1086,by decide⟩,⟨536,by decide⟩,⟨1460,by decide⟩] | 2 => ![⟨1461,by decide⟩,⟨1,by decide⟩,⟨1117,by decide⟩] | 3 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1116,by decide⟩] | 4 => ![⟨1462,by decide⟩,⟨1453,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨544,by decide⟩,⟨0,by decide⟩,⟨1124,by decide⟩]

def ntree12RLLRLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1463,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1464,by decide⟩,⟨1464,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1464,by decide⟩,⟨1465,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1439,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1440,by decide⟩] | _ => ![⟨1461,by decide⟩,⟨0,by decide⟩,⟨1116,by decide⟩]

def ntree12RLLRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLRLRL i else ntree12RLLRLRLRR (i - 6)

def ntree12RLLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRLRLL i else ntree12RLLRLRLR (i - 12)

def ntree12RLLRLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1165,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1167,by decide⟩,⟨506,by decide⟩,⟨1466,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1467,by decide⟩] | 3 => ![⟨1169,by decide⟩,⟨553,by decide⟩,⟨1468,by decide⟩] | 4 => ![⟨1116,by decide⟩,⟨554,by decide⟩,⟨1469,by decide⟩] | _ => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨1470,by decide⟩]

def ntree12RLLRLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨1471,by decide⟩] | 1 => ![⟨445,by decide⟩,⟨445,by decide⟩,⟨1472,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1473,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨443,by decide⟩,⟨1474,by decide⟩,⟨443,by decide⟩] | 4 => ![⟨1116,by decide⟩,⟨1473,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨1475,by decide⟩,⟨0,by decide⟩,⟨1475,by decide⟩]

def ntree12RLLRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLRRLL i else ntree12RLLRLRRLR (i - 6)

def ntree12RLLRLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1476,by decide⟩,⟨443,by decide⟩,⟨1476,by decide⟩] | 1 => ![⟨1475,by decide⟩,⟨506,by decide⟩,⟨1477,by decide⟩] | 2 => ![⟨1476,by decide⟩,⟨564,by decide⟩,⟨1478,by decide⟩] | 3 => ![⟨1479,by decide⟩,⟨38,by decide⟩,⟨1479,by decide⟩] | 4 => ![⟨1406,by decide⟩,⟨1480,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1458,by decide⟩,⟨506,by decide⟩]

def ntree12RLLRLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1481,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1082,by decide⟩,⟨1482,by decide⟩,⟨506,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨1483,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1484,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1485,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1485,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1485,by decide⟩,⟨1486,by decide⟩,⟨1183,by decide⟩]

def ntree12RLLRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRLRRRL i else ntree12RLLRLRRRR (i - 6)

def ntree12RLLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRLRRL i else ntree12RLLRLRRR (i - 12)

def ntree12RLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLRLRL i else ntree12RLLRLRR (i - 24)

def ntree12RLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12RLLRLL i else ntree12RLLRLR (i - 48)

def ntree12RLLRRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1487,by decide⟩,⟨1484,by decide⟩,⟨1183,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1486,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1488,by decide⟩,⟨42,by decide⟩,⟨1488,by decide⟩] | 3 => ![⟨579,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1475,by decide⟩,⟨0,by decide⟩,⟨1489,by decide⟩] | _ => ![⟨1490,by decide⟩,⟨0,by decide⟩,⟨1167,by decide⟩]

def ntree12RLLRRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1491,by decide⟩,⟨4,by decide⟩,⟨1169,by decide⟩] | 1 => ![⟨1492,by decide⟩,⟨0,by decide⟩,⟨1167,by decide⟩] | 2 => ![⟨1493,by decide⟩,⟨0,by decide⟩,⟨1116,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1486,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨544,by decide⟩,⟨1484,by decide⟩,⟨1061,by decide⟩] | _ => ![⟨1494,by decide⟩,⟨479,by decide⟩,⟨1494,by decide⟩]

def ntree12RLLRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRLLLL i else ntree12RLLRRLLLR (i - 6)

def ntree12RLLRRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1495,by decide⟩,⟨481,by decide⟩,⟨1495,by decide⟩] | 1 => ![⟨1496,by decide⟩,⟨1497,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1498,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1499,by decide⟩,⟨1497,by decide⟩,⟨1408,by decide⟩] | 4 => ![⟨1212,by decide⟩,⟨1500,by decide⟩,⟨433,by decide⟩] | _ => ![⟨1407,by decide⟩,⟨1498,by decide⟩,⟨1407,by decide⟩]

def ntree12RLLRRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1501,by decide⟩,⟨1212,by decide⟩,⟨1407,by decide⟩] | 1 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1499,by decide⟩,⟨1496,by decide⟩,⟨1407,by decide⟩] | 3 => ![⟨1502,by decide⟩,⟨1503,by decide⟩,⟨444,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨1504,by decide⟩,⟨443,by decide⟩] | _ => ![⟨1505,by decide⟩,⟨1497,by decide⟩,⟨1063,by decide⟩]

def ntree12RLLRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRLLRL i else ntree12RLLRRLLRR (i - 6)

def ntree12RLLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRRLLL i else ntree12RLLRRLLR (i - 12)

def ntree12RLLRRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1506,by decide⟩,⟨1503,by decide⟩,⟨1415,by decide⟩] | 1 => ![⟨1062,by decide⟩,⟨1498,by decide⟩,⟨1062,by decide⟩] | 2 => ![⟨1414,by decide⟩,⟨1504,by decide⟩,⟨1414,by decide⟩] | 3 => ![⟨1505,by decide⟩,⟨1496,by decide⟩,⟨1062,by decide⟩] | 4 => ![⟨1506,by decide⟩,⟨1502,by decide⟩,⟨1414,by decide⟩] | _ => ![⟨1502,by decide⟩,⟨1502,by decide⟩,⟨443,by decide⟩]

def ntree12RLLRRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1507,by decide⟩,⟨1507,by decide⟩,⟨161,by decide⟩] | 1 => ![⟨1496,by decide⟩,⟨1508,by decide⟩,⟨37,by decide⟩] | 2 => ![⟨1062,by decide⟩,⟨1509,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨1510,by decide⟩,⟨1511,by decide⟩,⟨43,by decide⟩] | 4 => ![⟨42,by decide⟩,⟨1512,by decide⟩,⟨42,by decide⟩] | _ => ![⟨1510,by decide⟩,⟨1510,by decide⟩,⟨42,by decide⟩]

def ntree12RLLRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRLRLL i else ntree12RLLRRLRLR (i - 6)

def ntree12RLLRRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1513,by decide⟩,⟨1510,by decide⟩,⟨1085,by decide⟩] | 1 => ![⟨1514,by decide⟩,⟨1496,by decide⟩,⟨1086,by decide⟩] | 2 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1423,by decide⟩] | 3 => ![⟨1515,by decide⟩,⟨0,by decide⟩,⟨1515,by decide⟩] | 4 => ![⟨1516,by decide⟩,⟨605,by decide⟩,⟨1516,by decide⟩] | _ => ![⟨494,by decide⟩,⟨1498,by decide⟩,⟨1247,by decide⟩]

def ntree12RLLRRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨591,by decide⟩,⟨0,by decide⟩,⟨1247,by decide⟩] | 1 => ![⟨1517,by decide⟩,⟨1518,by decide⟩,⟨480,by decide⟩] | 2 => ![⟨1519,by decide⟩,⟨1520,by decide⟩,⟨482,by decide⟩] | 3 => ![⟨479,by decide⟩,⟨1521,by decide⟩,⟨479,by decide⟩] | 4 => ![⟨1517,by decide⟩,⟨1517,by decide⟩,⟨479,by decide⟩] | _ => ![⟨1519,by decide⟩,⟨1519,by decide⟩,⟨481,by decide⟩]

def ntree12RLLRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRLRRL i else ntree12RLLRRLRRR (i - 6)

def ntree12RLLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRRLRL i else ntree12RLLRRLRR (i - 12)

def ntree12RLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLRRLL i else ntree12RLLRRLR (i - 24)

def ntree12RLLRRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1522,by decide⟩,⟨1523,by decide⟩,⟨499,by decide⟩] | 1 => ![⟨498,by decide⟩,⟨1524,by decide⟩,⟨498,by decide⟩] | 2 => ![⟨1496,by decide⟩,⟨1525,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨1526,by decide⟩,⟨1496,by decide⟩,⟨1261,by decide⟩] | 4 => ![⟨1261,by decide⟩,⟨506,by decide⟩,⟨1527,by decide⟩] | _ => ![⟨1436,by decide⟩,⟨1498,by decide⟩,⟨1264,by decide⟩]

def ntree12RLLRRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1264,by decide⟩] | 1 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1440,by decide⟩] | 2 => ![⟨1528,by decide⟩,⟨1528,by decide⟩,⟨218,by decide⟩] | 3 => ![⟨218,by decide⟩,⟨218,by decide⟩,⟨1529,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1440,by decide⟩] | _ => ![⟨1505,by decide⟩,⟨1525,by decide⟩,⟨1443,by decide⟩]

def ntree12RLLRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRRLLL i else ntree12RLLRRRLLR (i - 6)

def ntree12RLLRRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1496,by decide⟩,⟨1508,by decide⟩,⟨1445,by decide⟩] | 1 => ![⟨1062,by decide⟩,⟨1530,by decide⟩,⟨1443,by decide⟩] | 2 => ![⟨1531,by decide⟩,⟨1528,by decide⟩,⟨1269,by decide⟩] | 3 => ![⟨1269,by decide⟩,⟨630,by decide⟩,⟨1532,by decide⟩] | 4 => ![⟨1261,by decide⟩,⟨0,by decide⟩,⟨1533,by decide⟩] | _ => ![⟨1534,by decide⟩,⟨1535,by decide⟩,⟨228,by decide⟩]

def ntree12RLLRRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1536,by decide⟩,⟨1537,by decide⟩,⟨231,by decide⟩] | 1 => ![⟨1510,by decide⟩,⟨1538,by decide⟩,⟨535,by decide⟩] | 2 => ![⟨1496,by decide⟩,⟨1539,by decide⟩,⟨536,by decide⟩] | 3 => ![⟨1496,by decide⟩,⟨1540,by decide⟩,⟨231,by decide⟩] | 4 => ![⟨1541,by decide⟩,⟨1498,by decide⟩,⟨1275,by decide⟩] | _ => ![⟨1510,by decide⟩,⟨1510,by decide⟩,⟨1456,by decide⟩]

def ntree12RLLRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRRLRL i else ntree12RLLRRRLRR (i - 6)

def ntree12RLLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRRRLL i else ntree12RLLRRRLR (i - 12)

def ntree12RLLRRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨605,by decide⟩,⟨605,by decide⟩,⟨1542,by decide⟩] | 1 => ![⟨1515,by decide⟩,⟨231,by decide⟩,⟨1543,by decide⟩] | 2 => ![⟨1516,by decide⟩,⟨635,by decide⟩,⟨1544,by decide⟩] | 3 => ![⟨1513,by decide⟩,⟨1538,by decide⟩,⟨1459,by decide⟩] | 4 => ![⟨1514,by decide⟩,⟨1539,by decide⟩,⟨1460,by decide⟩] | _ => ![⟨1545,by decide⟩,⟨1497,by decide⟩,⟨1283,by decide⟩]

def ntree12RLLRRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1282,by decide⟩,⟨1498,by decide⟩,⟨1282,by decide⟩] | 1 => ![⟨1546,by decide⟩,⟨1510,by decide⟩,⟨1285,by decide⟩] | 2 => ![⟨1545,by decide⟩,⟨1496,by decide⟩,⟨1282,by decide⟩] | 3 => ![⟨1282,by decide⟩,⟨0,by decide⟩,⟨1547,by decide⟩] | 4 => ![⟨1285,by decide⟩,⟨42,by decide⟩,⟨1548,by decide⟩] | _ => ![⟨1549,by decide⟩,⟨1496,by decide⟩,⟨1167,by decide⟩]

def ntree12RLLRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRRRLL i else ntree12RLLRRRRLR (i - 6)

def ntree12RLLRRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1550,by decide⟩,⟨0,by decide⟩,⟨1550,by decide⟩] | 1 => ![⟨1551,by decide⟩,⟨0,by decide⟩,⟨1551,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1552,by decide⟩] | 3 => ![⟨1549,by decide⟩,⟨1525,by decide⟩,⟨1466,by decide⟩] | 4 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1467,by decide⟩] | _ => ![⟨1553,by decide⟩,⟨0,by decide⟩,⟨1553,by decide⟩]

def ntree12RLLRRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1553,by decide⟩,⟨0,by decide⟩,⟨1554,by decide⟩] | 1 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1183,by decide⟩] | 2 => ![⟨1502,by decide⟩,⟨1502,by decide⟩,⟨1471,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨443,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨643,by decide⟩,⟨643,by decide⟩] | _ => ![⟨1502,by decide⟩,⟨1555,by decide⟩,⟨564,by decide⟩]

def ntree12RLLRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLLRRRRRL i else ntree12RLLRRRRRR (i - 6)

def ntree12RLLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLLRRRRL i else ntree12RLLRRRRR (i - 12)

def ntree12RLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLLRRRL i else ntree12RLLRRRR (i - 24)

def ntree12RLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12RLLRRL i else ntree12RLLRRR (i - 48)

def ntree12RLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12RLLRL i else ntree12RLLRR (i - 97)

def ntree12RLL (i : Nat) : Fin 3 → Fin 2396 := if i < 194 then ntree12RLLL i else ntree12RLLR (i - 194)

def ntree12RLRLLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1496,by decide⟩,⟨1556,by decide⟩,⟨114,by decide⟩] | 1 => ![⟨443,by decide⟩,⟨1557,by decide⟩,⟨443,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1558,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨161,by decide⟩,⟨653,by decide⟩,⟨653,by decide⟩] | 4 => ![⟨1559,by decide⟩,⟨1419,by decide⟩,⟨1261,by decide⟩] | _ => ![⟨1560,by decide⟩,⟨506,by decide⟩,⟨1561,by decide⟩]

def ntree12RLRLLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1560,by decide⟩,⟨0,by decide⟩,⟨1560,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1271,by decide⟩,⟨1423,by decide⟩] | 2 => ![⟨1562,by decide⟩,⟨1496,by decide⟩,⟨1316,by decide⟩] | 3 => ![⟨1563,by decide⟩,⟨443,by decide⟩,⟨1563,by decide⟩] | 4 => ![⟨1261,by decide⟩,⟨681,by decide⟩,⟨1564,by decide⟩] | _ => ![⟨1565,by decide⟩,⟨1565,by decide⟩,⟨4,by decide⟩]

def ntree12RLRLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLLLLL i else ntree12RLRLLLLLR (i - 6)

def ntree12RLRLLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1566,by decide⟩,⟨1566,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1567,by decide⟩,⟨1566,by decide⟩,⟨1053,by decide⟩] | 2 => ![⟨1568,by decide⟩,⟨1565,by decide⟩,⟨1064,by decide⟩] | 3 => ![⟨1569,by decide⟩,⟨1566,by decide⟩,⟨1062,by decide⟩] | 4 => ![⟨1496,by decide⟩,⟨1570,by decide⟩,⟨328,by decide⟩] | _ => ![⟨1571,by decide⟩,⟨1571,by decide⟩,⟨38,by decide⟩]

def ntree12RLRLLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1572,by decide⟩,⟨1572,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1573,by decide⟩,⟨1573,by decide⟩,⟨46,by decide⟩] | 2 => ![⟨1574,by decide⟩,⟨1574,by decide⟩,⟨42,by decide⟩] | 3 => ![⟨1575,by decide⟩,⟨1573,by decide⟩,⟨1087,by decide⟩] | 4 => ![⟨1576,by decide⟩,⟨1565,by decide⟩,⟨1088,by decide⟩] | _ => ![⟨1577,by decide⟩,⟨1574,by decide⟩,⟨1085,by decide⟩]

def ntree12RLRLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLLLRL i else ntree12RLRLLLLRR (i - 6)

def ntree12RLRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLRLLLLL i else ntree12RLRLLLLR (i - 12)

def ntree12RLRLLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1578,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1578,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨1579,by decide⟩] | 3 => ![⟨1496,by decide⟩,⟨1580,by decide⟩,⟨736,by decide⟩] | 4 => ![⟨1581,by decide⟩,⟨1496,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨1116,by decide⟩,⟨736,by decide⟩,⟨1582,by decide⟩]

def ntree12RLRLLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1583,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1583,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1584,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1584,by decide⟩] | _ => ![⟨1522,by decide⟩,⟨1522,by decide⟩,⟨498,by decide⟩]

def ntree12RLRLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLLRLL i else ntree12RLRLLLRLR (i - 6)

def ntree12RLRLLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1585,by decide⟩] | 2 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1586,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1586,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1587,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1588,by decide⟩,⟨736,by decide⟩]

def ntree12RLRLLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1116,by decide⟩,⟨328,by decide⟩,⟨1353,by decide⟩] | 1 => ![⟨1589,by decide⟩,⟨1590,by decide⟩,⟨1131,by decide⟩] | 2 => ![⟨1591,by decide⟩,⟨1592,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨1496,by decide⟩,⟨1593,by decide⟩,⟨753,by decide⟩] | 4 => ![⟨1510,by decide⟩,⟨1594,by decide⟩,⟨755,by decide⟩] | _ => ![⟨1522,by decide⟩,⟨1595,by decide⟩,⟨758,by decide⟩]

def ntree12RLRLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLLRRL i else ntree12RLRLLLRRR (i - 6)

def ntree12RLRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLRLLLRL i else ntree12RLRLLLRR (i - 12)

def ntree12RLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLRLLLL i else ntree12RLRLLLR (i - 24)

def ntree12RLRLLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1424,by decide⟩,⟨736,by decide⟩,⟨1596,by decide⟩] | 1 => ![⟨1505,by decide⟩,⟨1593,by decide⟩,⟨1597,by decide⟩] | 2 => ![⟨1062,by decide⟩,⟨753,by decide⟩,⟨1597,by decide⟩] | 3 => ![⟨1598,by decide⟩,⟨1510,by decide⟩,⟨1149,by decide⟩] | 4 => ![⟨1599,by decide⟩,⟨1496,by decide⟩,⟨1152,by decide⟩] | _ => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1377,by decide⟩]

def ntree12RLRLLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1581,by decide⟩,⟨1496,by decide⟩,⟨1378,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨770,by decide⟩,⟨770,by decide⟩] | 2 => ![⟨1496,by decide⟩,⟨1496,by decide⟩,⟨1600,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1600,by decide⟩] | 4 => ![⟨1116,by decide⟩,⟨0,by decide⟩,⟨1601,by decide⟩] | _ => ![⟨1602,by decide⟩,⟨1565,by decide⟩,⟨1169,by decide⟩]

def ntree12RLRLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLRLLL i else ntree12RLRLLRLLR (i - 6)

def ntree12RLRLLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1603,by decide⟩,⟨1566,by decide⟩,⟨1167,by decide⟩] | 1 => ![⟨1496,by decide⟩,⟨1604,by decide⟩,⟨397,by decide⟩] | 2 => ![⟨1502,by decide⟩,⟨1605,by decide⟩,⟨779,by decide⟩] | 3 => ![⟨1581,by decide⟩,⟨1604,by decide⟩,⟨1399,by decide⟩] | 4 => ![⟨1475,by decide⟩,⟨397,by decide⟩,⟨1606,by decide⟩] | _ => ![⟨1476,by decide⟩,⟨779,by decide⟩,⟨1607,by decide⟩]

def ntree12RLRLLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1475,by decide⟩,⟨736,by decide⟩,⟨1608,by decide⟩] | 1 => ![⟨1609,by decide⟩,⟨1572,by decide⟩,⟨1116,by decide⟩] | 2 => ![⟨1496,by decide⟩,⟨1610,by decide⟩,⟨406,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1611,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1565,by decide⟩,⟨1612,by decide⟩,⟨409,by decide⟩] | _ => ![⟨1566,by decide⟩,⟨1613,by decide⟩,⟨231,by decide⟩]

def ntree12RLRLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLRLRL i else ntree12RLRLLRLRR (i - 6)

def ntree12RLRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLRLLRLL i else ntree12RLRLLRLR (i - 12)

def ntree12RLRLLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1475,by decide⟩,⟨753,by decide⟩,⟨1614,by decide⟩] | 1 => ![⟨1488,by decide⟩,⟨755,by decide⟩,⟨1615,by decide⟩] | 2 => ![⟨1475,by decide⟩,⟨231,by decide⟩,⟨1616,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1144,by decide⟩,⟨1578,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1617,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1475,by decide⟩,⟨681,by decide⟩,⟨1618,by decide⟩]

def ntree12RLRLLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1476,by decide⟩,⟨682,by decide⟩,⟨1619,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1061,by decide⟩] | 2 => ![⟨1620,by decide⟩,⟨2,by decide⟩,⟨1620,by decide⟩] | 3 => ![⟨1407,by decide⟩,⟨793,by decide⟩,⟨1621,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1622,by decide⟩,⟨0,by decide⟩] | _ => ![⟨4,by decide⟩,⟨1623,by decide⟩,⟨4,by decide⟩]

def ntree12RLRLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLRRLL i else ntree12RLRLLRRLR (i - 6)

def ntree12RLRLLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1622,by decide⟩,⟨1060,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1624,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨443,by decide⟩,⟨1625,by decide⟩] | 3 => ![⟨1062,by decide⟩,⟨1622,by decide⟩,⟨1062,by decide⟩] | 4 => ![⟨1064,by decide⟩,⟨1623,by decide⟩,⟨1064,by decide⟩] | _ => ![⟨1062,by decide⟩,⟨793,by decide⟩,⟨1626,by decide⟩]

def ntree12RLRLLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1414,by decide⟩,⟨798,by decide⟩,⟨1627,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨1628,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨1629,by decide⟩,⟨799,by decide⟩,⟨1629,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨806,by decide⟩,⟨806,by decide⟩] | 4 => ![⟨1074,by decide⟩,⟨1630,by decide⟩,⟨793,by decide⟩] | 5 => ![⟨1074,by decide⟩,⟨1631,by decide⟩,⟨437,by decide⟩] | _ => ![⟨1632,by decide⟩,⟨0,by decide⟩,⟨1632,by decide⟩]

def ntree12RLRLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLLRRRL i else ntree12RLRLLRRRR (i - 6)

def ntree12RLRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLRLLRRL i else ntree12RLRLLRRR (i - 12)

def ntree12RLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12RLRLLRL i else ntree12RLRLLRR (i - 24)

def ntree12RLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12RLRLLL i else ntree12RLRLLR (i - 48)

def ntree12RLRLRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1074,by decide⟩,⟨1074,by decide⟩,⟨1624,by decide⟩] | 1 => ![⟨1633,by decide⟩,⟨808,by decide⟩,⟨1633,by decide⟩] | 2 => ![⟨1089,by decide⟩,⟨1630,by decide⟩,⟨1626,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1634,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1635,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12RLRLRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1636,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨0,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨1638,by decide⟩,⟨1074,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨1074,by decide⟩,⟨1639,by decide⟩,⟨832,by decide⟩] | 4 => ![⟨1640,by decide⟩,⟨1640,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1641,by decide⟩,⟨1641,by decide⟩,⟨443,by decide⟩]

def ntree12RLRLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLRLLLL i else ntree12RLRLRLLLR (i - 6)

def ntree12RLRLRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1642,by decide⟩,⟨1642,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨1643,by decide⟩,⟨1643,by decide⟩,⟨445,by decide⟩] | 2 => ![⟨808,by decide⟩,⟨1644,by decide⟩,⟨808,by decide⟩] | 3 => ![⟨1640,by decide⟩,⟨1645,by decide⟩,⟨793,by decide⟩] | 4 => ![⟨1641,by decide⟩,⟨1646,by decide⟩,⟨798,by decide⟩] | _ => ![⟨1642,by decide⟩,⟨1647,by decide⟩,⟨26,by decide⟩]

def ntree12RLRLRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨1640,by decide⟩,⟨1648,by decide⟩,⟨27,by decide⟩] | 1 => ![⟨1424,by decide⟩,⟨1622,by decide⟩,⟨1424,by decide⟩] | 2 => ![⟨1649,by decide⟩,⟨1649,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1650,by decide⟩,⟨1650,by decide⟩,⟨443,by decide⟩] | 4 => ![⟨1651,by decide⟩,⟨443,by decide⟩,⟨1651,by decide⟩] | _ => ![⟨1649,by decide⟩,⟨1652,by decide⟩,⟨25,by decide⟩]

def ntree12RLRLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12RLRLRLLRL i else ntree12RLRLRLLRR (i - 6)

def ntree12RLRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12RLRLRLLL i else ntree12RLRLRLLR (i - 12)

def ntree12RLRLRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨1120,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 2 => ![⟨1653,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1120,by decide⟩,⟨437,by decide⟩,⟨437,by decide⟩] | 4 => ![⟨1654,by decide⟩,⟨1655,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨506,by decide⟩,⟨1656,by decide⟩]

end Paper2.Certificates.Q6.Coverage

import Paper2.Certificates.Q6CoverageCompact.Layer11Part005

namespace Paper2.Certificates.Q6.Coverage

def state11_3072 : State := natState 843954251586625525994305355719543336

def state11_3073 : State := natState 1609714952785719448922533920768

def state11_3074 : State := natState 20770876396898917194635875351269440

def state11_3075 : State := natState 20770877615496870699773704660848704

def state11_3076 : State := natState 836814874857554261099268570607681640

def state11_3077 : State := natState 841033616055113808551108773572411496

def state11_3078 : State := natState 421874120142811830445209174003499008

def state11_3079 : State := natState 238727180290988485611153602239431936

def state11_3080 : State := natState 415385358397834107412079479300900096

def state11_3081 : State := natState 6642489532148119340956645586904320

def state11_3082 : State := natState 415385333639033321704473981653959936

def state11_3083 : State := natState 415385352208133910985178104872387840

def state11_3084 : State := natState 457672758398011799937678377833473280

def state11_3085 : State := natState 415469973682404003020306866355840256

def state11_3086 : State := natState 415535891513615871183371875545785600

def state11_3087 : State := natState 457672733639211014230072880186533120

def state11_3088 : State := natState 457672749732431524940016453606712576

def state11_3089 : State := natState 594561734937458137096717954021673472

def state11_3090 : State := natState 478681663467671893447652779869684992

def state11_3091 : State := natState 415399146626594122317622905387361536

def state11_3092 : State := natState 584143723907227571831178445401367808

def state11_3093 : State := natState 415386918595278980841907932815770880

def state11_3094 : State := natState 20772383343372906072486959187497024

def state11_3095 : State := natState 843837659182818651983560306365311528

def state11_3096 : State := natState 843903577014030520146625315555256872

def state11_3097 : State := natState 415485185489606077692589973064123648

def state11_3098 : State := natState 220827941610450811472846239513528832

def state11_3099 : State := natState 836698251002333263994330873912631400

def state11_3100 : State := natState 840916992199892811446171076877361256

def state11_3101 : State := natState 836764168833545132157395883102576744

def state11_3102 : State := natState 6593367690482530622944923503117568

def state11_3103 : State := natState 768870759489133812371331326897635392

def state11_3104 : State := natState 208168616598584296256785965323206720

def state11_3105 : State := natState 457672731163330271578214526738244864

def state11_3106 : State := natState 442648457020961275187012630245097536

def state11_3107 : State := natState 238531464261002443722078830130111744

def state11_3108 : State := natState 795080783785204280157443205232076032

def stree11LLLLLLLLL (i : Nat) : State := match i with | 0 => state11_0 | 1 => state11_1 | 2 => state11_2 | 3 => state11_3 | 4 => state11_4 | _ => state11_5

def stree11LLLLLLLLR (i : Nat) : State := match i with | 0 => state11_6 | 1 => state11_7 | 2 => state11_8 | 3 => state11_9 | 4 => state11_10 | _ => state11_11

def stree11LLLLLLLL (i : Nat) : State := if i < 6 then stree11LLLLLLLLL i else stree11LLLLLLLLR (i - 6)

def stree11LLLLLLLRL (i : Nat) : State := match i with | 0 => state11_12 | 1 => state11_13 | 2 => state11_14 | 3 => state11_15 | 4 => state11_16 | _ => state11_17

def stree11LLLLLLLRR (i : Nat) : State := match i with | 0 => state11_18 | 1 => state11_19 | 2 => state11_20 | 3 => state11_21 | 4 => state11_22 | _ => state11_23

def stree11LLLLLLLR (i : Nat) : State := if i < 6 then stree11LLLLLLLRL i else stree11LLLLLLLRR (i - 6)

def stree11LLLLLLL (i : Nat) : State := if i < 12 then stree11LLLLLLLL i else stree11LLLLLLLR (i - 12)

def stree11LLLLLLRLL (i : Nat) : State := match i with | 0 => state11_24 | 1 => state11_25 | 2 => state11_26 | 3 => state11_27 | 4 => state11_28 | _ => state11_29

def stree11LLLLLLRLR (i : Nat) : State := match i with | 0 => state11_30 | 1 => state11_31 | 2 => state11_32 | 3 => state11_33 | 4 => state11_34 | _ => state11_35

def stree11LLLLLLRL (i : Nat) : State := if i < 6 then stree11LLLLLLRLL i else stree11LLLLLLRLR (i - 6)

def stree11LLLLLLRRL (i : Nat) : State := match i with | 0 => state11_36 | 1 => state11_37 | 2 => state11_38 | 3 => state11_39 | 4 => state11_40 | _ => state11_41

def stree11LLLLLLRRR (i : Nat) : State := match i with | 0 => state11_42 | 1 => state11_43 | 2 => state11_44 | 3 => state11_45 | 4 => state11_46 | _ => state11_47

def stree11LLLLLLRR (i : Nat) : State := if i < 6 then stree11LLLLLLRRL i else stree11LLLLLLRRR (i - 6)

def stree11LLLLLLR (i : Nat) : State := if i < 12 then stree11LLLLLLRL i else stree11LLLLLLRR (i - 12)

def stree11LLLLLL (i : Nat) : State := if i < 24 then stree11LLLLLLL i else stree11LLLLLLR (i - 24)

def stree11LLLLLRLLL (i : Nat) : State := match i with | 0 => state11_48 | 1 => state11_49 | 2 => state11_50 | 3 => state11_51 | 4 => state11_52 | _ => state11_53

def stree11LLLLLRLLR (i : Nat) : State := match i with | 0 => state11_54 | 1 => state11_55 | 2 => state11_56 | 3 => state11_57 | 4 => state11_58 | _ => state11_59

def stree11LLLLLRLL (i : Nat) : State := if i < 6 then stree11LLLLLRLLL i else stree11LLLLLRLLR (i - 6)

def stree11LLLLLRLRL (i : Nat) : State := match i with | 0 => state11_60 | 1 => state11_61 | 2 => state11_62 | 3 => state11_63 | 4 => state11_64 | _ => state11_65

def stree11LLLLLRLRR (i : Nat) : State := match i with | 0 => state11_66 | 1 => state11_67 | 2 => state11_68 | 3 => state11_69 | 4 => state11_70 | _ => state11_71

def stree11LLLLLRLR (i : Nat) : State := if i < 6 then stree11LLLLLRLRL i else stree11LLLLLRLRR (i - 6)

def stree11LLLLLRL (i : Nat) : State := if i < 12 then stree11LLLLLRLL i else stree11LLLLLRLR (i - 12)

def stree11LLLLLRRLL (i : Nat) : State := match i with | 0 => state11_72 | 1 => state11_73 | 2 => state11_74 | 3 => state11_75 | 4 => state11_76 | _ => state11_77

def stree11LLLLLRRLR (i : Nat) : State := match i with | 0 => state11_78 | 1 => state11_79 | 2 => state11_80 | 3 => state11_81 | 4 => state11_82 | _ => state11_83

def stree11LLLLLRRL (i : Nat) : State := if i < 6 then stree11LLLLLRRLL i else stree11LLLLLRRLR (i - 6)

def stree11LLLLLRRRL (i : Nat) : State := match i with | 0 => state11_84 | 1 => state11_85 | 2 => state11_86 | 3 => state11_87 | 4 => state11_88 | _ => state11_89

def stree11LLLLLRRRR (i : Nat) : State := match i with | 0 => state11_90 | 1 => state11_91 | 2 => state11_92 | 3 => state11_93 | 4 => state11_94 | 5 => state11_95 | _ => state11_96

def stree11LLLLLRRR (i : Nat) : State := if i < 6 then stree11LLLLLRRRL i else stree11LLLLLRRRR (i - 6)

def stree11LLLLLRR (i : Nat) : State := if i < 12 then stree11LLLLLRRL i else stree11LLLLLRRR (i - 12)

def stree11LLLLLR (i : Nat) : State := if i < 24 then stree11LLLLLRL i else stree11LLLLLRR (i - 24)

def stree11LLLLL (i : Nat) : State := if i < 48 then stree11LLLLLL i else stree11LLLLLR (i - 48)

def stree11LLLLRLLLL (i : Nat) : State := match i with | 0 => state11_97 | 1 => state11_98 | 2 => state11_99 | 3 => state11_100 | 4 => state11_101 | _ => state11_102

def stree11LLLLRLLLR (i : Nat) : State := match i with | 0 => state11_103 | 1 => state11_104 | 2 => state11_105 | 3 => state11_106 | 4 => state11_107 | _ => state11_108

def stree11LLLLRLLL (i : Nat) : State := if i < 6 then stree11LLLLRLLLL i else stree11LLLLRLLLR (i - 6)

def stree11LLLLRLLRL (i : Nat) : State := match i with | 0 => state11_109 | 1 => state11_110 | 2 => state11_111 | 3 => state11_112 | 4 => state11_113 | _ => state11_114

def stree11LLLLRLLRR (i : Nat) : State := match i with | 0 => state11_115 | 1 => state11_116 | 2 => state11_117 | 3 => state11_118 | 4 => state11_119 | _ => state11_120

def stree11LLLLRLLR (i : Nat) : State := if i < 6 then stree11LLLLRLLRL i else stree11LLLLRLLRR (i - 6)

def stree11LLLLRLL (i : Nat) : State := if i < 12 then stree11LLLLRLLL i else stree11LLLLRLLR (i - 12)

def stree11LLLLRLRLL (i : Nat) : State := match i with | 0 => state11_121 | 1 => state11_122 | 2 => state11_123 | 3 => state11_124 | 4 => state11_125 | _ => state11_126

def stree11LLLLRLRLR (i : Nat) : State := match i with | 0 => state11_127 | 1 => state11_128 | 2 => state11_129 | 3 => state11_130 | 4 => state11_131 | _ => state11_132

def stree11LLLLRLRL (i : Nat) : State := if i < 6 then stree11LLLLRLRLL i else stree11LLLLRLRLR (i - 6)

def stree11LLLLRLRRL (i : Nat) : State := match i with | 0 => state11_133 | 1 => state11_134 | 2 => state11_135 | 3 => state11_136 | 4 => state11_137 | _ => state11_138

def stree11LLLLRLRRR (i : Nat) : State := match i with | 0 => state11_139 | 1 => state11_140 | 2 => state11_141 | 3 => state11_142 | 4 => state11_143 | _ => state11_144

def stree11LLLLRLRR (i : Nat) : State := if i < 6 then stree11LLLLRLRRL i else stree11LLLLRLRRR (i - 6)

def stree11LLLLRLR (i : Nat) : State := if i < 12 then stree11LLLLRLRL i else stree11LLLLRLRR (i - 12)

def stree11LLLLRL (i : Nat) : State := if i < 24 then stree11LLLLRLL i else stree11LLLLRLR (i - 24)

def stree11LLLLRRLLL (i : Nat) : State := match i with | 0 => state11_145 | 1 => state11_146 | 2 => state11_147 | 3 => state11_148 | 4 => state11_149 | _ => state11_150

def stree11LLLLRRLLR (i : Nat) : State := match i with | 0 => state11_151 | 1 => state11_152 | 2 => state11_153 | 3 => state11_154 | 4 => state11_155 | _ => state11_156

def stree11LLLLRRLL (i : Nat) : State := if i < 6 then stree11LLLLRRLLL i else stree11LLLLRRLLR (i - 6)

def stree11LLLLRRLRL (i : Nat) : State := match i with | 0 => state11_157 | 1 => state11_158 | 2 => state11_159 | 3 => state11_160 | 4 => state11_161 | _ => state11_162

def stree11LLLLRRLRR (i : Nat) : State := match i with | 0 => state11_163 | 1 => state11_164 | 2 => state11_165 | 3 => state11_166 | 4 => state11_167 | _ => state11_168

def stree11LLLLRRLR (i : Nat) : State := if i < 6 then stree11LLLLRRLRL i else stree11LLLLRRLRR (i - 6)

def stree11LLLLRRL (i : Nat) : State := if i < 12 then stree11LLLLRRLL i else stree11LLLLRRLR (i - 12)

def stree11LLLLRRRLL (i : Nat) : State := match i with | 0 => state11_169 | 1 => state11_170 | 2 => state11_171 | 3 => state11_172 | 4 => state11_173 | _ => state11_174

def stree11LLLLRRRLR (i : Nat) : State := match i with | 0 => state11_175 | 1 => state11_176 | 2 => state11_177 | 3 => state11_178 | 4 => state11_179 | _ => state11_180

def stree11LLLLRRRL (i : Nat) : State := if i < 6 then stree11LLLLRRRLL i else stree11LLLLRRRLR (i - 6)

def stree11LLLLRRRRL (i : Nat) : State := match i with | 0 => state11_181 | 1 => state11_182 | 2 => state11_183 | 3 => state11_184 | 4 => state11_185 | _ => state11_186

def stree11LLLLRRRRR (i : Nat) : State := match i with | 0 => state11_187 | 1 => state11_188 | 2 => state11_189 | 3 => state11_190 | 4 => state11_191 | 5 => state11_192 | _ => state11_193

def stree11LLLLRRRR (i : Nat) : State := if i < 6 then stree11LLLLRRRRL i else stree11LLLLRRRRR (i - 6)

def stree11LLLLRRR (i : Nat) : State := if i < 12 then stree11LLLLRRRL i else stree11LLLLRRRR (i - 12)

def stree11LLLLRR (i : Nat) : State := if i < 24 then stree11LLLLRRL i else stree11LLLLRRR (i - 24)

def stree11LLLLR (i : Nat) : State := if i < 48 then stree11LLLLRL i else stree11LLLLRR (i - 48)

def stree11LLLL (i : Nat) : State := if i < 97 then stree11LLLLL i else stree11LLLLR (i - 97)

def stree11LLLRLLLLL (i : Nat) : State := match i with | 0 => state11_194 | 1 => state11_195 | 2 => state11_196 | 3 => state11_197 | 4 => state11_198 | _ => state11_199

def stree11LLLRLLLLR (i : Nat) : State := match i with | 0 => state11_200 | 1 => state11_201 | 2 => state11_202 | 3 => state11_203 | 4 => state11_204 | _ => state11_205

def stree11LLLRLLLL (i : Nat) : State := if i < 6 then stree11LLLRLLLLL i else stree11LLLRLLLLR (i - 6)

def stree11LLLRLLLRL (i : Nat) : State := match i with | 0 => state11_206 | 1 => state11_207 | 2 => state11_208 | 3 => state11_209 | 4 => state11_210 | _ => state11_211

def stree11LLLRLLLRR (i : Nat) : State := match i with | 0 => state11_212 | 1 => state11_213 | 2 => state11_214 | 3 => state11_215 | 4 => state11_216 | _ => state11_217

def stree11LLLRLLLR (i : Nat) : State := if i < 6 then stree11LLLRLLLRL i else stree11LLLRLLLRR (i - 6)

def stree11LLLRLLL (i : Nat) : State := if i < 12 then stree11LLLRLLLL i else stree11LLLRLLLR (i - 12)

def stree11LLLRLLRLL (i : Nat) : State := match i with | 0 => state11_218 | 1 => state11_219 | 2 => state11_220 | 3 => state11_221 | 4 => state11_222 | _ => state11_223

def stree11LLLRLLRLR (i : Nat) : State := match i with | 0 => state11_224 | 1 => state11_225 | 2 => state11_226 | 3 => state11_227 | 4 => state11_228 | _ => state11_229

def stree11LLLRLLRL (i : Nat) : State := if i < 6 then stree11LLLRLLRLL i else stree11LLLRLLRLR (i - 6)

def stree11LLLRLLRRL (i : Nat) : State := match i with | 0 => state11_230 | 1 => state11_231 | 2 => state11_232 | 3 => state11_233 | 4 => state11_234 | _ => state11_235

def stree11LLLRLLRRR (i : Nat) : State := match i with | 0 => state11_236 | 1 => state11_237 | 2 => state11_238 | 3 => state11_239 | 4 => state11_240 | _ => state11_241

def stree11LLLRLLRR (i : Nat) : State := if i < 6 then stree11LLLRLLRRL i else stree11LLLRLLRRR (i - 6)

def stree11LLLRLLR (i : Nat) : State := if i < 12 then stree11LLLRLLRL i else stree11LLLRLLRR (i - 12)

def stree11LLLRLL (i : Nat) : State := if i < 24 then stree11LLLRLLL i else stree11LLLRLLR (i - 24)

def stree11LLLRLRLLL (i : Nat) : State := match i with | 0 => state11_242 | 1 => state11_243 | 2 => state11_244 | 3 => state11_245 | 4 => state11_246 | _ => state11_247

def stree11LLLRLRLLR (i : Nat) : State := match i with | 0 => state11_248 | 1 => state11_249 | 2 => state11_250 | 3 => state11_251 | 4 => state11_252 | _ => state11_253

def stree11LLLRLRLL (i : Nat) : State := if i < 6 then stree11LLLRLRLLL i else stree11LLLRLRLLR (i - 6)

def stree11LLLRLRLRL (i : Nat) : State := match i with | 0 => state11_254 | 1 => state11_255 | 2 => state11_256 | 3 => state11_257 | 4 => state11_258 | _ => state11_259

def stree11LLLRLRLRR (i : Nat) : State := match i with | 0 => state11_260 | 1 => state11_261 | 2 => state11_262 | 3 => state11_263 | 4 => state11_264 | _ => state11_265

def stree11LLLRLRLR (i : Nat) : State := if i < 6 then stree11LLLRLRLRL i else stree11LLLRLRLRR (i - 6)

def stree11LLLRLRL (i : Nat) : State := if i < 12 then stree11LLLRLRLL i else stree11LLLRLRLR (i - 12)

def stree11LLLRLRRLL (i : Nat) : State := match i with | 0 => state11_266 | 1 => state11_267 | 2 => state11_268 | 3 => state11_269 | 4 => state11_270 | _ => state11_271

def stree11LLLRLRRLR (i : Nat) : State := match i with | 0 => state11_272 | 1 => state11_273 | 2 => state11_274 | 3 => state11_275 | 4 => state11_276 | _ => state11_277

def stree11LLLRLRRL (i : Nat) : State := if i < 6 then stree11LLLRLRRLL i else stree11LLLRLRRLR (i - 6)

def stree11LLLRLRRRL (i : Nat) : State := match i with | 0 => state11_278 | 1 => state11_279 | 2 => state11_280 | 3 => state11_281 | 4 => state11_282 | _ => state11_283

def stree11LLLRLRRRR (i : Nat) : State := match i with | 0 => state11_284 | 1 => state11_285 | 2 => state11_286 | 3 => state11_287 | 4 => state11_288 | 5 => state11_289 | _ => state11_290

def stree11LLLRLRRR (i : Nat) : State := if i < 6 then stree11LLLRLRRRL i else stree11LLLRLRRRR (i - 6)

def stree11LLLRLRR (i : Nat) : State := if i < 12 then stree11LLLRLRRL i else stree11LLLRLRRR (i - 12)

def stree11LLLRLR (i : Nat) : State := if i < 24 then stree11LLLRLRL i else stree11LLLRLRR (i - 24)

def stree11LLLRL (i : Nat) : State := if i < 48 then stree11LLLRLL i else stree11LLLRLR (i - 48)

def stree11LLLRRLLLL (i : Nat) : State := match i with | 0 => state11_291 | 1 => state11_292 | 2 => state11_293 | 3 => state11_294 | 4 => state11_295 | _ => state11_296

def stree11LLLRRLLLR (i : Nat) : State := match i with | 0 => state11_297 | 1 => state11_298 | 2 => state11_299 | 3 => state11_300 | 4 => state11_301 | _ => state11_302

def stree11LLLRRLLL (i : Nat) : State := if i < 6 then stree11LLLRRLLLL i else stree11LLLRRLLLR (i - 6)

def stree11LLLRRLLRL (i : Nat) : State := match i with | 0 => state11_303 | 1 => state11_304 | 2 => state11_305 | 3 => state11_306 | 4 => state11_307 | _ => state11_308

def stree11LLLRRLLRR (i : Nat) : State := match i with | 0 => state11_309 | 1 => state11_310 | 2 => state11_311 | 3 => state11_312 | 4 => state11_313 | _ => state11_314

def stree11LLLRRLLR (i : Nat) : State := if i < 6 then stree11LLLRRLLRL i else stree11LLLRRLLRR (i - 6)

def stree11LLLRRLL (i : Nat) : State := if i < 12 then stree11LLLRRLLL i else stree11LLLRRLLR (i - 12)

def stree11LLLRRLRLL (i : Nat) : State := match i with | 0 => state11_315 | 1 => state11_316 | 2 => state11_317 | 3 => state11_318 | 4 => state11_319 | _ => state11_320

def stree11LLLRRLRLR (i : Nat) : State := match i with | 0 => state11_321 | 1 => state11_322 | 2 => state11_323 | 3 => state11_324 | 4 => state11_325 | _ => state11_326

def stree11LLLRRLRL (i : Nat) : State := if i < 6 then stree11LLLRRLRLL i else stree11LLLRRLRLR (i - 6)

def stree11LLLRRLRRL (i : Nat) : State := match i with | 0 => state11_327 | 1 => state11_328 | 2 => state11_329 | 3 => state11_330 | 4 => state11_331 | _ => state11_332

def stree11LLLRRLRRR (i : Nat) : State := match i with | 0 => state11_333 | 1 => state11_334 | 2 => state11_335 | 3 => state11_336 | 4 => state11_337 | _ => state11_338

def stree11LLLRRLRR (i : Nat) : State := if i < 6 then stree11LLLRRLRRL i else stree11LLLRRLRRR (i - 6)

def stree11LLLRRLR (i : Nat) : State := if i < 12 then stree11LLLRRLRL i else stree11LLLRRLRR (i - 12)

def stree11LLLRRL (i : Nat) : State := if i < 24 then stree11LLLRRLL i else stree11LLLRRLR (i - 24)

def stree11LLLRRRLLL (i : Nat) : State := match i with | 0 => state11_339 | 1 => state11_340 | 2 => state11_341 | 3 => state11_342 | 4 => state11_343 | _ => state11_344

def stree11LLLRRRLLR (i : Nat) : State := match i with | 0 => state11_345 | 1 => state11_346 | 2 => state11_347 | 3 => state11_348 | 4 => state11_349 | _ => state11_350

def stree11LLLRRRLL (i : Nat) : State := if i < 6 then stree11LLLRRRLLL i else stree11LLLRRRLLR (i - 6)

def stree11LLLRRRLRL (i : Nat) : State := match i with | 0 => state11_351 | 1 => state11_352 | 2 => state11_353 | 3 => state11_354 | 4 => state11_355 | _ => state11_356

def stree11LLLRRRLRR (i : Nat) : State := match i with | 0 => state11_357 | 1 => state11_358 | 2 => state11_359 | 3 => state11_360 | 4 => state11_361 | _ => state11_362

def stree11LLLRRRLR (i : Nat) : State := if i < 6 then stree11LLLRRRLRL i else stree11LLLRRRLRR (i - 6)

def stree11LLLRRRL (i : Nat) : State := if i < 12 then stree11LLLRRRLL i else stree11LLLRRRLR (i - 12)

def stree11LLLRRRRLL (i : Nat) : State := match i with | 0 => state11_363 | 1 => state11_364 | 2 => state11_365 | 3 => state11_366 | 4 => state11_367 | _ => state11_368

def stree11LLLRRRRLR (i : Nat) : State := match i with | 0 => state11_369 | 1 => state11_370 | 2 => state11_371 | 3 => state11_372 | 4 => state11_373 | _ => state11_374

def stree11LLLRRRRL (i : Nat) : State := if i < 6 then stree11LLLRRRRLL i else stree11LLLRRRRLR (i - 6)

def stree11LLLRRRRRL (i : Nat) : State := match i with | 0 => state11_375 | 1 => state11_376 | 2 => state11_377 | 3 => state11_378 | 4 => state11_379 | _ => state11_380

def stree11LLLRRRRRR (i : Nat) : State := match i with | 0 => state11_381 | 1 => state11_382 | 2 => state11_383 | 3 => state11_384 | 4 => state11_385 | 5 => state11_386 | _ => state11_387

def stree11LLLRRRRR (i : Nat) : State := if i < 6 then stree11LLLRRRRRL i else stree11LLLRRRRRR (i - 6)

def stree11LLLRRRR (i : Nat) : State := if i < 12 then stree11LLLRRRRL i else stree11LLLRRRRR (i - 12)

def stree11LLLRRR (i : Nat) : State := if i < 24 then stree11LLLRRRL i else stree11LLLRRRR (i - 24)

def stree11LLLRR (i : Nat) : State := if i < 48 then stree11LLLRRL i else stree11LLLRRR (i - 48)

def stree11LLLR (i : Nat) : State := if i < 97 then stree11LLLRL i else stree11LLLRR (i - 97)

def stree11LLL (i : Nat) : State := if i < 194 then stree11LLLL i else stree11LLLR (i - 194)

def stree11LLRLLLLLL (i : Nat) : State := match i with | 0 => state11_388 | 1 => state11_389 | 2 => state11_390 | 3 => state11_391 | 4 => state11_392 | _ => state11_393

def stree11LLRLLLLLR (i : Nat) : State := match i with | 0 => state11_394 | 1 => state11_395 | 2 => state11_396 | 3 => state11_397 | 4 => state11_398 | _ => state11_399

def stree11LLRLLLLL (i : Nat) : State := if i < 6 then stree11LLRLLLLLL i else stree11LLRLLLLLR (i - 6)

def stree11LLRLLLLRL (i : Nat) : State := match i with | 0 => state11_400 | 1 => state11_401 | 2 => state11_402 | 3 => state11_403 | 4 => state11_404 | _ => state11_405

def stree11LLRLLLLRR (i : Nat) : State := match i with | 0 => state11_406 | 1 => state11_407 | 2 => state11_408 | 3 => state11_409 | 4 => state11_410 | _ => state11_411

def stree11LLRLLLLR (i : Nat) : State := if i < 6 then stree11LLRLLLLRL i else stree11LLRLLLLRR (i - 6)

def stree11LLRLLLL (i : Nat) : State := if i < 12 then stree11LLRLLLLL i else stree11LLRLLLLR (i - 12)

def stree11LLRLLLRLL (i : Nat) : State := match i with | 0 => state11_412 | 1 => state11_413 | 2 => state11_414 | 3 => state11_415 | 4 => state11_416 | _ => state11_417

def stree11LLRLLLRLR (i : Nat) : State := match i with | 0 => state11_418 | 1 => state11_419 | 2 => state11_420 | 3 => state11_421 | 4 => state11_422 | _ => state11_423

def stree11LLRLLLRL (i : Nat) : State := if i < 6 then stree11LLRLLLRLL i else stree11LLRLLLRLR (i - 6)

def stree11LLRLLLRRL (i : Nat) : State := match i with | 0 => state11_424 | 1 => state11_425 | 2 => state11_426 | 3 => state11_427 | 4 => state11_428 | _ => state11_429

def stree11LLRLLLRRR (i : Nat) : State := match i with | 0 => state11_430 | 1 => state11_431 | 2 => state11_432 | 3 => state11_433 | 4 => state11_434 | _ => state11_435

def stree11LLRLLLRR (i : Nat) : State := if i < 6 then stree11LLRLLLRRL i else stree11LLRLLLRRR (i - 6)

def stree11LLRLLLR (i : Nat) : State := if i < 12 then stree11LLRLLLRL i else stree11LLRLLLRR (i - 12)

def stree11LLRLLL (i : Nat) : State := if i < 24 then stree11LLRLLLL i else stree11LLRLLLR (i - 24)

def stree11LLRLLRLLL (i : Nat) : State := match i with | 0 => state11_436 | 1 => state11_437 | 2 => state11_438 | 3 => state11_439 | 4 => state11_440 | _ => state11_441

def stree11LLRLLRLLR (i : Nat) : State := match i with | 0 => state11_442 | 1 => state11_443 | 2 => state11_444 | 3 => state11_445 | 4 => state11_446 | _ => state11_447

def stree11LLRLLRLL (i : Nat) : State := if i < 6 then stree11LLRLLRLLL i else stree11LLRLLRLLR (i - 6)

def stree11LLRLLRLRL (i : Nat) : State := match i with | 0 => state11_448 | 1 => state11_449 | 2 => state11_450 | 3 => state11_451 | 4 => state11_452 | _ => state11_453

def stree11LLRLLRLRR (i : Nat) : State := match i with | 0 => state11_454 | 1 => state11_455 | 2 => state11_456 | 3 => state11_457 | 4 => state11_458 | _ => state11_459

def stree11LLRLLRLR (i : Nat) : State := if i < 6 then stree11LLRLLRLRL i else stree11LLRLLRLRR (i - 6)

def stree11LLRLLRL (i : Nat) : State := if i < 12 then stree11LLRLLRLL i else stree11LLRLLRLR (i - 12)

def stree11LLRLLRRLL (i : Nat) : State := match i with | 0 => state11_460 | 1 => state11_461 | 2 => state11_462 | 3 => state11_463 | 4 => state11_464 | _ => state11_465

def stree11LLRLLRRLR (i : Nat) : State := match i with | 0 => state11_466 | 1 => state11_467 | 2 => state11_468 | 3 => state11_469 | 4 => state11_470 | _ => state11_471

def stree11LLRLLRRL (i : Nat) : State := if i < 6 then stree11LLRLLRRLL i else stree11LLRLLRRLR (i - 6)

def stree11LLRLLRRRL (i : Nat) : State := match i with | 0 => state11_472 | 1 => state11_473 | 2 => state11_474 | 3 => state11_475 | 4 => state11_476 | _ => state11_477

def stree11LLRLLRRRR (i : Nat) : State := match i with | 0 => state11_478 | 1 => state11_479 | 2 => state11_480 | 3 => state11_481 | 4 => state11_482 | 5 => state11_483 | _ => state11_484

def stree11LLRLLRRR (i : Nat) : State := if i < 6 then stree11LLRLLRRRL i else stree11LLRLLRRRR (i - 6)

def stree11LLRLLRR (i : Nat) : State := if i < 12 then stree11LLRLLRRL i else stree11LLRLLRRR (i - 12)

def stree11LLRLLR (i : Nat) : State := if i < 24 then stree11LLRLLRL i else stree11LLRLLRR (i - 24)

def stree11LLRLL (i : Nat) : State := if i < 48 then stree11LLRLLL i else stree11LLRLLR (i - 48)

def stree11LLRLRLLLL (i : Nat) : State := match i with | 0 => state11_485 | 1 => state11_486 | 2 => state11_487 | 3 => state11_488 | 4 => state11_489 | _ => state11_490

def stree11LLRLRLLLR (i : Nat) : State := match i with | 0 => state11_491 | 1 => state11_492 | 2 => state11_493 | 3 => state11_494 | 4 => state11_495 | _ => state11_496

def stree11LLRLRLLL (i : Nat) : State := if i < 6 then stree11LLRLRLLLL i else stree11LLRLRLLLR (i - 6)

def stree11LLRLRLLRL (i : Nat) : State := match i with | 0 => state11_497 | 1 => state11_498 | 2 => state11_499 | 3 => state11_500 | 4 => state11_501 | _ => state11_502

def stree11LLRLRLLRR (i : Nat) : State := match i with | 0 => state11_503 | 1 => state11_504 | 2 => state11_505 | 3 => state11_506 | 4 => state11_507 | _ => state11_508

def stree11LLRLRLLR (i : Nat) : State := if i < 6 then stree11LLRLRLLRL i else stree11LLRLRLLRR (i - 6)

def stree11LLRLRLL (i : Nat) : State := if i < 12 then stree11LLRLRLLL i else stree11LLRLRLLR (i - 12)

def stree11LLRLRLRLL (i : Nat) : State := match i with | 0 => state11_509 | 1 => state11_510 | 2 => state11_511 | 3 => state11_512 | 4 => state11_513 | _ => state11_514

def stree11LLRLRLRLR (i : Nat) : State := match i with | 0 => state11_515 | 1 => state11_516 | 2 => state11_517 | 3 => state11_518 | 4 => state11_519 | _ => state11_520

def stree11LLRLRLRL (i : Nat) : State := if i < 6 then stree11LLRLRLRLL i else stree11LLRLRLRLR (i - 6)

def stree11LLRLRLRRL (i : Nat) : State := match i with | 0 => state11_521 | 1 => state11_522 | 2 => state11_523 | 3 => state11_524 | 4 => state11_525 | _ => state11_526

def stree11LLRLRLRRR (i : Nat) : State := match i with | 0 => state11_527 | 1 => state11_528 | 2 => state11_529 | 3 => state11_530 | 4 => state11_531 | _ => state11_532

def stree11LLRLRLRR (i : Nat) : State := if i < 6 then stree11LLRLRLRRL i else stree11LLRLRLRRR (i - 6)

def stree11LLRLRLR (i : Nat) : State := if i < 12 then stree11LLRLRLRL i else stree11LLRLRLRR (i - 12)

def stree11LLRLRL (i : Nat) : State := if i < 24 then stree11LLRLRLL i else stree11LLRLRLR (i - 24)

def stree11LLRLRRLLL (i : Nat) : State := match i with | 0 => state11_533 | 1 => state11_534 | 2 => state11_535 | 3 => state11_536 | 4 => state11_537 | _ => state11_538

def stree11LLRLRRLLR (i : Nat) : State := match i with | 0 => state11_539 | 1 => state11_540 | 2 => state11_541 | 3 => state11_542 | 4 => state11_543 | _ => state11_544

def stree11LLRLRRLL (i : Nat) : State := if i < 6 then stree11LLRLRRLLL i else stree11LLRLRRLLR (i - 6)

def stree11LLRLRRLRL (i : Nat) : State := match i with | 0 => state11_545 | 1 => state11_546 | 2 => state11_547 | 3 => state11_548 | 4 => state11_549 | _ => state11_550

def stree11LLRLRRLRR (i : Nat) : State := match i with | 0 => state11_551 | 1 => state11_552 | 2 => state11_553 | 3 => state11_554 | 4 => state11_555 | _ => state11_556

def stree11LLRLRRLR (i : Nat) : State := if i < 6 then stree11LLRLRRLRL i else stree11LLRLRRLRR (i - 6)

def stree11LLRLRRL (i : Nat) : State := if i < 12 then stree11LLRLRRLL i else stree11LLRLRRLR (i - 12)

def stree11LLRLRRRLL (i : Nat) : State := match i with | 0 => state11_557 | 1 => state11_558 | 2 => state11_559 | 3 => state11_560 | 4 => state11_561 | _ => state11_562

def stree11LLRLRRRLR (i : Nat) : State := match i with | 0 => state11_563 | 1 => state11_564 | 2 => state11_565 | 3 => state11_566 | 4 => state11_567 | _ => state11_568

def stree11LLRLRRRL (i : Nat) : State := if i < 6 then stree11LLRLRRRLL i else stree11LLRLRRRLR (i - 6)

def stree11LLRLRRRRL (i : Nat) : State := match i with | 0 => state11_569 | 1 => state11_570 | 2 => state11_571 | 3 => state11_572 | 4 => state11_573 | _ => state11_574

def stree11LLRLRRRRR (i : Nat) : State := match i with | 0 => state11_575 | 1 => state11_576 | 2 => state11_577 | 3 => state11_578 | 4 => state11_579 | 5 => state11_580 | _ => state11_581

def stree11LLRLRRRR (i : Nat) : State := if i < 6 then stree11LLRLRRRRL i else stree11LLRLRRRRR (i - 6)

def stree11LLRLRRR (i : Nat) : State := if i < 12 then stree11LLRLRRRL i else stree11LLRLRRRR (i - 12)

def stree11LLRLRR (i : Nat) : State := if i < 24 then stree11LLRLRRL i else stree11LLRLRRR (i - 24)

def stree11LLRLR (i : Nat) : State := if i < 48 then stree11LLRLRL i else stree11LLRLRR (i - 48)

def stree11LLRL (i : Nat) : State := if i < 97 then stree11LLRLL i else stree11LLRLR (i - 97)

def stree11LLRRLLLLL (i : Nat) : State := match i with | 0 => state11_582 | 1 => state11_583 | 2 => state11_584 | 3 => state11_585 | 4 => state11_586 | _ => state11_587

def stree11LLRRLLLLR (i : Nat) : State := match i with | 0 => state11_588 | 1 => state11_589 | 2 => state11_590 | 3 => state11_591 | 4 => state11_592 | _ => state11_593

def stree11LLRRLLLL (i : Nat) : State := if i < 6 then stree11LLRRLLLLL i else stree11LLRRLLLLR (i - 6)

def stree11LLRRLLLRL (i : Nat) : State := match i with | 0 => state11_594 | 1 => state11_595 | 2 => state11_596 | 3 => state11_597 | 4 => state11_598 | _ => state11_599

def stree11LLRRLLLRR (i : Nat) : State := match i with | 0 => state11_600 | 1 => state11_601 | 2 => state11_602 | 3 => state11_603 | 4 => state11_604 | _ => state11_605

def stree11LLRRLLLR (i : Nat) : State := if i < 6 then stree11LLRRLLLRL i else stree11LLRRLLLRR (i - 6)

def stree11LLRRLLL (i : Nat) : State := if i < 12 then stree11LLRRLLLL i else stree11LLRRLLLR (i - 12)

def stree11LLRRLLRLL (i : Nat) : State := match i with | 0 => state11_606 | 1 => state11_607 | 2 => state11_608 | 3 => state11_609 | 4 => state11_610 | _ => state11_611

def stree11LLRRLLRLR (i : Nat) : State := match i with | 0 => state11_612 | 1 => state11_613 | 2 => state11_614 | 3 => state11_615 | 4 => state11_616 | _ => state11_617

def stree11LLRRLLRL (i : Nat) : State := if i < 6 then stree11LLRRLLRLL i else stree11LLRRLLRLR (i - 6)

def stree11LLRRLLRRL (i : Nat) : State := match i with | 0 => state11_618 | 1 => state11_619 | 2 => state11_620 | 3 => state11_621 | 4 => state11_622 | _ => state11_623

def stree11LLRRLLRRR (i : Nat) : State := match i with | 0 => state11_624 | 1 => state11_625 | 2 => state11_626 | 3 => state11_627 | 4 => state11_628 | _ => state11_629

def stree11LLRRLLRR (i : Nat) : State := if i < 6 then stree11LLRRLLRRL i else stree11LLRRLLRRR (i - 6)

def stree11LLRRLLR (i : Nat) : State := if i < 12 then stree11LLRRLLRL i else stree11LLRRLLRR (i - 12)

def stree11LLRRLL (i : Nat) : State := if i < 24 then stree11LLRRLLL i else stree11LLRRLLR (i - 24)

def stree11LLRRLRLLL (i : Nat) : State := match i with | 0 => state11_630 | 1 => state11_631 | 2 => state11_632 | 3 => state11_633 | 4 => state11_634 | _ => state11_635

def stree11LLRRLRLLR (i : Nat) : State := match i with | 0 => state11_636 | 1 => state11_637 | 2 => state11_638 | 3 => state11_639 | 4 => state11_640 | _ => state11_641

def stree11LLRRLRLL (i : Nat) : State := if i < 6 then stree11LLRRLRLLL i else stree11LLRRLRLLR (i - 6)

def stree11LLRRLRLRL (i : Nat) : State := match i with | 0 => state11_642 | 1 => state11_643 | 2 => state11_644 | 3 => state11_645 | 4 => state11_646 | _ => state11_647

def stree11LLRRLRLRR (i : Nat) : State := match i with | 0 => state11_648 | 1 => state11_649 | 2 => state11_650 | 3 => state11_651 | 4 => state11_652 | _ => state11_653

def stree11LLRRLRLR (i : Nat) : State := if i < 6 then stree11LLRRLRLRL i else stree11LLRRLRLRR (i - 6)

def stree11LLRRLRL (i : Nat) : State := if i < 12 then stree11LLRRLRLL i else stree11LLRRLRLR (i - 12)

def stree11LLRRLRRLL (i : Nat) : State := match i with | 0 => state11_654 | 1 => state11_655 | 2 => state11_656 | 3 => state11_657 | 4 => state11_658 | _ => state11_659

def stree11LLRRLRRLR (i : Nat) : State := match i with | 0 => state11_660 | 1 => state11_661 | 2 => state11_662 | 3 => state11_663 | 4 => state11_664 | _ => state11_665

def stree11LLRRLRRL (i : Nat) : State := if i < 6 then stree11LLRRLRRLL i else stree11LLRRLRRLR (i - 6)

def stree11LLRRLRRRL (i : Nat) : State := match i with | 0 => state11_666 | 1 => state11_667 | 2 => state11_668 | 3 => state11_669 | 4 => state11_670 | _ => state11_671

def stree11LLRRLRRRR (i : Nat) : State := match i with | 0 => state11_672 | 1 => state11_673 | 2 => state11_674 | 3 => state11_675 | 4 => state11_676 | 5 => state11_677 | _ => state11_678

def stree11LLRRLRRR (i : Nat) : State := if i < 6 then stree11LLRRLRRRL i else stree11LLRRLRRRR (i - 6)

def stree11LLRRLRR (i : Nat) : State := if i < 12 then stree11LLRRLRRL i else stree11LLRRLRRR (i - 12)

def stree11LLRRLR (i : Nat) : State := if i < 24 then stree11LLRRLRL i else stree11LLRRLRR (i - 24)

def stree11LLRRL (i : Nat) : State := if i < 48 then stree11LLRRLL i else stree11LLRRLR (i - 48)

def stree11LLRRRLLLL (i : Nat) : State := match i with | 0 => state11_679 | 1 => state11_680 | 2 => state11_681 | 3 => state11_682 | 4 => state11_683 | _ => state11_684

def stree11LLRRRLLLR (i : Nat) : State := match i with | 0 => state11_685 | 1 => state11_686 | 2 => state11_687 | 3 => state11_688 | 4 => state11_689 | _ => state11_690

def stree11LLRRRLLL (i : Nat) : State := if i < 6 then stree11LLRRRLLLL i else stree11LLRRRLLLR (i - 6)

def stree11LLRRRLLRL (i : Nat) : State := match i with | 0 => state11_691 | 1 => state11_692 | 2 => state11_693 | 3 => state11_694 | 4 => state11_695 | _ => state11_696

def stree11LLRRRLLRR (i : Nat) : State := match i with | 0 => state11_697 | 1 => state11_698 | 2 => state11_699 | 3 => state11_700 | 4 => state11_701 | _ => state11_702

def stree11LLRRRLLR (i : Nat) : State := if i < 6 then stree11LLRRRLLRL i else stree11LLRRRLLRR (i - 6)

def stree11LLRRRLL (i : Nat) : State := if i < 12 then stree11LLRRRLLL i else stree11LLRRRLLR (i - 12)

def stree11LLRRRLRLL (i : Nat) : State := match i with | 0 => state11_703 | 1 => state11_704 | 2 => state11_705 | 3 => state11_706 | 4 => state11_707 | _ => state11_708

def stree11LLRRRLRLR (i : Nat) : State := match i with | 0 => state11_709 | 1 => state11_710 | 2 => state11_711 | 3 => state11_712 | 4 => state11_713 | _ => state11_714

def stree11LLRRRLRL (i : Nat) : State := if i < 6 then stree11LLRRRLRLL i else stree11LLRRRLRLR (i - 6)

def stree11LLRRRLRRL (i : Nat) : State := match i with | 0 => state11_715 | 1 => state11_716 | 2 => state11_717 | 3 => state11_718 | 4 => state11_719 | _ => state11_720

def stree11LLRRRLRRR (i : Nat) : State := match i with | 0 => state11_721 | 1 => state11_722 | 2 => state11_723 | 3 => state11_724 | 4 => state11_725 | 5 => state11_726 | _ => state11_727

def stree11LLRRRLRR (i : Nat) : State := if i < 6 then stree11LLRRRLRRL i else stree11LLRRRLRRR (i - 6)

def stree11LLRRRLR (i : Nat) : State := if i < 12 then stree11LLRRRLRL i else stree11LLRRRLRR (i - 12)

def stree11LLRRRL (i : Nat) : State := if i < 24 then stree11LLRRRLL i else stree11LLRRRLR (i - 24)

def stree11LLRRRRLLL (i : Nat) : State := match i with | 0 => state11_728 | 1 => state11_729 | 2 => state11_730 | 3 => state11_731 | 4 => state11_732 | _ => state11_733

def stree11LLRRRRLLR (i : Nat) : State := match i with | 0 => state11_734 | 1 => state11_735 | 2 => state11_736 | 3 => state11_737 | 4 => state11_738 | _ => state11_739

def stree11LLRRRRLL (i : Nat) : State := if i < 6 then stree11LLRRRRLLL i else stree11LLRRRRLLR (i - 6)

def stree11LLRRRRLRL (i : Nat) : State := match i with | 0 => state11_740 | 1 => state11_741 | 2 => state11_742 | 3 => state11_743 | 4 => state11_744 | _ => state11_745

def stree11LLRRRRLRR (i : Nat) : State := match i with | 0 => state11_746 | 1 => state11_747 | 2 => state11_748 | 3 => state11_749 | 4 => state11_750 | _ => state11_751

def stree11LLRRRRLR (i : Nat) : State := if i < 6 then stree11LLRRRRLRL i else stree11LLRRRRLRR (i - 6)

def stree11LLRRRRL (i : Nat) : State := if i < 12 then stree11LLRRRRLL i else stree11LLRRRRLR (i - 12)

def stree11LLRRRRRLL (i : Nat) : State := match i with | 0 => state11_752 | 1 => state11_753 | 2 => state11_754 | 3 => state11_755 | 4 => state11_756 | _ => state11_757

def stree11LLRRRRRLR (i : Nat) : State := match i with | 0 => state11_758 | 1 => state11_759 | 2 => state11_760 | 3 => state11_761 | 4 => state11_762 | _ => state11_763

def stree11LLRRRRRL (i : Nat) : State := if i < 6 then stree11LLRRRRRLL i else stree11LLRRRRRLR (i - 6)

def stree11LLRRRRRRL (i : Nat) : State := match i with | 0 => state11_764 | 1 => state11_765 | 2 => state11_766 | 3 => state11_767 | 4 => state11_768 | _ => state11_769

def stree11LLRRRRRRR (i : Nat) : State := match i with | 0 => state11_770 | 1 => state11_771 | 2 => state11_772 | 3 => state11_773 | 4 => state11_774 | 5 => state11_775 | _ => state11_776

def stree11LLRRRRRR (i : Nat) : State := if i < 6 then stree11LLRRRRRRL i else stree11LLRRRRRRR (i - 6)

def stree11LLRRRRR (i : Nat) : State := if i < 12 then stree11LLRRRRRL i else stree11LLRRRRRR (i - 12)

def stree11LLRRRR (i : Nat) : State := if i < 24 then stree11LLRRRRL i else stree11LLRRRRR (i - 24)

def stree11LLRRR (i : Nat) : State := if i < 49 then stree11LLRRRL i else stree11LLRRRR (i - 49)

def stree11LLRR (i : Nat) : State := if i < 97 then stree11LLRRL i else stree11LLRRR (i - 97)

def stree11LLR (i : Nat) : State := if i < 194 then stree11LLRL i else stree11LLRR (i - 194)

def stree11LL (i : Nat) : State := if i < 388 then stree11LLL i else stree11LLR (i - 388)

def stree11LRLLLLLLL (i : Nat) : State := match i with | 0 => state11_777 | 1 => state11_778 | 2 => state11_779 | 3 => state11_780 | 4 => state11_781 | _ => state11_782

def stree11LRLLLLLLR (i : Nat) : State := match i with | 0 => state11_783 | 1 => state11_784 | 2 => state11_785 | 3 => state11_786 | 4 => state11_787 | _ => state11_788

def stree11LRLLLLLL (i : Nat) : State := if i < 6 then stree11LRLLLLLLL i else stree11LRLLLLLLR (i - 6)

def stree11LRLLLLLRL (i : Nat) : State := match i with | 0 => state11_789 | 1 => state11_790 | 2 => state11_791 | 3 => state11_792 | 4 => state11_793 | _ => state11_794

def stree11LRLLLLLRR (i : Nat) : State := match i with | 0 => state11_795 | 1 => state11_796 | 2 => state11_797 | 3 => state11_798 | 4 => state11_799 | _ => state11_800

def stree11LRLLLLLR (i : Nat) : State := if i < 6 then stree11LRLLLLLRL i else stree11LRLLLLLRR (i - 6)

def stree11LRLLLLL (i : Nat) : State := if i < 12 then stree11LRLLLLLL i else stree11LRLLLLLR (i - 12)

def stree11LRLLLLRLL (i : Nat) : State := match i with | 0 => state11_801 | 1 => state11_802 | 2 => state11_803 | 3 => state11_804 | 4 => state11_805 | _ => state11_806

def stree11LRLLLLRLR (i : Nat) : State := match i with | 0 => state11_807 | 1 => state11_808 | 2 => state11_809 | 3 => state11_810 | 4 => state11_811 | _ => state11_812

def stree11LRLLLLRL (i : Nat) : State := if i < 6 then stree11LRLLLLRLL i else stree11LRLLLLRLR (i - 6)

def stree11LRLLLLRRL (i : Nat) : State := match i with | 0 => state11_813 | 1 => state11_814 | 2 => state11_815 | 3 => state11_816 | 4 => state11_817 | _ => state11_818

def stree11LRLLLLRRR (i : Nat) : State := match i with | 0 => state11_819 | 1 => state11_820 | 2 => state11_821 | 3 => state11_822 | 4 => state11_823 | _ => state11_824

def stree11LRLLLLRR (i : Nat) : State := if i < 6 then stree11LRLLLLRRL i else stree11LRLLLLRRR (i - 6)

def stree11LRLLLLR (i : Nat) : State := if i < 12 then stree11LRLLLLRL i else stree11LRLLLLRR (i - 12)

def stree11LRLLLL (i : Nat) : State := if i < 24 then stree11LRLLLLL i else stree11LRLLLLR (i - 24)

def stree11LRLLLRLLL (i : Nat) : State := match i with | 0 => state11_825 | 1 => state11_826 | 2 => state11_827 | 3 => state11_828 | 4 => state11_829 | _ => state11_830

def stree11LRLLLRLLR (i : Nat) : State := match i with | 0 => state11_831 | 1 => state11_832 | 2 => state11_833 | 3 => state11_834 | 4 => state11_835 | _ => state11_836

def stree11LRLLLRLL (i : Nat) : State := if i < 6 then stree11LRLLLRLLL i else stree11LRLLLRLLR (i - 6)

def stree11LRLLLRLRL (i : Nat) : State := match i with | 0 => state11_837 | 1 => state11_838 | 2 => state11_839 | 3 => state11_840 | 4 => state11_841 | _ => state11_842

def stree11LRLLLRLRR (i : Nat) : State := match i with | 0 => state11_843 | 1 => state11_844 | 2 => state11_845 | 3 => state11_846 | 4 => state11_847 | _ => state11_848

def stree11LRLLLRLR (i : Nat) : State := if i < 6 then stree11LRLLLRLRL i else stree11LRLLLRLRR (i - 6)

def stree11LRLLLRL (i : Nat) : State := if i < 12 then stree11LRLLLRLL i else stree11LRLLLRLR (i - 12)

def stree11LRLLLRRLL (i : Nat) : State := match i with | 0 => state11_849 | 1 => state11_850 | 2 => state11_851 | 3 => state11_852 | 4 => state11_853 | _ => state11_854

def stree11LRLLLRRLR (i : Nat) : State := match i with | 0 => state11_855 | 1 => state11_856 | 2 => state11_857 | 3 => state11_858 | 4 => state11_859 | _ => state11_860

def stree11LRLLLRRL (i : Nat) : State := if i < 6 then stree11LRLLLRRLL i else stree11LRLLLRRLR (i - 6)

def stree11LRLLLRRRL (i : Nat) : State := match i with | 0 => state11_861 | 1 => state11_862 | 2 => state11_863 | 3 => state11_864 | 4 => state11_865 | _ => state11_866

def stree11LRLLLRRRR (i : Nat) : State := match i with | 0 => state11_867 | 1 => state11_868 | 2 => state11_869 | 3 => state11_870 | 4 => state11_871 | 5 => state11_872 | _ => state11_873

def stree11LRLLLRRR (i : Nat) : State := if i < 6 then stree11LRLLLRRRL i else stree11LRLLLRRRR (i - 6)

def stree11LRLLLRR (i : Nat) : State := if i < 12 then stree11LRLLLRRL i else stree11LRLLLRRR (i - 12)

def stree11LRLLLR (i : Nat) : State := if i < 24 then stree11LRLLLRL i else stree11LRLLLRR (i - 24)

def stree11LRLLL (i : Nat) : State := if i < 48 then stree11LRLLLL i else stree11LRLLLR (i - 48)

def stree11LRLLRLLLL (i : Nat) : State := match i with | 0 => state11_874 | 1 => state11_875 | 2 => state11_876 | 3 => state11_877 | 4 => state11_878 | _ => state11_879

def stree11LRLLRLLLR (i : Nat) : State := match i with | 0 => state11_880 | 1 => state11_881 | 2 => state11_882 | 3 => state11_883 | 4 => state11_884 | _ => state11_885

def stree11LRLLRLLL (i : Nat) : State := if i < 6 then stree11LRLLRLLLL i else stree11LRLLRLLLR (i - 6)

def stree11LRLLRLLRL (i : Nat) : State := match i with | 0 => state11_886 | 1 => state11_887 | 2 => state11_888 | 3 => state11_889 | 4 => state11_890 | _ => state11_891

def stree11LRLLRLLRR (i : Nat) : State := match i with | 0 => state11_892 | 1 => state11_893 | 2 => state11_894 | 3 => state11_895 | 4 => state11_896 | _ => state11_897

def stree11LRLLRLLR (i : Nat) : State := if i < 6 then stree11LRLLRLLRL i else stree11LRLLRLLRR (i - 6)

def stree11LRLLRLL (i : Nat) : State := if i < 12 then stree11LRLLRLLL i else stree11LRLLRLLR (i - 12)

def stree11LRLLRLRLL (i : Nat) : State := match i with | 0 => state11_898 | 1 => state11_899 | 2 => state11_900 | 3 => state11_901 | 4 => state11_902 | _ => state11_903

def stree11LRLLRLRLR (i : Nat) : State := match i with | 0 => state11_904 | 1 => state11_905 | 2 => state11_906 | 3 => state11_907 | 4 => state11_908 | _ => state11_909

def stree11LRLLRLRL (i : Nat) : State := if i < 6 then stree11LRLLRLRLL i else stree11LRLLRLRLR (i - 6)

def stree11LRLLRLRRL (i : Nat) : State := match i with | 0 => state11_910 | 1 => state11_911 | 2 => state11_912 | 3 => state11_913 | 4 => state11_914 | _ => state11_915

def stree11LRLLRLRRR (i : Nat) : State := match i with | 0 => state11_916 | 1 => state11_917 | 2 => state11_918 | 3 => state11_919 | 4 => state11_920 | _ => state11_921

def stree11LRLLRLRR (i : Nat) : State := if i < 6 then stree11LRLLRLRRL i else stree11LRLLRLRRR (i - 6)

def stree11LRLLRLR (i : Nat) : State := if i < 12 then stree11LRLLRLRL i else stree11LRLLRLRR (i - 12)

def stree11LRLLRL (i : Nat) : State := if i < 24 then stree11LRLLRLL i else stree11LRLLRLR (i - 24)

def stree11LRLLRRLLL (i : Nat) : State := match i with | 0 => state11_922 | 1 => state11_923 | 2 => state11_924 | 3 => state11_925 | 4 => state11_926 | _ => state11_927

def stree11LRLLRRLLR (i : Nat) : State := match i with | 0 => state11_928 | 1 => state11_929 | 2 => state11_930 | 3 => state11_931 | 4 => state11_932 | _ => state11_933

def stree11LRLLRRLL (i : Nat) : State := if i < 6 then stree11LRLLRRLLL i else stree11LRLLRRLLR (i - 6)

def stree11LRLLRRLRL (i : Nat) : State := match i with | 0 => state11_934 | 1 => state11_935 | 2 => state11_936 | 3 => state11_937 | 4 => state11_938 | _ => state11_939

def stree11LRLLRRLRR (i : Nat) : State := match i with | 0 => state11_940 | 1 => state11_941 | 2 => state11_942 | 3 => state11_943 | 4 => state11_944 | _ => state11_945

def stree11LRLLRRLR (i : Nat) : State := if i < 6 then stree11LRLLRRLRL i else stree11LRLLRRLRR (i - 6)

def stree11LRLLRRL (i : Nat) : State := if i < 12 then stree11LRLLRRLL i else stree11LRLLRRLR (i - 12)

def stree11LRLLRRRLL (i : Nat) : State := match i with | 0 => state11_946 | 1 => state11_947 | 2 => state11_948 | 3 => state11_949 | 4 => state11_950 | _ => state11_951

def stree11LRLLRRRLR (i : Nat) : State := match i with | 0 => state11_952 | 1 => state11_953 | 2 => state11_954 | 3 => state11_955 | 4 => state11_956 | _ => state11_957

def stree11LRLLRRRL (i : Nat) : State := if i < 6 then stree11LRLLRRRLL i else stree11LRLLRRRLR (i - 6)

def stree11LRLLRRRRL (i : Nat) : State := match i with | 0 => state11_958 | 1 => state11_959 | 2 => state11_960 | 3 => state11_961 | 4 => state11_962 | _ => state11_963

def stree11LRLLRRRRR (i : Nat) : State := match i with | 0 => state11_964 | 1 => state11_965 | 2 => state11_966 | 3 => state11_967 | 4 => state11_968 | 5 => state11_969 | _ => state11_970

def stree11LRLLRRRR (i : Nat) : State := if i < 6 then stree11LRLLRRRRL i else stree11LRLLRRRRR (i - 6)

def stree11LRLLRRR (i : Nat) : State := if i < 12 then stree11LRLLRRRL i else stree11LRLLRRRR (i - 12)

def stree11LRLLRR (i : Nat) : State := if i < 24 then stree11LRLLRRL i else stree11LRLLRRR (i - 24)

def stree11LRLLR (i : Nat) : State := if i < 48 then stree11LRLLRL i else stree11LRLLRR (i - 48)

def stree11LRLL (i : Nat) : State := if i < 97 then stree11LRLLL i else stree11LRLLR (i - 97)

def stree11LRLRLLLLL (i : Nat) : State := match i with | 0 => state11_971 | 1 => state11_972 | 2 => state11_973 | 3 => state11_974 | 4 => state11_975 | _ => state11_976

def stree11LRLRLLLLR (i : Nat) : State := match i with | 0 => state11_977 | 1 => state11_978 | 2 => state11_979 | 3 => state11_980 | 4 => state11_981 | _ => state11_982

def stree11LRLRLLLL (i : Nat) : State := if i < 6 then stree11LRLRLLLLL i else stree11LRLRLLLLR (i - 6)

def stree11LRLRLLLRL (i : Nat) : State := match i with | 0 => state11_983 | 1 => state11_984 | 2 => state11_985 | 3 => state11_986 | 4 => state11_987 | _ => state11_988

def stree11LRLRLLLRR (i : Nat) : State := match i with | 0 => state11_989 | 1 => state11_990 | 2 => state11_991 | 3 => state11_992 | 4 => state11_993 | _ => state11_994

def stree11LRLRLLLR (i : Nat) : State := if i < 6 then stree11LRLRLLLRL i else stree11LRLRLLLRR (i - 6)

def stree11LRLRLLL (i : Nat) : State := if i < 12 then stree11LRLRLLLL i else stree11LRLRLLLR (i - 12)

def stree11LRLRLLRLL (i : Nat) : State := match i with | 0 => state11_995 | 1 => state11_996 | 2 => state11_997 | 3 => state11_998 | 4 => state11_999 | _ => state11_1000

def stree11LRLRLLRLR (i : Nat) : State := match i with | 0 => state11_1001 | 1 => state11_1002 | 2 => state11_1003 | 3 => state11_1004 | 4 => state11_1005 | _ => state11_1006

def stree11LRLRLLRL (i : Nat) : State := if i < 6 then stree11LRLRLLRLL i else stree11LRLRLLRLR (i - 6)

def stree11LRLRLLRRL (i : Nat) : State := match i with | 0 => state11_1007 | 1 => state11_1008 | 2 => state11_1009 | 3 => state11_1010 | 4 => state11_1011 | _ => state11_1012

def stree11LRLRLLRRR (i : Nat) : State := match i with | 0 => state11_1013 | 1 => state11_1014 | 2 => state11_1015 | 3 => state11_1016 | 4 => state11_1017 | _ => state11_1018

def stree11LRLRLLRR (i : Nat) : State := if i < 6 then stree11LRLRLLRRL i else stree11LRLRLLRRR (i - 6)

def stree11LRLRLLR (i : Nat) : State := if i < 12 then stree11LRLRLLRL i else stree11LRLRLLRR (i - 12)

def stree11LRLRLL (i : Nat) : State := if i < 24 then stree11LRLRLLL i else stree11LRLRLLR (i - 24)

def stree11LRLRLRLLL (i : Nat) : State := match i with | 0 => state11_1019 | 1 => state11_1020 | 2 => state11_1021 | 3 => state11_1022 | 4 => state11_1023 | _ => state11_1024

def stree11LRLRLRLLR (i : Nat) : State := match i with | 0 => state11_1025 | 1 => state11_1026 | 2 => state11_1027 | 3 => state11_1028 | 4 => state11_1029 | _ => state11_1030

def stree11LRLRLRLL (i : Nat) : State := if i < 6 then stree11LRLRLRLLL i else stree11LRLRLRLLR (i - 6)

def stree11LRLRLRLRL (i : Nat) : State := match i with | 0 => state11_1031 | 1 => state11_1032 | 2 => state11_1033 | 3 => state11_1034 | 4 => state11_1035 | _ => state11_1036

def stree11LRLRLRLRR (i : Nat) : State := match i with | 0 => state11_1037 | 1 => state11_1038 | 2 => state11_1039 | 3 => state11_1040 | 4 => state11_1041 | _ => state11_1042

def stree11LRLRLRLR (i : Nat) : State := if i < 6 then stree11LRLRLRLRL i else stree11LRLRLRLRR (i - 6)

def stree11LRLRLRL (i : Nat) : State := if i < 12 then stree11LRLRLRLL i else stree11LRLRLRLR (i - 12)

def stree11LRLRLRRLL (i : Nat) : State := match i with | 0 => state11_1043 | 1 => state11_1044 | 2 => state11_1045 | 3 => state11_1046 | 4 => state11_1047 | _ => state11_1048

def stree11LRLRLRRLR (i : Nat) : State := match i with | 0 => state11_1049 | 1 => state11_1050 | 2 => state11_1051 | 3 => state11_1052 | 4 => state11_1053 | _ => state11_1054

def stree11LRLRLRRL (i : Nat) : State := if i < 6 then stree11LRLRLRRLL i else stree11LRLRLRRLR (i - 6)

def stree11LRLRLRRRL (i : Nat) : State := match i with | 0 => state11_1055 | 1 => state11_1056 | 2 => state11_1057 | 3 => state11_1058 | 4 => state11_1059 | _ => state11_1060

def stree11LRLRLRRRR (i : Nat) : State := match i with | 0 => state11_1061 | 1 => state11_1062 | 2 => state11_1063 | 3 => state11_1064 | 4 => state11_1065 | 5 => state11_1066 | _ => state11_1067

def stree11LRLRLRRR (i : Nat) : State := if i < 6 then stree11LRLRLRRRL i else stree11LRLRLRRRR (i - 6)

def stree11LRLRLRR (i : Nat) : State := if i < 12 then stree11LRLRLRRL i else stree11LRLRLRRR (i - 12)

def stree11LRLRLR (i : Nat) : State := if i < 24 then stree11LRLRLRL i else stree11LRLRLRR (i - 24)

def stree11LRLRL (i : Nat) : State := if i < 48 then stree11LRLRLL i else stree11LRLRLR (i - 48)

def stree11LRLRRLLLL (i : Nat) : State := match i with | 0 => state11_1068 | 1 => state11_1069 | 2 => state11_1070 | 3 => state11_1071 | 4 => state11_1072 | _ => state11_1073

def stree11LRLRRLLLR (i : Nat) : State := match i with | 0 => state11_1074 | 1 => state11_1075 | 2 => state11_1076 | 3 => state11_1077 | 4 => state11_1078 | _ => state11_1079

def stree11LRLRRLLL (i : Nat) : State := if i < 6 then stree11LRLRRLLLL i else stree11LRLRRLLLR (i - 6)

def stree11LRLRRLLRL (i : Nat) : State := match i with | 0 => state11_1080 | 1 => state11_1081 | 2 => state11_1082 | 3 => state11_1083 | 4 => state11_1084 | _ => state11_1085

def stree11LRLRRLLRR (i : Nat) : State := match i with | 0 => state11_1086 | 1 => state11_1087 | 2 => state11_1088 | 3 => state11_1089 | 4 => state11_1090 | _ => state11_1091

def stree11LRLRRLLR (i : Nat) : State := if i < 6 then stree11LRLRRLLRL i else stree11LRLRRLLRR (i - 6)

def stree11LRLRRLL (i : Nat) : State := if i < 12 then stree11LRLRRLLL i else stree11LRLRRLLR (i - 12)

def stree11LRLRRLRLL (i : Nat) : State := match i with | 0 => state11_1092 | 1 => state11_1093 | 2 => state11_1094 | 3 => state11_1095 | 4 => state11_1096 | _ => state11_1097

def stree11LRLRRLRLR (i : Nat) : State := match i with | 0 => state11_1098 | 1 => state11_1099 | 2 => state11_1100 | 3 => state11_1101 | 4 => state11_1102 | _ => state11_1103

def stree11LRLRRLRL (i : Nat) : State := if i < 6 then stree11LRLRRLRLL i else stree11LRLRRLRLR (i - 6)

def stree11LRLRRLRRL (i : Nat) : State := match i with | 0 => state11_1104 | 1 => state11_1105 | 2 => state11_1106 | 3 => state11_1107 | 4 => state11_1108 | _ => state11_1109

def stree11LRLRRLRRR (i : Nat) : State := match i with | 0 => state11_1110 | 1 => state11_1111 | 2 => state11_1112 | 3 => state11_1113 | 4 => state11_1114 | _ => state11_1115

def stree11LRLRRLRR (i : Nat) : State := if i < 6 then stree11LRLRRLRRL i else stree11LRLRRLRRR (i - 6)

def stree11LRLRRLR (i : Nat) : State := if i < 12 then stree11LRLRRLRL i else stree11LRLRRLRR (i - 12)

def stree11LRLRRL (i : Nat) : State := if i < 24 then stree11LRLRRLL i else stree11LRLRRLR (i - 24)

def stree11LRLRRRLLL (i : Nat) : State := match i with | 0 => state11_1116 | 1 => state11_1117 | 2 => state11_1118 | 3 => state11_1119 | 4 => state11_1120 | _ => state11_1121

def stree11LRLRRRLLR (i : Nat) : State := match i with | 0 => state11_1122 | 1 => state11_1123 | 2 => state11_1124 | 3 => state11_1125 | 4 => state11_1126 | _ => state11_1127

def stree11LRLRRRLL (i : Nat) : State := if i < 6 then stree11LRLRRRLLL i else stree11LRLRRRLLR (i - 6)

def stree11LRLRRRLRL (i : Nat) : State := match i with | 0 => state11_1128 | 1 => state11_1129 | 2 => state11_1130 | 3 => state11_1131 | 4 => state11_1132 | _ => state11_1133

def stree11LRLRRRLRR (i : Nat) : State := match i with | 0 => state11_1134 | 1 => state11_1135 | 2 => state11_1136 | 3 => state11_1137 | 4 => state11_1138 | _ => state11_1139

def stree11LRLRRRLR (i : Nat) : State := if i < 6 then stree11LRLRRRLRL i else stree11LRLRRRLRR (i - 6)

def stree11LRLRRRL (i : Nat) : State := if i < 12 then stree11LRLRRRLL i else stree11LRLRRRLR (i - 12)

def stree11LRLRRRRLL (i : Nat) : State := match i with | 0 => state11_1140 | 1 => state11_1141 | 2 => state11_1142 | 3 => state11_1143 | 4 => state11_1144 | _ => state11_1145

def stree11LRLRRRRLR (i : Nat) : State := match i with | 0 => state11_1146 | 1 => state11_1147 | 2 => state11_1148 | 3 => state11_1149 | 4 => state11_1150 | _ => state11_1151

def stree11LRLRRRRL (i : Nat) : State := if i < 6 then stree11LRLRRRRLL i else stree11LRLRRRRLR (i - 6)

def stree11LRLRRRRRL (i : Nat) : State := match i with | 0 => state11_1152 | 1 => state11_1153 | 2 => state11_1154 | 3 => state11_1155 | 4 => state11_1156 | _ => state11_1157

def stree11LRLRRRRRR (i : Nat) : State := match i with | 0 => state11_1158 | 1 => state11_1159 | 2 => state11_1160 | 3 => state11_1161 | 4 => state11_1162 | 5 => state11_1163 | _ => state11_1164

def stree11LRLRRRRR (i : Nat) : State := if i < 6 then stree11LRLRRRRRL i else stree11LRLRRRRRR (i - 6)

def stree11LRLRRRR (i : Nat) : State := if i < 12 then stree11LRLRRRRL i else stree11LRLRRRRR (i - 12)

def stree11LRLRRR (i : Nat) : State := if i < 24 then stree11LRLRRRL i else stree11LRLRRRR (i - 24)

def stree11LRLRR (i : Nat) : State := if i < 48 then stree11LRLRRL i else stree11LRLRRR (i - 48)

def stree11LRLR (i : Nat) : State := if i < 97 then stree11LRLRL i else stree11LRLRR (i - 97)

def stree11LRL (i : Nat) : State := if i < 194 then stree11LRLL i else stree11LRLR (i - 194)

def stree11LRRLLLLLL (i : Nat) : State := match i with | 0 => state11_1165 | 1 => state11_1166 | 2 => state11_1167 | 3 => state11_1168 | 4 => state11_1169 | _ => state11_1170

def stree11LRRLLLLLR (i : Nat) : State := match i with | 0 => state11_1171 | 1 => state11_1172 | 2 => state11_1173 | 3 => state11_1174 | 4 => state11_1175 | _ => state11_1176

def stree11LRRLLLLL (i : Nat) : State := if i < 6 then stree11LRRLLLLLL i else stree11LRRLLLLLR (i - 6)

def stree11LRRLLLLRL (i : Nat) : State := match i with | 0 => state11_1177 | 1 => state11_1178 | 2 => state11_1179 | 3 => state11_1180 | 4 => state11_1181 | _ => state11_1182

def stree11LRRLLLLRR (i : Nat) : State := match i with | 0 => state11_1183 | 1 => state11_1184 | 2 => state11_1185 | 3 => state11_1186 | 4 => state11_1187 | _ => state11_1188

def stree11LRRLLLLR (i : Nat) : State := if i < 6 then stree11LRRLLLLRL i else stree11LRRLLLLRR (i - 6)

def stree11LRRLLLL (i : Nat) : State := if i < 12 then stree11LRRLLLLL i else stree11LRRLLLLR (i - 12)

def stree11LRRLLLRLL (i : Nat) : State := match i with | 0 => state11_1189 | 1 => state11_1190 | 2 => state11_1191 | 3 => state11_1192 | 4 => state11_1193 | _ => state11_1194

def stree11LRRLLLRLR (i : Nat) : State := match i with | 0 => state11_1195 | 1 => state11_1196 | 2 => state11_1197 | 3 => state11_1198 | 4 => state11_1199 | _ => state11_1200

def stree11LRRLLLRL (i : Nat) : State := if i < 6 then stree11LRRLLLRLL i else stree11LRRLLLRLR (i - 6)

def stree11LRRLLLRRL (i : Nat) : State := match i with | 0 => state11_1201 | 1 => state11_1202 | 2 => state11_1203 | 3 => state11_1204 | 4 => state11_1205 | _ => state11_1206

def stree11LRRLLLRRR (i : Nat) : State := match i with | 0 => state11_1207 | 1 => state11_1208 | 2 => state11_1209 | 3 => state11_1210 | 4 => state11_1211 | _ => state11_1212

def stree11LRRLLLRR (i : Nat) : State := if i < 6 then stree11LRRLLLRRL i else stree11LRRLLLRRR (i - 6)

def stree11LRRLLLR (i : Nat) : State := if i < 12 then stree11LRRLLLRL i else stree11LRRLLLRR (i - 12)

def stree11LRRLLL (i : Nat) : State := if i < 24 then stree11LRRLLLL i else stree11LRRLLLR (i - 24)

def stree11LRRLLRLLL (i : Nat) : State := match i with | 0 => state11_1213 | 1 => state11_1214 | 2 => state11_1215 | 3 => state11_1216 | 4 => state11_1217 | _ => state11_1218

def stree11LRRLLRLLR (i : Nat) : State := match i with | 0 => state11_1219 | 1 => state11_1220 | 2 => state11_1221 | 3 => state11_1222 | 4 => state11_1223 | _ => state11_1224

def stree11LRRLLRLL (i : Nat) : State := if i < 6 then stree11LRRLLRLLL i else stree11LRRLLRLLR (i - 6)

def stree11LRRLLRLRL (i : Nat) : State := match i with | 0 => state11_1225 | 1 => state11_1226 | 2 => state11_1227 | 3 => state11_1228 | 4 => state11_1229 | _ => state11_1230

def stree11LRRLLRLRR (i : Nat) : State := match i with | 0 => state11_1231 | 1 => state11_1232 | 2 => state11_1233 | 3 => state11_1234 | 4 => state11_1235 | _ => state11_1236

def stree11LRRLLRLR (i : Nat) : State := if i < 6 then stree11LRRLLRLRL i else stree11LRRLLRLRR (i - 6)

def stree11LRRLLRL (i : Nat) : State := if i < 12 then stree11LRRLLRLL i else stree11LRRLLRLR (i - 12)

def stree11LRRLLRRLL (i : Nat) : State := match i with | 0 => state11_1237 | 1 => state11_1238 | 2 => state11_1239 | 3 => state11_1240 | 4 => state11_1241 | _ => state11_1242

def stree11LRRLLRRLR (i : Nat) : State := match i with | 0 => state11_1243 | 1 => state11_1244 | 2 => state11_1245 | 3 => state11_1246 | 4 => state11_1247 | _ => state11_1248

def stree11LRRLLRRL (i : Nat) : State := if i < 6 then stree11LRRLLRRLL i else stree11LRRLLRRLR (i - 6)

def stree11LRRLLRRRL (i : Nat) : State := match i with | 0 => state11_1249 | 1 => state11_1250 | 2 => state11_1251 | 3 => state11_1252 | 4 => state11_1253 | _ => state11_1254

def stree11LRRLLRRRR (i : Nat) : State := match i with | 0 => state11_1255 | 1 => state11_1256 | 2 => state11_1257 | 3 => state11_1258 | 4 => state11_1259 | 5 => state11_1260 | _ => state11_1261

def stree11LRRLLRRR (i : Nat) : State := if i < 6 then stree11LRRLLRRRL i else stree11LRRLLRRRR (i - 6)

def stree11LRRLLRR (i : Nat) : State := if i < 12 then stree11LRRLLRRL i else stree11LRRLLRRR (i - 12)

def stree11LRRLLR (i : Nat) : State := if i < 24 then stree11LRRLLRL i else stree11LRRLLRR (i - 24)

def stree11LRRLL (i : Nat) : State := if i < 48 then stree11LRRLLL i else stree11LRRLLR (i - 48)

def stree11LRRLRLLLL (i : Nat) : State := match i with | 0 => state11_1262 | 1 => state11_1263 | 2 => state11_1264 | 3 => state11_1265 | 4 => state11_1266 | _ => state11_1267

def stree11LRRLRLLLR (i : Nat) : State := match i with | 0 => state11_1268 | 1 => state11_1269 | 2 => state11_1270 | 3 => state11_1271 | 4 => state11_1272 | _ => state11_1273

def stree11LRRLRLLL (i : Nat) : State := if i < 6 then stree11LRRLRLLLL i else stree11LRRLRLLLR (i - 6)

def stree11LRRLRLLRL (i : Nat) : State := match i with | 0 => state11_1274 | 1 => state11_1275 | 2 => state11_1276 | 3 => state11_1277 | 4 => state11_1278 | _ => state11_1279

def stree11LRRLRLLRR (i : Nat) : State := match i with | 0 => state11_1280 | 1 => state11_1281 | 2 => state11_1282 | 3 => state11_1283 | 4 => state11_1284 | _ => state11_1285

def stree11LRRLRLLR (i : Nat) : State := if i < 6 then stree11LRRLRLLRL i else stree11LRRLRLLRR (i - 6)

def stree11LRRLRLL (i : Nat) : State := if i < 12 then stree11LRRLRLLL i else stree11LRRLRLLR (i - 12)

def stree11LRRLRLRLL (i : Nat) : State := match i with | 0 => state11_1286 | 1 => state11_1287 | 2 => state11_1288 | 3 => state11_1289 | 4 => state11_1290 | _ => state11_1291

def stree11LRRLRLRLR (i : Nat) : State := match i with | 0 => state11_1292 | 1 => state11_1293 | 2 => state11_1294 | 3 => state11_1295 | 4 => state11_1296 | _ => state11_1297

def stree11LRRLRLRL (i : Nat) : State := if i < 6 then stree11LRRLRLRLL i else stree11LRRLRLRLR (i - 6)

def stree11LRRLRLRRL (i : Nat) : State := match i with | 0 => state11_1298 | 1 => state11_1299 | 2 => state11_1300 | 3 => state11_1301 | 4 => state11_1302 | _ => state11_1303

def stree11LRRLRLRRR (i : Nat) : State := match i with | 0 => state11_1304 | 1 => state11_1305 | 2 => state11_1306 | 3 => state11_1307 | 4 => state11_1308 | _ => state11_1309

def stree11LRRLRLRR (i : Nat) : State := if i < 6 then stree11LRRLRLRRL i else stree11LRRLRLRRR (i - 6)

def stree11LRRLRLR (i : Nat) : State := if i < 12 then stree11LRRLRLRL i else stree11LRRLRLRR (i - 12)

def stree11LRRLRL (i : Nat) : State := if i < 24 then stree11LRRLRLL i else stree11LRRLRLR (i - 24)

def stree11LRRLRRLLL (i : Nat) : State := match i with | 0 => state11_1310 | 1 => state11_1311 | 2 => state11_1312 | 3 => state11_1313 | 4 => state11_1314 | _ => state11_1315

def stree11LRRLRRLLR (i : Nat) : State := match i with | 0 => state11_1316 | 1 => state11_1317 | 2 => state11_1318 | 3 => state11_1319 | 4 => state11_1320 | _ => state11_1321

def stree11LRRLRRLL (i : Nat) : State := if i < 6 then stree11LRRLRRLLL i else stree11LRRLRRLLR (i - 6)

def stree11LRRLRRLRL (i : Nat) : State := match i with | 0 => state11_1322 | 1 => state11_1323 | 2 => state11_1324 | 3 => state11_1325 | 4 => state11_1326 | _ => state11_1327

def stree11LRRLRRLRR (i : Nat) : State := match i with | 0 => state11_1328 | 1 => state11_1329 | 2 => state11_1330 | 3 => state11_1331 | 4 => state11_1332 | _ => state11_1333

def stree11LRRLRRLR (i : Nat) : State := if i < 6 then stree11LRRLRRLRL i else stree11LRRLRRLRR (i - 6)

def stree11LRRLRRL (i : Nat) : State := if i < 12 then stree11LRRLRRLL i else stree11LRRLRRLR (i - 12)

def stree11LRRLRRRLL (i : Nat) : State := match i with | 0 => state11_1334 | 1 => state11_1335 | 2 => state11_1336 | 3 => state11_1337 | 4 => state11_1338 | _ => state11_1339

def stree11LRRLRRRLR (i : Nat) : State := match i with | 0 => state11_1340 | 1 => state11_1341 | 2 => state11_1342 | 3 => state11_1343 | 4 => state11_1344 | _ => state11_1345

def stree11LRRLRRRL (i : Nat) : State := if i < 6 then stree11LRRLRRRLL i else stree11LRRLRRRLR (i - 6)

def stree11LRRLRRRRL (i : Nat) : State := match i with | 0 => state11_1346 | 1 => state11_1347 | 2 => state11_1348 | 3 => state11_1349 | 4 => state11_1350 | _ => state11_1351

def stree11LRRLRRRRR (i : Nat) : State := match i with | 0 => state11_1352 | 1 => state11_1353 | 2 => state11_1354 | 3 => state11_1355 | 4 => state11_1356 | 5 => state11_1357 | _ => state11_1358

def stree11LRRLRRRR (i : Nat) : State := if i < 6 then stree11LRRLRRRRL i else stree11LRRLRRRRR (i - 6)

def stree11LRRLRRR (i : Nat) : State := if i < 12 then stree11LRRLRRRL i else stree11LRRLRRRR (i - 12)

def stree11LRRLRR (i : Nat) : State := if i < 24 then stree11LRRLRRL i else stree11LRRLRRR (i - 24)

def stree11LRRLR (i : Nat) : State := if i < 48 then stree11LRRLRL i else stree11LRRLRR (i - 48)

def stree11LRRL (i : Nat) : State := if i < 97 then stree11LRRLL i else stree11LRRLR (i - 97)

def stree11LRRRLLLLL (i : Nat) : State := match i with | 0 => state11_1359 | 1 => state11_1360 | 2 => state11_1361 | 3 => state11_1362 | 4 => state11_1363 | _ => state11_1364

def stree11LRRRLLLLR (i : Nat) : State := match i with | 0 => state11_1365 | 1 => state11_1366 | 2 => state11_1367 | 3 => state11_1368 | 4 => state11_1369 | _ => state11_1370

def stree11LRRRLLLL (i : Nat) : State := if i < 6 then stree11LRRRLLLLL i else stree11LRRRLLLLR (i - 6)

def stree11LRRRLLLRL (i : Nat) : State := match i with | 0 => state11_1371 | 1 => state11_1372 | 2 => state11_1373 | 3 => state11_1374 | 4 => state11_1375 | _ => state11_1376

def stree11LRRRLLLRR (i : Nat) : State := match i with | 0 => state11_1377 | 1 => state11_1378 | 2 => state11_1379 | 3 => state11_1380 | 4 => state11_1381 | _ => state11_1382

def stree11LRRRLLLR (i : Nat) : State := if i < 6 then stree11LRRRLLLRL i else stree11LRRRLLLRR (i - 6)

def stree11LRRRLLL (i : Nat) : State := if i < 12 then stree11LRRRLLLL i else stree11LRRRLLLR (i - 12)

def stree11LRRRLLRLL (i : Nat) : State := match i with | 0 => state11_1383 | 1 => state11_1384 | 2 => state11_1385 | 3 => state11_1386 | 4 => state11_1387 | _ => state11_1388

def stree11LRRRLLRLR (i : Nat) : State := match i with | 0 => state11_1389 | 1 => state11_1390 | 2 => state11_1391 | 3 => state11_1392 | 4 => state11_1393 | _ => state11_1394

def stree11LRRRLLRL (i : Nat) : State := if i < 6 then stree11LRRRLLRLL i else stree11LRRRLLRLR (i - 6)

def stree11LRRRLLRRL (i : Nat) : State := match i with | 0 => state11_1395 | 1 => state11_1396 | 2 => state11_1397 | 3 => state11_1398 | 4 => state11_1399 | _ => state11_1400

def stree11LRRRLLRRR (i : Nat) : State := match i with | 0 => state11_1401 | 1 => state11_1402 | 2 => state11_1403 | 3 => state11_1404 | 4 => state11_1405 | _ => state11_1406

def stree11LRRRLLRR (i : Nat) : State := if i < 6 then stree11LRRRLLRRL i else stree11LRRRLLRRR (i - 6)

def stree11LRRRLLR (i : Nat) : State := if i < 12 then stree11LRRRLLRL i else stree11LRRRLLRR (i - 12)

def stree11LRRRLL (i : Nat) : State := if i < 24 then stree11LRRRLLL i else stree11LRRRLLR (i - 24)

def stree11LRRRLRLLL (i : Nat) : State := match i with | 0 => state11_1407 | 1 => state11_1408 | 2 => state11_1409 | 3 => state11_1410 | 4 => state11_1411 | _ => state11_1412

def stree11LRRRLRLLR (i : Nat) : State := match i with | 0 => state11_1413 | 1 => state11_1414 | 2 => state11_1415 | 3 => state11_1416 | 4 => state11_1417 | _ => state11_1418

def stree11LRRRLRLL (i : Nat) : State := if i < 6 then stree11LRRRLRLLL i else stree11LRRRLRLLR (i - 6)

def stree11LRRRLRLRL (i : Nat) : State := match i with | 0 => state11_1419 | 1 => state11_1420 | 2 => state11_1421 | 3 => state11_1422 | 4 => state11_1423 | _ => state11_1424

def stree11LRRRLRLRR (i : Nat) : State := match i with | 0 => state11_1425 | 1 => state11_1426 | 2 => state11_1427 | 3 => state11_1428 | 4 => state11_1429 | _ => state11_1430

def stree11LRRRLRLR (i : Nat) : State := if i < 6 then stree11LRRRLRLRL i else stree11LRRRLRLRR (i - 6)

def stree11LRRRLRL (i : Nat) : State := if i < 12 then stree11LRRRLRLL i else stree11LRRRLRLR (i - 12)

def stree11LRRRLRRLL (i : Nat) : State := match i with | 0 => state11_1431 | 1 => state11_1432 | 2 => state11_1433 | 3 => state11_1434 | 4 => state11_1435 | _ => state11_1436

def stree11LRRRLRRLR (i : Nat) : State := match i with | 0 => state11_1437 | 1 => state11_1438 | 2 => state11_1439 | 3 => state11_1440 | 4 => state11_1441 | _ => state11_1442

def stree11LRRRLRRL (i : Nat) : State := if i < 6 then stree11LRRRLRRLL i else stree11LRRRLRRLR (i - 6)

def stree11LRRRLRRRL (i : Nat) : State := match i with | 0 => state11_1443 | 1 => state11_1444 | 2 => state11_1445 | 3 => state11_1446 | 4 => state11_1447 | _ => state11_1448

def stree11LRRRLRRRR (i : Nat) : State := match i with | 0 => state11_1449 | 1 => state11_1450 | 2 => state11_1451 | 3 => state11_1452 | 4 => state11_1453 | 5 => state11_1454 | _ => state11_1455

def stree11LRRRLRRR (i : Nat) : State := if i < 6 then stree11LRRRLRRRL i else stree11LRRRLRRRR (i - 6)

def stree11LRRRLRR (i : Nat) : State := if i < 12 then stree11LRRRLRRL i else stree11LRRRLRRR (i - 12)

def stree11LRRRLR (i : Nat) : State := if i < 24 then stree11LRRRLRL i else stree11LRRRLRR (i - 24)

end Paper2.Certificates.Q6.Coverage

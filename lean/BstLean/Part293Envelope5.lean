import BstLean.Part293Envelope4

namespace BstLean.Part293.Envelope
open Real

noncomputable def v225 (x : ℝ) : ℝ := (v224 x) * (v0 x)

theorem v225_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v225 x ∧ v225 x ≤ (15361320584303 / 10000000000000000 : ℝ) := by
  have h224 := v224_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v225
  constructor <;> interval_num

noncomputable def v226 (x : ℝ) : ℝ := (v0 x) * ((3 : ℝ))

theorem v226_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v226 x ∧ v226 x ≤ (375000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v226
  constructor <;> interval_num

noncomputable def v227 (x : ℝ) : ℝ := ((1 : ℝ)) - (v226 x)

theorem v227_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499812499999999999 / 500000000000000000 : ℝ) ≤ v227 x ∧ v227 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h226 := v226_bounds x hx0 hx1
  unfold v227
  constructor <;> interval_num

noncomputable def v228 (x : ℝ) : ℝ := (v225 x) / (v227 x)

theorem v228_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v228 x ∧ v228 x ≤ (1536708324051821 / 1000000000000000000 : ℝ) := by
  have h225 := v225_bounds x hx0 hx1
  have h227 := v227_bounds x hx0 hx1
  unfold v228
  constructor <;> interval_num

noncomputable def v229 (x : ℝ) : ℝ := (v6 x) ^ 2

theorem v229_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v229 x ∧ v229 x ≤ (22416815361443203601 / 1000000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  unfold v229
  constructor <;> interval_num

noncomputable def v230 (x : ℝ) : ℝ := (v229 x) * ((196 : ℝ))

theorem v230_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v230 x ∧ v230 x ≤ (4393695810842867905797 / 1000000000000000000 : ℝ) := by
  have h229 := v229_bounds x hx0 hx1
  unfold v230
  constructor <;> interval_num

noncomputable def v231 (x : ℝ) : ℝ := (v230 x) * ((1521 / 500 : ℝ))

theorem v231_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v231 x ∧ v231 x ≤ (3341405664146001042359 / 250000000000000000 : ℝ) := by
  have h230 := v230_bounds x hx0 hx1
  unfold v231
  constructor <;> interval_num

noncomputable def v232 (x : ℝ) : ℝ := (v231 x) * (v0 x)

theorem v232_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v232 x ∧ v232 x ≤ (1670702832073000523 / 1000000000000000000 : ℝ) := by
  have h231 := v231_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v232
  constructor <;> interval_num

noncomputable def v233 (x : ℝ) : ℝ := (v0 x) * ((25 : ℝ))

theorem v233_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v233 x ∧ v233 x ≤ (3125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v233
  constructor <;> interval_num

noncomputable def v234 (x : ℝ) : ℝ := ((1 : ℝ)) - (v233 x)

theorem v234_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (498437499999999999 / 500000000000000000 : ℝ) ≤ v234 x ∧ v234 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h233 := v233_bounds x hx0 hx1
  unfold v234
  constructor <;> interval_num

noncomputable def v235 (x : ℝ) : ℝ := (v234 x) * ((9 / 50 : ℝ))

theorem v235_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (89718749999999999 / 500000000000000000 : ℝ) ≤ v235 x ∧ v235 x ≤ (90000000000000001 / 500000000000000000 : ℝ) := by
  have h234 := v234_bounds x hx0 hx1
  unfold v235
  constructor <;> interval_num

noncomputable def v236 (x : ℝ) : ℝ := (v232 x) / (v235 x)

theorem v236_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v236 x ∧ v236 x ≤ (9310778583478930223 / 1000000000000000000 : ℝ) := by
  have h232 := v232_bounds x hx0 hx1
  have h235 := v235_bounds x hx0 hx1
  unfold v236
  constructor <;> interval_num

noncomputable def v237 (x : ℝ) : ℝ := √((9 / 50 : ℝ))

theorem v237_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (212132034355964257 / 500000000000000000 : ℝ) ≤ v237 x ∧ v237 x ≤ (84852813742385703 / 200000000000000000 : ℝ) := by
  unfold v237
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v238 (x : ℝ) : ℝ := (v26 x) / (v237 x)

theorem v238_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v238 x ∧ v238 x ≤ (4264400827883959 / 500000000000000000 : ℝ) := by
  have h26 := v26_bounds x hx0 hx1
  have h237 := v237_bounds x hx0 hx1
  unfold v238
  constructor <;> interval_num

noncomputable def v239 (x : ℝ) : ℝ := (v238 x) + ((1 : ℝ))

theorem v239_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v239 x ∧ v239 x ≤ (1008528801655767919 / 1000000000000000000 : ℝ) := by
  have h238 := v238_bounds x hx0 hx1
  unfold v239
  constructor <;> interval_num

noncomputable def v240 (x : ℝ) : ℝ := (v239 x) ^ 2

theorem v240_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999997 / 1000000000000000000 : ℝ) ≤ v240 x ∧ v240 x ≤ (1017130343769219269 / 1000000000000000000 : ℝ) := by
  have h239 := v239_bounds x hx0 hx1
  unfold v240
  constructor <;> interval_num

noncomputable def v241 (x : ℝ) : ℝ := (v236 x) * (v240 x)

theorem v241_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v241 x ∧ v241 x ≤ (1183784427671626091 / 125000000000000000 : ℝ) := by
  have h236 := v236_bounds x hx0 hx1
  have h240 := v240_bounds x hx0 hx1
  unfold v241
  constructor <;> interval_num

noncomputable def v242 (x : ℝ) : ℝ := (v241 x) / ((2 : ℝ))

theorem v242_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v242 x ∧ v242 x ≤ (947027542137300873 / 200000000000000000 : ℝ) := by
  have h241 := v241_bounds x hx0 hx1
  unfold v242
  constructor <;> interval_num

noncomputable def v243 (x : ℝ) : ℝ := (v195 x) + ((1 : ℝ))

theorem v243_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (199999999999999999 / 200000000000000000 : ℝ) ≤ v243 x ∧ v243 x ≤ (517203084226902699 / 500000000000000000 : ℝ) := by
  have h195 := v195_bounds x hx0 hx1
  unfold v243
  constructor <;> interval_num

noncomputable def v244 (x : ℝ) : ℝ := (v208 x) * (v243 x)

theorem v244_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v244 x ∧ v244 x ≤ (2601511013569754687 / 1000000000000000000 : ℝ) := by
  have h208 := v208_bounds x hx0 hx1
  have h243 := v243_bounds x hx0 hx1
  unfold v244
  constructor <;> interval_num

noncomputable def v245 (x : ℝ) : ℝ := (v242 x) + (v244 x)

theorem v245_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v245 x ∧ v245 x ≤ (7336648724256259053 / 1000000000000000000 : ℝ) := by
  have h242 := v242_bounds x hx0 hx1
  have h244 := v244_bounds x hx0 hx1
  unfold v245
  constructor <;> interval_num

noncomputable def v246 (x : ℝ) : ℝ := (v198 x) * (v245 x)

theorem v246_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v246 x ∧ v246 x ≤ (7345344028132653347 / 1000000000000000000 : ℝ) := by
  have h198 := v198_bounds x hx0 hx1
  have h245 := v245_bounds x hx0 hx1
  unfold v246
  constructor <;> interval_num

noncomputable def v247 (x : ℝ) : ℝ := (v221 x) / ((2 : ℝ))

theorem v247_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v247 x ∧ v247 x ≤ (2893273508978799 / 1000000000000000000 : ℝ) := by
  have h221 := v221_bounds x hx0 hx1
  unfold v247
  constructor <;> interval_num

noncomputable def v248 (x : ℝ) : ℝ := (v247 x) + (v228 x)

theorem v248_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v248 x ∧ v248 x ≤ (4429981833030621 / 1000000000000000000 : ℝ) := by
  have h247 := v247_bounds x hx0 hx1
  have h228 := v228_bounds x hx0 hx1
  unfold v248
  constructor <;> interval_num

noncomputable def v249 (x : ℝ) : ℝ := (v208 x) * (v216 x)

theorem v249_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v249 x ∧ v249 x ≤ (56847855751 / 31250000000000000 : ℝ) := by
  have h208 := v208_bounds x hx0 hx1
  have h216 := v216_bounds x hx0 hx1
  unfold v249
  constructor <;> interval_num

noncomputable def v250 (x : ℝ) : ℝ := (v249 x) * (v228 x)

theorem v250_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v250 x ∧ v250 x ≤ (1397737171 / 500000000000000000 : ℝ) := by
  have h249 := v249_bounds x hx0 hx1
  have h228 := v228_bounds x hx0 hx1
  unfold v250
  constructor <;> interval_num

noncomputable def v251 (x : ℝ) : ℝ := √(v250 x)

theorem v251_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v251 x ∧ v251 x ≤ (1321806136977 / 25000000000000000 : ℝ) := by
  have h250 := v250_bounds x hx0 hx1
  unfold v251
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v252 (x : ℝ) : ℝ := (v248 x) + (v251 x)

theorem v252_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v252 x ∧ v252 x ≤ (2241427039254851 / 500000000000000000 : ℝ) := by
  have h248 := v248_bounds x hx0 hx1
  have h251 := v251_bounds x hx0 hx1
  unfold v252
  constructor <;> interval_num

noncomputable def v253 (x : ℝ) : ℝ := (v198 x) * (v252 x)

theorem v253_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v253 x ∧ v253 x ≤ (4488167100832457 / 1000000000000000000 : ℝ) := by
  have h198 := v198_bounds x hx0 hx1
  have h252 := v252_bounds x hx0 hx1
  unfold v253
  constructor <;> interval_num

noncomputable def v254 (x : ℝ) : ℝ := (2000 / 1991 : ℝ) ^ ((8 : ℝ)⁻¹)

theorem v254_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1000563928382592107 / 1000000000000000000 : ℝ) ≤ v254 x ∧ v254 x ≤ (250140982095648027 / 250000000000000000 : ℝ) := by
  unfold v254
  constructor
  · apply (le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 8)).mpr
    rw [show (8 : ℝ) = (8 : ℕ) by norm_num, rpow_natCast]
    norm_num
  · apply (rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 8)).mpr
    rw [show (8 : ℝ) = (8 : ℕ) by norm_num, rpow_natCast]
    norm_num

noncomputable def v255 (x : ℝ) : ℝ := √((9 / 2000 : ℝ))

theorem v255_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (6708203932499369 / 100000000000000000 : ℝ) ≤ v255 x ∧ v255 x ≤ (67082039324993691 / 1000000000000000000 : ℝ) := by
  unfold v255
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v256 (x : ℝ) : ℝ := (v255 x) / ((1991 / 2000 : ℝ))

theorem v256_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (33692636526867749 / 500000000000000000 : ℝ) ≤ v256 x ∧ v256 x ≤ (33692636526867751 / 500000000000000000 : ℝ) := by
  have h255 := v255_bounds x hx0 hx1
  unfold v256
  constructor <;> interval_num

noncomputable def v257 (x : ℝ) : ℝ := (v254 x) + (v256 x)

theorem v257_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (266987300359081901 / 250000000000000000 : ℝ) ≤ v257 x ∧ v257 x ≤ (1067949201436327611 / 1000000000000000000 : ℝ) := by
  have h254 := v254_bounds x hx0 hx1
  have h256 := v256_bounds x hx0 hx1
  unfold v257
  constructor <;> interval_num

noncomputable def v258 (x : ℝ) : ℝ := √((17919 / 100000 : ℝ))

theorem v258_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (105827099553942231 / 250000000000000000 : ℝ) ≤ v258 x ∧ v258 x ≤ (16932335928630757 / 40000000000000000 : ℝ) := by
  unfold v258
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v259 (x : ℝ) : ℝ := (v26 x) / (v258 x)

theorem v259_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v259 x ∧ v259 x ≤ (2137014117228029 / 250000000000000000 : ℝ) := by
  have h26 := v26_bounds x hx0 hx1
  have h258 := v258_bounds x hx0 hx1
  unfold v259
  constructor <;> interval_num

noncomputable def v260 (x : ℝ) : ℝ := (v257 x) + (v259 x)

theorem v260_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1067949201436327603 / 1000000000000000000 : ℝ) ≤ v260 x ∧ v260 x ≤ (67281078619077483 / 62500000000000000 : ℝ) := by
  have h257 := v257_bounds x hx0 hx1
  have h259 := v259_bounds x hx0 hx1
  unfold v260
  constructor <;> interval_num

noncomputable def v261 (x : ℝ) : ℝ := (v26 x) * ((2 : ℝ))

theorem v261_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v261 x ∧ v261 x ≤ (7236928183426259 / 1000000000000000000 : ℝ) := by
  have h26 := v26_bounds x hx0 hx1
  unfold v261
  constructor <;> interval_num

noncomputable def v262 (x : ℝ) : ℝ := √((9 / 50 : ℝ))

theorem v262_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (212132034355964257 / 500000000000000000 : ℝ) ≤ v262 x ∧ v262 x ≤ (84852813742385703 / 200000000000000000 : ℝ) := by
  unfold v262
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v263 (x : ℝ) : ℝ := (v261 x) / (v262 x)

theorem v263_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v263 x ∧ v263 x ≤ (17057603311535837 / 1000000000000000000 : ℝ) := by
  have h261 := v261_bounds x hx0 hx1
  have h262 := v262_bounds x hx0 hx1
  unfold v263
  constructor <;> interval_num

noncomputable def v264 (x : ℝ) : ℝ := (v263 x) + ((2 : ℝ))

theorem v264_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1999999999999999999 / 1000000000000000000 : ℝ) ≤ v264 x ∧ v264 x ≤ (1008528801655767919 / 500000000000000000 : ℝ) := by
  have h263 := v263_bounds x hx0 hx1
  unfold v264
  constructor <;> interval_num

noncomputable def v265 (x : ℝ) : ℝ := √((9 / 50 : ℝ))

theorem v265_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (212132034355964257 / 500000000000000000 : ℝ) ≤ v265 x ∧ v265 x ≤ (84852813742385703 / 200000000000000000 : ℝ) := by
  unfold v265
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v266 (x : ℝ) : ℝ := (v264 x) / (v265 x)

theorem v266_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (235702260395515841 / 50000000000000000 : ℝ) ≤ v266 x ∧ v266 x ≤ (2377125182242453587 / 500000000000000000 : ℝ) := by
  have h264 := v264_bounds x hx0 hx1
  have h265 := v265_bounds x hx0 hx1
  unfold v266
  constructor <;> interval_num

noncomputable def v267 (x : ℝ) : ℝ := (v266 x) * (v260 x)

theorem v267_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258590203830642443 / 250000000000000000 : ℝ) ≤ v267 x ∧ v267 x ≤ (5117937480762989099 / 1000000000000000000 : ℝ) := by
  have h266 := v266_bounds x hx0 hx1
  have h260 := v260_bounds x hx0 hx1
  unfold v267
  constructor <;> interval_num

noncomputable def v268 (x : ℝ) : ℝ := (v32 x) / ((9 / 50 : ℝ))

theorem v268_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2777777777777777771 / 500000000000000000 : ℝ) ≤ v268 x ∧ v268 x ≤ (3001276852567078801 / 500000000000000000 : ℝ) := by
  have h32 := v32_bounds x hx0 hx1
  unfold v268
  constructor <;> interval_num

noncomputable def v269 (x : ℝ) : ℝ := √(v268 x)

theorem v269_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2357022603955158411 / 1000000000000000000 : ℝ) ≤ v269 x ∧ v269 x ≤ (1225005480103472599 / 500000000000000000 : ℝ) := by
  have h268 := v268_bounds x hx0 hx1
  unfold v269
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

end BstLean.Part293.Envelope

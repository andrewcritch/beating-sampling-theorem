import BstLean.Part293Envelope5

namespace BstLean.Part293.Envelope
open Real

noncomputable def v270 (x : ℝ) : ℝ := (v269 x) * (v260 x)

theorem v270_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258590203830642443 / 500000000000000000 : ℝ) ≤ v270 x ∧ v270 x ≤ (527486016100111983 / 200000000000000000 : ℝ) := by
  have h269 := v269_bounds x hx0 hx1
  have h260 := v260_bounds x hx0 hx1
  unfold v270
  constructor <;> interval_num

noncomputable def v271 (x : ℝ) : ℝ := (v3 x) ^ 2

theorem v271_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v271 x ∧ v271 x ≤ (7898364572744526401 / 1000000000000000000 : ℝ) := by
  have h3 := v3_bounds x hx0 hx1
  unfold v271
  constructor <;> interval_num

noncomputable def v272 (x : ℝ) : ℝ := (v271 x) * ((1521 / 500 : ℝ))

theorem v272_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v272 x ∧ v272 x ≤ (24026825030288849313 / 1000000000000000000 : ℝ) := by
  have h271 := v271_bounds x hx0 hx1
  unfold v272
  constructor <;> interval_num

noncomputable def v273 (x : ℝ) : ℝ := (v272 x) * (v0 x)

theorem v273_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v273 x ∧ v273 x ≤ (750838282196527 / 250000000000000000 : ℝ) := by
  have h272 := v272_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v273
  constructor <;> interval_num

noncomputable def v274 (x : ℝ) : ℝ := (v0 x) * ((9 : ℝ))

theorem v274_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v274 x ∧ v274 x ≤ (1125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v274
  constructor <;> interval_num

noncomputable def v275 (x : ℝ) : ℝ := ((1 : ℝ)) - (v274 x)

theorem v275_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499437499999999999 / 500000000000000000 : ℝ) ≤ v275 x ∧ v275 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h274 := v274_bounds x hx0 hx1
  unfold v275
  constructor <;> interval_num

noncomputable def v276 (x : ℝ) : ℝ := (v273 x) / (v275 x)

theorem v276_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v276 x ∧ v276 x ≤ (46980245413373 / 15625000000000000 : ℝ) := by
  have h273 := v273_bounds x hx0 hx1
  have h275 := v275_bounds x hx0 hx1
  unfold v276
  constructor <;> interval_num

noncomputable def v277 (x : ℝ) : ℝ := (v198 x) * (v276 x)

theorem v277_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v277 x ∧ v277 x ≤ (120411970073313 / 40000000000000000 : ℝ) := by
  have h198 := v198_bounds x hx0 hx1
  have h276 := v276_bounds x hx0 hx1
  unfold v277
  constructor <;> interval_num

noncomputable def v278 (x : ℝ) : ℝ := (v267 x) ^ 2

theorem v278_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3168098602356916183 / 125000000000000000 : ℝ) ≤ v278 x ∧ v278 x ≤ (5238656811399722283 / 200000000000000000 : ℝ) := by
  have h267 := v267_bounds x hx0 hx1
  unfold v278
  constructor <;> interval_num

noncomputable def v279 (x : ℝ) : ℝ := (v278 x) / ((2 : ℝ))

theorem v279_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (12672394409427664731 / 1000000000000000000 : ℝ) ≤ v279 x ∧ v279 x ≤ (13096642028499305709 / 1000000000000000000 : ℝ) := by
  have h278 := v278_bounds x hx0 hx1
  unfold v279
  constructor <;> interval_num

noncomputable def v280 (x : ℝ) : ℝ := (v270 x) ^ 2

theorem v280_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1267239440942766473 / 200000000000000000 : ℝ) ≤ v280 x ∧ v280 x ≤ (1391207485905837991 / 200000000000000000 : ℝ) := by
  have h270 := v270_bounds x hx0 hx1
  unfold v280
  constructor <;> interval_num

noncomputable def v281 (x : ℝ) : ℝ := (v279 x) + (v280 x)

theorem v281_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3801718322828299419 / 200000000000000000 : ℝ) ≤ v281 x ∧ v281 x ≤ (4010535891605699133 / 200000000000000000 : ℝ) := by
  have h279 := v279_bounds x hx0 hx1
  have h280 := v280_bounds x hx0 hx1
  unfold v281
  constructor <;> interval_num

noncomputable def v282 (x : ℝ) : ℝ := (v208 x) * (v0 x)

theorem v282_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v282 x ∧ v282 x ≤ (314372522722193 / 1000000000000000000 : ℝ) := by
  have h208 := v208_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v282
  constructor <;> interval_num

noncomputable def v283 (x : ℝ) : ℝ := √(v282 x)

theorem v283_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v283 x ∧ v283 x ≤ (17730553367624853 / 1000000000000000000 : ℝ) := by
  have h282 := v282_bounds x hx0 hx1
  unfold v283
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v284 (x : ℝ) : ℝ := (v283 x) * (v267 x)

theorem v284_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v284 x ∧ v284 x ≤ (45371931817417837 / 500000000000000000 : ℝ) := by
  have h283 := v283_bounds x hx0 hx1
  have h267 := v267_bounds x hx0 hx1
  unfold v284
  constructor <;> interval_num

noncomputable def v285 (x : ℝ) : ℝ := (v284 x) * (v270 x)

theorem v285_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v285 x ∧ v285 x ≤ (47866119114271297 / 200000000000000000 : ℝ) := by
  have h284 := v284_bounds x hx0 hx1
  have h270 := v270_bounds x hx0 hx1
  unfold v285
  constructor <;> interval_num

noncomputable def v286 (x : ℝ) : ℝ := (v281 x) + (v285 x)

theorem v286_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (9504295807070748547 / 500000000000000000 : ℝ) ≤ v286 x ∧ v286 x ≤ (20292010053599852151 / 1000000000000000000 : ℝ) := by
  have h281 := v281_bounds x hx0 hx1
  have h285 := v285_bounds x hx0 hx1
  unfold v286
  constructor <;> interval_num

noncomputable def v287 (x : ℝ) : ℝ := (v277 x) * (v286 x)

theorem v287_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v287 x ∧ v287 x ≤ (305425113412679 / 5000000000000000 : ℝ) := by
  have h277 := v277_bounds x hx0 hx1
  have h286 := v286_bounds x hx0 hx1
  unfold v287
  constructor <;> interval_num

noncomputable def v288 (x : ℝ) : ℝ := (2000 / 1991 : ℝ) ^ ((12 : ℝ)⁻¹)

theorem v288_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1000375916928890159 / 1000000000000000000 : ℝ) ≤ v288 x ∧ v288 x ≤ (12504698961611127 / 12500000000000000 : ℝ) := by
  unfold v288
  constructor
  · apply (le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 12)).mpr
    rw [show (12 : ℝ) = (12 : ℕ) by norm_num, rpow_natCast]
    norm_num
  · apply (rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 12)).mpr
    rw [show (12 : ℝ) = (12 : ℕ) by norm_num, rpow_natCast]
    norm_num

noncomputable def v289 (x : ℝ) : ℝ := √((9 / 2000 : ℝ))

theorem v289_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (6708203932499369 / 100000000000000000 : ℝ) ≤ v289 x ∧ v289 x ≤ (67082039324993691 / 1000000000000000000 : ℝ) := by
  unfold v289
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v290 (x : ℝ) : ℝ := (v289 x) / ((1991 / 2000 : ℝ))

theorem v290_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (33692636526867749 / 500000000000000000 : ℝ) ≤ v290 x ∧ v290 x ≤ (33692636526867751 / 500000000000000000 : ℝ) := by
  have h289 := v289_bounds x hx0 hx1
  unfold v290
  constructor <;> interval_num

noncomputable def v291 (x : ℝ) : ℝ := (v288 x) + (v290 x)

theorem v291_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (133470148747828207 / 125000000000000000 : ℝ) ≤ v291 x ∧ v291 x ≤ (1067761189982625663 / 1000000000000000000 : ℝ) := by
  have h288 := v288_bounds x hx0 hx1
  have h290 := v290_bounds x hx0 hx1
  unfold v291
  constructor <;> interval_num

noncomputable def v292 (x : ℝ) : ℝ := √((17919 / 100000 : ℝ))

theorem v292_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (105827099553942231 / 250000000000000000 : ℝ) ≤ v292 x ∧ v292 x ≤ (16932335928630757 / 40000000000000000 : ℝ) := by
  unfold v292
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v293 (x : ℝ) : ℝ := (v26 x) / (v292 x)

theorem v293_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v293 x ∧ v293 x ≤ (2137014117228029 / 250000000000000000 : ℝ) := by
  have h26 := v26_bounds x hx0 hx1
  have h292 := v292_bounds x hx0 hx1
  unfold v293
  constructor <;> interval_num

noncomputable def v294 (x : ℝ) : ℝ := (v291 x) + (v293 x)

theorem v294_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (213552237996525131 / 200000000000000000 : ℝ) ≤ v294 x ∧ v294 x ≤ (53815462322576889 / 50000000000000000 : ℝ) := by
  have h291 := v291_bounds x hx0 hx1
  have h293 := v293_bounds x hx0 hx1
  unfold v294
  constructor <;> interval_num

noncomputable def v295 (x : ℝ) : ℝ := (v26 x) * ((2 : ℝ))

theorem v295_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v295 x ∧ v295 x ≤ (7236928183426259 / 1000000000000000000 : ℝ) := by
  have h26 := v26_bounds x hx0 hx1
  unfold v295
  constructor <;> interval_num

noncomputable def v296 (x : ℝ) : ℝ := √((9 / 50 : ℝ))

theorem v296_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (212132034355964257 / 500000000000000000 : ℝ) ≤ v296 x ∧ v296 x ≤ (84852813742385703 / 200000000000000000 : ℝ) := by
  unfold v296
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v297 (x : ℝ) : ℝ := (v295 x) / (v296 x)

theorem v297_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v297 x ∧ v297 x ≤ (17057603311535837 / 1000000000000000000 : ℝ) := by
  have h295 := v295_bounds x hx0 hx1
  have h296 := v296_bounds x hx0 hx1
  unfold v297
  constructor <;> interval_num

noncomputable def v298 (x : ℝ) : ℝ := (v297 x) + ((2 : ℝ))

theorem v298_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1999999999999999999 / 1000000000000000000 : ℝ) ≤ v298 x ∧ v298 x ≤ (1008528801655767919 / 500000000000000000 : ℝ) := by
  have h297 := v297_bounds x hx0 hx1
  unfold v298
  constructor <;> interval_num

noncomputable def v299 (x : ℝ) : ℝ := √((9 / 50 : ℝ))

theorem v299_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (212132034355964257 / 500000000000000000 : ℝ) ≤ v299 x ∧ v299 x ≤ (84852813742385703 / 200000000000000000 : ℝ) := by
  unfold v299
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v300 (x : ℝ) : ℝ := (v298 x) / (v299 x)

theorem v300_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (235702260395515841 / 50000000000000000 : ℝ) ≤ v300 x ∧ v300 x ≤ (2377125182242453587 / 500000000000000000 : ℝ) := by
  have h298 := v298_bounds x hx0 hx1
  have h299 := v299_bounds x hx0 hx1
  unfold v300
  constructor <;> interval_num

noncomputable def v301 (x : ℝ) : ℝ := (v300 x) * (v294 x)

theorem v301_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258368630207553463 / 250000000000000000 : ℝ) ≤ v301 x ∧ v301 x ≤ (204681745089627971 / 40000000000000000 : ℝ) := by
  have h300 := v300_bounds x hx0 hx1
  have h294 := v294_bounds x hx0 hx1
  unfold v301
  constructor <;> interval_num

noncomputable def v302 (x : ℝ) : ℝ := (v32 x) / ((9 / 50 : ℝ))

theorem v302_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2777777777777777771 / 500000000000000000 : ℝ) ≤ v302 x ∧ v302 x ≤ (3001276852567078801 / 500000000000000000 : ℝ) := by
  have h32 := v32_bounds x hx0 hx1
  unfold v302
  constructor <;> interval_num

noncomputable def v303 (x : ℝ) : ℝ := √(v302 x)

theorem v303_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2357022603955158411 / 1000000000000000000 : ℝ) ≤ v303 x ∧ v303 x ≤ (1225005480103472599 / 500000000000000000 : ℝ) := by
  have h302 := v302_bounds x hx0 hx1
  unfold v303
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v304 (x : ℝ) : ℝ := (v303 x) * (v294 x)

theorem v304_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258368630207553463 / 500000000000000000 : ℝ) ≤ v304 x ∧ v304 x ≤ (2636969450378345701 / 1000000000000000000 : ℝ) := by
  have h303 := v303_bounds x hx0 hx1
  have h294 := v294_bounds x hx0 hx1
  unfold v304
  constructor <;> interval_num

noncomputable def v305 (x : ℝ) : ℝ := (v4 x) ^ 2

theorem v305_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v305 x ∧ v305 x ≤ (11526848913323395601 / 1000000000000000000 : ℝ) := by
  have h4 := v4_bounds x hx0 hx1
  unfold v305
  constructor <;> interval_num

noncomputable def v306 (x : ℝ) : ℝ := (v305 x) * ((1521 / 500 : ℝ))

theorem v306_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v306 x ∧ v306 x ≤ (1753233719716488471 / 50000000000000000 : ℝ) := by
  have h305 := v305_bounds x hx0 hx1
  unfold v306
  constructor <;> interval_num

noncomputable def v307 (x : ℝ) : ℝ := (v306 x) * (v0 x)

theorem v307_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v307 x ∧ v307 x ≤ (4383084299291223 / 1000000000000000000 : ℝ) := by
  have h306 := v306_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v307
  constructor <;> interval_num

noncomputable def v308 (x : ℝ) : ℝ := (v0 x) * ((13 : ℝ))

theorem v308_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v308 x ∧ v308 x ≤ (1625000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v308
  constructor <;> interval_num

noncomputable def v309 (x : ℝ) : ℝ := ((1 : ℝ)) - (v308 x)

theorem v309_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499187499999999999 / 500000000000000000 : ℝ) ≤ v309 x ∧ v309 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h308 := v308_bounds x hx0 hx1
  unfold v309
  constructor <;> interval_num

noncomputable def v310 (x : ℝ) : ℝ := (v307 x) / (v309 x)

theorem v310_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v310 x ∧ v310 x ≤ (2195109202099023 / 500000000000000000 : ℝ) := by
  have h307 := v307_bounds x hx0 hx1
  have h309 := v309_bounds x hx0 hx1
  unfold v310
  constructor <;> interval_num

noncomputable def v311 (x : ℝ) : ℝ := (v198 x) * (v310 x)

theorem v311_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v311 x ∧ v311 x ≤ (2197710817941829 / 500000000000000000 : ℝ) := by
  have h198 := v198_bounds x hx0 hx1
  have h310 := v310_bounds x hx0 hx1
  unfold v311
  constructor <;> interval_num

noncomputable def v312 (x : ℝ) : ℝ := (v301 x) ^ 2

theorem v312_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1266793287592347547 / 50000000000000000 : ℝ) ≤ v312 x ∧ v312 x ≤ (26184135483084652513 / 1000000000000000000 : ℝ) := by
  have h301 := v301_bounds x hx0 hx1
  unfold v312
  constructor <;> interval_num

noncomputable def v313 (x : ℝ) : ℝ := (v312 x) / ((2 : ℝ))

theorem v313_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (12667932875923475469 / 1000000000000000000 : ℝ) ≤ v313 x ∧ v313 x ≤ (6546033870771163129 / 500000000000000000 : ℝ) := by
  have h312 := v312_bounds x hx0 hx1
  unfold v313
  constructor <;> interval_num

noncomputable def v314 (x : ℝ) : ℝ := (v304 x) ^ 2

theorem v314_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3166983218980868867 / 500000000000000000 : ℝ) ≤ v314 x ∧ v314 x ≤ (1738401970557168653 / 250000000000000000 : ℝ) := by
  have h304 := v304_bounds x hx0 hx1
  unfold v314
  constructor <;> interval_num

end BstLean.Part293.Envelope

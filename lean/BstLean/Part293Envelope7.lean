import BstLean.Part293Envelope6

namespace BstLean.Part293.Envelope
open Real

noncomputable def v315 (x : ℝ) : ℝ := (v313 x) + (v314 x)

theorem v315_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (9500949656942606601 / 500000000000000000 : ℝ) ≤ v315 x ∧ v315 x ≤ (20045675623771000871 / 1000000000000000000 : ℝ) := by
  have h313 := v313_bounds x hx0 hx1
  have h314 := v314_bounds x hx0 hx1
  unfold v315
  constructor <;> interval_num

noncomputable def v316 (x : ℝ) : ℝ := (v208 x) * (v0 x)

theorem v316_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v316 x ∧ v316 x ≤ (314372522722193 / 1000000000000000000 : ℝ) := by
  have h208 := v208_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v316
  constructor <;> interval_num

noncomputable def v317 (x : ℝ) : ℝ := √(v316 x)

theorem v317_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v317 x ∧ v317 x ≤ (17730553367624853 / 1000000000000000000 : ℝ) := by
  have h316 := v316_bounds x hx0 hx1
  unfold v317
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v318 (x : ℝ) : ℝ := (v317 x) * (v301 x)

theorem v318_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v318 x ∧ v318 x ≤ (725824120938047 / 8000000000000000 : ℝ) := by
  have h317 := v317_bounds x hx0 hx1
  have h301 := v301_bounds x hx0 hx1
  unfold v318
  constructor <;> interval_num

noncomputable def v319 (x : ℝ) : ℝ := (v318 x) * (v304 x)

theorem v319_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v319 x ∧ v319 x ≤ (119623502078834233 / 500000000000000000 : ℝ) := by
  have h318 := v318_bounds x hx0 hx1
  have h304 := v304_bounds x hx0 hx1
  unfold v319
  constructor <;> interval_num

noncomputable def v320 (x : ℝ) : ℝ := (v315 x) + (v319 x)

theorem v320_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (19001899313885213201 / 1000000000000000000 : ℝ) ≤ v320 x ∧ v320 x ≤ (10142461313964334669 / 500000000000000000 : ℝ) := by
  have h315 := v315_bounds x hx0 hx1
  have h319 := v319_bounds x hx0 hx1
  unfold v320
  constructor <;> interval_num

noncomputable def v321 (x : ℝ) : ℝ := (v311 x) * (v320 x)

theorem v321_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v321 x ∧ v321 x ≤ (5572549237563979 / 62500000000000000 : ℝ) := by
  have h311 := v311_bounds x hx0 hx1
  have h320 := v320_bounds x hx0 hx1
  unfold v321
  constructor <;> interval_num

noncomputable def v322 (x : ℝ) : ℝ := (v221 x) * (v216 x)

theorem v322_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v322 x ∧ v322 x ≤ (4185515801 / 1000000000000000000 : ℝ) := by
  have h221 := v221_bounds x hx0 hx1
  have h216 := v216_bounds x hx0 hx1
  unfold v322
  constructor <;> interval_num

noncomputable def v323 (x : ℝ) : ℝ := (v322 x) / ((4 : ℝ))

theorem v323_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v323 x ∧ v323 x ≤ (130797369 / 125000000000000000 : ℝ) := by
  have h322 := v322_bounds x hx0 hx1
  unfold v323
  constructor <;> interval_num

noncomputable def v324 (x : ℝ) : ℝ := (v195 x) + ((1 : ℝ))

theorem v324_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (199999999999999999 / 200000000000000000 : ℝ) ≤ v324 x ∧ v324 x ≤ (517203084226902699 / 500000000000000000 : ℝ) := by
  have h195 := v195_bounds x hx0 hx1
  unfold v324
  constructor <;> interval_num

noncomputable def v325 (x : ℝ) : ℝ := (v324 x) * (v216 x)

theorem v325_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v325 x ∧ v325 x ≤ (748204991239 / 1000000000000000000 : ℝ) := by
  have h324 := v324_bounds x hx0 hx1
  have h216 := v216_bounds x hx0 hx1
  unfold v325
  constructor <;> interval_num

noncomputable def v326 (x : ℝ) : ℝ := (v325 x) * (v228 x)

theorem v326_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v326 x ∧ v326 x ≤ (28744321 / 25000000000000000 : ℝ) := by
  have h325 := v325_bounds x hx0 hx1
  have h228 := v228_bounds x hx0 hx1
  unfold v326
  constructor <;> interval_num

noncomputable def v327 (x : ℝ) : ℝ := (v323 x) + (v326 x)

theorem v327_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v327 x ∧ v327 x ≤ (2196151793 / 1000000000000000000 : ℝ) := by
  have h323 := v323_bounds x hx0 hx1
  have h326 := v326_bounds x hx0 hx1
  unfold v327
  constructor <;> interval_num

noncomputable def v328 (x : ℝ) : ℝ := (v198 x) * (v327 x)

theorem v328_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v328 x ∧ v328 x ≤ (1099377323 / 500000000000000000 : ℝ) := by
  have h198 := v198_bounds x hx0 hx1
  have h327 := v327_bounds x hx0 hx1
  unfold v328
  constructor <;> interval_num

noncomputable def v329 (x : ℝ) : ℝ := (v253 x) ^ 2

theorem v329_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v329 x ∧ v329 x ≤ (5035910981249 / 250000000000000000 : ℝ) := by
  have h253 := v253_bounds x hx0 hx1
  unfold v329
  constructor <;> interval_num

noncomputable def v330 (x : ℝ) : ℝ := (v329 x) / ((2 : ℝ))

theorem v330_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v330 x ∧ v330 x ≤ (10071821962499 / 1000000000000000000 : ℝ) := by
  have h329 := v329_bounds x hx0 hx1
  unfold v330
  constructor <;> interval_num

noncomputable def v331 (x : ℝ) : ℝ := (v328 x) + (v330 x)

theorem v331_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v331 x ∧ v331 x ≤ (5037010358573 / 500000000000000000 : ℝ) := by
  have h328 := v328_bounds x hx0 hx1
  have h330 := v330_bounds x hx0 hx1
  unfold v331
  constructor <;> interval_num

noncomputable def v332 (x : ℝ) : ℝ := (v287 x) ^ 2

theorem v332_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v332 x ∧ v332 x ≤ (746275999225183 / 200000000000000000 : ℝ) := by
  have h287 := v287_bounds x hx0 hx1
  unfold v332
  constructor <;> interval_num

noncomputable def v333 (x : ℝ) : ℝ := (v253 x) * (v332 x)

theorem v333_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v333 x ∧ v333 x ≤ (8373528469659 / 500000000000000000 : ℝ) := by
  have h253 := v253_bounds x hx0 hx1
  have h332 := v332_bounds x hx0 hx1
  unfold v333
  constructor <;> interval_num

noncomputable def v334 (x : ℝ) : ℝ := (v333 x) / ((6 : ℝ))

theorem v334_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v334 x ∧ v334 x ≤ (558235231311 / 200000000000000000 : ℝ) := by
  have h333 := v333_bounds x hx0 hx1
  unfold v334
  constructor <;> interval_num

noncomputable def v335 (x : ℝ) : ℝ := (v331 x) + (v334 x)

theorem v335_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v335 x ∧ v335 x ≤ (6432598436851 / 500000000000000000 : ℝ) := by
  have h331 := v331_bounds x hx0 hx1
  have h334 := v334_bounds x hx0 hx1
  unfold v335
  constructor <;> interval_num

noncomputable def v336 (x : ℝ) : ℝ := (v287 x) ^ 4

theorem v336_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v336 x ∧ v336 x ≤ (1392319667549 / 100000000000000000 : ℝ) := by
  have h287 := v287_bounds x hx0 hx1
  unfold v336
  constructor <;> interval_num

noncomputable def v337 (x : ℝ) : ℝ := (v336 x) / ((24 : ℝ))

theorem v337_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v337 x ∧ v337 x ≤ (290066597407 / 500000000000000000 : ℝ) := by
  have h336 := v336_bounds x hx0 hx1
  unfold v337
  constructor <;> interval_num

noncomputable def v338 (x : ℝ) : ℝ := (v335 x) + (v337 x)

theorem v338_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v338 x ∧ v338 x ≤ (13445330068517 / 1000000000000000000 : ℝ) := by
  have h335 := v335_bounds x hx0 hx1
  have h337 := v337_bounds x hx0 hx1
  unfold v338
  constructor <;> interval_num

noncomputable def v339 (x : ℝ) : ℝ := (v321 x) ^ 5

theorem v339_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v339 x ∧ v339 x ≤ (176083842719 / 31250000000000000 : ℝ) := by
  have h321 := v321_bounds x hx0 hx1
  unfold v339
  constructor <;> interval_num

noncomputable def v340 (x : ℝ) : ℝ := (v339 x) / ((120 : ℝ))

theorem v340_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v340 x ∧ v340 x ≤ (46955691393 / 1000000000000000000 : ℝ) := by
  have h339 := v339_bounds x hx0 hx1
  unfold v340
  constructor <;> interval_num

noncomputable def v341 (x : ℝ) : ℝ := (v338 x) + (v340 x)

theorem v341_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v341 x ∧ v341 x ≤ (13492285759911 / 1000000000000000000 : ℝ) := by
  have h338 := v338_bounds x hx0 hx1
  have h340 := v340_bounds x hx0 hx1
  unfold v341
  constructor <;> interval_num

noncomputable def v342 (x : ℝ) : ℝ := exp (v246 x)

theorem v342_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v342 x ∧ v342 x ≤ (77448388109780436519 / 50000000000000000 : ℝ) := by
  have h246 := v246_bounds x hx0 hx1
  unfold v342
  constructor
  · exact (exp_pos _).le
  · apply exp_scaled_upper (v := (56080827923130179 / 50000000000000000 : ℝ))
    · apply (exp_enclose (l := -1) _ _ _).2
      · apply abs_le.mpr; constructor <;> interval_num
      · dsimp only [expApprox16]; interval_num
      · dsimp only [expApprox16]; interval_num
    · norm_num

noncomputable def v343 (x : ℝ) : ℝ := (v321 x) ^ 6

theorem v343_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v343 x ∧ v343 x ≤ (502392772349 / 1000000000000000000 : ℝ) := by
  have h321 := v321_bounds x hx0 hx1
  unfold v343
  constructor <;> interval_num

noncomputable def v344 (x : ℝ) : ℝ := (v342 x) * (v343 x)

theorem v344_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v344 x ∧ v344 x ≤ (19454755208217 / 25000000000000000 : ℝ) := by
  have h342 := v342_bounds x hx0 hx1
  have h343 := v343_bounds x hx0 hx1
  unfold v344
  constructor <;> interval_num

noncomputable def v345 (x : ℝ) : ℝ := (v344 x) / ((720 : ℝ))

theorem v345_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v345 x ∧ v345 x ≤ (1080819733791 / 1000000000000000000 : ℝ) := by
  have h344 := v344_bounds x hx0 hx1
  unfold v345
  constructor <;> interval_num

noncomputable def v346 (x : ℝ) : ℝ := (v341 x) + (v345 x)

theorem v346_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v346 x ∧ v346 x ≤ (14573105493703 / 1000000000000000000 : ℝ) := by
  have h341 := v341_bounds x hx0 hx1
  have h345 := v345_bounds x hx0 hx1
  unfold v346
  constructor <;> interval_num

noncomputable def v347 (x : ℝ) : ℝ := ((1 : ℝ)) - (v195 x)

theorem v347_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (482796915773097301 / 500000000000000000 : ℝ) ≤ v347 x ∧ v347 x ≤ (200000000000000001 / 200000000000000000 : ℝ) := by
  have h195 := v195_bounds x hx0 hx1
  unfold v347
  constructor <;> interval_num

noncomputable def v348 (x : ℝ) : ℝ := (v347 x) ^ 2

theorem v348_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (233092861880015209 / 250000000000000000 : ℝ) ≤ v348 x ∧ v348 x ≤ (250000000000000003 / 250000000000000000 : ℝ) := by
  have h347 := v347_bounds x hx0 hx1
  unfold v348
  constructor <;> interval_num

noncomputable def v349 (x : ℝ) : ℝ := (v348 x) * ((4 : ℝ))

theorem v349_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3729485790080243343 / 1000000000000000000 : ℝ) ≤ v349 x ∧ v349 x ≤ (4000000000000000049 / 1000000000000000000 : ℝ) := by
  have h348 := v348_bounds x hx0 hx1
  unfold v349
  constructor <;> interval_num

noncomputable def v350 (x : ℝ) : ℝ := (v221 x) / (v349 x)

theorem v350_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v350 x ∧ v350 x ≤ (387891745917679 / 250000000000000000 : ℝ) := by
  have h221 := v221_bounds x hx0 hx1
  have h349 := v349_bounds x hx0 hx1
  unfold v350
  constructor <;> interval_num

noncomputable def v351 (x : ℝ) : ℝ := ((1 : ℝ)) - (v195 x)

theorem v351_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (482796915773097301 / 500000000000000000 : ℝ) ≤ v351 x ∧ v351 x ≤ (200000000000000001 / 200000000000000000 : ℝ) := by
  have h195 := v195_bounds x hx0 hx1
  unfold v351
  constructor <;> interval_num

noncomputable def v352 (x : ℝ) : ℝ := (v351 x) * ((2 : ℝ))

theorem v352_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1931187663092389203 / 1000000000000000000 : ℝ) ≤ v352 x ∧ v352 x ≤ (2000000000000000011 / 1000000000000000000 : ℝ) := by
  have h351 := v351_bounds x hx0 hx1
  unfold v352
  constructor <;> interval_num

noncomputable def v353 (x : ℝ) : ℝ := (v228 x) / (v352 x)

theorem v353_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v353 x ∧ v353 x ≤ (198933065053749 / 250000000000000000 : ℝ) := by
  have h228 := v228_bounds x hx0 hx1
  have h352 := v352_bounds x hx0 hx1
  unfold v353
  constructor <;> interval_num

noncomputable def v354 (x : ℝ) : ℝ := (v350 x) + (v353 x)

theorem v354_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v354 x ∧ v354 x ≤ (2347299243885713 / 1000000000000000000 : ℝ) := by
  have h350 := v350_bounds x hx0 hx1
  have h353 := v353_bounds x hx0 hx1
  unfold v354
  constructor <;> interval_num

noncomputable def v355 (x : ℝ) : ℝ := (v216 x) * (v228 x)

theorem v355_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v355 x ∧ v355 x ≤ (1111529373 / 1000000000000000000 : ℝ) := by
  have h216 := v216_bounds x hx0 hx1
  have h228 := v228_bounds x hx0 hx1
  unfold v355
  constructor <;> interval_num

noncomputable def v356 (x : ℝ) : ℝ := √(v355 x)

theorem v356_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v356 x ∧ v356 x ≤ (16669803335673 / 500000000000000000 : ℝ) := by
  have h355 := v355_bounds x hx0 hx1
  unfold v356
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v357 (x : ℝ) : ℝ := (v0 x) / ((2 : ℝ))

theorem v357_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v357 x ∧ v357 x ≤ (62500000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v357
  constructor <;> interval_num

noncomputable def v358 (x : ℝ) : ℝ := √(v357 x)

theorem v358_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v358 x ∧ v358 x ≤ (1976423537605253 / 250000000000000000 : ℝ) := by
  have h357 := v357_bounds x hx0 hx1
  unfold v358
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v359 (x : ℝ) : ℝ := (v358 x) * (v221 x)

theorem v359_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v359 x ∧ v359 x ≤ (9149334182201 / 200000000000000000 : ℝ) := by
  have h358 := v358_bounds x hx0 hx1
  have h221 := v221_bounds x hx0 hx1
  unfold v359
  constructor <;> interval_num

end BstLean.Part293.Envelope

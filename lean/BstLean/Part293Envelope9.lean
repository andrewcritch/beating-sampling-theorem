import BstLean.Part293Envelope8

namespace BstLean.Part293.Envelope
open Real

noncomputable def v405 (x : ℝ) : ℝ := (v402 x) * (v404 x)

theorem v405_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (249999999999999999 / 250000000000000000 : ℝ) ≤ v405 x ∧ v405 x ≤ (31634681680154899 / 31250000000000000 : ℝ) := by
  have h402 := v402_bounds x hx0 hx1
  have h404 := v404_bounds x hx0 hx1
  unfold v405
  constructor <;> interval_num

noncomputable def v406 (x : ℝ) : ℝ := ((1 : ℝ)) - (v0 x)

theorem v406_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999874999999999999 / 1000000000000000000 : ℝ) ≤ v406 x ∧ v406 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v406
  constructor <;> interval_num

noncomputable def v407 (x : ℝ) : ℝ := (v0 x) / (v406 x)

theorem v407_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v407 x ∧ v407 x ≤ (125015626953371 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  have h406 := v406_bounds x hx0 hx1
  unfold v407
  constructor <;> interval_num

noncomputable def v408 (x : ℝ) : ℝ := √(v407 x)

theorem v408_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v408 x ∧ v408 x ≤ (2795259681064657 / 250000000000000000 : ℝ) := by
  have h407 := v407_bounds x hx0 hx1
  unfold v408
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v409 (x : ℝ) : ℝ := (v408 x) * ((2 : ℝ))

theorem v409_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v409 x ∧ v409 x ≤ (22362077448517257 / 1000000000000000000 : ℝ) := by
  have h408 := v408_bounds x hx0 hx1
  unfold v409
  constructor <;> interval_num

noncomputable def v410 (x : ℝ) : ℝ := √(v0 x)

theorem v410_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v410 x ∧ v410 x ≤ (11180339887498949 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v410
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v411 (x : ℝ) : ℝ := (v410 x) + ((1 : ℝ))

theorem v411_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v411 x ∧ v411 x ≤ (20223606797749979 / 20000000000000000 : ℝ) := by
  have h410 := v410_bounds x hx0 hx1
  unfold v411
  constructor <;> interval_num

noncomputable def v412 (x : ℝ) : ℝ := (v0 x) * ((6 : ℝ))

theorem v412_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v412 x ∧ v412 x ≤ (750000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v412
  constructor <;> interval_num

noncomputable def v413 (x : ℝ) : ℝ := (v411 x) + (v412 x)

theorem v413_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499999999999999999 / 500000000000000000 : ℝ) ≤ v413 x ∧ v413 x ≤ (126491292485937369 / 125000000000000000 : ℝ) := by
  have h411 := v411_bounds x hx0 hx1
  have h412 := v412_bounds x hx0 hx1
  unfold v413
  constructor <;> interval_num

noncomputable def v414 (x : ℝ) : ℝ := (v409 x) * (v413 x)

theorem v414_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v414 x ∧ v414 x ≤ (4525772926613729 / 200000000000000000 : ℝ) := by
  have h409 := v409_bounds x hx0 hx1
  have h413 := v413_bounds x hx0 hx1
  unfold v414
  constructor <;> interval_num

noncomputable def v415 (x : ℝ) : ℝ := ((19 / 100 : ℝ)) * (v414 x)

theorem v415_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v415 x ∧ v415 x ≤ (1074871070070761 / 250000000000000000 : ℝ) := by
  have h414 := v414_bounds x hx0 hx1
  unfold v415
  constructor <;> interval_num

noncomputable def v416 (x : ℝ) : ℝ := √(v398 x)

theorem v416_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (367423461417476713 / 500000000000000000 : ℝ) ≤ v416 x ∧ v416 x ≤ (155491097138791149 / 200000000000000000 : ℝ) := by
  have h398 := v398_bounds x hx0 hx1
  unfold v416
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v417 (x : ℝ) : ℝ := (v415 x) * (v416 x)

theorem v417_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v417 x ∧ v417 x ≤ (3342657639360983 / 1000000000000000000 : ℝ) := by
  have h415 := v415_bounds x hx0 hx1
  have h416 := v416_bounds x hx0 hx1
  unfold v417
  constructor <;> interval_num

noncomputable def v418 (x : ℝ) : ℝ := √(v0 x)

theorem v418_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v418 x ∧ v418 x ≤ (11180339887498949 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v418
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v419 (x : ℝ) : ℝ := (v0 x) * (v418 x)

theorem v419_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v419 x ∧ v419 x ≤ (1397542485939 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  have h418 := v418_bounds x hx0 hx1
  unfold v419
  constructor <;> interval_num

noncomputable def v420 (x : ℝ) : ℝ := ((1 : ℝ)) - (v419 x)

theorem v420_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (49999930122875703 / 50000000000000000 : ℝ) ≤ v420 x ∧ v420 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h419 := v419_bounds x hx0 hx1
  unfold v420
  constructor <;> interval_num

noncomputable def v421 (x : ℝ) : ℝ := (v417 x) / (v420 x)

theorem v421_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v421 x ∧ v421 x ≤ (167133115543679 / 50000000000000000 : ℝ) := by
  have h417 := v417_bounds x hx0 hx1
  have h420 := v420_bounds x hx0 hx1
  unfold v421
  constructor <;> interval_num

noncomputable def v422 (x : ℝ) : ℝ := ((9 / 100 : ℝ)) * ((4 : ℝ))

theorem v422_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (359999999999999999 / 1000000000000000000 : ℝ) ≤ v422 x ∧ v422 x ≤ (360000000000000001 / 1000000000000000000 : ℝ) := by
  unfold v422
  constructor <;> interval_num

noncomputable def v423 (x : ℝ) : ℝ := (v422 x) * (v398 x)

theorem v423_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (194399999999999997 / 1000000000000000000 : ℝ) ≤ v423 x ∧ v423 x ≤ (217597331604824867 / 1000000000000000000 : ℝ) := by
  have h422 := v422_bounds x hx0 hx1
  have h398 := v398_bounds x hx0 hx1
  unfold v423
  constructor <;> interval_num

noncomputable def v424 (x : ℝ) : ℝ := √(v0 x)

theorem v424_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v424 x ∧ v424 x ≤ (11180339887498949 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v424
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v425 (x : ℝ) : ℝ := (v423 x) * (v424 x)

theorem v425_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v425 x ∧ v425 x ≤ (2432812125954761 / 1000000000000000000 : ℝ) := by
  have h423 := v423_bounds x hx0 hx1
  have h424 := v424_bounds x hx0 hx1
  unfold v425
  constructor <;> interval_num

noncomputable def v426 (x : ℝ) : ℝ := √(v0 x)

theorem v426_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v426 x ∧ v426 x ≤ (11180339887498949 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v426
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v427 (x : ℝ) : ℝ := (v426 x) + ((1 : ℝ))

theorem v427_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v427 x ∧ v427 x ≤ (20223606797749979 / 20000000000000000 : ℝ) := by
  have h426 := v426_bounds x hx0 hx1
  unfold v427
  constructor <;> interval_num

noncomputable def v428 (x : ℝ) : ℝ := (v0 x) * ((6 : ℝ))

theorem v428_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v428 x ∧ v428 x ≤ (750000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v428
  constructor <;> interval_num

noncomputable def v429 (x : ℝ) : ℝ := (v427 x) + (v428 x)

theorem v429_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499999999999999999 / 500000000000000000 : ℝ) ≤ v429 x ∧ v429 x ≤ (126491292485937369 / 125000000000000000 : ℝ) := by
  have h427 := v427_bounds x hx0 hx1
  have h428 := v428_bounds x hx0 hx1
  unfold v429
  constructor <;> interval_num

noncomputable def v430 (x : ℝ) : ℝ := (v429 x) ^ 2

theorem v430_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (199999999999999999 / 200000000000000000 : ℝ) ≤ v430 x ∧ v430 x ≤ (512001506392414577 / 500000000000000000 : ℝ) := by
  have h429 := v429_bounds x hx0 hx1
  unfold v430
  constructor <;> interval_num

noncomputable def v431 (x : ℝ) : ℝ := (v425 x) * (v430 x)

theorem v431_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v431 x ∧ v431 x ≤ (1245603473258571 / 500000000000000000 : ℝ) := by
  have h425 := v425_bounds x hx0 hx1
  have h430 := v430_bounds x hx0 hx1
  unfold v431
  constructor <;> interval_num

noncomputable def v432 (x : ℝ) : ℝ := ((1 : ℝ)) - (v0 x)

theorem v432_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999874999999999999 / 1000000000000000000 : ℝ) ≤ v432 x ∧ v432 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v432
  constructor <;> interval_num

noncomputable def v433 (x : ℝ) : ℝ := √(v0 x)

theorem v433_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v433 x ∧ v433 x ≤ (11180339887498949 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v433
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v434 (x : ℝ) : ℝ := (v0 x) * (v433 x)

theorem v434_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v434 x ∧ v434 x ≤ (1397542485939 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  have h433 := v433_bounds x hx0 hx1
  unfold v434
  constructor <;> interval_num

noncomputable def v435 (x : ℝ) : ℝ := ((1 : ℝ)) - (v434 x)

theorem v435_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (49999930122875703 / 50000000000000000 : ℝ) ≤ v435 x ∧ v435 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h434 := v434_bounds x hx0 hx1
  unfold v435
  constructor <;> interval_num

noncomputable def v436 (x : ℝ) : ℝ := (v432 x) * (v435 x)

theorem v436_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (249968400658051717 / 250000000000000000 : ℝ) ≤ v436 x ∧ v436 x ≤ (250000000000000001 / 250000000000000000 : ℝ) := by
  have h432 := v432_bounds x hx0 hx1
  have h435 := v435_bounds x hx0 hx1
  unfold v436
  constructor <;> interval_num

noncomputable def v437 (x : ℝ) : ℝ := (v431 x) / (v436 x)

theorem v437_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v437 x ∧ v437 x ≤ (2491521868323099 / 1000000000000000000 : ℝ) := by
  have h431 := v431_bounds x hx0 hx1
  have h436 := v436_bounds x hx0 hx1
  unfold v437
  constructor <;> interval_num

noncomputable def v438 (x : ℝ) : ℝ := (v0 x) * ((27 / 50 : ℝ))

theorem v438_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v438 x ∧ v438 x ≤ (67500000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v438
  constructor <;> interval_num

noncomputable def v439 (x : ℝ) : ℝ := √(v438 x)

theorem v439_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v439 x ∧ v439 x ≤ (8215838362577553 / 1000000000000000000 : ℝ) := by
  have h438 := v438_bounds x hx0 hx1
  unfold v439
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v440 (x : ℝ) : ℝ := (v439 x) * ((24 : ℝ))

theorem v440_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v440 x ∧ v440 x ≤ (197180120701861273 / 1000000000000000000 : ℝ) := by
  have h439 := v439_bounds x hx0 hx1
  unfold v440
  constructor <;> interval_num

noncomputable def v441 (x : ℝ) : ℝ := (v440 x) * (v405 x)

theorem v441_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v441 x ∧ v441 x ≤ (199607371265852883 / 1000000000000000000 : ℝ) := by
  have h440 := v440_bounds x hx0 hx1
  have h405 := v405_bounds x hx0 hx1
  unfold v441
  constructor <;> interval_num

noncomputable def v442 (x : ℝ) : ℝ := √(v396 x)

theorem v442_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (625350276056847371 / 1000000000000000000 : ℝ) ≤ v442 x ∧ v442 x ≤ (339116499156263409 / 500000000000000000 : ℝ) := by
  have h396 := v396_bounds x hx0 hx1
  unfold v442
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v443 (x : ℝ) : ℝ := (v442 x) * ((512 : ℝ))

theorem v443_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (320179341341105853951 / 1000000000000000000 : ℝ) ≤ v443 x ∧ v443 x ≤ (347255295136013730817 / 1000000000000000000 : ℝ) := by
  have h442 := v442_bounds x hx0 hx1
  unfold v443
  constructor <;> interval_num

noncomputable def v444 (x : ℝ) : ℝ := (v441 x) / (v443 x)

theorem v444_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v444 x ∧ v444 x ≤ (155855910651337 / 250000000000000000 : ℝ) := by
  have h441 := v441_bounds x hx0 hx1
  have h443 := v443_bounds x hx0 hx1
  unfold v444
  constructor <;> interval_num

noncomputable def v445 (x : ℝ) : ℝ := (v0 x) * ((27 / 50 : ℝ))

theorem v445_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v445 x ∧ v445 x ≤ (67500000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v445
  constructor <;> interval_num

noncomputable def v446 (x : ℝ) : ℝ := √(v445 x)

theorem v446_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v446 x ∧ v446 x ≤ (8215838362577553 / 1000000000000000000 : ℝ) := by
  have h445 := v445_bounds x hx0 hx1
  unfold v446
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v447 (x : ℝ) : ℝ := (v446 x) * ((192 : ℝ))

theorem v447_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v447 x ∧ v447 x ≤ (1577440965614890177 / 1000000000000000000 : ℝ) := by
  have h446 := v446_bounds x hx0 hx1
  unfold v447
  constructor <;> interval_num

noncomputable def v448 (x : ℝ) : ℝ := (v405 x) ^ 2

theorem v448_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999991 / 1000000000000000000 : ℝ) ≤ v448 x ∧ v448 x ≤ (1024771159044841457 / 1000000000000000000 : ℝ) := by
  have h405 := v405_bounds x hx0 hx1
  unfold v448
  constructor <;> interval_num

noncomputable def v449 (x : ℝ) : ℝ := (v447 x) * (v448 x)

theorem v449_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v449 x ∧ v449 x ≤ (1616516006657984907 / 1000000000000000000 : ℝ) := by
  have h447 := v447_bounds x hx0 hx1
  have h448 := v448_bounds x hx0 hx1
  unfold v449
  constructor <;> interval_num

end BstLean.Part293.Envelope

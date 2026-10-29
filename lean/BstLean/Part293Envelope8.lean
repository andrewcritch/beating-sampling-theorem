import BstLean.Part293Envelope7

namespace BstLean.Part293.Envelope
open Real

noncomputable def v360 (x : ℝ) : ℝ := (v356 x) + (v359 x)

theorem v360_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v360 x ∧ v360 x ≤ (4942892348897 / 62500000000000000 : ℝ) := by
  have h356 := v356_bounds x hx0 hx1
  have h359 := v359_bounds x hx0 hx1
  unfold v360
  constructor <;> interval_num

noncomputable def v361 (x : ℝ) : ℝ := ((1 : ℝ)) - (v195 x)

theorem v361_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (482796915773097301 / 500000000000000000 : ℝ) ≤ v361 x ∧ v361 x ≤ (200000000000000001 / 200000000000000000 : ℝ) := by
  have h195 := v195_bounds x hx0 hx1
  unfold v361
  constructor <;> interval_num

noncomputable def v362 (x : ℝ) : ℝ := (v360 x) / (v361 x)

theorem v362_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v362 x ∧ v362 x ≤ (16380858078953 / 200000000000000000 : ℝ) := by
  have h360 := v360_bounds x hx0 hx1
  have h361 := v361_bounds x hx0 hx1
  unfold v362
  constructor <;> interval_num

noncomputable def v363 (x : ℝ) : ℝ := (v354 x) + (v362 x)

theorem v363_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v363 x ∧ v363 x ≤ (2429203534280479 / 1000000000000000000 : ℝ) := by
  have h354 := v354_bounds x hx0 hx1
  have h362 := v362_bounds x hx0 hx1
  unfold v363
  constructor <;> interval_num

noncomputable def v364 (x : ℝ) : ℝ := (v346 x) / ((4 : ℝ))

theorem v364_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v364 x ∧ v364 x ≤ (3643276373427 / 1000000000000000000 : ℝ) := by
  have h346 := v346_bounds x hx0 hx1
  unfold v364
  constructor <;> interval_num

noncomputable def v365 (x : ℝ) : ℝ := (v363 x) ^ 3

theorem v365_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v365 x ∧ v365 x ≤ (7167401237 / 500000000000000000 : ℝ) := by
  have h363 := v363_bounds x hx0 hx1
  unfold v365
  constructor <;> interval_num

noncomputable def v366 (x : ℝ) : ℝ := (v365 x) * ((6 : ℝ))

theorem v366_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v366 x ∧ v366 x ≤ (17201762969 / 200000000000000000 : ℝ) := by
  have h365 := v365_bounds x hx0 hx1
  unfold v366
  constructor <;> interval_num

noncomputable def v367 (x : ℝ) : ℝ := (v364 x) + (v366 x)

theorem v367_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v367 x ∧ v367 x ≤ (3729285188273 / 1000000000000000000 : ℝ) := by
  have h364 := v364_bounds x hx0 hx1
  have h366 := v366_bounds x hx0 hx1
  unfold v367
  constructor <;> interval_num

noncomputable def v368 (x : ℝ) : ℝ := √(v367 x)

theorem v368_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v368 x ∧ v368 x ≤ (386227144994911 / 200000000000000000 : ℝ) := by
  have h367 := v367_bounds x hx0 hx1
  unfold v368
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v369 (x : ℝ) : ℝ := √(v47 x)

theorem v369_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (52312612007 / 125000000000000000 : ℝ) ≤ v369 x ∧ v369 x ≤ (341468153713 / 250000000000000000 : ℝ) := by
  have h47 := v47_bounds x hx0 hx1
  unfold v369
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v370 (x : ℝ) : ℝ := (v369 x) / ((1991 / 2000 : ℝ))

theorem v370_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (210196331519 / 500000000000000000 : ℝ) ≤ v370 x ∧ v370 x ≤ (1372046825569 / 1000000000000000000 : ℝ) := by
  have h369 := v369_bounds x hx0 hx1
  unfold v370
  constructor <;> interval_num

noncomputable def v371 (x : ℝ) : ℝ := (v228 x) / ((2 : ℝ))

theorem v371_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v371 x ∧ v371 x ≤ (96044270253239 / 125000000000000000 : ℝ) := by
  have h228 := v228_bounds x hx0 hx1
  unfold v371
  constructor <;> interval_num

noncomputable def v372 (x : ℝ) : ℝ := (v7 x) + ((1 : ℝ))

theorem v372_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v372 x ∧ v372 x ≤ (501313030437500001 / 500000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v372
  constructor <;> interval_num

noncomputable def v373 (x : ℝ) : ℝ := (v372 x) ^ 2

theorem v373_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999997 / 1000000000000000000 : ℝ) ≤ v373 x ∧ v373 x ≤ (1005259017945719211 / 1000000000000000000 : ℝ) := by
  have h372 := v372_bounds x hx0 hx1
  unfold v373
  constructor <;> interval_num

noncomputable def v374 (x : ℝ) : ℝ := (v3 x) ^ 2

theorem v374_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v374 x ∧ v374 x ≤ (7898364572744526401 / 1000000000000000000 : ℝ) := by
  have h3 := v3_bounds x hx0 hx1
  unfold v374
  constructor <;> interval_num

noncomputable def v375 (x : ℝ) : ℝ := (v373 x) * (v374 x)

theorem v375_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v375 x ∧ v375 x ≤ (1587980442754884543 / 200000000000000000 : ℝ) := by
  have h373 := v373_bounds x hx0 hx1
  have h374 := v374_bounds x hx0 hx1
  unfold v375
  constructor <;> interval_num

noncomputable def v376 (x : ℝ) : ℝ := (v375 x) * ((1521 / 500 : ℝ))

theorem v376_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v376 x ∧ v376 x ≤ (24153182534301793901 / 1000000000000000000 : ℝ) := by
  have h375 := v375_bounds x hx0 hx1
  unfold v376
  constructor <;> interval_num

noncomputable def v377 (x : ℝ) : ℝ := (v376 x) * (v0 x)

theorem v377_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v377 x ∧ v377 x ≤ (1509573908393863 / 500000000000000000 : ℝ) := by
  have h376 := v376_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v377
  constructor <;> interval_num

noncomputable def v378 (x : ℝ) : ℝ := (v0 x) * ((9 : ℝ))

theorem v378_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v378 x ∧ v378 x ≤ (1125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v378
  constructor <;> interval_num

noncomputable def v379 (x : ℝ) : ℝ := ((1 : ℝ)) - (v378 x)

theorem v379_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499437499999999999 / 500000000000000000 : ℝ) ≤ v379 x ∧ v379 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h378 := v378_bounds x hx0 hx1
  unfold v379
  constructor <;> interval_num

noncomputable def v380 (x : ℝ) : ℝ := (v379 x) * ((81 / 2500 : ℝ))

theorem v380_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (16181774999999999 / 500000000000000000 : ℝ) ≤ v380 x ∧ v380 x ≤ (16200000000000001 / 500000000000000000 : ℝ) := by
  have h379 := v379_bounds x hx0 hx1
  unfold v380
  constructor <;> interval_num

noncomputable def v381 (x : ℝ) : ℝ := (v377 x) / (v380 x)

theorem v381_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v381 x ∧ v381 x ≤ (93288524181918431 / 1000000000000000000 : ℝ) := by
  have h377 := v377_bounds x hx0 hx1
  have h380 := v380_bounds x hx0 hx1
  unfold v381
  constructor <;> interval_num

noncomputable def v382 (x : ℝ) : ℝ := (v371 x) + (v381 x)

theorem v382_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v382 x ∧ v382 x ≤ (11757109792993043 / 125000000000000000 : ℝ) := by
  have h371 := v371_bounds x hx0 hx1
  have h381 := v381_bounds x hx0 hx1
  unfold v382
  constructor <;> interval_num

noncomputable def v383 (x : ℝ) : ℝ := (v370 x) * (v382 x)

theorem v383_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v383 x ∧ v383 x ≤ (32262610339 / 250000000000000000 : ℝ) := by
  have h370 := v370_bounds x hx0 hx1
  have h382 := v382_bounds x hx0 hx1
  unfold v383
  constructor <;> interval_num

noncomputable def v384 (x : ℝ) : ℝ := √(v383 x)

theorem v384_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v384 x ∧ v384 x ≤ (359235913232517 / 1000000000000000000 : ℝ) := by
  have h383 := v383_bounds x hx0 hx1
  unfold v384
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v385 (x : ℝ) : ℝ := √((23 / 50 : ℝ))

theorem v385_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (678232998312526813 / 1000000000000000000 : ℝ) ≤ v385 x ∧ v385 x ≤ (339116499156263407 / 500000000000000000 : ℝ) := by
  unfold v385
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v386 (x : ℝ) : ℝ := (v0 x) * ((27 / 50 : ℝ))

theorem v386_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v386 x ∧ v386 x ≤ (67500000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v386
  constructor <;> interval_num

noncomputable def v387 (x : ℝ) : ℝ := √(v386 x)

theorem v387_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v387 x ∧ v387 x ≤ (8215838362577553 / 1000000000000000000 : ℝ) := by
  have h386 := v386_bounds x hx0 hx1
  unfold v387
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v388 (x : ℝ) : ℝ := (v387 x) * ((6 : ℝ))

theorem v388_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v388 x ∧ v388 x ≤ (49295030175465319 / 1000000000000000000 : ℝ) := by
  have h387 := v387_bounds x hx0 hx1
  unfold v388
  constructor <;> interval_num

noncomputable def v389 (x : ℝ) : ℝ := (v385 x) - (v388 x)

theorem v389_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (628937968137061493 / 1000000000000000000 : ℝ) ≤ v389 x ∧ v389 x ≤ (135646599662505363 / 200000000000000000 : ℝ) := by
  have h385 := v385_bounds x hx0 hx1
  have h388 := v388_bounds x hx0 hx1
  unfold v389
  constructor <;> interval_num

noncomputable def v390 (x : ℝ) : ℝ := √((27 / 50 : ℝ))

theorem v390_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (734846922834953429 / 1000000000000000000 : ℝ) ≤ v390 x ∧ v390 x ≤ (73484692283495343 / 100000000000000000 : ℝ) := by
  unfold v390
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v391 (x : ℝ) : ℝ := (v0 x) * ((23 / 50 : ℝ))

theorem v391_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v391 x ∧ v391 x ≤ (57500000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v391
  constructor <;> interval_num

noncomputable def v392 (x : ℝ) : ℝ := √(v391 x)

theorem v392_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v392 x ∧ v392 x ≤ (7582875444051617 / 1000000000000000000 : ℝ) := by
  have h391 := v391_bounds x hx0 hx1
  unfold v392
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v393 (x : ℝ) : ℝ := (v392 x) * ((6 : ℝ))

theorem v393_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v393 x ∧ v393 x ≤ (45497252664309703 / 1000000000000000000 : ℝ) := by
  have h392 := v392_bounds x hx0 hx1
  unfold v393
  constructor <;> interval_num

noncomputable def v394 (x : ℝ) : ℝ := (v390 x) + (v393 x)

theorem v394_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (183711730708738357 / 250000000000000000 : ℝ) ≤ v394 x ∧ v394 x ≤ (390172087749631567 / 500000000000000000 : ℝ) := by
  have h390 := v390_bounds x hx0 hx1
  have h393 := v393_bounds x hx0 hx1
  unfold v394
  constructor <;> interval_num

noncomputable def v395 (x : ℝ) : ℝ := (v394 x) ^ 2

theorem v395_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134999999999999999 / 250000000000000000 : ℝ) ≤ v395 x ∧ v395 x ≤ (38058564514726549 / 62500000000000000 : ℝ) := by
  have h394 := v394_bounds x hx0 hx1
  unfold v395
  constructor <;> interval_num

noncomputable def v396 (x : ℝ) : ℝ := ((1 : ℝ)) - (v395 x)

theorem v396_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (78212593552875043 / 200000000000000000 : ℝ) ≤ v396 x ∧ v396 x ≤ (92000000000000001 / 200000000000000000 : ℝ) := by
  have h395 := v395_bounds x hx0 hx1
  unfold v396
  constructor <;> interval_num

noncomputable def v397 (x : ℝ) : ℝ := (v389 x) ^ 2

theorem v397_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (24722685485273461 / 62500000000000000 : ℝ) ≤ v397 x ∧ v397 x ≤ (460000000000000003 / 1000000000000000000 : ℝ) := by
  have h389 := v389_bounds x hx0 hx1
  unfold v397
  constructor <;> interval_num

noncomputable def v398 (x : ℝ) : ℝ := ((1 : ℝ)) - (v397 x)

theorem v398_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134999999999999999 / 250000000000000000 : ℝ) ≤ v398 x ∧ v398 x ≤ (4835496257884997 / 8000000000000000 : ℝ) := by
  have h397 := v397_bounds x hx0 hx1
  unfold v398
  constructor <;> interval_num

noncomputable def v399 (x : ℝ) : ℝ := √(v0 x)

theorem v399_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v399 x ∧ v399 x ≤ (11180339887498949 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v399
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v400 (x : ℝ) : ℝ := (v399 x) + ((1 : ℝ))

theorem v400_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v400 x ∧ v400 x ≤ (20223606797749979 / 20000000000000000 : ℝ) := by
  have h399 := v399_bounds x hx0 hx1
  unfold v400
  constructor <;> interval_num

noncomputable def v401 (x : ℝ) : ℝ := (v0 x) * ((6 : ℝ))

theorem v401_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v401 x ∧ v401 x ≤ (750000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v401
  constructor <;> interval_num

noncomputable def v402 (x : ℝ) : ℝ := (v400 x) + (v401 x)

theorem v402_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499999999999999999 / 500000000000000000 : ℝ) ≤ v402 x ∧ v402 x ≤ (126491292485937369 / 125000000000000000 : ℝ) := by
  have h400 := v400_bounds x hx0 hx1
  have h401 := v401_bounds x hx0 hx1
  unfold v402
  constructor <;> interval_num

noncomputable def v403 (x : ℝ) : ℝ := (v0 x) * ((3 : ℝ))

theorem v403_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v403 x ∧ v403 x ≤ (375000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v403
  constructor <;> interval_num

noncomputable def v404 (x : ℝ) : ℝ := (v403 x) + ((1 : ℝ))

theorem v404_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v404 x ∧ v404 x ≤ (500187500000000001 / 500000000000000000 : ℝ) := by
  have h403 := v403_bounds x hx0 hx1
  unfold v404
  constructor <;> interval_num

end BstLean.Part293.Envelope

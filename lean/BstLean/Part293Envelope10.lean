import BstLean.Part293Envelope9

namespace BstLean.Part293.Envelope
open Real

noncomputable def v450 (x : ℝ) : ℝ := √(v396 x)

theorem v450_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (625350276056847371 / 1000000000000000000 : ℝ) ≤ v450 x ∧ v450 x ≤ (339116499156263409 / 500000000000000000 : ℝ) := by
  have h396 := v396_bounds x hx0 hx1
  unfold v450
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v451 (x : ℝ) : ℝ := (v450 x) * ((512 : ℝ))

theorem v451_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (320179341341105853951 / 1000000000000000000 : ℝ) ≤ v451 x ∧ v451 x ≤ (347255295136013730817 / 1000000000000000000 : ℝ) := by
  have h450 := v450_bounds x hx0 hx1
  unfold v451
  constructor <;> interval_num

noncomputable def v452 (x : ℝ) : ℝ := (v449 x) / (v451 x)

theorem v452_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v452 x ∧ v452 x ≤ (2524391486169959 / 500000000000000000 : ℝ) := by
  have h449 := v449_bounds x hx0 hx1
  have h451 := v451_bounds x hx0 hx1
  unfold v452
  constructor <;> interval_num

noncomputable def v453 (x : ℝ) : ℝ := (v421 x) + ((236328823 / 5000000000 : ℝ))

theorem v453_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (47265764599999999 / 1000000000000000000 : ℝ) ≤ v453 x ∧ v453 x ≤ (50608426910873581 / 1000000000000000000 : ℝ) := by
  have h421 := v421_bounds x hx0 hx1
  unfold v453
  constructor <;> interval_num

noncomputable def v454 (x : ℝ) : ℝ := (v453 x) + (v444 x)

theorem v454_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (23632882299999999 / 500000000000000000 : ℝ) ≤ v454 x ∧ v454 x ≤ (5123185055347893 / 100000000000000000 : ℝ) := by
  have h453 := v453_bounds x hx0 hx1
  have h444 := v444_bounds x hx0 hx1
  unfold v454
  constructor <;> interval_num

noncomputable def v455 (x : ℝ) : ℝ := (v437 x) + ((107887269 / 625000000 : ℝ))

theorem v455_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (172619630399999999 / 1000000000000000000 : ℝ) ≤ v455 x ∧ v455 x ≤ (1751111522683231 / 10000000000000000 : ℝ) := by
  have h437 := v437_bounds x hx0 hx1
  unfold v455
  constructor <;> interval_num

noncomputable def v456 (x : ℝ) : ℝ := (v455 x) + (v452 x)

theorem v456_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (86309815199999999 / 500000000000000000 : ℝ) ≤ v456 x ∧ v456 x ≤ (180159935240663019 / 1000000000000000000 : ℝ) := by
  have h455 := v455_bounds x hx0 hx1
  have h452 := v452_bounds x hx0 hx1
  unfold v456
  constructor <;> interval_num

noncomputable def v457 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v457_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v457 x ∧ v457 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v457
  constructor <;> interval_num

noncomputable def v458 (x : ℝ) : ℝ := √(v457 x)

theorem v458_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v458 x ∧ v458 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h457 := v457_bounds x hx0 hx1
  unfold v458
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v459 (x : ℝ) : ℝ := (v3 x) * (v458 x)

theorem v459_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v459 x ∧ v459 x ≤ (5193830657870867 / 500000000000000000 : ℝ) := by
  have h3 := v3_bounds x hx0 hx1
  have h458 := v458_bounds x hx0 hx1
  unfold v459
  constructor <;> interval_num

noncomputable def v460 (x : ℝ) : ℝ := (v11 x) + (v459 x)

theorem v460_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (841289486443281303 / 1000000000000000000 : ℝ) ≤ v460 x ∧ v460 x ≤ (854271709379027663 / 1000000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  have h459 := v459_bounds x hx0 hx1
  unfold v460
  constructor <;> interval_num

noncomputable def v461 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v461_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v461 x ∧ v461 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v461
  constructor <;> interval_num

noncomputable def v462 (x : ℝ) : ℝ := √(v461 x)

theorem v462_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v462 x ∧ v462 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h461 := v461_bounds x hx0 hx1
  unfold v462
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v463 (x : ℝ) : ℝ := (v6 x) * (v462 x)

theorem v463_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v463 x ∧ v463 x ≤ (8749961757921843 / 500000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  have h462 := v462_bounds x hx0 hx1
  unfold v463
  constructor <;> interval_num

noncomputable def v464 (x : ℝ) : ℝ := (v11 x) + (v463 x)

theorem v464_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (841289486443281303 / 1000000000000000000 : ℝ) ≤ v464 x ∧ v464 x ≤ (172276794315825923 / 200000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  have h463 := v463_bounds x hx0 hx1
  unfold v464
  constructor <;> interval_num

noncomputable def v465 (x : ℝ) : ℝ := (v0 x) * ((1521 / 500 : ℝ))

theorem v465_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v465 x ∧ v465 x ≤ (380250000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v465
  constructor <;> interval_num

noncomputable def v466 (x : ℝ) : ℝ := (v0 x) * ((3 : ℝ))

theorem v466_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v466 x ∧ v466 x ≤ (375000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v466
  constructor <;> interval_num

noncomputable def v467 (x : ℝ) : ℝ := ((1 : ℝ)) - (v466 x)

theorem v467_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499812499999999999 / 500000000000000000 : ℝ) ≤ v467 x ∧ v467 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h466 := v466_bounds x hx0 hx1
  unfold v467
  constructor <;> interval_num

noncomputable def v468 (x : ℝ) : ℝ := (v465 x) / (v467 x)

theorem v468_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v468 x ∧ v468 x ≤ (380392647242719 / 1000000000000000000 : ℝ) := by
  have h465 := v465_bounds x hx0 hx1
  have h467 := v467_bounds x hx0 hx1
  unfold v468
  constructor <;> interval_num

noncomputable def v469 (x : ℝ) : ℝ := (v460 x) * ((2 : ℝ))

theorem v469_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (336515794577312521 / 200000000000000000 : ℝ) ≤ v469 x ∧ v469 x ≤ (1708543418758055327 / 1000000000000000000 : ℝ) := by
  have h460 := v460_bounds x hx0 hx1
  unfold v469
  constructor <;> interval_num

noncomputable def v470 (x : ℝ) : ℝ := (v469 x) * (v454 x)

theorem v470_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (39764190826683023 / 500000000000000000 : ℝ) ≤ v470 x ∧ v470 x ≤ (43765920546971331 / 500000000000000000 : ℝ) := by
  have h469 := v469_bounds x hx0 hx1
  have h454 := v454_bounds x hx0 hx1
  unfold v470
  constructor <;> interval_num

noncomputable def v471 (x : ℝ) : ℝ := (v456 x) + (v470 x)

theorem v471_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (252148012053366043 / 1000000000000000000 : ℝ) ≤ v471 x ∧ v471 x ≤ (133845888167302841 / 500000000000000000 : ℝ) := by
  have h456 := v456_bounds x hx0 hx1
  have h470 := v470_bounds x hx0 hx1
  unfold v471
  constructor <;> interval_num

noncomputable def v472 (x : ℝ) : ℝ := (v454 x) ^ 2

theorem v472_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2234052503222611 / 1000000000000000000 : ℝ) ≤ v472 x ∧ v472 x ≤ (2624702511134001 / 1000000000000000000 : ℝ) := by
  have h454 := v454_bounds x hx0 hx1
  unfold v472
  constructor <;> interval_num

noncomputable def v473 (x : ℝ) : ℝ := (v472 x) * (v0 x)

theorem v473_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v473 x ∧ v473 x ≤ (328087813893 / 1000000000000000000 : ℝ) := by
  have h472 := v472_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v473
  constructor <;> interval_num

noncomputable def v474 (x : ℝ) : ℝ := (v471 x) + (v473 x)

theorem v474_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (126074006026683021 / 500000000000000000 : ℝ) ≤ v474 x ∧ v474 x ≤ (33461513052802447 / 125000000000000000 : ℝ) := by
  have h471 := v471_bounds x hx0 hx1
  have h473 := v473_bounds x hx0 hx1
  unfold v474
  constructor <;> interval_num

noncomputable def v475 (x : ℝ) : ℝ := (v474 x) * (v189 x)

theorem v475_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (431417524523950211 / 500000000000000000 : ℝ) ≤ v475 x ∧ v475 x ≤ (996046147218111329 / 1000000000000000000 : ℝ) := by
  have h474 := v474_bounds x hx0 hx1
  have h189 := v189_bounds x hx0 hx1
  unfold v475
  constructor <;> interval_num

noncomputable def v476 (x : ℝ) : ℝ := (v468 x) / ((17919 / 100000 : ℝ))

theorem v476_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v476 x ∧ v476 x ≤ (2122845288479933 / 1000000000000000000 : ℝ) := by
  have h468 := v468_bounds x hx0 hx1
  unfold v476
  constructor <;> interval_num

noncomputable def v477 (x : ℝ) : ℝ := (v475 x) + (v476 x)

theorem v477_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (862835049047900421 / 1000000000000000000 : ℝ) ≤ v477 x ∧ v477 x ≤ (998168992506591263 / 1000000000000000000 : ℝ) := by
  have h475 := v475_bounds x hx0 hx1
  have h476 := v476_bounds x hx0 hx1
  unfold v477
  constructor <;> interval_num

noncomputable def v478 (x : ℝ) : ℝ := (v32 x) * (v189 x)

theorem v478_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3421938733608913383 / 1000000000000000000 : ℝ) ≤ v478 x ∧ v478 x ≤ (2010122208845823621 / 500000000000000000 : ℝ) := by
  have h32 := v32_bounds x hx0 hx1
  have h189 := v189_bounds x hx0 hx1
  unfold v478
  constructor <;> interval_num

noncomputable def v479 (x : ℝ) : ℝ := (v478 x) / ((493 / 125 : ℝ))

theorem v479_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (433815762374355143 / 500000000000000000 : ℝ) ≤ v479 x ∧ v479 x ≤ (127416468613452309 / 125000000000000000 : ℝ) := by
  have h478 := v478_bounds x hx0 hx1
  unfold v479
  constructor <;> interval_num

noncomputable def v480 (x : ℝ) : ℝ := (v454 x) ^ 2

theorem v480_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2234052503222611 / 1000000000000000000 : ℝ) ≤ v480 x ∧ v480 x ≤ (2624702511134001 / 1000000000000000000 : ℝ) := by
  have h454 := v454_bounds x hx0 hx1
  unfold v480
  constructor <;> interval_num

noncomputable def v481 (x : ℝ) : ℝ := (v479 x) * (v480 x)

theorem v481_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (387666875947941 / 200000000000000000 : ℝ) ≤ v481 x ∧ v481 x ≤ (2675442601036441 / 1000000000000000000 : ℝ) := by
  have h479 := v479_bounds x hx0 hx1
  have h480 := v480_bounds x hx0 hx1
  unfold v481
  constructor <;> interval_num

noncomputable def v482 (x : ℝ) : ℝ := (v477 x) ^ 2

theorem v482_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (186121080466373181 / 250000000000000000 : ℝ) ≤ v482 x ∧ v482 x ≤ (498170668800811723 / 500000000000000000 : ℝ) := by
  have h477 := v477_bounds x hx0 hx1
  unfold v482
  constructor <;> interval_num

noncomputable def v483 (x : ℝ) : ℝ := (v482 x) / ((972 / 125 : ℝ))

theorem v483_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (47870648268100097 / 500000000000000000 : ℝ) ≤ v483 x ∧ v483 x ≤ (64065158024795747 / 500000000000000000 : ℝ) := by
  have h482 := v482_bounds x hx0 hx1
  unfold v483
  constructor <;> interval_num

noncomputable def v484 (x : ℝ) : ℝ := (v481 x) + (v483 x)

theorem v484_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (48839815457969949 / 500000000000000000 : ℝ) ≤ v484 x ∧ v484 x ≤ (4087679957832123 / 31250000000000000 : ℝ) := by
  have h481 := v481_bounds x hx0 hx1
  have h483 := v483_bounds x hx0 hx1
  unfold v484
  constructor <;> interval_num

noncomputable def v485 (x : ℝ) : ℝ := (v484 x) * (v0 x)

theorem v485_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v485 x ∧ v485 x ≤ (1635071983133 / 100000000000000000 : ℝ) := by
  have h484 := v484_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v485
  constructor <;> interval_num

noncomputable def v486 (x : ℝ) : ℝ := (v405 x) ^ 2

theorem v486_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999991 / 1000000000000000000 : ℝ) ≤ v486 x ∧ v486 x ≤ (1024771159044841457 / 1000000000000000000 : ℝ) := by
  have h405 := v405_bounds x hx0 hx1
  unfold v486
  constructor <;> interval_num

noncomputable def v487 (x : ℝ) : ℝ := (v486 x) * ((32 : ℝ))

theorem v487_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (31999999999999999711 / 1000000000000000000 : ℝ) ≤ v487 x ∧ v487 x ≤ (262341416715479413 / 8000000000000000 : ℝ) := by
  have h486 := v486_bounds x hx0 hx1
  unfold v487
  constructor <;> interval_num

noncomputable def v488 (x : ℝ) : ℝ := (v487 x) * (v0 x)

theorem v488_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v488 x ∧ v488 x ≤ (4099084636179367 / 1000000000000000000 : ℝ) := by
  have h487 := v487_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v488
  constructor <;> interval_num

noncomputable def v489 (x : ℝ) : ℝ := (v0 x) * ((2 : ℝ))

theorem v489_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v489 x ∧ v489 x ≤ (250000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v489
  constructor <;> interval_num

noncomputable def v490 (x : ℝ) : ℝ := ((1 : ℝ)) - (v489 x)

theorem v490_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499874999999999999 / 500000000000000000 : ℝ) ≤ v490 x ∧ v490 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h489 := v489_bounds x hx0 hx1
  unfold v490
  constructor <;> interval_num

noncomputable def v491 (x : ℝ) : ℝ := (v488 x) / (v490 x)

theorem v491_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v491 x ∧ v491 x ≤ (4100109663595267 / 1000000000000000000 : ℝ) := by
  have h488 := v488_bounds x hx0 hx1
  have h490 := v490_bounds x hx0 hx1
  unfold v491
  constructor <;> interval_num

noncomputable def v492 (x : ℝ) : ℝ := (v491 x) / ((17919 / 100000 : ℝ))

theorem v492_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v492 x ∧ v492 x ≤ (4576270621792809 / 200000000000000000 : ℝ) := by
  have h491 := v491_bounds x hx0 hx1
  unfold v492
  constructor <;> interval_num

noncomputable def v493 (x : ℝ) : ℝ := ((7 / 250 : ℝ)) - (v492 x)

theorem v493_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2559323445517977 / 500000000000000000 : ℝ) ≤ v493 x ∧ v493 x ≤ (28000000000000001 / 1000000000000000000 : ℝ) := by
  have h492 := v492_bounds x hx0 hx1
  unfold v493
  constructor <;> interval_num

noncomputable def v494 (x : ℝ) : ℝ := (v464 x) * ((2 : ℝ))

theorem v494_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (336515794577312521 / 200000000000000000 : ℝ) ≤ v494 x ∧ v494 x ≤ (1722767943158259231 / 1000000000000000000 : ℝ) := by
  have h464 := v464_bounds x hx0 hx1
  unfold v494
  constructor <;> interval_num

end BstLean.Part293.Envelope

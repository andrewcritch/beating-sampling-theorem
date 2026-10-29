import BstLean.Part290Mean

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part228 BstLean.Part250
open BstLean.Part271.R3 (angularMomentCore angularMomentCore_formula j2Core j4Core
  jbCore aCore bCore offsetCore ba1Core ba2Core traceCore diagonalCore covariancePaymentCore normCore)
theorem tracepay {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (traceCore (2*n) (mW n)) (79999999944087866196568947/1000000000000000) (80000000069888857064778217/1000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v16 : ℝ := 3
  have h16 : Bounds v16 3 3 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v60 : ℝ := 8
  have h60 : Bounds v60 8 8 := Bounds.point _
  let v382 : ℝ := (1/100000)
  have h382 : Bounds v382 (1/100000) (1/100000) := Bounds.point _
  let v463 : ℝ := -(1/(mW n : ℝ))
  have h463 : Bounds v463 (-1/45793280000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (inverse_width ha)
  let v464 : ℝ := v0+v463
  have h464 : Bounds v464 (99999999999997816273479427/100000000000000000000000000) 1 := Bounds.add h0 h463 (by norm_num)
  let v465 : ℝ := v464*v12
  have h465 : Bounds v465 (99999999999997816273479427/50000000000000000000000000) 2 := Bounds.mul h464 h12 (by norm_num)
  let v466 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))*v12
  have h466 : Bounds v466 0 (34939624329159212880143113/50000000000000000000000000000000000) := Bounds.mul (dimension_width ha) h12 (by norm_num)
  let v467 : ℝ := (1/(mW n : ℝ))*v41
  have h467 : Bounds v467 0 (131023591234347048300536673/1000000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h41 (by norm_num)
  let v468 : ℝ := v466+v467
  have h468 : Bounds v468 0 (698923510174418604651162797/1000000000000000000000000000000000000) := Bounds.add h466 h467 (by norm_num)
  let v469 : ℝ := v465*v468
  have h469 : Bounds v469 0 (1747308775436046511627907/1250000000000000000000000000000000) := Bounds.mul h465 h468 (by norm_num)
  let v470 : ℝ := -(1/(mW n : ℝ))
  have h470 : Bounds v470 (-1/45793280000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (inverse_width ha)
  let v471 : ℝ := v0+v470
  have h471 : Bounds v471 (99999999999997816273479427/100000000000000000000000000) 1 := Bounds.add h0 h470 (by norm_num)
  let v472 : ℝ := v471*v60
  have h472 : Bounds v472 (99999999999997816273479427/12500000000000000000000000) 8 := Bounds.mul h471 h60 (by norm_num)
  let v473 : ℝ := (1/(mW n : ℝ))*v12
  have h473 : Bounds v473 0 (43674530411449016100178891/1000000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h12 (by norm_num)
  let v474 : ℝ := -v473
  have h474 : Bounds v474 (-43674530411449016100178891/1000000000000000000000000000000000000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h473
  let v475 : ℝ := v0+v474
  have h475 : Bounds v475 (19999999999999126509391771/20000000000000000000000000) 1 := Bounds.add h0 h474 (by norm_num)
  let v476 : ℝ := v472*v475
  have h476 : Bounds v476 (127999999999991614490161/16000000000000000000000) 8 := Bounds.mul h472 h475 (by norm_num)
  let v477 : ℝ := v469+v476
  have h477 : Bounds v477 (127999999999991614490161/16000000000000000000000) (80000000013978470203488373/10000000000000000000000000) := Bounds.add h469 h476 (by norm_num)
  let v478 : ℝ := (1/(mW n : ℝ))*v12
  have h478 : Bounds v478 0 (43674530411449016100178891/1000000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h12 (by norm_num)
  let v479 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))+v478
  have h479 : Bounds v479 0 (34943991782200357781753131/100000000000000000000000000000000000) := Bounds.add (dimension_width ha) h478 (by norm_num)
  let v480 : ℝ := v479*v60
  have h480 : Bounds v480 0 (34943991782200357781753131/12500000000000000000000000000000000) := Bounds.mul h479 h60 (by norm_num)
  let v481 : ℝ := (1/(mW n : ℝ))*v16
  have h481 : Bounds v481 0 (65511795617173524150268337/1000000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h16 (by norm_num)
  let v482 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))+v481
  have h482 : Bounds v482 0 (1747308775436046511627907/5000000000000000000000000000000000) := Bounds.add (dimension_width ha) h481 (by norm_num)
  let v483 : ℝ := v480*v482
  have h483 : Bounds v483 0 (48846354791843023743343597/50000000000000000000000000000000000000000000) := Bounds.mul h480 h482 (by norm_num)
  let v484 : ℝ := v477+v483
  have h484 : Bounds v484 (127999999999991614490161/16000000000000000000000) (20000000003494617553314411/2500000000000000000000000) := Bounds.add h477 h483 (by norm_num)
  let v485 : ℝ := -(1/(mW n : ℝ))
  have h485 : Bounds v485 (-1/45793280000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (inverse_width ha)
  let v486 : ℝ := v0+v485
  have h486 : Bounds v486 (99999999999997816273479427/100000000000000000000000000) 1 := Bounds.add h0 h485 (by norm_num)
  let v487 : ℝ := 16
  have h487 : Bounds v487 16 16 := Bounds.point _
  let v488 : ℝ := v486*v487
  have h488 : Bounds v488 (159999999999996506037567083/10000000000000000000000000) 16 := Bounds.mul h486 h487 (by norm_num)
  let v489 : ℝ := (1/(mW n : ℝ))*v12
  have h489 : Bounds v489 0 (43674530411449016100178891/1000000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h12 (by norm_num)
  let v490 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))+v489
  have h490 : Bounds v490 0 (34943991782200357781753131/100000000000000000000000000000000000) := Bounds.add (dimension_width ha) h489 (by norm_num)
  let v491 : ℝ := v488*v490
  have h491 : Bounds v491 0 (5591038685152057245080501/1000000000000000000000000000000000) := Bounds.mul h488 h490 (by norm_num)
  let v492 : ℝ := v484+v491
  have h492 : Bounds v492 (127999999999991614490161/16000000000000000000000) (160000000139777714129556433/20000000000000000000000000) := Bounds.add h484 h491 (by norm_num)
  let v493 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))+v0
  have h493 : Bounds v493 1 (100000000034939624329159213/100000000000000000000000000) := Bounds.add (dimension_width ha) h0 (by norm_num)
  let v494 : ℝ := v493+(1/(mW n : ℝ))
  have h494 : Bounds v494 1 (50000000017470904027839893/50000000000000000000000000) := Bounds.add h493 (inverse_width ha) (by norm_num)
  let v495 : ℝ := v382*v494
  have h495 : Bounds v495 (1/100000) (50000000017470904027839893/5000000000000000000000000000000) := Bounds.mul h382 h494 (by norm_num)
  let v496 : ℝ := v495^2
  have h496 : Bounds v496 (1/10000000000) (12500000008735452015446109/125000000000000000000000000000000000) := Bounds.pow h495 2 (by norm_num)
  let v497 : ℝ := 1/v496
  have h497 : Bounds v497 (3999999997204655357010733/400000000000000) 10000000000 := Bounds.inv h496 (by norm_num)
  let v498 : ℝ := v492/v496
  have h498 : Bounds v498 (79999999944087866196568947/1000000000000000) (80000000069888857064778217/1000000000000000) := bounds_div h492 h497 (by norm_num)
  convert h498 using 1 <;>
    simp only [v0, v12, v16, v41, v60, v382, v463, v464, v465, v466, v467, v468, v469, v470, v471, v472, v473, v474, v475, v476, v477, v478, v479, v480, v481, v482, v483, v484, v485, v486, v487, v488, v489, v490, v491, v492, v493, v494, v495, v496, v498, traceCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem diagpay {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (diagonalCore (2*n)) (99987501562304711911011123/12500000000000000000) 8001500 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v16 : ℝ := 3
  have h16 : Bounds v16 3 3 := Bounds.point _
  let v60 : ℝ := 8
  have h60 : Bounds v60 8 8 := Bounds.point _
  let v397 : ℝ := (1/1000)
  have h397 : Bounds v397 (1/1000) (1/1000) := Bounds.point _
  let v499 : ℝ := (1/((2*n : ℕ) : ℝ))*v16
  have h499 : Bounds v499 0 (3/16000) := Bounds.mul (inverse_dimension ha) h16 (by norm_num)
  let v500 : ℝ := v499+v0
  have h500 : Bounds v500 1 (16003/16000) := Bounds.add h499 h0 (by norm_num)
  let v501 : ℝ := v500*v60
  have h501 : Bounds v501 8 (16003/2000) := Bounds.mul h500 h60 (by norm_num)
  let v502 : ℝ := v397^2
  have h502 : Bounds v502 (1/1000000) (1/1000000) := Bounds.pow h397 2 (by norm_num)
  let v503 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h503 : Bounds v503 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v504 : ℝ := v503+v0
  have h504 : Bounds v504 1 (8001/8000) := Bounds.add h503 h0 (by norm_num)
  let v505 : ℝ := v502*v504
  have h505 : Bounds v505 (1/1000000) (8001/8000000000) := Bounds.mul h502 h504 (by norm_num)
  let v506 : ℝ := 1/v505
  have h506 : Bounds v506 (99987501562304711911011123/100000000000000000000) 1000000 := Bounds.inv h505 (by norm_num)
  let v507 : ℝ := v501/v505
  have h507 : Bounds v507 (99987501562304711911011123/12500000000000000000) 8001500 := bounds_div h501 h506 (by norm_num)
  convert h507 using 1 <;>
    simp only [v0, v12, v16, v60, v397, v499, v500, v501, v502, v503, v504, v505, v507, diagonalCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem covpay {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (covariancePaymentCore (2*n) (mW n)) (187846671979759357367991647/1000000000000000000) (188168350597519213547118293/1000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v397 : ℝ := (1/1000)
  have h397 : Bounds v397 (1/1000) (1/1000) := Bounds.point _
  let v508 : ℝ := (1/(mW n : ℝ))*v12
  have h508 : Bounds v508 0 (43674530411449016100178891/1000000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h12 (by norm_num)
  let v509 : ℝ := v508+v25
  have h509 : Bounds v509 4 (80000000000000873490608229/20000000000000000000000000) := Bounds.add h508 h25 (by norm_num)
  let v510 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h510 : Bounds v510 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v511 : ℝ := v510+v0
  have h511 : Bounds v511 1 (8001/8000) := Bounds.add h510 h0 (by norm_num)
  let v512 : ℝ := v511*v25
  have h512 : Bounds v512 4 (8001/2000) := Bounds.mul h511 h25 (by norm_num)
  let v513 : ℝ := v512^2
  have h513 : Bounds v513 16 (64016001/4000000) := Bounds.pow h512 2 (by norm_num)
  let v514 : ℝ := v509*v513
  have h514 : Bounds v514 64 (8002000125000087370899453/125000000000000000000000) := Bounds.mul h509 h513 (by norm_num)
  let v515 : ℝ := v514*(j4Core (2*n))
  have h515 : Bounds v515 (15069864264320214089182693/31250000000000000000000000) (241376088338237100317748709/500000000000000000000000000) := Bounds.mul h514 (jfourth ha) (by norm_num)
  let v516 : ℝ := v397*v25
  have h516 : Bounds v516 (1/250) (1/250) := Bounds.mul h397 h25 (by norm_num)
  let v517 : ℝ := -(1/(mW n : ℝ))
  have h517 : Bounds v517 (-1/45793280000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (inverse_width ha)
  let v518 : ℝ := v0+v517
  have h518 : Bounds v518 (99999999999997816273479427/100000000000000000000000000) 1 := Bounds.add h0 h517 (by norm_num)
  let v519 : ℝ := v516*v518
  have h519 : Bounds v519 (99999999999997816273479427/25000000000000000000000000000) (1/250) := Bounds.mul h516 h518 (by norm_num)
  let v520 : ℝ := v519*(j2Core (2*n))
  have h520 : Bounds v520 (25325547073705265065221263/500000000000000000000000000000) (63334146143300287050519261/1250000000000000000000000000000) := Bounds.mul h519 (jsecond ha) (by norm_num)
  let v521 : ℝ := v520^2
  have h521 : Bounds v521 (32069166729123065727295221/12500000000000000000000000000000000) (128358850166429395978686873/50000000000000000000000000000000000) := Bounds.pow h520 2 (by norm_num)
  let v522 : ℝ := 1/v521
  have h522 : Bounds v522 (38953293781589869686037687/100000000000000000) (9744562515127917726287301/25000000000000000) := Bounds.inv h521 (by norm_num)
  let v523 : ℝ := v515/v521
  have h523 : Bounds v523 (187846671979759357367991647/1000000000000000000) (188168350597519213547118293/1000000000000000000) := bounds_div h515 h522 (by norm_num)
  convert h523 using 1 <;>
    simp only [v0, v12, v25, v397, v508, v509, v510, v511, v512, v513, v514, v515, v516, v517, v518, v519, v520, v521, v523, covariancePaymentCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem normpay {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (normCore (2*n)) (28813044080374392078921129/500000000000000000000000000) (74891115235498223400299/1250000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v16 : ℝ := 3
  have h16 : Bounds v16 3 3 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v418 : ℝ := 5
  have h418 : Bounds v418 5 5 := Bounds.point _
  let v524 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h524 : Bounds v524 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v525 : ℝ := v524+v0
  have h525 : Bounds v525 1 (8001/8000) := Bounds.add h524 h0 (by norm_num)
  let v526 : ℝ := v525*v25
  have h526 : Bounds v526 4 (8001/2000) := Bounds.mul h525 h25 (by norm_num)
  let v527 : ℝ := v526^2
  have h527 : Bounds v527 16 (64016001/4000000) := Bounds.pow h526 2 (by norm_num)
  let v528 : ℝ := v527*v12
  have h528 : Bounds v528 32 (64016001/2000000) := Bounds.mul h527 h12 (by norm_num)
  let v529 : ℝ := v528*(jbCore (2*n))
  have h529 : Bounds v529 (32414674590421191088786271/2500000000000000000000000) (134797267307778111920367673/10000000000000000000000000) := Bounds.mul h528 (jnorm ha) (by norm_num)
  let v530 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h530 : Bounds v530 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v531 : ℝ := -v530
  have h531 : Bounds v531 (-1/8000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h530
  let v532 : ℝ := v418+v531
  have h532 : Bounds v532 (39999/8000) 5 := Bounds.add h418 h531 (by norm_num)
  let v533 : ℝ := v532*v16
  have h533 : Bounds v533 (119997/8000) 15 := Bounds.mul h532 h16 (by norm_num)
  let v534 : ℝ := v533^2
  have h534 : Bounds v534 (14399280009/64000000) 225 := Bounds.pow h533 2 (by norm_num)
  let v535 : ℝ := 1/v534
  have h535 : Bounds v535 (11111111111111111111111111/2500000000000000000000000000) (27779166718751736165366211/6250000000000000000000000000) := Bounds.inv h534 (by norm_num)
  let v536 : ℝ := v529/v534
  have h536 : Bounds v536 (28813044080374392078921129/500000000000000000000000000) (74891115235498223400299/1250000000000000000000000) := bounds_div h529 h535 (by norm_num)
  convert h536 using 1 <;>
    simp only [v0, v12, v16, v25, v418, v524, v525, v526, v527, v528, v529, v530, v531, v532, v533, v534, v536, normCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem endpoint {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (endpointPolynomial (firstRatio (2*n))) (409436776727639818460833/2000000000000000000000000) (102366918560841583810417203/500000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v16 : ℝ := 3
  have h16 : Bounds v16 3 3 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v537 : ℝ := 1/v12
  have h537 : Bounds v537 (1/2) (1/2) := Bounds.inv h12 (by norm_num)
  let v538 : ℝ := π/v12
  have h538 : Bounds v538 (157079632679489661923/100000000000000000000) (314159265358979323847/200000000000000000000) := bounds_div pi_bounds h537 (by norm_num)
  let v539 : ℝ := firstRatio (2*n)^3
  have h539 : Bounds v539 (80628836082998722955152519/2500000000000000000000000000) (4031819787654794959148213/125000000000000000000000000) := Bounds.pow (ratio_window_reduced ha) 3 (by norm_num)
  let v540 : ℝ := 1/v41
  have h540 : Bounds v540 (8333333333333333333333333/50000000000000000000000000) (16666666666666666666666667/100000000000000000000000000) := Bounds.inv h41 (by norm_num)
  let v541 : ℝ := v539/v41
  have h541 : Bounds v541 (107505114777331630606870021/20000000000000000000000000000) (268787985843652997276547539/50000000000000000000000000000) := bounds_div h539 h540 (by norm_num)
  let v542 : ℝ := firstRatio (2*n)+v541
  have h542 : Bounds v542 (323685141922657253060343501/1000000000000000000000000000) (4046194921460913249319137/12500000000000000000000000) := Bounds.add (ratio_window_reduced ha) h541 (by norm_num)
  let v543 : ℝ := firstRatio (2*n)^5
  have h543 : Bounds v543 (81694091076334636805738579/25000000000000000000000000000) (8170685738733958206259683/2500000000000000000000000000) := Bounds.pow (ratio_window_reduced ha) 5 (by norm_num)
  let v544 : ℝ := v543*v16
  have h544 : Bounds v544 (49016454645800782083443147/5000000000000000000000000000) (24512057216201874618779049/2500000000000000000000000000) := Bounds.mul h543 h16 (by norm_num)
  let v545 : ℝ := 40
  have h545 : Bounds v545 40 40 := Bounds.point _
  let v546 : ℝ := 1/v545
  have h546 : Bounds v546 (1/40) (1/40) := Bounds.inv h545 (by norm_num)
  let v547 : ℝ := v544/v545
  have h547 : Bounds v547 (49016454645800782083443147/200000000000000000000000000000) (24512057216201874618779049/100000000000000000000000000000) := bounds_div h544 h546 (by norm_num)
  let v548 : ℝ := v542+v547
  have h548 : Bounds v548 (80982556048971564242690179/250000000000000000000000000) (323940714289035078691718751/1000000000000000000000000000) := Bounds.add h542 h547 (by norm_num)
  let v549 : ℝ := -v548
  have h549 : Bounds v549 (-323940714289035078691718751/1000000000000000000000000000) (-80982556048971564242690179/250000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h548
  let v550 : ℝ := v538+v549
  have h550 : Bounds v550 (31171390312646538513457031/25000000000000000000000000) (124686610259901036226423929/100000000000000000000000000) := Bounds.add h538 h549 (by norm_num)
  let v551 : ℝ := firstRatio (2*n)^2
  have h551 : Bounds v551 (50660591821168885719467251/500000000000000000000000000) (25331879179446889/250000000000000000) := Bounds.pow (ratio_window_reduced ha) 2 (by norm_num)
  let v552 : ℝ := -v551
  have h552 : Bounds v552 (-25331879179446889/250000000000000000) (-50660591821168885719467251/500000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h551
  let v553 : ℝ := v0+v552
  have h553 : Bounds v553 (224668120820553111/250000000000000000) (1797357632715324457122131/2000000000000000000000000) := Bounds.add h0 h552 (by norm_num)
  let v554 : ℝ := Real.sqrt v553
  have h554 : Bounds v554 (18959667542256245417131121/20000000000000000000000000) (94798671739516594798706941/100000000000000000000000000) := Bounds.sqrt h553 (by norm_num)
  let v555 : ℝ := -v554
  have h555 : Bounds v555 (-94798671739516594798706941/100000000000000000000000000) (-18959667542256245417131121/20000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h554
  let v556 : ℝ := v550+v555
  have h556 : Bounds v556 (29886889511069559255121183/100000000000000000000000000) (7472068137154952285192081/25000000000000000000000000) := Bounds.add h550 h555 (by norm_num)
  let v557 : ℝ := 1/π
  have h557 : Bounds v557 (15915494309189533576851107/50000000000000000000000000) (159154943091895335769017679/500000000000000000000000000) := Bounds.inv pi_bounds (by norm_num)
  let v558 : ℝ := v556/π
  have h558 : Bounds v558 (47566461993280393189800631/500000000000000000000000000) (19027465266362573175524771/200000000000000000000000000) := bounds_div h556 h557 (by norm_num)
  let v559 : ℝ := -firstRatio (2*n)
  have h559 : Bounds v559 (-159159917/500000000) (-31830988618379067153/100000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (ratio_window_reduced ha)
  let v560 : ℝ := v0+v559
  have h560 : Bounds v560 (340840083/500000000) (68169011381620932847/100000000000000000000) := Bounds.add h0 h559 (by norm_num)
  let v561 : ℝ := v560^2
  have h561 : Bounds v561 (116171962179446889/250000000000000000) (464701411274756428378934503/1000000000000000000000000000) := Bounds.pow h560 2 (by norm_num)
  let v562 : ℝ := 1/v561
  have h562 : Bounds v562 (21519194384558180326478007/10000000000000000000000000) (215198224519814411773434497/100000000000000000000000000) := Bounds.inv h561 (by norm_num)
  let v563 : ℝ := v558/v561
  have h563 : Bounds v563 (409436776727639818460833/2000000000000000000000000) (102366918560841583810417203/500000000000000000000000000) := bounds_div h558 h562 (by norm_num)
  convert h563 using 1 <;>
    simp only [v0, v12, v16, v41, v538, v539, v541, v542, v543, v544, v545, v547, v548, v549, v550, v551, v552, v553, v554, v555, v556, v558, v559, v560, v561, v563, endpointPolynomial, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

end BstLean.Part290

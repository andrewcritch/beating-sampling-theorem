import BstLean.Part290Angular

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part228 BstLean.Part250
open BstLean.Part271.R3 (angularMomentCore angularMomentCore_formula j2Core j4Core
  jbCore aCore bCore offsetCore ba1Core ba2Core traceCore diagonalCore covariancePaymentCore normCore)
theorem frob {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (frobCore (2*n) (mW n)) (12500062499843750781245117/25000000000000000000000000) (12544639581924376370937237/25000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v382 : ℝ := (1/100000)
  have h382 : Bounds v382 (1/100000) (1/100000) := Bounds.point _
  let v383 : ℝ := v382+v0
  have h383 : Bounds v383 (100001/100000) (100001/100000) := Bounds.add h382 h0 (by norm_num)
  let v384 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))+v0
  have h384 : Bounds v384 1 (100000000034939624329159213/100000000000000000000000000) := Bounds.add (dimension_width ha) h0 (by norm_num)
  let v385 : ℝ := v384+(1/(mW n : ℝ))
  have h385 : Bounds v385 1 (50000000017470904027839893/50000000000000000000000000) := Bounds.add h384 (inverse_width ha) (by norm_num)
  let v386 : ℝ := v383*v385
  have h386 : Bounds v386 (100001/100000) (100001000034942157473760343/100000000000000000000000000) := Bounds.mul h383 h385 (by norm_num)
  let v387 : ℝ := 1/v25
  have h387 : Bounds v387 (1/4) (1/4) := Bounds.inv h25 (by norm_num)
  let v388 : ℝ := v386/v25
  have h388 : Bounds v388 (100001/400000) (12500125004367769684220043/50000000000000000000000000) := bounds_div h386 h387 (by norm_num)
  let v389 : ℝ := Real.sqrt v388
  have h389 : Bounds v389 (12500062499843750781245117/25000000000000000000000000) (3125015625506906175955513/6250000000000000000000000) := Bounds.sqrt h388 (by norm_num)
  let v390 : ℝ := (1/4)
  have h390 : Bounds v390 (1/4) (1/4) := Bounds.point _
  let v391 : ℝ := 1/v12
  have h391 : Bounds v391 (1/2) (1/2) := Bounds.inv h12 (by norm_num)
  let v392 : ℝ := firstRatio (2*n)/v12
  have h392 : Bounds v392 (31830988618379067153/200000000000000000000) (159159917/1000000000) := bounds_div (ratio_window_reduced ha) h391 (by norm_num)
  let v393 : ℝ := -v392
  have h393 : Bounds v393 (-159159917/1000000000) (-31830988618379067153/200000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h392
  let v394 : ℝ := v390+v393
  have h394 : Bounds v394 (90840083/1000000000) (18169011381620932847/200000000000000000000) := Bounds.add h390 h393 (by norm_num)
  let v395 : ℝ := v394^2
  have h395 : Bounds v395 (8251920679446889/1000000000000000000) (644751903487248045096377/78125000000000000000000000) := Bounds.pow h394 2 (by norm_num)
  let v396 : ℝ := v395*v25
  have h396 : Bounds v396 (8251920679446889/250000000000000000) (644751903487248045096377/19531250000000000000000000) := Bounds.mul h395 h25 (by norm_num)
  let v397 : ℝ := (1/1000)
  have h397 : Bounds v397 (1/1000) (1/1000) := Bounds.point _
  let v398 : ℝ := v397+v0
  have h398 : Bounds v398 (1001/1000) (1001/1000) := Bounds.add h397 h0 (by norm_num)
  let v399 : ℝ := v396*v398
  have h399 : Bounds v399 (8260172600126335889/250000000000000000000) (33044308756005647008843437/1000000000000000000000000000) := Bounds.mul h396 h398 (by norm_num)
  let v400 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h400 : Bounds v400 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v401 : ℝ := v400+v0
  have h401 : Bounds v401 1 (8001/8000) := Bounds.add h400 h0 (by norm_num)
  let v402 : ℝ := v399*v401
  have h402 : Bounds v402 (8260172600126335889/250000000000000000000) (33048439294600147714719543/1000000000000000000000000000) := Bounds.mul h399 h401 (by norm_num)
  let v403 : ℝ := v402*(((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have h403 : Bounds v403 0 (115470005361835265662453681/10000000000000000000000000000000000000) := Bounds.mul h402 (dimension_width ha) (by norm_num)
  let v404 : ℝ := (1/250)
  have h404 : Bounds v404 (1/250) (1/250) := Bounds.point _
  let v405 : ℝ := v404+v0
  have h405 : Bounds v405 (251/250) (251/250) := Bounds.add h404 h0 (by norm_num)
  let v406 : ℝ := v405*v25
  have h406 : Bounds v406 (502/125) (502/125) := Bounds.mul h405 h25 (by norm_num)
  let v407 : ℝ := -(1/(mW n : ℝ))
  have h407 : Bounds v407 (-1/45793280000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (inverse_width ha)
  let v408 : ℝ := v0+v407
  have h408 : Bounds v408 (99999999999997816273479427/100000000000000000000000000) 1 := Bounds.add h0 h407 (by norm_num)
  let v409 : ℝ := v406*v408
  have h409 : Bounds v409 (40159999999999123015429337/10000000000000000000000000) (502/125) := Bounds.mul h406 h408 (by norm_num)
  let v410 : ℝ := v409*(j2Core (2*n))
  have h410 : Bounds v410 (508536985240001722509642959/10000000000000000000000000000) (50869986182298790558977071/1000000000000000000000000000) := Bounds.mul h409 (jsecond ha) (by norm_num)
  let v411 : ℝ := v410*(1/((2*n : ℕ) : ℝ))
  have h411 : Bounds v411 0 (158968706819683720496803347/50000000000000000000000000000000) := Bounds.mul h410 (inverse_dimension ha) (by norm_num)
  let v412 : ℝ := v403+v411
  have h412 : Bounds v412 0 (317938568339421059346263319/100000000000000000000000000000000) := Bounds.add h403 h411 (by norm_num)
  let v413 : ℝ := Real.sqrt v412
  have h413 : Bounds v413 0 (89154159793503334230369677/50000000000000000000000000000) := Bounds.sqrt h412 (by norm_num)
  let v414 : ℝ := v389+v413
  have h414 : Bounds v414 (12500062499843750781245117/25000000000000000000000000) (12544639581924376370937237/25000000000000000000000000) := Bounds.add h389 h413 (by norm_num)
  convert h414 using 1 <;>
    simp only [v0, v12, v25, v382, v383, v384, v385, v386, v388, v389, v390, v392, v393, v394, v395, v396, v397, v398, v399, v400, v401, v402, v403, v404, v405, v406, v407, v408, v409, v410, v411, v412, v413, v414, frobCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem nu {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (nuCore (2*n) (mW n)) 0 (13863108886318539354478993/100000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v82 : ℝ := 10
  have h82 : Bounds v82 10 10 := Bounds.point _
  let v397 : ℝ := (1/1000)
  have h397 : Bounds v397 (1/1000) (1/1000) := Bounds.point _
  let v415 : ℝ := v397+v0
  have h415 : Bounds v415 (1001/1000) (1001/1000) := Bounds.add h397 h0 (by norm_num)
  let v416 : ℝ := v415+v82
  have h416 : Bounds v416 (11001/1000) (11001/1000) := Bounds.add h415 h82 (by norm_num)
  let v417 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h417 : Bounds v417 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v418 : ℝ := 5
  have h418 : Bounds v418 5 5 := Bounds.point _
  let v419 : ℝ := -v417
  have h419 : Bounds v419 (-1/8000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h417
  let v420 : ℝ := v418+v419
  have h420 : Bounds v420 (39999/8000) 5 := Bounds.add h418 h419 (by norm_num)
  let v421 : ℝ := v416*v420
  have h421 : Bounds v421 (440028999/8000000) (11001/200) := Bounds.mul h416 h420 (by norm_num)
  let v422 : ℝ := v421*(((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have h422 : Bounds v422 0 (120115877264087656529517/6250000000000000000000000000000) := Bounds.mul h421 (dimension_width ha) (by norm_num)
  let v423 : ℝ := Real.sqrt v422
  have h423 : Bounds v423 0 (138630950232096530359396371/1000000000000000000000000000000) := Bounds.sqrt h422 (by norm_num)
  let v424 : ℝ := (1/1000000)
  have h424 : Bounds v424 (1/1000000) (1/1000000) := Bounds.point _
  let v425 : ℝ := -v424
  have h425 : Bounds v425 (-1/1000000) (-1/1000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h424
  let v426 : ℝ := v0+v425
  have h426 : Bounds v426 (999999/1000000) (999999/1000000) := Bounds.add h0 h425 (by norm_num)
  let v427 : ℝ := 1/v426
  have h427 : Bounds v427 (1000001000001000001000001/1000000000000000000000000) (10000010000010000010000011/10000000000000000000000000) := Bounds.inv h426 (by norm_num)
  let v428 : ℝ := v423/v426
  have h428 : Bounds v428 0 (13863108886318539354478993/100000000000000000000000000000) := bounds_div h423 h427 (by norm_num)
  convert h428 using 1 <;>
    simp only [v0, v12, v82, v397, v415, v416, v417, v418, v419, v420, v421, v422, v423, v424, v425, v426, v428, nuCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem tvalue {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (tCore (2*n) (mW n)) (6250075000143750212500281/25000000000000000000000000) (253305815877014014634830213/1000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v424 : ℝ := (1/1000000)
  have h424 : Bounds v424 (1/1000000) (1/1000000) := Bounds.point _
  let v429 : ℝ := (frobCore (2*n) (mW n))^2
  have h429 : Bounds v429 (25000249999999999999999999/100000000000000000000000000) (6294719289615351695322211/25000000000000000000000000) := Bounds.pow (frob ha) 2 (by norm_num)
  let v430 : ℝ := firstRatio (2*n)*v12
  have h430 : Bounds v430 (31830988618379067153/50000000000000000000) (159159917/250000000) := Bounds.mul (ratio_window_reduced ha) h12 (by norm_num)
  let v431 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h431 : Bounds v431 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v432 : ℝ := v431+v0
  have h432 : Bounds v432 1 (8001/8000) := Bounds.add h431 h0 (by norm_num)
  let v433 : ℝ := v430*v432
  have h433 : Bounds v433 (31830988618379067153/50000000000000000000) (1273438495917/2000000000000) := Bounds.mul h430 h432 (by norm_num)
  let v434 : ℝ := -firstRatio (2*n)
  have h434 : Bounds v434 (-159159917/500000000) (-31830988618379067153/100000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (ratio_window_reduced ha)
  let v435 : ℝ := v0+v434
  have h435 : Bounds v435 (340840083/500000000) (68169011381620932847/100000000000000000000) := Bounds.add h0 h434 (by norm_num)
  let v436 : ℝ := v433*v435
  have h436 : Bounds v436 (21698553605320753147782187/50000000000000000000000000) (27127826038112567131914419/62500000000000000000000000) := Bounds.mul h433 h435 (by norm_num)
  let v437 : ℝ := v436*(((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have h437 : Bounds v437 0 (151653768102149860978949123/1000000000000000000000000000000000000) := Bounds.mul h436 (dimension_width ha) (by norm_num)
  let v438 : ℝ := (1/10000000)
  have h438 : Bounds v438 (1/10000000) (1/10000000) := Bounds.point _
  let v439 : ℝ := 1/v438
  have h439 : Bounds v439 10000000 10000000 := Bounds.inv h438 (by norm_num)
  let v440 : ℝ := v437/v438
  have h440 : Bounds v440 0 (151653768102149860978949123/100000000000000000000000000000) := bounds_div h437 h439 (by norm_num)
  let v441 : ℝ := v429+v440
  have h441 : Bounds v441 (25000249999999999999999999/100000000000000000000000000) (63326327316408891605669483/250000000000000000000000000) := Bounds.add h429 h440 (by norm_num)
  let v442 : ℝ := -v424
  have h442 : Bounds v442 (-1/1000000) (-1/1000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h424
  let v443 : ℝ := v0+v442
  have h443 : Bounds v443 (999999/1000000) (999999/1000000) := Bounds.add h0 h442 (by norm_num)
  let v444 : ℝ := v443^2
  have h444 : Bounds v444 (999998000001/1000000000000) (999998000001/1000000000000) := Bounds.pow h443 2 (by norm_num)
  let v445 : ℝ := 1/v444
  have h445 : Bounds v445 (200000400000600000800001/200000000000000000000000) (10000020000030000040000051/10000000000000000000000000) := Bounds.inv h444 (by norm_num)
  let v446 : ℝ := v441/v444
  have h446 : Bounds v446 (6250075000143750212500281/25000000000000000000000000) (253305815877014014634830213/1000000000000000000000000000) := bounds_div h441 h445 (by norm_num)
  convert h446 using 1 <;>
    simp only [v0, v12, v424, v429, v430, v431, v432, v433, v434, v435, v436, v437, v438, v440, v441, v442, v443, v444, v446, tCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem meanvalue {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (meanCore (2*n) (mW n)) (51185614221177256740292299/1000000000000000000000000000) (521405781618943098294971193/10000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v447 : ℝ := (10237/50000)
  have h447 : Bounds v447 (10237/50000) (10237/50000) := Bounds.point _
  let v448 : ℝ := Real.sqrt (tCore (2*n) (mW n))
  have h448 : Bounds v448 (250001499998375013999916339/500000000000000000000000000) (251647479560701151201124833/500000000000000000000000000) := Bounds.sqrt (tvalue ha) (by norm_num)
  let v449 : ℝ := Real.sqrt v12
  have h449 : Bounds v449 (17677669529663688110021109/12500000000000000000000000) (141421356237309504880168873/100000000000000000000000000) := Bounds.sqrt h12 (by norm_num)
  let v450 : ℝ := v449*(nuCore (2*n) (mW n))
  have h450 : Bounds v450 0 (7842158641474660757447623/40000000000000000000000000000) := Bounds.mul h449 (nu ha) (by norm_num)
  let v451 : ℝ := v448+v450
  have h451 : Bounds v451 (50000299999675002799983267/100000000000000000000000000) (25174550654371958446059293/50000000000000000000000000) := Bounds.add h448 h450 (by norm_num)
  let v452 : ℝ := v451^2
  have h452 : Bounds v452 (250003000005750008500011231/1000000000000000000000000000) (12675160012990792023982879/50000000000000000000000000) := Bounds.pow h451 2 (by norm_num)
  let v453 : ℝ := v447*v452
  have h453 : Bounds v453 (51185614221177256740292299/1000000000000000000000000000) (51902245221194695179805093/1000000000000000000000000000) := Bounds.mul h447 h452 (by norm_num)
  let v454 : ℝ := (nuCore (2*n) (mW n))^2
  have h454 : Bounds v454 0 (192185787993924052507338331/10000000000000000000000000000000000) := Bounds.pow (nu ha) 2 (by norm_num)
  let v455 : ℝ := v454*v41
  have h455 : Bounds v455 0 (115311472796354431504402999/1000000000000000000000000000000000) := Bounds.mul h454 h41 (by norm_num)
  let v456 : ℝ := v453+v455
  have h456 : Bounds v456 (51185614221177256740292299/1000000000000000000000000000) (20760944213066996613694639/400000000000000000000000000) := Bounds.add h453 h455 (by norm_num)
  let v457 : ℝ := Real.sqrt v12
  have h457 : Bounds v457 (17677669529663688110021109/12500000000000000000000000) (141421356237309504880168873/100000000000000000000000000) := Bounds.sqrt h12 (by norm_num)
  let v458 : ℝ := v457+v12
  have h458 : Bounds v458 (42677669529663688110021109/12500000000000000000000000) (341421356237309504880168873/100000000000000000000000000) := Bounds.add h457 h12 (by norm_num)
  let v459 : ℝ := v458*(nuCore (2*n) (mW n))
  have h459 : Bounds v459 0 (94663228752647461205154087/200000000000000000000000000000) := Bounds.mul h458 (nu ha) (by norm_num)
  let v460 : ℝ := Real.sqrt (tCore (2*n) (mW n))
  have h460 : Bounds v460 (250001499998375013999916339/500000000000000000000000000) (251647479560701151201124833/500000000000000000000000000) := Bounds.sqrt (tvalue ha) (by norm_num)
  let v461 : ℝ := v459*v460
  have h461 : Bounds v461 0 (238217629226818295260521797/1000000000000000000000000000000) := Bounds.mul h459 h460 (by norm_num)
  let v462 : ℝ := v456+v461
  have h462 : Bounds v462 (51185614221177256740292299/1000000000000000000000000000) (521405781618943098294971193/10000000000000000000000000000) := Bounds.add h456 h461 (by norm_num)
  convert h462 using 1 <;>
    simp only [v12, v41, v447, v448, v449, v450, v451, v452, v453, v454, v455, v456, v457, v458, v459, v460, v461, v462, meanCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

end BstLean.Part290

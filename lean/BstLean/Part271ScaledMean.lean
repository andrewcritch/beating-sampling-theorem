import BstLean.Part271ScaledAngular

namespace BstLean.Part271.R3.Band
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part228 BstLean.Part250
theorem frob {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (frobCore (2*n) (mW n)) (50125357305416064107857187/100000000000000000000000000) (501698377107224717466157273/1000000000000000000000000000) := by
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
  have h384 : Bounds v384 1 (20000000001988706941193159/20000000000000000000000000) := Bounds.add (dimension_width ha) h0 (by norm_num)
  let v385 : ℝ := v384+(1/(mW n : ℝ))
  have h385 : Bounds v385 1 (100000000009943910643005719/100000000000000000000000000) := Bounds.add h384 (inverse_width ha) (by norm_num)
  let v386 : ℝ := v383*v385
  have h386 : Bounds v386 (100001/100000) (2000020000198880201642243/2000000000000000000000000) := Bounds.mul h383 h385 (by norm_num)
  let v387 : ℝ := 1/v25
  have h387 : Bounds v387 (1/4) (1/4) := Bounds.inv h25 (by norm_num)
  let v388 : ℝ := v386/v25
  have h388 : Bounds v388 (100001/400000) (12500125001243001260264019/50000000000000000000000000) := bounds_div h386 h387 (by norm_num)
  let v389 : ℝ := Real.sqrt v388
  have h389 : Bounds v389 (12500062499843750781245117/25000000000000000000000000) (1562507812558156037985229/3125000000000000000000000) := Bounds.sqrt h388 (by norm_num)
  let v390 : ℝ := (1/4)
  have h390 : Bounds v390 (1/4) (1/4) := Bounds.point _
  let v391 : ℝ := 1/v12
  have h391 : Bounds v391 (1/2) (1/2) := Bounds.inv h12 (by norm_num)
  let v392 : ℝ := firstRatio (2*n)/v12
  have h392 : Bounds v392 (4973591971621729242765971/31250000000000000000000000) (159160960519514220994764173/1000000000000000000000000000) := bounds_div (ratio_window_reduced ha) h391 (by norm_num)
  let v393 : ℝ := -v392
  have h393 : Bounds v393 (-159160960519514220994764173/1000000000000000000000000000) (-4973591971621729242765971/31250000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h392
  let v394 : ℝ := v390+v393
  have h394 : Bounds v394 (90839039480485779005235827/1000000000000000000000000000) (2838908028378270757234029/31250000000000000000000000) := Bounds.add h390 h393 (by norm_num)
  let v395 : ℝ := v394^2
  have h395 : Bounds v395 (825173109373725406687058081/100000000000000000000000000000) (16505648729273549953191397/2000000000000000000000000000) := Bounds.pow h394 2 (by norm_num)
  let v396 : ℝ := v395*v25
  have h396 : Bounds v396 (5157331933585783791794113/156250000000000000000000000) (16505648729273549953191397/500000000000000000000000000) := Bounds.mul h395 h25 (by norm_num)
  let v397 : ℝ := (1/1000)
  have h397 : Bounds v397 (1/1000) (1/1000) := Bounds.point _
  let v398 : ℝ := v397+v0
  have h398 : Bounds v398 (1001/1000) (1001/1000) := Bounds.add h397 h0 (by norm_num)
  let v399 : ℝ := v396*v398
  have h399 : Bounds v399 (66079862598647930567499611/2000000000000000000000000000) (33044308756005647006289177/1000000000000000000000000000) := Bounds.mul h396 h398 (by norm_num)
  let v400 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h400 : Bounds v400 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.mul (inverse_dimension ha hb) h12 (by norm_num)
  let v401 : ℝ := v400+v0
  have h401 : Bounds v401 (2500154330514229273411939/2500000000000000000000000) (5000378071833648393194707/5000000000000000000000000) := Bounds.add h400 h0 (by norm_num)
  let v402 : ℝ := v399*v401
  have h402 : Bounds v402 (33041970927158975097027399/1000000000000000000000000000) (33046807380486252348217819/1000000000000000000000000000) := Bounds.mul h399 h401 (by norm_num)
  let v403 : ℝ := v402*(((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have h403 : Bounds v403 0 (328602076109231616507377003/100000000000000000000000000000000000000) := Bounds.mul h402 (dimension_width ha) (by norm_num)
  let v404 : ℝ := v397+v0
  have h404 : Bounds v404 (1001/1000) (1001/1000) := Bounds.add h397 h0 (by norm_num)
  let v405 : ℝ := v404*v25
  have h405 : Bounds v405 (1001/250) (1001/250) := Bounds.mul h404 h25 (by norm_num)
  let v406 : ℝ := -(1/(mW n : ℝ))
  have h406 : Bounds v406 (-1/266001988046875) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (inverse_width ha)
  let v407 : ℝ := v0+v406
  have h407 : Bounds v407 (24999999999999906015740019/25000000000000000000000000) 1 := Bounds.add h0 h406 (by norm_num)
  let v408 : ℝ := v405*v407
  have h408 : Bounds v408 (20019999999999924737404607/5000000000000000000000000) (1001/250) := Bounds.mul h405 h407 (by norm_num)
  let v409 : ℝ := v408*(j2Core (2*n))
  have h409 : Bounds v409 (50708824832914517898914187/1000000000000000000000000000) (38035044635756645710707589/500000000000000000000000000) := Bounds.mul h408 (jsecond ha hb) (by norm_num)
  let v410 : ℝ := v409*(1/((2*n : ℕ) : ℝ))
  have h410 : Bounds v410 (31303676049703387801045859/20000000000000000000000000000000) (143799790683389964879801849/50000000000000000000000000000000) := Bounds.mul h409 (inverse_dimension ha hb) (by norm_num)
  let v411 : ℝ := v403+v410
  have h411 : Bounds v411 (31303676049703387801045859/20000000000000000000000000000000) (143799954984428019495610103/50000000000000000000000000000000) := Bounds.add h403 h410 (by norm_num)
  let v412 : ℝ := Real.sqrt v411
  have h412 : Bounds v412 (62553653020530491438359573/50000000000000000000000000000) (21198463607684816386049911/12500000000000000000000000000) := Bounds.sqrt h411 (by norm_num)
  let v413 : ℝ := v389+v412
  have h413 : Bounds v413 (50125357305416064107857187/100000000000000000000000000) (501698377107224717466157273/1000000000000000000000000000) := Bounds.add h389 h412 (by norm_num)
  convert h413 using 1 <;>
    simp only [v0, v12, v25, v382, v383, v384, v385, v386, v388, v389, v390, v392, v393, v394, v395, v396, v397, v398, v399, v400, v401, v402, v403, v404, v405, v406, v407, v408, v409, v410, v411, v412, v413, frobCore, Nat.cast_mul, Nat.cast_ofNat] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
        Nat.choose] <;> ring <;> simp

theorem nu {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (nuCore (2*n) (mW n)) 0 (223001319317957582653833213/5000000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v16 : ℝ := 3
  have h16 : Bounds v16 3 3 := Bounds.point _
  let v397 : ℝ := (1/1000)
  have h397 : Bounds v397 (1/1000) (1/1000) := Bounds.point _
  let v414 : ℝ := v397+v0
  have h414 : Bounds v414 (1001/1000) (1001/1000) := Bounds.add h397 h0 (by norm_num)
  let v415 : ℝ := v414+v16
  have h415 : Bounds v415 (4001/1000) (4001/1000) := Bounds.add h414 h16 (by norm_num)
  let v416 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h416 : Bounds v416 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.mul (inverse_dimension ha hb) h12 (by norm_num)
  let v417 : ℝ := 5
  have h417 : Bounds v417 5 5 := Bounds.point _
  let v418 : ℝ := -v416
  have h418 : Bounds v418 (-37807183364839319470699433/500000000000000000000000000000) (-7716525711463670596950429/125000000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h416
  let v419 : ℝ := v417+v418
  have h419 : Bounds v419 (24999621928166351606805293/5000000000000000000000000) (12499845669485770726588061/2500000000000000000000000) := Bounds.add h417 h418 (by norm_num)
  let v420 : ℝ := v415*v419
  have h420 : Bounds v420 (4000939493383742911153119/200000000000000000000000) (200047530094450274708315329/10000000000000000000000000) := Bounds.mul h415 h419 (by norm_num)
  let v421 : ℝ := v420*(((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have h421 : Bounds v421 0 (777023264975352753529121/390625000000000000000000000000000) := Bounds.mul h420 (dimension_width ha) (by norm_num)
  let v422 : ℝ := Real.sqrt v421
  have h422 : Bounds v422 0 (446002192633276529392501073/10000000000000000000000000000000) := Bounds.sqrt h421 (by norm_num)
  let v423 : ℝ := (1/1000000)
  have h423 : Bounds v423 (1/1000000) (1/1000000) := Bounds.point _
  let v424 : ℝ := -v423
  have h424 : Bounds v424 (-1/1000000) (-1/1000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h423
  let v425 : ℝ := v0+v424
  have h425 : Bounds v425 (999999/1000000) (999999/1000000) := Bounds.add h0 h424 (by norm_num)
  let v426 : ℝ := 1/v425
  have h426 : Bounds v426 (1000001000001000001000001/1000000000000000000000000) (10000010000010000010000011/10000000000000000000000000) := Bounds.inv h425 (by norm_num)
  let v427 : ℝ := v422/v425
  have h427 : Bounds v427 0 (223001319317957582653833213/5000000000000000000000000000000) := bounds_div h422 h426 (by norm_num)
  convert h427 using 1 <;>
    simp only [v0, v12, v16, v397, v414, v415, v416, v417, v418, v419, v420, v421, v422, v423, v424, v425, v427, nuCore, Nat.cast_mul, Nat.cast_ofNat] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
        Nat.choose] <;> ring <;> simp

theorem tvalue {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (tCore (2*n) (mW n)) (125627823505302762140090387/500000000000000000000000000) (126066670871831970754776533/500000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v423 : ℝ := (1/1000000)
  have h423 : Bounds v423 (1/1000000) (1/1000000) := Bounds.point _
  let v428 : ℝ := (frobCore (2*n) (mW n))^2
  have h428 : Bounds v428 (125627572249781379358071411/500000000000000000000000000) (251701261592023062465606453/1000000000000000000000000000) := Bounds.pow (frob ha hb) 2 (by norm_num)
  let v429 : ℝ := firstRatio (2*n)*v12
  have h429 : Bounds v429 (63661977236758134307404429/100000000000000000000000000) (6366438420780568839790567/10000000000000000000000000) := Bounds.mul (ratio_window_reduced ha) h12 (by norm_num)
  let v430 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h430 : Bounds v430 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.mul (inverse_dimension ha hb) h12 (by norm_num)
  let v431 : ℝ := v430+v0
  have h431 : Bounds v431 (2500154330514229273411939/2500000000000000000000000) (5000378071833648393194707/5000000000000000000000000) := Bounds.add h430 h0 (by norm_num)
  let v432 : ℝ := v429*v431
  have h432 : Bounds v432 (63665907231031654779921707/100000000000000000000000000) (31834599074950398289251433/50000000000000000000000000) := Bounds.mul h429 h431 (by norm_num)
  let v433 : ℝ := -firstRatio (2*n)
  have h433 : Bounds v433 (-1322500000000000000000000/4154599204739822068201427) (-100000000000000000000/314159265358979323847) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (ratio_window_reduced ha)
  let v434 : ℝ := v0+v433
  have h434 : Bounds v434 (13633561579219431160209433/20000000000000000000000000) (34084505690810466423148893/50000000000000000000000000) := Bounds.add h0 h433 (by norm_num)
  let v435 : ℝ := v432*v434
  have h435 : Bounds v435 (86799306673114172902982369/200000000000000000000000000) (21701331466696329212048217/50000000000000000000000000) := Bounds.mul h432 h434 (by norm_num)
  let v436 : ℝ := v435*(((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have h436 : Bounds v436 0 (43157588520952505780723181/1000000000000000000000000000000000000) := Bounds.mul h435 (dimension_width ha) (by norm_num)
  let v437 : ℝ := (1/10000000)
  have h437 : Bounds v437 (1/10000000) (1/10000000) := Bounds.point _
  let v438 : ℝ := 1/v437
  have h438 : Bounds v438 10000000 10000000 := Bounds.inv h437 (by norm_num)
  let v439 : ℝ := v436/v437
  have h439 : Bounds v439 0 (43157588520952505780723181/100000000000000000000000000000) := bounds_div h436 h438 (by norm_num)
  let v440 : ℝ := v428+v439
  have h440 : Bounds v440 (12562757224978137935807141/50000000000000000000000000) (50426567495446517504682737/200000000000000000000000000) := Bounds.add h428 h439 (by norm_num)
  let v441 : ℝ := -v423
  have h441 : Bounds v441 (-1/1000000) (-1/1000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h423
  let v442 : ℝ := v0+v441
  have h442 : Bounds v442 (999999/1000000) (999999/1000000) := Bounds.add h0 h441 (by norm_num)
  let v443 : ℝ := v442^2
  have h443 : Bounds v443 (999998000001/1000000000000) (999998000001/1000000000000) := Bounds.pow h442 2 (by norm_num)
  let v444 : ℝ := 1/v443
  have h444 : Bounds v444 (200000400000600000800001/200000000000000000000000) (10000020000030000040000051/10000000000000000000000000) := Bounds.inv h443 (by norm_num)
  let v445 : ℝ := v440/v443
  have h445 : Bounds v445 (125627823505302762140090387/500000000000000000000000000) (126066670871831970754776533/500000000000000000000000000) := bounds_div h440 h444 (by norm_num)
  convert h445 using 1 <;>
    simp only [v0, v12, v423, v428, v429, v430, v431, v432, v433, v434, v435, v436, v437, v439, v440, v441, v442, v443, v445, tCore, Nat.cast_mul, Nat.cast_ofNat] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
        Nat.choose] <;> ring <;> simp

theorem meanvalue {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (meanCore (2*n) (mW n)) (51442081168951375041124211/1000000000000000000000000000) (25855611764619858450076827/500000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v446 : ℝ := (10237/50000)
  have h446 : Bounds v446 (10237/50000) (10237/50000) := Bounds.point _
  let v447 : ℝ := Real.sqrt (tCore (2*n) (mW n))
  have h447 : Bounds v447 (25062703715411747465676059/50000000000000000000000000) (50212880991202241662036183/100000000000000000000000000) := Bounds.sqrt (tvalue ha hb) (by norm_num)
  let v448 : ℝ := Real.sqrt v12
  have h448 : Bounds v448 (17677669529663688110021109/12500000000000000000000000) (141421356237309504880168873/100000000000000000000000000) := Bounds.sqrt h12 (by norm_num)
  let v449 : ℝ := v448*(nuCore (2*n) (mW n))
  have h449 : Bounds v449 0 (7884287255163722291089031/125000000000000000000000000000) := Bounds.mul h448 (nu ha hb) (by norm_num)
  let v450 : ℝ := v447+v449
  have h450 : Bounds v450 (25062703715411747465676059/50000000000000000000000000) (502191884210063726398690543/1000000000000000000000000000) := Bounds.add h447 h449 (by norm_num)
  let v451 : ℝ := v450^2
  have h451 : Bounds v451 (251255647010605524280180773/1000000000000000000000000000) (252196688566454053084564647/1000000000000000000000000000) := Bounds.pow h450 2 (by norm_num)
  let v452 : ℝ := v446*v451
  have h452 : Bounds v452 (51442081168951375041124211/1000000000000000000000000000) (25817375008547901414266883/500000000000000000000000000) := Bounds.mul h446 h451 (by norm_num)
  let v453 : ℝ := (nuCore (2*n) (mW n))^2
  have h453 : Bounds v453 0 (198918353670198726947238713/100000000000000000000000000000000000) := Bounds.pow (nu ha hb) 2 (by norm_num)
  let v454 : ℝ := v453*v41
  have h454 : Bounds v454 0 (29837753050529809042085807/2500000000000000000000000000000000) := Bounds.mul h453 h41 (by norm_num)
  let v455 : ℝ := v452+v454
  have h455 : Bounds v455 (51442081168951375041124211/1000000000000000000000000000) (51634761952197023040457383/1000000000000000000000000000) := Bounds.add h452 h454 (by norm_num)
  let v456 : ℝ := Real.sqrt v12
  have h456 : Bounds v456 (17677669529663688110021109/12500000000000000000000000) (141421356237309504880168873/100000000000000000000000000) := Bounds.sqrt h12 (by norm_num)
  let v457 : ℝ := v456+v12
  have h457 : Bounds v457 (42677669529663688110021109/12500000000000000000000000) (341421356237309504880168873/100000000000000000000000000) := Bounds.add h456 h12 (by norm_num)
  let v458 : ℝ := v457*(nuCore (2*n) (mW n))
  have h458 : Bounds v458 0 (152274825768492811390245533/1000000000000000000000000000000) := Bounds.mul h457 (nu ha hb) (by norm_num)
  let v459 : ℝ := Real.sqrt (tCore (2*n) (mW n))
  have h459 : Bounds v459 (25062703715411747465676059/50000000000000000000000000) (50212880991202241662036183/100000000000000000000000000) := Bounds.sqrt (tvalue ha hb) (by norm_num)
  let v460 : ℝ := v458*v459
  have h460 : Bounds v460 0 (764615770426938596962709839/10000000000000000000000000000000) := Bounds.mul h458 h459 (by norm_num)
  let v461 : ℝ := v455+v460
  have h461 : Bounds v461 (51442081168951375041124211/1000000000000000000000000000) (25855611764619858450076827/500000000000000000000000000) := Bounds.add h455 h460 (by norm_num)
  convert h461 using 1 <;>
    simp only [v12, v41, v446, v447, v448, v449, v450, v451, v452, v453, v454, v455, v456, v457, v458, v459, v460, v461, meanCore, Nat.cast_mul, Nat.cast_ofNat] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
        Nat.choose] <;> ring <;> simp

end BstLean.Part271.R3.Band

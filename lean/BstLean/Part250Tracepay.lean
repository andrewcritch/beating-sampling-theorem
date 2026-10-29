import BstLean.Part250Bounds
import BstLean.Part250Conditional
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem tracepay : Bounds (traceVariance 24450 (mW 12225) / ((1/10^5) * ((mW 12225 : ℝ)*24450*((mW 12225 : ℝ)+24450+1)))^2) (80986026379553923701950297/5000000000000000000000000000000000) (32394410551821569480780123/2000000000000000000000000000000000) := by
  let v0 : ℝ := 24450
  have h0 : Bounds v0 24450 24450 := Bounds.point _
  let v1 : ℝ := 202009148155087
  have h1 : Bounds v1 202009148155087 202009148155087 := Bounds.point _
  let v2 : ℝ := 2
  have h2 : Bounds v2 2 2 := Bounds.point _
  let v8 : ℝ := 6
  have h8 : Bounds v8 6 6 := Bounds.point _
  let v13 : ℝ := 3
  have h13 : Bounds v13 3 3 := Bounds.point _
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v208 : ℝ := (1/100000)
  have h208 : Bounds v208 (1/100000) (1/100000) := Bounds.point _
  let v344 : ℝ := v1*v2
  have h344 : Bounds v344 404018296310174 404018296310174 := Bounds.mul h1 h2 (by norm_num)
  let v345 : ℝ := -v22
  have h345 : Bounds v345 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h22
  let v346 : ℝ := v1+v345
  have h346 : Bounds v346 202009148155086 202009148155086 := Bounds.add h1 h345 (by norm_num)
  let v347 : ℝ := v344*v346
  have h347 : Bounds v347 81615391876687374973311644900 81615391876687374973311645000 := Bounds.mul h344 h346 (by norm_num)
  let v348 : ℝ := v0^2
  have h348 : Bounds v348 597802500 597802500 := Bounds.pow h0 2 (by norm_num)
  let v349 : ℝ := v348*v2
  have h349 : Bounds v349 1195605000 1195605000 := Bounds.mul h348 h2 (by norm_num)
  let v350 : ℝ := v0*v8
  have h350 : Bounds v350 146700 146700 := Bounds.mul h0 h8 (by norm_num)
  let v351 : ℝ := v349+v350
  have h351 : Bounds v351 1195751700 1195751700 := Bounds.add h349 h350 (by norm_num)
  let v352 : ℝ := v347*v351
  have h352 : Bounds v352 97591743582715118992874854000000000000 97591743582715118992874854200000000000 := Bounds.mul h347 h351 (by norm_num)
  let v353 : ℝ := 8
  have h353 : Bounds v353 8 8 := Bounds.point _
  let v354 : ℝ := v0*v353
  have h354 : Bounds v354 195600 195600 := Bounds.mul h0 h353 (by norm_num)
  let v355 : ℝ := v354*v1
  have h355 : Bounds v355 39512989379135017200 39512989379135017200 := Bounds.mul h354 h1 (by norm_num)
  let v356 : ℝ := -v22
  have h356 : Bounds v356 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h22
  let v357 : ℝ := v1+v356
  have h357 : Bounds v357 202009148155086 202009148155086 := Bounds.add h1 h356 (by norm_num)
  let v358 : ℝ := v355*v357
  have h358 : Bounds v358 7981985325540025272389878870000000 7981985325540025272389878880000000 := Bounds.mul h355 h357 (by norm_num)
  let v359 : ℝ := -v2
  have h359 : Bounds v359 (-2) (-2) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h2
  let v360 : ℝ := v1+v359
  have h360 : Bounds v360 202009148155085 202009148155085 := Bounds.add h1 h359 (by norm_num)
  let v361 : ℝ := v358*v360
  have h361 : Bounds v361 1612434056198729339385322170000000000000000000000 1612434056198729339385322180000000000000000000000 := Bounds.mul h358 h360 (by norm_num)
  let v362 : ℝ := v352+v361
  have h362 : Bounds v362 1612434056296321082968037280000000000000000000000 1612434056296321082968037300000000000000000000000 := Bounds.add h352 h361 (by norm_num)
  let v363 : ℝ := v1*v353
  have h363 : Bounds v363 1616073185240696 1616073185240696 := Bounds.mul h1 h353 (by norm_num)
  let v364 : ℝ := v363*v0
  have h364 : Bounds v364 39512989379135017200 39512989379135017200 := Bounds.mul h363 h0 (by norm_num)
  let v365 : ℝ := v0+v2
  have h365 : Bounds v365 24452 24452 := Bounds.add h0 h2 (by norm_num)
  let v366 : ℝ := v364*v365
  have h366 : Bounds v366 966171616298609440574400 966171616298609440574400 := Bounds.mul h364 h365 (by norm_num)
  let v367 : ℝ := v0+v13
  have h367 : Bounds v367 24453 24453 := Bounds.add h0 h13 (by norm_num)
  let v368 : ℝ := v366*v367
  have h368 : Bounds v368 23625794533349896650365803200 23625794533349896650365803200 := Bounds.mul h366 h367 (by norm_num)
  let v369 : ℝ := v362+v368
  have h369 : Bounds v369 1612434056296321082991663070000000000000000000000 1612434056296321082991663100000000000000000000000 := Bounds.add h362 h368 (by norm_num)
  let v370 : ℝ := v1*v353
  have h370 : Bounds v370 1616073185240696 1616073185240696 := Bounds.mul h1 h353 (by norm_num)
  let v371 : ℝ := -v22
  have h371 : Bounds v371 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h22
  let v372 : ℝ := v1+v371
  have h372 : Bounds v372 202009148155086 202009148155086 := Bounds.add h1 h371 (by norm_num)
  let v373 : ℝ := v370*v372
  have h373 : Bounds v373 326461567506749499893246579000 326461567506749499893246580000 := Bounds.mul h370 h372 (by norm_num)
  let v374 : ℝ := v373*v0
  have h374 : Bounds v374 7981985325540025272389878850000000 7981985325540025272389878890000000 := Bounds.mul h373 h0 (by norm_num)
  let v375 : ℝ := v0+v2
  have h375 : Bounds v375 24452 24452 := Bounds.add h0 h2 (by norm_num)
  let v376 : ℝ := v374*v375
  have h376 : Bounds v376 195175505180104697960477317000000000000 195175505180104697960477319000000000000 := Bounds.mul h374 h375 (by norm_num)
  let v377 : ℝ := v376*v2
  have h377 : Bounds v377 390351010360209395920954634000000000000 390351010360209395920954638000000000000 := Bounds.mul h376 h2 (by norm_num)
  let v378 : ℝ := v369+v377
  have h378 : Bounds v378 1612434056686672093351872460000000000000000000000 1612434056686672093351872500000000000000000000000 := Bounds.add h369 h377 (by norm_num)
  let v379 : ℝ := v1*v0
  have h379 : Bounds v379 4939123672391877150 4939123672391877150 := Bounds.mul h1 h0 (by norm_num)
  let v380 : ℝ := v1+v0
  have h380 : Bounds v380 202009148179537 202009148179537 := Bounds.add h1 h0 (by norm_num)
  let v381 : ℝ := v380+v22
  have h381 : Bounds v381 202009148179538 202009148179538 := Bounds.add h380 h22 (by norm_num)
  let v382 : ℝ := v379*v381
  have h382 : Bounds v382 997748165813274611086061039000000 997748165813274611086061040000000 := Bounds.mul h379 h381 (by norm_num)
  let v383 : ℝ := v208*v382
  have h383 : Bounds v383 9977481658132746110860610390 9977481658132746110860610400 := Bounds.mul h208 h382 (by norm_num)
  let v384 : ℝ := v383^2
  have h384 : Bounds v384 99550140238375372736582771000000000000000000000000000000 99550140238375372736582771300000000000000000000000000000 := Bounds.pow h383 2 (by norm_num)
  let v385 : ℝ := 1/v384
  have h385 : Bounds v385 (5022594632239966035557943/500000000000000000000000000000000000000000000000000000000000000000000000000000000) (10045189264479932071115887/1000000000000000000000000000000000000000000000000000000000000000000000000000000000) := Bounds.inv h384 (by norm_num)
  let v386 : ℝ := v378/v384
  have h386 : Bounds v386 (80986026379553923701950297/5000000000000000000000000000000000) (32394410551821569480780123/2000000000000000000000000000000000) := bounds_div h378 h385 (by norm_num)
  convert h386 using 1 <;>
    simp only [v0, v1, v2, v8, v13, v22, v208, v344, v345, v346, v347, v348, v349, v350, v351, v352, v353, v354, v355, v356, v357, v358, v359, v360, v361, v362, v363, v364, v365, v366, v367, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377, v378, v379, v380, v381, v382, v383, v384, v386, traceVariance, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.tracepay

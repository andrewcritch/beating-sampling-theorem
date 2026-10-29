import BstLean.Part291Energy
import BstLean.Part255Bounds
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part206 BstLean.Part211 BstLean.Part255
theorem lowEnergy80_hz0 : B (26666666666666409 / 40000000000000000) (133333333333342669 / 200000000000000000) (kdot ((1 / 2))) := by
    constructor
    · apply bkdot_lower (q := (115470053837925153 / 200000000000000000)) (a := (523598775598308991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144337567297406441 / 250000000000000000)) (a := (523598775598225551 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy80_hz1 : B (1 / 4) (1 / 4) (((1 / 2) : ℝ)^2) := bsq (bpoint ((1 / 2) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy80_hz2 : B (3 / 4) (3 / 4) ((1 : ℝ) - (((1 / 2) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy80_hz1 (by norm_num) (by norm_num)

theorem lowEnergy80_hz3 : B (433012701892219323 / 500000000000000000) (866025403784438647 / 1000000000000000000) (√((1 : ℝ) - (((1 / 2) : ℝ)^2))) := bsqrt lowEnergy80_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy80_hz4 : B (34458055963862003 / 125000000000000000) (11026577908435841 / 40000000000000000) ((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) := bdiv lowEnergy80_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy80_hz5 : B (5208333333333283 / 15625000000000000) (333333333333356673 / 1000000000000000000) (((1 / 2) : ℝ) * (kdot ((1 / 2)))) := bmul (bpoint ((1 / 2) : ℝ)) lowEnergy80_hz0 (by norm_num) (by norm_num)

theorem lowEnergy80_hz6 : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) + (((1 / 2) : ℝ) * (kdot ((1 / 2))))) := badd lowEnergy80_hz4 lowEnergy80_hz5 (by norm_num) (by norm_num)

theorem lowEnergy80_hz7 : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (kappa ((1 / 2))) := by rw [kappa_eq]; exact lowEnergy80_hz6

theorem lowEnergy80_hz8 : B (22176533090246413 / 31250000000000000) (709649058887885237 / 1000000000000000000) (kdot ((122407104869 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (30661167925726297 / 62500000000000000)) (a := (456082191780351237 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (490578686811620751 / 1000000000000000000)) (a := (228041095890175603 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy80_hz9 : B (374587483060259087 / 1000000000000000000) (23411717691266193 / 62500000000000000) (((122407104869 / 200000000000) : ℝ)^2) := bsq (bpoint ((122407104869 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy80_hz10 : B (39088282308733807 / 62500000000000000) (625412516939740913 / 1000000000000000000) ((1 : ℝ) - (((122407104869 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy80_hz9 (by norm_num) (by norm_num)

theorem lowEnergy80_hz11 : B (790830270626852593 / 1000000000000000000) (158166054125370519 / 200000000000000000) (√((1 : ℝ) - (((122407104869 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy80_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy80_hz12 : B (251729093433929823 / 1000000000000000000) (10069163737357193 / 40000000000000000) ((√((1 : ℝ) - (((122407104869 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy80_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy80_hz13 : B (43433043385738261 / 100000000000000000) (13572826058043207 / 31250000000000000) (((122407104869 / 200000000000) : ℝ) * (kdot ((122407104869 / 200000000000)))) := bmul (bpoint ((122407104869 / 200000000000) : ℝ)) lowEnergy80_hz8 (by norm_num) (by norm_num)

theorem lowEnergy80_hz14 : B (686059527291312433 / 1000000000000000000) (686059527291312449 / 1000000000000000000) (((√((1 : ℝ) - (((122407104869 / 200000000000) : ℝ)^2))) / Real.pi) + (((122407104869 / 200000000000) : ℝ) * (kdot ((122407104869 / 200000000000))))) := badd lowEnergy80_hz12 lowEnergy80_hz13 (by norm_num) (by norm_num)

theorem lowEnergy80_hz15 : B (686059527291312433 / 1000000000000000000) (686059527291312449 / 1000000000000000000) (kappa ((122407104869 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy80_hz14

theorem lowEnergy80 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1 / 2)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (688885274171 / 1000000000000) := by
  have hk1 : kappa q ≤ (121799556209 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1 / 2) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy80_hz7.2.trans (by norm_num))
  have hk2 : kappa ((122407104869 / 200000000000) : ℝ) ≤ (171514881823 / 250000000000) := lowEnergy80_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((195195860139 / 250000000000) : ℝ)) (R := ((19541236649 / 25000000000) : ℝ)) (Q2 := ((122407104869 / 200000000000) : ℝ)) (T := ((829004422061 / 1000000000000) : ℝ))
    (B := ((688885274171 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy81_hz0 : B (666482920977161467 / 1000000000000000000) (13329658419544327 / 20000000000000000) (kdot ((999 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (577735169411837961 / 1000000000000000000)) (a := (130971850663109509 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (14443379235295949 / 25000000000000000)) (a := (523887402652351827 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy81_hz1 : B (998001 / 4000000) (998001 / 4000000) (((999 / 2000) : ℝ)^2) := bsq (bpoint ((999 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy81_hz2 : B (3001999 / 4000000) (3001999 / 4000000) ((1 : ℝ) - (((999 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy81_hz1 (by norm_num) (by norm_num)

theorem lowEnergy81_hz3 : B (866313886533051021 / 1000000000000000000) (433156943266525511 / 500000000000000000) (√((1 : ℝ) - (((999 / 2000) : ℝ)^2))) := bsqrt lowEnergy81_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy81_hz4 : B (17234767163860801 / 62500000000000000) (137878137310886409 / 500000000000000000) ((√((1 : ℝ) - (((999 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy81_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy81_hz5 : B (41613527378511519 / 125000000000000000) (332908219028119567 / 1000000000000000000) (((999 / 2000) : ℝ) * (kdot ((999 / 2000)))) := bmul (bpoint ((999 / 2000) : ℝ)) lowEnergy81_hz0 (by norm_num) (by norm_num)

theorem lowEnergy81_hz6 : B (76083061706233121 / 125000000000000000) (121732898729978477 / 200000000000000000) (((√((1 : ℝ) - (((999 / 2000) : ℝ)^2))) / Real.pi) + (((999 / 2000) : ℝ) * (kdot ((999 / 2000))))) := badd lowEnergy81_hz4 lowEnergy81_hz5 (by norm_num) (by norm_num)

theorem lowEnergy81_hz7 : B (76083061706233121 / 125000000000000000) (121732898729978477 / 200000000000000000) (kappa ((999 / 2000))) := by rw [kappa_eq]; exact lowEnergy81_hz6

theorem lowEnergy81_hz8 : B (354757275337165303 / 500000000000000000) (354757275337165313 / 500000000000000000) (kdot ((611701288551 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (122710212105115973 / 250000000000000000)) (a := (456293476788126563 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (490840848420463891 / 1000000000000000000)) (a := (114073369197031633 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy81_hz9 : B (374178466414953763 / 1000000000000000000) (93544616603738441 / 250000000000000000) (((611701288551 / 1000000000000) : ℝ)^2) := bsq (bpoint ((611701288551 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy81_hz10 : B (156455383396261559 / 250000000000000000) (625821533585046237 / 1000000000000000000) ((1 : ℝ) - (((611701288551 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy81_hz9 (by norm_num) (by norm_num)

theorem lowEnergy81_hz11 : B (395544413936363863 / 500000000000000000) (791088827872727727 / 1000000000000000000) (√((1 : ℝ) - (((611701288551 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy81_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy81_hz12 : B (251811394761436331 / 1000000000000000000) (251811394761436333 / 1000000000000000000) ((√((1 : ℝ) - (((611701288551 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy81_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy81_hz13 : B (434010964893171817 / 1000000000000000000) (43401096489317183 / 100000000000000000) (((611701288551 / 1000000000000) : ℝ) * (kdot ((611701288551 / 1000000000000)))) := bmul (bpoint ((611701288551 / 1000000000000) : ℝ)) lowEnergy81_hz8 (by norm_num) (by norm_num)

theorem lowEnergy81_hz14 : B (171455589913652037 / 250000000000000000) (685822359654608163 / 1000000000000000000) (((√((1 : ℝ) - (((611701288551 / 1000000000000) : ℝ)^2))) / Real.pi) + (((611701288551 / 1000000000000) : ℝ) * (kdot ((611701288551 / 1000000000000))))) := badd lowEnergy81_hz12 lowEnergy81_hz13 (by norm_num) (by norm_num)

theorem lowEnergy81_hz15 : B (171455589913652037 / 250000000000000000) (685822359654608163 / 1000000000000000000) (kappa ((611701288551 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy81_hz14

theorem lowEnergy81 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (999 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (68864741277 / 100000000000) := by
  have hk1 : kappa q ≤ (12173289873 / 20000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((999 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy81_hz7.2.trans (by norm_num))
  have hk2 : kappa ((611701288551 / 1000000000000) : ℝ) ≤ (137164471931 / 200000000000) := lowEnergy81_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((780569979983 / 1000000000000) : ℝ)) (R := ((781436005387 / 1000000000000) : ℝ)) (Q2 := ((611701288551 / 1000000000000) : ℝ)) (T := ((414430559079 / 500000000000) : ℝ))
    (B := ((68864741277 / 100000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy82_hz0 : B (666299236424077829 / 1000000000000000000) (666299236424134533 / 1000000000000000000) (kdot ((499 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (4624960559123609 / 8000000000000000)) (a := (65521991709213847 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144530017472612781 / 250000000000000000)) (a := (524175933673621707 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy82_hz1 : B (249001 / 1000000) (249001 / 1000000) (((499 / 1000) : ℝ)^2) := bsq (bpoint ((499 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy82_hz2 : B (750999 / 1000000) (750999 / 1000000) ((1 : ℝ) - (((499 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy82_hz1 (by norm_num) (by norm_num)

theorem lowEnergy82_hz3 : B (216650496191446559 / 250000000000000000) (866601984765786237 / 1000000000000000000) (√((1 : ℝ) - (((499 / 1000) : ℝ)^2))) := bsqrt lowEnergy82_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy82_hz4 : B (137923989568722257 / 500000000000000000) (55169595827488903 / 200000000000000000) ((√((1 : ℝ) - (((499 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy82_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy82_hz5 : B (83120829743903709 / 250000000000000000) (83120829743910783 / 250000000000000000) (((499 / 1000) : ℝ) * (kdot ((499 / 1000)))) := bmul (bpoint ((499 / 1000) : ℝ)) lowEnergy82_hz0 (by norm_num) (by norm_num)

theorem lowEnergy82_hz6 : B (12166625962261187 / 20000000000000000) (608331298113087647 / 1000000000000000000) (((√((1 : ℝ) - (((499 / 1000) : ℝ)^2))) / Real.pi) + (((499 / 1000) : ℝ) * (kdot ((499 / 1000))))) := badd lowEnergy82_hz4 lowEnergy82_hz5 (by norm_num) (by norm_num)

theorem lowEnergy82_hz7 : B (12166625962261187 / 20000000000000000) (608331298113087647 / 1000000000000000000) (kappa ((499 / 1000))) := by rw [kappa_eq]; exact lowEnergy82_hz6

theorem lowEnergy82_hz8 : B (354690061705523407 / 500000000000000000) (141876024682209367 / 200000000000000000) (kdot ((305683572389 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (30693931661678829 / 62500000000000000)) (a := (228252317319756917 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (491102906586861263 / 1000000000000000000)) (a := (228252317319756901 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy82_hz9 : B (93442446428501003 / 250000000000000000) (373769785714004013 / 1000000000000000000) (((305683572389 / 500000000000) : ℝ)^2) := bsq (bpoint ((305683572389 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy82_hz10 : B (626230214285995987 / 1000000000000000000) (156557553571498997 / 250000000000000000) ((1 : ℝ) - (((305683572389 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy82_hz9 (by norm_num) (by norm_num)

theorem lowEnergy82_hz11 : B (395673544189523741 / 500000000000000000) (197836772094761871 / 250000000000000000) (√((1 : ℝ) - (((305683572389 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy82_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy82_hz12 : B (251893601633808741 / 1000000000000000000) (251893601633808743 / 1000000000000000000) ((√((1 : ℝ) - (((305683572389 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy82_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy82_hz13 : B (108422925153019241 / 250000000000000000) (216845850306038489 / 500000000000000000) (((305683572389 / 500000000000) : ℝ) * (kdot ((305683572389 / 500000000000)))) := bmul (bpoint ((305683572389 / 500000000000) : ℝ)) lowEnergy82_hz8 (by norm_num) (by norm_num)

theorem lowEnergy82_hz14 : B (137117060449177141 / 200000000000000000) (685585302245885721 / 1000000000000000000) (((√((1 : ℝ) - (((305683572389 / 500000000000) : ℝ)^2))) / Real.pi) + (((305683572389 / 500000000000) : ℝ) * (kdot ((305683572389 / 500000000000))))) := badd lowEnergy82_hz12 lowEnergy82_hz13 (by norm_num) (by norm_num)

theorem lowEnergy82_hz15 : B (137117060449177141 / 200000000000000000) (685585302245885721 / 1000000000000000000) (kappa ((305683572389 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy82_hz14

theorem lowEnergy82 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (499 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (688409661873 / 1000000000000) := by
  have hk1 : kappa q ≤ (304165649057 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((499 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy82_hz7.2.trans (by norm_num))
  have hk2 : kappa ((305683572389 / 500000000000) : ℝ) ≤ (342792651123 / 500000000000) := lowEnergy82_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((780356519877 / 1000000000000) : ℝ)) (R := ((781222545281 / 1000000000000) : ℝ)) (Q2 := ((305683572389 / 500000000000) : ℝ)) (T := ((25897433003 / 31250000000) : ℝ))
    (B := ((688409661873 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy83_hz0 : B (666115612885319299 / 1000000000000000000) (666115612885377883 / 1000000000000000000) (kdot ((997 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (72313121360194289 / 125000000000000000)) (a := (104892873770781151 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (578504970881554311 / 1000000000000000000)) (a := (524464368853813733 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy83_hz1 : B (994009 / 4000000) (994009 / 4000000) (((997 / 2000) : ℝ)^2) := bsq (bpoint ((997 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy83_hz2 : B (3005991 / 4000000) (3005991 / 4000000) ((1 : ℝ) - (((997 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy83_hz1 (by norm_num) (by norm_num)

theorem lowEnergy83_hz3 : B (173377939773201827 / 200000000000000000) (54180606179125571 / 62500000000000000) (√((1 : ℝ) - (((997 / 2000) : ℝ)^2))) := bsqrt lowEnergy83_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy83_hz4 : B (8623111293123123 / 31250000000000000) (137969780689969969 / 500000000000000000) ((√((1 : ℝ) - (((997 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy83_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy83_hz5 : B (33205863302333167 / 100000000000000000) (2656469064186887 / 8000000000000000) (((997 / 2000) : ℝ) * (kdot ((997 / 2000)))) := bmul (bpoint ((997 / 2000) : ℝ)) lowEnergy83_hz0 (by norm_num) (by norm_num)

theorem lowEnergy83_hz6 : B (303999097201635803 / 500000000000000000) (607998194403300813 / 1000000000000000000) (((√((1 : ℝ) - (((997 / 2000) : ℝ)^2))) / Real.pi) + (((997 / 2000) : ℝ) * (kdot ((997 / 2000))))) := badd lowEnergy83_hz4 lowEnergy83_hz5 (by norm_num) (by norm_num)

theorem lowEnergy83_hz7 : B (303999097201635803 / 500000000000000000) (607998194403300813 / 1000000000000000000) (kappa ((997 / 2000))) := by rw [kappa_eq]; exact lowEnergy83_hz6

theorem lowEnergy83_hz8 : B (88655722122545581 / 125000000000000000) (70924577698036467 / 100000000000000000) (kdot ((61103309299 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (98272972296476029 / 200000000000000000)) (a := (91343133103869477 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (30710303842648759 / 62500000000000000)) (a := (57089458189918419 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy83_hz9 : B (373361440728925987 / 1000000000000000000) (93340360182231497 / 250000000000000000) (((61103309299 / 100000000000) : ℝ)^2) := bsq (bpoint ((61103309299 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy83_hz10 : B (156659639817768503 / 250000000000000000) (626638559271074013 / 1000000000000000000) ((1 : ℝ) - (((61103309299 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy83_hz9 (by norm_num) (by norm_num)

theorem lowEnergy83_hz11 : B (791605052580561799 / 1000000000000000000) (791605052580561801 / 1000000000000000000) (√((1 : ℝ) - (((61103309299 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy83_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy83_hz12 : B (3937120534209879 / 15625000000000000) (251975714189432257 / 1000000000000000000) ((√((1 : ℝ) - (((61103309299 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy83_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy83_hz13 : B (433372640798407953 / 1000000000000000000) (433372640798407967 / 1000000000000000000) (((61103309299 / 100000000000) : ℝ) * (kdot ((61103309299 / 100000000000)))) := bmul (bpoint ((61103309299 / 100000000000) : ℝ)) lowEnergy83_hz8 (by norm_num) (by norm_num)

theorem lowEnergy83_hz14 : B (685348354987840209 / 1000000000000000000) (21417136093370007 / 31250000000000000) (((√((1 : ℝ) - (((61103309299 / 100000000000) : ℝ)^2))) / Real.pi) + (((61103309299 / 100000000000) : ℝ) * (kdot ((61103309299 / 100000000000))))) := badd lowEnergy83_hz12 lowEnergy83_hz13 (by norm_num) (by norm_num)

theorem lowEnergy83_hz15 : B (685348354987840209 / 1000000000000000000) (21417136093370007 / 31250000000000000) (kappa ((61103309299 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy83_hz14

theorem lowEnergy83 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (997 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (3440860107 / 5000000000) := by
  have hk1 : kappa q ≤ (151999548601 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((997 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy83_hz7.2.trans (by norm_num))
  have hk2 : kappa ((61103309299 / 100000000000) : ℝ) ≤ (171337088747 / 250000000000) := lowEnergy83_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((780143060217 / 1000000000000) : ℝ)) (R := ((781009085621 / 1000000000000) : ℝ)) (Q2 := ((61103309299 / 100000000000) : ℝ)) (T := ((828574635849 / 1000000000000) : ℝ))
    (B := ((3440860107 / 5000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy84_hz0 : B (665932050239079683 / 1000000000000000000) (41620753139946263 / 62500000000000000) (kdot ((249 / 500))) := by
    constructor
    · apply bkdot_lower (q := (115777974528179569 / 200000000000000000)) (a := (104950541676871139 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144722468160224461 / 250000000000000000)) (a := (839604333414817 / 1600000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy84_hz1 : B (62001 / 250000) (62001 / 250000) (((249 / 500) : ℝ)^2) := bsq (bpoint ((249 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy84_hz2 : B (187999 / 250000) (187999 / 250000) ((1 : ℝ) - (((249 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy84_hz1 (by norm_num) (by norm_num)

theorem lowEnergy84_hz3 : B (86717702921606497 / 100000000000000000) (867177029216064971 / 1000000000000000000) (√((1 : ℝ) - (((249 / 500) : ℝ)^2))) := bsqrt lowEnergy84_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy84_hz4 : B (138015510735481679 / 500000000000000000) (276031021470963359 / 1000000000000000000) ((√((1 : ℝ) - (((249 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy84_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy84_hz5 : B (165817080509530841 / 500000000000000000) (20727135063693239 / 62500000000000000) (((249 / 500) : ℝ) * (kdot ((249 / 500)))) := bmul (bpoint ((249 / 500) : ℝ)) lowEnergy84_hz0 (by norm_num) (by norm_num)

theorem lowEnergy84_hz6 : B (7595814781125313 / 12500000000000000) (607665182490055183 / 1000000000000000000) (((√((1 : ℝ) - (((249 / 500) : ℝ)^2))) / Real.pi) + (((249 / 500) : ℝ) * (kdot ((249 / 500))))) := badd lowEnergy84_hz4 lowEnergy84_hz5 (by norm_num) (by norm_num)

theorem lowEnergy84_hz7 : B (7595814781125313 / 12500000000000000) (607665182490055183 / 1000000000000000000) (kappa ((249 / 500))) := by rw [kappa_eq]; exact lowEnergy84_hz6

theorem lowEnergy84_hz8 : B (354555755634055137 / 500000000000000000) (88638938908513787 / 125000000000000000) (kdot ((610699133159 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (3072666957949379 / 6250000000000000)) (a := (28557910600435691 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (491626713271900639 / 1000000000000000000)) (a := (456926569606971023 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy84_hz9 : B (372953431241154013 / 1000000000000000000) (186476715620577007 / 500000000000000000) (((610699133159 / 1000000000000) : ℝ)^2) := bsq (bpoint ((610699133159 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy84_hz10 : B (313523284379422993 / 500000000000000000) (627046568758845987 / 1000000000000000000) ((1 : ℝ) - (((610699133159 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy84_hz9 (by norm_num) (by norm_num)

theorem lowEnergy84_hz11 : B (3959313604524293 / 5000000000000000) (395931360452429301 / 500000000000000000) (√((1 : ℝ) - (((610699133159 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy84_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy84_hz12 : B (252057732564412339 / 1000000000000000000) (12602886628220617 / 50000000000000000) ((√((1 : ℝ) - (((610699133159 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy84_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy84_hz13 : B (86610757048900681 / 200000000000000000) (433053785244503419 / 1000000000000000000) (((610699133159 / 1000000000000) : ℝ) * (kdot ((610699133159 / 1000000000000)))) := bmul (bpoint ((610699133159 / 1000000000000) : ℝ)) lowEnergy84_hz8 (by norm_num) (by norm_num)

theorem lowEnergy84_hz14 : B (21409734931528617 / 31250000000000000) (685111517808915759 / 1000000000000000000) (((√((1 : ℝ) - (((610699133159 / 1000000000000) : ℝ)^2))) / Real.pi) + (((610699133159 / 1000000000000) : ℝ) * (kdot ((610699133159 / 1000000000000))))) := badd lowEnergy84_hz12 lowEnergy84_hz13 (by norm_num) (by norm_num)

theorem lowEnergy84_hz15 : B (21409734931528617 / 31250000000000000) (685111517808915759 / 1000000000000000000) (kappa ((610699133159 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy84_hz14

theorem lowEnergy84 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (687934491279 / 1000000000000) := by
  have hk1 : kappa q ≤ (607665182491 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((249 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy84_hz7.2.trans (by norm_num))
  have hk2 : kappa ((610699133159 / 1000000000000) : ℝ) ≤ (685111517809 / 1000000000000) := lowEnergy84_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((97491200123 / 125000000000) : ℝ)) (R := ((195198906597 / 250000000000) : ℝ)) (Q2 := ((610699133159 / 1000000000000) : ℝ)) (T := ((165686291479 / 200000000000) : ℝ))
    (B := ((687934491279 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy85_hz0 : B (665748548363835577 / 1000000000000000000) (133149709672779621 / 200000000000000000) (kdot ((199 / 400))) := by
    constructor
    · apply bkdot_lower (q := (289637387711947509 / 500000000000000000)) (a := (525040952455949113 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (579274775423895017 / 1000000000000000000)) (a := (32815059528490681 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy85_hz1 : B (39601 / 160000) (39601 / 160000) (((199 / 400) : ℝ)^2) := bsq (bpoint ((199 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy85_hz2 : B (120399 / 160000) (120399 / 160000) ((1 : ℝ) - (((199 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy85_hz1 (by norm_num) (by norm_num)

theorem lowEnergy85_hz3 : B (216865994049320697 / 250000000000000000) (867463976197282789 / 1000000000000000000) (√((1 : ℝ) - (((199 / 400) : ℝ)^2))) := bsqrt lowEnergy85_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy85_hz4 : B (8628823735371737 / 31250000000000000) (55224471906379117 / 200000000000000000) ((√((1 : ℝ) - (((199 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy85_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy85_hz5 : B (331209902811008199 / 1000000000000000000) (82802475702759827 / 250000000000000000) (((199 / 400) : ℝ) * (kdot ((199 / 400)))) := bmul (bpoint ((199 / 400) : ℝ)) lowEnergy85_hz0 (by norm_num) (by norm_num)

theorem lowEnergy85_hz6 : B (607332262342903783 / 1000000000000000000) (607332262342934893 / 1000000000000000000) (((√((1 : ℝ) - (((199 / 400) : ℝ)^2))) / Real.pi) + (((199 / 400) : ℝ) * (kdot ((199 / 400))))) := badd lowEnergy85_hz4 lowEnergy85_hz5 (by norm_num) (by norm_num)

theorem lowEnergy85_hz7 : B (607332262342903783 / 1000000000000000000) (607332262342934893 / 1000000000000000000) (kappa ((199 / 400))) := by rw [kappa_eq]; exact lowEnergy85_hz6

theorem lowEnergy85_hz8 : B (177244331539694217 / 250000000000000000) (708977326158776891 / 1000000000000000000) (kdot ((610365265253 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (491888462123028173 / 1000000000000000000)) (a := (228568673541911271 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (122972115530757043 / 250000000000000000)) (a := (457137347083822507 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy85_hz9 : B (372545757027365049 / 1000000000000000000) (7450915140547301 / 20000000000000000) (((610365265253 / 1000000000000) : ℝ)^2) := bsq (bpoint ((610365265253 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy85_hz10 : B (12549084859452699 / 20000000000000000) (627454242972634951 / 1000000000000000000) ((1 : ℝ) - (((610365265253 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy85_hz9 (by norm_num) (by norm_num)

theorem lowEnergy85_hz11 : B (158424018756328101 / 200000000000000000) (792120093781640507 / 1000000000000000000) (√((1 : ℝ) - (((610365265253 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy85_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy85_hz12 : B (126069828447763791 / 500000000000000000) (252139656895527583 / 1000000000000000000) ((√((1 : ℝ) - (((610365265253 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy85_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy85_hz13 : B (216367566869632269 / 500000000000000000) (432735133739264553 / 1000000000000000000) (((610365265253 / 1000000000000) : ℝ) * (kdot ((610365265253 / 1000000000000)))) := bmul (bpoint ((610365265253 / 1000000000000) : ℝ)) lowEnergy85_hz8 (by norm_num) (by norm_num)

theorem lowEnergy85_hz14 : B (17121869765869803 / 25000000000000000) (85609348829349017 / 125000000000000000) (((√((1 : ℝ) - (((610365265253 / 1000000000000) : ℝ)^2))) / Real.pi) + (((610365265253 / 1000000000000) : ℝ) * (kdot ((610365265253 / 1000000000000))))) := badd lowEnergy85_hz12 lowEnergy85_hz13 (by norm_num) (by norm_num)

theorem lowEnergy85_hz15 : B (17121869765869803 / 25000000000000000) (85609348829349017 / 125000000000000000) (kappa ((610365265253 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy85_hz14

theorem lowEnergy85 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (199 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (171924267859 / 250000000000) := by
  have hk1 : kappa q ≤ (607332262343 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((199 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy85_hz7.2.trans (by norm_num))
  have hk2 : kappa ((610365265253 / 1000000000000) : ℝ) ≤ (136974958127 / 200000000000) := lowEnergy85_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((779716142159 / 1000000000000) : ℝ)) (R := ((780582167563 / 1000000000000) : ℝ)) (Q2 := ((610365265253 / 1000000000000) : ℝ)) (T := ((828288320711 / 1000000000000) : ℝ))
    (B := ((171924267859 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy86_hz0 : B (166391276784586337 / 250000000000000000) (133113021427681989 / 200000000000000000) (kdot ((497 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (579659679485623777 / 1000000000000000000)) (a := (525329101259131919 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (18114364983925743 / 31250000000000000)) (a := (131332275314757613 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy86_hz1 : B (247009 / 1000000) (247009 / 1000000) (((497 / 1000) : ℝ)^2) := bsq (bpoint ((497 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy86_hz2 : B (752991 / 1000000) (752991 / 1000000) ((1 : ℝ) - (((497 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy86_hz1 (by norm_num) (by norm_num)

theorem lowEnergy86_hz3 : B (108468817523747349 / 125000000000000000) (867750540189978793 / 1000000000000000000) (√((1 : ℝ) - (((497 / 1000) : ℝ)^2))) := bsqrt lowEnergy86_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy86_hz4 : B (138106787841897511 / 500000000000000000) (276213575683795023 / 1000000000000000000) ((√((1 : ℝ) - (((497 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy86_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy86_hz5 : B (330785858247757637 / 1000000000000000000) (330785858247789743 / 1000000000000000000) (((497 / 1000) : ℝ) * (kdot ((497 / 1000)))) := bmul (bpoint ((497 / 1000) : ℝ)) lowEnergy86_hz0 (by norm_num) (by norm_num)

theorem lowEnergy86_hz6 : B (606999433931552659 / 1000000000000000000) (303499716965792383 / 500000000000000000) (((√((1 : ℝ) - (((497 / 1000) : ℝ)^2))) / Real.pi) + (((497 / 1000) : ℝ) * (kdot ((497 / 1000))))) := badd lowEnergy86_hz4 lowEnergy86_hz5 (by norm_num) (by norm_num)

theorem lowEnergy86_hz7 : B (606999433931552659 / 1000000000000000000) (303499716965792383 / 500000000000000000) (kappa ((497 / 1000))) := by rw [kappa_eq]; exact lowEnergy86_hz6

theorem lowEnergy86_hz8 : B (177210805384785429 / 250000000000000000) (35442161076957087 / 50000000000000000) (kdot ((122006297849 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (123037527049759609 / 250000000000000000)) (a := (228673999063875833 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (98430021639807687 / 200000000000000000)) (a := (45734799812775163 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy86_hz9 : B (7442768357409451 / 20000000000000000) (372138417870472551 / 1000000000000000000) (((122006297849 / 200000000000) : ℝ)^2) := bsq (bpoint ((122006297849 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy86_hz10 : B (627861582129527449 / 1000000000000000000) (12557231642590549 / 20000000000000000) ((1 : ℝ) - (((122006297849 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy86_hz9 (by norm_num) (by norm_num)

theorem lowEnergy86_hz11 : B (792377171635785737 / 1000000000000000000) (396188585817892869 / 500000000000000000) (√((1 : ℝ) - (((122006297849 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy86_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy86_hz12 : B (252221487318020923 / 1000000000000000000) (10088859492720837 / 40000000000000000) ((√((1 : ℝ) - (((122006297849 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy86_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy86_hz13 : B (216208343038373041 / 500000000000000000) (432416686076746097 / 1000000000000000000) (((122006297849 / 200000000000) : ℝ) * (kdot ((122006297849 / 200000000000)))) := bmul (bpoint ((122006297849 / 200000000000) : ℝ)) lowEnergy86_hz8 (by norm_num) (by norm_num)

theorem lowEnergy86_hz14 : B (136927634678953401 / 200000000000000000) (342319086697383511 / 500000000000000000) (((√((1 : ℝ) - (((122006297849 / 200000000000) : ℝ)^2))) / Real.pi) + (((122006297849 / 200000000000) : ℝ) * (kdot ((122006297849 / 200000000000))))) := badd lowEnergy86_hz12 lowEnergy86_hz13 (by norm_num) (by norm_num)

theorem lowEnergy86_hz15 : B (136927634678953401 / 200000000000000000) (342319086697383511 / 500000000000000000) (kappa ((122006297849 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy86_hz14

theorem lowEnergy86 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (497 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (3437298809 / 5000000000) := by
  have hk1 : kappa q ≤ (151749858483 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((497 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy86_hz7.2.trans (by norm_num))
  have hk2 : kappa ((122006297849 / 200000000000) : ℝ) ≤ (136927634679 / 200000000000) := lowEnergy86_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((194875670931 / 250000000000) : ℝ)) (R := ((97546088641 / 125000000000) : ℝ)) (Q2 := ((122006297849 / 200000000000) : ℝ)) (T := ((51759076611 / 62500000000) : ℝ))
    (B := ((3437298809 / 5000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy87_hz0 : B (665381726441648127 / 1000000000000000000) (665381726441714859 / 1000000000000000000) (kdot ((993 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (580044585080828401 / 1000000000000000000)) (a := (525617154983909003 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1450111462702071 / 2500000000000000)) (a := (525617154983804181 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy87_hz1 : B (986049 / 4000000) (986049 / 4000000) (((993 / 2000) : ℝ)^2) := bsq (bpoint ((993 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy87_hz2 : B (3013951 / 4000000) (3013951 / 4000000) ((1 : ℝ) - (((993 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy87_hz1 (by norm_num) (by norm_num)

theorem lowEnergy87_hz3 : B (868036721573459701 / 1000000000000000000) (434018360786729851 / 500000000000000000) (√((1 : ℝ) - (((993 / 2000) : ℝ)^2))) := bsqrt lowEnergy87_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy87_hz4 : B (221043736037919 / 800000000000000) (276304670047398751 / 1000000000000000000) ((√((1 : ℝ) - (((993 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy87_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy87_hz5 : B (66072405435655659 / 200000000000000000) (82590506794577857 / 250000000000000000) (((993 / 2000) : ℝ) * (kdot ((993 / 2000)))) := bmul (bpoint ((993 / 2000) : ℝ)) lowEnergy87_hz0 (by norm_num) (by norm_num)

theorem lowEnergy87_hz6 : B (121333339445135409 / 200000000000000000) (606666697225710179 / 1000000000000000000) (((√((1 : ℝ) - (((993 / 2000) : ℝ)^2))) / Real.pi) + (((993 / 2000) : ℝ) * (kdot ((993 / 2000))))) := badd lowEnergy87_hz4 lowEnergy87_hz5 (by norm_num) (by norm_num)

theorem lowEnergy87_hz7 : B (121333339445135409 / 200000000000000000) (606666697225710179 / 1000000000000000000) (kappa ((993 / 2000))) := by rw [kappa_eq]; exact lowEnergy87_hz6

theorem lowEnergy87_hz8 : B (708709197293442981 / 1000000000000000000) (354354598646721503 / 500000000000000000) (kdot ((609697805101 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (492411651668286253 / 1000000000000000000)) (a := (91511704584119339 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (123102912917071563 / 250000000000000000)) (a := (228779261460298329 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy87_hz9 : B (371731413544976981 / 1000000000000000000) (185865706772488491 / 500000000000000000) (((609697805101 / 1000000000000) : ℝ)^2) := bsq (bpoint ((609697805101 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy87_hz10 : B (314134293227511509 / 500000000000000000) (628268586455023019 / 1000000000000000000) ((1 : ℝ) - (((609697805101 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy87_hz9 (by norm_num) (by norm_num)

theorem lowEnergy87_hz11 : B (158526790979319709 / 200000000000000000) (792633954896598547 / 1000000000000000000) (√((1 : ℝ) - (((609697805101 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy87_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy87_hz12 : B (252303223968544151 / 1000000000000000000) (252303223968544153 / 1000000000000000000) ((√((1 : ℝ) - (((609697805101 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy87_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy87_hz13 : B (86419688408940751 / 200000000000000000) (432098442044703771 / 1000000000000000000) (((609697805101 / 1000000000000) : ℝ) * (kdot ((609697805101 / 1000000000000)))) := bmul (bpoint ((609697805101 / 1000000000000) : ℝ)) lowEnergy87_hz8 (by norm_num) (by norm_num)

theorem lowEnergy87_hz14 : B (342200833006623953 / 500000000000000000) (171100416503311981 / 250000000000000000) (((√((1 : ℝ) - (((609697805101 / 1000000000000) : ℝ)^2))) / Real.pi) + (((609697805101 / 1000000000000) : ℝ) * (kdot ((609697805101 / 1000000000000))))) := badd lowEnergy87_hz12 lowEnergy87_hz13 (by norm_num) (by norm_num)

theorem lowEnergy87_hz15 : B (342200833006623953 / 500000000000000000) (171100416503311981 / 250000000000000000) (kappa ((609697805101 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy87_hz14

theorem lowEnergy87 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (993 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (137444512459 / 200000000000) := by
  have hk1 : kappa q ≤ (303333348613 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((993 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy87_hz7.2.trans (by norm_num))
  have hk2 : kappa ((609697805101 / 1000000000000) : ℝ) ≤ (342200833007 / 500000000000) := lowEnergy87_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((389644612829 / 500000000000) : ℝ)) (R := ((390077625531 / 500000000000) : ℝ)) (Q2 := ((609697805101 / 1000000000000) : ℝ)) (T := ((414001086283 / 500000000000) : ℝ))
    (B := ((137444512459 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy88_hz0 : B (665198406153062791 / 1000000000000000000) (41574900384570733 / 62500000000000000) (kdot ((62 / 125))) := by
    constructor
    · apply bkdot_lower (q := (29021474623196059 / 50000000000000000)) (a := (131476278454961457 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (580429492463921179 / 1000000000000000000)) (a := (65738139227467193 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy88_hz1 : B (3844 / 15625) (3844 / 15625) (((62 / 125) : ℝ)^2) := bsq (bpoint ((62 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy88_hz2 : B (11781 / 15625) (11781 / 15625) ((1 : ℝ) - (((62 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy88_hz1 (by norm_num) (by norm_num)

theorem lowEnergy88_hz3 : B (173664504145205217 / 200000000000000000) (434161260363013043 / 500000000000000000) (√((1 : ℝ) - (((62 / 125) : ℝ)^2))) := bsqrt lowEnergy88_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy88_hz4 : B (276395642743123579 / 1000000000000000000) (13819782137156179 / 50000000000000000) ((√((1 : ℝ) - (((62 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy88_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy88_hz5 : B (41242301181489893 / 125000000000000000) (164969204725976669 / 500000000000000000) (((62 / 125) : ℝ) * (kdot ((62 / 125)))) := bmul (bpoint ((62 / 125) : ℝ)) lowEnergy88_hz0 (by norm_num) (by norm_num)

theorem lowEnergy88_hz6 : B (606334052195042723 / 1000000000000000000) (303167026097538459 / 500000000000000000) (((√((1 : ℝ) - (((62 / 125) : ℝ)^2))) / Real.pi) + (((62 / 125) : ℝ) * (kdot ((62 / 125))))) := badd lowEnergy88_hz4 lowEnergy88_hz5 (by norm_num) (by norm_num)

theorem lowEnergy88_hz7 : B (606334052195042723 / 1000000000000000000) (303167026097538459 / 500000000000000000) (kappa ((62 / 125))) := by rw [kappa_eq]; exact lowEnergy88_hz6

theorem lowEnergy88_hz8 : B (88571906663575279 / 125000000000000000) (44285953331787641 / 62500000000000000) (kdot ((609364212793 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (492673092694016129 / 1000000000000000000)) (a := (91553784327996163 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (3849008536672001 / 7812500000000000)) (a := (228884460819990389 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy88_hz9 : B (46415592979104073 / 125000000000000000) (74264948766566517 / 200000000000000000) (((609364212793 / 1000000000000) : ℝ)^2) := bsq (bpoint ((609364212793 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy88_hz10 : B (125735051233433483 / 200000000000000000) (78584407020895927 / 125000000000000000) ((1 : ℝ) - (((609364212793 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy88_hz9 (by norm_num) (by norm_num)

theorem lowEnergy88_hz11 : B (158578088797559597 / 200000000000000000) (792890443987797987 / 1000000000000000000) (√((1 : ℝ) - (((609364212793 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy88_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy88_hz12 : B (252384866981971229 / 1000000000000000000) (25238486698197123 / 100000000000000000) ((√((1 : ℝ) - (((609364212793 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy88_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy88_hz13 : B (431780401436996967 / 1000000000000000000) (431780401436996983 / 1000000000000000000) (((609364212793 / 1000000000000) : ℝ) * (kdot ((609364212793 / 1000000000000)))) := bmul (bpoint ((609364212793 / 1000000000000) : ℝ)) lowEnergy88_hz8 (by norm_num) (by norm_num)

theorem lowEnergy88_hz14 : B (171041317104742049 / 250000000000000000) (684165268418968213 / 1000000000000000000) (((√((1 : ℝ) - (((609364212793 / 1000000000000) : ℝ)^2))) / Real.pi) + (((609364212793 / 1000000000000) : ℝ) * (kdot ((609364212793 / 1000000000000))))) := badd lowEnergy88_hz12 lowEnergy88_hz13 (by norm_num) (by norm_num)

theorem lowEnergy88_hz15 : B (171041317104742049 / 250000000000000000) (684165268418968213 / 1000000000000000000) (kappa ((609364212793 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy88_hz14

theorem lowEnergy88 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (62 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (686985472849 / 1000000000000) := by
  have hk1 : kappa q ≤ (151583513049 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((62 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy88_hz7.2.trans (by norm_num))
  have hk2 : kappa ((609364212793 / 1000000000000) : ℝ) ≤ (684165268419 / 1000000000000) := lowEnergy88_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((97384470993 / 125000000000) : ℝ)) (R := ((194985448337 / 250000000000) : ℝ)) (Q2 := ((609364212793 / 1000000000000) : ℝ)) (T := ((827859161059 / 1000000000000) : ℝ))
    (B := ((686985472849 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy89_hz0 : B (166253786538046741 / 250000000000000000) (665015146152258177 / 1000000000000000000) (kdot ((991 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (145203600472246019 / 250000000000000000)) (a := (526192977956070007 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (23232576075559363 / 40000000000000000)) (a := (131548244488989537 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy89_hz1 : B (982081 / 4000000) (982081 / 4000000) (((991 / 2000) : ℝ)^2) := bsq (bpoint ((991 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy89_hz2 : B (3017919 / 4000000) (3017919 / 4000000) ((1 : ℝ) - (((991 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy89_hz1 (by norm_num) (by norm_num)

theorem lowEnergy89_hz3 : B (217151984506243921 / 250000000000000000) (173721587604995137 / 200000000000000000) (√((1 : ℝ) - (((991 / 2000) : ℝ)^2))) := bsqrt lowEnergy89_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy89_hz4 : B (276486493891067111 / 1000000000000000000) (34560811736383389 / 125000000000000000) ((√((1 : ℝ) - (((991 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy89_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy89_hz5 : B (1029734390370027 / 3125000000000000) (329515004918443927 / 1000000000000000000) (((991 / 2000) : ℝ) * (kdot ((991 / 2000)))) := bmul (bpoint ((991 / 2000) : ℝ)) lowEnergy89_hz0 (by norm_num) (by norm_num)

theorem lowEnergy89_hz6 : B (606001498809475751 / 1000000000000000000) (606001498809511039 / 1000000000000000000) (((√((1 : ℝ) - (((991 / 2000) : ℝ)^2))) / Real.pi) + (((991 / 2000) : ℝ) * (kdot ((991 / 2000))))) := badd lowEnergy89_hz4 lowEnergy89_hz5 (by norm_num) (by norm_num)

theorem lowEnergy89_hz7 : B (606001498809475751 / 1000000000000000000) (606001498809511039 / 1000000000000000000) (kappa ((991 / 2000))) := by rw [kappa_eq]; exact lowEnergy89_hz6

theorem lowEnergy89_hz8 : B (708441389469403693 / 1000000000000000000) (708441389469403719 / 1000000000000000000) (kdot ((609030712287 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (123233607860942339 / 250000000000000000)) (a := (228989597233442271 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (98586886288753871 / 200000000000000000)) (a := (57247399308360563 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy89_hz9 : B (92729602127202643 / 250000000000000000) (370918408508810573 / 1000000000000000000) (((609030712287 / 1000000000000) : ℝ)^2) := bsq (bpoint ((609030712287 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy89_hz10 : B (629081591491189427 / 1000000000000000000) (157270397872797357 / 250000000000000000) ((1 : ℝ) - (((609030712287 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy89_hz9 (by norm_num) (by norm_num)

theorem lowEnergy89_hz11 : B (31725865573470223 / 40000000000000000) (793146639336755577 / 1000000000000000000) (√((1 : ℝ) - (((609030712287 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy89_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy89_hz12 : B (15779151030896171 / 62500000000000000) (252466416494338737 / 1000000000000000000) ((√((1 : ℝ) - (((609030712287 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy89_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy89_hz13 : B (6741602563158483 / 15625000000000000) (26966410252633933 / 62500000000000000) (((609030712287 / 1000000000000) : ℝ) * (kdot ((609030712287 / 1000000000000)))) := bmul (bpoint ((609030712287 / 1000000000000) : ℝ)) lowEnergy89_hz8 (by norm_num) (by norm_num)

theorem lowEnergy89_hz14 : B (42745561283530103 / 62500000000000000) (136785796107296333 / 200000000000000000) (((√((1 : ℝ) - (((609030712287 / 1000000000000) : ℝ)^2))) / Real.pi) + (((609030712287 / 1000000000000) : ℝ) * (kdot ((609030712287 / 1000000000000))))) := badd lowEnergy89_hz12 lowEnergy89_hz13 (by norm_num) (by norm_num)

theorem lowEnergy89_hz15 : B (42745561283530103 / 62500000000000000) (136785796107296333 / 200000000000000000) (kappa ((609030712287 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy89_hz14

theorem lowEnergy89 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (991 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (686748493389 / 1000000000000) := by
  have hk1 : kappa q ≤ (60600149881 / 100000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((991 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy89_hz7.2.trans (by norm_num))
  have hk2 : kappa ((609030712287 / 1000000000000) : ℝ) ≤ (683928980537 / 1000000000000) := lowEnergy89_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((4867889441 / 6250000000) : ℝ)) (R := ((194932083991 / 250000000000) : ℝ)) (Q2 := ((609030712287 / 1000000000000) : ℝ)) (T := ((808316593 / 976562500) : ℝ))
    (B := ((686748493389 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy90_hz0 : B (332415973159448007 / 500000000000000000) (83103993289871197 / 125000000000000000) (kdot ((99 / 200))) := by
    constructor
    · apply bkdot_lower (q := (290599656804885193 / 500000000000000000)) (a := (526480747581272869 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (116239862721954077 / 200000000000000000)) (a := (526480747581157319 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy90_hz1 : B (9801 / 40000) (9801 / 40000) (((99 / 200) : ℝ)^2) := bsq (bpoint ((99 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy90_hz2 : B (30199 / 40000) (30199 / 40000) ((1 : ℝ) - (((99 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy90_hz1 (by norm_num) (by norm_num)

theorem lowEnergy90_hz3 : B (434446486923303363 / 500000000000000000) (868892973846606727 / 1000000000000000000) (√((1 : ℝ) - (((99 / 200) : ℝ)^2))) := bsqrt lowEnergy90_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy90_hz4 : B (276577223611008791 / 1000000000000000000) (34572152951376099 / 125000000000000000) ((√((1 : ℝ) - (((99 / 200) : ℝ)^2))) / Real.pi) := bdiv lowEnergy90_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy90_hz5 : B (164545906713926763 / 500000000000000000) (329091813427889941 / 1000000000000000000) (((99 / 200) : ℝ) * (kdot ((99 / 200)))) := bmul (bpoint ((99 / 200) : ℝ)) lowEnergy90_hz0 (by norm_num) (by norm_num)

theorem lowEnergy90_hz6 : B (605669037038862317 / 1000000000000000000) (605669037038898733 / 1000000000000000000) (((√((1 : ℝ) - (((99 / 200) : ℝ)^2))) / Real.pi) + (((99 / 200) : ℝ) * (kdot ((99 / 200))))) := badd lowEnergy90_hz4 lowEnergy90_hz5 (by norm_num) (by norm_num)

theorem lowEnergy90_hz7 : B (605669037038862317 / 1000000000000000000) (605669037038898733 / 1000000000000000000) (kappa ((99 / 200))) := by rw [kappa_eq]; exact lowEnergy90_hz6

theorem lowEnergy90_hz8 : B (354153802831856373 / 500000000000000000) (708307605663712771 / 1000000000000000000) (kdot ((152174325889 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (30824729254949837 / 62500000000000000)) (a := (114547335394362131 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (493195668079197391 / 1000000000000000000)) (a := (229094670788724243 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy90_hz9 : B (37051240735634521 / 100000000000000000) (370512407356345211 / 1000000000000000000) (((152174325889 / 250000000000) : ℝ)^2) := bsq (bpoint ((152174325889 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy90_hz10 : B (629487592643654789 / 1000000000000000000) (62948759264365479 / 100000000000000000) ((1 : ℝ) - (((152174325889 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy90_hz9 (by norm_num) (by norm_num)

theorem lowEnergy90_hz11 : B (99175317670563103 / 125000000000000000) (396701270682252413 / 500000000000000000) (√((1 : ℝ) - (((152174325889 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy90_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy90_hz12 : B (1262739363198329 / 5000000000000000) (126273936319832901 / 500000000000000000) ((√((1 : ℝ) - (((152174325889 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy90_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy90_hz13 : B (215572464827854251 / 500000000000000000) (215572464827854259 / 500000000000000000) (((152174325889 / 250000000000) : ℝ) * (kdot ((152174325889 / 250000000000)))) := bmul (bpoint ((152174325889 / 250000000000) : ℝ)) lowEnergy90_hz8 (by norm_num) (by norm_num)

theorem lowEnergy90_hz14 : B (341846401147687151 / 500000000000000000) (8546160028692179 / 12500000000000000) (((√((1 : ℝ) - (((152174325889 / 250000000000) : ℝ)^2))) / Real.pi) + (((152174325889 / 250000000000) : ℝ) * (kdot ((152174325889 / 250000000000))))) := badd lowEnergy90_hz12 lowEnergy90_hz13 (by norm_num) (by norm_num)

theorem lowEnergy90_hz15 : B (341846401147687151 / 500000000000000000) (8546160028692179 / 12500000000000000) (kappa ((152174325889 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy90_hz14

theorem lowEnergy90 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (99 / 200)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (343255811921 / 500000000000) := by
  have hk1 : kappa q ≤ (605669037039 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((99 / 200) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy90_hz7.2.trans (by norm_num))
  have hk2 : kappa ((152174325889 / 250000000000) : ℝ) ≤ (85461600287 / 125000000000) := lowEnergy90_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((778648853489 / 1000000000000) : ℝ)) (R := ((779514878893 / 1000000000000) : ℝ)) (Q2 := ((152174325889 / 250000000000) : ℝ)) (T := ((827573263063 / 1000000000000) : ℝ))
    (B := ((343255811921 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy91_hz0 : B (83081100816667757 / 125000000000000000) (166162201633354511 / 250000000000000000) (kdot ((989 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (581584227879706397 / 1000000000000000000)) (a := (526768422883711031 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (145396056969926599 / 250000000000000000)) (a := (526768422883591671 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy91_hz1 : B (978121 / 4000000) (978121 / 4000000) (((989 / 2000) : ℝ)^2) := bsq (bpoint ((989 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy91_hz2 : B (3021879 / 4000000) (3021879 / 4000000) ((1 : ℝ) - (((989 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy91_hz1 (by norm_num) (by norm_num)

theorem lowEnergy91_hz3 : B (869177628566221209 / 1000000000000000000) (86917762856622121 / 100000000000000000) (√((1 : ℝ) - (((989 / 2000) : ℝ)^2))) := bsqrt lowEnergy91_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy91_hz4 : B (69166958005602739 / 250000000000000000) (276667832022410957 / 1000000000000000000) ((√((1 : ℝ) - (((989 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy91_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy91_hz5 : B (164334417415368823 / 500000000000000000) (328668834830775223 / 1000000000000000000) (((989 / 2000) : ℝ) * (kdot ((989 / 2000)))) := bmul (bpoint ((989 / 2000) : ℝ)) lowEnergy91_hz0 (by norm_num) (by norm_num)

theorem lowEnergy91_hz6 : B (302668333426574301 / 500000000000000000) (30266833342659309 / 50000000000000000) (((√((1 : ℝ) - (((989 / 2000) : ℝ)^2))) / Real.pi) + (((989 / 2000) : ℝ) * (kdot ((989 / 2000))))) := badd lowEnergy91_hz4 lowEnergy91_hz5 (by norm_num) (by norm_num)

theorem lowEnergy91_hz7 : B (302668333426574301 / 500000000000000000) (30266833342659309 / 50000000000000000) (kappa ((989 / 2000))) := by rw [kappa_eq]; exact lowEnergy91_hz6

theorem lowEnergy91_hz8 : B (354086950889229897 / 500000000000000000) (708173901778459821 / 1000000000000000000) (kdot ((60836398657 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (24672840138195021 / 50000000000000000)) (a := (458399363149282067 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (493456802763900419 / 1000000000000000000)) (a := (458399363149282027 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy91_hz9 : B (18505337007767157 / 50000000000000000) (370106740155343141 / 1000000000000000000) (((60836398657 / 100000000000) : ℝ)^2) := bsq (bpoint ((60836398657 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy91_hz10 : B (629893259844656859 / 1000000000000000000) (31494662992232843 / 50000000000000000) ((1 : ℝ) - (((60836398657 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy91_hz9 (by norm_num) (by norm_num)

theorem lowEnergy91_hz11 : B (49603634405839567 / 62500000000000000) (396829075246716537 / 500000000000000000) (√((1 : ℝ) - (((60836398657 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy91_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy91_hz12 : B (252629235552402489 / 1000000000000000000) (25262923555240249 / 100000000000000000) ((√((1 : ℝ) - (((60836398657 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy91_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy91_hz13 : B (430827498070775413 / 1000000000000000000) (43082749807077543 / 100000000000000000) (((60836398657 / 100000000000) : ℝ) * (kdot ((60836398657 / 100000000000)))) := bmul (bpoint ((60836398657 / 100000000000) : ℝ)) lowEnergy91_hz8 (by norm_num) (by norm_num)

theorem lowEnergy91_hz14 : B (341728366811588951 / 500000000000000000) (2135802292572431 / 3125000000000000) (((√((1 : ℝ) - (((60836398657 / 100000000000) : ℝ)^2))) / Real.pi) + (((60836398657 / 100000000000) : ℝ) * (kdot ((60836398657 / 100000000000))))) := badd lowEnergy91_hz12 lowEnergy91_hz13 (by norm_num) (by norm_num)

theorem lowEnergy91_hz15 : B (341728366811588951 / 500000000000000000) (2135802292572431 / 3125000000000000) (kappa ((60836398657 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy91_hz14

theorem lowEnergy91 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (989 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (137254972827 / 200000000000) := by
  have hk1 : kappa q ≤ (302668333427 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((989 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy91_hz7.2.trans (by norm_num))
  have hk2 : kappa ((60836398657 / 100000000000) : ℝ) ≤ (85432091703 / 125000000000) := lowEnergy91_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((97304424589 / 125000000000) : ℝ)) (R := ((194825355529 / 250000000000) : ℝ)) (Q2 := ((60836398657 / 100000000000) : ℝ)) (T := ((82743037653 / 100000000000) : ℝ))
    (B := ((137254972827 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy92_hz0 : B (664465726675952961 / 1000000000000000000) (664465726676031453 / 1000000000000000000) (kdot ((247 / 500))) := by
    constructor
    · apply bkdot_lower (q := (581969144951893033 / 1000000000000000000)) (a := (105411200810241591 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (72746143118986629 / 125000000000000000)) (a := (263528002025542331 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy92_hz1 : B (61009 / 250000) (61009 / 250000) (((247 / 500) : ℝ)^2) := bsq (bpoint ((247 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy92_hz2 : B (188991 / 250000) (188991 / 250000) ((1 : ℝ) - (((247 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy92_hz1 (by norm_num) (by norm_num)

theorem lowEnergy92_hz3 : B (86946190255812819 / 100000000000000000) (869461902558128191 / 1000000000000000000) (√((1 : ℝ) - (((247 / 500) : ℝ)^2))) := bsqrt lowEnergy92_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy92_hz4 : B (276758319244419879 / 1000000000000000000) (6918957981110497 / 25000000000000000) ((√((1 : ℝ) - (((247 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy92_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy92_hz5 : B (164123034488960381 / 500000000000000000) (164123034488979769 / 500000000000000000) (((247 / 500) : ℝ) * (kdot ((247 / 500)))) := bmul (bpoint ((247 / 500) : ℝ)) lowEnergy92_hz0 (by norm_num) (by norm_num)

theorem lowEnergy92_hz6 : B (605004388222340641 / 1000000000000000000) (302502194111189709 / 500000000000000000) (((√((1 : ℝ) - (((247 / 500) : ℝ)^2))) / Real.pi) + (((247 / 500) : ℝ) * (kdot ((247 / 500))))) := badd lowEnergy92_hz4 lowEnergy92_hz5 (by norm_num) (by norm_num)

theorem lowEnergy92_hz7 : B (605004388222340641 / 1000000000000000000) (302502194111189709 / 500000000000000000) (kappa ((247 / 500))) := by rw [kappa_eq]; exact lowEnergy92_hz6

theorem lowEnergy92_hz8 : B (177010069425211023 / 250000000000000000) (708040277700844119 / 1000000000000000000) (kdot ((608030761299 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (49371783566107749 / 100000000000000000)) (a := (458609259359572169 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (493717835661077489 / 1000000000000000000)) (a := (14331539354986629 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy92_hz9 : B (92425351671460379 / 250000000000000000) (369701406685841517 / 1000000000000000000) (((608030761299 / 1000000000000) : ℝ)^2) := bsq (bpoint ((608030761299 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy92_hz10 : B (630298593314158483 / 1000000000000000000) (157574648328539621 / 250000000000000000) ((1 : ℝ) - (((608030761299 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy92_hz9 (by norm_num) (by norm_num)

theorem lowEnergy92_hz11 : B (158782693428995401 / 200000000000000000) (793913467144977007 / 1000000000000000000) (√((1 : ℝ) - (((608030761299 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy92_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy92_hz12 : B (50542101073339253 / 200000000000000000) (126355252683348133 / 500000000000000000) ((√((1 : ℝ) - (((608030761299 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy92_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy92_hz13 : B (215255134540399803 / 500000000000000000) (53813783635099953 / 125000000000000000) (((608030761299 / 1000000000000) : ℝ) * (kdot ((608030761299 / 1000000000000)))) := bmul (bpoint ((608030761299 / 1000000000000) : ℝ)) lowEnergy92_hz8 (by norm_num) (by norm_num)

theorem lowEnergy92_hz14 : B (683220774447495871 / 1000000000000000000) (68322077444749589 / 100000000000000000) (((√((1 : ℝ) - (((608030761299 / 1000000000000) : ℝ)^2))) / Real.pi) + (((608030761299 / 1000000000000) : ℝ) * (kdot ((608030761299 / 1000000000000))))) := badd lowEnergy92_hz12 lowEnergy92_hz13 (by norm_num) (by norm_num)

theorem lowEnergy92_hz15 : B (683220774447495871 / 1000000000000000000) (68322077444749589 / 100000000000000000) (kappa ((608030761299 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy92_hz14

theorem lowEnergy92 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (247 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (343019107099 / 500000000000) := by
  have hk1 : kappa q ≤ (605004388223 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((247 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy92_hz7.2.trans (by norm_num))
  have hk2 : kappa ((608030761299 / 1000000000000) : ℝ) ≤ (42701298403 / 62500000000) := lowEnergy92_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((77822194021 / 100000000000) : ℝ)) (R := ((389543982807 / 500000000000) : ℝ)) (Q2 := ((608030761299 / 1000000000000) : ℝ)) (T := ((827287531611 / 1000000000000) : ℝ))
    (B := ((343019107099 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy93_hz0 : B (664282706627431371 / 1000000000000000000) (5189708645527441 / 7812500000000000) (kdot ((987 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (291177032539553747 / 500000000000000000)) (a := (131835872817788873 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (582354065079107493 / 1000000000000000000)) (a := (527343491271028139 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy93_hz1 : B (974169 / 4000000) (974169 / 4000000) (((987 / 2000) : ℝ)^2) := bsq (bpoint ((987 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy93_hz2 : B (3025831 / 4000000) (3025831 / 4000000) ((1 : ℝ) - (((987 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy93_hz1 (by norm_num) (by norm_num)

theorem lowEnergy93_hz3 : B (869745796195647041 / 1000000000000000000) (434872898097823521 / 500000000000000000) (√((1 : ℝ) - (((987 / 2000) : ℝ)^2))) := bsqrt lowEnergy93_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy93_hz4 : B (276848685395866807 / 1000000000000000000) (34606085674483351 / 125000000000000000) ((√((1 : ℝ) - (((987 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy93_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy93_hz5 : B (327823515720637381 / 1000000000000000000) (163911757860338697 / 500000000000000000) (((987 / 2000) : ℝ) * (kdot ((987 / 2000)))) := bmul (bpoint ((987 / 2000) : ℝ)) lowEnergy93_hz0 (by norm_num) (by norm_num)

theorem lowEnergy93_hz6 : B (151168050279126047 / 250000000000000000) (302336100558272101 / 500000000000000000) (((√((1 : ℝ) - (((987 / 2000) : ℝ)^2))) / Real.pi) + (((987 / 2000) : ℝ) * (kdot ((987 / 2000))))) := badd lowEnergy93_hz4 lowEnergy93_hz5 (by norm_num) (by norm_num)

theorem lowEnergy93_hz7 : B (151168050279126047 / 250000000000000000) (302336100558272101 / 500000000000000000) (kappa ((987 / 2000))) := by rw [kappa_eq]; exact lowEnergy93_hz6

theorem lowEnergy93_hz8 : B (707906733317531197 / 1000000000000000000) (28316269332701249 / 40000000000000000) (kdot ((607697627711 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (98795753387018873 / 200000000000000000)) (a := (229409515193172077 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (123494691733773591 / 250000000000000000)) (a := (28676189399146507 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy93_hz9 : B (73859281345115431 / 200000000000000000) (92324101681394289 / 250000000000000000) (((607697627711 / 1000000000000) : ℝ)^2) := bsq (bpoint ((607697627711 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy93_hz10 : B (157675898318605711 / 250000000000000000) (126140718654884569 / 200000000000000000) ((1 : ℝ) - (((607697627711 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy93_hz9 (by norm_num) (by norm_num)

theorem lowEnergy93_hz11 : B (31766739669646247 / 40000000000000000) (49635530733822261 / 62500000000000000) (√((1 : ℝ) - (((607697627711 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy93_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy93_hz12 : B (252791682216880123 / 1000000000000000000) (2022333457735041 / 8000000000000000) ((√((1 : ℝ) - (((607697627711 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy93_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy93_hz13 : B (430193242477707233 / 1000000000000000000) (430193242477707251 / 1000000000000000000) (((607697627711 / 1000000000000) : ℝ) * (kdot ((607697627711 / 1000000000000)))) := bmul (bpoint ((607697627711 / 1000000000000) : ℝ)) lowEnergy93_hz8 (by norm_num) (by norm_num)

theorem lowEnergy93_hz14 : B (170746231173646839 / 250000000000000000) (42686557793411711 / 62500000000000000) (((√((1 : ℝ) - (((607697627711 / 1000000000000) : ℝ)^2))) / Real.pi) + (((607697627711 / 1000000000000) : ℝ) * (kdot ((607697627711 / 1000000000000))))) := badd lowEnergy93_hz12 lowEnergy93_hz13 (by norm_num) (by norm_num)

theorem lowEnergy93_hz15 : B (170746231173646839 / 250000000000000000) (42686557793411711 / 62500000000000000) (kappa ((607697627711 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy93_hz14

theorem lowEnergy93 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (987 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (685801673953 / 1000000000000) := by
  have hk1 : kappa q ≤ (604672201117 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((987 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy93_hz7.2.trans (by norm_num))
  have hk2 : kappa ((607697627711 / 1000000000000) : ℝ) ≤ (136596984939 / 200000000000) := lowEnergy93_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((778008483963 / 1000000000000) : ℝ)) (R := ((778874509367 / 1000000000000) : ℝ)) (Q2 := ((607697627711 / 1000000000000) : ℝ)) (T := ((413572364141 / 500000000000) : ℝ))
    (B := ((685801673953 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy94_hz0 : B (664099746268753713 / 1000000000000000000) (41506234141802341 / 62500000000000000) (kdot ((493 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (291369494256902447 / 500000000000000000)) (a := (105526176946103087 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (582738988513804893 / 1000000000000000000)) (a := (131907721182595973 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy94_hz1 : B (243049 / 1000000) (243049 / 1000000) (((493 / 1000) : ℝ)^2) := bsq (bpoint ((493 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy94_hz2 : B (756951 / 1000000) (756951 / 1000000) ((1 : ℝ) - (((493 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy94_hz1 (by norm_num) (by norm_num)

theorem lowEnergy94_hz3 : B (174005861970222141 / 200000000000000000) (435014654925555353 / 500000000000000000) (√((1 : ℝ) - (((493 / 1000) : ℝ)^2))) := bsqrt lowEnergy94_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy94_hz4 : B (69234732648817249 / 250000000000000000) (276938930595268997 / 1000000000000000000) ((√((1 : ℝ) - (((493 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy94_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy94_hz5 : B (16370058745524779 / 50000000000000000) (163700587455268433 / 500000000000000000) (((493 / 1000) : ℝ) * (kdot ((493 / 1000)))) := bmul (bpoint ((493 / 1000) : ℝ)) lowEnergy94_hz0 (by norm_num) (by norm_num)

theorem lowEnergy94_hz6 : B (18885628297055143 / 31250000000000000) (604340105505805863 / 1000000000000000000) (((√((1 : ℝ) - (((493 / 1000) : ℝ)^2))) / Real.pi) + (((493 / 1000) : ℝ) * (kdot ((493 / 1000))))) := badd lowEnergy94_hz4 lowEnergy94_hz5 (by norm_num) (by norm_num)

theorem lowEnergy94_hz7 : B (18885628297055143 / 31250000000000000) (604340105505805863 / 1000000000000000000) (kappa ((493 / 1000))) := by rw [kappa_eq]; exact lowEnergy94_hz6

theorem lowEnergy94_hz8 : B (707773268516656741 / 1000000000000000000) (70777326851665677 / 100000000000000000) (kdot ((607364585777 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (49423959674756839 / 100000000000000000)) (a := (459028676405314161 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (494239596747568389 / 1000000000000000000)) (a := (229514338202657059 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy94_hz9 : B (36889174005606679 / 100000000000000000) (368891740056066791 / 1000000000000000000) (((607364585777 / 1000000000000) : ℝ)^2) := bsq (bpoint ((607364585777 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy94_hz10 : B (631108259943933209 / 1000000000000000000) (63110825994393321 / 100000000000000000) ((1 : ℝ) - (((607364585777 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy94_hz9 (by norm_num) (by norm_num)

theorem lowEnergy94_hz11 : B (39721161235037339 / 50000000000000000) (794423224700746781 / 1000000000000000000) (√((1 : ℝ) - (((607364585777 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy94_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy94_hz12 : B (252872766236254669 / 1000000000000000000) (25287276623625467 / 100000000000000000) ((√((1 : ℝ) - (((607364585777 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy94_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy94_hz13 : B (53734552257081577 / 125000000000000000) (85975283611330527 / 200000000000000000) (((607364585777 / 1000000000000) : ℝ) * (kdot ((607364585777 / 1000000000000)))) := bmul (bpoint ((607364585777 / 1000000000000) : ℝ)) lowEnergy94_hz8 (by norm_num) (by norm_num)

theorem lowEnergy94_hz14 : B (136549836858581457 / 200000000000000000) (136549836858581461 / 200000000000000000) (((√((1 : ℝ) - (((607364585777 / 1000000000000) : ℝ)^2))) / Real.pi) + (((607364585777 / 1000000000000) : ℝ) * (kdot ((607364585777 / 1000000000000))))) := badd lowEnergy94_hz12 lowEnergy94_hz13 (by norm_num) (by norm_num)

theorem lowEnergy94_hz15 : B (136549836858581457 / 200000000000000000) (136549836858581461 / 200000000000000000) (kappa ((607364585777 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy94_hz14

theorem lowEnergy94 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (493 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (171391310833 / 250000000000) := by
  have hk1 : kappa q ≤ (302170052753 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((493 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy94_hz7.2.trans (by norm_num))
  have hk2 : kappa ((607364585777 / 1000000000000) : ℝ) ≤ (682749184293 / 1000000000000) := lowEnergy94_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((48612189247 / 62500000000) : ℝ)) (R := ((194665263339 / 250000000000) : ℝ)) (Q2 := ((607364585777 / 1000000000000) : ℝ)) (T := ((413500983261 / 500000000000) : ℝ))
    (B := ((171391310833 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy95_hz0 : B (331958422740584609 / 500000000000000000) (165979211370313929 / 250000000000000000) (kdot ((197 / 400))) := by
    constructor
    · apply bkdot_lower (q := (116624783101623977 / 200000000000000000)) (a := (131979546153955263 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (145780978877029971 / 250000000000000000)) (a := (527918184615685183 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy95_hz1 : B (38809 / 160000) (38809 / 160000) (((197 / 400) : ℝ)^2) := bsq (bpoint ((197 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy95_hz2 : B (121191 / 160000) (121191 / 160000) ((1 : ℝ) - (((197 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy95_hz1 (by norm_num) (by norm_num)

theorem lowEnergy95_hz3 : B (870312443895868927 / 1000000000000000000) (1699828991984119 / 1953125000000000) (√((1 : ℝ) - (((197 / 400) : ℝ)^2))) := bsqrt lowEnergy95_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy95_hz4 : B (138514527480415371 / 500000000000000000) (277029054960830743 / 1000000000000000000) ((√((1 : ℝ) - (((197 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy95_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy95_hz5 : B (326979046399475839 / 1000000000000000000) (326979046399518441 / 1000000000000000000) (((197 / 400) : ℝ) * (kdot ((197 / 400)))) := bmul (bpoint ((197 / 400) : ℝ)) lowEnergy95_hz0 (by norm_num) (by norm_num)

theorem lowEnergy95_hz6 : B (604008101360306581 / 1000000000000000000) (147462915371179 / 244140625000000) (((√((1 : ℝ) - (((197 / 400) : ℝ)^2))) / Real.pi) + (((197 / 400) : ℝ) * (kdot ((197 / 400))))) := badd lowEnergy95_hz4 lowEnergy95_hz5 (by norm_num) (by norm_num)

theorem lowEnergy95_hz7 : B (604008101360306581 / 1000000000000000000) (147462915371179 / 244140625000000) (kappa ((197 / 400))) := by rw [kappa_eq]; exact lowEnergy95_hz6

theorem lowEnergy95_hz8 : B (707639883186621929 / 1000000000000000000) (353819941593310979 / 500000000000000000) (kdot ((151757908867 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (123625081314930087 / 250000000000000000)) (a := (45923819759178117 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (494500325259720347 / 1000000000000000000)) (a := (229619098795890563 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy95_hz9 : B (73697481291790967 / 200000000000000000) (92121851614738709 / 250000000000000000) (((151757908867 / 250000000000) : ℝ)^2) := bsq (bpoint ((151757908867 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy95_hz10 : B (157878148385261291 / 250000000000000000) (126302518708209033 / 200000000000000000) ((1 : ℝ) - (((151757908867 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy95_hz9 (by norm_num) (by norm_num)

theorem lowEnergy95_hz11 : B (397338833220793171 / 500000000000000000) (99334708305198293 / 125000000000000000) (√((1 : ℝ) - (((151757908867 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy95_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy95_hz12 : B (63238439389455429 / 250000000000000000) (252953757557821717 / 1000000000000000000) ((√((1 : ℝ) - (((151757908867 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy95_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy95_hz13 : B (85911959122631917 / 200000000000000000) (429559795613159603 / 1000000000000000000) (((151757908867 / 250000000000) : ℝ) * (kdot ((151757908867 / 250000000000)))) := bmul (bpoint ((151757908867 / 250000000000) : ℝ)) lowEnergy95_hz8 (by norm_num) (by norm_num)

theorem lowEnergy95_hz14 : B (682513553170981301 / 1000000000000000000) (17062838829274533 / 25000000000000000) (((√((1 : ℝ) - (((151757908867 / 250000000000) : ℝ)^2))) / Real.pi) + (((151757908867 / 250000000000) : ℝ) * (kdot ((151757908867 / 250000000000))))) := badd lowEnergy95_hz12 lowEnergy95_hz13 (by norm_num) (by norm_num)

theorem lowEnergy95_hz15 : B (682513553170981301 / 1000000000000000000) (17062838829274533 / 25000000000000000) (kappa ((151757908867 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy95_hz14

theorem lowEnergy95 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (197 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (685328922263 / 1000000000000) := by
  have hk1 : kappa q ≤ (604008101361 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((197 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy95_hz7.2.trans (by norm_num))
  have hk2 : kappa ((151757908867 / 250000000000) : ℝ) ≤ (682513553171 / 1000000000000) := lowEnergy95_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((777581572159 / 1000000000000) : ℝ)) (R := ((778447597563 / 1000000000000) : ℝ)) (Q2 := ((151757908867 / 250000000000) : ℝ)) (T := ((82685924631 / 100000000000) : ℝ))
    (B := ((685328922263 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy96_hz0 : B (132746800829239791 / 200000000000000000) (82966750518286037 / 125000000000000000) (kdot ((123 / 250))) := by
    constructor
    · apply bkdot_lower (q := (583508846313868283 / 1000000000000000000)) (a := (528205391113178617 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (291754423156934141 / 500000000000000000)) (a := (264102695556519141 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy96_hz1 : B (15129 / 62500) (15129 / 62500) (((123 / 250) : ℝ)^2) := bsq (bpoint ((123 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy96_hz2 : B (47371 / 62500) (47371 / 62500) ((1 : ℝ) - (((123 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy96_hz1 (by norm_num) (by norm_num)

theorem lowEnergy96_hz3 : B (870595198700291477 / 1000000000000000000) (435297599350145739 / 500000000000000000) (√((1 : ℝ) - (((123 / 250) : ℝ)^2))) := bsqrt lowEnergy96_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy96_hz4 : B (69279764652611101 / 250000000000000000) (55423811722088881 / 200000000000000000) ((√((1 : ℝ) - (((123 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy96_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy96_hz5 : B (65311426007985977 / 200000000000000000) (163278565019986921 / 500000000000000000) (((123 / 250) : ℝ) * (kdot ((123 / 250)))) := bmul (bpoint ((123 / 250) : ℝ)) lowEnergy96_hz0 (by norm_num) (by norm_num)

theorem lowEnergy96_hz6 : B (603676188650374289 / 1000000000000000000) (603676188650418247 / 1000000000000000000) (((√((1 : ℝ) - (((123 / 250) : ℝ)^2))) / Real.pi) + (((123 / 250) : ℝ) * (kdot ((123 / 250))))) := badd lowEnergy96_hz4 lowEnergy96_hz5 (by norm_num) (by norm_num)

theorem lowEnergy96_hz7 : B (603676188650374289 / 1000000000000000000) (603676188650418247 / 1000000000000000000) (kappa ((123 / 250))) := by rw [kappa_eq]; exact lowEnergy96_hz6

theorem lowEnergy96_hz8 : B (707506577215291771 / 1000000000000000000) (3537532886076459 / 5000000000000000) (kdot ((606698776753 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (494760952633941759 / 1000000000000000000)) (a := (57430949265235801 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (247380476316970879 / 500000000000000000)) (a := (459447594121886363 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy96_hz9 : B (368083405713586533 / 1000000000000000000) (184041702856793267 / 500000000000000000) (((606698776753 / 1000000000000) : ℝ)^2) := bsq (bpoint ((606698776753 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy96_hz10 : B (315958297143206733 / 500000000000000000) (631916594286413467 / 1000000000000000000) ((1 : ℝ) - (((606698776753 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy96_hz9 (by norm_num) (by norm_num)

theorem lowEnergy96_hz11 : B (198732954345525799 / 250000000000000000) (397465908691051599 / 500000000000000000) (√((1 : ℝ) - (((606698776753 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy96_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy96_hz12 : B (253034656314771139 / 1000000000000000000) (12651732815738557 / 50000000000000000) ((√((1 : ℝ) - (((606698776753 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy96_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy96_hz13 : B (214621687470609729 / 500000000000000000) (429243374941219477 / 1000000000000000000) (((606698776753 / 1000000000000) : ℝ) * (kdot ((606698776753 / 1000000000000)))) := bmul (bpoint ((606698776753 / 1000000000000) : ℝ)) lowEnergy96_hz8 (by norm_num) (by norm_num)

theorem lowEnergy96_hz14 : B (682278031255990597 / 1000000000000000000) (682278031255990617 / 1000000000000000000) (((√((1 : ℝ) - (((606698776753 / 1000000000000) : ℝ)^2))) / Real.pi) + (((606698776753 / 1000000000000) : ℝ) * (kdot ((606698776753 / 1000000000000))))) := badd lowEnergy96_hz12 lowEnergy96_hz13 (by norm_num) (by norm_num)

theorem lowEnergy96_hz15 : B (682278031255990597 / 1000000000000000000) (682278031255990617 / 1000000000000000000) (kappa ((606698776753 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy96_hz14

theorem lowEnergy96 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (685092710671 / 1000000000000) := by
  have hk1 : kappa q ≤ (603676188651 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((123 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy96_hz7.2.trans (by norm_num))
  have hk2 : kappa ((606698776753 / 1000000000000) : ℝ) ≤ (85284753907 / 125000000000) := lowEnergy96_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((155473623313 / 200000000000) : ℝ)) (R := ((778234141969 / 1000000000000) : ℝ)) (Q2 := ((606698776753 / 1000000000000) : ℝ)) (T := ((413358283811 / 500000000000) : ℝ))
    (B := ((685092710671 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy97_hz0 : B (663551222145634853 / 1000000000000000000) (663551222145727127 / 1000000000000000000) (kdot ((983 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (583893781182548681 / 1000000000000000000)) (a := (132123126102067233 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (14597344529563717 / 25000000000000000)) (a := (528492504408123989 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy97_hz1 : B (966289 / 4000000) (966289 / 4000000) (((983 / 2000) : ℝ)^2) := bsq (bpoint ((983 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy97_hz2 : B (3033711 / 4000000) (3033711 / 4000000) ((1 : ℝ) - (((983 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy97_hz1 (by norm_num) (by norm_num)

theorem lowEnergy97_hz3 : B (217719393658442839 / 250000000000000000) (870877574633771357 / 1000000000000000000) (√((1 : ℝ) - (((983 / 2000) : ℝ)^2))) := bsqrt lowEnergy97_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy97_hz4 : B (138604470830845713 / 500000000000000000) (277208941661691427 / 1000000000000000000) ((√((1 : ℝ) - (((983 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy97_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy97_hz5 : B (32613542568457953 / 100000000000000000) (326135425684624883 / 1000000000000000000) (((983 / 2000) : ℝ) * (kdot ((983 / 2000)))) := bmul (bpoint ((983 / 2000) : ℝ)) lowEnergy97_hz0 (by norm_num) (by norm_num)

theorem lowEnergy97_hz6 : B (150836091836567739 / 250000000000000000) (60334436734631631 / 100000000000000000) (((√((1 : ℝ) - (((983 / 2000) : ℝ)^2))) / Real.pi) + (((983 / 2000) : ℝ) * (kdot ((983 / 2000))))) := badd lowEnergy97_hz4 lowEnergy97_hz5 (by norm_num) (by norm_num)

theorem lowEnergy97_hz7 : B (150836091836567739 / 250000000000000000) (60334436734631631 / 100000000000000000) (kappa ((983 / 2000))) := by rw [kappa_eq]; exact lowEnergy97_hz6

theorem lowEnergy97_hz8 : B (14147467009831933 / 20000000000000000) (17684333762289917 / 25000000000000000) (kdot ((606366009603 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (495021479030663919 / 1000000000000000000)) (a := (229828433085048811 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (247510739515331959 / 500000000000000000)) (a := (57457108271262197 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy97_hz9 : B (22979983600116593 / 62500000000000000) (367679737601865489 / 1000000000000000000) (((606366009603 / 1000000000000) : ℝ)^2) := bsq (bpoint ((606366009603 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy97_hz10 : B (632320262398134511 / 1000000000000000000) (39520016399883407 / 62500000000000000) ((1 : ℝ) - (((606366009603 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy97_hz9 (by norm_num) (by norm_num)

theorem lowEnergy97_hz11 : B (397592838969131369 / 500000000000000000) (795185677938262739 / 1000000000000000000) (√((1 : ℝ) - (((606366009603 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy97_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy97_hz12 : B (63278865659877209 / 250000000000000000) (126557731319754419 / 500000000000000000) ((√((1 : ℝ) - (((606366009603 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy97_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy97_hz13 : B (428927155837093779 / 1000000000000000000) (214463577918546899 / 500000000000000000) (((606366009603 / 1000000000000) : ℝ) * (kdot ((606366009603 / 1000000000000)))) := bmul (bpoint ((606366009603 / 1000000000000) : ℝ)) lowEnergy97_hz8 (by norm_num) (by norm_num)

theorem lowEnergy97_hz14 : B (136408523695320523 / 200000000000000000) (170510654619150659 / 250000000000000000) (((√((1 : ℝ) - (((606366009603 / 1000000000000) : ℝ)^2))) / Real.pi) + (((606366009603 / 1000000000000) : ℝ) * (kdot ((606366009603 / 1000000000000))))) := badd lowEnergy97_hz12 lowEnergy97_hz13 (by norm_num) (by norm_num)

theorem lowEnergy97_hz15 : B (136408523695320523 / 200000000000000000) (170510654619150659 / 250000000000000000) (kappa ((606366009603 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy97_hz14

theorem lowEnergy97 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (983 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (342428304243 / 500000000000) := by
  have hk1 : kappa q ≤ (603344367347 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((983 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy97_hz7.2.trans (by norm_num))
  have hk2 : kappa ((606366009603 / 1000000000000) : ℝ) ≤ (682042618477 / 1000000000000) := lowEnergy97_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((15543093223 / 20000000000) : ℝ)) (R := ((389010343277 / 500000000000) : ℝ)) (Q2 := ((606366009603 / 1000000000000) : ℝ)) (T := ((826573930437 / 1000000000000) : ℝ))
    (B := ((342428304243 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy98_hz0 : B (41460531210096171 / 62500000000000000) (663368499361634039 / 1000000000000000000) (kdot ((491 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (292139360182672029 / 500000000000000000)) (a := (33048720292896803 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (584278720365344057 / 1000000000000000000)) (a := (132194881171549787 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy98_hz1 : B (241081 / 1000000) (241081 / 1000000) (((491 / 1000) : ℝ)^2) := bsq (bpoint ((491 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy98_hz2 : B (758919 / 1000000) (758919 / 1000000) ((1 : ℝ) - (((491 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy98_hz1 (by norm_num) (by norm_num)

theorem lowEnergy98_hz3 : B (871159572064727989 / 1000000000000000000) (87115957206472799 / 100000000000000000) (√((1 : ℝ) - (((491 / 1000) : ℝ)^2))) := bsqrt lowEnergy98_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy98_hz4 : B (277298704231843353 / 1000000000000000000) (138649352115921677 / 500000000000000000) ((√((1 : ℝ) - (((491 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy98_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy98_hz5 : B (325713933186515519 / 1000000000000000000) (162856966593281157 / 500000000000000000) (((491 / 1000) : ℝ) * (kdot ((491 / 1000)))) := bmul (bpoint ((491 / 1000) : ℝ)) lowEnergy98_hz0 (by norm_num) (by norm_num)

theorem lowEnergy98_hz6 : B (75376579677294859 / 125000000000000000) (150753159354601417 / 250000000000000000) (((√((1 : ℝ) - (((491 / 1000) : ℝ)^2))) / Real.pi) + (((491 / 1000) : ℝ) * (kdot ((491 / 1000))))) := badd lowEnergy98_hz4 lowEnergy98_hz5 (by norm_num) (by norm_num)

theorem lowEnergy98_hz7 : B (75376579677294859 / 125000000000000000) (150753159354601417 / 250000000000000000) (kappa ((491 / 1000))) := by rw [kappa_eq]; exact lowEnergy98_hz6

theorem lowEnergy98_hz8 : B (35362010145196473 / 50000000000000000) (707240202903929491 / 1000000000000000000) (kdot ((606033333987 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (495281904611491271 / 1000000000000000000)) (a := (229933006955863423 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (49528190461149127 / 100000000000000000)) (a := (229933006955863399 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy98_hz9 : B (367276401903398689 / 1000000000000000000) (36727640190339869 / 100000000000000000) (((606033333987 / 1000000000000) : ℝ)^2) := bsq (bpoint ((606033333987 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy98_hz10 : B (63272359809660131 / 100000000000000000) (632723598096601311 / 1000000000000000000) ((1 : ℝ) - (((606033333987 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy98_hz9 (by norm_num) (by norm_num)

theorem lowEnergy98_hz11 : B (397719624263312317 / 500000000000000000) (159087849705324927 / 200000000000000000) (√((1 : ℝ) - (((606033333987 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy98_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy98_hz12 : B (63299044166157467 / 250000000000000000) (25319617666462987 / 100000000000000000) ((√((1 : ℝ) - (((606033333987 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy98_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy98_hz13 : B (428611138095510729 / 1000000000000000000) (428611138095510749 / 1000000000000000000) (((606033333987 / 1000000000000) : ℝ) * (kdot ((606033333987 / 1000000000000)))) := bmul (bpoint ((606033333987 / 1000000000000) : ℝ)) lowEnergy98_hz8 (by norm_num) (by norm_num)

theorem lowEnergy98_hz14 : B (681807314760140597 / 1000000000000000000) (681807314760140619 / 1000000000000000000) (((√((1 : ℝ) - (((606033333987 / 1000000000000) : ℝ)^2))) / Real.pi) + (((606033333987 / 1000000000000) : ℝ) * (kdot ((606033333987 / 1000000000000))))) := badd lowEnergy98_hz12 lowEnergy98_hz13 (by norm_num) (by norm_num)

theorem lowEnergy98_hz15 : B (681807314760140597 / 1000000000000000000) (681807314760140619 / 1000000000000000000) (kappa ((606033333987 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy98_hz14

theorem lowEnergy98 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (491 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (171155153909 / 250000000000) := by
  have hk1 : kappa q ≤ (603012637419 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((491 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy98_hz7.2.trans (by norm_num))
  have hk2 : kappa ((606033333987 / 1000000000000) : ℝ) ≤ (681807314761 / 1000000000000) := lowEnergy98_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((97117650737 / 125000000000) : ℝ)) (R := ((7778072313 / 10000000000) : ℝ)) (Q2 := ((606033333987 / 1000000000000) : ℝ)) (T := ((826431334733 / 1000000000000) : ℝ))
    (B := ((171155153909 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy99_hz0 : B (82898229459530171 / 125000000000000000) (663185835676339797 / 1000000000000000000) (kdot ((981 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (73082958014140423 / 125000000000000000)) (a := (529066452132252773 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (584663664113123383 / 1000000000000000000)) (a := (529066452132098163 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy99_hz1 : B (962361 / 4000000) (962361 / 4000000) (((981 / 2000) : ℝ)^2) := bsq (bpoint ((981 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy99_hz2 : B (3037639 / 4000000) (3037639 / 4000000) ((1 : ℝ) - (((981 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy99_hz1 (by norm_num) (by norm_num)

theorem lowEnergy99_hz3 : B (871441191360610403 / 1000000000000000000) (217860297840152601 / 250000000000000000) (√((1 : ℝ) - (((981 / 2000) : ℝ)^2))) := bsqrt lowEnergy99_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy99_hz4 : B (69347086609465711 / 250000000000000000) (55477669287572569 / 200000000000000000) ((√((1 : ℝ) - (((981 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy99_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy99_hz5 : B (325292652399196391 / 1000000000000000000) (325292652399244671 / 1000000000000000000) (((981 / 2000) : ℝ) * (kdot ((981 / 2000)))) := bmul (bpoint ((981 / 2000) : ℝ)) lowEnergy99_hz0 (by norm_num) (by norm_num)

theorem lowEnergy99_hz6 : B (120536199767411847 / 200000000000000000) (150670249709276879 / 250000000000000000) (((√((1 : ℝ) - (((981 / 2000) : ℝ)^2))) / Real.pi) + (((981 / 2000) : ℝ) * (kdot ((981 / 2000))))) := badd lowEnergy99_hz4 lowEnergy99_hz5 (by norm_num) (by norm_num)

theorem lowEnergy99_hz7 : B (120536199767411847 / 200000000000000000) (150670249709276879 / 250000000000000000) (kappa ((981 / 2000))) := by rw [kappa_eq]; exact lowEnergy99_hz6

theorem lowEnergy99_hz8 : B (707107134342946267 / 1000000000000000000) (707107134342946299 / 1000000000000000000) (kdot ((605700749879 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (495542229533723073 / 1000000000000000000)) (a := (57509379689816391 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (7742847336464423 / 15625000000000000)) (a := (460075037518531079 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy99_hz9 : B (183436699201991459 / 500000000000000000) (366873398403982919 / 1000000000000000000) (((605700749879 / 1000000000000) : ℝ)^2) := bsq (bpoint ((605700749879 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy99_hz10 : B (633126601596017081 / 1000000000000000000) (316563300798008541 / 500000000000000000) ((1 : ℝ) - (((605700749879 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy99_hz9 (by norm_num) (by norm_num)

theorem lowEnergy99_hz11 : B (795692529559010677 / 1000000000000000000) (795692529559010679 / 1000000000000000000) (√((1 : ℝ) - (((605700749879 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy99_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy99_hz12 : B (253276798521221183 / 1000000000000000000) (3957449976894081 / 15625000000000000) ((√((1 : ℝ) - (((605700749879 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy99_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy99_hz13 : B (428295321516313347 / 1000000000000000000) (53536915189539171 / 125000000000000000) (((605700749879 / 1000000000000) : ℝ) * (kdot ((605700749879 / 1000000000000)))) := bmul (bpoint ((605700749879 / 1000000000000) : ℝ)) lowEnergy99_hz8 (by norm_num) (by norm_num)

theorem lowEnergy99_hz14 : B (68157212003753453 / 100000000000000000) (85196515004691819 / 125000000000000000) (((√((1 : ℝ) - (((605700749879 / 1000000000000) : ℝ)^2))) / Real.pi) + (((605700749879 / 1000000000000) : ℝ) * (kdot ((605700749879 / 1000000000000))))) := badd lowEnergy99_hz12 lowEnergy99_hz13 (by norm_num) (by norm_num)

theorem lowEnergy99_hz15 : B (68157212003753453 / 100000000000000000) (85196515004691819 / 125000000000000000) (kappa ((605700749879 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy99_hz14

theorem lowEnergy99 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (981 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (42774045753 / 62500000000) := by
  have hk1 : kappa q ≤ (301340499419 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((981 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy99_hz7.2.trans (by norm_num))
  have hk2 : kappa ((605700749879 / 1000000000000) : ℝ) ≤ (340786060019 / 500000000000) := lowEnergy99_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((155345550157 / 200000000000) : ℝ)) (R := ((777593776189 / 1000000000000) : ℝ)) (Q2 := ((605700749879 / 1000000000000) : ℝ)) (T := ((826288780487 / 1000000000000) : ℝ))
    (B := ((42774045753 / 62500000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy100_hz0 : B (331501615486170743 / 500000000000000000) (331501615486221571 / 500000000000000000) (kdot ((49 / 100))) := by
    constructor
    · apply bkdot_lower (q := (117009722535288643 / 200000000000000000)) (a := (529353286930394177 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (292524306338221607 / 500000000000000000)) (a := (529353286930234499 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy100_hz1 : B (2401 / 10000) (2401 / 10000) (((49 / 100) : ℝ)^2) := bsq (bpoint ((49 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy100_hz2 : B (7599 / 10000) (7599 / 10000) ((1 : ℝ) - (((49 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy100_hz1 (by norm_num) (by norm_num)

theorem lowEnergy100_hz3 : B (87172243288790039 / 100000000000000000) (871722432887900391 / 1000000000000000000) (√((1 : ℝ) - (((49 / 100) : ℝ)^2))) := bsqrt lowEnergy100_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy100_hz4 : B (11099114735856187 / 40000000000000000) (69369467099101169 / 250000000000000000) ((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) := bdiv lowEnergy100_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy100_hz5 : B (10152236974263979 / 31250000000000000) (16243579158824857 / 50000000000000000) (((49 / 100) : ℝ) * (kdot ((49 / 100)))) := bmul (bpoint ((49 / 100) : ℝ)) lowEnergy100_hz0 (by norm_num) (by norm_num)

theorem lowEnergy100_hz6 : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) + (((49 / 100) : ℝ) * (kdot ((49 / 100))))) := badd lowEnergy100_hz4 lowEnergy100_hz5 (by norm_num) (by norm_num)

theorem lowEnergy100_hz7 : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (kappa ((49 / 100))) := by rw [kappa_eq]; exact lowEnergy100_hz6

theorem lowEnergy100_hz8 : B (353487072347781761 / 500000000000000000) (141394828939112711 / 200000000000000000) (kdot ((605368257243 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (99160490792419199 / 200000000000000000)) (a := (115070984292035423 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (247901226981047997 / 500000000000000000)) (a := (230141968584070821 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy100_hz9 : B (366470726877427021 / 1000000000000000000) (183235363438713511 / 500000000000000000) (((605368257243 / 1000000000000) : ℝ)^2) := bsq (bpoint ((605368257243 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy100_hz10 : B (316764636561286489 / 500000000000000000) (633529273122572979 / 1000000000000000000) ((1 : ℝ) - (((605368257243 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy100_hz9 (by norm_num) (by norm_num)

theorem lowEnergy100_hz11 : B (397972760726966393 / 500000000000000000) (198986380363483197 / 250000000000000000) (√((1 : ℝ) - (((605368257243 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy100_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy100_hz12 : B (253357328342499261 / 1000000000000000000) (126678664171249631 / 500000000000000000) ((√((1 : ℝ) - (((605368257243 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy100_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy100_hz13 : B (213989852945106901 / 500000000000000000) (427979705890213823 / 1000000000000000000) (((605368257243 / 1000000000000) : ℝ) * (kdot ((605368257243 / 1000000000000)))) := bmul (bpoint ((605368257243 / 1000000000000) : ℝ)) lowEnergy100_hz8 (by norm_num) (by norm_num)

theorem lowEnergy100_hz14 : B (681337034232713063 / 1000000000000000000) (136267406846542617 / 200000000000000000) (((√((1 : ℝ) - (((605368257243 / 1000000000000) : ℝ)^2))) / Real.pi) + (((605368257243 / 1000000000000) : ℝ) * (kdot ((605368257243 / 1000000000000))))) := badd lowEnergy100_hz12 lowEnergy100_hz13 (by norm_num) (by norm_num)

theorem lowEnergy100_hz15 : B (681337034232713063 / 1000000000000000000) (136267406846542617 / 200000000000000000) (kappa ((605368257243 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy100_hz14

theorem lowEnergy100 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (49 / 100)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (684148957649 / 1000000000000) := by
  have hk1 : kappa q ≤ (602349451573 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((49 / 100) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy100_hz7.2.trans (by norm_num))
  have hk2 : kappa ((605368257243 / 1000000000000) : ℝ) ≤ (681337034233 / 1000000000000) := lowEnergy100_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((155302859159 / 200000000000) : ℝ)) (R := ((777380321199 / 1000000000000) : ℝ)) (Q2 := ((605368257243 / 1000000000000) : ℝ)) (T := ((826146267677 / 1000000000000) : ℝ))
    (B := ((684148957649 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy101_hz0 : B (82852585641588107 / 125000000000000000) (662820685132809841 / 1000000000000000000) (kdot ((979 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (292716783152774643 / 500000000000000000)) (a := (529640029264767087 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (117086713261109857 / 200000000000000000)) (a := (264820014632301089 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy101_hz1 : B (958441 / 4000000) (958441 / 4000000) (((979 / 2000) : ℝ)^2) := bsq (bpoint ((979 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy101_hz2 : B (3041559 / 4000000) (3041559 / 4000000) ((1 : ℝ) - (((979 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy101_hz1 (by norm_num) (by norm_num)

theorem lowEnergy101_hz3 : B (43600164850605783 / 50000000000000000) (872003297012115661 / 1000000000000000000) (√((1 : ℝ) - (((979 / 2000) : ℝ)^2))) := bsqrt lowEnergy101_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy101_hz4 : B (277567270223816747 / 1000000000000000000) (277567270223816749 / 1000000000000000000) ((√((1 : ℝ) - (((979 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy101_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy101_hz5 : B (324450725372459027 / 1000000000000000000) (162225362686255209 / 500000000000000000) (((979 / 2000) : ℝ) * (kdot ((979 / 2000)))) := bmul (bpoint ((979 / 2000) : ℝ)) lowEnergy101_hz0 (by norm_num) (by norm_num)

theorem lowEnergy101_hz6 : B (301008997798137887 / 500000000000000000) (602017995596327167 / 1000000000000000000) (((√((1 : ℝ) - (((979 / 2000) : ℝ)^2))) / Real.pi) + (((979 / 2000) : ℝ) * (kdot ((979 / 2000))))) := badd lowEnergy101_hz4 lowEnergy101_hz5 (by norm_num) (by norm_num)

theorem lowEnergy101_hz7 : B (301008997798137887 / 500000000000000000) (602017995596327167 / 1000000000000000000) (kappa ((979 / 2000))) := by rw [kappa_eq]; exact lowEnergy101_hz6

theorem lowEnergy101_hz8 : B (706841233854158631 / 1000000000000000000) (88355154231769833 / 125000000000000000) (kdot ((75629482007 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (124015644512695811 / 250000000000000000)) (a := (230246356514805857 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (496062578050783243 / 1000000000000000000)) (a := (460492713029611663 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy101_hz9 : B (366068387113416751 / 1000000000000000000) (22879274194588547 / 62500000000000000) (((75629482007 / 125000000000) : ℝ)^2) := bsq (bpoint ((75629482007 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy101_hz10 : B (39620725805411453 / 62500000000000000) (633931612886583249 / 1000000000000000000) ((1 : ℝ) - (((75629482007 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy101_hz9 (by norm_num) (by norm_num)

theorem lowEnergy101_hz11 : B (398099112309542599 / 500000000000000000) (1990495561547713 / 2500000000000000) (√((1 : ℝ) - (((75629482007 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy101_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy101_hz12 : B (253437766258237209 / 1000000000000000000) (25343776625823721 / 100000000000000000) ((√((1 : ℝ) - (((75629482007 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy101_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy101_hz13 : B (85532858204126031 / 200000000000000000) (13364509094394693 / 31250000000000000) (((75629482007 / 125000000000) : ℝ) * (kdot ((75629482007 / 125000000000)))) := bmul (bpoint ((75629482007 / 125000000000) : ℝ)) lowEnergy101_hz8 (by norm_num) (by norm_num)

theorem lowEnergy101_hz14 : B (170275514319716841 / 250000000000000000) (340551028639433693 / 500000000000000000) (((√((1 : ℝ) - (((75629482007 / 125000000000) : ℝ)^2))) / Real.pi) + (((75629482007 / 125000000000) : ℝ) * (kdot ((75629482007 / 125000000000))))) := badd lowEnergy101_hz12 lowEnergy101_hz13 (by norm_num) (by norm_num)

theorem lowEnergy101_hz15 : B (170275514319716841 / 250000000000000000) (340551028639433693 / 500000000000000000) (kappa ((75629482007 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy101_hz14

theorem lowEnergy101 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (979 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (683913292373 / 1000000000000) := by
  have hk1 : kappa q ≤ (602017995597 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((979 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy101_hz7.2.trans (by norm_num))
  have hk2 : kappa ((75629482007 / 125000000000) : ℝ) ≤ (681102057279 / 1000000000000) := lowEnergy101_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((77630084091 / 100000000000) : ℝ)) (R := ((388583433157 / 500000000000) : ℝ)) (Q2 := ((75629482007 / 125000000000) : ℝ)) (T := ((206500949071 / 250000000000) : ℝ))
    (B := ((683913292373 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy102_hz0 : B (662638198040463317 / 1000000000000000000) (331319099020285869 / 500000000000000000) (kdot ((489 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (58581852525037809 / 100000000000000000)) (a := (264963339659473789 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (585818525250378089 / 1000000000000000000)) (a := (66240834914847159 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy102_hz1 : B (239121 / 1000000) (239121 / 1000000) (((489 / 1000) : ℝ)^2) := bsq (bpoint ((489 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy102_hz2 : B (760879 / 1000000) (760879 / 1000000) ((1 : ℝ) - (((489 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy102_hz1 (by norm_num) (by norm_num)

theorem lowEnergy102_hz3 : B (34891351363912519 / 40000000000000000) (54517736506113311 / 62500000000000000) (√((1 : ℝ) - (((489 / 1000) : ℝ)^2))) := bsqrt lowEnergy102_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy102_hz4 : B (277656552036141083 / 1000000000000000000) (69414138009035271 / 250000000000000000) ((√((1 : ℝ) - (((489 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy102_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy102_hz5 : B (162015039420893281 / 500000000000000000) (16201503942091979 / 50000000000000000) (((489 / 1000) : ℝ) * (kdot ((489 / 1000)))) := bmul (bpoint ((489 / 1000) : ℝ)) lowEnergy102_hz0 (by norm_num) (by norm_num)

theorem lowEnergy102_hz6 : B (120337326175585529 / 200000000000000000) (75210828859747583 / 125000000000000000) (((√((1 : ℝ) - (((489 / 1000) : ℝ)^2))) / Real.pi) + (((489 / 1000) : ℝ) * (kdot ((489 / 1000))))) := badd lowEnergy102_hz4 lowEnergy102_hz5 (by norm_num) (by norm_num)

theorem lowEnergy102_hz7 : B (120337326175585529 / 200000000000000000) (75210828859747583 / 125000000000000000) (kappa ((489 / 1000))) := by rw [kappa_eq]; exact lowEnergy102_hz6

theorem lowEnergy102_hz8 : B (353354200853484479 / 500000000000000000) (706708401706968993 / 1000000000000000000) (kdot ((151175886571 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (496322601962179891 / 1000000000000000000)) (a := (460701365278497531 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (49632260196217989 / 100000000000000000)) (a := (230350682639248739 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy102_hz9 : B (36566637888844573 / 100000000000000000) (365666378888445731 / 1000000000000000000) (((151175886571 / 250000000000) : ℝ)^2) := bsq (bpoint ((151175886571 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy102_hz10 : B (634333621111554269 / 1000000000000000000) (63433362111155427 / 100000000000000000) ((1 : ℝ) - (((151175886571 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy102_hz9 (by norm_num) (by norm_num)

theorem lowEnergy102_hz11 : B (398225319734806123 / 500000000000000000) (99556329933701531 / 125000000000000000) (√((1 : ℝ) - (((151175886571 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy102_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy102_hz12 : B (63379528100144893 / 250000000000000000) (126759056200289787 / 500000000000000000) ((√((1 : ℝ) - (((151175886571 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy102_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy102_hz13 : B (427349076700901767 / 1000000000000000000) (42734907670090179 / 100000000000000000) (((151175886571 / 250000000000) : ℝ) * (kdot ((151175886571 / 250000000000)))) := bmul (bpoint ((151175886571 / 250000000000) : ℝ)) lowEnergy102_hz8 (by norm_num) (by norm_num)

theorem lowEnergy102_hz14 : B (680867189101481339 / 1000000000000000000) (170216797275370341 / 250000000000000000) (((√((1 : ℝ) - (((151175886571 / 250000000000) : ℝ)^2))) / Real.pi) + (((151175886571 / 250000000000) : ℝ) * (kdot ((151175886571 / 250000000000))))) := badd lowEnergy102_hz12 lowEnergy102_hz13 (by norm_num) (by norm_num)

theorem lowEnergy102_hz15 : B (680867189101481339 / 1000000000000000000) (170216797275370341 / 250000000000000000) (kappa ((151175886571 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy102_hz14

theorem lowEnergy102 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (489 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (683677736143 / 1000000000000) := by
  have hk1 : kappa q ≤ (300843315439 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((489 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy102_hz7.2.trans (by norm_num))
  have hk2 : kappa ((151175886571 / 250000000000) : ℝ) ≤ (340433594551 / 500000000000) := lowEnergy102_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((77608738611 / 100000000000) : ℝ)) (R := ((388476705757 / 500000000000) : ℝ)) (Q2 := ((151175886571 / 250000000000) : ℝ)) (T := ((825861366283 / 1000000000000) : ℝ))
    (B := ((683677736143 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy103_hz0 : B (331227884789506919 / 500000000000000000) (331227884789562903 / 500000000000000000) (kdot ((977 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (4579714763754363 / 7812500000000000)) (a := (530213237276095263 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (586203489760558463 / 1000000000000000000)) (a := (265106618637959693 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy103_hz1 : B (954529 / 4000000) (954529 / 4000000) (((977 / 2000) : ℝ)^2) := bsq (bpoint ((977 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy103_hz2 : B (3045471 / 4000000) (3045471 / 4000000) ((1 : ℝ) - (((977 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy103_hz1 (by norm_num) (by norm_num)

theorem lowEnergy103_hz3 : B (872563894508591273 / 1000000000000000000) (436281947254295637 / 500000000000000000) (√((1 : ℝ) - (((977 / 2000) : ℝ)^2))) := bsqrt lowEnergy103_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy103_hz4 : B (138872856974557409 / 500000000000000000) (277745713949114819 / 1000000000000000000) ((√((1 : ℝ) - (((977 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy103_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy103_hz5 : B (323609643439348259 / 1000000000000000000) (323609643439402957 / 1000000000000000000) (((977 / 2000) : ℝ) * (kdot ((977 / 2000)))) := bmul (bpoint ((977 / 2000) : ℝ)) lowEnergy103_hz0 (by norm_num) (by norm_num)

theorem lowEnergy103_hz6 : B (601355357388463077 / 1000000000000000000) (37584709836782361 / 62500000000000000) (((√((1 : ℝ) - (((977 / 2000) : ℝ)^2))) / Real.pi) + (((977 / 2000) : ℝ) * (kdot ((977 / 2000))))) := badd lowEnergy103_hz4 lowEnergy103_hz5 (by norm_num) (by norm_num)

theorem lowEnergy103_hz7 : B (601355357388463077 / 1000000000000000000) (37584709836782361 / 62500000000000000) (kappa ((977 / 2000))) := by rw [kappa_eq]; exact lowEnergy103_hz6

theorem lowEnergy103_hz8 : B (353287824072644767 / 500000000000000000) (706575648145289569 / 1000000000000000000) (kdot ((6043713279 / 10000000000))) := by
    constructor
    · apply bkdot_lower (q := (496582525852817259 / 1000000000000000000)) (a := (460909894085552511 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (248291262926408629 / 500000000000000000)) (a := (460909894085552457 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy103_hz9 : B (182632350993804659 / 500000000000000000) (365264701987609319 / 1000000000000000000) (((6043713279 / 10000000000) : ℝ)^2) := bsq (bpoint ((6043713279 / 10000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy103_hz10 : B (634735298012390681 / 1000000000000000000) (317367649006195341 / 500000000000000000) ((1 : ℝ) - (((6043713279 / 10000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy103_hz9 (by norm_num) (by norm_num)

theorem lowEnergy103_hz11 : B (99587845801802563 / 125000000000000000) (398351383207210253 / 500000000000000000) (√((1 : ℝ) - (((6043713279 / 10000000000) : ℝ)^2))) := bsqrt lowEnergy103_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy103_hz12 : B (50719673379937071 / 200000000000000000) (253598366899685357 / 1000000000000000000) ((√((1 : ℝ) - (((6043713279 / 10000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy103_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy103_hz13 : B (427034062731371807 / 1000000000000000000) (427034062731371829 / 1000000000000000000) (((6043713279 / 10000000000) : ℝ) * (kdot ((6043713279 / 10000000000)))) := bmul (bpoint ((6043713279 / 10000000000) : ℝ)) lowEnergy103_hz8 (by norm_num) (by norm_num)

theorem lowEnergy103_hz14 : B (340316214815528581 / 500000000000000000) (340316214815528593 / 500000000000000000) (((√((1 : ℝ) - (((6043713279 / 10000000000) : ℝ)^2))) / Real.pi) + (((6043713279 / 10000000000) : ℝ) * (kdot ((6043713279 / 10000000000))))) := badd lowEnergy103_hz12 lowEnergy103_hz13 (by norm_num) (by norm_num)

theorem lowEnergy103_hz15 : B (340316214815528581 / 500000000000000000) (340316214815528593 / 500000000000000000) (kappa ((6043713279 / 10000000000))) := by rw [kappa_eq]; exact lowEnergy103_hz14

theorem lowEnergy103 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (977 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (683442288889 / 1000000000000) := by
  have hk1 : kappa q ≤ (601355357389 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((977 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy103_hz7.2.trans (by norm_num))
  have hk2 : kappa ((6043713279 / 10000000000) : ℝ) ≤ (10634881713 / 15625000000) := lowEnergy103_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((775873931377 / 1000000000000) : ℝ)) (R := ((776739956781 / 1000000000000) : ℝ)) (Q2 := ((6043713279 / 10000000000) : ℝ)) (T := ((825718977653 / 1000000000000) : ℝ))
    (B := ((683442288889 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy104_hz0 : B (331136699816008791 / 500000000000000000) (66227339963213321 / 100000000000000000) (kdot ((61 / 125))) := by
    constructor
    · apply bkdot_lower (q := (586588460085413157 / 1000000000000000000)) (a := (530499703318954763 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (146647115021353289 / 250000000000000000)) (a := (33156231457423321 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy104_hz1 : B (3721 / 15625) (3721 / 15625) (((61 / 125) : ℝ)^2) := bsq (bpoint ((61 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy104_hz2 : B (11904 / 15625) (11904 / 15625) ((1 : ℝ) - (((61 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy104_hz1 (by norm_num) (by norm_num)

theorem lowEnergy104_hz3 : B (872843628607094777 / 1000000000000000000) (436421814303547389 / 500000000000000000) (√((1 : ℝ) - (((61 / 125) : ℝ)^2))) := bsqrt lowEnergy104_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy104_hz4 : B (277834756078171193 / 1000000000000000000) (55566951215634239 / 200000000000000000) ((√((1 : ℝ) - (((61 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy104_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy104_hz5 : B (16159470951021229 / 50000000000000000) (323189419020481007 / 1000000000000000000) (((61 / 125) : ℝ) * (kdot ((61 / 125)))) := bmul (bpoint ((61 / 125) : ℝ)) lowEnergy104_hz0 (by norm_num) (by norm_num)

theorem lowEnergy104_hz6 : B (601024175098595773 / 1000000000000000000) (300512087549326101 / 500000000000000000) (((√((1 : ℝ) - (((61 / 125) : ℝ)^2))) / Real.pi) + (((61 / 125) : ℝ) * (kdot ((61 / 125))))) := badd lowEnergy104_hz4 lowEnergy104_hz5 (by norm_num) (by norm_num)

theorem lowEnergy104_hz7 : B (601024175098595773 / 1000000000000000000) (300512087549326101 / 500000000000000000) (kappa ((61 / 125))) := by rw [kappa_eq]; exact lowEnergy104_hz6

theorem lowEnergy104_hz8 : B (706442973059473659 / 1000000000000000000) (141288594611894739 / 200000000000000000) (kdot ((302019600437 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (496842349881189873 / 1000000000000000000)) (a := (92223659924601857 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (31052646867574367 / 62500000000000000)) (a := (46111829962300923 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy104_hz9 : B (182431678096250261 / 500000000000000000) (364863356192500523 / 1000000000000000000) (((302019600437 / 500000000000) : ℝ)^2) := bsq (bpoint ((302019600437 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy104_hz10 : B (635136643807499477 / 1000000000000000000) (317568321903749739 / 500000000000000000) ((1 : ℝ) - (((302019600437 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy104_hz9 (by norm_num) (by norm_num)

theorem lowEnergy104_hz11 : B (796954605863784111 / 1000000000000000000) (796954605863784113 / 1000000000000000000) (√((1 : ℝ) - (((302019600437 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy104_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy104_hz12 : B (126839264943074437 / 500000000000000000) (2029428239089191 / 8000000000000000) ((√((1 : ℝ) - (((302019600437 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy104_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy104_hz13 : B (426719248909897179 / 1000000000000000000) (213359624454948601 / 500000000000000000) (((302019600437 / 500000000000) : ℝ) * (kdot ((302019600437 / 500000000000)))) := bmul (bpoint ((302019600437 / 500000000000) : ℝ)) lowEnergy104_hz8 (by norm_num) (by norm_num)

theorem lowEnergy104_hz14 : B (680397778796046053 / 1000000000000000000) (680397778796046077 / 1000000000000000000) (((√((1 : ℝ) - (((302019600437 / 500000000000) : ℝ)^2))) / Real.pi) + (((302019600437 / 500000000000) : ℝ) * (kdot ((302019600437 / 500000000000))))) := badd lowEnergy104_hz12 lowEnergy104_hz13 (by norm_num) (by norm_num)

theorem lowEnergy104_hz15 : B (680397778796046053 / 1000000000000000000) (680397778796046077 / 1000000000000000000) (kappa ((302019600437 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy104_hz14

theorem lowEnergy104 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (61 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (683206950541 / 1000000000000) := by
  have hk1 : kappa q ≤ (601024175099 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((61 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy104_hz7.2.trans (by norm_num))
  have hk2 : kappa ((302019600437 / 500000000000) : ℝ) ≤ (680397778797 / 1000000000000) := lowEnergy104_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((775660476691 / 1000000000000) : ℝ)) (R := ((155305300419 / 200000000000) : ℝ)) (Q2 := ((302019600437 / 500000000000) : ℝ)) (T := ((825576630373 / 1000000000000) : ℝ))
    (B := ((683206950541 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy105_hz0 : B (662091088083398961 / 1000000000000000000) (662091088083518367 / 1000000000000000000) (kdot ((39 / 80))) := by
    constructor
    · apply bkdot_lower (q := (146743359118490099 / 250000000000000000)) (a := (530786077629857181 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (117394687294792079 / 200000000000000000)) (a := (530786077629669621 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy105_hz1 : B (1521 / 6400) (1521 / 6400) (((39 / 80) : ℝ)^2) := bsq (bpoint ((39 / 80) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy105_hz2 : B (4879 / 6400) (4879 / 6400) ((1 : ℝ) - (((39 / 80) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy105_hz1 (by norm_num) (by norm_num)

theorem lowEnergy105_hz3 : B (109140373344377011 / 125000000000000000) (873122986755016089 / 1000000000000000000) (√((1 : ℝ) - (((39 / 80) : ℝ)^2))) := bsqrt lowEnergy105_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy105_hz4 : B (13896183926922027 / 50000000000000000) (138961839269220271 / 500000000000000000) ((√((1 : ℝ) - (((39 / 80) : ℝ)^2))) / Real.pi) := bdiv lowEnergy105_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy105_hz5 : B (322769405440656993 / 1000000000000000000) (80692351360178801 / 250000000000000000) (((39 / 80) : ℝ) * (kdot ((39 / 80)))) := bmul (bpoint ((39 / 80) : ℝ)) lowEnergy105_hz0 (by norm_num) (by norm_num)

theorem lowEnergy105_hz6 : B (600693083979097533 / 1000000000000000000) (300346541989577873 / 500000000000000000) (((√((1 : ℝ) - (((39 / 80) : ℝ)^2))) / Real.pi) + (((39 / 80) : ℝ) * (kdot ((39 / 80))))) := badd lowEnergy105_hz4 lowEnergy105_hz5 (by norm_num) (by norm_num)

theorem lowEnergy105_hz7 : B (600693083979097533 / 1000000000000000000) (300346541989577873 / 500000000000000000) (kappa ((39 / 80))) := by rw [kappa_eq]; exact lowEnergy105_hz6

theorem lowEnergy105_hz8 : B (44144398521283191 / 62500000000000000) (176577594085132773 / 250000000000000000) (kdot ((603707165177 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (124275518551156703 / 250000000000000000)) (a := (461326582062069381 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (497102074204626811 / 1000000000000000000)) (a := (18453063282482773 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy105_hz9 : B (364462341286049561 / 1000000000000000000) (182231170643024781 / 500000000000000000) (((603707165177 / 1000000000000) : ℝ)^2) := bsq (bpoint ((603707165177 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy105_hz10 : B (317768829356975219 / 500000000000000000) (635537658713950439 / 1000000000000000000) ((1 : ℝ) - (((603707165177 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy105_hz9 (by norm_num) (by norm_num)

theorem lowEnergy105_hz11 : B (797206158226308759 / 1000000000000000000) (797206158226308761 / 1000000000000000000) (√((1 : ℝ) - (((603707165177 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy105_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy105_hz12 : B (126879300745016679 / 500000000000000000) (3171982518625417 / 12500000000000000) ((√((1 : ℝ) - (((603707165177 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy105_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy105_hz13 : B (85280927007128403 / 200000000000000000) (426404635035642037 / 1000000000000000000) (((603707165177 / 1000000000000) : ℝ) * (kdot ((603707165177 / 1000000000000)))) := bmul (bpoint ((603707165177 / 1000000000000) : ℝ)) lowEnergy105_hz8 (by norm_num) (by norm_num)

theorem lowEnergy105_hz14 : B (680163236525675373 / 1000000000000000000) (680163236525675397 / 1000000000000000000) (((√((1 : ℝ) - (((603707165177 / 1000000000000) : ℝ)^2))) / Real.pi) + (((603707165177 / 1000000000000) : ℝ) * (kdot ((603707165177 / 1000000000000))))) := badd lowEnergy105_hz12 lowEnergy105_hz13 (by norm_num) (by norm_num)

theorem lowEnergy105_hz15 : B (680163236525675373 / 1000000000000000000) (680163236525675397 / 1000000000000000000) (kappa ((603707165177 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy105_hz14

theorem lowEnergy105 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (39 / 80)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (341485860513 / 500000000000) := by
  have hk1 : kappa q ≤ (30034654199 / 50000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((39 / 80) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy105_hz7.2.trans (by norm_num))
  have hk2 : kappa ((603707165177 / 1000000000000) : ℝ) ≤ (340081618263 / 500000000000) := lowEnergy105_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((387723511017 / 500000000000) : ℝ)) (R := ((388156523719 / 500000000000) : ℝ)) (Q2 := ((603707165177 / 1000000000000) : ℝ)) (T := ((825434324421 / 1000000000000) : ℝ))
    (B := ((341485860513 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy106_hz0 : B (661908834817344711 / 1000000000000000000) (41369302176091751 / 62500000000000000) (kdot ((487 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (73419802396864431 / 125000000000000000)) (a := (53107236039072157 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (587358419174915447 / 1000000000000000000)) (a := (106214472078105577 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy106_hz1 : B (237169 / 1000000) (237169 / 1000000) (((487 / 1000) : ℝ)^2) := bsq (bpoint ((487 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy106_hz2 : B (762831 / 1000000) (762831 / 1000000) ((1 : ℝ) - (((487 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy106_hz1 (by norm_num) (by norm_num)

theorem lowEnergy106_hz3 : B (87340196931309927 / 100000000000000000) (873401969313099271 / 1000000000000000000) (√((1 : ℝ) - (((487 / 1000) : ℝ)^2))) := bsqrt lowEnergy106_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy106_hz4 : B (278012481444751261 / 1000000000000000000) (139006240722375631 / 500000000000000000) ((√((1 : ℝ) - (((487 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy106_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy106_hz5 : B (161174801278023437 / 500000000000000000) (80587400639026731 / 250000000000000000) (((487 / 1000) : ℝ) * (kdot ((487 / 1000)))) := bmul (bpoint ((487 / 1000) : ℝ)) lowEnergy106_hz0 (by norm_num) (by norm_num)

theorem lowEnergy106_hz6 : B (120072416800159627 / 200000000000000000) (300181042000429093 / 500000000000000000) (((√((1 : ℝ) - (((487 / 1000) : ℝ)^2))) / Real.pi) + (((487 / 1000) : ℝ) * (kdot ((487 / 1000))))) := badd lowEnergy106_hz4 lowEnergy106_hz5 (by norm_num) (by norm_num)

theorem lowEnergy106_hz7 : B (120072416800159627 / 200000000000000000) (300181042000429093 / 500000000000000000) (kappa ((487 / 1000))) := by rw [kappa_eq]; exact lowEnergy106_hz6

theorem lowEnergy106_hz8 : B (44136116117408109 / 62500000000000000) (353088928939264891 / 500000000000000000) (kdot ((603375220777 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (248680849491210913 / 500000000000000000)) (a := (461534741575413551 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (19894467959296873 / 40000000000000000)) (a := (461534741575413493 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy106_hz9 : B (91015414261923373 / 250000000000000000) (364061657047693493 / 1000000000000000000) (((603375220777 / 1000000000000) : ℝ)^2) := bsq (bpoint ((603375220777 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy106_hz10 : B (635938342952306507 / 1000000000000000000) (158984585738076627 / 250000000000000000) ((1 : ℝ) - (((603375220777 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy106_hz9 (by norm_num) (by norm_num)

theorem lowEnergy106_hz11 : B (79745742391196441 / 100000000000000000) (199364355977991103 / 250000000000000000) (√((1 : ℝ) - (((603375220777 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy106_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy106_hz12 : B (2538385818418363 / 10000000000000000) (126919290920918151 / 500000000000000000) ((√((1 : ℝ) - (((603375220777 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy106_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy106_hz13 : B (426090220905286813 / 1000000000000000000) (426090220905286837 / 1000000000000000000) (((603375220777 / 1000000000000) : ℝ) * (kdot ((603375220777 / 1000000000000)))) := bmul (bpoint ((603375220777 / 1000000000000) : ℝ)) lowEnergy106_hz8 (by norm_num) (by norm_num)

theorem lowEnergy106_hz14 : B (679928802747123113 / 1000000000000000000) (679928802747123139 / 1000000000000000000) (((√((1 : ℝ) - (((603375220777 / 1000000000000) : ℝ)^2))) / Real.pi) + (((603375220777 / 1000000000000) : ℝ) * (kdot ((603375220777 / 1000000000000))))) := badd lowEnergy106_hz12 lowEnergy106_hz13 (by norm_num) (by norm_num)

theorem lowEnergy106_hz15 : B (679928802747123113 / 1000000000000000000) (679928802747123139 / 1000000000000000000) (kappa ((603375220777 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy106_hz14

theorem lowEnergy106 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (487 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (27309464011 / 40000000000) := by
  have hk1 : kappa q ≤ (600362084001 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((487 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy106_hz7.2.trans (by norm_num))
  have hk2 : kappa ((603375220777 / 1000000000000) : ℝ) ≤ (169982200687 / 250000000000) := lowEnergy106_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((387616783693 / 500000000000) : ℝ)) (R := ((77609959279 / 100000000000) : ℝ)) (Q2 := ((603375220777 / 1000000000000) : ℝ)) (T := ((33011682391 / 40000000000) : ℝ))
    (B := ((27309464011 / 40000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy107_hz0 : B (8271582996478787 / 12500000000000000) (41357914982401893 / 62500000000000000) (kdot ((973 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (293871704218346087 / 500000000000000000)) (a := (106271710356611277 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (587743408436692173 / 1000000000000000000)) (a := (531358551782856381 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy107_hz1 : B (946729 / 4000000) (946729 / 4000000) (((973 / 2000) : ℝ)^2) := bsq (bpoint ((973 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy107_hz2 : B (3053271 / 4000000) (3053271 / 4000000) ((1 : ℝ) - (((973 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy107_hz1 (by norm_num) (by norm_num)

theorem lowEnergy107_hz3 : B (174736115328228583 / 200000000000000000) (218420144160285729 / 250000000000000000) (√((1 : ℝ) - (((973 / 2000) : ℝ)^2))) := bsqrt lowEnergy107_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy107_hz4 : B (69525291227907701 / 250000000000000000) (55620232982326161 / 200000000000000000) ((√((1 : ℝ) - (((973 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy107_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy107_hz5 : B (32193001022295439 / 100000000000000000) (20120625638938521 / 62500000000000000) (((973 / 2000) : ℝ) * (kdot ((973 / 2000)))) := bmul (bpoint ((973 / 2000) : ℝ)) lowEnergy107_hz0 (by norm_num) (by norm_num)

theorem lowEnergy107_hz6 : B (300015587567292597 / 500000000000000000) (600031175134647141 / 1000000000000000000) (((√((1 : ℝ) - (((973 / 2000) : ℝ)^2))) / Real.pi) + (((973 / 2000) : ℝ) * (kdot ((973 / 2000))))) := badd lowEnergy107_hz4 lowEnergy107_hz5 (by norm_num) (by norm_num)

theorem lowEnergy107_hz7 : B (300015587567292597 / 500000000000000000) (600031175134647141 / 1000000000000000000) (kappa ((973 / 2000))) := by rw [kappa_eq]; exact lowEnergy107_hz6

theorem lowEnergy107_hz8 : B (706045417566587353 / 1000000000000000000) (1378994956184741 / 1953125000000000) (kdot ((603043367649 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (497621224368013333 / 1000000000000000000)) (a := (115435694582733057 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (124405306092003333 / 250000000000000000)) (a := (461742778330932169 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy107_hz9 : B (363661303265446979 / 1000000000000000000) (18183065163272349 / 50000000000000000) (((603043367649 / 1000000000000) : ℝ)^2) := bsq (bpoint ((603043367649 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy107_hz10 : B (31816934836727651 / 50000000000000000) (636338696734553021 / 1000000000000000000) ((1 : ℝ) - (((603043367649 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy107_hz9 (by norm_num) (by norm_num)

theorem lowEnergy107_hz11 : B (398854201662259357 / 500000000000000000) (199427100831129679 / 250000000000000000) (√((1 : ℝ) - (((603043367649 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy107_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy107_hz12 : B (50783694214016187 / 200000000000000000) (253918471070080937 / 1000000000000000000) ((√((1 : ℝ) - (((603043367649 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy107_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy107_hz13 : B (21288800316124963 / 50000000000000000) (106444001580624821 / 250000000000000000) (((603043367649 / 1000000000000) : ℝ) * (kdot ((603043367649 / 1000000000000)))) := bmul (bpoint ((603043367649 / 1000000000000) : ℝ)) lowEnergy107_hz8 (by norm_num) (by norm_num)

theorem lowEnergy107_hz14 : B (135938895478516039 / 200000000000000000) (679694477392580221 / 1000000000000000000) (((√((1 : ℝ) - (((603043367649 / 1000000000000) : ℝ)^2))) / Real.pi) + (((603043367649 / 1000000000000) : ℝ) * (kdot ((603043367649 / 1000000000000))))) := badd lowEnergy107_hz12 lowEnergy107_hz13 (by norm_num) (by norm_num)

theorem lowEnergy107_hz15 : B (135938895478516039 / 200000000000000000) (679694477392580221 / 1000000000000000000) (kappa ((603043367649 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy107_hz14

theorem lowEnergy107 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (973 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (136500317643 / 200000000000) := by
  have hk1 : kappa q ≤ (120006235027 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((973 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy107_hz7.2.trans (by norm_num))
  have hk2 : kappa ((603043367649 / 1000000000000) : ℝ) ≤ (679694477393 / 1000000000000) := lowEnergy107_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((77502011273 / 100000000000) : ℝ)) (R := ((387943069067 / 500000000000) : ℝ)) (Q2 := ((603043367649 / 1000000000000) : ℝ)) (T := ((412574918207 / 500000000000) : ℝ))
    (B := ((136500317643 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy108_hz0 : B (661544502670982303 / 1000000000000000000) (661544502671113783 / 1000000000000000000) (kdot ((243 / 500))) := by
    constructor
    · apply bkdot_lower (q := (18379012640856393 / 31250000000000000)) (a := (531644651987960941 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (23525136180296183 / 40000000000000000)) (a := (106328930397550883 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy108_hz1 : B (59049 / 250000) (59049 / 250000) (((243 / 500) : ℝ)^2) := bsq (bpoint ((243 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy108_hz2 : B (190951 / 250000) (190951 / 250000) ((1 : ℝ) - (((243 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy108_hz1 (by norm_num) (by norm_num)

theorem lowEnergy108_hz3 : B (873958809098003199 / 1000000000000000000) (136556063921563 / 156250000000000) (√((1 : ℝ) - (((243 / 500) : ℝ)^2))) := bsqrt lowEnergy108_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy108_hz4 : B (278189729053306637 / 1000000000000000000) (139094864526653319 / 500000000000000000) ((√((1 : ℝ) - (((243 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy108_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy108_hz5 : B (321510628298097399 / 1000000000000000000) (321510628298161299 / 1000000000000000000) (((243 / 500) : ℝ) * (kdot ((243 / 500)))) := bmul (bpoint ((243 / 500) : ℝ)) lowEnergy108_hz0 (by norm_num) (by norm_num)

theorem lowEnergy108_hz6 : B (149925089337851009 / 250000000000000000) (599700357351467937 / 1000000000000000000) (((√((1 : ℝ) - (((243 / 500) : ℝ)^2))) / Real.pi) + (((243 / 500) : ℝ) * (kdot ((243 / 500))))) := badd lowEnergy108_hz4 lowEnergy108_hz5 (by norm_num) (by norm_num)

theorem lowEnergy108_hz7 : B (149925089337851009 / 250000000000000000) (599700357351467937 / 1000000000000000000) (kappa ((243 / 500))) := by rw [kappa_eq]; exact lowEnergy108_hz6

theorem lowEnergy108_hz8 : B (705913055295281203 / 1000000000000000000) (352956527647640621 / 500000000000000000) (kdot ((602711605761 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (1244701626299839 / 2500000000000000)) (a := (461950692500506159 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (497880650519935599 / 1000000000000000000)) (a := (461950692500506099 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy108_hz9 : B (22703829982437693 / 62500000000000000) (363261279719003089 / 1000000000000000000) (((602711605761 / 1000000000000) : ℝ)^2) := bsq (bpoint ((602711605761 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy108_hz10 : B (636738720280996911 / 1000000000000000000) (39796170017562307 / 62500000000000000) ((1 : ℝ) - (((602711605761 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy108_hz9 (by norm_num) (by norm_num)

theorem lowEnergy108_hz11 : B (199489774218034311 / 250000000000000000) (398979548436068623 / 500000000000000000) (√((1 : ℝ) - (((602711605761 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy108_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy108_hz12 : B (317497836630863 / 1250000000000000) (126999134652345201 / 500000000000000000) ((√((1 : ℝ) - (((602711605761 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy108_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy108_hz13 : B (425461991084672517 / 1000000000000000000) (212730995542336271 / 500000000000000000) (((602711605761 / 1000000000000) : ℝ) * (kdot ((602711605761 / 1000000000000)))) := bmul (bpoint ((602711605761 / 1000000000000) : ℝ)) lowEnergy108_hz8 (by norm_num) (by norm_num)

theorem lowEnergy108_hz14 : B (679460260389362917 / 1000000000000000000) (2654141642145949 / 3906250000000000) (((√((1 : ℝ) - (((602711605761 / 1000000000000) : ℝ)^2))) / Real.pi) + (((602711605761 / 1000000000000) : ℝ) * (kdot ((602711605761 / 1000000000000))))) := badd lowEnergy108_hz12 lowEnergy108_hz13 (by norm_num) (by norm_num)

theorem lowEnergy108_hz15 : B (679460260389362917 / 1000000000000000000) (2654141642145949 / 3906250000000000) (kappa ((602711605761 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy108_hz14

theorem lowEnergy108 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (85283335597 / 125000000000) := by
  have hk1 : kappa q ≤ (74962544669 / 125000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((243 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy108_hz7.2.trans (by norm_num))
  have hk2 : kappa ((602711605761 / 1000000000000) : ℝ) ≤ (67946026039 / 100000000000) := lowEnergy108_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((387403329023 / 500000000000) : ℝ)) (R := ((15513453669 / 20000000000) : ℝ)) (Q2 := ((602711605761 / 1000000000000) : ℝ)) (T := ((165001530863 / 200000000000) : ℝ))
    (B := ((85283335597 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy109_hz0 : B (661362423560350883 / 1000000000000000000) (661362423560486647 / 1000000000000000000) (kdot ((971 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (588513407634868343 / 1000000000000000000)) (a := (531930661186126857 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (294256703817434171 / 500000000000000000)) (a := (265965330592956801 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy109_hz1 : B (942841 / 4000000) (942841 / 4000000) (((971 / 2000) : ℝ)^2) := bsq (bpoint ((971 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy109_hz2 : B (3057159 / 4000000) (3057159 / 4000000) ((1 : ℝ) - (((971 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy109_hz1 (by norm_num) (by norm_num)

theorem lowEnergy109_hz3 : B (874236667041596923 / 1000000000000000000) (218559166760399231 / 250000000000000000) (√((1 : ℝ) - (((971 / 2000) : ℝ)^2))) := bsqrt lowEnergy109_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy109_hz4 : B (278278173983707217 / 1000000000000000000) (278278173983707219 / 1000000000000000000) ((√((1 : ℝ) - (((971 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy109_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy109_hz5 : B (321091456638550353 / 1000000000000000000) (80272864159654067 / 250000000000000000) (((971 / 2000) : ℝ) * (kdot ((971 / 2000)))) := bmul (bpoint ((971 / 2000) : ℝ)) lowEnergy109_hz0 (by norm_num) (by norm_num)

theorem lowEnergy109_hz6 : B (59936963062225757 / 100000000000000000) (599369630622323487 / 1000000000000000000) (((√((1 : ℝ) - (((971 / 2000) : ℝ)^2))) / Real.pi) + (((971 / 2000) : ℝ) * (kdot ((971 / 2000))))) := badd lowEnergy109_hz4 lowEnergy109_hz5 (by norm_num) (by norm_num)

theorem lowEnergy109_hz7 : B (59936963062225757 / 100000000000000000) (599369630622323487 / 1000000000000000000) (kappa ((971 / 2000))) := by rw [kappa_eq]; exact lowEnergy109_hz6

theorem lowEnergy109_hz8 : B (441112981848149 / 625000000000000) (705780770957038441 / 1000000000000000000) (kdot ((120475987017 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (249069988796608443 / 500000000000000000)) (a := (462158484253110447 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (99627995518643377 / 200000000000000000)) (a := (92431696850622077 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy109_hz9 : B (362861586193008813 / 1000000000000000000) (181430793096504407 / 500000000000000000) (((120475987017 / 200000000000) : ℝ)^2) := bsq (bpoint ((120475987017 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy109_hz10 : B (318569206903495593 / 500000000000000000) (637138413806991187 / 1000000000000000000) ((1 : ℝ) - (((120475987017 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy109_hz9 (by norm_num) (by norm_num)

theorem lowEnergy109_hz11 : B (798209504959062227 / 1000000000000000000) (199552376239765557 / 250000000000000000) (√((1 : ℝ) - (((120475987017 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy109_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy109_hz12 : B (254077976674338993 / 1000000000000000000) (127038988337169497 / 500000000000000000) ((√((1 : ℝ) - (((120475987017 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy109_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy109_hz13 : B (106287043748335511 / 250000000000000000) (42514817499334207 / 100000000000000000) (((120475987017 / 200000000000) : ℝ) * (kdot ((120475987017 / 200000000000)))) := bmul (bpoint ((120475987017 / 200000000000) : ℝ)) lowEnergy109_hz8 (by norm_num) (by norm_num)

theorem lowEnergy109_hz14 : B (679226151667681037 / 1000000000000000000) (84903268958460133 / 125000000000000000) (((√((1 : ℝ) - (((120475987017 / 200000000000) : ℝ)^2))) / Real.pi) + (((120475987017 / 200000000000) : ℝ) * (kdot ((120475987017 / 200000000000))))) := badd lowEnergy109_hz12 lowEnergy109_hz13 (by norm_num) (by norm_num)

theorem lowEnergy109_hz15 : B (679226151667681037 / 1000000000000000000) (84903268958460133 / 125000000000000000) (kappa ((120475987017 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy109_hz14

theorem lowEnergy109 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (971 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (682031889889 / 1000000000000) := by
  have hk1 : kappa q ≤ (599369630623 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((971 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy109_hz7.2.trans (by norm_num))
  have hk2 : kappa ((120475987017 / 200000000000) : ℝ) ≤ (169806537917 / 250000000000) := lowEnergy109_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((193648300829 / 250000000000) : ℝ)) (R := ((9693240359 / 12500000000) : ℝ)) (Q2 := ((120475987017 / 200000000000) : ℝ)) (T := ((824865513459 / 1000000000000) : ℝ))
    (B := ((682031889889 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy110_hz0 : B (330590201135817737 / 500000000000000000) (661180402271775659 / 1000000000000000000) (kdot ((97 / 200))) := by
    constructor
    · apply bkdot_lower (q := (117779683613320477 / 200000000000000000)) (a := (106443315911567899 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (36806151129162649 / 62500000000000000)) (a := (106443315911523859 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy110_hz1 : B (9409 / 40000) (9409 / 40000) (((97 / 200) : ℝ)^2) := bsq (bpoint ((97 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy110_hz2 : B (30591 / 40000) (30591 / 40000) ((1 : ℝ) - (((97 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy110_hz1 (by norm_num) (by norm_num)

theorem lowEnergy110_hz3 : B (43725707541445227 / 50000000000000000) (874514150828904541 / 1000000000000000000) (√((1 : ℝ) - (((97 / 200) : ℝ)^2))) := bsqrt lowEnergy110_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy110_hz4 : B (34795812477057869 / 125000000000000000) (139183249908231477 / 500000000000000000) ((√((1 : ℝ) - (((97 / 200) : ℝ)^2))) / Real.pi) := bdiv lowEnergy110_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy110_hz5 : B (80168123775435801 / 250000000000000000) (64134499020362239 / 200000000000000000) (((97 / 200) : ℝ) * (kdot ((97 / 200)))) := bmul (bpoint ((97 / 200) : ℝ)) lowEnergy110_hz0 (by norm_num) (by norm_num)

theorem lowEnergy110_hz6 : B (149759748729551539 / 250000000000000000) (599038994918274149 / 1000000000000000000) (((√((1 : ℝ) - (((97 / 200) : ℝ)^2))) / Real.pi) + (((97 / 200) : ℝ) * (kdot ((97 / 200))))) := badd lowEnergy110_hz4 lowEnergy110_hz5 (by norm_num) (by norm_num)

theorem lowEnergy110_hz7 : B (149759748729551539 / 250000000000000000) (599038994918274149 / 1000000000000000000) (kappa ((97 / 200))) := by rw [kappa_eq]; exact lowEnergy110_hz6

theorem lowEnergy110_hz8 : B (176412141111134467 / 250000000000000000) (70564856444453791 / 100000000000000000) (kdot ((602048355593 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (124599801435627361 / 250000000000000000)) (a := (231183076878662323 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (498399205742509443 / 1000000000000000000)) (a := (231183076878662291 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy110_hz9 : B (181231111236117687 / 500000000000000000) (2899697779777883 / 8000000000000000) (((602048355593 / 1000000000000) : ℝ)^2) := bsq (bpoint ((602048355593 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy110_hz10 : B (5100302220222117 / 8000000000000000) (318768888763882313 / 500000000000000000) ((1 : ℝ) - (((602048355593 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy110_hz9 (by norm_num) (by norm_num)

theorem lowEnergy110_hz11 : B (99807453498580567 / 125000000000000000) (798459627988644537 / 1000000000000000000) (√((1 : ℝ) - (((602048355593 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy110_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy110_hz12 : B (127078796653708641 / 500000000000000000) (63539398326854321 / 250000000000000000) ((√((1 : ℝ) - (((602048355593 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy110_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy110_hz13 : B (42483455785039511 / 100000000000000000) (424834557850395137 / 1000000000000000000) (((602048355593 / 1000000000000) : ℝ) * (kdot ((602048355593 / 1000000000000)))) := bmul (bpoint ((602048355593 / 1000000000000) : ℝ)) lowEnergy110_hz8 (by norm_num) (by norm_num)

theorem lowEnergy110_hz14 : B (84874018894726549 / 125000000000000000) (678992151157812421 / 1000000000000000000) (((√((1 : ℝ) - (((602048355593 / 1000000000000) : ℝ)^2))) / Real.pi) + (((602048355593 / 1000000000000) : ℝ) * (kdot ((602048355593 / 1000000000000))))) := badd lowEnergy110_hz12 lowEnergy110_hz13 (by norm_num) (by norm_num)

theorem lowEnergy110_hz15 : B (84874018894726549 / 125000000000000000) (678992151157812421 / 1000000000000000000) (kappa ((602048355593 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy110_hz14

theorem lowEnergy110 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (97 / 200)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (681797203479 / 1000000000000) := by
  have hk1 : kappa q ≤ (599038994919 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((97 / 200) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy110_hz7.2.trans (by norm_num))
  have hk2 : kappa ((602048355593 / 1000000000000) : ℝ) ≤ (339496075579 / 500000000000) := lowEnergy110_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((774379748521 / 1000000000000) : ℝ)) (R := ((31009830957 / 40000000000) : ℝ)) (Q2 := ((602048355593 / 1000000000000) : ℝ)) (T := ((412361706911 / 500000000000) : ℝ))
    (B := ((681797203479 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy111_hz0 : B (660998438690320569 / 1000000000000000000) (165249609672616329 / 250000000000000000) (kdot ((969 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (589283436049830363 / 1000000000000000000)) (a := (8320350113796553 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (294641718024915181 / 500000000000000000)) (a := (266251203641376013 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy111_hz1 : B (938961 / 4000000) (938961 / 4000000) (((969 / 2000) : ℝ)^2) := bsq (bpoint ((969 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy111_hz2 : B (3061039 / 4000000) (3061039 / 4000000) ((1 : ℝ) - (((969 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy111_hz1 (by norm_num) (by norm_num)

theorem lowEnergy111_hz3 : B (218697815203993293 / 250000000000000000) (874791260815973173 / 1000000000000000000) (√((1 : ℝ) - (((969 / 2000) : ℝ)^2))) := bsqrt lowEnergy111_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy111_hz4 : B (6961367666622679 / 25000000000000000) (278454706664907161 / 1000000000000000000) ((√((1 : ℝ) - (((969 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy111_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy111_hz5 : B (64050748709092063 / 200000000000000000) (160126871772765223 / 500000000000000000) (((969 / 2000) : ℝ) * (kdot ((969 / 2000)))) := bmul (bpoint ((969 / 2000) : ℝ)) lowEnergy111_hz0 (by norm_num) (by norm_num)

theorem lowEnergy111_hz6 : B (23948338008414699 / 40000000000000000) (598708450210437607 / 1000000000000000000) (((√((1 : ℝ) - (((969 / 2000) : ℝ)^2))) / Real.pi) + (((969 / 2000) : ℝ) * (kdot ((969 / 2000))))) := badd lowEnergy111_hz4 lowEnergy111_hz5 (by norm_num) (by norm_num)

theorem lowEnergy111_hz7 : B (23948338008414699 / 40000000000000000) (598708450210437607 / 1000000000000000000) (kappa ((969 / 2000))) := by rw [kappa_eq]; exact lowEnergy111_hz6

theorem lowEnergy111_hz8 : B (705516435649115367 / 1000000000000000000) (70551643564911541 / 100000000000000000) (kdot ((601716867253 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (498658335125217517 / 1000000000000000000)) (a := (92514740236767629 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (124664583781304379 / 250000000000000000)) (a := (462573701183838079 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy111_hz9 : B (362063188336764423 / 1000000000000000000) (45257898542095553 / 125000000000000000) (((601716867253 / 1000000000000) : ℝ)^2) := bsq (bpoint ((601716867253 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy111_hz10 : B (79742101457904447 / 125000000000000000) (637936811663235577 / 1000000000000000000) ((1 : ℝ) - (((601716867253 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy111_hz9 (by norm_num) (by norm_num)

theorem lowEnergy111_hz11 : B (199677366591590003 / 250000000000000000) (399354733183180007 / 500000000000000000) (√((1 : ℝ) - (((601716867253 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy111_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy111_hz12 : B (127118559666496119 / 500000000000000000) (3177963991662403 / 12500000000000000) ((√((1 : ℝ) - (((601716867253 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy111_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy111_hz13 : B (106130284863572117 / 250000000000000000) (84904227890857699 / 200000000000000000) (((601716867253 / 1000000000000) : ℝ) * (kdot ((601716867253 / 1000000000000)))) := bmul (bpoint ((601716867253 / 1000000000000) : ℝ)) lowEnergy111_hz8 (by norm_num) (by norm_num)

theorem lowEnergy111_hz14 : B (339379129393640353 / 500000000000000000) (135751651757456147 / 200000000000000000) (((√((1 : ℝ) - (((601716867253 / 1000000000000) : ℝ)^2))) / Real.pi) + (((601716867253 / 1000000000000) : ℝ) * (kdot ((601716867253 / 1000000000000))))) := badd lowEnergy111_hz12 lowEnergy111_hz13 (by norm_num) (by norm_num)

theorem lowEnergy111_hz15 : B (339379129393640353 / 500000000000000000) (135751651757456147 / 200000000000000000) (kappa ((601716867253 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy111_hz14

theorem lowEnergy111 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (969 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (340781312741 / 500000000000) := by
  have hk1 : kappa q ≤ (598708450211 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((969 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy111_hz7.2.trans (by norm_num))
  have hk2 : kappa ((601716867253 / 1000000000000) : ℝ) ≤ (169689564697 / 250000000000) := lowEnergy111_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((387083146821 / 500000000000) : ℝ)) (R := ((387516159523 / 500000000000) : ℝ)) (Q2 := ((601716867253 / 1000000000000) : ℝ)) (T := ((164916271077 / 200000000000) : ℝ))
    (B := ((340781312741 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy112_hz0 : B (41301033293884217 / 62500000000000000) (26432661308091877 / 40000000000000000) (kdot ((121 / 250))) := by
    constructor
    · apply bkdot_lower (q := (589668461831482217 / 1000000000000000000)) (a := (53278814454102369 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (73708557728935277 / 125000000000000000)) (a := (53278814454078893 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy112_hz1 : B (14641 / 62500) (14641 / 62500) (((121 / 250) : ℝ)^2) := bsq (bpoint ((121 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy112_hz2 : B (47859 / 62500) (47859 / 62500) ((1 : ℝ) - (((121 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy112_hz1 (by norm_num) (by norm_num)

theorem lowEnergy112_hz3 : B (875067997357919609 / 1000000000000000000) (87506799735791961 / 100000000000000000) (√((1 : ℝ) - (((121 / 250) : ℝ)^2))) := bsqrt lowEnergy112_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy112_hz4 : B (139271397321038513 / 500000000000000000) (69635698660519257 / 250000000000000000) ((√((1 : ℝ) - (((121 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy112_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy112_hz5 : B (19989700114239961 / 62500000000000000) (9994850057122241 / 31250000000000000) (((121 / 250) : ℝ) * (kdot ((121 / 250)))) := bmul (bpoint ((121 / 250) : ℝ)) lowEnergy112_hz0 (by norm_num) (by norm_num)

theorem lowEnergy112_hz6 : B (299188998234958201 / 500000000000000000) (29918899823499437 / 50000000000000000) (((√((1 : ℝ) - (((121 / 250) : ℝ)^2))) / Real.pi) + (((121 / 250) : ℝ) * (kdot ((121 / 250))))) := badd lowEnergy112_hz4 lowEnergy112_hz5 (by norm_num) (by norm_num)

theorem lowEnergy112_hz7 : B (299188998234958201 / 500000000000000000) (29918899823499437 / 50000000000000000) (kappa ((121 / 250))) := by rw [kappa_eq]; exact lowEnergy112_hz6

theorem lowEnergy112_hz8 : B (176346096116286901 / 250000000000000000) (2755407751816983 / 3906250000000000) (kdot ((15034636751 / 25000000000))) := by
    constructor
    · apply bkdot_lower (q := (124729341473224869 / 250000000000000000)) (a := (57847640837320453 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (19956694635715979 / 40000000000000000)) (a := (462781126698563557 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy112_hz9 : B (361664483575231737 / 1000000000000000000) (180832241787615869 / 500000000000000000) (((15034636751 / 25000000000) : ℝ)^2) := bsq (bpoint ((15034636751 / 25000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy112_hz10 : B (319167758212384131 / 500000000000000000) (638335516424768263 / 1000000000000000000) ((1 : ℝ) - (((15034636751 / 25000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy112_hz9 (by norm_num) (by norm_num)

theorem lowEnergy112_hz11 : B (798959020491519491 / 1000000000000000000) (199739755122879873 / 250000000000000000) (√((1 : ℝ) - (((15034636751 / 25000000000) : ℝ)^2))) := bsqrt lowEnergy112_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy112_hz12 : B (1986848084985691 / 7812500000000000) (254316554878168449 / 1000000000000000000) ((√((1 : ℝ) - (((15034636751 / 25000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy112_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy112_hz13 : B (84841583922089773 / 200000000000000000) (424207919610448893 / 1000000000000000000) (((15034636751 / 25000000000) : ℝ) * (kdot ((15034636751 / 25000000000)))) := bmul (bpoint ((15034636751 / 25000000000) : ℝ)) lowEnergy112_hz8 (by norm_num) (by norm_num)

theorem lowEnergy112_hz14 : B (678524474488617313 / 1000000000000000000) (339262237244308671 / 500000000000000000) (((√((1 : ℝ) - (((15034636751 / 25000000000) : ℝ)^2))) / Real.pi) + (((15034636751 / 25000000000) : ℝ) * (kdot ((15034636751 / 25000000000))))) := badd lowEnergy112_hz12 lowEnergy112_hz13 (by norm_num) (by norm_num)

theorem lowEnergy112_hz15 : B (678524474488617313 / 1000000000000000000) (339262237244308671 / 500000000000000000) (kappa ((15034636751 / 25000000000))) := by rw [kappa_eq]; exact lowEnergy112_hz14

theorem lowEnergy112 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (121 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (340664077911 / 500000000000) := by
  have hk1 : kappa q ≤ (59837799647 / 100000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((121 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy112_hz7.2.trans (by norm_num))
  have hk2 : kappa ((15034636751 / 25000000000) : ℝ) ≤ (678524474489 / 1000000000000) := lowEnergy112_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((773952838661 / 1000000000000) : ℝ)) (R := ((154963772813 / 200000000000) : ℝ)) (Q2 := ((15034636751 / 25000000000) : ℝ)) (T := ((1319102941 / 1600000000) : ℝ))
    (B := ((340664077911 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy113_hz0 : B (660634684193113389 / 1000000000000000000) (6606346841932677 / 10000000000000000) (kdot ((967 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (118010699131639137 / 200000000000000000)) (a := (133268447877761889 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (147513373914548921 / 250000000000000000)) (a := (266536895755402583 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy113_hz1 : B (935089 / 4000000) (935089 / 4000000) (((967 / 2000) : ℝ)^2) := bsq (bpoint ((967 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy113_hz2 : B (3064911 / 4000000) (3064911 / 4000000) ((1 : ℝ) - (((967 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy113_hz1 (by norm_num) (by norm_num)

theorem lowEnergy113_hz3 : B (875344360808933297 / 1000000000000000000) (437672180404466649 / 500000000000000000) (√((1 : ℝ) - (((967 / 2000) : ℝ)^2))) := bsqrt lowEnergy113_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy113_hz4 : B (278630763860714553 / 1000000000000000000) (139315381930357277 / 500000000000000000) ((√((1 : ℝ) - (((967 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy113_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy113_hz5 : B (319416869807370323 / 1000000000000000000) (319416869807444933 / 1000000000000000000) (((967 / 2000) : ℝ) * (kdot ((967 / 2000)))) := bmul (bpoint ((967 / 2000) : ℝ)) lowEnergy113_hz0 (by norm_num) (by norm_num)

theorem lowEnergy113_hz6 : B (149511908417021219 / 250000000000000000) (598047633668159487 / 1000000000000000000) (((√((1 : ℝ) - (((967 / 2000) : ℝ)^2))) / Real.pi) + (((967 / 2000) : ℝ) * (kdot ((967 / 2000))))) := badd lowEnergy113_hz4 lowEnergy113_hz5 (by norm_num) (by norm_num)

theorem lowEnergy113_hz7 : B (149511908417021219 / 250000000000000000) (598047633668159487 / 1000000000000000000) (kappa ((967 / 2000))) := by rw [kappa_eq]; exact lowEnergy113_hz6

theorem lowEnergy113_hz8 : B (70525241078486937 / 100000000000000000) (141050482156973883 / 200000000000000000) (kdot ((601054163923 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (499176298201431609 / 1000000000000000000)) (a := (231494215235389139 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (62397037275178951 / 125000000000000000)) (a := (462988430470778209 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy113_hz9 : B (180633053984588277 / 500000000000000000) (72253221593835311 / 200000000000000000) (((601054163923 / 1000000000000) : ℝ)^2) := bsq (bpoint ((601054163923 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy113_hz10 : B (127746778406164689 / 200000000000000000) (319366946015411723 / 500000000000000000) ((1 : ℝ) - (((601054163923 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy113_hz9 (by norm_num) (by norm_num)

theorem lowEnergy113_hz11 : B (199802072691767803 / 250000000000000000) (399604145383535607 / 500000000000000000) (√((1 : ℝ) - (((601054163923 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy113_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy113_hz12 : B (127197950035604159 / 500000000000000000) (397493593861263 / 1562500000000000) ((√((1 : ℝ) - (((601054163923 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy113_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy113_hz13 : B (423894898118979807 / 1000000000000000000) (84778979623795967 / 200000000000000000) (((601054163923 / 1000000000000) : ℝ) * (kdot ((601054163923 / 1000000000000)))) := bmul (bpoint ((601054163923 / 1000000000000) : ℝ)) lowEnergy113_hz8 (by norm_num) (by norm_num)

theorem lowEnergy113_hz14 : B (1085265277104301 / 1600000000000000) (135658159638037631 / 200000000000000000) (((√((1 : ℝ) - (((601054163923 / 1000000000000) : ℝ)^2))) / Real.pi) + (((601054163923 / 1000000000000) : ℝ) * (kdot ((601054163923 / 1000000000000))))) := badd lowEnergy113_hz12 lowEnergy113_hz13 (by norm_num) (by norm_num)

theorem lowEnergy113_hz15 : B (1085265277104301 / 1600000000000000) (135658159638037631 / 200000000000000000) (kappa ((601054163923 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy113_hz14

theorem lowEnergy113 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (967 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (681093794431 / 1000000000000) := by
  have hk1 : kappa q ≤ (598047633669 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((967 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy113_hz7.2.trans (by norm_num))
  have hk2 : kappa ((601054163923 / 1000000000000) : ℝ) ≤ (678290798191 / 1000000000000) := lowEnergy113_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((773739383559 / 1000000000000) : ℝ)) (R := ((774605408963 / 1000000000000) : ℝ)) (Q2 := ((601054163923 / 1000000000000) : ℝ)) (T := ((824297362021 / 1000000000000) : ℝ))
    (B := ((681093794431 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy114_hz0 : B (330226446524735267 / 500000000000000000) (330226446524814929 / 500000000000000000) (kdot ((483 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (295219268888158907 / 500000000000000000)) (a := (106671869674345119 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (590438537776317813 / 1000000000000000000)) (a := (133339837092868833 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy114_hz1 : B (233289 / 1000000) (233289 / 1000000) (((483 / 1000) : ℝ)^2) := bsq (bpoint ((483 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy114_hz2 : B (766711 / 1000000) (766711 / 1000000) ((1 : ℝ) - (((483 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy114_hz1 (by norm_num) (by norm_num)

theorem lowEnergy114_hz3 : B (875620351522279317 / 1000000000000000000) (437810175761139659 / 500000000000000000) (√((1 : ℝ) - (((483 / 1000) : ℝ)^2))) := bsqrt lowEnergy114_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy114_hz4 : B (69679653608316877 / 250000000000000000) (278718614433267509 / 1000000000000000000) ((√((1 : ℝ) - (((483 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy114_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy114_hz5 : B (318998747342894267 / 1000000000000000000) (159499373671485611 / 500000000000000000) (((483 / 1000) : ℝ) * (kdot ((483 / 1000)))) := bmul (bpoint ((483 / 1000) : ℝ)) lowEnergy114_hz0 (by norm_num) (by norm_num)

theorem lowEnergy114_hz6 : B (23908694471046471 / 40000000000000000) (597717361776238731 / 1000000000000000000) (((√((1 : ℝ) - (((483 / 1000) : ℝ)^2))) / Real.pi) + (((483 / 1000) : ℝ) * (kdot ((483 / 1000))))) := badd lowEnergy114_hz4 lowEnergy114_hz5 (by norm_num) (by norm_num)

theorem lowEnergy114_hz7 : B (23908694471046471 / 40000000000000000) (597717361776238731 / 1000000000000000000) (kappa ((483 / 1000))) := by rw [kappa_eq]; exact lowEnergy114_hz6

theorem lowEnergy114_hz8 : B (11017508039074459 / 15625000000000000) (352560257250382711 / 500000000000000000) (kdot ((600722948871 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (499435132206318377 / 1000000000000000000)) (a := (463195612669366729 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (62429391525789797 / 125000000000000000)) (a := (231597806334683329 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy114_hz9 : B (70482043222709 / 195312500000000) (360868061300270081 / 1000000000000000000) (((600722948871 / 1000000000000) : ℝ)^2) := bsq (bpoint ((600722948871 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy114_hz10 : B (639131938699729919 / 1000000000000000000) (124830456777291 / 195312500000000) ((1 : ℝ) - (((600722948871 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy114_hz9 (by norm_num) (by norm_num)

theorem lowEnergy114_hz11 : B (159891455519015139 / 200000000000000000) (49966079849692231 / 62500000000000000) (√((1 : ℝ) - (((600722948871 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy114_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy114_hz12 : B (31809394380011461 / 125000000000000000) (254475155040091689 / 1000000000000000000) ((√((1 : ℝ) - (((600722948871 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy114_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy114_hz13 : B (423582074780336493 / 1000000000000000000) (423582074780336521 / 1000000000000000000) (((600722948871 / 1000000000000) : ℝ) * (kdot ((600722948871 / 1000000000000)))) := bmul (bpoint ((600722948871 / 1000000000000) : ℝ)) lowEnergy114_hz8 (by norm_num) (by norm_num)

theorem lowEnergy114_hz14 : B (678057229820428181 / 1000000000000000000) (67805722982042821 / 100000000000000000) (((√((1 : ℝ) - (((600722948871 / 1000000000000) : ℝ)^2))) / Real.pi) + (((600722948871 / 1000000000000) : ℝ) * (kdot ((600722948871 / 1000000000000))))) := badd lowEnergy114_hz12 lowEnergy114_hz13 (by norm_num) (by norm_num)

theorem lowEnergy114_hz15 : B (678057229820428181 / 1000000000000000000) (67805722982042821 / 100000000000000000) (kappa ((600722948871 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy114_hz14

theorem lowEnergy114 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (483 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (340429770619 / 500000000000) := by
  have hk1 : kappa q ≤ (597717361777 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((483 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy114_hz7.2.trans (by norm_num))
  have hk2 : kappa ((600722948871 / 1000000000000) : ℝ) ≤ (678057229821 / 1000000000000) := lowEnergy114_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((193381482079 / 250000000000) : ℝ)) (R := ((19359798843 / 25000000000) : ℝ)) (Q2 := ((600722948871 / 1000000000000) : ℝ)) (T := ((824155427051 / 1000000000000) : ℝ))
    (B := ((340429770619 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy115_hz0 : B (660271159157725229 / 1000000000000000000) (165067789789472431 / 250000000000000000) (kdot ((193 / 400))) := by
    constructor
    · apply bkdot_lower (q := (73852948553988309 / 125000000000000000)) (a := (266822407650666631 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (590823588431906471 / 1000000000000000000)) (a := (4269158522408599 / 8000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy115_hz1 : B (37249 / 160000) (37249 / 160000) (((193 / 400) : ℝ)^2) := bsq (bpoint ((193 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy115_hz2 : B (122751 / 160000) (122751 / 160000) ((1 : ℝ) - (((193 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy115_hz1 (by norm_num) (by norm_num)

theorem lowEnergy115_hz3 : B (875895969850301343 / 1000000000000000000) (27371749057821917 / 31250000000000000) (√((1 : ℝ) - (((193 / 400) : ℝ)^2))) := bsqrt lowEnergy115_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy115_hz4 : B (139403173235945183 / 500000000000000000) (278806346471890367 / 1000000000000000000) ((√((1 : ℝ) - (((193 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy115_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy115_hz5 : B (159290417146801211 / 500000000000000000) (2488912767919389 / 7812500000000000) (((193 / 400) : ℝ) * (kdot ((193 / 400)))) := bmul (bpoint ((193 / 400) : ℝ)) lowEnergy115_hz0 (by norm_num) (by norm_num)

theorem lowEnergy115_hz6 : B (149346795191373197 / 250000000000000000) (597387180765572159 / 1000000000000000000) (((√((1 : ℝ) - (((193 / 400) : ℝ)^2))) / Real.pi) + (((193 / 400) : ℝ) * (kdot ((193 / 400))))) := badd lowEnergy115_hz4 lowEnergy115_hz5 (by norm_num) (by norm_num)

theorem lowEnergy115_hz7 : B (149346795191373197 / 250000000000000000) (597387180765572159 / 1000000000000000000) (kappa ((193 / 400))) := by rw [kappa_eq]; exact lowEnergy115_hz6

theorem lowEnergy115_hz8 : B (352494347754177821 / 500000000000000000) (704988695508355689 / 1000000000000000000) (kdot ((30019591243 / 50000000000))) := by
    constructor
    · apply bkdot_lower (q := (124923467014306069 / 250000000000000000)) (a := (463402673458445743 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (19987754722288971 / 40000000000000000)) (a := (463402673458445671 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy115_hz9 : B (180235171679360457 / 500000000000000000) (72094068671744183 / 200000000000000000) (((30019591243 / 50000000000) : ℝ)^2) := bsq (bpoint ((30019591243 / 50000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy115_hz10 : B (127905931328255817 / 200000000000000000) (319764828320639543 / 500000000000000000) ((1 : ℝ) - (((30019591243 / 50000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy115_hz9 (by norm_num) (by norm_num)

theorem lowEnergy115_hz11 : B (39985299068572661 / 50000000000000000) (799705981371453221 / 1000000000000000000) (√((1 : ℝ) - (((30019591243 / 50000000000) : ℝ)^2))) := bsqrt lowEnergy115_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy115_hz12 : B (254554319910843897 / 1000000000000000000) (127277159955421949 / 500000000000000000) ((√((1 : ℝ) - (((30019591243 / 50000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy115_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy115_hz13 : B (423269449401932529 / 1000000000000000000) (211634724700966279 / 500000000000000000) (((30019591243 / 50000000000) : ℝ) * (kdot ((30019591243 / 50000000000)))) := bmul (bpoint ((30019591243 / 50000000000) : ℝ)) lowEnergy115_hz8 (by norm_num) (by norm_num)

theorem lowEnergy115_hz14 : B (338911884656388213 / 500000000000000000) (84727971164097057 / 125000000000000000) (((√((1 : ℝ) - (((30019591243 / 50000000000) : ℝ)^2))) / Real.pi) + (((30019591243 / 50000000000) : ℝ) * (kdot ((30019591243 / 50000000000))))) := badd lowEnergy115_hz12 lowEnergy115_hz13 (by norm_num) (by norm_num)

theorem lowEnergy115_hz15 : B (338911884656388213 / 500000000000000000) (84727971164097057 / 125000000000000000) (kappa ((30019591243 / 50000000000))) := by rw [kappa_eq]; exact lowEnergy115_hz14

theorem lowEnergy115 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (193 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (680625396173 / 1000000000000) := by
  have hk1 : kappa q ≤ (298693590383 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((193 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy115_hz7.2.trans (by norm_num))
  have hk2 : kappa ((30019591243 / 50000000000) : ℝ) ≤ (677823769313 / 1000000000000) := lowEnergy115_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((193328118229 / 250000000000) : ℝ)) (R := ((9677231229 / 12500000000) : ℝ)) (Q2 := ((30019591243 / 50000000000) : ℝ)) (T := ((164802706639 / 200000000000) : ℝ))
    (B := ((680625396173 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy116_hz0 : B (660089482404637011 / 1000000000000000000) (330044741202403421 / 500000000000000000) (kdot ((241 / 500))) := by
    constructor
    · apply bkdot_lower (q := (118241729574146369 / 200000000000000000)) (a := (533930192477748259 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (147802161967682961 / 250000000000000000)) (a := (53393019247748149 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy116_hz1 : B (58081 / 250000) (58081 / 250000) (((241 / 500) : ℝ)^2) := bsq (bpoint ((241 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy116_hz2 : B (191919 / 250000) (191919 / 250000) ((1 : ℝ) - (((241 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy116_hz1 (by norm_num) (by norm_num)

theorem lowEnergy116_hz3 : B (876171216144424593 / 1000000000000000000) (438085608072212297 / 500000000000000000) (√((1 : ℝ) - (((241 / 500) : ℝ)^2))) := bsqrt lowEnergy116_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy116_hz4 : B (278893960088445247 / 1000000000000000000) (278893960088445249 / 1000000000000000000) ((√((1 : ℝ) - (((241 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy116_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy116_hz5 : B (318163130519035039 / 1000000000000000000) (159081565259558449 / 500000000000000000) (((241 / 500) : ℝ) * (kdot ((241 / 500)))) := bmul (bpoint ((241 / 500) : ℝ)) lowEnergy116_hz0 (by norm_num) (by norm_num)

theorem lowEnergy116_hz6 : B (298528545303740143 / 500000000000000000) (597057090607562147 / 1000000000000000000) (((√((1 : ℝ) - (((241 / 500) : ℝ)^2))) / Real.pi) + (((241 / 500) : ℝ) * (kdot ((241 / 500))))) := badd lowEnergy116_hz4 lowEnergy116_hz5 (by norm_num) (by norm_num)

theorem lowEnergy116_hz7 : B (298528545303740143 / 500000000000000000) (597057090607562147 / 1000000000000000000) (kappa ((241 / 500))) := by rw [kappa_eq]; exact lowEnergy116_hz6

theorem lowEnergy116_hz8 : B (140971390740044337 / 200000000000000000) (704856953700221733 / 1000000000000000000) (kdot ((300030395929 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (15623515809678029 / 31250000000000000)) (a := (463609613006747881 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (499952505909696927 / 1000000000000000000)) (a := (463609613006747807 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy116_hz9 : B (360072953925249999 / 1000000000000000000) (1440291815701 / 4000000000000) (((300030395929 / 500000000000) : ℝ)^2) := bsq (bpoint ((300030395929 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy116_hz10 : B (2559708184299 / 4000000000000) (639927046074750001 / 1000000000000000000) ((1 : ℝ) - (((300030395929 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy116_hz9 (by norm_num) (by norm_num)

theorem lowEnergy116_hz11 : B (799954402497261089 / 1000000000000000000) (799954402497261091 / 1000000000000000000) (√((1 : ℝ) - (((300030395929 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy116_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy116_hz12 : B (254633394811125449 / 1000000000000000000) (254633394811125451 / 1000000000000000000) ((√((1 : ℝ) - (((300030395929 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy116_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy116_hz13 : B (422957021783972667 / 1000000000000000000) (422957021783972697 / 1000000000000000000) (((300030395929 / 500000000000) : ℝ) * (kdot ((300030395929 / 500000000000)))) := bmul (bpoint ((300030395929 / 500000000000) : ℝ)) lowEnergy116_hz8 (by norm_num) (by norm_num)

theorem lowEnergy116_hz14 : B (169397604148774529 / 250000000000000000) (169397604148774537 / 250000000000000000) (((√((1 : ℝ) - (((300030395929 / 500000000000) : ℝ)^2))) / Real.pi) + (((300030395929 / 500000000000) : ℝ) * (kdot ((300030395929 / 500000000000))))) := badd lowEnergy116_hz12 lowEnergy116_hz13 (by norm_num) (by norm_num)

theorem lowEnergy116_hz15 : B (169397604148774529 / 250000000000000000) (169397604148774537 / 250000000000000000) (kappa ((300030395929 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy116_hz14

theorem lowEnergy116 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (241 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (680391359169 / 1000000000000) := by
  have hk1 : kappa q ≤ (37316068163 / 62500000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((241 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy116_hz7.2.trans (by norm_num))
  have hk2 : kappa ((300030395929 / 500000000000) : ℝ) ≤ (169397604149 / 250000000000) := lowEnergy116_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((386549508669 / 500000000000) : ℝ)) (R := ((386982521371 / 500000000000) : ℝ)) (Q2 := ((300030395929 / 500000000000) : ℝ)) (T := ((51491980027 / 62500000000) : ℝ))
    (B := ((680391359169 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy117_hz0 : B (32995393133860887 / 50000000000000000) (659907862677393077 / 1000000000000000000) (kdot ((963 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (591593716338277941 / 1000000000000000000)) (a := (26710774003922597 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (29579685816913897 / 50000000000000000)) (a := (534215480078176523 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy117_hz1 : B (927369 / 4000000) (927369 / 4000000) (((963 / 2000) : ℝ)^2) := bsq (bpoint ((963 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy117_hz2 : B (3072631 / 4000000) (3072631 / 4000000) ((1 : ℝ) - (((963 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy117_hz1 (by norm_num) (by norm_num)

theorem lowEnergy117_hz3 : B (54777880672197423 / 62500000000000000) (876446090755158769 / 1000000000000000000) (√((1 : ℝ) - (((963 / 2000) : ℝ)^2))) := bsqrt lowEnergy117_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy117_hz4 : B (34872681924312857 / 125000000000000000) (139490727697251429 / 500000000000000000) ((√((1 : ℝ) - (((963 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy117_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy117_hz5 : B (317745635879080341 / 1000000000000000000) (317745635879164767 / 1000000000000000000) (((963 / 2000) : ℝ) * (kdot ((963 / 2000)))) := bmul (bpoint ((963 / 2000) : ℝ)) lowEnergy117_hz0 (by norm_num) (by norm_num)

theorem lowEnergy117_hz6 : B (596727091273583197 / 1000000000000000000) (4773816730189341 / 8000000000000000) (((√((1 : ℝ) - (((963 / 2000) : ℝ)^2))) / Real.pi) + (((963 / 2000) : ℝ) * (kdot ((963 / 2000))))) := badd lowEnergy117_hz4 lowEnergy117_hz5 (by norm_num) (by norm_num)

theorem lowEnergy117_hz7 : B (596727091273583197 / 1000000000000000000) (4773816730189341 / 8000000000000000) (kappa ((963 / 2000))) := by rw [kappa_eq]; exact lowEnergy117_hz6

theorem lowEnergy117_hz8 : B (176181322242596571 / 250000000000000000) (704725288970386333 / 1000000000000000000) (kdot ((149932462459 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (125052761479143019 / 250000000000000000)) (a := (463816431480741771 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (20008441836662883 / 40000000000000000)) (a := (7247131741886589 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy117_hz9 : B (359675892784311109 / 1000000000000000000) (35967589278431111 / 100000000000000000) (((149932462459 / 250000000000) : ℝ)^2) := bsq (bpoint ((149932462459 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy117_hz10 : B (64032410721568889 / 100000000000000000) (640324107215688891 / 1000000000000000000) ((1 : ℝ) - (((149932462459 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy117_hz9 (by norm_num) (by norm_num)

theorem lowEnergy117_hz11 : B (800202541370426347 / 1000000000000000000) (800202541370426349 / 1000000000000000000) (√((1 : ℝ) - (((149932462459 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy117_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy117_hz12 : B (31839047483450057 / 125000000000000000) (127356189933800229 / 500000000000000000) ((√((1 : ℝ) - (((149932462459 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy117_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy117_hz13 : B (422644791729841473 / 1000000000000000000) (422644791729841503 / 1000000000000000000) (((149932462459 / 250000000000) : ℝ) * (kdot ((149932462459 / 250000000000)))) := bmul (bpoint ((149932462459 / 250000000000) : ℝ)) lowEnergy117_hz8 (by norm_num) (by norm_num)

theorem lowEnergy117_hz14 : B (677357171597441929 / 1000000000000000000) (677357171597441961 / 1000000000000000000) (((√((1 : ℝ) - (((149932462459 / 250000000000) : ℝ)^2))) / Real.pi) + (((149932462459 / 250000000000) : ℝ) * (kdot ((149932462459 / 250000000000))))) := badd lowEnergy117_hz12 lowEnergy117_hz13 (by norm_num) (by norm_num)

theorem lowEnergy117_hz15 : B (677357171597441929 / 1000000000000000000) (677357171597441961 / 1000000000000000000) (kappa ((149932462459 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy117_hz14

theorem lowEnergy117 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (963 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (13603148603 / 20000000000) := by
  have hk1 : kappa q ≤ (298363545637 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((963 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy117_hz7.2.trans (by norm_num))
  have hk2 : kappa ((149932462459 / 250000000000) : ℝ) ≤ (338678585799 / 500000000000) := lowEnergy117_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((193221390391 / 250000000000) : ℝ)) (R := ((96718948371 / 125000000000) : ℝ)) (Q2 := ((149932462459 / 250000000000) : ℝ)) (T := ((823729868739 / 1000000000000) : ℝ))
    (B := ((13603148603 / 20000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy118_hz0 : B (329863149931365361 / 500000000000000000) (659726299862911739 / 1000000000000000000) (kdot ((481 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (73997349259968009 / 125000000000000000)) (a := (534500678280530691 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (591978794079744071 / 1000000000000000000)) (a := (33406292392515397 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy118_hz1 : B (231361 / 1000000) (231361 / 1000000) (((481 / 1000) : ℝ)^2) := bsq (bpoint ((481 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy118_hz2 : B (768639 / 1000000) (768639 / 1000000) ((1 : ℝ) - (((481 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy118_hz1 (by norm_num) (by norm_num)

theorem lowEnergy118_hz3 : B (87672059403210097 / 100000000000000000) (876720594032100971 / 1000000000000000000) (√((1 : ℝ) - (((481 / 1000) : ℝ)^2))) := bsqrt lowEnergy118_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy118_hz4 : B (139534416250671703 / 500000000000000000) (17441802031333963 / 62500000000000000) ((√((1 : ℝ) - (((481 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy118_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy118_hz5 : B (317328350233973477 / 1000000000000000000) (317328350234060547 / 1000000000000000000) (((481 / 1000) : ℝ) * (kdot ((481 / 1000)))) := bmul (bpoint ((481 / 1000) : ℝ)) lowEnergy118_hz0 (by norm_num) (by norm_num)

theorem lowEnergy118_hz6 : B (596397182735316883 / 1000000000000000000) (119279436547080791 / 200000000000000000) (((√((1 : ℝ) - (((481 / 1000) : ℝ)^2))) / Real.pi) + (((481 / 1000) : ℝ) * (kdot ((481 / 1000))))) := badd lowEnergy118_hz4 lowEnergy118_hz5 (by norm_num) (by norm_num)

theorem lowEnergy118_hz7 : B (596397182735316883 / 1000000000000000000) (119279436547080791 / 200000000000000000) (kappa ((481 / 1000))) := by rw [kappa_eq]; exact lowEnergy118_hz6

theorem lowEnergy118_hz8 : B (140918740242941693 / 200000000000000000) (176148425303677129 / 250000000000000000) (kdot ((599398998769 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (250234744113597479 / 500000000000000000)) (a := (464023129044011673 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (500469488227194957 / 1000000000000000000)) (a := (92804625808802319 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy118_hz9 : B (359279159725279663 / 1000000000000000000) (22454947482829979 / 62500000000000000) (((599398998769 / 1000000000000) : ℝ)^2) := bsq (bpoint ((599398998769 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy118_hz10 : B (40045052517170021 / 62500000000000000) (640720840274720337 / 1000000000000000000) ((1 : ℝ) - (((599398998769 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy118_hz9 (by norm_num) (by norm_num)

theorem lowEnergy118_hz11 : B (100056299798126181 / 125000000000000000) (800450398385009449 / 1000000000000000000) (√((1 : ℝ) - (((599398998769 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy118_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy118_hz12 : B (254791275205702257 / 1000000000000000000) (254791275205702259 / 1000000000000000000) ((√((1 : ℝ) - (((599398998769 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy118_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy118_hz13 : B (422332759047040193 / 1000000000000000000) (13197898720220007 / 31250000000000000) (((599398998769 / 1000000000000) : ℝ) * (kdot ((599398998769 / 1000000000000)))) := bmul (bpoint ((599398998769 / 1000000000000) : ℝ)) lowEnergy118_hz8 (by norm_num) (by norm_num)

theorem lowEnergy118_hz14 : B (13542480685054849 / 20000000000000000) (677124034252742483 / 1000000000000000000) (((√((1 : ℝ) - (((599398998769 / 1000000000000) : ℝ)^2))) / Real.pi) + (((599398998769 / 1000000000000) : ℝ) * (kdot ((599398998769 / 1000000000000))))) := badd lowEnergy118_hz12 lowEnergy118_hz13 (by norm_num) (by norm_num)

theorem lowEnergy118_hz15 : B (13542480685054849 / 20000000000000000) (677124034252742483 / 1000000000000000000) (kappa ((599398998769 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy118_hz14

theorem lowEnergy118 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (169980902263 / 250000000000) := by
  have hk1 : kappa q ≤ (37274823921 / 62500000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((481 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy118_hz7.2.trans (by norm_num))
  have hk2 : kappa ((599398998769 / 1000000000000) : ℝ) ≤ (677124034253 / 1000000000000) := lowEnergy118_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((772672105577 / 1000000000000) : ℝ)) (R := ((773538130981 / 1000000000000) : ℝ)) (Q2 := ((599398998769 / 1000000000000) : ℝ)) (T := ((823588098097 / 1000000000000) : ℝ))
    (B := ((169980902263 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy119_hz0 : B (659544793848689817 / 1000000000000000000) (131908958769775339 / 200000000000000000) (kdot ((961 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (11847277626800927 / 20000000000000000)) (a := (534785787260677327 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (592363881340046349 / 1000000000000000000)) (a := (534785787260383781 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy119_hz1 : B (923521 / 4000000) (923521 / 4000000) (((961 / 2000) : ℝ)^2) := bsq (bpoint ((961 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy119_hz2 : B (3076479 / 4000000) (3076479 / 4000000) ((1 : ℝ) - (((961 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy119_hz1 (by norm_num) (by norm_num)

theorem lowEnergy119_hz3 : B (43849736316196931 / 50000000000000000) (876994726323938621 / 1000000000000000000) (√((1 : ℝ) - (((961 / 2000) : ℝ)^2))) := bsqrt lowEnergy119_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy119_hz4 : B (5583121830399151 / 20000000000000000) (17447255719997347 / 62500000000000000) ((√((1 : ℝ) - (((961 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy119_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy119_hz5 : B (316911273444295457 / 1000000000000000000) (79227818361096313 / 250000000000000000) (((961 / 2000) : ℝ) * (kdot ((961 / 2000)))) := bmul (bpoint ((961 / 2000) : ℝ)) lowEnergy119_hz0 (by norm_num) (by norm_num)

theorem lowEnergy119_hz6 : B (596067364964253007 / 1000000000000000000) (149016841241085701 / 250000000000000000) (((√((1 : ℝ) - (((961 / 2000) : ℝ)^2))) / Real.pi) + (((961 / 2000) : ℝ) * (kdot ((961 / 2000))))) := badd lowEnergy119_hz4 lowEnergy119_hz5 (by norm_num) (by norm_num)

theorem lowEnergy119_hz7 : B (596067364964253007 / 1000000000000000000) (149016841241085701 / 250000000000000000) (kappa ((961 / 2000))) := by rw [kappa_eq]; exact lowEnergy119_hz6

theorem lowEnergy119_hz8 : B (704462190326904813 / 1000000000000000000) (140892438065380973 / 200000000000000000) (kdot ((299534119313 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (500727832995233401 / 1000000000000000000)) (a := (232114852931753593 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2503639164976167 / 5000000000000000)) (a := (232114852931753553 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy119_hz9 : B (179441377265229039 / 500000000000000000) (358882754530458079 / 1000000000000000000) (((299534119313 / 500000000000) : ℝ)^2) := bsq (bpoint ((299534119313 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy119_hz10 : B (641117245469541921 / 1000000000000000000) (320558622734770961 / 500000000000000000) ((1 : ℝ) - (((299534119313 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy119_hz9 (by norm_num) (by norm_num)

theorem lowEnergy119_hz11 : B (400348986969350879 / 500000000000000000) (2502181168558443 / 3125000000000000) (√((1 : ℝ) - (((299534119313 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy119_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy119_hz12 : B (50974016190403989 / 200000000000000000) (254870080952019947 / 1000000000000000000) ((√((1 : ℝ) - (((299534119313 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy119_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy119_hz13 : B (422020923537752841 / 1000000000000000000) (422020923537752873 / 1000000000000000000) (((299534119313 / 500000000000) : ℝ) * (kdot ((299534119313 / 500000000000)))) := bmul (bpoint ((299534119313 / 500000000000) : ℝ)) lowEnergy119_hz8 (by norm_num) (by norm_num)

theorem lowEnergy119_hz14 : B (338445502244886393 / 500000000000000000) (33844550224488641 / 50000000000000000) (((√((1 : ℝ) - (((299534119313 / 500000000000) : ℝ)^2))) / Real.pi) + (((299534119313 / 500000000000) : ℝ) * (kdot ((299534119313 / 500000000000))))) := badd lowEnergy119_hz12 lowEnergy119_hz13 (by norm_num) (by norm_num)

theorem lowEnergy119_hz15 : B (338445502244886393 / 500000000000000000) (33844550224488641 / 50000000000000000) (kappa ((299534119313 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy119_hz14

theorem lowEnergy119 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (961 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (135937979161 / 200000000000) := by
  have hk1 : kappa q ≤ (119213472993 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((961 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy119_hz7.2.trans (by norm_num))
  have hk2 : kappa ((299534119313 / 500000000000) : ℝ) ≤ (67689100449 / 100000000000) := lowEnergy119_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((772458649357 / 1000000000000) : ℝ)) (R := ((773324674761 / 1000000000000) : ℝ)) (Q2 := ((299534119313 / 500000000000) : ℝ)) (T := ((164689273697 / 200000000000) : ℝ))
    (B := ((135937979161 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy120_hz0 : B (659363344522858571 / 1000000000000000000) (82420418065381437 / 125000000000000000) (kdot ((12 / 25))) := by
    constructor
    · apply bkdot_lower (q := (296374489181909579 / 500000000000000000)) (a := (535070807195192459 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (592748978363819157 / 1000000000000000000)) (a := (267535403597444707 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy120_hz1 : B (144 / 625) (144 / 625) (((12 / 25) : ℝ)^2) := bsq (bpoint ((12 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy120_hz2 : B (481 / 625) (481 / 625) ((1 : ℝ) - (((12 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy120_hz1 (by norm_num) (by norm_num)

theorem lowEnergy120_hz3 : B (6853660062331659 / 7812500000000000) (877268487978452353 / 1000000000000000000) (√((1 : ℝ) - (((12 / 25) : ℝ)^2))) := bsqrt lowEnergy120_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy120_hz4 : B (279243232561047303 / 1000000000000000000) (34905404070130913 / 125000000000000000) ((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) := bdiv lowEnergy120_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy120_hz5 : B (158247202685486057 / 500000000000000000) (316494405371064719 / 1000000000000000000) (((12 / 25) : ℝ) * (kdot ((12 / 25)))) := bmul (bpoint ((12 / 25) : ℝ)) lowEnergy120_hz0 (by norm_num) (by norm_num)

theorem lowEnergy120_hz6 : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) + (((12 / 25) : ℝ) * (kdot ((12 / 25))))) := badd lowEnergy120_hz4 lowEnergy120_hz5 (by norm_num) (by norm_num)

theorem lowEnergy120_hz7 : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (kappa ((12 / 25))) := by rw [kappa_eq]; exact lowEnergy120_hz6

theorem lowEnergy120_hz8 : B (4402067226260823 / 6250000000000000) (352165378100865867 / 500000000000000000) (kdot ((299368784689 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (250493040186214557 / 500000000000000000)) (a := (464436162104544643 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (500986080372429113 / 1000000000000000000)) (a := (464436162104544561 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy120_hz9 : B (358486676984675363 / 1000000000000000000) (89621669246168841 / 250000000000000000) (((299368784689 / 500000000000) : ℝ)^2) := bsq (bpoint ((299368784689 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy120_hz10 : B (160378330753831159 / 250000000000000000) (641513323015324637 / 1000000000000000000) ((1 : ℝ) - (((299368784689 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy120_hz9 (by norm_num) (by norm_num)

theorem lowEnergy120_hz11 : B (800945268426828673 / 1000000000000000000) (400472634213414337 / 500000000000000000) (√((1 : ℝ) - (((299368784689 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy120_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy120_hz12 : B (127474398616194751 / 500000000000000000) (1991787478378043 / 7812500000000000) ((√((1 : ℝ) - (((299368784689 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy120_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy120_hz13 : B (16868371400255741 / 40000000000000000) (210854642503196779 / 500000000000000000) (((299368784689 / 500000000000) : ℝ) * (kdot ((299368784689 / 500000000000)))) := bmul (bpoint ((299368784689 / 500000000000) : ℝ)) lowEnergy120_hz8 (by norm_num) (by norm_num)

theorem lowEnergy120_hz14 : B (676658082238783027 / 1000000000000000000) (338329041119391531 / 500000000000000000) (((√((1 : ℝ) - (((299368784689 / 500000000000) : ℝ)^2))) / Real.pi) + (((299368784689 / 500000000000) : ℝ) * (kdot ((299368784689 / 500000000000))))) := badd lowEnergy120_hz12 lowEnergy120_hz13 (by norm_num) (by norm_num)

theorem lowEnergy120_hz15 : B (676658082238783027 / 1000000000000000000) (338329041119391531 / 500000000000000000) (kappa ((299368784689 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy120_hz14

theorem lowEnergy120 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (12 / 25)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (135891258067 / 200000000000) := by
  have hk1 : kappa q ≤ (595737637933 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((12 / 25) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy120_hz7.2.trans (by norm_num))
  have hk2 : kappa ((299368784689 / 500000000000) : ℝ) ≤ (676658082239 / 1000000000000) := lowEnergy120_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((154449038577 / 200000000000) : ℝ)) (R := ((773111218289 / 1000000000000) : ℝ)) (Q2 := ((299368784689 / 500000000000) : ℝ)) (T := ((823304679879 / 1000000000000) : ℝ))
    (B := ((135891258067 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy121_hz0 : B (82397743971656167 / 125000000000000000) (659181951773448499 / 1000000000000000000) (kdot ((959 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (148283521348854157 / 250000000000000000)) (a := (33459733641249117 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (593134085395416627 / 1000000000000000000)) (a := (133838934564918257 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy121_hz1 : B (919681 / 4000000) (919681 / 4000000) (((959 / 2000) : ℝ)^2) := bsq (bpoint ((959 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy121_hz2 : B (3080319 / 4000000) (3080319 / 4000000) ((1 : ℝ) - (((959 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy121_hz1 (by norm_num) (by norm_num)

theorem lowEnergy121_hz3 : B (8775418793425189 / 10000000000000000) (877541879342518901 / 1000000000000000000) (√((1 : ℝ) - (((959 / 2000) : ℝ)^2))) := bsqrt lowEnergy121_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy121_hz4 : B (279330255735026957 / 1000000000000000000) (139665127867513479 / 500000000000000000) ((√((1 : ℝ) - (((959 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy121_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy121_hz5 : B (9877429558602283 / 31250000000000000) (79019436468842139 / 250000000000000000) (((959 / 2000) : ℝ) * (kdot ((959 / 2000)))) := bmul (bpoint ((959 / 2000) : ℝ)) lowEnergy121_hz0 (by norm_num) (by norm_num)

theorem lowEnergy121_hz6 : B (595408001610300013 / 1000000000000000000) (297704000805197757 / 500000000000000000) (((√((1 : ℝ) - (((959 / 2000) : ℝ)^2))) / Real.pi) + (((959 / 2000) : ℝ) * (kdot ((959 / 2000))))) := badd lowEnergy121_hz4 lowEnergy121_hz5 (by norm_num) (by norm_num)

theorem lowEnergy121_hz7 : B (595408001610300013 / 1000000000000000000) (297704000805197757 / 500000000000000000) (kappa ((959 / 2000))) := by rw [kappa_eq]; exact lowEnergy121_hz6

theorem lowEnergy121_hz8 : B (704199398734585851 / 1000000000000000000) (140839879746917181 / 200000000000000000) (kdot ((598406990997 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (501244230509380601 / 1000000000000000000)) (a := (464642497931434393 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2506221152546903 / 5000000000000000)) (a := (46464249793143431 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy121_hz9 : B (358090926874083639 / 1000000000000000000) (8952273171852091 / 25000000000000000) (((598406990997 / 1000000000000) : ℝ)^2) := bsq (bpoint ((598406990997 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy121_hz10 : B (16047726828147909 / 25000000000000000) (641909073125916361 / 1000000000000000000) ((1 : ℝ) - (((598406990997 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy121_hz9 (by norm_num) (by norm_num)

theorem lowEnergy121_hz11 : B (801192282243105709 / 1000000000000000000) (80119228224310571 / 100000000000000000) (√((1 : ℝ) - (((598406990997 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy121_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy121_hz12 : B (25502742417213447 / 100000000000000000) (255027424172134471 / 1000000000000000000) ((√((1 : ℝ) - (((598406990997 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy121_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy121_hz13 : B (13168682601833129 / 31250000000000000) (421397843258660161 / 1000000000000000000) (((598406990997 / 1000000000000) : ℝ) * (kdot ((598406990997 / 1000000000000)))) := bmul (bpoint ((598406990997 / 1000000000000) : ℝ)) lowEnergy121_hz8 (by norm_num) (by norm_num)

theorem lowEnergy121_hz14 : B (338212633715397299 / 500000000000000000) (84553158428849329 / 125000000000000000) (((√((1 : ℝ) - (((598406990997 / 1000000000000) : ℝ)^2))) / Real.pi) + (((598406990997 / 1000000000000) : ℝ) * (kdot ((598406990997 / 1000000000000))))) := badd lowEnergy121_hz12 lowEnergy121_hz13 (by norm_num) (by norm_num)

theorem lowEnergy121_hz15 : B (338212633715397299 / 500000000000000000) (84553158428849329 / 125000000000000000) (kappa ((598406990997 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy121_hz14

theorem lowEnergy121 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (959 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (5306428067 / 7812500000) := by
  have hk1 : kappa q ≤ (595408001611 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((959 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy121_hz7.2.trans (by norm_num))
  have hk2 : kappa ((598406990997 / 1000000000000) : ℝ) ≤ (676425267431 / 1000000000000) := lowEnergy121_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((772031736143 / 1000000000000) : ℝ)) (R := ((772897761547 / 1000000000000) : ℝ)) (Q2 := ((598406990997 / 1000000000000) : ℝ)) (T := ((823163032261 / 1000000000000) : ℝ))
    (B := ((5306428067 / 7812500000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy122_hz0 : B (659000615488122401 / 1000000000000000000) (659000615488328001 / 1000000000000000000) (kdot ((479 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (9273737541858033 / 15625000000000000)) (a := (535640580630577893 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (593519202678914111 / 1000000000000000000)) (a := (535640580630254939 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy122_hz1 : B (229441 / 1000000) (229441 / 1000000) (((479 / 1000) : ℝ)^2) := bsq (bpoint ((479 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy122_hz2 : B (770559 / 1000000) (770559 / 1000000) ((1 : ℝ) - (((479 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy122_hz1 (by norm_num) (by norm_num)

theorem lowEnergy122_hz3 : B (877814900762113971 / 1000000000000000000) (219453725190528493 / 250000000000000000) (√((1 : ℝ) - (((479 / 1000) : ℝ)^2))) := bsqrt lowEnergy122_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy122_hz4 : B (279417161152024001 / 1000000000000000000) (139708580576012001 / 500000000000000000) ((√((1 : ℝ) - (((479 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy122_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy122_hz5 : B (31566129481881063 / 100000000000000000) (315661294818909113 / 1000000000000000000) (((479 / 1000) : ℝ) * (kdot ((479 / 1000)))) := bmul (bpoint ((479 / 1000) : ℝ)) lowEnergy122_hz0 (by norm_num) (by norm_num)

theorem lowEnergy122_hz6 : B (595078455970834631 / 1000000000000000000) (119015691194186623 / 200000000000000000) (((√((1 : ℝ) - (((479 / 1000) : ℝ)^2))) / Real.pi) + (((479 / 1000) : ℝ) * (kdot ((479 / 1000))))) := badd lowEnergy122_hz4 lowEnergy122_hz5 (by norm_num) (by norm_num)

theorem lowEnergy122_hz7 : B (595078455970834631 / 1000000000000000000) (119015691194186623 / 200000000000000000) (kappa ((479 / 1000))) := by rw [kappa_eq]; exact lowEnergy122_hz6

theorem lowEnergy122_hz8 : B (140813623564141753 / 200000000000000000) (704068117820708821 / 1000000000000000000) (kdot ((299038251727 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (250751141778553183 / 500000000000000000)) (a := (464848713508730797 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (100300456711421273 / 200000000000000000)) (a := (464848713508730711 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy122_hz9 : B (357695503983762473 / 1000000000000000000) (178847751991881237 / 500000000000000000) (((299038251727 / 500000000000) : ℝ)^2) := bsq (bpoint ((299038251727 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy122_hz10 : B (321152248008118763 / 500000000000000000) (642304496016237527 / 1000000000000000000) ((1 : ℝ) - (((299038251727 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy122_hz9 (by norm_num) (by norm_num)

theorem lowEnergy122_hz11 : B (801439015781136977 / 1000000000000000000) (801439015781136979 / 1000000000000000000) (√((1 : ℝ) - (((299038251727 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy122_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy122_hz12 : B (255105961896542927 / 1000000000000000000) (15944122618533933 / 62500000000000000) ((√((1 : ℝ) - (((299038251727 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy122_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy122_hz13 : B (105271649524912101 / 250000000000000000) (421086598099648439 / 1000000000000000000) (((299038251727 / 500000000000) : ℝ) * (kdot ((299038251727 / 500000000000)))) := bmul (bpoint ((299038251727 / 500000000000) : ℝ)) lowEnergy122_hz8 (by norm_num) (by norm_num)

theorem lowEnergy122_hz14 : B (676192559996191331 / 1000000000000000000) (676192559996191367 / 1000000000000000000) (((√((1 : ℝ) - (((299038251727 / 500000000000) : ℝ)^2))) / Real.pi) + (((299038251727 / 500000000000) : ℝ) * (kdot ((299038251727 / 500000000000))))) := badd lowEnergy122_hz12 lowEnergy122_hz13 (by norm_num) (by norm_num)

theorem lowEnergy122_hz15 : B (676192559996191331 / 1000000000000000000) (676192559996191367 / 1000000000000000000) (kappa ((299038251727 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy122_hz14

theorem lowEnergy122 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (479 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (339494701229 / 500000000000) := by
  have hk1 : kappa q ≤ (595078455971 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((479 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy122_hz7.2.trans (by norm_num))
  have hk2 : kappa ((299038251727 / 500000000000) : ℝ) ≤ (676192559997 / 1000000000000) := lowEnergy122_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((96477284889 / 125000000000) : ℝ)) (R := ((193171076129 / 250000000000) : ℝ)) (Q2 := ((299038251727 / 500000000000) : ℝ)) (T := ((823021425609 / 1000000000000) : ℝ))
    (B := ((339494701229 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy123_hz0 : B (82352416944498141 / 125000000000000000) (82352416944524671 / 125000000000000000) (kdot ((957 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (148476082614527411 / 250000000000000000)) (a := (2143701337928403 / 4000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (593904330458109643 / 1000000000000000000)) (a := (267962667240883683 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy123_hz1 : B (915849 / 4000000) (915849 / 4000000) (((957 / 2000) : ℝ)^2) := bsq (bpoint ((957 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy123_hz2 : B (3084151 / 4000000) (3084151 / 4000000) ((1 : ℝ) - (((957 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy123_hz1 (by norm_num) (by norm_num)

theorem lowEnergy123_hz3 : B (219521888145578777 / 250000000000000000) (878087552582315109 / 1000000000000000000) (√((1 : ℝ) - (((957 / 2000) : ℝ)^2))) := bsqrt lowEnergy123_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy123_hz4 : B (69875987230470007 / 250000000000000000) (279503948921880029 / 1000000000000000000) ((√((1 : ℝ) - (((957 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy123_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy123_hz5 : B (315245052063538883 / 1000000000000000000) (315245052063640441 / 1000000000000000000) (((957 / 2000) : ℝ) * (kdot ((957 / 2000)))) := bmul (bpoint ((957 / 2000) : ℝ)) lowEnergy123_hz0 (by norm_num) (by norm_num)

theorem lowEnergy123_hz6 : B (594749000985418911 / 1000000000000000000) (59474900098552047 / 100000000000000000) (((√((1 : ℝ) - (((957 / 2000) : ℝ)^2))) / Real.pi) + (((957 / 2000) : ℝ) * (kdot ((957 / 2000))))) := badd lowEnergy123_hz4 lowEnergy123_hz5 (by norm_num) (by norm_num)

theorem lowEnergy123_hz7 : B (594749000985418911 / 1000000000000000000) (59474900098552047 / 100000000000000000) (kappa ((957 / 2000))) := by rw [kappa_eq]; exact lowEnergy123_hz6

theorem lowEnergy123_hz8 : B (351968456678585789 / 500000000000000000) (140787382671434327 / 200000000000000000) (kdot ((149436526681 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (62720029957892777 / 125000000000000000)) (a := (93010961799622821 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (100352047932628443 / 200000000000000000)) (a := (232527404499057009 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy123_hz9 : B (178650204051849799 / 500000000000000000) (357300408103699599 / 1000000000000000000) (((149436526681 / 250000000000) : ℝ)^2) := bsq (bpoint ((149436526681 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy123_hz10 : B (642699591896300401 / 1000000000000000000) (321349795948150201 / 500000000000000000) ((1 : ℝ) - (((149436526681 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy123_hz9 (by norm_num) (by norm_num)

theorem lowEnergy123_hz11 : B (400842734715343319 / 500000000000000000) (10021068367883583 / 12500000000000000) (√((1 : ℝ) - (((149436526681 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy123_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy123_hz12 : B (255184410529680659 / 1000000000000000000) (255184410529680661 / 1000000000000000000) ((√((1 : ℝ) - (((149436526681 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy123_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy123_hz13 : B (420775549338559023 / 1000000000000000000) (210387774669279529 / 500000000000000000) (((149436526681 / 250000000000) : ℝ) * (kdot ((149436526681 / 250000000000)))) := bmul (bpoint ((149436526681 / 250000000000) : ℝ)) lowEnergy123_hz8 (by norm_num) (by norm_num)

theorem lowEnergy123_hz14 : B (337979979934119841 / 500000000000000000) (675959959868239719 / 1000000000000000000) (((√((1 : ℝ) - (((149436526681 / 250000000000) : ℝ)^2))) / Real.pi) + (((149436526681 / 250000000000) : ℝ) * (kdot ((149436526681 / 250000000000))))) := badd lowEnergy123_hz12 lowEnergy123_hz13 (by norm_num) (by norm_num)

theorem lowEnergy123_hz15 : B (337979979934119841 / 500000000000000000) (675959959868239719 / 1000000000000000000) (kappa ((149436526681 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy123_hz14

theorem lowEnergy123 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (957 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (84844514989 / 125000000000) := by
  have hk1 : kappa q ≤ (297374500493 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((957 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy123_hz7.2.trans (by norm_num))
  have hk2 : kappa ((149436526681 / 250000000000) : ℝ) ≤ (675959959869 / 1000000000000) := lowEnergy123_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((30864192871 / 40000000000) : ℝ)) (R := ((772470847179 / 1000000000000) : ℝ)) (Q2 := ((149436526681 / 250000000000) : ℝ)) (T := ((822879859903 / 1000000000000) : ℝ))
    (B := ((84844514989 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy124_hz0 : B (131727622373118217 / 200000000000000000) (329319055932905087 / 500000000000000000) (kdot ((239 / 500))) := by
    constructor
    · apply bkdot_lower (q := (594289468976525397 / 1000000000000000000)) (a := (67026249998662491 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (148572367244131349 / 250000000000000000)) (a := (107241999997791157 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy124_hz1 : B (57121 / 250000) (57121 / 250000) (((239 / 500) : ℝ)^2) := bsq (bpoint ((239 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy124_hz2 : B (192879 / 250000) (192879 / 250000) ((1 : ℝ) - (((239 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy124_hz1 (by norm_num) (by norm_num)

theorem lowEnergy124_hz3 : B (175671967029460907 / 200000000000000000) (109794979393413067 / 125000000000000000) (√((1 : ℝ) - (((239 / 500) : ℝ)^2))) := bsqrt lowEnergy124_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy124_hz4 : B (279590619154151643 / 1000000000000000000) (55918123830830329 / 200000000000000000) ((√((1 : ℝ) - (((239 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy124_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy124_hz5 : B (157414508735876269 / 500000000000000000) (19676813591991079 / 62500000000000000) (((239 / 500) : ℝ) * (kdot ((239 / 500)))) := bmul (bpoint ((239 / 500) : ℝ)) lowEnergy124_hz0 (by norm_num) (by norm_num)

theorem lowEnergy124_hz6 : B (594419636625904181 / 1000000000000000000) (594419636626008909 / 1000000000000000000) (((√((1 : ℝ) - (((239 / 500) : ℝ)^2))) / Real.pi) + (((239 / 500) : ℝ) * (kdot ((239 / 500))))) := badd lowEnergy124_hz4 lowEnergy124_hz5 (by norm_num) (by norm_num)

theorem lowEnergy124_hz7 : B (594419636625904181 / 1000000000000000000) (594419636626008909 / 1000000000000000000) (kappa ((239 / 500))) := by rw [kappa_eq]; exact lowEnergy124_hz6

theorem lowEnergy124_hz8 : B (175951446309824889 / 250000000000000000) (140761157047859923 / 200000000000000000) (kdot ((597415800777 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (251009049489284857 / 500000000000000000)) (a := (93052156912801401 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (502018098978569713 / 1000000000000000000)) (a := (93052156912801383 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy124_hz9 : B (356905639018024153 / 1000000000000000000) (178452819509012077 / 500000000000000000) (((597415800777 / 1000000000000) : ℝ)^2) := bsq (bpoint ((597415800777 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy124_hz10 : B (321547180490987923 / 500000000000000000) (643094360981975847 / 1000000000000000000) ((1 : ℝ) - (((597415800777 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy124_hz9 (by norm_num) (by norm_num)

theorem lowEnergy124_hz11 : B (50120727724024949 / 62500000000000000) (400965821792199593 / 500000000000000000) (√((1 : ℝ) - (((597415800777 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy124_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy124_hz12 : B (25526277019653029 / 100000000000000000) (63815692549132573 / 250000000000000000) ((√((1 : ℝ) - (((597415800777 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy124_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy124_hz13 : B (42046469678022143 / 100000000000000000) (420464696780221467 / 1000000000000000000) (((597415800777 / 1000000000000) : ℝ) * (kdot ((597415800777 / 1000000000000)))) := bmul (bpoint ((597415800777 / 1000000000000) : ℝ)) lowEnergy124_hz8 (by norm_num) (by norm_num)

theorem lowEnergy124_hz14 : B (16893186674418793 / 25000000000000000) (675727466976751759 / 1000000000000000000) (((√((1 : ℝ) - (((597415800777 / 1000000000000) : ℝ)^2))) / Real.pi) + (((597415800777 / 1000000000000) : ℝ) * (kdot ((597415800777 / 1000000000000))))) := badd lowEnergy124_hz12 lowEnergy124_hz13 (by norm_num) (by norm_num)

theorem lowEnergy124_hz15 : B (16893186674418793 / 25000000000000000) (675727466976751759 / 1000000000000000000) (kappa ((597415800777 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy124_hz14

theorem lowEnergy124 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (239 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (678522944871 / 1000000000000) := by
  have hk1 : kappa q ≤ (594419636627 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((239 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy124_hz7.2.trans (by norm_num))
  have hk2 : kappa ((597415800777 / 1000000000000) : ℝ) ≤ (675727466977 / 1000000000000) := lowEnergy124_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((771391364113 / 1000000000000) : ℝ)) (R := ((772257389517 / 1000000000000) : ℝ)) (Q2 := ((597415800777 / 1000000000000) : ℝ)) (T := ((411369167561 / 500000000000) : ℝ))
    (B := ((678522944871 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy125_hz0 : B (82307118038242399 / 125000000000000000) (164614236076541337 / 250000000000000000) (kdot ((191 / 400))) := by
    constructor
    · apply bkdot_lower (q := (37167163654838071 / 62500000000000000)) (a := (536494577326535517 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (118934923695481827 / 200000000000000000)) (a := (536494577326180273 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy125_hz1 : B (36481 / 160000) (36481 / 160000) (((191 / 400) : ℝ)^2) := bsq (bpoint ((191 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy125_hz2 : B (123519 / 160000) (123519 / 160000) ((1 : ℝ) - (((191 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy125_hz1 (by norm_num) (by norm_num)

theorem lowEnergy125_hz3 : B (439315874400185999 / 500000000000000000) (878631748800371999 / 1000000000000000000) (√((1 : ℝ) - (((191 / 400) : ℝ)^2))) := bsqrt lowEnergy125_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy125_hz4 : B (139838585979055683 / 500000000000000000) (279677171958111367 / 1000000000000000000) ((√((1 : ℝ) - (((191 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy125_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy125_hz5 : B (78603297726521491 / 250000000000000000) (157206595453096977 / 500000000000000000) (((191 / 400) : ℝ) * (kdot ((191 / 400)))) := bmul (bpoint ((191 / 400) : ℝ)) lowEnergy125_hz0 (by norm_num) (by norm_num)

theorem lowEnergy125_hz6 : B (59409036286419733 / 100000000000000000) (594090362864305321 / 1000000000000000000) (((√((1 : ℝ) - (((191 / 400) : ℝ)^2))) / Real.pi) + (((191 / 400) : ℝ) * (kdot ((191 / 400))))) := badd lowEnergy125_hz4 lowEnergy125_hz5 (by norm_num) (by norm_num)

theorem lowEnergy125_hz7 : B (59409036286419733 / 100000000000000000) (594090362864305321 / 1000000000000000000) (kappa ((191 / 400))) := by rw [kappa_eq]; exact lowEnergy125_hz6

theorem lowEnergy125_hz8 : B (17591868334066459 / 25000000000000000) (35183736668132921 / 50000000000000000) (kdot ((597085585583 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (502275861654112691 / 1000000000000000000)) (a := (232733320185227287 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (50227586165411269 / 100000000000000000)) (a := (232733320185227241 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy125_hz9 : B (356511196510994017 / 1000000000000000000) (178255598255497009 / 500000000000000000) (((597085585583 / 1000000000000) : ℝ)^2) := bsq (bpoint ((597085585583 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy125_hz10 : B (321744401744502991 / 500000000000000000) (643488803489005983 / 1000000000000000000) ((1 : ℝ) - (((597085585583 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy125_hz9 (by norm_num) (by norm_num)

theorem lowEnergy125_hz11 : B (802177538634064461 / 1000000000000000000) (802177538634064463 / 1000000000000000000) (√((1 : ℝ) - (((597085585583 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy125_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy125_hz12 : B (127670520510901201 / 500000000000000000) (63835260255450601 / 250000000000000000) ((√((1 : ℝ) - (((597085585583 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy125_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy125_hz13 : B (420154040229804253 / 1000000000000000000) (42015404022980429 / 100000000000000000) (((597085585583 / 1000000000000) : ℝ) * (kdot ((597085585583 / 1000000000000)))) := bmul (bpoint ((597085585583 / 1000000000000) : ℝ)) lowEnergy125_hz8 (by norm_num) (by norm_num)

theorem lowEnergy125_hz14 : B (135099016250321331 / 200000000000000000) (337747540625803347 / 500000000000000000) (((√((1 : ℝ) - (((597085585583 / 1000000000000) : ℝ)^2))) / Real.pi) + (((597085585583 / 1000000000000) : ℝ) * (kdot ((597085585583 / 1000000000000))))) := badd lowEnergy125_hz12 lowEnergy125_hz13 (by norm_num) (by norm_num)

theorem lowEnergy125_hz15 : B (135099016250321331 / 200000000000000000) (337747540625803347 / 500000000000000000) (kappa ((597085585583 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy125_hz14

theorem lowEnergy125 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (191 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (33914493863 / 50000000000) := by
  have hk1 : kappa q ≤ (118818072573 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((191 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy125_hz7.2.trans (by norm_num))
  have hk2 : kappa ((597085585583 / 1000000000000) : ℝ) ≤ (168873770313 / 250000000000) := lowEnergy125_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((385588953053 / 500000000000) : ℝ)) (R := ((77204393151 / 100000000000) : ℝ)) (Q2 := ((597085585583 / 1000000000000) : ℝ)) (T := ((822596851243 / 1000000000000) : ℝ))
    (B := ((33914493863 / 50000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy126_hz0 : B (658275832766272861 / 1000000000000000000) (164568958191626577 / 250000000000000000) (kdot ((477 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (59505977920373567 / 100000000000000000)) (a := (536779066667783557 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (595059779203735669 / 1000000000000000000)) (a := (268389533333708431 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy126_hz1 : B (227529 / 1000000) (227529 / 1000000) (((477 / 1000) : ℝ)^2) := bsq (bpoint ((477 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy126_hz2 : B (772471 / 1000000) (772471 / 1000000) ((1 : ℝ) - (((477 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy126_hz1 (by norm_num) (by norm_num)

theorem lowEnergy126_hz3 : B (878903293883917583 / 1000000000000000000) (54931455867744849 / 62500000000000000) (√((1 : ℝ) - (((477 / 1000) : ℝ)^2))) := bsqrt lowEnergy126_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy126_hz4 : B (279763607442748529 / 1000000000000000000) (27976360744274853 / 100000000000000000) ((√((1 : ℝ) - (((477 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy126_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy126_hz5 : B (156998786114756077 / 500000000000000000) (313997572229623509 / 1000000000000000000) (((477 / 1000) : ℝ) * (kdot ((477 / 1000)))) := bmul (bpoint ((477 / 1000) : ℝ)) lowEnergy126_hz0 (by norm_num) (by norm_num)

theorem lowEnergy126_hz6 : B (593761179672260683 / 1000000000000000000) (593761179672372039 / 1000000000000000000) (((√((1 : ℝ) - (((477 / 1000) : ℝ)^2))) / Real.pi) + (((477 / 1000) : ℝ) * (kdot ((477 / 1000))))) := badd lowEnergy126_hz4 lowEnergy126_hz5 (by norm_num) (by norm_num)

theorem lowEnergy126_hz7 : B (593761179672260683 / 1000000000000000000) (593761179672372039 / 1000000000000000000) (kappa ((477 / 1000))) := by rw [kappa_eq]; exact lowEnergy126_hz6

theorem lowEnergy126_hz8 : B (351771878812121649 / 500000000000000000) (703543757624243359 / 1000000000000000000) (kdot ((119351092223 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (100506705567559409 / 200000000000000000)) (a := (465672376579256203 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (125633381959449261 / 250000000000000000)) (a := (116418094144814027 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy126_hz9 : B (356117080370576277 / 1000000000000000000) (178058540185288139 / 500000000000000000) (((119351092223 / 200000000000) : ℝ)^2) := bsq (bpoint ((119351092223 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy126_hz10 : B (321941459814711861 / 500000000000000000) (643882919629423723 / 1000000000000000000) ((1 : ℝ) - (((119351092223 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy126_hz9 (by norm_num) (by norm_num)

theorem lowEnergy126_hz11 : B (802423154968389307 / 1000000000000000000) (802423154968389309 / 1000000000000000000) (√((1 : ℝ) - (((119351092223 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy126_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy126_hz12 : B (15963701445576639 / 62500000000000000) (127709611564613113 / 500000000000000000) ((√((1 : ℝ) - (((119351092223 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy126_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy126_hz13 : B (209921789747817553 / 500000000000000000) (419843579495635143 / 1000000000000000000) (((119351092223 / 200000000000) : ℝ) * (kdot ((119351092223 / 200000000000)))) := bmul (bpoint ((119351092223 / 200000000000) : ℝ)) lowEnergy126_hz8 (by norm_num) (by norm_num)

theorem lowEnergy126_hz14 : B (67526280262486133 / 100000000000000000) (675262802624861369 / 1000000000000000000) (((√((1 : ℝ) - (((119351092223 / 200000000000) : ℝ)^2))) / Real.pi) + (((119351092223 / 200000000000) : ℝ) * (kdot ((119351092223 / 200000000000))))) := badd lowEnergy126_hz12 lowEnergy126_hz13 (by norm_num) (by norm_num)

theorem lowEnergy126_hz15 : B (67526280262486133 / 100000000000000000) (675262802624861369 / 1000000000000000000) (kappa ((119351092223 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy126_hz14

theorem lowEnergy126 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (477 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (84757114627 / 125000000000) := by
  have hk1 : kappa q ≤ (593761179673 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((477 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy126_hz7.2.trans (by norm_num))
  have hk2 : kappa ((119351092223 / 200000000000) : ℝ) ≤ (5402102421 / 8000000000) := lowEnergy126_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((770964447737 / 1000000000000) : ℝ)) (R := ((771830473141 / 1000000000000) : ℝ)) (Q2 := ((119351092223 / 200000000000) : ℝ)) (T := ((102806926031 / 125000000000) : ℝ))
    (B := ((84757114627 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy127_hz0 : B (658094777136079149 / 1000000000000000000) (164523694284080029 / 250000000000000000) (kdot ((953 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (18607654731194009 / 31250000000000000)) (a := (8391616690416209 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (595444951398208287 / 1000000000000000000)) (a := (537063468186258867 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy127_hz1 : B (908209 / 4000000) (908209 / 4000000) (((953 / 2000) : ℝ)^2) := bsq (bpoint ((953 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy127_hz2 : B (3091791 / 4000000) (3091791 / 4000000) ((1 : ℝ) - (((953 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy127_hz1 (by norm_num) (by norm_num)

theorem lowEnergy127_hz3 : B (175834894147890907 / 200000000000000000) (109896808842431817 / 125000000000000000) (√((1 : ℝ) - (((953 / 2000) : ℝ)^2))) := bsqrt lowEnergy127_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy127_hz4 : B (11193997028670807 / 40000000000000000) (2186327544662267 / 7812500000000000) ((√((1 : ℝ) - (((953 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy127_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy127_hz5 : B (156791080652670857 / 500000000000000000) (39197770163182067 / 125000000000000000) (((953 / 2000) : ℝ) * (kdot ((953 / 2000)))) := bmul (bpoint ((953 / 2000) : ℝ)) lowEnergy127_hz0 (by norm_num) (by norm_num)

theorem lowEnergy127_hz6 : B (593432087022111889 / 1000000000000000000) (74179010877778339 / 125000000000000000) (((√((1 : ℝ) - (((953 / 2000) : ℝ)^2))) / Real.pi) + (((953 / 2000) : ℝ) * (kdot ((953 / 2000))))) := badd lowEnergy127_hz4 lowEnergy127_hz5 (by norm_num) (by norm_num)

theorem lowEnergy127_hz7 : B (593432087022111889 / 1000000000000000000) (74179010877778339 / 125000000000000000) (kappa ((953 / 2000))) := by rw [kappa_eq]; exact lowEnergy127_hz6

theorem lowEnergy127_hz8 : B (35170642896064351 / 50000000000000000) (703412857921287083 / 1000000000000000000) (kdot ((298212713673 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (502791097677294303 / 1000000000000000000)) (a := (465877993351838467 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (251395548838647151 / 500000000000000000)) (a := (46587799335183837 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy127_hz9 : B (88930822596214681 / 250000000000000000) (14228931615394349 / 40000000000000000) (((298212713673 / 500000000000) : ℝ)^2) := bsq (bpoint ((298212713673 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy127_hz10 : B (25771068384605651 / 40000000000000000) (161069177403785319 / 250000000000000000) ((1 : ℝ) - (((298212713673 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy127_hz9 (by norm_num) (by norm_num)

theorem lowEnergy127_hz11 : B (100333561621904873 / 125000000000000000) (401334246487619493 / 500000000000000000) (√((1 : ℝ) - (((298212713673 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy127_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy127_hz12 : B (255497316642263103 / 1000000000000000000) (3992145572535361 / 15625000000000000) ((√((1 : ℝ) - (((298212713673 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy127_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy127_hz13 : B (52441664298296849 / 125000000000000000) (41953331438637483 / 100000000000000000) (((298212713673 / 500000000000) : ℝ) * (kdot ((298212713673 / 500000000000)))) := bmul (bpoint ((298212713673 / 500000000000) : ℝ)) lowEnergy127_hz8 (by norm_num) (by norm_num)

theorem lowEnergy127_hz14 : B (135006126205727579 / 200000000000000000) (337515315514318967 / 500000000000000000) (((√((1 : ℝ) - (((298212713673 / 500000000000) : ℝ)^2))) / Real.pi) + (((298212713673 / 500000000000) : ℝ) * (kdot ((298212713673 / 500000000000))))) := badd lowEnergy127_hz12 lowEnergy127_hz13 (by norm_num) (by norm_num)

theorem lowEnergy127_hz15 : B (135006126205727579 / 200000000000000000) (337515315514318967 / 500000000000000000) (kappa ((298212713673 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy127_hz14

theorem lowEnergy127 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (953 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (169456016017 / 250000000000) := by
  have hk1 : kappa q ≤ (593432087023 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((953 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy127_hz7.2.trans (by norm_num))
  have hk2 : kappa ((298212713673 / 500000000000) : ℝ) ≤ (675030631029 / 1000000000000) := lowEnergy127_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((770750988987 / 1000000000000) : ℝ)) (R := ((771617014391 / 1000000000000) : ℝ)) (Q2 := ((298212713673 / 500000000000) : ℝ)) (T := ((164462801223 / 200000000000) : ℝ))
    (B := ((169456016017 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy128_hz0 : B (131582755461017581 / 200000000000000000) (657913777305336629 / 1000000000000000000) (kdot ((119 / 250))) := by
    constructor
    · apply bkdot_lower (q := (595830135303260199 / 1000000000000000000)) (a := (537347782056308919 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (297915067651630099 / 500000000000000000)) (a := (21493911282236729 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy128_hz1 : B (14161 / 62500) (14161 / 62500) (((119 / 250) : ℝ)^2) := bsq (bpoint ((119 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy128_hz2 : B (48339 / 62500) (48339 / 62500) ((1 : ℝ) - (((119 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy128_hz1 (by norm_num) (by norm_num)

theorem lowEnergy128_hz3 : B (219861319926903013 / 250000000000000000) (879445279707612053 / 1000000000000000000) (√((1 : ℝ) - (((119 / 250) : ℝ)^2))) := bsqrt lowEnergy128_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy128_hz4 : B (34992015861075243 / 125000000000000000) (55987225377720389 / 200000000000000000) ((√((1 : ℝ) - (((119 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy128_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy128_hz5 : B (156583478998610921 / 500000000000000000) (78291739499335059 / 250000000000000000) (((119 / 250) : ℝ) * (kdot ((119 / 250)))) := bmul (bpoint ((119 / 250) : ℝ)) lowEnergy128_hz0 (by norm_num) (by norm_num)

theorem lowEnergy128_hz6 : B (296551542442911893 / 500000000000000000) (593103084885942181 / 1000000000000000000) (((√((1 : ℝ) - (((119 / 250) : ℝ)^2))) / Real.pi) + (((119 / 250) : ℝ) * (kdot ((119 / 250))))) := badd lowEnergy128_hz4 lowEnergy128_hz5 (by norm_num) (by norm_num)

theorem lowEnergy128_hz7 : B (296551542442911893 / 500000000000000000) (593103084885942181 / 1000000000000000000) (kappa ((119 / 250))) := by rw [kappa_eq]; exact lowEnergy128_hz6

theorem lowEnergy128_hz8 : B (175820508537517349 / 250000000000000000) (35164101707503473 / 50000000000000000) (kdot ((298047742123 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (503048571322263787 / 1000000000000000000)) (a := (466083490851124567 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (251524285661131893 / 500000000000000000)) (a := (116520872712781117 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy128_hz9 : B (177664913169236617 / 500000000000000000) (71065965267694647 / 200000000000000000) (((298047742123 / 500000000000) : ℝ)^2) := bsq (bpoint ((298047742123 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy128_hz10 : B (128934034732305353 / 200000000000000000) (322335086830763383 / 500000000000000000) ((1 : ℝ) - (((298047742123 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy128_hz9 (by norm_num) (by norm_num)

theorem lowEnergy128_hz11 : B (401456776521933543 / 500000000000000000) (802913553043867087 / 1000000000000000000) (√((1 : ℝ) - (((298047742123 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy128_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy128_hz12 : B (127787660842408153 / 500000000000000000) (255575321684816307 / 1000000000000000000) ((√((1 : ℝ) - (((298047742123 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy128_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy128_hz13 : B (16768929788327901 / 40000000000000000) (104805811177049391 / 250000000000000000) (((298047742123 / 500000000000) : ℝ) * (kdot ((298047742123 / 500000000000)))) := bmul (bpoint ((298047742123 / 500000000000) : ℝ)) lowEnergy128_hz8 (by norm_num) (by norm_num)

theorem lowEnergy128_hz14 : B (674798566393013831 / 1000000000000000000) (674798566393013871 / 1000000000000000000) (((√((1 : ℝ) - (((298047742123 / 500000000000) : ℝ)^2))) / Real.pi) + (((298047742123 / 500000000000) : ℝ) * (kdot ((298047742123 / 500000000000))))) := badd lowEnergy128_hz12 lowEnergy128_hz13 (by norm_num) (by norm_num)

theorem lowEnergy128_hz15 : B (674798566393013831 / 1000000000000000000) (674798566393013871 / 1000000000000000000) (kappa ((298047742123 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy128_hz14

theorem lowEnergy128 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (119 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (338795659173 / 500000000000) := by
  have hk1 : kappa q ≤ (296551542443 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((119 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy128_hz7.2.trans (by norm_num))
  have hk2 : kappa ((298047742123 / 500000000000) : ℝ) ≤ (337399283197 / 500000000000) := lowEnergy128_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((770537529837 / 1000000000000) : ℝ)) (R := ((771403555241 / 1000000000000) : ℝ)) (Q2 := ((298047742123 / 500000000000) : ℝ)) (T := ((822172644823 / 1000000000000) : ℝ))
    (B := ((338795659173 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy129_hz0 : B (41108302072704433 / 62500000000000000) (131546566632705531 / 200000000000000000) (kdot ((951 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (119243066232211193 / 200000000000000000)) (a := (537632008449630081 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (149053832790263991 / 250000000000000000)) (a := (537632008449226817 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy129_hz1 : B (904401 / 4000000) (904401 / 4000000) (((951 / 2000) : ℝ)^2) := bsq (bpoint ((951 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy129_hz2 : B (3095599 / 4000000) (3095599 / 4000000) ((1 : ℝ) - (((951 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy129_hz1 (by norm_num) (by norm_num)

theorem lowEnergy129_hz3 : B (35188628845125523 / 40000000000000000) (219928930282034519 / 250000000000000000) (√((1 : ℝ) - (((951 / 2000) : ℝ)^2))) := bsqrt lowEnergy129_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy129_hz4 : B (56004442213277793 / 200000000000000000) (140011105533194483 / 500000000000000000) ((√((1 : ℝ) - (((951 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy129_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy129_hz5 : B (156375981084567663 / 500000000000000000) (1563759810846287 / 5000000000000000) (((951 / 2000) : ℝ) * (kdot ((951 / 2000)))) := bmul (bpoint ((951 / 2000) : ℝ)) lowEnergy129_hz0 (by norm_num) (by norm_num)

theorem lowEnergy129_hz6 : B (592774173235524291 / 1000000000000000000) (296387086617823183 / 500000000000000000) (((√((1 : ℝ) - (((951 / 2000) : ℝ)^2))) / Real.pi) + (((951 / 2000) : ℝ) * (kdot ((951 / 2000))))) := badd lowEnergy129_hz4 lowEnergy129_hz5 (by norm_num) (by norm_num)

theorem lowEnergy129_hz7 : B (592774173235524291 / 1000000000000000000) (296387086617823183 / 500000000000000000) (kappa ((951 / 2000))) := by rw [kappa_eq]; exact lowEnergy129_hz6

theorem lowEnergy129_hz8 : B (439469553880433 / 625000000000000) (351575643104346433 / 500000000000000000) (kdot ((595765631789 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (251652974459445479 / 500000000000000000)) (a := (233144434618587459 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (503305948918890957 / 1000000000000000000)) (a := (14571527163661713 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy129_hz9 : B (354936688020946327 / 1000000000000000000) (44367086002618291 / 125000000000000000) (((595765631789 / 1000000000000) : ℝ)^2) := bsq (bpoint ((595765631789 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy129_hz10 : B (80632913997381709 / 125000000000000000) (645063311979053673 / 1000000000000000000) ((1 : ℝ) - (((595765631789 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy129_hz9 (by norm_num) (by norm_num)

theorem lowEnergy129_hz11 : B (80315833555971619 / 100000000000000000) (803158335559716191 / 1000000000000000000) (√((1 : ℝ) - (((595765631789 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy129_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy129_hz12 : B (15978327398723501 / 62500000000000000) (255653238379576017 / 1000000000000000000) ((√((1 : ℝ) - (((595765631789 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy129_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy129_hz13 : B (104728342567842457 / 250000000000000000) (104728342567842467 / 250000000000000000) (((595765631789 / 1000000000000) : ℝ) * (kdot ((595765631789 / 1000000000000)))) := bmul (bpoint ((595765631789 / 1000000000000) : ℝ)) lowEnergy129_hz8 (by norm_num) (by norm_num)

theorem lowEnergy129_hz14 : B (168641652162736461 / 250000000000000000) (134913321730189177 / 200000000000000000) (((√((1 : ℝ) - (((595765631789 / 1000000000000) : ℝ)^2))) / Real.pi) + (((595765631789 / 1000000000000) : ℝ) * (kdot ((595765631789 / 1000000000000))))) := badd lowEnergy129_hz12 lowEnergy129_hz13 (by norm_num) (by norm_num)

theorem lowEnergy129_hz15 : B (168641652162736461 / 250000000000000000) (134913321730189177 / 200000000000000000) (kappa ((595765631789 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy129_hz14

theorem lowEnergy129 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (951 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (338679339891 / 500000000000) := by
  have hk1 : kappa q ≤ (148193543309 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((951 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy129_hz7.2.trans (by norm_num))
  have hk2 : kappa ((595765631789 / 1000000000000) : ℝ) ≤ (674566608651 / 1000000000000) := lowEnergy129_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((77032407027 / 100000000000) : ℝ)) (R := ((385595047837 / 500000000000) : ℝ)) (Q2 := ((595765631789 / 1000000000000) : ℝ)) (T := ((12844239443 / 15625000000) : ℝ))
    (B := ((338679339891 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy130_hz0 : B (657551944600841127 / 1000000000000000000) (657551944601106109 / 1000000000000000000) (kdot ((19 / 40))) := by
    constructor
    · apply bkdot_lower (q := (23864021568539717 / 40000000000000000)) (a := (268958073769527011 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (149150134803373231 / 250000000000000000)) (a := (537916147538637791 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy130_hz1 : B (361 / 1600) (361 / 1600) (((19 / 40) : ℝ)^2) := bsq (bpoint ((19 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy130_hz2 : B (1239 / 1600) (1239 / 1600) ((1 : ℝ) - (((19 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy130_hz1 (by norm_num) (by norm_num)

theorem lowEnergy130_hz3 : B (879985795339902063 / 1000000000000000000) (54999112208743879 / 62500000000000000) (√((1 : ℝ) - (((19 / 40) : ℝ)^2))) := bsqrt lowEnergy130_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy130_hz4 : B (280108178357996737 / 1000000000000000000) (140054089178998369 / 500000000000000000) ((√((1 : ℝ) - (((19 / 40) : ℝ)^2))) / Real.pi) := bdiv lowEnergy130_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy130_hz5 : B (62467434737079907 / 200000000000000000) (156168586842762701 / 500000000000000000) (((19 / 40) : ℝ) * (kdot ((19 / 40)))) := bmul (bpoint ((19 / 40) : ℝ)) lowEnergy130_hz0 (by norm_num) (by norm_num)

theorem lowEnergy130_hz6 : B (37027834502712267 / 62500000000000000) (29622267602176107 / 50000000000000000) (((√((1 : ℝ) - (((19 / 40) : ℝ)^2))) / Real.pi) + (((19 / 40) : ℝ) * (kdot ((19 / 40))))) := badd lowEnergy130_hz4 lowEnergy130_hz5 (by norm_num) (by norm_num)

theorem lowEnergy130_hz7 : B (37027834502712267 / 62500000000000000) (29622267602176107 / 50000000000000000) (kappa ((19 / 40))) := by rw [kappa_eq]; exact lowEnergy130_hz6

theorem lowEnergy130_hz8 : B (703020613993909297 / 1000000000000000000) (175755153498477341 / 250000000000000000) (kdot ((119087173989 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (503563230616131477 / 1000000000000000000)) (a := (466494128672170999 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (125890807654032869 / 250000000000000000)) (a := (93298825734434179 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy130_hz9 : B (177271937608579477 / 500000000000000000) (70908775043431791 / 200000000000000000) (((119087173989 / 200000000000) : ℝ)^2) := bsq (bpoint ((119087173989 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy130_hz10 : B (129091224956568209 / 200000000000000000) (322728062391420523 / 500000000000000000) ((1 : ℝ) - (((119087173989 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy130_hz9 (by norm_num) (by norm_num)

theorem lowEnergy130_hz11 : B (40170142045518119 / 50000000000000000) (401701420455181191 / 500000000000000000) (√((1 : ℝ) - (((119087173989 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy130_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy130_hz12 : B (255731066849911533 / 1000000000000000000) (127865533424955767 / 500000000000000000) ((√((1 : ℝ) - (((119087173989 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy130_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy130_hz13 : B (418603690882731423 / 1000000000000000000) (52325461360341433 / 125000000000000000) (((119087173989 / 200000000000) : ℝ) * (kdot ((119087173989 / 200000000000)))) := bmul (bpoint ((119087173989 / 200000000000) : ℝ)) lowEnergy130_hz8 (by norm_num) (by norm_num)

theorem lowEnergy130_hz14 : B (168583689433160739 / 250000000000000000) (337167378866321499 / 500000000000000000) (((√((1 : ℝ) - (((119087173989 / 200000000000) : ℝ)^2))) / Real.pi) + (((119087173989 / 200000000000) : ℝ) * (kdot ((119087173989 / 200000000000))))) := badd lowEnergy130_hz12 lowEnergy130_hz13 (by norm_num) (by norm_num)

theorem lowEnergy130_hz15 : B (168583689433160739 / 250000000000000000) (337167378866321499 / 500000000000000000) (kappa ((119087173989 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy130_hz14

theorem lowEnergy130 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (19 / 40)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (677126148311 / 1000000000000) := by
  have hk1 : kappa q ≤ (148111338011 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((19 / 40) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy130_hz7.2.trans (by norm_num))
  have hk2 : kappa ((119087173989 / 200000000000) : ℝ) ≤ (674334757733 / 1000000000000) := lowEnergy130_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((385055305133 / 500000000000) : ℝ)) (R := ((77097663567 / 100000000000) : ℝ)) (Q2 := ((119087173989 / 200000000000) : ℝ)) (T := ((410945022341 / 500000000000) : ℝ))
    (B := ((677126148311 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy131_hz0 : B (328685555754125841 / 500000000000000000) (657371111508525179 / 1000000000000000000) (kdot ((949 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (596985759702202617 / 1000000000000000000)) (a := (538200199496656483 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (74623219962775327 / 125000000000000000)) (a := (538200199496226877 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy131_hz1 : B (900601 / 4000000) (900601 / 4000000) (((949 / 2000) : ℝ)^2) := bsq (bpoint ((949 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy131_hz2 : B (3099399 / 4000000) (3099399 / 4000000) ((1 : ℝ) - (((949 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy131_hz1 (by norm_num) (by norm_num)

theorem lowEnergy131_hz3 : B (880255502680897757 / 1000000000000000000) (440127751340448879 / 500000000000000000) (√((1 : ℝ) - (((949 / 2000) : ℝ)^2))) := bsqrt lowEnergy131_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy131_hz4 : B (280194028871012009 / 1000000000000000000) (28019402887101201 / 100000000000000000) ((√((1 : ℝ) - (((949 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy131_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy131_hz5 : B (311922592410665423 / 1000000000000000000) (155961296205397599 / 500000000000000000) (((949 / 2000) : ℝ) * (kdot ((949 / 2000)))) := bmul (bpoint ((949 / 2000) : ℝ)) lowEnergy131_hz0 (by norm_num) (by norm_num)

theorem lowEnergy131_hz6 : B (74014577660209679 / 125000000000000000) (74014577660225901 / 125000000000000000) (((√((1 : ℝ) - (((949 / 2000) : ℝ)^2))) / Real.pi) + (((949 / 2000) : ℝ) * (kdot ((949 / 2000))))) := badd lowEnergy131_hz4 lowEnergy131_hz5 (by norm_num) (by norm_num)

theorem lowEnergy131_hz7 : B (74014577660209679 / 125000000000000000) (74014577660225901 / 125000000000000000) (kappa ((949 / 2000))) := by rw [kappa_eq]; exact lowEnergy131_hz6

theorem lowEnergy131_hz8 : B (28115600696171637 / 40000000000000000) (351445008702145497 / 500000000000000000) (kdot ((18597068709 / 31250000000))) := by
    constructor
    · apply bkdot_lower (q := (100764083311894029 / 200000000000000000)) (a := (466699269315435479 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (7872194008741721 / 15625000000000000)) (a := (116674817328858843 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy131_hz9 : B (88537846929220333 / 250000000000000000) (354151387716881333 / 1000000000000000000) (((18597068709 / 31250000000) : ℝ)^2) := bsq (bpoint ((18597068709 / 31250000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy131_hz10 : B (645848612283118667 / 1000000000000000000) (161462153070779667 / 250000000000000000) ((1 : ℝ) - (((18597068709 / 31250000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy131_hz9 (by norm_num) (by norm_num)

theorem lowEnergy131_hz11 : B (803647069479581109 / 1000000000000000000) (80364706947958111 / 100000000000000000) (√((1 : ℝ) - (((18597068709 / 31250000000) : ℝ)^2))) := bsqrt lowEnergy131_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy131_hz12 : B (31976100902247797 / 125000000000000000) (127904403608991189 / 500000000000000000) ((√((1 : ℝ) - (((18597068709 / 31250000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy131_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy131_hz13 : B (418294206353209733 / 1000000000000000000) (16731768254128391 / 40000000000000000) (((18597068709 / 31250000000) : ℝ) * (kdot ((18597068709 / 31250000000)))) := bmul (bpoint ((18597068709 / 31250000000) : ℝ)) lowEnergy131_hz8 (by norm_num) (by norm_num)

theorem lowEnergy131_hz14 : B (674103013571192109 / 1000000000000000000) (674103013571192153 / 1000000000000000000) (((√((1 : ℝ) - (((18597068709 / 31250000000) : ℝ)^2))) / Real.pi) + (((18597068709 / 31250000000) : ℝ) * (kdot ((18597068709 / 31250000000))))) := badd lowEnergy131_hz12 lowEnergy131_hz13 (by norm_num) (by norm_num)

theorem lowEnergy131_hz15 : B (674103013571192109 / 1000000000000000000) (674103013571192153 / 1000000000000000000) (kappa ((18597068709 / 31250000000))) := by rw [kappa_eq]; exact lowEnergy131_hz14

theorem lowEnergy131 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (949 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (676893723859 / 1000000000000) := by
  have hk1 : kappa q ≤ (296058310641 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((949 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy131_hz7.2.trans (by norm_num))
  have hk2 : kappa ((18597068709 / 31250000000) : ℝ) ≤ (168525753393 / 250000000000) := lowEnergy131_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((48118571863 / 62500000000) : ℝ)) (R := ((192690793803 / 250000000000) : ℝ)) (Q2 := ((18597068709 / 31250000000) : ℝ)) (T := ((821748805791 / 1000000000000) : ℝ))
    (B := ((676893723859 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy132_hz0 : B (164297583444048803 / 250000000000000000) (657190333776477491 / 1000000000000000000) (kdot ((237 / 500))) := by
    constructor
    · apply bkdot_lower (q := (119474198573710439 / 200000000000000000)) (a := (538484164494137099 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (298685496434276097 / 500000000000000000)) (a := (538484164493693697 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy132_hz1 : B (56169 / 250000) (56169 / 250000) (((237 / 500) : ℝ)^2) := bsq (bpoint ((237 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy132_hz2 : B (193831 / 250000) (193831 / 250000) ((1 : ℝ) - (((237 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy132_hz1 (by norm_num) (by norm_num)

theorem lowEnergy132_hz3 : B (176104968697649187 / 200000000000000000) (55032802718015371 / 62500000000000000) (√((1 : ℝ) - (((237 / 500) : ℝ)^2))) := bsqrt lowEnergy132_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy132_hz4 : B (140139881356371829 / 500000000000000000) (280279762712743659 / 1000000000000000000) ((√((1 : ℝ) - (((237 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy132_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy132_hz5 : B (31150821820991653 / 100000000000000000) (311508218210050331 / 1000000000000000000) (((237 / 500) : ℝ) * (kdot ((237 / 500)))) := bmul (bpoint ((237 / 500) : ℝ)) lowEnergy132_hz0 (by norm_num) (by norm_num)

theorem lowEnergy132_hz6 : B (147946995230665047 / 250000000000000000) (59178798092279399 / 100000000000000000) (((√((1 : ℝ) - (((237 / 500) : ℝ)^2))) / Real.pi) + (((237 / 500) : ℝ) * (kdot ((237 / 500))))) := badd lowEnergy132_hz4 lowEnergy132_hz5 (by norm_num) (by norm_num)

theorem lowEnergy132_hz7 : B (147946995230665047 / 250000000000000000) (59178798092279399 / 100000000000000000) (kappa ((237 / 500))) := by rw [kappa_eq]; exact lowEnergy132_hz6

theorem lowEnergy132_hz8 : B (702759496337850743 / 1000000000000000000) (351379748168925407 / 500000000000000000) (kdot ((59477661799 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (504077506895603693 / 1000000000000000000)) (a := (466904291327169069 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (126019376723900923 / 250000000000000000)) (a := (466904291327168959 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy132_hz9 : B (353759225307622391 / 1000000000000000000) (44219903163452799 / 125000000000000000) (((59477661799 / 100000000000) : ℝ)^2) := bsq (bpoint ((59477661799 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy132_hz10 : B (80780096836547201 / 125000000000000000) (646240774692377609 / 1000000000000000000) ((1 : ℝ) - (((59477661799 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy132_hz9 (by norm_num) (by norm_num)

theorem lowEnergy132_hz11 : B (803891021651801761 / 1000000000000000000) (401945510825900881 / 500000000000000000) (√((1 : ℝ) - (((59477661799 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy132_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy132_hz12 : B (12794322980307811 / 50000000000000000) (127943229803078111 / 500000000000000000) ((√((1 : ℝ) - (((59477661799 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy132_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy132_hz13 : B (83596983298436531 / 200000000000000000) (208992458246091349 / 500000000000000000) (((59477661799 / 100000000000) : ℝ) * (kdot ((59477661799 / 100000000000)))) := bmul (bpoint ((59477661799 / 100000000000) : ℝ)) lowEnergy132_hz8 (by norm_num) (by norm_num)

theorem lowEnergy132_hz14 : B (5390971008786711 / 8000000000000000) (16846784402458473 / 25000000000000000) (((√((1 : ℝ) - (((59477661799 / 100000000000) : ℝ)^2))) / Real.pi) + (((59477661799 / 100000000000) : ℝ) * (kdot ((59477661799 / 100000000000))))) := badd lowEnergy132_hz12 lowEnergy132_hz13 (by norm_num) (by norm_num)

theorem lowEnergy132_hz15 : B (5390971008786711 / 8000000000000000) (16846784402458473 / 25000000000000000) (kappa ((59477661799 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy132_hz14

theorem lowEnergy132 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (237 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (676661406363 / 1000000000000) := by
  have hk1 : kappa q ≤ (591787980923 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((237 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy132_hz7.2.trans (by norm_num))
  have hk2 : kappa ((59477661799 / 100000000000) : ℝ) ≤ (673871376099 / 1000000000000) := lowEnergy132_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((769683688877 / 1000000000000) : ℝ)) (R := ((770549714281 / 1000000000000) : ℝ)) (Q2 := ((59477661799 / 100000000000) : ℝ)) (T := ((41080380383 / 50000000000) : ℝ))
    (B := ((676661406363 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy133_hz0 : B (32850480564780147 / 50000000000000000) (16425240282397357 / 25000000000000000) (kdot ((947 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (7471952986920573 / 12500000000000000)) (a := (538768042702820701 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (597756238953645839 / 1000000000000000000)) (a := (134692010675590767 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy133_hz1 : B (896809 / 4000000) (896809 / 4000000) (((947 / 2000) : ℝ)^2) := bsq (bpoint ((947 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy133_hz2 : B (3103191 / 4000000) (3103191 / 4000000) ((1 : ℝ) - (((947 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy133_hz1 (by norm_num) (by norm_num)

theorem lowEnergy133_hz3 : B (110099227262274643 / 125000000000000000) (176158763619639429 / 200000000000000000) (√((1 : ℝ) - (((947 / 2000) : ℝ)^2))) := bsqrt lowEnergy133_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy133_hz4 : B (280365379990223557 / 1000000000000000000) (140182689995111779 / 500000000000000000) ((√((1 : ℝ) - (((947 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy133_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy133_hz5 : B (38886756368558499 / 125000000000000000) (155547025474302971 / 500000000000000000) (((947 / 2000) : ℝ) * (kdot ((947 / 2000)))) := bmul (bpoint ((947 / 2000) : ℝ)) lowEnergy133_hz0 (by norm_num) (by norm_num)

theorem lowEnergy133_hz6 : B (591459430938691549 / 1000000000000000000) (1182918861877659 / 2000000000000000) (((√((1 : ℝ) - (((947 / 2000) : ℝ)^2))) / Real.pi) + (((947 / 2000) : ℝ) * (kdot ((947 / 2000))))) := badd lowEnergy133_hz4 lowEnergy133_hz5 (by norm_num) (by norm_num)

theorem lowEnergy133_hz7 : B (591459430938691549 / 1000000000000000000) (1182918861877659 / 2000000000000000) (kappa ((947 / 2000))) := by rw [kappa_eq]; exact lowEnergy133_hz6

theorem lowEnergy133_hz8 : B (702629050693230783 / 1000000000000000000) (87828631336653857 / 125000000000000000) (kdot ((37152945489 / 62500000000))) := by
    constructor
    · apply bkdot_lower (q := (50433450177010139 / 100000000000000000)) (a := (233554597433292247 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (504334501770101389 / 1000000000000000000)) (a := (233554597433292191 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy133_hz9 : B (176683693889101497 / 500000000000000000) (70673477555640599 / 200000000000000000) (((37152945489 / 62500000000) : ℝ)^2) := bsq (bpoint ((37152945489 / 62500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy133_hz10 : B (129326522444359401 / 200000000000000000) (323316306110898503 / 500000000000000000) ((1 : ℝ) - (((37152945489 / 62500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy133_hz9 (by norm_num) (by norm_num)

theorem lowEnergy133_hz11 : B (201033674452471551 / 250000000000000000) (402067348904943103 / 500000000000000000) (√((1 : ℝ) - (((37152945489 / 62500000000) : ℝ)^2))) := bsqrt lowEnergy133_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy133_hz12 : B (255964024136301783 / 1000000000000000000) (51192804827260357 / 200000000000000000) ((√((1 : ℝ) - (((37152945489 / 62500000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy133_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy133_hz13 : B (83535164222058947 / 200000000000000000) (417675821110294779 / 1000000000000000000) (((37152945489 / 62500000000) : ℝ) * (kdot ((37152945489 / 62500000000)))) := bmul (bpoint ((37152945489 / 62500000000) : ℝ)) lowEnergy133_hz8 (by norm_num) (by norm_num)

theorem lowEnergy133_hz14 : B (336819922623298259 / 500000000000000000) (168409961311649141 / 250000000000000000) (((√((1 : ℝ) - (((37152945489 / 62500000000) : ℝ)^2))) / Real.pi) + (((37152945489 / 62500000000) : ℝ) * (kdot ((37152945489 / 62500000000))))) := badd lowEnergy133_hz12 lowEnergy133_hz13 (by norm_num) (by norm_num)

theorem lowEnergy133_hz15 : B (336819922623298259 / 500000000000000000) (168409961311649141 / 250000000000000000) (kappa ((37152945489 / 62500000000))) := by rw [kappa_eq]; exact lowEnergy133_hz14

theorem lowEnergy133 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (947 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (84553649469 / 125000000000) := by
  have hk1 : kappa q ≤ (591459430939 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((947 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy133_hz7.2.trans (by norm_num))
  have hk2 : kappa ((37152945489 / 62500000000) : ℝ) ≤ (673639845247 / 1000000000000) := lowEnergy133_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((153894045491 / 200000000000) : ℝ)) (R := ((770336252859 / 1000000000000) : ℝ)) (Q2 := ((37152945489 / 62500000000) : ℝ)) (T := ((205366612567 / 250000000000) : ℝ))
    (B := ((84553649469 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy134_hz0 : B (164207235989410969 / 250000000000000000) (656828943957944559 / 1000000000000000000) (kdot ((473 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (149535374549581541 / 250000000000000000)) (a := (134762958573414653 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (598141498198326163 / 1000000000000000000)) (a := (539051834293186301 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy134_hz1 : B (223729 / 1000000) (223729 / 1000000) (((473 / 1000) : ℝ)^2) := bsq (bpoint ((473 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy134_hz2 : B (776271 / 1000000) (776271 / 1000000) ((1 : ℝ) - (((473 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy134_hz1 (by norm_num) (by norm_num)

theorem lowEnergy134_hz3 : B (881062426846134439 / 1000000000000000000) (22026560671153361 / 25000000000000000) (√((1 : ℝ) - (((473 / 1000) : ℝ)^2))) := bsqrt lowEnergy134_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy134_hz4 : B (280450880810207447 / 1000000000000000000) (280450880810207449 / 1000000000000000000) ((√((1 : ℝ) - (((473 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy134_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy134_hz5 : B (310680090491965553 / 1000000000000000000) (310680090492107777 / 1000000000000000000) (((473 / 1000) : ℝ) * (kdot ((473 / 1000)))) := bmul (bpoint ((473 / 1000) : ℝ)) lowEnergy134_hz0 (by norm_num) (by norm_num)

theorem lowEnergy134_hz6 : B (591130971302173 / 1000000000000000) (295565485651157613 / 500000000000000000) (((√((1 : ℝ) - (((473 / 1000) : ℝ)^2))) / Real.pi) + (((473 / 1000) : ℝ) * (kdot ((473 / 1000))))) := badd lowEnergy134_hz4 lowEnergy134_hz5 (by norm_num) (by norm_num)

theorem lowEnergy134_hz7 : B (591130971302173 / 1000000000000000) (295565485651157613 / 500000000000000000) (kappa ((473 / 1000))) := by rw [kappa_eq]; exact lowEnergy134_hz6

theorem lowEnergy134_hz8 : B (702498680368513519 / 1000000000000000000) (702498680368513593 / 1000000000000000000) (kdot ((594117728161 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (25229570066487309 / 50000000000000000)) (a := (467313980093773431 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (504591401329746179 / 1000000000000000000)) (a := (116828495023443329 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy134_hz9 : B (88243968728796973 / 250000000000000000) (352975874915187893 / 1000000000000000000) (((594117728161 / 1000000000000) : ℝ)^2) := bsq (bpoint ((594117728161 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy134_hz10 : B (647024125084812107 / 1000000000000000000) (161756031271203027 / 250000000000000000) ((1 : ℝ) - (((594117728161 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy134_hz9 (by norm_num) (by norm_num)

theorem lowEnergy134_hz11 : B (804378098337350373 / 1000000000000000000) (402189049168675187 / 500000000000000000) (√((1 : ℝ) - (((594117728161 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy134_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy134_hz12 : B (256041500930495977 / 1000000000000000000) (128020750465247989 / 500000000000000000) ((√((1 : ℝ) - (((594117728161 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy134_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy134_hz13 : B (208683460008320871 / 500000000000000000) (417366920016641787 / 1000000000000000000) (((594117728161 / 1000000000000) : ℝ) * (kdot ((594117728161 / 1000000000000)))) := bmul (bpoint ((594117728161 / 1000000000000) : ℝ)) lowEnergy134_hz8 (by norm_num) (by norm_num)

theorem lowEnergy134_hz14 : B (673408420947137719 / 1000000000000000000) (134681684189427553 / 200000000000000000) (((√((1 : ℝ) - (((594117728161 / 1000000000000) : ℝ)^2))) / Real.pi) + (((594117728161 / 1000000000000) : ℝ) * (kdot ((594117728161 / 1000000000000))))) := badd lowEnergy134_hz12 lowEnergy134_hz13 (by norm_num) (by norm_num)

theorem lowEnergy134_hz15 : B (673408420947137719 / 1000000000000000000) (134681684189427553 / 200000000000000000) (kappa ((594117728161 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy134_hz14

theorem lowEnergy134 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (473 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (16904927299 / 25000000000) := by
  have hk1 : kappa q ≤ (591130971303 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((473 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy134_hz7.2.trans (by norm_num))
  have hk2 : kappa ((594117728161 / 1000000000000) : ℝ) ≤ (168352105237 / 250000000000) := lowEnergy134_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((192314191381 / 250000000000) : ℝ)) (R := ((48132674433 / 62500000000) : ℝ)) (Q2 := ((594117728161 / 1000000000000) : ℝ)) (T := ((164265066719 / 200000000000) : ℝ))
    (B := ((16904927299 / 25000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy135_hz0 : B (656648331653723981 / 1000000000000000000) (656648331654034303 / 1000000000000000000) (kdot ((189 / 400))) := by
    constructor
    · apply bkdot_lower (q := (598526770843175613 / 1000000000000000000)) (a := (269667769718614973 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (149631692710793903 / 250000000000000000)) (a := (107867107887348499 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy135_hz1 : B (35721 / 160000) (35721 / 160000) (((189 / 400) : ℝ)^2) := bsq (bpoint ((189 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy135_hz2 : B (124279 / 160000) (124279 / 160000) ((1 : ℝ) - (((189 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy135_hz1 (by norm_num) (by norm_num)

theorem lowEnergy135_hz3 : B (881330670066576089 / 1000000000000000000) (88133067006657609 / 100000000000000000) (√((1 : ℝ) - (((189 / 400) : ℝ)^2))) := bsqrt lowEnergy135_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy135_hz4 : B (140268132639587901 / 500000000000000000) (70134066319793951 / 250000000000000000) ((√((1 : ℝ) - (((189 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy135_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy135_hz5 : B (310266336706384581 / 1000000000000000000) (310266336706531209 / 1000000000000000000) (((189 / 400) : ℝ) * (kdot ((189 / 400)))) := bmul (bpoint ((189 / 400) : ℝ)) lowEnergy135_hz0 (by norm_num) (by norm_num)

theorem lowEnergy135_hz6 : B (590802601985560383 / 1000000000000000000) (590802601985707013 / 1000000000000000000) (((√((1 : ℝ) - (((189 / 400) : ℝ)^2))) / Real.pi) + (((189 / 400) : ℝ) * (kdot ((189 / 400))))) := badd lowEnergy135_hz4 lowEnergy135_hz5 (by norm_num) (by norm_num)

theorem lowEnergy135_hz7 : B (590802601985560383 / 1000000000000000000) (590802601985707013 / 1000000000000000000) (kappa ((189 / 400))) := by rw [kappa_eq]; exact lowEnergy135_hz6

theorem lowEnergy135_hz8 : B (87796048157751687 / 125000000000000000) (702368385262013573 / 1000000000000000000) (kdot ((148447104743 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (20193928228839021 / 40000000000000000)) (a := (58439830896057877 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (126212051430243881 / 250000000000000000)) (a := (233759323584231449 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy135_hz9 : B (352584686505267409 / 1000000000000000000) (35258468650526741 / 100000000000000000) (((148447104743 / 250000000000) : ℝ)^2) := bsq (bpoint ((148447104743 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy135_hz10 : B (64741531349473259 / 100000000000000000) (647415313494732591 / 1000000000000000000) ((1 : ℝ) - (((148447104743 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy135_hz9 (by norm_num) (by norm_num)

theorem lowEnergy135_hz11 : B (402310611808442293 / 500000000000000000) (804621223616884587 / 1000000000000000000) (√((1 : ℝ) - (((148447104743 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy135_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy135_hz12 : B (51223778022110583 / 200000000000000000) (64029722527638229 / 250000000000000000) ((√((1 : ℝ) - (((148447104743 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy135_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy135_hz13 : B (417058213020647579 / 1000000000000000000) (208529106510323813 / 500000000000000000) (((148447104743 / 250000000000) : ℝ) * (kdot ((148447104743 / 250000000000)))) := bmul (bpoint ((148447104743 / 250000000000) : ℝ)) lowEnergy135_hz8 (by norm_num) (by norm_num)

theorem lowEnergy135_hz14 : B (336588551565600247 / 500000000000000000) (336588551565600271 / 500000000000000000) (((√((1 : ℝ) - (((148447104743 / 250000000000) : ℝ)^2))) / Real.pi) + (((148447104743 / 250000000000) : ℝ) * (kdot ((148447104743 / 250000000000))))) := badd lowEnergy135_hz12 lowEnergy135_hz13 (by norm_num) (by norm_num)

theorem lowEnergy135_hz15 : B (336588551565600247 / 500000000000000000) (336588551565600271 / 500000000000000000) (kappa ((148447104743 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy135_hz14

theorem lowEnergy135 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (189 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (135193018983 / 200000000000) := by
  have hk1 : kappa q ≤ (295401300993 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((189 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy135_hz7.2.trans (by norm_num))
  have hk2 : kappa ((148447104743 / 250000000000) : ℝ) ≤ (168294275783 / 250000000000) := lowEnergy135_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((769043303063 / 1000000000000) : ℝ)) (R := ((769909328467 / 1000000000000) : ℝ)) (Q2 := ((148447104743 / 250000000000) : ℝ)) (T := ((821184257619 / 1000000000000) : ℝ))
    (B := ((135193018983 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy136_hz0 : B (328233887137742679 / 500000000000000000) (656467774275805621 / 1000000000000000000) (kdot ((59 / 125))) := by
    constructor
    · apply bkdot_lower (q := (598912057128517863 / 1000000000000000000)) (a := (134904789575935723 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (299456028564258931 / 500000000000000000)) (a := (21584766332129593 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy136_hz1 : B (3481 / 15625) (3481 / 15625) (((59 / 125) : ℝ)^2) := bsq (bpoint ((59 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy136_hz2 : B (12144 / 15625) (12144 / 15625) ((1 : ℝ) - (((59 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy136_hz1 (by norm_num) (by norm_num)

theorem lowEnergy136_hz3 : B (881598548093178293 / 1000000000000000000) (440799274046589147 / 500000000000000000) (√((1 : ℝ) - (((59 / 125) : ℝ)^2))) := bsqrt lowEnergy136_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy136_hz4 : B (280621533503334689 / 1000000000000000000) (28062153350333469 / 100000000000000000) ((√((1 : ℝ) - (((59 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy136_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy136_hz5 : B (9682899670563409 / 31250000000000000) (154926394729090127 / 500000000000000000) (((59 / 125) : ℝ) * (kdot ((59 / 125)))) := bmul (bpoint ((59 / 125) : ℝ)) lowEnergy136_hz0 (by norm_num) (by norm_num)

theorem lowEnergy136_hz6 : B (590474322961363777 / 1000000000000000000) (9226161296273671 / 15625000000000000) (((√((1 : ℝ) - (((59 / 125) : ℝ)^2))) / Real.pi) + (((59 / 125) : ℝ) * (kdot ((59 / 125))))) := badd lowEnergy136_hz4 lowEnergy136_hz5 (by norm_num) (by norm_num)

theorem lowEnergy136_hz7 : B (590474322961363777 / 1000000000000000000) (9226161296273671 / 15625000000000000) (kappa ((59 / 125))) := by rw [kappa_eq]; exact lowEnergy136_hz6

theorem lowEnergy136_hz8 : B (351119082636929251 / 500000000000000000) (35111908263692929 / 50000000000000000) (kdot ((74182400029 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (505104915086763711 / 1000000000000000000)) (a := (116930799061883039 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (50510491508676371 / 100000000000000000)) (a := (93544639249506407 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy136_hz9 : B (88048455585001267 / 250000000000000000) (352193822340005069 / 1000000000000000000) (((74182400029 / 125000000000) : ℝ)^2) := bsq (bpoint ((74182400029 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy136_hz10 : B (647806177659994931 / 1000000000000000000) (161951544414998733 / 250000000000000000) ((1 : ℝ) - (((74182400029 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy136_hz9 (by norm_num) (by norm_num)

theorem lowEnergy136_hz11 : B (804864074027406773 / 1000000000000000000) (32194562961096271 / 40000000000000000) (√((1 : ℝ) - (((74182400029 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy136_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy136_hz12 : B (256196191797085919 / 1000000000000000000) (256196191797085921 / 1000000000000000000) ((√((1 : ℝ) - (((74182400029 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy136_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy136_hz13 : B (416749699935811101 / 1000000000000000000) (416749699935811149 / 1000000000000000000) (((74182400029 / 125000000000) : ℝ) * (kdot ((74182400029 / 125000000000)))) := bmul (bpoint ((74182400029 / 125000000000) : ℝ)) lowEnergy136_hz8 (by norm_num) (by norm_num)

theorem lowEnergy136_hz14 : B (33647294586644851 / 50000000000000000) (67294589173289707 / 100000000000000000) (((√((1 : ℝ) - (((74182400029 / 125000000000) : ℝ)^2))) / Real.pi) + (((74182400029 / 125000000000) : ℝ) * (kdot ((74182400029 / 125000000000))))) := badd lowEnergy136_hz12 lowEnergy136_hz13 (by norm_num) (by norm_num)

theorem lowEnergy136_hz15 : B (33647294586644851 / 50000000000000000) (67294589173289707 / 100000000000000000) (kappa ((74182400029 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy136_hz14

theorem lowEnergy136 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (59 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (84466650569 / 125000000000) := by
  have hk1 : kappa q ≤ (295237161481 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((59 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy136_hz7.2.trans (by norm_num))
  have hk2 : kappa ((74182400029 / 125000000000) : ℝ) ≤ (672945891733 / 1000000000000) := lowEnergy136_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((768829840057 / 1000000000000) : ℝ)) (R := ((769695865461 / 1000000000000) : ℝ)) (Q2 := ((74182400029 / 125000000000) : ℝ)) (T := ((821043222321 / 1000000000000) : ℝ))
    (B := ((84466650569 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy137_hz0 : B (82035908964350679 / 125000000000000000) (164071817928783987 / 250000000000000000) (kdot ((943 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (599297357294419207 / 1000000000000000000)) (a := (539902691063035993 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (299648678647209603 / 500000000000000000)) (a := (539902691062516821 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy137_hz1 : B (889249 / 4000000) (889249 / 4000000) (((943 / 2000) : ℝ)^2) := bsq (bpoint ((943 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy137_hz2 : B (3110751 / 4000000) (3110751 / 4000000) ((1 : ℝ) - (((943 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy137_hz1 (by norm_num) (by norm_num)

theorem lowEnergy137_hz3 : B (440933030629368931 / 500000000000000000) (881866061258737863 / 1000000000000000000) (√((1 : ℝ) - (((943 / 2000) : ℝ)^2))) := bsqrt lowEnergy137_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy137_hz4 : B (14035334279430831 / 50000000000000000) (140353342794308311 / 500000000000000000) ((√((1 : ℝ) - (((943 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy137_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy137_hz5 : B (309439448613530761 / 1000000000000000000) (1547197243068433 / 5000000000000000) (((943 / 2000) : ℝ) * (kdot ((943 / 2000)))) := bmul (bpoint ((943 / 2000) : ℝ)) lowEnergy137_hz0 (by norm_num) (by norm_num)

theorem lowEnergy137_hz6 : B (590146134202147381 / 1000000000000000000) (295073067101151611 / 500000000000000000) (((√((1 : ℝ) - (((943 / 2000) : ℝ)^2))) / Real.pi) + (((943 / 2000) : ℝ) * (kdot ((943 / 2000))))) := badd lowEnergy137_hz4 lowEnergy137_hz5 (by norm_num) (by norm_num)

theorem lowEnergy137_hz7 : B (590146134202147381 / 1000000000000000000) (295073067101151611 / 500000000000000000) (kappa ((943 / 2000))) := by rw [kappa_eq]; exact lowEnergy137_hz6

theorem lowEnergy137_hz8 : B (702108020303614233 / 1000000000000000000) (702108020303614313 / 1000000000000000000) (kdot ((296565035957 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (25268076478565117 / 50000000000000000)) (a := (93585525497748537 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (505361529571302339 / 1000000000000000000)) (a := (467927627488742561 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy137_hz9 : B (351803282208706811 / 1000000000000000000) (87950820552176703 / 250000000000000000) (((296565035957 / 500000000000) : ℝ)^2) := bsq (bpoint ((296565035957 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy137_hz10 : B (162049179447823297 / 250000000000000000) (648196717791293189 / 1000000000000000000) ((1 : ℝ) - (((296565035957 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy137_hz9 (by norm_num) (by norm_num)

theorem lowEnergy137_hz11 : B (805106649948497933 / 1000000000000000000) (161021329989699587 / 200000000000000000) (√((1 : ℝ) - (((296565035957 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy137_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy137_hz12 : B (128136703055459687 / 500000000000000000) (16017087881932461 / 62500000000000000) ((√((1 : ℝ) - (((296565035957 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy137_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy137_hz13 : B (208220690287039441 / 500000000000000000) (41644138057407893 / 100000000000000000) (((296565035957 / 500000000000) : ℝ) * (kdot ((296565035957 / 500000000000)))) := bmul (bpoint ((296565035957 / 500000000000) : ℝ)) lowEnergy137_hz8 (by norm_num) (by norm_num)

theorem lowEnergy137_hz14 : B (42044674167812391 / 62500000000000000) (336357393342499153 / 500000000000000000) (((√((1 : ℝ) - (((296565035957 / 500000000000) : ℝ)^2))) / Real.pi) + (((296565035957 / 500000000000) : ℝ) * (kdot ((296565035957 / 500000000000))))) := badd lowEnergy137_hz12 lowEnergy137_hz13 (by norm_num) (by norm_num)

theorem lowEnergy137_hz15 : B (42044674167812391 / 62500000000000000) (336357393342499153 / 500000000000000000) (kappa ((296565035957 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy137_hz14

theorem lowEnergy137 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (943 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (675501420803 / 1000000000000) := by
  have hk1 : kappa q ≤ (590146134203 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((943 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy137_hz7.2.trans (by norm_num))
  have hk2 : kappa ((296565035957 / 500000000000) : ℝ) ≤ (134542957337 / 200000000000) := lowEnergy137_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((768616376487 / 1000000000000) : ℝ)) (R := ((769482401891 / 1000000000000) : ℝ)) (Q2 := ((296565035957 / 500000000000) : ℝ)) (T := ((820902227681 / 1000000000000) : ℝ))
    (B := ((675501420803 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy138_hz0 : B (328053411931898067 / 500000000000000000) (26244272954565489 / 40000000000000000) (kdot ((471 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (299841335790344973 / 500000000000000000)) (a := (54018613788457943 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (119936534316137989 / 200000000000000000)) (a := (540186137884043647 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy138_hz1 : B (221841 / 1000000) (221841 / 1000000) (((471 / 1000) : ℝ)^2) := bsq (bpoint ((471 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy138_hz2 : B (778159 / 1000000) (778159 / 1000000) ((1 : ℝ) - (((471 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy138_hz1 (by norm_num) (by norm_num)

theorem lowEnergy138_hz3 : B (88213320989519491 / 100000000000000000) (882133209895194911 / 1000000000000000000) (√((1 : ℝ) - (((471 / 1000) : ℝ)^2))) := bsqrt lowEnergy138_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy138_hz4 : B (140395860820340709 / 500000000000000000) (14039586082034071 / 50000000000000000) ((√((1 : ℝ) - (((471 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy138_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy138_hz5 : B (309026314039847979 / 1000000000000000000) (309026314040008633 / 1000000000000000000) (((471 / 1000) : ℝ) * (kdot ((471 / 1000)))) := bmul (bpoint ((471 / 1000) : ℝ)) lowEnergy138_hz0 (by norm_num) (by norm_num)

theorem lowEnergy138_hz6 : B (589818035680529397 / 1000000000000000000) (589818035680690053 / 1000000000000000000) (((√((1 : ℝ) - (((471 / 1000) : ℝ)^2))) / Real.pi) + (((471 / 1000) : ℝ) * (kdot ((471 / 1000))))) := badd lowEnergy138_hz4 lowEnergy138_hz5 (by norm_num) (by norm_num)

theorem lowEnergy138_hz7 : B (589818035680529397 / 1000000000000000000) (589818035680690053 / 1000000000000000000) (kappa ((471 / 1000))) := by rw [kappa_eq]; exact lowEnergy138_hz6

theorem lowEnergy138_hz8 : B (140395590049898849 / 200000000000000000) (701977950249494327 / 1000000000000000000) (kdot ((592801033987 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (126404512330389969 / 250000000000000000)) (a := (58516492631497547 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (4044944394572479 / 8000000000000000)) (a := (468131941051980249 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy138_hz9 : B (351413065896056329 / 1000000000000000000) (35141306589605633 / 100000000000000000) (((592801033987 / 1000000000000) : ℝ)^2) := bsq (bpoint ((592801033987 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy138_hz10 : B (64858693410394367 / 100000000000000000) (648586934103943671 / 1000000000000000000) ((1 : ℝ) - (((592801033987 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy138_hz9 (by norm_num) (by norm_num)

theorem lowEnergy138_hz11 : B (201337237940467633 / 250000000000000000) (402674475880935267 / 500000000000000000) (√((1 : ℝ) - (((592801033987 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy138_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy138_hz12 : B (64087633293389033 / 250000000000000000) (128175266586778067 / 500000000000000000) ((√((1 : ℝ) - (((592801033987 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy138_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy138_hz13 : B (416133254743975033 / 1000000000000000000) (208066627371987541 / 500000000000000000) (((592801033987 / 1000000000000) : ℝ) * (kdot ((592801033987 / 1000000000000)))) := bmul (bpoint ((592801033987 / 1000000000000) : ℝ)) lowEnergy138_hz8 (by norm_num) (by norm_num)

theorem lowEnergy138_hz14 : B (134496757583506233 / 200000000000000000) (42030236744845701 / 62500000000000000) (((√((1 : ℝ) - (((592801033987 / 1000000000000) : ℝ)^2))) / Real.pi) + (((592801033987 / 1000000000000) : ℝ) * (kdot ((592801033987 / 1000000000000))))) := badd lowEnergy138_hz12 lowEnergy138_hz13 (by norm_num) (by norm_num)

theorem lowEnergy138_hz15 : B (134496757583506233 / 200000000000000000) (42030236744845701 / 62500000000000000) (kappa ((592801033987 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy138_hz14

theorem lowEnergy138 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (471 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (675269743601 / 1000000000000) := by
  have hk1 : kappa q ≤ (589818035681 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((471 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy138_hz7.2.trans (by norm_num))
  have hk2 : kappa ((592801033987 / 1000000000000) : ℝ) ≤ (336241893959 / 500000000000) := lowEnergy138_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((768402912333 / 1000000000000) : ℝ)) (R := ((769268937737 / 1000000000000) : ℝ)) (Q2 := ((592801033987 / 1000000000000) : ℝ)) (T := ((410380636839 / 500000000000) : ℝ))
    (B := ((675269743601 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy139_hz0 : B (655926430614803097 / 1000000000000000000) (327963215307577547 / 500000000000000000) (kdot ((941 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (75008500028360721 / 125000000000000000)) (a := (540469498937476291 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (600068000226885767 / 1000000000000000000)) (a := (33779343683557711 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy139_hz1 : B (885481 / 4000000) (885481 / 4000000) (((941 / 2000) : ℝ)^2) := bsq (bpoint ((941 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy139_hz2 : B (3114519 / 4000000) (3114519 / 4000000) ((1 : ℝ) - (((941 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy139_hz1 (by norm_num) (by norm_num)

theorem lowEnergy139_hz3 : B (882399994333635521 / 1000000000000000000) (441199997166817761 / 500000000000000000) (√((1 : ℝ) - (((941 / 2000) : ℝ)^2))) := bsqrt lowEnergy139_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy139_hz4 : B (4388697527576829 / 15625000000000000) (280876641764917057 / 1000000000000000000) ((√((1 : ℝ) - (((941 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy139_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy139_hz5 : B (308613385604264857 / 1000000000000000000) (38576673200553809 / 125000000000000000) (((941 / 2000) : ℝ) * (kdot ((941 / 2000)))) := bmul (bpoint ((941 / 2000) : ℝ)) lowEnergy139_hz0 (by norm_num) (by norm_num)

theorem lowEnergy139_hz6 : B (589490027369181913 / 1000000000000000000) (589490027369347529 / 1000000000000000000) (((√((1 : ℝ) - (((941 / 2000) : ℝ)^2))) / Real.pi) + (((941 / 2000) : ℝ) * (kdot ((941 / 2000))))) := badd lowEnergy139_hz4 lowEnergy139_hz5 (by norm_num) (by norm_num)

theorem lowEnergy139_hz7 : B (589490027369181913 / 1000000000000000000) (589490027369347529 / 1000000000000000000) (kappa ((941 / 2000))) := by rw [kappa_eq]; exact lowEnergy139_hz6

theorem lowEnergy139_hz8 : B (701847955012312837 / 1000000000000000000) (701847955012312921 / 1000000000000000000) (kdot ((296236043213 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (252937237239743187 / 500000000000000000)) (a := (468336137093045763 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (505874474479486373 / 1000000000000000000)) (a := (468336137093045633 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy139_hz9 : B (351023173193977613 / 1000000000000000000) (175511586596988807 / 500000000000000000) (((296236043213 / 500000000000) : ℝ)^2) := bsq (bpoint ((296236043213 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy139_hz10 : B (324488413403011193 / 500000000000000000) (648976826806022387 / 1000000000000000000) ((1 : ℝ) - (((296236043213 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy139_hz9 (by norm_num) (by norm_num)

theorem lowEnergy139_hz11 : B (402795489922001977 / 500000000000000000) (201397744961000989 / 250000000000000000) (√((1 : ℝ) - (((296236043213 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy139_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy139_hz12 : B (256427573104833303 / 1000000000000000000) (51285514620966661 / 200000000000000000) ((√((1 : ℝ) - (((296236043213 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy139_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy139_hz13 : B (415825322259966371 / 1000000000000000000) (415825322259966421 / 1000000000000000000) (((296236043213 / 500000000000) : ℝ) * (kdot ((296236043213 / 500000000000)))) := bmul (bpoint ((296236043213 / 500000000000) : ℝ)) lowEnergy139_hz8 (by norm_num) (by norm_num)

theorem lowEnergy139_hz14 : B (336126447682399837 / 500000000000000000) (336126447682399863 / 500000000000000000) (((√((1 : ℝ) - (((296236043213 / 500000000000) : ℝ)^2))) / Real.pi) + (((296236043213 / 500000000000) : ℝ) * (kdot ((296236043213 / 500000000000))))) := badd lowEnergy139_hz12 lowEnergy139_hz13 (by norm_num) (by norm_num)

theorem lowEnergy139_hz15 : B (336126447682399837 / 500000000000000000) (336126447682399863 / 500000000000000000) (kappa ((296236043213 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy139_hz14

theorem lowEnergy139 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (941 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (168759543219 / 250000000000) := by
  have hk1 : kappa q ≤ (58949002737 / 100000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((941 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy139_hz7.2.trans (by norm_num))
  have hk2 : kappa ((296236043213 / 500000000000) : ℝ) ≤ (134450579073 / 200000000000) := lowEnergy139_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((384094723789 / 500000000000) : ℝ)) (R := ((384527736491 / 500000000000) : ℝ)) (Q2 := ((296236043213 / 500000000000) : ℝ)) (T := ((205155090073 / 250000000000) : ℝ))
    (B := ((168759543219 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy140_hz0 : B (131149218372080969 / 200000000000000000) (655746091860768091 / 1000000000000000000) (kdot ((47 / 100))) := by
    constructor
    · apply bkdot_lower (q := (600453343472309121 / 1000000000000000000)) (a := (540752774390463831 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (938208349175483 / 1562500000000000)) (a := (4224631049921041 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy140_hz1 : B (2209 / 10000) (2209 / 10000) (((47 / 100) : ℝ)^2) := bsq (bpoint ((47 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy140_hz2 : B (7791 / 10000) (7791 / 10000) ((1 : ℝ) - (((47 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy140_hz1 (by norm_num) (by norm_num)

theorem lowEnergy140_hz3 : B (882666414904294407 / 1000000000000000000) (110333301863036801 / 125000000000000000) (√((1 : ℝ) - (((47 / 100) : ℝ)^2))) := bsqrt lowEnergy140_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy140_hz4 : B (140480723033220253 / 500000000000000000) (70240361516610127 / 250000000000000000) ((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) := bdiv lowEnergy140_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy140_hz5 : B (308200663174390277 / 1000000000000000000) (308200663174561003 / 1000000000000000000) (((47 / 100) : ℝ) * (kdot ((47 / 100)))) := bmul (bpoint ((47 / 100) : ℝ)) lowEnergy140_hz0 (by norm_num) (by norm_num)

theorem lowEnergy140_hz6 : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) + (((47 / 100) : ℝ) * (kdot ((47 / 100))))) := badd lowEnergy140_hz4 lowEnergy140_hz5 (by norm_num) (by norm_num)

theorem lowEnergy140_hz7 : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (kappa ((47 / 100))) := by rw [kappa_eq]; exact lowEnergy140_hz6

theorem lowEnergy140_hz8 : B (28068721379692827 / 40000000000000000) (17542950862308019 / 25000000000000000) (kdot ((148035807301 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (506130805188252203 / 1000000000000000000)) (a := (234270107884312367 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (253065402594126101 / 500000000000000000)) (a := (468540215768624601 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy140_hz9 : B (175316801946070439 / 500000000000000000) (350633603892140879 / 1000000000000000000) (((148035807301 / 250000000000) : ℝ)^2) := bsq (bpoint ((148035807301 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy140_hz10 : B (649366396107859121 / 1000000000000000000) (324683198053929561 / 500000000000000000) ((1 : ℝ) - (((148035807301 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy140_hz9 (by norm_num) (by norm_num)

theorem lowEnergy140_hz11 : B (402916367286022249 / 500000000000000000) (1611665469144089 / 2000000000000000) (√((1 : ℝ) - (((148035807301 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy140_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy140_hz12 : B (128252263012400141 / 500000000000000000) (64126131506200071 / 250000000000000000) ((√((1 : ℝ) - (((148035807301 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy140_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy140_hz13 : B (415517582934966619 / 1000000000000000000) (41551758293496667 / 100000000000000000) (((148035807301 / 250000000000) : ℝ) * (kdot ((148035807301 / 250000000000)))) := bmul (bpoint ((148035807301 / 250000000000) : ℝ)) lowEnergy140_hz8 (by norm_num) (by norm_num)

theorem lowEnergy140_hz14 : B (672022108959766901 / 1000000000000000000) (336011054479883477 / 500000000000000000) (((√((1 : ℝ) - (((148035807301 / 250000000000) : ℝ)^2))) / Real.pi) + (((148035807301 / 250000000000) : ℝ) * (kdot ((148035807301 / 250000000000))))) := badd lowEnergy140_hz12 lowEnergy140_hz13 (by norm_num) (by norm_num)

theorem lowEnergy140_hz15 : B (672022108959766901 / 1000000000000000000) (336011054479883477 / 500000000000000000) (kappa ((148035807301 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy140_hz14

theorem lowEnergy140 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (47 / 100)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (134961341713 / 200000000000) := by
  have hk1 : kappa q ≤ (294581054621 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((47 / 100) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy140_hz7.2.trans (by norm_num))
  have hk2 : kappa ((148035807301 / 250000000000) : ℝ) ≤ (4200138181 / 6250000000) := lowEnergy140_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191993995551 / 250000000000) : ℝ)) (R := ((96105250951 / 125000000000) : ℝ)) (Q2 := ((148035807301 / 250000000000) : ℝ)) (T := ((51279967969 / 62500000000) : ℝ))
    (B := ((134961341713 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy141_hz0 : B (131113161498682399 / 200000000000000000) (327782903746893421 / 500000000000000000) (kdot ((939 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (150209675389002647 / 250000000000000000)) (a := (541035964411914743 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (600838701556010587 / 1000000000000000000)) (a := (541035964411325937 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy141_hz1 : B (881721 / 4000000) (881721 / 4000000) (((939 / 2000) : ℝ)^2) := bsq (bpoint ((939 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy141_hz2 : B (3118279 / 4000000) (3118279 / 4000000) ((1 : ℝ) - (((939 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy141_hz1 (by norm_num) (by norm_num)

theorem lowEnergy141_hz3 : B (441466235968278779 / 500000000000000000) (882932471936557559 / 1000000000000000000) (√((1 : ℝ) - (((939 / 2000) : ℝ)^2))) := bsqrt lowEnergy141_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy141_hz4 : B (281046134650098587 / 1000000000000000000) (70261533662524647 / 250000000000000000) ((√((1 : ℝ) - (((939 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy141_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy141_hz5 : B (307788146618156931 / 1000000000000000000) (307788146618332923 / 1000000000000000000) (((939 / 2000) : ℝ) * (kdot ((939 / 2000)))) := bmul (bpoint ((939 / 2000) : ℝ)) lowEnergy141_hz0 (by norm_num) (by norm_num)

theorem lowEnergy141_hz6 : B (294417140634127759 / 500000000000000000) (588834281268431511 / 1000000000000000000) (((√((1 : ℝ) - (((939 / 2000) : ℝ)^2))) / Real.pi) + (((939 / 2000) : ℝ) * (kdot ((939 / 2000))))) := badd lowEnergy141_hz4 lowEnergy141_hz5 (by norm_num) (by norm_num)

theorem lowEnergy141_hz7 : B (294417140634127759 / 500000000000000000) (588834281268431511 / 1000000000000000000) (kappa ((939 / 2000))) := by rw [kappa_eq]; exact lowEnergy141_hz6

theorem lowEnergy141_hz8 : B (701588188589600123 / 1000000000000000000) (701588188589600211 / 1000000000000000000) (kdot ((591814462293 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (253193520795734551 / 500000000000000000)) (a := (58593022154458443 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (506387041591469101 / 1000000000000000000)) (a := (468744177235667407 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy141_hz9 : B (175122178889576359 / 500000000000000000) (350244357779152719 / 1000000000000000000) (((591814462293 / 1000000000000) : ℝ)^2) := bsq (bpoint ((591814462293 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy141_hz10 : B (649755642220847281 / 1000000000000000000) (324877821110423641 / 500000000000000000) ((1 : ℝ) - (((591814462293 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy141_hz9 (by norm_num) (by norm_num)

theorem lowEnergy141_hz11 : B (806074216323067413 / 1000000000000000000) (161214843264613483 / 200000000000000000) (√((1 : ℝ) - (((591814462293 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy141_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy141_hz12 : B (32072674006685481 / 125000000000000000) (5131627841069677 / 20000000000000000) ((√((1 : ℝ) - (((591814462293 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy141_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy141_hz13 : B (207605018290637037 / 500000000000000000) (415210036581274127 / 1000000000000000000) (((591814462293 / 1000000000000) : ℝ) * (kdot ((591814462293 / 1000000000000)))) := bmul (bpoint ((591814462293 / 1000000000000) : ℝ)) lowEnergy141_hz8 (by norm_num) (by norm_num)

theorem lowEnergy141_hz14 : B (335895714317378961 / 500000000000000000) (671791428634757977 / 1000000000000000000) (((√((1 : ℝ) - (((591814462293 / 1000000000000) : ℝ)^2))) / Real.pi) + (((591814462293 / 1000000000000) : ℝ) * (kdot ((591814462293 / 1000000000000))))) := badd lowEnergy141_hz12 lowEnergy141_hz13 (by norm_num) (by norm_num)

theorem lowEnergy141_hz15 : B (335895714317378961 / 500000000000000000) (671791428634757977 / 1000000000000000000) (kappa ((591814462293 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy141_hz14

theorem lowEnergy141 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (939 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (168643837649 / 250000000000) := by
  have hk1 : kappa q ≤ (588834281269 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((939 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy141_hz7.2.trans (by norm_num))
  have hk2 : kappa ((591814462293 / 1000000000000) : ℝ) ≤ (134358285727 / 200000000000) := lowEnergy141_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((23992578631 / 31250000000) : ℝ)) (R := ((192157135399 / 250000000000) : ℝ)) (Q2 := ((591814462293 / 1000000000000) : ℝ)) (T := ((205084663823 / 250000000000) : ℝ))
    (B := ((168643837649 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy142_hz0 : B (327692788703433227 / 500000000000000000) (131077115481450653 / 200000000000000000) (kdot ((469 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (601224074716790251 / 1000000000000000000)) (a := (108263813833967681 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2404896298867161 / 4000000000000000)) (a := (270659534584615403 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy142_hz1 : B (219961 / 1000000) (219961 / 1000000) (((469 / 1000) : ℝ)^2) := bsq (bpoint ((469 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy142_hz2 : B (780039 / 1000000) (780039 / 1000000) ((1 : ℝ) - (((469 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy142_hz1 (by norm_num) (by norm_num)

theorem lowEnergy142_hz3 : B (883198165758964877 / 1000000000000000000) (441599082879482439 / 500000000000000000) (√((1 : ℝ) - (((469 / 1000) : ℝ)^2))) := bsqrt lowEnergy142_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy142_hz4 : B (281130707620468797 / 1000000000000000000) (140565353810234399 / 500000000000000000) ((√((1 : ℝ) - (((469 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy142_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy142_hz5 : B (153687917901910183 / 500000000000000000) (153687917902000891 / 500000000000000000) (((469 / 1000) : ℝ) * (kdot ((469 / 1000)))) := bmul (bpoint ((469 / 1000) : ℝ)) lowEnergy142_hz0 (by norm_num) (by norm_num)

theorem lowEnergy142_hz6 : B (588506543424289163 / 1000000000000000000) (29425327171223529 / 50000000000000000) (((√((1 : ℝ) - (((469 / 1000) : ℝ)^2))) / Real.pi) + (((469 / 1000) : ℝ) * (kdot ((469 / 1000))))) := badd lowEnergy142_hz4 lowEnergy142_hz5 (by norm_num) (by norm_num)

theorem lowEnergy142_hz7 : B (588506543424289163 / 1000000000000000000) (29425327171223529 / 50000000000000000) (kappa ((469 / 1000))) := by rw [kappa_eq]; exact lowEnergy142_hz6

theorem lowEnergy142_hz8 : B (140291683440891973 / 200000000000000000) (140291683440891991 / 200000000000000000) (kdot ((118297157133 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (126660795958102917 / 250000000000000000)) (a := (468948021650768947 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (506643183832411667 / 1000000000000000000)) (a := (468948021650768807 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy142_hz9 : B (349855434643742319 / 1000000000000000000) (4373192933046779 / 12500000000000000) (((118297157133 / 200000000000) : ℝ)^2) := bsq (bpoint ((118297157133 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy142_hz10 : B (8126807066953221 / 12500000000000000) (650144565356257681 / 1000000000000000000) ((1 : ℝ) - (((118297157133 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy142_hz9 (by norm_num) (by norm_num)

theorem lowEnergy142_hz11 : B (201578856368335677 / 250000000000000000) (80631542547334271 / 100000000000000000) (√((1 : ℝ) - (((118297157133 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy142_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy142_hz12 : B (128329085655327233 / 500000000000000000) (64164542827663617 / 250000000000000000) ((√((1 : ℝ) - (((118297157133 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy142_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy142_hz13 : B (12965708844109603 / 31250000000000000) (8298053660230147 / 20000000000000000) (((118297157133 / 200000000000) : ℝ) * (kdot ((118297157133 / 200000000000)))) := bmul (bpoint ((118297157133 / 200000000000) : ℝ)) lowEnergy142_hz8 (by norm_num) (by norm_num)

theorem lowEnergy142_hz14 : B (335780427161080881 / 500000000000000000) (335780427161080909 / 500000000000000000) (((√((1 : ℝ) - (((118297157133 / 200000000000) : ℝ)^2))) / Real.pi) + (((118297157133 / 200000000000) : ℝ) * (kdot ((118297157133 / 200000000000))))) := badd lowEnergy142_hz12 lowEnergy142_hz13 (by norm_num) (by norm_num)

theorem lowEnergy142_hz15 : B (335780427161080881 / 500000000000000000) (335780427161080909 / 500000000000000000) (kappa ((118297157133 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy142_hz14

theorem lowEnergy142 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (469 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (134868819781 / 200000000000) := by
  have hk1 : kappa q ≤ (23540261737 / 40000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((469 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy142_hz7.2.trans (by norm_num))
  have hk2 : kappa ((118297157133 / 200000000000) : ℝ) ≤ (671560854323 / 1000000000000) := lowEnergy142_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191887262381 / 250000000000) : ℝ)) (R := ((48025942183 / 62500000000) : ℝ)) (Q2 := ((118297157133 / 200000000000) : ℝ)) (T := ((820197863637 / 1000000000000) : ℝ))
    (B := ((134868819781 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy143_hz0 : B (327602700747020313 / 500000000000000000) (327602700747219887 / 500000000000000000) (kdot ((937 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (601609463193199053 / 1000000000000000000)) (a := (270801044415941067 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (150402365798299763 / 250000000000000000)) (a := (108320417766251031 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy143_hz1 : B (877969 / 4000000) (877969 / 4000000) (((937 / 2000) : ℝ)^2) := bsq (bpoint ((937 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy143_hz2 : B (3122031 / 4000000) (3122031 / 4000000) ((1 : ℝ) - (((937 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy143_hz1 (by norm_num) (by norm_num)

theorem lowEnergy143_hz3 : B (883463496699212807 / 1000000000000000000) (110432937087401601 / 125000000000000000) (√((1 : ℝ) - (((937 / 2000) : ℝ)^2))) := bsqrt lowEnergy143_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy143_hz4 : B (140607582540930077 / 500000000000000000) (56243033016372031 / 200000000000000000) ((√((1 : ℝ) - (((937 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy143_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy143_hz5 : B (306963730599958033 / 1000000000000000000) (61392746120029007 / 200000000000000000) (((937 / 2000) : ℝ) * (kdot ((937 / 2000)))) := bmul (bpoint ((937 / 2000) : ℝ)) lowEnergy143_hz0 (by norm_num) (by norm_num)

theorem lowEnergy143_hz6 : B (588178895681818187 / 1000000000000000000) (58817889568200519 / 100000000000000000) (((√((1 : ℝ) - (((937 / 2000) : ℝ)^2))) / Real.pi) + (((937 / 2000) : ℝ) * (kdot ((937 / 2000))))) := badd lowEnergy143_hz4 lowEnergy143_hz5 (by norm_num) (by norm_num)

theorem lowEnergy143_hz7 : B (588178895681818187 / 1000000000000000000) (58817889568200519 / 100000000000000000) (kappa ((937 / 2000))) := by rw [kappa_eq]; exact lowEnergy143_hz6

theorem lowEnergy143_hz8 : B (701328720238618117 / 1000000000000000000) (701328720238618209 / 1000000000000000000) (kdot ((118231439859 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (253449616025840439 / 500000000000000000)) (a := (469151749168309609 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (506899232051680877 / 1000000000000000000)) (a := (93830349833661893 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy143_hz9 : B (87366708569577087 / 250000000000000000) (349466834278308349 / 1000000000000000000) (((118231439859 / 200000000000) : ℝ)^2) := bsq (bpoint ((118231439859 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy143_hz10 : B (650533165721691651 / 1000000000000000000) (162633291430422913 / 250000000000000000) ((1 : ℝ) - (((118231439859 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy143_hz9 (by norm_num) (by norm_num)

theorem lowEnergy143_hz11 : B (403278181198069421 / 500000000000000000) (806556362396138843 / 1000000000000000000) (√((1 : ℝ) - (((118231439859 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy143_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy143_hz12 : B (256734863915127177 / 1000000000000000000) (128367431957563589 / 500000000000000000) ((√((1 : ℝ) - (((118231439859 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy143_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy143_hz13 : B (41459552204140807 / 100000000000000000) (663352835266253 / 1600000000000000) (((118231439859 / 200000000000) : ℝ) * (kdot ((118231439859 / 200000000000)))) := bmul (bpoint ((118231439859 / 200000000000) : ℝ)) lowEnergy143_hz8 (by norm_num) (by norm_num)

theorem lowEnergy143_hz14 : B (671330385956535247 / 1000000000000000000) (671330385956535303 / 1000000000000000000) (((√((1 : ℝ) - (((118231439859 / 200000000000) : ℝ)^2))) / Real.pi) + (((118231439859 / 200000000000) : ℝ) * (kdot ((118231439859 / 200000000000))))) := badd lowEnergy143_hz12 lowEnergy143_hz13 (by norm_num) (by norm_num)

theorem lowEnergy143_hz15 : B (671330385956535247 / 1000000000000000000) (671330385956535303 / 1000000000000000000) (kappa ((118231439859 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy143_hz14

theorem lowEnergy143 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (937 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (674112953423 / 1000000000000) := by
  have hk1 : kappa q ≤ (588178895683 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((937 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy143_hz7.2.trans (by norm_num))
  have hk2 : kappa ((118231439859 / 200000000000) : ℝ) ≤ (671330385957 / 1000000000000) := lowEnergy143_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((767335582183 / 1000000000000) : ℝ)) (R := ((768201607587 / 1000000000000) : ℝ)) (Q2 := ((118231439859 / 200000000000) : ℝ)) (T := ((820057112519 / 1000000000000) : ℝ))
    (B := ((674112953423 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy144_hz0 : B (131005055929687323 / 200000000000000000) (81878159956106061 / 125000000000000000) (kdot ((117 / 250))) := by
    constructor
    · apply bkdot_lower (q := (300997433611770077 / 500000000000000000)) (a := (541885023565332431 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (601994867223540153 / 1000000000000000000)) (a := (108377004712937093 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy144_hz1 : B (13689 / 62500) (13689 / 62500) (((117 / 250) : ℝ)^2) := bsq (bpoint ((117 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy144_hz2 : B (48811 / 62500) (48811 / 62500) ((1 : ℝ) - (((117 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy144_hz1 (by norm_num) (by norm_num)

theorem lowEnergy144_hz3 : B (55233029067759809 / 62500000000000000) (176745693016831389 / 200000000000000000) (√((1 : ℝ) - (((117 / 250) : ℝ)^2))) := bsqrt lowEnergy144_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy144_hz4 : B (11251980285532561 / 40000000000000000) (140649753569157013 / 500000000000000000) ((√((1 : ℝ) - (((117 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy144_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy144_hz5 : B (61310366175093667 / 200000000000000000) (306551830875661093 / 1000000000000000000) (((117 / 250) : ℝ) * (kdot ((117 / 250)))) := bmul (bpoint ((117 / 250) : ℝ)) lowEnergy144_hz0 (by norm_num) (by norm_num)

theorem lowEnergy144_hz6 : B (14696283450344559 / 25000000000000000) (587851338013975119 / 1000000000000000000) (((√((1 : ℝ) - (((117 / 250) : ℝ)^2))) / Real.pi) + (((117 / 250) : ℝ) * (kdot ((117 / 250))))) := badd lowEnergy144_hz4 lowEnergy144_hz5 (by norm_num) (by norm_num)

theorem lowEnergy144_hz7 : B (14696283450344559 / 25000000000000000) (587851338013975119 / 1000000000000000000) (kappa ((117 / 250))) := by rw [kappa_eq]; exact lowEnergy144_hz6

theorem lowEnergy144_hz8 : B (2191247179975137 / 3125000000000000) (140239819518408787 / 200000000000000000) (kdot ((590828703153 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (101431037278687871 / 200000000000000000)) (a := (93871071989083583 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (253577593196719677 / 500000000000000000)) (a := (58669419993177221 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy144_hz9 : B (21817409779340987 / 62500000000000000) (349078556469455793 / 1000000000000000000) (((590828703153 / 1000000000000) : ℝ)^2) := bsq (bpoint ((590828703153 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy144_hz10 : B (650921443530544207 / 1000000000000000000) (40682590220659013 / 62500000000000000) ((1 : ℝ) - (((590828703153 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy144_hz9 (by norm_num) (by norm_num)

theorem lowEnergy144_hz11 : B (806797027467593119 / 1000000000000000000) (806797027467593121 / 1000000000000000000) (√((1 : ℝ) - (((590828703153 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy144_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy144_hz12 : B (256811469986630201 / 1000000000000000000) (256811469986630203 / 1000000000000000000) ((√((1 : ℝ) - (((590828703153 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy144_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy144_hz13 : B (414288553482361147 / 1000000000000000000) (103572138370590301 / 250000000000000000) (((590828703153 / 1000000000000) : ℝ) * (kdot ((590828703153 / 1000000000000)))) := bmul (bpoint ((590828703153 / 1000000000000) : ℝ)) lowEnergy144_hz8 (by norm_num) (by norm_num)

theorem lowEnergy144_hz14 : B (167775005867247837 / 250000000000000000) (671100023468991407 / 1000000000000000000) (((√((1 : ℝ) - (((590828703153 / 1000000000000) : ℝ)^2))) / Real.pi) + (((590828703153 / 1000000000000) : ℝ) * (kdot ((590828703153 / 1000000000000))))) := badd lowEnergy144_hz12 lowEnergy144_hz13 (by norm_num) (by norm_num)

theorem lowEnergy144_hz15 : B (167775005867247837 / 250000000000000000) (671100023468991407 / 1000000000000000000) (kappa ((590828703153 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy144_hz14

theorem lowEnergy144 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (117 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (336940957041 / 500000000000) := by
  have hk1 : kappa q ≤ (293925669007 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((117 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy144_hz7.2.trans (by norm_num))
  have hk2 : kappa ((590828703153 / 1000000000000) : ℝ) ≤ (671100023469 / 1000000000000) := lowEnergy144_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191780528537 / 250000000000) : ℝ)) (R := ((23999629361 / 31250000000) : ℝ)) (Q2 := ((590828703153 / 1000000000000) : ℝ)) (T := ((819916401917 / 1000000000000) : ℝ))
    (B := ((336940957041 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy145_hz0 : B (654845211763785443 / 1000000000000000000) (654845211764210437 / 1000000000000000000) (kdot ((187 / 400))) := by
    constructor
    · apply bkdot_lower (q := (602380287045870283 / 1000000000000000000)) (a := (542167873537116219 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (301190143522935141 / 500000000000000000)) (a := (271083936768224321 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy145_hz1 : B (34969 / 160000) (34969 / 160000) (((187 / 400) : ℝ)^2) := bsq (bpoint ((187 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy145_hz2 : B (125031 / 160000) (125031 / 160000) ((1 : ℝ) - (((187 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy145_hz1 (by norm_num) (by norm_num)

theorem lowEnergy145_hz3 : B (883993071239814639 / 1000000000000000000) (11049913390497683 / 12500000000000000) (√((1 : ℝ) - (((187 / 400) : ℝ)^2))) := bsqrt lowEnergy145_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy145_hz4 : B (70345933473401239 / 250000000000000000) (281383733893604957 / 1000000000000000000) ((√((1 : ℝ) - (((187 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy145_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy145_hz5 : B (153070068249784847 / 500000000000000000) (15307006824988419 / 50000000000000000) (((187 / 400) : ℝ) * (kdot ((187 / 400)))) := bmul (bpoint ((187 / 400) : ℝ)) lowEnergy145_hz0 (by norm_num) (by norm_num)

theorem lowEnergy145_hz6 : B (11750477407863493 / 20000000000000000) (587523870393373337 / 1000000000000000000) (((√((1 : ℝ) - (((187 / 400) : ℝ)^2))) / Real.pi) + (((187 / 400) : ℝ) * (kdot ((187 / 400))))) := badd lowEnergy145_hz4 lowEnergy145_hz5 (by norm_num) (by norm_num)

theorem lowEnergy145_hz7 : B (11750477407863493 / 20000000000000000) (587523870393373337 / 1000000000000000000) (kappa ((187 / 400))) := by rw [kappa_eq]; exact lowEnergy145_hz6

theorem lowEnergy145_hz8 : B (701069549167297551 / 1000000000000000000) (43816846822956103 / 62500000000000000) (kdot ((118100059443 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (50741104699684101 / 100000000000000000)) (a := (117389713533787863 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (507411046996841009 / 1000000000000000000)) (a := (469558854135151301 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy145_hz9 : B (43586325126375417 / 125000000000000000) (348690601011003337 / 1000000000000000000) (((118100059443 / 200000000000) : ℝ)^2) := bsq (bpoint ((118100059443 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy145_hz10 : B (651309398988996663 / 1000000000000000000) (81413674873624583 / 125000000000000000) ((1 : ℝ) - (((118100059443 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy145_hz9 (by norm_num) (by norm_num)

theorem lowEnergy145_hz11 : B (403518710529324979 / 500000000000000000) (807037421058649959 / 1000000000000000000) (√((1 : ℝ) - (((118100059443 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy145_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy145_hz12 : B (256887989643238817 / 1000000000000000000) (128443994821619409 / 500000000000000000) ((√((1 : ℝ) - (((118100059443 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy145_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy145_hz13 : B (413981777151675259 / 1000000000000000000) (413981777151675317 / 1000000000000000000) (((118100059443 / 200000000000) : ℝ) * (kdot ((118100059443 / 200000000000)))) := bmul (bpoint ((118100059443 / 200000000000) : ℝ)) lowEnergy145_hz8 (by norm_num) (by norm_num)

theorem lowEnergy145_hz14 : B (167717441698728519 / 250000000000000000) (134173953358982827 / 200000000000000000) (((√((1 : ℝ) - (((118100059443 / 200000000000) : ℝ)^2))) / Real.pi) + (((118100059443 / 200000000000) : ℝ) * (kdot ((118100059443 / 200000000000))))) := badd lowEnergy145_hz12 lowEnergy145_hz13 (by norm_num) (by norm_num)

theorem lowEnergy145_hz15 : B (167717441698728519 / 250000000000000000) (134173953358982827 / 200000000000000000) (kappa ((118100059443 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy145_hz14

theorem lowEnergy145 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (187 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (673650980819 / 1000000000000) := by
  have hk1 : kappa q ≤ (293761935197 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((187 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy145_hz7.2.trans (by norm_num))
  have hk2 : kappa ((118100059443 / 200000000000) : ℝ) ≤ (134173953359 / 200000000000) := lowEnergy145_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191727161351 / 250000000000) : ℝ)) (R := ((95971833851 / 125000000000) : ℝ)) (Q2 := ((118100059443 / 200000000000) : ℝ)) (T := ((819775731813 / 1000000000000) : ℝ))
    (B := ((673650980819 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy146_hz0 : B (654665197734046257 / 1000000000000000000) (327332598867242391 / 500000000000000000) (kdot ((467 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (301382861449000543 / 500000000000000000)) (a := (542450638913802081 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (120553144579600217 / 200000000000000000)) (a := (16951582466034789 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy146_hz1 : B (218089 / 1000000) (218089 / 1000000) (((467 / 1000) : ℝ)^2) := bsq (bpoint ((467 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy146_hz2 : B (781911 / 1000000) (781911 / 1000000) ((1 : ℝ) - (((467 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy146_hz1 (by norm_num) (by norm_num)

theorem lowEnergy146_hz3 : B (884257315491367591 / 1000000000000000000) (110532164436420949 / 125000000000000000) (√((1 : ℝ) - (((467 / 1000) : ℝ)^2))) := bsqrt lowEnergy146_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy146_hz4 : B (281467845451241497 / 1000000000000000000) (281467845451241499 / 1000000000000000000) ((√((1 : ℝ) - (((467 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy146_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy146_hz5 : B (152864323670899801 / 500000000000000000) (152864323671002197 / 500000000000000000) (((467 / 1000) : ℝ) * (kdot ((467 / 1000)))) := bmul (bpoint ((467 / 1000) : ℝ)) lowEnergy146_hz0 (by norm_num) (by norm_num)

theorem lowEnergy146_hz6 : B (587196492793041099 / 1000000000000000000) (587196492793245893 / 1000000000000000000) (((√((1 : ℝ) - (((467 / 1000) : ℝ)^2))) / Real.pi) + (((467 / 1000) : ℝ) * (kdot ((467 / 1000))))) := badd lowEnergy146_hz4 lowEnergy146_hz5 (by norm_num) (by norm_num)

theorem lowEnergy146_hz7 : B (587196492793041099 / 1000000000000000000) (587196492793245893 / 1000000000000000000) (kappa ((467 / 1000))) := by rw [kappa_eq]; exact lowEnergy146_hz6

theorem lowEnergy146_hz8 : B (700940074864401151 / 1000000000000000000) (560752059891521 / 800000000000000) (kdot ((11803439629 / 20000000000))) := by
    constructor
    · apply bkdot_lower (q := (253833407003080593 / 500000000000000000)) (a := (469762231894555447 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (101533362801232237 / 200000000000000000)) (a := (117440557973638823 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy146_hz9 : B (43537870961077393 / 125000000000000000) (69660593537723829 / 200000000000000000) (((11803439629 / 20000000000) : ℝ)^2) := bsq (bpoint ((11803439629 / 20000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy146_hz10 : B (130339406462276171 / 200000000000000000) (81462129038922607 / 125000000000000000) ((1 : ℝ) - (((11803439629 / 20000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy146_hz9 (by norm_num) (by norm_num)

theorem lowEnergy146_hz11 : B (100909692943073243 / 125000000000000000) (161455508708917189 / 200000000000000000) (√((1 : ℝ) - (((11803439629 / 20000000000) : ℝ)^2))) := bsqrt lowEnergy146_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy146_hz12 : B (256964423004407269 / 1000000000000000000) (25696442300440727 / 100000000000000000) ((√((1 : ℝ) - (((11803439629 / 20000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy146_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy146_hz13 : B (413675192860434967 / 1000000000000000000) (206837596430217513 / 500000000000000000) (((11803439629 / 20000000000) : ℝ) * (kdot ((11803439629 / 20000000000)))) := bmul (bpoint ((11803439629 / 20000000000) : ℝ)) lowEnergy146_hz8 (by norm_num) (by norm_num)

theorem lowEnergy146_hz14 : B (167659903966210559 / 250000000000000000) (83829951983105287 / 125000000000000000) (((√((1 : ℝ) - (((11803439629 / 20000000000) : ℝ)^2))) / Real.pi) + (((11803439629 / 20000000000) : ℝ) * (kdot ((11803439629 / 20000000000))))) := badd lowEnergy146_hz12 lowEnergy146_hz13 (by norm_num) (by norm_num)

theorem lowEnergy146_hz15 : B (167659903966210559 / 250000000000000000) (83829951983105287 / 125000000000000000) (kappa ((11803439629 / 20000000000))) := by rw [kappa_eq]; exact lowEnergy146_hz14

theorem lowEnergy146 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (467 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (336710076781 / 500000000000) := by
  have hk1 : kappa q ≤ (293598246397 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((467 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy146_hz7.2.trans (by norm_num))
  have hk2 : kappa ((11803439629 / 20000000000) : ℝ) ≤ (134127923173 / 200000000000) := lowEnergy146_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((76669517593 / 100000000000) : ℝ)) (R := ((383780600667 / 500000000000) : ℝ)) (Q2 := ((11803439629 / 20000000000) : ℝ)) (T := ((163927020437 / 200000000000) : ℝ))
    (B := ((336710076781 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy147_hz0 : B (654485237453405549 / 1000000000000000000) (163621309363464507 / 250000000000000000) (kdot ((933 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (120630235003500093 / 200000000000000000)) (a := (542733319861601483 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (37696948438593779 / 62500000000000000)) (a := (135683329965222683 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy147_hz1 : B (870489 / 4000000) (870489 / 4000000) (((933 / 2000) : ℝ)^2) := bsq (bpoint ((933 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy147_hz2 : B (3129511 / 4000000) (3129511 / 4000000) ((1 : ℝ) - (((933 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy147_hz1 (by norm_num) (by norm_num)

theorem lowEnergy147_hz3 : B (884521198163164431 / 1000000000000000000) (55282574885197777 / 62500000000000000) (√((1 : ℝ) - (((933 / 2000) : ℝ)^2))) := bsqrt lowEnergy147_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy147_hz4 : B (17596990119654189 / 62500000000000000) (11262073676578681 / 40000000000000000) ((√((1 : ℝ) - (((933 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy147_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy147_hz5 : B (38164670409001711 / 125000000000000000) (305317363272224771 / 1000000000000000000) (((933 / 2000) : ℝ) * (kdot ((933 / 2000)))) := bmul (bpoint ((933 / 2000) : ℝ)) lowEnergy147_hz0 (by norm_num) (by norm_num)

theorem lowEnergy147_hz6 : B (73358650648310089 / 125000000000000000) (146717301296672949 / 250000000000000000) (((√((1 : ℝ) - (((933 / 2000) : ℝ)^2))) / Real.pi) + (((933 / 2000) : ℝ) * (kdot ((933 / 2000))))) := badd lowEnergy147_hz4 lowEnergy147_hz5 (by norm_num) (by norm_num)

theorem lowEnergy147_hz7 : B (73358650648310089 / 125000000000000000) (146717301296672949 / 250000000000000000) (kappa ((933 / 2000))) := by rw [kappa_eq]; exact lowEnergy147_hz6

theorem lowEnergy147_hz8 : B (700810674586754059 / 1000000000000000000) (700810674586754161 / 1000000000000000000) (kdot ((117968751167 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (507922487559111469 / 1000000000000000000)) (a := (469965493375369739 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (126980621889777867 / 250000000000000000)) (a := (23498274668768479 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy147_hz9 : B (43489457037192387 / 125000000000000000) (347915656297539097 / 1000000000000000000) (((117968751167 / 200000000000) : ℝ)^2) := bsq (bpoint ((117968751167 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy147_hz10 : B (652084343702460903 / 1000000000000000000) (81510542962807613 / 125000000000000000) ((1 : ℝ) - (((117968751167 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy147_hz9 (by norm_num) (by norm_num)

theorem lowEnergy147_hz11 : B (403758697647016919 / 500000000000000000) (807517395294033839 / 1000000000000000000) (√((1 : ℝ) - (((117968751167 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy147_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy147_hz12 : B (257040770187475011 / 1000000000000000000) (257040770187475013 / 1000000000000000000) ((√((1 : ℝ) - (((117968751167 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy147_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy147_hz13 : B (413368800427511 / 1000000000000000) (413368800427511061 / 1000000000000000000) (((117968751167 / 200000000000) : ℝ) * (kdot ((117968751167 / 200000000000)))) := bmul (bpoint ((117968751167 / 200000000000) : ℝ)) lowEnergy147_hz8 (by norm_num) (by norm_num)

theorem lowEnergy147_hz14 : B (670409570614986011 / 1000000000000000000) (335204785307493037 / 500000000000000000) (((√((1 : ℝ) - (((117968751167 / 200000000000) : ℝ)^2))) / Real.pi) + (((117968751167 / 200000000000) : ℝ) * (kdot ((117968751167 / 200000000000))))) := badd lowEnergy147_hz12 lowEnergy147_hz13 (by norm_num) (by norm_num)

theorem lowEnergy147_hz15 : B (670409570614986011 / 1000000000000000000) (335204785307493037 / 500000000000000000) (kappa ((117968751167 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy147_hz14

theorem lowEnergy147 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (933 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (2692757729 / 4000000000) := by
  have hk1 : kappa q ≤ (586869205187 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((933 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy147_hz7.2.trans (by norm_num))
  have hk2 : kappa ((117968751167 / 200000000000) : ℝ) ≤ (134081914123 / 200000000000) := lowEnergy147_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((76648170571 / 100000000000) : ℝ)) (R := ((383673865557 / 500000000000) : ℝ)) (Q2 := ((117968751167 / 200000000000) : ℝ)) (T := ((163898902603 / 200000000000) : ℝ))
    (B := ((2692757729 / 4000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy148_hz0 : B (327152665408138189 / 500000000000000000) (327152665408371623 / 500000000000000000) (kdot ((233 / 500))) := by
    constructor
    · apply bkdot_lower (q := (3772104022760587 / 6250000000000000)) (a := (67876989568296251 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (603536643641693919 / 1000000000000000000)) (a := (271507958272818327 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy148_hz1 : B (54289 / 250000) (54289 / 250000) (((233 / 500) : ℝ)^2) := bsq (bpoint ((233 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy148_hz2 : B (195711 / 250000) (195711 / 250000) ((1 : ℝ) - (((233 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy148_hz1 (by norm_num) (by norm_num)

theorem lowEnergy148_hz3 : B (176956943915744657 / 200000000000000000) (442392359789361643 / 500000000000000000) (√((1 : ℝ) - (((233 / 500) : ℝ)^2))) := bsqrt lowEnergy148_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy148_hz4 : B (140817861693130277 / 500000000000000000) (56327144677252111 / 200000000000000000) ((√((1 : ℝ) - (((233 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy148_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy148_hz5 : B (38113285520048099 / 125000000000000000) (304906284160602353 / 1000000000000000000) (((233 / 500) : ℝ) * (kdot ((233 / 500)))) := bmul (bpoint ((233 / 500) : ℝ)) lowEnergy148_hz0 (by norm_num) (by norm_num)

theorem lowEnergy148_hz6 : B (293271003773322673 / 500000000000000000) (146635501886715727 / 250000000000000000) (((√((1 : ℝ) - (((233 / 500) : ℝ)^2))) / Real.pi) + (((233 / 500) : ℝ) * (kdot ((233 / 500))))) := badd lowEnergy148_hz4 lowEnergy148_hz5 (by norm_num) (by norm_num)

theorem lowEnergy148_hz7 : B (293271003773322673 / 500000000000000000) (146635501886715727 / 250000000000000000) (kappa ((233 / 500))) := by rw [kappa_eq]; exact lowEnergy148_hz6

theorem lowEnergy148_hz8 : B (175170337058804201 / 250000000000000000) (175170337058804227 / 250000000000000000) (kdot ((29475781017 / 50000000000))) := by
    constructor
    · apply bkdot_lower (q := (25408903389926319 / 50000000000000000)) (a := (117542159683330561 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (508178067798526379 / 1000000000000000000)) (a := (235084319366661041 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy148_hz9 : B (347528666624855021 / 1000000000000000000) (173764333312427511 / 500000000000000000) (((29475781017 / 50000000000) : ℝ)^2) := bsq (bpoint ((29475781017 / 50000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy148_hz10 : B (326235666687572489 / 500000000000000000) (652471333375144979 / 1000000000000000000) ((1 : ℝ) - (((29475781017 / 50000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy148_hz9 (by norm_num) (by norm_num)

theorem lowEnergy148_hz11 : B (201939244169989309 / 250000000000000000) (807756976679957237 / 1000000000000000000) (√((1 : ℝ) - (((29475781017 / 50000000000) : ℝ)^2))) := bsqrt lowEnergy148_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy148_hz12 : B (257117031311160043 / 1000000000000000000) (64279257827790011 / 250000000000000000) ((√((1 : ℝ) - (((29475781017 / 50000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy148_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy148_hz13 : B (206531299832775699 / 500000000000000000) (20653129983277573 / 50000000000000000) (((29475781017 / 50000000000) : ℝ) * (kdot ((29475781017 / 50000000000)))) := bmul (bpoint ((29475781017 / 50000000000) : ℝ)) lowEnergy148_hz8 (by norm_num) (by norm_num)

theorem lowEnergy148_hz14 : B (670179630976711441 / 1000000000000000000) (41886226936044469 / 62500000000000000) (((√((1 : ℝ) - (((29475781017 / 50000000000) : ℝ)^2))) / Real.pi) + (((29475781017 / 50000000000) : ℝ) * (kdot ((29475781017 / 50000000000))))) := badd lowEnergy148_hz12 lowEnergy148_hz13 (by norm_num) (by norm_num)

theorem lowEnergy148_hz15 : B (670179630976711441 / 1000000000000000000) (41886226936044469 / 62500000000000000) (kappa ((29475781017 / 50000000000))) := by rw [kappa_eq]; exact lowEnergy148_hz14

theorem lowEnergy148 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (233 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (168239704203 / 250000000000) := by
  have hk1 : kappa q ≤ (586542007547 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((233 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy148_hz7.2.trans (by norm_num))
  have hk2 : kappa ((29475781017 / 50000000000) : ℝ) ≤ (670179630977 / 1000000000000) := lowEnergy148_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191567058681 / 250000000000) : ℝ)) (R := ((23972945629 / 31250000000) : ℝ)) (Q2 := ((29475781017 / 50000000000) : ℝ)) (T := ((409676982141 / 500000000000) : ℝ))
    (B := ((168239704203 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy149_hz0 : B (81765684714662199 / 125000000000000000) (327062738858889649 / 500000000000000000) (kdot ((931 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (603922129007665877 / 1000000000000000000)) (a := (543298429133608563 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (150980532251916469 / 250000000000000000)) (a := (543298429132851903 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy149_hz1 : B (866761 / 4000000) (866761 / 4000000) (((931 / 2000) : ℝ)^2) := bsq (bpoint ((931 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy149_hz2 : B (3133239 / 4000000) (3133239 / 4000000) ((1 : ℝ) - (((931 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy149_hz1 (by norm_num) (by norm_num)

theorem lowEnergy149_hz3 : B (885047880060734341 / 1000000000000000000) (442523940030367171 / 500000000000000000) (√((1 : ℝ) - (((931 / 2000) : ℝ)^2))) := bsqrt lowEnergy149_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy149_hz4 : B (56343897993867513 / 200000000000000000) (140859744984668783 / 500000000000000000) ((√((1 : ℝ) - (((931 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy149_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy149_hz5 : B (304495409877402029 / 1000000000000000000) (38061926234703283 / 125000000000000000) (((931 / 2000) : ℝ) * (kdot ((931 / 2000)))) := bmul (bpoint ((931 / 2000) : ℝ)) lowEnergy149_hz0 (by norm_num) (by norm_num)

theorem lowEnergy149_hz6 : B (293107449923369797 / 500000000000000000) (58621489984696383 / 100000000000000000) (((√((1 : ℝ) - (((931 / 2000) : ℝ)^2))) / Real.pi) + (((931 / 2000) : ℝ) * (kdot ((931 / 2000))))) := badd lowEnergy149_hz4 lowEnergy149_hz5 (by norm_num) (by norm_num)

theorem lowEnergy149_hz7 : B (293107449923369797 / 500000000000000000) (58621489984696383 / 100000000000000000) (kappa ((931 / 2000))) := by rw [kappa_eq]; exact lowEnergy149_hz6

theorem lowEnergy149_hz8 : B (21892252991038617 / 31250000000000000) (700552095713235851 / 1000000000000000000) (kdot ((589187574941 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (508433554862237859 / 1000000000000000000)) (a := (47037166812007907 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (254216777431118929 / 500000000000000000)) (a := (58796458515009863 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy149_hz9 : B (347141998464856491 / 1000000000000000000) (86785499616214123 / 250000000000000000) (((589187574941 / 1000000000000) : ℝ)^2) := bsq (bpoint ((589187574941 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy149_hz10 : B (163214500383785877 / 250000000000000000) (652858001535143509 / 1000000000000000000) ((1 : ℝ) - (((589187574941 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy149_hz9 (by norm_num) (by norm_num)

theorem lowEnergy149_hz11 : B (807996288070151661 / 1000000000000000000) (807996288070151663 / 1000000000000000000) (√((1 : ℝ) - (((589187574941 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy149_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy149_hz12 : B (51438641298507063 / 200000000000000000) (257193206492535317 / 1000000000000000000) ((√((1 : ℝ) - (((589187574941 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy149_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy149_hz13 : B (412756590393116689 / 1000000000000000000) (412756590393116753 / 1000000000000000000) (((589187574941 / 1000000000000) : ℝ) * (kdot ((589187574941 / 1000000000000)))) := bmul (bpoint ((589187574941 / 1000000000000) : ℝ)) lowEnergy149_hz8 (by norm_num) (by norm_num)

theorem lowEnergy149_hz14 : B (167487449221413001 / 250000000000000000) (66994979688565207 / 100000000000000000) (((√((1 : ℝ) - (((589187574941 / 1000000000000) : ℝ)^2))) / Real.pi) + (((589187574941 / 1000000000000) : ℝ) * (kdot ((589187574941 / 1000000000000))))) := badd lowEnergy149_hz12 lowEnergy149_hz13 (by norm_num) (by norm_num)

theorem lowEnergy149_hz15 : B (167487449221413001 / 250000000000000000) (66994979688565207 / 100000000000000000) (kappa ((589187574941 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy149_hz14

theorem lowEnergy149 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (931 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (336364153591 / 500000000000) := by
  have hk1 : kappa q ≤ (586214899847 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((931 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy149_hz7.2.trans (by norm_num))
  have hk2 : kappa ((589187574941 / 1000000000000) : ℝ) ≤ (334974898443 / 500000000000) := lowEnergy149_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191513690739 / 250000000000) : ℝ)) (R := ((19173019709 / 25000000000) : ℝ)) (Q2 := ((589187574941 / 1000000000000) : ℝ)) (T := ((409606727983 / 500000000000) : ℝ))
    (B := ((336364153591 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy150_hz0 : B (653945678051333057 / 1000000000000000000) (326972839025915031 / 500000000000000000) (kdot ((93 / 200))) := by
    constructor
    · apply bkdot_lower (q := (604307631352261019 / 1000000000000000000)) (a := (108716171557692921 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (302153815676130509 / 500000000000000000)) (a := (67947607223460489 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy150_hz1 : B (8649 / 40000) (8649 / 40000) (((93 / 200) : ℝ)^2) := bsq (bpoint ((93 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy150_hz2 : B (31351 / 40000) (31351 / 40000) ((1 : ℝ) - (((93 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy150_hz1 (by norm_num) (by norm_num)

theorem lowEnergy150_hz3 : B (110663834991382799 / 125000000000000000) (885310679931062393 / 1000000000000000000) (√((1 : ℝ) - (((93 / 200) : ℝ)^2))) := bsqrt lowEnergy150_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy150_hz4 : B (140901570883075401 / 500000000000000000) (281803141766150803 / 1000000000000000000) ((√((1 : ℝ) - (((93 / 200) : ℝ)^2))) / Real.pi) := bdiv lowEnergy150_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy150_hz5 : B (304084740293869871 / 1000000000000000000) (304084740294100979 / 1000000000000000000) (((93 / 200) : ℝ) * (kdot ((93 / 200)))) := bmul (bpoint ((93 / 200) : ℝ)) lowEnergy150_hz0 (by norm_num) (by norm_num)

theorem lowEnergy150_hz6 : B (585887882060020673 / 1000000000000000000) (292943941030125891 / 500000000000000000) (((√((1 : ℝ) - (((93 / 200) : ℝ)^2))) / Real.pi) + (((93 / 200) : ℝ) * (kdot ((93 / 200))))) := badd lowEnergy150_hz4 lowEnergy150_hz5 (by norm_num) (by norm_num)

theorem lowEnergy150_hz7 : B (585887882060020673 / 1000000000000000000) (292943941030125891 / 500000000000000000) (kappa ((93 / 200))) := by rw [kappa_eq]; exact lowEnergy150_hz6

theorem lowEnergy150_hz8 : B (700422916922900511 / 1000000000000000000) (35021145846145031 / 50000000000000000) (kdot ((58885961961 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (254344474445432787 / 500000000000000000)) (a := (235287290844718731 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (508688948890865573 / 1000000000000000000)) (a := (117643645422359323 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy150_hz9 : B (43344456450904237 / 125000000000000000) (346755651607233897 / 1000000000000000000) (((58885961961 / 100000000000) : ℝ)^2) := bsq (bpoint ((58885961961 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy150_hz10 : B (653244348392766103 / 1000000000000000000) (81655543549095763 / 125000000000000000) ((1 : ℝ) - (((58885961961 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy150_hz9 (by norm_num) (by norm_num)

theorem lowEnergy150_hz11 : B (404117664917275703 / 500000000000000000) (50514708114659463 / 62500000000000000) (√((1 : ℝ) - (((58885961961 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy150_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy150_hz12 : B (25726929584935457 / 100000000000000000) (64317323962338643 / 250000000000000000) ((√((1 : ℝ) - (((58885961961 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy150_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy150_hz13 : B (206225386212672913 / 500000000000000000) (412450772425345891 / 1000000000000000000) (((58885961961 / 100000000000) : ℝ) * (kdot ((58885961961 / 100000000000)))) := bmul (bpoint ((58885961961 / 100000000000) : ℝ)) lowEnergy150_hz8 (by norm_num) (by norm_num)

theorem lowEnergy150_hz14 : B (167430017068675099 / 250000000000000000) (669720068274700463 / 1000000000000000000) (((√((1 : ℝ) - (((58885961961 / 100000000000) : ℝ)^2))) / Real.pi) + (((58885961961 / 100000000000) : ℝ) * (kdot ((58885961961 / 100000000000))))) := badd lowEnergy150_hz12 lowEnergy150_hz13 (by norm_num) (by norm_num)

theorem lowEnergy150_hz15 : B (167430017068675099 / 250000000000000000) (669720068274700463 / 1000000000000000000) (kappa ((58885961961 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy150_hz14

theorem lowEnergy150 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (93 / 200)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (10507779739 / 15625000000) := by
  have hk1 : kappa q ≤ (585887882061 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((93 / 200) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy150_hz7.2.trans (by norm_num))
  have hk2 : kappa ((58885961961 / 100000000000) : ℝ) ≤ (26788802731 / 40000000000) := lowEnergy150_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((765841290387 / 1000000000000) : ℝ)) (R := ((766707315791 / 1000000000000) : ℝ)) (Q2 := ((58885961961 / 100000000000) : ℝ)) (T := ((819072988049 / 1000000000000) : ℝ))
    (B := ((10507779739 / 15625000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy151_hz0 : B (326882965856735441 / 500000000000000000) (40860370732123979 / 62500000000000000) (kdot ((929 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (151173287728021403 / 250000000000000000)) (a := (16995725083616667 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (604693150912085611 / 1000000000000000000)) (a := (543863202674927869 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy151_hz1 : B (863041 / 4000000) (863041 / 4000000) (((929 / 2000) : ℝ)^2) := bsq (bpoint ((929 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy151_hz2 : B (3136959 / 4000000) (3136959 / 4000000) ((1 : ℝ) - (((929 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy151_hz1 (by norm_num) (by norm_num)

theorem lowEnergy151_hz3 : B (885573119510749377 / 1000000000000000000) (442786559755374689 / 500000000000000000) (√((1 : ℝ) - (((929 / 2000) : ℝ)^2))) := bsqrt lowEnergy151_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy151_hz4 : B (17617917429930693 / 62500000000000000) (281886678878891089 / 1000000000000000000) ((√((1 : ℝ) - (((929 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy151_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy151_hz5 : B (37959284410113403 / 125000000000000000) (75918568820286353 / 250000000000000000) (((929 / 2000) : ℝ) * (kdot ((929 / 2000)))) := bmul (bpoint ((929 / 2000) : ℝ)) lowEnergy151_hz0 (by norm_num) (by norm_num)

theorem lowEnergy151_hz6 : B (73195119269974789 / 125000000000000000) (585560954160036501 / 1000000000000000000) (((√((1 : ℝ) - (((929 / 2000) : ℝ)^2))) / Real.pi) + (((929 / 2000) : ℝ) * (kdot ((929 / 2000))))) := badd lowEnergy151_hz4 lowEnergy151_hz5 (by norm_num) (by norm_num)

theorem lowEnergy151_hz7 : B (73195119269974789 / 125000000000000000) (585560954160036501 / 1000000000000000000) (kappa ((929 / 2000))) := by rw [kappa_eq]; exact lowEnergy151_hz6

theorem lowEnergy151_hz8 : B (700293811766520499 / 1000000000000000000) (700293811766520611 / 1000000000000000000) (kdot ((588531754319 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (254472125012351023 / 500000000000000000)) (a := (235388689797424733 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (101788850004940409 / 200000000000000000)) (a := (470777379594849291 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy151_hz9 : B (13854785033671991 / 40000000000000000) (10824050807556243 / 31250000000000000) (((588531754319 / 1000000000000) : ℝ)^2) := bsq (bpoint ((588531754319 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy151_hz10 : B (20425949192443757 / 31250000000000000) (26145214966328009 / 40000000000000000) ((1 : ℝ) - (((588531754319 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy151_hz9 (by norm_num) (by norm_num)

theorem lowEnergy151_hz11 : B (808474102342307699 / 1000000000000000000) (808474102342307701 / 1000000000000000000) (√((1 : ℝ) - (((588531754319 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy151_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy151_hz12 : B (128672649749561147 / 500000000000000000) (32168162437390287 / 125000000000000000) ((√((1 : ℝ) - (((588531754319 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy151_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy151_hz13 : B (412145145577689873 / 1000000000000000000) (20607257278884497 / 50000000000000000) (((588531754319 / 1000000000000) : ℝ) * (kdot ((588531754319 / 1000000000000)))) := bmul (bpoint ((588531754319 / 1000000000000) : ℝ)) lowEnergy151_hz8 (by norm_num) (by norm_num)

theorem lowEnergy151_hz14 : B (669490445076812167 / 1000000000000000000) (167372611269203059 / 250000000000000000) (((√((1 : ℝ) - (((588531754319 / 1000000000000) : ℝ)^2))) / Real.pi) + (((588531754319 / 1000000000000) : ℝ) * (kdot ((588531754319 / 1000000000000))))) := badd lowEnergy151_hz12 lowEnergy151_hz13 (by norm_num) (by norm_num)

theorem lowEnergy151_hz15 : B (669490445076812167 / 1000000000000000000) (167372611269203059 / 250000000000000000) (kappa ((588531754319 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy151_hz14

theorem lowEnergy151 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (929 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (134453521017 / 200000000000) := by
  have hk1 : kappa q ≤ (585560954161 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((929 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy151_hz7.2.trans (by norm_num))
  have hk2 : kappa ((588531754319 / 1000000000000) : ℝ) ≤ (669490445077 / 1000000000000) := lowEnergy151_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((382813908499 / 500000000000) : ℝ)) (R := ((383246921201 / 500000000000) : ℝ)) (Q2 := ((588531754319 / 1000000000000) : ℝ)) (T := ((818932560509 / 1000000000000) : ℝ))
    (B := ((134453521017 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy152_hz0 : B (653586238599022661 / 1000000000000000000) (653586238599551711 / 1000000000000000000) (kdot ((58 / 125))) := by
    constructor
    · apply bkdot_lower (q := (37817417995219301 / 62500000000000000)) (a := (2125568218593199 / 3906250000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (121015737584701763 / 200000000000000000)) (a := (136036365989756979 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy152_hz1 : B (3364 / 15625) (3364 / 15625) (((58 / 125) : ℝ)^2) := bsq (bpoint ((58 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy152_hz2 : B (12261 / 15625) (12261 / 15625) ((1 : ℝ) - (((58 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy152_hz1 (by norm_num) (by norm_num)

theorem lowEnergy152_hz3 : B (177167039824003381 / 200000000000000000) (442917599560008453 / 500000000000000000) (√((1 : ℝ) - (((58 / 125) : ℝ)^2))) := bsqrt lowEnergy152_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy152_hz4 : B (281970101409488127 / 1000000000000000000) (1101445708630813 / 3906250000000000) ((√((1 : ℝ) - (((58 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy152_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy152_hz5 : B (151632007354973257 / 500000000000000000) (151632007355095997 / 500000000000000000) (((58 / 125) : ℝ) * (kdot ((58 / 125)))) := bmul (bpoint ((58 / 125) : ℝ)) lowEnergy152_hz0 (by norm_num) (by norm_num)

theorem lowEnergy152_hz6 : B (585234116119434641 / 1000000000000000000) (292617058059840061 / 500000000000000000) (((√((1 : ℝ) - (((58 / 125) : ℝ)^2))) / Real.pi) + (((58 / 125) : ℝ) * (kdot ((58 / 125))))) := badd lowEnergy152_hz4 lowEnergy152_hz5 (by norm_num) (by norm_num)

theorem lowEnergy152_hz7 : B (585234116119434641 / 1000000000000000000) (292617058059840061 / 500000000000000000) (kappa ((58 / 125))) := by rw [kappa_eq]; exact lowEnergy152_hz6

theorem lowEnergy152_hz8 : B (700164780147804949 / 1000000000000000000) (87520597518475633 / 125000000000000000) (kdot ((588203979043 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (509199458401378019 / 1000000000000000000)) (a := (470980061987568251 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (254599729200689009 / 500000000000000000)) (a := (58872507748446009 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy152_hz9 : B (345983920962017983 / 1000000000000000000) (5405998765031531 / 15625000000000000) (((588203979043 / 1000000000000) : ℝ)^2) := bsq (bpoint ((588203979043 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy152_hz10 : B (10219001234968469 / 15625000000000000) (654016079037982017 / 1000000000000000000) ((1 : ℝ) - (((588203979043 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy152_hz9 (by norm_num) (by norm_num)

theorem lowEnergy152_hz11 : B (202178151489902281 / 250000000000000000) (404356302979804563 / 500000000000000000) (√((1 : ℝ) - (((588203979043 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy152_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy152_hz12 : B (257421217558399933 / 1000000000000000000) (51484243511679987 / 200000000000000000) ((√((1 : ℝ) - (((588203979043 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy152_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy152_hz13 : B (102959927417176541 / 250000000000000000) (411839709668706233 / 1000000000000000000) (((588203979043 / 1000000000000) : ℝ) * (kdot ((588203979043 / 1000000000000)))) := bmul (bpoint ((588203979043 / 1000000000000) : ℝ)) lowEnergy152_hz8 (by norm_num) (by norm_num)

theorem lowEnergy152_hz14 : B (669260927227106097 / 1000000000000000000) (83657615903388271 / 125000000000000000) (((√((1 : ℝ) - (((588203979043 / 1000000000000) : ℝ)^2))) / Real.pi) + (((588203979043 / 1000000000000) : ℝ) * (kdot ((588203979043 / 1000000000000))))) := badd lowEnergy152_hz12 lowEnergy152_hz13 (by norm_num) (by norm_num)

theorem lowEnergy152_hz15 : B (669260927227106097 / 1000000000000000000) (83657615903388271 / 125000000000000000) (kappa ((588203979043 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy152_hz14

theorem lowEnergy152 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (58 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (336018706243 / 500000000000) := by
  have hk1 : kappa q ≤ (14630852903 / 25000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((58 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy152_hz7.2.trans (by norm_num))
  have hk2 : kappa ((588203979043 / 1000000000000) : ℝ) ≤ (167315231807 / 250000000000) := lowEnergy152_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191353585693 / 250000000000) : ℝ)) (R := ((47892523011 / 62500000000) : ℝ)) (Q2 := ((588203979043 / 1000000000000) : ℝ)) (T := ((818792173329 / 1000000000000) : ℝ))
    (B := ((336018706243 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy153_hz0 : B (653406598603522703 / 1000000000000000000) (653406598604068527 / 1000000000000000000) (kdot ((927 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (605464242622664007 / 1000000000000000000)) (a := (544427641804935729 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (302732121311332003 / 500000000000000000)) (a := (544427641804078353 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy153_hz1 : B (859329 / 4000000) (859329 / 4000000) (((927 / 2000) : ℝ)^2) := bsq (bpoint ((927 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy153_hz2 : B (3140671 / 4000000) (3140671 / 4000000) ((1 : ℝ) - (((927 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy153_hz1 (by norm_num) (by norm_num)

theorem lowEnergy153_hz3 : B (443048459539134387 / 500000000000000000) (35443876763130751 / 40000000000000000) (√((1 : ℝ) - (((927 / 2000) : ℝ)^2))) := bsqrt lowEnergy153_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy153_hz4 : B (141026704729805653 / 500000000000000000) (282053409459611307 / 1000000000000000000) ((√((1 : ℝ) - (((927 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy153_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy153_hz5 : B (75713489613183193 / 250000000000000000) (302853958452985763 / 1000000000000000000) (((927 / 2000) : ℝ) * (kdot ((927 / 2000)))) := bmul (bpoint ((927 / 2000) : ℝ)) lowEnergy153_hz0 (by norm_num) (by norm_num)

theorem lowEnergy153_hz6 : B (292453683956172039 / 500000000000000000) (58490736791259707 / 100000000000000000) (((√((1 : ℝ) - (((927 / 2000) : ℝ)^2))) / Real.pi) + (((927 / 2000) : ℝ) * (kdot ((927 / 2000))))) := badd lowEnergy153_hz4 lowEnergy153_hz5 (by norm_num) (by norm_num)

theorem lowEnergy153_hz7 : B (292453683956172039 / 500000000000000000) (58490736791259707 / 100000000000000000) (kappa ((927 / 2000))) := by rw [kappa_eq]; exact lowEnergy153_hz6

theorem lowEnergy153_hz8 : B (87504477746187449 / 125000000000000000) (70003582196949971 / 100000000000000000) (kdot ((293938146877 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (509454574160535601 / 1000000000000000000)) (a := (471182629020360467 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1273636435401339 / 2500000000000000)) (a := (117795657255090071 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy153_hz9 : B (345598536757939299 / 1000000000000000000) (3455985367579393 / 10000000000000000) (((293938146877 / 500000000000) : ℝ)^2) := bsq (bpoint ((293938146877 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy153_hz10 : B (6544014632420607 / 10000000000000000) (654401463242060701 / 1000000000000000000) ((1 : ℝ) - (((293938146877 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy153_hz9 (by norm_num) (by norm_num)

theorem lowEnergy153_hz11 : B (161790168210810721 / 200000000000000000) (404475420527026803 / 500000000000000000) (√((1 : ℝ) - (((293938146877 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy153_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy153_hz12 : B (257497050144197541 / 1000000000000000000) (128748525072098771 / 500000000000000000) ((√((1 : ℝ) - (((293938146877 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy153_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy153_hz13 : B (102883616128616097 / 250000000000000000) (411534464514464459 / 1000000000000000000) (((293938146877 / 500000000000) : ℝ) * (kdot ((293938146877 / 500000000000)))) := bmul (bpoint ((293938146877 / 500000000000) : ℝ)) lowEnergy153_hz8 (by norm_num) (by norm_num)

theorem lowEnergy153_hz14 : B (669031514658661929 / 1000000000000000000) (669031514658662001 / 1000000000000000000) (((√((1 : ℝ) - (((293938146877 / 500000000000) : ℝ)^2))) / Real.pi) + (((293938146877 / 500000000000) : ℝ) * (kdot ((293938146877 / 500000000000))))) := badd lowEnergy153_hz12 lowEnergy153_hz13 (by norm_num) (by norm_num)

theorem lowEnergy153_hz15 : B (669031514658661929 / 1000000000000000000) (669031514658662001 / 1000000000000000000) (kappa ((293938146877 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy153_hz14

theorem lowEnergy153 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (927 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (167951831357 / 250000000000) := by
  have hk1 : kappa q ≤ (584907367913 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((927 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy153_hz7.2.trans (by norm_num))
  have hk2 : kappa ((293938146877 / 500000000000) : ℝ) ≤ (669031514659 / 1000000000000) := lowEnergy153_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((76520086769 / 100000000000) : ℝ)) (R := ((383033446547 / 500000000000) : ℝ)) (Q2 := ((293938146877 / 500000000000) : ℝ)) (T := ((409325913243 / 500000000000) : ℝ))
    (B := ((167951831357 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy154_hz0 : B (26129080464909091 / 40000000000000000) (653227011623290393 / 1000000000000000000) (kdot ((463 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (121169963049090017 / 200000000000000000)) (a := (272354868187354687 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (151462453811362521 / 250000000000000000)) (a := (8511089630841013 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy154_hz1 : B (214369 / 1000000) (214369 / 1000000) (((463 / 1000) : ℝ)^2) := bsq (bpoint ((463 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy154_hz2 : B (785631 / 1000000) (785631 / 1000000) ((1 : ℝ) - (((463 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy154_hz1 (by norm_num) (by norm_num)

theorem lowEnergy154_hz3 : B (886358279704093473 / 1000000000000000000) (443179139852046737 / 500000000000000000) (√((1 : ℝ) - (((463 / 1000) : ℝ)^2))) := bsqrt lowEnergy154_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy154_hz4 : B (28213660313067049 / 100000000000000000) (282136603130670491 / 1000000000000000000) ((√((1 : ℝ) - (((463 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy154_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy154_hz5 : B (37805513297665341 / 125000000000000000) (75611026595395863 / 250000000000000000) (((463 / 1000) : ℝ) * (kdot ((463 / 1000)))) := bmul (bpoint ((463 / 1000) : ℝ)) lowEnergy154_hz0 (by norm_num) (by norm_num)

theorem lowEnergy154_hz6 : B (292290354755996609 / 500000000000000000) (584580709512253943 / 1000000000000000000) (((√((1 : ℝ) - (((463 / 1000) : ℝ)^2))) / Real.pi) + (((463 / 1000) : ℝ) * (kdot ((463 / 1000))))) := badd lowEnergy154_hz4 lowEnergy154_hz5 (by norm_num) (by norm_num)

theorem lowEnergy154_hz7 : B (292290354755996609 / 500000000000000000) (584580709512253943 / 1000000000000000000) (kappa ((463 / 1000))) := by rw [kappa_eq]; exact lowEnergy154_hz6

theorem lowEnergy154_hz8 : B (699906937135747893 / 1000000000000000000) (349953468567874007 / 500000000000000000) (kdot ((587548698427 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (509709597439157693 / 1000000000000000000)) (a := (471385080843797207 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (127427399359789423 / 250000000000000000)) (a := (471385080843797019 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy154_hz9 : B (10787921031976931 / 31250000000000000) (345213473023261793 / 1000000000000000000) (((587548698427 / 1000000000000) : ℝ)^2) := bsq (bpoint ((587548698427 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy154_hz10 : B (654786526976738207 / 1000000000000000000) (20462078968023069 / 31250000000000000) ((1 : ℝ) - (((587548698427 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy154_hz9 (by norm_num) (by norm_num)

theorem lowEnergy154_hz11 : B (404594403995142463 / 500000000000000000) (6321787562424101 / 7812500000000000) (√((1 : ℝ) - (((587548698427 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy154_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy154_hz12 : B (128786398686292419 / 500000000000000000) (257572797372584839 / 1000000000000000000) ((√((1 : ℝ) - (((587548698427 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy154_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy154_hz13 : B (82245881986827357 / 200000000000000000) (205614704967068429 / 500000000000000000) (((587548698427 / 1000000000000) : ℝ) * (kdot ((587548698427 / 1000000000000)))) := bmul (bpoint ((587548698427 / 1000000000000) : ℝ)) lowEnergy154_hz8 (by norm_num) (by norm_num)

theorem lowEnergy154_hz14 : B (668802207306721623 / 1000000000000000000) (668802207306721697 / 1000000000000000000) (((√((1 : ℝ) - (((587548698427 / 1000000000000) : ℝ)^2))) / Real.pi) + (((587548698427 / 1000000000000) : ℝ) * (kdot ((587548698427 / 1000000000000))))) := badd lowEnergy154_hz12 lowEnergy154_hz13 (by norm_num) (by norm_num)

theorem lowEnergy154_hz15 : B (668802207306721623 / 1000000000000000000) (668802207306721697 / 1000000000000000000) (kappa ((587548698427 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy154_hz14

theorem lowEnergy154 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (463 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (13431546877 / 20000000000) := by
  have hk1 : kappa q ≤ (584580709513 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((463 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy154_hz7.2.trans (by norm_num))
  have hk2 : kappa ((587548698427 / 1000000000000) : ℝ) ≤ (668802207307 / 1000000000000) := lowEnergy154_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((152997478347 / 200000000000) : ℝ)) (R := ((765853417139 / 1000000000000) : ℝ)) (Q2 := ((587548698427 / 1000000000000) : ℝ)) (T := ((204627879991 / 250000000000) : ℝ))
    (B := ((13431546877 / 20000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy155_hz0 : B (326523738776306921 / 500000000000000000) (81630934694149349 / 125000000000000000) (kdot ((37 / 80))) := by
    constructor
    · apply bkdot_lower (q := (24249416241101311 / 40000000000000000)) (a := (136247936958144523 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (303117703013766387 / 500000000000000000)) (a := (544991747831665539 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy155_hz1 : B (1369 / 6400) (1369 / 6400) (((37 / 80) : ℝ)^2) := bsq (bpoint ((37 / 80) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy155_hz2 : B (5031 / 6400) (5031 / 6400) ((1 : ℝ) - (((37 / 80) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy155_hz1 (by norm_num) (by norm_num)

theorem lowEnergy155_hz3 : B (443309640657633341 / 500000000000000000) (886619281315266683 / 1000000000000000000) (√((1 : ℝ) - (((37 / 80) : ℝ)^2))) := bsqrt lowEnergy155_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy155_hz4 : B (14110984126190841 / 50000000000000000) (141109841261908411 / 500000000000000000) ((√((1 : ℝ) - (((37 / 80) : ℝ)^2))) / Real.pi) := bdiv lowEnergy155_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy155_hz5 : B (302034458368083901 / 1000000000000000000) (18877153648022037 / 62500000000000000) (((37 / 80) : ℝ) * (kdot ((37 / 80)))) := bmul (bpoint ((37 / 80) : ℝ)) lowEnergy155_hz0 (by norm_num) (by norm_num)

theorem lowEnergy155_hz6 : B (584254140891900721 / 1000000000000000000) (292127070446084707 / 500000000000000000) (((√((1 : ℝ) - (((37 / 80) : ℝ)^2))) / Real.pi) + (((37 / 80) : ℝ) * (kdot ((37 / 80))))) := badd lowEnergy155_hz4 lowEnergy155_hz5 (by norm_num) (by norm_num)

theorem lowEnergy155_hz7 : B (584254140891900721 / 1000000000000000000) (292127070446084707 / 500000000000000000) (kappa ((37 / 80))) := by rw [kappa_eq]; exact lowEnergy155_hz6

theorem lowEnergy155_hz8 : B (4373613284683349 / 6250000000000000) (174944531387333991 / 250000000000000000) (kdot ((587221193033 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (509964528377018661 / 1000000000000000000)) (a := (471587417610581883 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (25498226418850933 / 50000000000000000)) (a := (47158741761058169 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy155_hz9 : B (344828729547099847 / 1000000000000000000) (43103591193387481 / 125000000000000000) (((587221193033 / 1000000000000) : ℝ)^2) := bsq (bpoint ((587221193033 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy155_hz10 : B (81896408806612519 / 125000000000000000) (655171270452900153 / 1000000000000000000) ((1 : ℝ) - (((587221193033 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy155_hz9 (by norm_num) (by norm_num)

theorem lowEnergy155_hz11 : B (809426507135082741 / 1000000000000000000) (404713253567541371 / 500000000000000000) (√((1 : ℝ) - (((587221193033 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy155_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy155_hz12 : B (51529691872062283 / 200000000000000000) (32206057420038927 / 125000000000000000) ((√((1 : ℝ) - (((587221193033 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy155_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy155_hz13 : B (8218490914869549 / 20000000000000000) (102731136435869381 / 250000000000000000) (((587221193033 / 1000000000000) : ℝ) * (kdot ((587221193033 / 1000000000000)))) := bmul (bpoint ((587221193033 / 1000000000000) : ℝ)) lowEnergy155_hz8 (by norm_num) (by norm_num)

theorem lowEnergy155_hz14 : B (133714601020757773 / 200000000000000000) (33428650255189447 / 50000000000000000) (((√((1 : ℝ) - (((587221193033 / 1000000000000) : ℝ)^2))) / Real.pi) + (((587221193033 / 1000000000000) : ℝ) * (kdot ((587221193033 / 1000000000000))))) := badd lowEnergy155_hz12 lowEnergy155_hz13 (by norm_num) (by norm_num)

theorem lowEnergy155_hz15 : B (133714601020757773 / 200000000000000000) (33428650255189447 / 50000000000000000) (kappa ((587221193033 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy155_hz14

theorem lowEnergy155 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (37 / 80)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (671347467681 / 1000000000000) := by
  have hk1 : kappa q ≤ (584254140893 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((37 / 80) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy155_hz7.2.trans (by norm_num))
  have hk2 : kappa ((587221193033 / 1000000000000) : ℝ) ≤ (41785812819 / 62500000000) := lowEnergy155_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((95596739361 / 125000000000) : ℝ)) (R := ((191409985073 / 250000000000) : ℝ)) (Q2 := ((587221193033 / 1000000000000) : ℝ)) (T := ((40918562687 / 50000000000) : ℝ))
    (B := ((671347467681 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy156_hz0 : B (652867996289380317 / 1000000000000000000) (326433998144989827 / 500000000000000000) (kdot ((231 / 500))) := by
    constructor
    · apply bkdot_lower (q := (606621015204345933 / 1000000000000000000)) (a := (27263683817079691 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (151655253801086483 / 250000000000000000)) (a := (272636838170326193 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy156_hz1 : B (53361 / 250000) (53361 / 250000) (((231 / 500) : ℝ)^2) := bsq (bpoint ((231 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy156_hz2 : B (196639 / 250000) (196639 / 250000) ((1 : ℝ) - (((231 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy156_hz1 (by norm_num) (by norm_num)

theorem lowEnergy156_hz3 : B (443439962114376877 / 500000000000000000) (177375984845750751 / 200000000000000000) (√((1 : ℝ) - (((231 / 500) : ℝ)^2))) := bsqrt lowEnergy156_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy156_hz4 : B (141151323869971751 / 500000000000000000) (282302647739943503 / 1000000000000000000) ((√((1 : ℝ) - (((231 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy156_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy156_hz5 : B (150812507142846853 / 500000000000000000) (301625014285970601 / 1000000000000000000) (((231 / 500) : ℝ) * (kdot ((231 / 500)))) := bmul (bpoint ((231 / 500) : ℝ)) lowEnergy156_hz0 (by norm_num) (by norm_num)

theorem lowEnergy156_hz6 : B (72990957753204651 / 125000000000000000) (72990957753239263 / 125000000000000000) (((√((1 : ℝ) - (((231 / 500) : ℝ)^2))) / Real.pi) + (((231 / 500) : ℝ) * (kdot ((231 / 500))))) := badd lowEnergy156_hz4 lowEnergy156_hz5 (by norm_num) (by norm_num)

theorem lowEnergy156_hz7 : B (72990957753204651 / 125000000000000000) (72990957753239263 / 125000000000000000) (kappa ((231 / 500))) := by rw [kappa_eq]; exact lowEnergy156_hz6

theorem lowEnergy156_hz8 : B (699649387115231799 / 1000000000000000000) (349824693557615963 / 500000000000000000) (kdot ((146723444387 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (510219367109679339 / 1000000000000000000)) (a := (471789639469989837 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (255109683554839669 / 500000000000000000)) (a := (11794740986749741 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy156_hz9 : B (86111076531140327 / 250000000000000000) (344444306124561309 / 1000000000000000000) (((146723444387 / 250000000000) : ℝ)^2) := bsq (bpoint ((146723444387 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy156_hz10 : B (655555693875438691 / 1000000000000000000) (163888923468859673 / 250000000000000000) ((1 : ℝ) - (((146723444387 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy156_hz9 (by norm_num) (by norm_num)

theorem lowEnergy156_hz11 : B (25301998089088401 / 31250000000000000) (404831969425414417 / 500000000000000000) (√((1 : ℝ) - (((146723444387 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy156_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy156_hz12 : B (10308961448909079 / 40000000000000000) (257724036222726977 / 1000000000000000000) ((√((1 : ℝ) - (((146723444387 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy156_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy156_hz13 : B (102654967940800347 / 250000000000000000) (51327483970400183 / 125000000000000000) (((146723444387 / 250000000000) : ℝ) * (kdot ((146723444387 / 250000000000)))) := bmul (bpoint ((146723444387 / 250000000000) : ℝ)) lowEnergy156_hz8 (by norm_num) (by norm_num)

theorem lowEnergy156_hz14 : B (668343907985928363 / 1000000000000000000) (668343907985928441 / 1000000000000000000) (((√((1 : ℝ) - (((146723444387 / 250000000000) : ℝ)^2))) / Real.pi) + (((146723444387 / 250000000000) : ℝ) * (kdot ((146723444387 / 250000000000))))) := badd lowEnergy156_hz12 lowEnergy156_hz13 (by norm_num) (by norm_num)

theorem lowEnergy156_hz15 : B (668343907985928363 / 1000000000000000000) (668343907985928441 / 1000000000000000000) (kappa ((146723444387 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy156_hz14

theorem lowEnergy156 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (231 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (33555884843 / 50000000000) := by
  have hk1 : kappa q ≤ (291963831013 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((231 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy156_hz7.2.trans (by norm_num))
  have hk2 : kappa ((146723444387 / 250000000000) : ℝ) ≤ (334171953993 / 500000000000) := lowEnergy156_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((191140109283 / 250000000000) : ℝ)) (R := ((95678307817 / 125000000000) : ℝ)) (Q2 := ((146723444387 / 250000000000) : ℝ)) (T := ((409115513899 / 500000000000) : ℝ))
    (B := ((33555884843 / 50000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy157_hz0 : B (163172141932361077 / 250000000000000000) (652688567730062601 / 1000000000000000000) (kdot ((923 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (607006643011092841 / 1000000000000000000)) (a := (545555522064463401 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (15175166075277321 / 25000000000000000)) (a := (545555522063492191 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy157_hz1 : B (851929 / 4000000) (851929 / 4000000) (((923 / 2000) : ℝ)^2) := bsq (bpoint ((923 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy157_hz2 : B (3148071 / 4000000) (3148071 / 4000000) ((1 : ℝ) - (((923 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy157_hz1 (by norm_num) (by norm_num)

theorem lowEnergy157_hz3 : B (443570104380356093 / 500000000000000000) (887140208760712187 / 1000000000000000000) (√((1 : ℝ) - (((923 / 2000) : ℝ)^2))) := bsqrt lowEnergy157_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy157_hz4 : B (282385498879686591 / 1000000000000000000) (282385498879686593 / 1000000000000000000) ((√((1 : ℝ) - (((923 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy157_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy157_hz5 : B (75303943501784637 / 250000000000000000) (301215774007423891 / 1000000000000000000) (((923 / 2000) : ℝ) * (kdot ((923 / 2000)))) := bmul (bpoint ((923 / 2000) : ℝ)) lowEnergy157_hz0 (by norm_num) (by norm_num)

theorem lowEnergy157_hz6 : B (583601272886825139 / 1000000000000000000) (145900318221777621 / 250000000000000000) (((√((1 : ℝ) - (((923 / 2000) : ℝ)^2))) / Real.pi) + (((923 / 2000) : ℝ) * (kdot ((923 / 2000))))) := badd lowEnergy157_hz4 lowEnergy157_hz5 (by norm_num) (by norm_num)

theorem lowEnergy157_hz7 : B (583601272886825139 / 1000000000000000000) (145900318221777621 / 250000000000000000) (kappa ((923 / 2000))) := by rw [kappa_eq]; exact lowEnergy157_hz6

theorem lowEnergy157_hz8 : B (349760360868522861 / 500000000000000000) (699520721737045851 / 1000000000000000000) (kdot ((73320806493 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (127618528443873471 / 250000000000000000)) (a := (117997936643357551 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (510474113775493883 / 1000000000000000000)) (a := (235995873286715001 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy157_hz9 : B (344060202546172861 / 1000000000000000000) (172030101273086431 / 500000000000000000) (((73320806493 / 125000000000) : ℝ)^2) := bsq (bpoint ((73320806493 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy157_hz10 : B (327969898726913569 / 500000000000000000) (655939797453827139 / 1000000000000000000) ((1 : ℝ) - (((73320806493 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy157_hz9 (by norm_num) (by norm_num)

theorem lowEnergy157_hz11 : B (25309409484438847 / 31250000000000000) (404950551751021553 / 500000000000000000) (√((1 : ℝ) - (((73320806493 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy157_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy157_hz12 : B (16112470504741363 / 62500000000000000) (25779952807586181 / 100000000000000000) ((√((1 : ℝ) - (((73320806493 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy157_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy157_hz13 : B (16412615512424201 / 40000000000000000) (205157693905302551 / 500000000000000000) (((73320806493 / 125000000000) : ℝ) * (kdot ((73320806493 / 125000000000)))) := bmul (bpoint ((73320806493 / 125000000000) : ℝ)) lowEnergy157_hz8 (by norm_num) (by norm_num)

theorem lowEnergy157_hz14 : B (668114915886466833 / 1000000000000000000) (20878591121452091 / 31250000000000000) (((√((1 : ℝ) - (((73320806493 / 125000000000) : ℝ)^2))) / Real.pi) + (((73320806493 / 125000000000) : ℝ) * (kdot ((73320806493 / 125000000000))))) := badd lowEnergy157_hz12 lowEnergy157_hz13 (by norm_num) (by norm_num)

theorem lowEnergy157_hz15 : B (668114915886466833 / 1000000000000000000) (20878591121452091 / 31250000000000000) (kappa ((73320806493 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy157_hz14

theorem lowEnergy157 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (923 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (670888031319 / 1000000000000) := by
  have hk1 : kappa q ≤ (72950159111 / 125000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((923 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy157_hz7.2.trans (by norm_num))
  have hk2 : kappa ((73320806493 / 125000000000) : ℝ) ≤ (668114915887 / 1000000000000) := lowEnergy157_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((47771684903 / 62500000000) : ℝ)) (R := ((191303245963 / 250000000000) : ℝ)) (Q2 := ((73320806493 / 125000000000) : ℝ)) (T := ((204522710529 / 250000000000) : ℝ))
    (B := ((670888031319 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy158_hz0 : B (65250919176944237 / 100000000000000000) (652509191770080207 / 1000000000000000000) (kdot ((461 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (75924036210343437 / 125000000000000000)) (a := (272918642581774877 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (121478457936549499 / 200000000000000000)) (a := (545837285162547843 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy158_hz1 : B (212521 / 1000000) (212521 / 1000000) (((461 / 1000) : ℝ)^2) := bsq (bpoint ((461 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy158_hz2 : B (787479 / 1000000) (787479 / 1000000) ((1 : ℝ) - (((461 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy158_hz1 (by norm_num) (by norm_num)

theorem lowEnergy158_hz3 : B (887400135226494091 / 1000000000000000000) (221850033806623523 / 250000000000000000) (√((1 : ℝ) - (((461 / 1000) : ℝ)^2))) := bsqrt lowEnergy158_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy158_hz4 : B (56493647208685157 / 200000000000000000) (141234118021712893 / 500000000000000000) ((√((1 : ℝ) - (((461 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy158_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy158_hz5 : B (75201684351428233 / 250000000000000000) (4700105271968859 / 15625000000000000) (((461 / 1000) : ℝ) * (kdot ((461 / 1000)))) := bmul (bpoint ((461 / 1000) : ℝ)) lowEnergy158_hz0 (by norm_num) (by norm_num)

theorem lowEnergy158_hz6 : B (583274973449138717 / 1000000000000000000) (291637486724716381 / 500000000000000000) (((√((1 : ℝ) - (((461 / 1000) : ℝ)^2))) / Real.pi) + (((461 / 1000) : ℝ) * (kdot ((461 / 1000))))) := badd lowEnergy158_hz4 lowEnergy158_hz5 (by norm_num) (by norm_num)

theorem lowEnergy158_hz7 : B (583274973449138717 / 1000000000000000000) (291637486724716381 / 500000000000000000) (kappa ((461 / 1000))) := by rw [kappa_eq]; exact lowEnergy158_hz6

theorem lowEnergy158_hz8 : B (699392129318995299 / 1000000000000000000) (87424016164874429 / 125000000000000000) (kdot ((293119608097 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (10214575370234373 / 20000000000000000)) (a := (236096869535678741 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (510728768511718649 / 1000000000000000000)) (a := (18887749562854291 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy158_hz9 : B (343676418603755471 / 1000000000000000000) (21479776162734717 / 62500000000000000) (((293119608097 / 500000000000) : ℝ)^2) := bsq (bpoint ((293119608097 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy158_hz10 : B (41020223837265283 / 62500000000000000) (656323581396244529 / 1000000000000000000) ((1 : ℝ) - (((293119608097 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy158_hz9 (by norm_num) (by norm_num)

theorem lowEnergy158_hz11 : B (810138001451755457 / 1000000000000000000) (810138001451755459 / 1000000000000000000) (√((1 : ℝ) - (((293119608097 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy158_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy158_hz12 : B (257874935035271921 / 1000000000000000000) (128937467517635961 / 500000000000000000) ((√((1 : ℝ) - (((293119608097 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy158_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy158_hz13 : B (410011093704220491 / 1000000000000000000) (41001109370422057 / 100000000000000000) (((293119608097 / 500000000000) : ℝ) * (kdot ((293119608097 / 500000000000)))) := bmul (bpoint ((293119608097 / 500000000000) : ℝ)) lowEnergy158_hz8 (by norm_num) (by norm_num)

theorem lowEnergy158_hz14 : B (166971507184873103 / 250000000000000000) (166971507184873123 / 250000000000000000) (((√((1 : ℝ) - (((293119608097 / 500000000000) : ℝ)^2))) / Real.pi) + (((293119608097 / 500000000000) : ℝ) * (kdot ((293119608097 / 500000000000))))) := badd lowEnergy158_hz12 lowEnergy158_hz13 (by norm_num) (by norm_num)

theorem lowEnergy158_hz15 : B (166971507184873103 / 250000000000000000) (166971507184873123 / 250000000000000000) (kappa ((293119608097 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy158_hz14

theorem lowEnergy158 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (461 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (670658470991 / 1000000000000) := by
  have hk1 : kappa q ≤ (11665499469 / 20000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((461 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy158_hz7.2.trans (by norm_num))
  have hk2 : kappa ((293119608097 / 500000000000) : ℝ) ≤ (33394301437 / 50000000000) := lowEnergy158_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((382066739409 / 500000000000) : ℝ)) (R := ((382499752111 / 500000000000) : ℝ)) (Q2 := ((293119608097 / 500000000000) : ℝ)) (T := ((32718027867 / 40000000000) : ℝ))
    (B := ((670658470991 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy159_hz0 : B (326164934153114631 / 500000000000000000) (2609319473227549 / 4000000000000000) (kdot ((921 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (607777955454055901 / 1000000000000000000)) (a := (136529741450218261 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (6077779554540559 / 10000000000000000)) (a := (546118965799839481 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy159_hz1 : B (848241 / 4000000) (848241 / 4000000) (((921 / 2000) : ℝ)^2) := bsq (bpoint ((921 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy159_hz2 : B (3151759 / 4000000) (3151759 / 4000000) ((1 : ℝ) - (((921 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy159_hz1 (by norm_num) (by norm_num)

theorem lowEnergy159_hz3 : B (443829851970324321 / 500000000000000000) (887659703940648643 / 1000000000000000000) (√((1 : ℝ) - (((921 / 2000) : ℝ)^2))) := bsqrt lowEnergy159_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy159_hz4 : B (282550859331285193 / 1000000000000000000) (141275429665642597 / 500000000000000000) ((√((1 : ℝ) - (((921 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy159_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy159_hz5 : B (12015916174200743 / 40000000000000000) (300397904355321579 / 1000000000000000000) (((921 / 2000) : ℝ) * (kdot ((921 / 2000)))) := bmul (bpoint ((921 / 2000) : ℝ)) lowEnergy159_hz0 (by norm_num) (by norm_num)

theorem lowEnergy159_hz6 : B (72868595460787971 / 125000000000000000) (582948763686606773 / 1000000000000000000) (((√((1 : ℝ) - (((921 / 2000) : ℝ)^2))) / Real.pi) + (((921 / 2000) : ℝ) * (kdot ((921 / 2000))))) := badd lowEnergy159_hz4 lowEnergy159_hz5 (by norm_num) (by norm_num)

theorem lowEnergy159_hz7 : B (72868595460787971 / 125000000000000000) (582948763686606773 / 1000000000000000000) (kappa ((921 / 2000))) := by rw [kappa_eq]; exact lowEnergy159_hz6

theorem lowEnergy159_hz8 : B (699263609767083073 / 1000000000000000000) (699263609767083209 / 1000000000000000000) (kdot ((23436482811 / 40000000000))) := by
    constructor
    · apply bkdot_lower (q := (255491665726089641 / 500000000000000000)) (a := (118098904277855633 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (510983331452179281 / 1000000000000000000)) (a := (5904945213892779 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy159_hz9 : B (171646477046968269 / 500000000000000000) (343292954093936539 / 1000000000000000000) (((23436482811 / 40000000000) : ℝ)^2) := bsq (bpoint ((23436482811 / 40000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy159_hz10 : B (656707045906063461 / 1000000000000000000) (328353522953031731 / 500000000000000000) ((1 : ℝ) - (((23436482811 / 40000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy159_hz9 (by norm_num) (by norm_num)

theorem lowEnergy159_hz11 : B (405187316529671083 / 500000000000000000) (810374633059342167 / 1000000000000000000) (√((1 : ℝ) - (((23436482811 / 40000000000) : ℝ)^2))) := bsqrt lowEnergy159_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy159_hz12 : B (128975128607675167 / 500000000000000000) (51590051443070067 / 200000000000000000) ((√((1 : ℝ) - (((23436482811 / 40000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy159_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy159_hz13 : B (409706989266601353 / 1000000000000000000) (204853494633300717 / 500000000000000000) (((23436482811 / 40000000000) : ℝ) * (kdot ((23436482811 / 40000000000)))) := bmul (bpoint ((23436482811 / 40000000000) : ℝ)) lowEnergy159_hz8 (by norm_num) (by norm_num)

theorem lowEnergy159_hz14 : B (667657246481951687 / 1000000000000000000) (667657246481951769 / 1000000000000000000) (((√((1 : ℝ) - (((23436482811 / 40000000000) : ℝ)^2))) / Real.pi) + (((23436482811 / 40000000000) : ℝ) * (kdot ((23436482811 / 40000000000))))) := badd lowEnergy159_hz12 lowEnergy159_hz13 (by norm_num) (by norm_num)

theorem lowEnergy159_hz15 : B (667657246481951687 / 1000000000000000000) (667657246481951769 / 1000000000000000000) (kappa ((23436482811 / 40000000000))) := by rw [kappa_eq]; exact lowEnergy159_hz14

theorem lowEnergy159 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (921 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (670429015813 / 1000000000000) := by
  have hk1 : kappa q ≤ (582948763687 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((921 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy159_hz7.2.trans (by norm_num))
  have hk2 : kappa ((23436482811 / 40000000000) : ℝ) ≤ (333828623241 / 500000000000) := lowEnergy159_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((30556799929 / 40000000000) : ℝ)) (R := ((764786023629 / 1000000000000) : ℝ)) (Q2 := ((23436482811 / 40000000000) : ℝ)) (T := ((817810591457 / 1000000000000) : ℝ))
    (B := ((670429015813 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

end BstLean.BlueprintLow

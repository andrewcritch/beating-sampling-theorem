import BstLean.Part291Energy
import BstLean.Part255Bounds
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part206 BstLean.Part211 BstLean.Part255
theorem lowEnergy0_hz0 : B (340787885684049643 / 500000000000000000) (340787885684051451 / 500000000000000000) (kdot ((27 / 50))) := by
    constructor
    · apply bkdot_lower (q := (68316965625002639 / 125000000000000000)) (a := (50017960869748799 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (546535725000021111 / 1000000000000000000)) (a := (500179608697482311 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy0_hz1 : B (729 / 2500) (729 / 2500) (((27 / 50) : ℝ)^2) := bsq (bpoint ((27 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy0_hz2 : B (1771 / 2500) (1771 / 2500) ((1 : ℝ) - (((27 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy0_hz1 (by norm_num) (by norm_num)

theorem lowEnergy0_hz3 : B (841665016500032511 / 1000000000000000000) (821938492675813 / 976562500000000) (√((1 : ℝ) - (((27 / 50) : ℝ)^2))) := bsqrt lowEnergy0_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy0_hz4 : B (133955147803501823 / 500000000000000000) (267910295607003647 / 1000000000000000000) ((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) := bdiv lowEnergy0_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy0_hz5 : B (184025458269386807 / 500000000000000000) (23003182283673473 / 62500000000000000) (((27 / 50) : ℝ) * (kdot ((27 / 50)))) := bmul (bpoint ((27 / 50) : ℝ)) lowEnergy0_hz0 (by norm_num) (by norm_num)

theorem lowEnergy0_hz6 : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) + (((27 / 50) : ℝ) * (kdot ((27 / 50))))) := badd lowEnergy0_hz4 lowEnergy0_hz5 (by norm_num) (by norm_num)

theorem lowEnergy0_hz7 : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (kappa ((27 / 50))) := by rw [kappa_eq]; exact lowEnergy0_hz6

theorem lowEnergy0_hz8 : B (144136561642574133 / 200000000000000000) (72068280821287067 / 100000000000000000) (kdot ((12781507079 / 20000000000))) := by
    constructor
    · apply bkdot_lower (q := (469254892806200439 / 1000000000000000000)) (a := (54843802358736053 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (234627446403100219 / 500000000000000000)) (a := (219375209434944209 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy0_hz9 : B (20420865401315889 / 50000000000000000) (408417308026317781 / 1000000000000000000) (((12781507079 / 20000000000) : ℝ)^2) := bsq (bpoint ((12781507079 / 20000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy0_hz10 : B (591582691973682219 / 1000000000000000000) (29579134598684111 / 50000000000000000) ((1 : ℝ) - (((12781507079 / 20000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy0_hz9 (by norm_num) (by norm_num)

theorem lowEnergy0_hz11 : B (192286032379773073 / 250000000000000000) (769144129519092293 / 1000000000000000000) (√((1 : ℝ) - (((12781507079 / 20000000000) : ℝ)^2))) := bsqrt lowEnergy0_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy0_hz12 : B (122413090163076509 / 500000000000000000) (244826180326153019 / 1000000000000000000) ((√((1 : ℝ) - (((12781507079 / 20000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy0_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy0_hz13 : B (460570620744320287 / 1000000000000000000) (460570620744320291 / 1000000000000000000) (((12781507079 / 20000000000) : ℝ) * (kdot ((12781507079 / 20000000000)))) := bmul (bpoint ((12781507079 / 20000000000) : ℝ)) lowEnergy0_hz8 (by norm_num) (by norm_num)

theorem lowEnergy0_hz14 : B (141079360214094661 / 200000000000000000) (70539680107047331 / 100000000000000000) (((√((1 : ℝ) - (((12781507079 / 20000000000) : ℝ)^2))) / Real.pi) + (((12781507079 / 20000000000) : ℝ) * (kdot ((12781507079 / 20000000000))))) := badd lowEnergy0_hz12 lowEnergy0_hz13 (by norm_num) (by norm_num)

theorem lowEnergy0_hz15 : B (141079360214094661 / 200000000000000000) (70539680107047331 / 100000000000000000) (kappa ((12781507079 / 20000000000))) := by rw [kappa_eq]; exact lowEnergy0_hz14

theorem lowEnergy0 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (27 / 50)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (44267434443 / 62500000000) := by
  have hk1 : kappa q ≤ (317980606073 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((27 / 50) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy0_hz7.2.trans (by norm_num))
  have hk2 : kappa ((12781507079 / 20000000000) : ℝ) ≤ (705396801071 / 1000000000000) := lowEnergy0_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((49866470611 / 62500000000) : ℝ)) (R := ((39936477759 / 50000000000) : ℝ)) (Q2 := ((12781507079 / 20000000000) : ℝ)) (T := ((210151599033 / 250000000000) : ℝ))
    (B := ((44267434443 / 62500000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy1_hz0 : B (681386712026585727 / 1000000000000000000) (681386712026589471 / 1000000000000000000) (kdot ((1079 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (273460733887407843 / 500000000000000000)) (a := (400381265933347 / 800000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (109384293554963137 / 200000000000000000)) (a := (500476582416677871 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy1_hz1 : B (1164241 / 4000000) (1164241 / 4000000) (((1079 / 2000) : ℝ)^2) := bsq (bpoint ((1079 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy1_hz2 : B (2835759 / 4000000) (2835759 / 4000000) ((1 : ℝ) - (((1079 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy1_hz1 (by norm_num) (by norm_num)

theorem lowEnergy1_hz3 : B (210496399909832187 / 250000000000000000) (841985599639328749 / 1000000000000000000) (√((1 : ℝ) - (((1079 / 2000) : ℝ)^2))) := bsqrt lowEnergy1_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy1_hz4 : B (268012340389585473 / 1000000000000000000) (134006170194792737 / 500000000000000000) ((√((1 : ℝ) - (((1079 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy1_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy1_hz5 : B (367608131138342999 / 1000000000000000000) (18380406556917251 / 50000000000000000) (((1079 / 2000) : ℝ) * (kdot ((1079 / 2000)))) := bmul (bpoint ((1079 / 2000) : ℝ)) lowEnergy1_hz0 (by norm_num) (by norm_num)

theorem lowEnergy1_hz6 : B (79452558940991059 / 125000000000000000) (317810235763965247 / 500000000000000000) (((√((1 : ℝ) - (((1079 / 2000) : ℝ)^2))) / Real.pi) + (((1079 / 2000) : ℝ) * (kdot ((1079 / 2000))))) := badd lowEnergy1_hz4 lowEnergy1_hz5 (by norm_num) (by norm_num)

theorem lowEnergy1_hz7 : B (79452558940991059 / 125000000000000000) (317810235763965247 / 500000000000000000) (kappa ((1079 / 2000))) := by rw [kappa_eq]; exact lowEnergy1_hz6

theorem lowEnergy1_hz8 : B (720541421060658517 / 1000000000000000000) (720541421060658521 / 1000000000000000000) (kdot ((638733651833 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (469525915819853821 / 1000000000000000000)) (a := (438972509289239257 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (23476295790992691 / 50000000000000000)) (a := (109743127322309813 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy1_hz9 : B (6374698093498751 / 15625000000000000) (81596135596784013 / 200000000000000000) (((638733651833 / 1000000000000) : ℝ)^2) := bsq (bpoint ((638733651833 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy1_hz10 : B (118403864403215987 / 200000000000000000) (9250301906501249 / 15625000000000000) ((1 : ℝ) - (((638733651833 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy1_hz9 (by norm_num) (by norm_num)

theorem lowEnergy1_hz11 : B (192356979665425699 / 250000000000000000) (384713959330851399 / 500000000000000000) (√((1 : ℝ) - (((638733651833 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy1_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy1_hz12 : B (244916513215837563 / 1000000000000000000) (48983302643167513 / 200000000000000000) ((√((1 : ℝ) - (((638733651833 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy1_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy1_hz13 : B (46023405317101371 / 100000000000000000) (230117026585506857 / 500000000000000000) (((638733651833 / 1000000000000) : ℝ) * (kdot ((638733651833 / 1000000000000)))) := bmul (bpoint ((638733651833 / 1000000000000) : ℝ)) lowEnergy1_hz8 (by norm_num) (by norm_num)

theorem lowEnergy1_hz14 : B (705150566386851273 / 1000000000000000000) (705150566386851279 / 1000000000000000000) (((√((1 : ℝ) - (((638733651833 / 1000000000000) : ℝ)^2))) / Real.pi) + (((638733651833 / 1000000000000) : ℝ) * (kdot ((638733651833 / 1000000000000))))) := badd lowEnergy1_hz12 lowEnergy1_hz13 (by norm_num) (by norm_num)

theorem lowEnergy1_hz15 : B (705150566386851273 / 1000000000000000000) (705150566386851279 / 1000000000000000000) (kappa ((638733651833 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy1_hz14

theorem lowEnergy1 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1079 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (708032000171 / 1000000000000) := by
  have hk1 : kappa q ≤ (79452558941 / 125000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1079 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy1_hz7.2.trans (by norm_num))
  have hk2 : kappa ((638733651833 / 1000000000000) : ℝ) ≤ (705150566387 / 1000000000000) := lowEnergy1_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((797649968049 / 1000000000000) : ℝ)) (R := ((798515993453 / 1000000000000) : ℝ)) (Q2 := ((638733651833 / 1000000000000) : ℝ)) (T := ((840459667003 / 1000000000000) : ℝ))
    (B := ((708032000171 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy2_hz0 : B (681197724608070961 / 1000000000000000000) (170299431152018709 / 250000000000000000) (kdot ((539 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (109461437811547497 / 200000000000000000)) (a := (100154688631899439 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (136826797264434371 / 250000000000000000)) (a := (500773443159491109 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy2_hz1 : B (290521 / 1000000) (290521 / 1000000) (((539 / 1000) : ℝ)^2) := bsq (bpoint ((539 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy2_hz2 : B (709479 / 1000000) (709479 / 1000000) ((1 : ℝ) - (((539 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy2_hz1 (by norm_num) (by norm_num)

theorem lowEnergy2_hz3 : B (210576440989964497 / 250000000000000000) (842305763959857989 / 1000000000000000000) (√((1 : ℝ) - (((539 / 1000) : ℝ)^2))) := bsqrt lowEnergy2_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy2_hz4 : B (134057125929006623 / 500000000000000000) (4189285185281457 / 15625000000000000) ((√((1 : ℝ) - (((539 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy2_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy2_hz5 : B (367165573563750247 / 1000000000000000000) (367165573563752337 / 1000000000000000000) (((539 / 1000) : ℝ) * (kdot ((539 / 1000)))) := bmul (bpoint ((539 / 1000) : ℝ)) lowEnergy2_hz0 (by norm_num) (by norm_num)

theorem lowEnergy2_hz6 : B (635279825421763493 / 1000000000000000000) (127055965084353117 / 200000000000000000) (((√((1 : ℝ) - (((539 / 1000) : ℝ)^2))) / Real.pi) + (((539 / 1000) : ℝ) * (kdot ((539 / 1000))))) := badd lowEnergy2_hz4 lowEnergy2_hz5 (by norm_num) (by norm_num)

theorem lowEnergy2_hz7 : B (635279825421763493 / 1000000000000000000) (127055965084353117 / 200000000000000000) (kappa ((539 / 1000))) := by rw [kappa_eq]; exact lowEnergy2_hz6

theorem lowEnergy2_hz8 : B (144080025035456469 / 200000000000000000) (720400125177282349 / 1000000000000000000) (kdot ((127678408879 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (234898410177893089 / 500000000000000000)) (a := (109798614085959447 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (469796820355786177 / 1000000000000000000)) (a := (439194456343837783 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy2_hz9 : B (8150888046936553 / 20000000000000000) (407544402346827651 / 1000000000000000000) (((127678408879 / 200000000000) : ℝ)^2) := bsq (bpoint ((127678408879 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy2_hz10 : B (592455597653172349 / 1000000000000000000) (11849111953063447 / 20000000000000000) ((1 : ℝ) - (((127678408879 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy2_hz9 (by norm_num) (by norm_num)

theorem lowEnergy2_hz11 : B (153942274590597413 / 200000000000000000) (769711372952987067 / 1000000000000000000) (√((1 : ℝ) - (((127678408879 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy2_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy2_hz12 : B (122503369759517283 / 500000000000000000) (245006739519034567 / 1000000000000000000) ((√((1 : ℝ) - (((127678408879 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy2_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy2_hz13 : B (114974427173584797 / 250000000000000000) (459897708694339191 / 1000000000000000000) (((127678408879 / 200000000000) : ℝ) * (kdot ((127678408879 / 200000000000)))) := bmul (bpoint ((127678408879 / 200000000000) : ℝ)) lowEnergy2_hz8 (by norm_num) (by norm_num)

theorem lowEnergy2_hz14 : B (352452224106686877 / 500000000000000000) (352452224106686879 / 500000000000000000) (((√((1 : ℝ) - (((127678408879 / 200000000000) : ℝ)^2))) / Real.pi) + (((127678408879 / 200000000000) : ℝ) * (kdot ((127678408879 / 200000000000))))) := badd lowEnergy2_hz12 lowEnergy2_hz13 (by norm_num) (by norm_num)

theorem lowEnergy2_hz15 : B (352452224106686877 / 500000000000000000) (352452224106686879 / 500000000000000000) (kappa ((127678408879 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy2_hz14

theorem lowEnergy2 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (539 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (353892583027 / 500000000000) := by
  have hk1 : kappa q ≤ (317639912711 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((539 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy2_hz7.2.trans (by norm_num))
  have hk2 : kappa ((127678408879 / 200000000000) : ℝ) ≤ (352452224107 / 500000000000) := lowEnergy2_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((199359102097 / 250000000000) : ℝ)) (R := ((1559184441 / 1953125000) : ℝ)) (Q2 := ((127678408879 / 200000000000) : ℝ)) (T := ((840312981699 / 1000000000000) : ℝ))
    (B := ((353892583027 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy3_hz0 : B (340504404481995099 / 500000000000000000) (681008808963994209 / 1000000000000000000) (kdot ((1077 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (547692889138137057 / 1000000000000000000)) (a := (501070191159293349 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (17115402785566783 / 31250000000000000)) (a := (10021403823185741 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy3_hz1 : B (1159929 / 4000000) (1159929 / 4000000) (((1077 / 2000) : ℝ)^2) := bsq (bpoint ((1077 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy3_hz2 : B (2840071 / 4000000) (2840071 / 4000000) ((1 : ℝ) - (((1077 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy3_hz1 (by norm_num) (by norm_num)

theorem lowEnergy3_hz3 : B (842625509939023861 / 1000000000000000000) (421312754969511931 / 500000000000000000) (√((1 : ℝ) - (((1077 / 2000) : ℝ)^2))) := bsqrt lowEnergy3_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy3_hz4 : B (13410801508212463 / 50000000000000000) (268216030164249261 / 1000000000000000000) ((√((1 : ℝ) - (((1077 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy3_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy3_hz5 : B (366723243627108721 / 1000000000000000000) (183361621813555441 / 500000000000000000) (((1077 / 2000) : ℝ) * (kdot ((1077 / 2000)))) := bmul (bpoint ((1077 / 2000) : ℝ)) lowEnergy3_hz0 (by norm_num) (by norm_num)

theorem lowEnergy3_hz6 : B (634939273791357981 / 1000000000000000000) (634939273791360143 / 1000000000000000000) (((√((1 : ℝ) - (((1077 / 2000) : ℝ)^2))) / Real.pi) + (((1077 / 2000) : ℝ) * (kdot ((1077 / 2000))))) := badd lowEnergy3_hz4 lowEnergy3_hz5 (by norm_num) (by norm_num)

theorem lowEnergy3_hz7 : B (634939273791357981 / 1000000000000000000) (634939273791360143 / 1000000000000000000) (kappa ((1077 / 2000))) := by rw [kappa_eq]; exact lowEnergy3_hz6

theorem lowEnergy3_hz8 : B (180064730104809777 / 250000000000000000) (90032365052404889 / 125000000000000000) (kdot ((1595126329 / 2500000000))) := by
    constructor
    · apply bkdot_lower (q := (235033803312063391 / 500000000000000000)) (a := (439416260259098067 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (470067606624126781 / 1000000000000000000)) (a := (219708130129549031 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy3_hz9 : B (203554240437521299 / 500000000000000000) (407108480875042599 / 1000000000000000000) (((1595126329 / 2500000000) : ℝ)^2) := bsq (bpoint ((1595126329 / 2500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy3_hz10 : B (592891519124957401 / 1000000000000000000) (296445759562478701 / 500000000000000000) ((1 : ℝ) - (((1595126329 / 2500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy3_hz9 (by norm_num) (by norm_num)

theorem lowEnergy3_hz11 : B (153998898583718111 / 200000000000000000) (769994492918590557 / 1000000000000000000) (√((1 : ℝ) - (((1595126329 / 2500000000) : ℝ)^2))) := bsqrt lowEnergy3_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy3_hz12 : B (245096859403062171 / 1000000000000000000) (245096859403062173 / 1000000000000000000) ((√((1 : ℝ) - (((1595126329 / 2500000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy3_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy3_hz13 : B (459561587063137607 / 1000000000000000000) (459561587063137611 / 1000000000000000000) (((1595126329 / 2500000000) : ℝ) * (kdot ((1595126329 / 2500000000)))) := bmul (bpoint ((1595126329 / 2500000000) : ℝ)) lowEnergy3_hz8 (by norm_num) (by norm_num)

theorem lowEnergy3_hz14 : B (352329223233099889 / 500000000000000000) (88082305808274973 / 125000000000000000) (((√((1 : ℝ) - (((1595126329 / 2500000000) : ℝ)^2))) / Real.pi) + (((1595126329 / 2500000000) : ℝ) * (kdot ((1595126329 / 2500000000))))) := badd lowEnergy3_hz12 lowEnergy3_hz13 (by norm_num) (by norm_num)

theorem lowEnergy3_hz15 : B (352329223233099889 / 500000000000000000) (88082305808274973 / 125000000000000000) (kappa ((1595126329 / 2500000000))) := by rw [kappa_eq]; exact lowEnergy3_hz14

theorem lowEnergy3 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1077 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (707538448651 / 1000000000000) := by
  have hk1 : kappa q ≤ (9920926153 / 15625000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1077 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy3_hz7.2.trans (by norm_num))
  have hk2 : kappa ((1595126329 / 2500000000) : ℝ) ≤ (704658446467 / 1000000000000) := lowEnergy3_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((199305712693 / 250000000000) : ℝ)) (R := ((49880554761 / 62500000000) : ℝ)) (Q2 := ((1595126329 / 2500000000) : ℝ)) (T := ((840166340193 / 1000000000000) : ℝ))
    (B := ((707538448651 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy4_hz0 : B (680819964946161617 / 1000000000000000000) (680819964946165769 / 1000000000000000000) (kdot ((269 / 500))) := by
    constructor
    · apply bkdot_lower (q := (548078568304864967 / 1000000000000000000)) (a := (250683413324417837 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (274039284152432483 / 500000000000000000)) (a := (250683413324414577 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy4_hz1 : B (72361 / 250000) (72361 / 250000) (((269 / 500) : ℝ)^2) := bsq (bpoint ((269 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy4_hz2 : B (177639 / 250000) (177639 / 250000) ((1 : ℝ) - (((269 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy4_hz1 (by norm_num) (by norm_num)

theorem lowEnergy4_hz3 : B (842944838052882319 / 1000000000000000000) (10536810475661029 / 12500000000000000) (√((1 : ℝ) - (((269 / 500) : ℝ)^2))) := bsqrt lowEnergy4_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy4_hz4 : B (26831767545982683 / 100000000000000000) (16769854716239177 / 62500000000000000) ((√((1 : ℝ) - (((269 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy4_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy4_hz5 : B (366281141141034949 / 1000000000000000000) (2861571415164353 / 7812500000000000) (((269 / 500) : ℝ) * (kdot ((269 / 500)))) := bmul (bpoint ((269 / 500) : ℝ)) lowEnergy4_hz0 (by norm_num) (by norm_num)

theorem lowEnergy4_hz6 : B (634598816600861779 / 1000000000000000000) (39662426037554001 / 62500000000000000) (((√((1 : ℝ) - (((269 / 500) : ℝ)^2))) / Real.pi) + (((269 / 500) : ℝ) * (kdot ((269 / 500))))) := badd lowEnergy4_hz4 lowEnergy4_hz5 (by norm_num) (by norm_num)

theorem lowEnergy4_hz7 : B (634598816600861779 / 1000000000000000000) (39662426037554001 / 62500000000000000) (kappa ((269 / 500))) := by rw [kappa_eq]; exact lowEnergy4_hz6

theorem lowEnergy4_hz8 : B (360058903321699543 / 500000000000000000) (72011780664339909 / 100000000000000000) (kdot ((159427278353 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (117584568708611689 / 250000000000000000)) (a := (109909480314961933 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (94067654966889351 / 200000000000000000)) (a := (439637921259847727 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy4_hz9 : B (203336456664359539 / 500000000000000000) (406672913328719079 / 1000000000000000000) (((159427278353 / 250000000000) : ℝ)^2) := bsq (bpoint ((159427278353 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy4_hz10 : B (593327086671280921 / 1000000000000000000) (296663543335640461 / 500000000000000000) ((1 : ℝ) - (((159427278353 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy4_hz9 (by norm_num) (by norm_num)

theorem lowEnergy4_hz11 : B (154055455816570277 / 200000000000000000) (770277279082851387 / 1000000000000000000) (√((1 : ℝ) - (((159427278353 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy4_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy4_hz12 : B (245186873034822387 / 1000000000000000000) (61296718258705597 / 250000000000000000) ((√((1 : ℝ) - (((159427278353 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy4_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy4_hz13 : B (229612844013378037 / 500000000000000000) (229612844013378039 / 500000000000000000) (((159427278353 / 250000000000) : ℝ) * (kdot ((159427278353 / 250000000000)))) := bmul (bpoint ((159427278353 / 250000000000) : ℝ)) lowEnergy4_hz8 (by norm_num) (by norm_num)

theorem lowEnergy4_hz14 : B (704412561061578461 / 1000000000000000000) (352206280530789233 / 500000000000000000) (((√((1 : ℝ) - (((159427278353 / 250000000000) : ℝ)^2))) / Real.pi) + (((159427278353 / 250000000000) : ℝ) * (kdot ((159427278353 / 250000000000))))) := badd lowEnergy4_hz12 lowEnergy4_hz13 (by norm_num) (by norm_num)

theorem lowEnergy4_hz15 : B (704412561061578461 / 1000000000000000000) (352206280530789233 / 500000000000000000) (kappa ((159427278353 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy4_hz14

theorem lowEnergy4 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (269 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (707291847877 / 1000000000000) := by
  have hk1 : kappa q ≤ (634598816601 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((269 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy4_hz7.2.trans (by norm_num))
  have hk2 : kappa ((159427278353 / 250000000000) : ℝ) ≤ (352206280531 / 500000000000) := lowEnergy4_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((797009295179 / 1000000000000) : ℝ)) (R := ((797875320583 / 1000000000000) : ℝ)) (Q2 := ((159427278353 / 250000000000) : ℝ)) (T := ((840019742457 / 1000000000000) : ℝ))
    (B := ((707291847877 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy5_hz0 : B (680631192406784877 / 1000000000000000000) (27225247696271567 / 40000000000000000) (kdot ((43 / 80))) := by
    constructor
    · apply bkdot_lower (q := (548464226846274179 / 1000000000000000000)) (a := (250831674930144201 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (274232113423137089 / 500000000000000000)) (a := (501663349860281653 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy5_hz1 : B (1849 / 6400) (1849 / 6400) (((43 / 80) : ℝ)^2) := bsq (bpoint ((43 / 80) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy5_hz2 : B (4551 / 6400) (4551 / 6400) ((1 : ℝ) - (((43 / 80) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy5_hz1 (by norm_num) (by norm_num)

theorem lowEnergy5_hz3 : B (210815937194036637 / 250000000000000000) (843263748776146549 / 1000000000000000000) (√((1 : ℝ) - (((43 / 80) : ℝ)^2))) := bsqrt lowEnergy5_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy5_hz4 : B (268419187895851857 / 1000000000000000000) (268419187895851859 / 1000000000000000000) ((√((1 : ℝ) - (((43 / 80) : ℝ)^2))) / Real.pi) := bdiv lowEnergy5_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy5_hz5 : B (365839265918646871 / 1000000000000000000) (182919632959324591 / 500000000000000000) (((43 / 80) : ℝ) * (kdot ((43 / 80)))) := bmul (bpoint ((43 / 80) : ℝ)) lowEnergy5_hz0 (by norm_num) (by norm_num)

theorem lowEnergy5_hz6 : B (79282306726812341 / 125000000000000000) (634258453814501041 / 1000000000000000000) (((√((1 : ℝ) - (((43 / 80) : ℝ)^2))) / Real.pi) + (((43 / 80) : ℝ) * (kdot ((43 / 80))))) := badd lowEnergy5_hz4 lowEnergy5_hz5 (by norm_num) (by norm_num)

theorem lowEnergy5_hz7 : B (79282306726812341 / 125000000000000000) (634258453814501041 / 1000000000000000000) (kappa ((43 / 80))) := by rw [kappa_eq]; exact lowEnergy5_hz6

theorem lowEnergy5_hz8 : B (359988391853708783 / 500000000000000000) (719976783707417571 / 1000000000000000000) (kdot ((159341947449 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (235304412597484317 / 500000000000000000)) (a := (54982429946210167 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (470608825194968633 / 1000000000000000000)) (a := (43985943956968133 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy5_hz9 : B (406237699469438041 / 1000000000000000000) (203118849734719021 / 500000000000000000) (((159341947449 / 250000000000) : ℝ)^2) := bsq (bpoint ((159341947449 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy5_hz10 : B (296881150265280979 / 500000000000000000) (593762300530561959 / 1000000000000000000) ((1 : ℝ) - (((159341947449 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy5_hz9 (by norm_num) (by norm_num)

theorem lowEnergy5_hz11 : B (77055973196797791 / 100000000000000000) (770559731967977911 / 1000000000000000000) (√((1 : ℝ) - (((159341947449 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy5_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy5_hz12 : B (122638390290269647 / 500000000000000000) (7664899393141853 / 31250000000000000) ((√((1 : ℝ) - (((159341947449 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy5_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy5_hz13 : B (114722502834007369 / 250000000000000000) (11472250283400737 / 25000000000000000) (((159341947449 / 250000000000) : ℝ) * (kdot ((159341947449 / 250000000000)))) := bmul (bpoint ((159341947449 / 250000000000) : ℝ)) lowEnergy5_hz8 (by norm_num) (by norm_num)

theorem lowEnergy5_hz14 : B (70416679191656877 / 100000000000000000) (88020848989571097 / 125000000000000000) (((√((1 : ℝ) - (((159341947449 / 250000000000) : ℝ)^2))) / Real.pi) + (((159341947449 / 250000000000) : ℝ) * (kdot ((159341947449 / 250000000000))))) := badd lowEnergy5_hz12 lowEnergy5_hz13 (by norm_num) (by norm_num)

theorem lowEnergy5_hz15 : B (70416679191656877 / 100000000000000000) (88020848989571097 / 125000000000000000) (kappa ((159341947449 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy5_hz14

theorem lowEnergy5 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (43 / 80)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (176761340913 / 250000000000) := by
  have hk1 : kappa q ≤ (126851690763 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((43 / 80) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy5_hz7.2.trans (by norm_num))
  have hk2 : kappa ((159341947449 / 250000000000) : ℝ) ≤ (704166791917 / 1000000000000) := lowEnergy5_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((79679574159 / 100000000000) : ℝ)) (R := ((398830883497 / 500000000000) : ℝ)) (Q2 := ((159341947449 / 250000000000) : ℝ)) (T := ((419936594233 / 500000000000) : ℝ))
    (B := ((176761340913 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy6_hz0 : B (340221245599219823 / 500000000000000000) (340221245599222047 / 500000000000000000) (kdot ((537 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (548849865050222423 / 1000000000000000000)) (a := (10039195220504377 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (274424932525111211 / 500000000000000000)) (a := (100391952205042373 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy6_hz1 : B (288369 / 1000000) (288369 / 1000000) (((537 / 1000) : ℝ)^2) := bsq (bpoint ((537 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy6_hz2 : B (711631 / 1000000) (711631 / 1000000) ((1 : ℝ) - (((537 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy6_hz1 (by norm_num) (by norm_num)

theorem lowEnergy6_hz3 : B (843582242582191863 / 1000000000000000000) (105447780322773983 / 125000000000000000) (√((1 : ℝ) - (((537 / 1000) : ℝ)^2))) := bsqrt lowEnergy6_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy6_hz4 : B (8391267738218887 / 31250000000000000) (53704113524600877 / 200000000000000000) ((√((1 : ℝ) - (((537 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy6_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy6_hz5 : B (365397617773562089 / 1000000000000000000) (365397617773564479 / 1000000000000000000) (((537 / 1000) : ℝ) * (kdot ((537 / 1000)))) := bmul (bpoint ((537 / 1000) : ℝ)) lowEnergy6_hz0 (by norm_num) (by norm_num)

theorem lowEnergy6_hz6 : B (633918185396566473 / 1000000000000000000) (19809943293642777 / 31250000000000000) (((√((1 : ℝ) - (((537 / 1000) : ℝ)^2))) / Real.pi) + (((537 / 1000) : ℝ) * (kdot ((537 / 1000))))) := badd lowEnergy6_hz4 lowEnergy6_hz5 (by norm_num) (by norm_num)

theorem lowEnergy6_hz7 : B (633918185396566473 / 1000000000000000000) (19809943293642777 / 31250000000000000) (kappa ((537 / 1000))) := by rw [kappa_eq]; exact lowEnergy6_hz6

theorem lowEnergy6_hz8 : B (143967170293698773 / 200000000000000000) (71983585146849387 / 100000000000000000) (kdot ((127405312143 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (470879257914946523 / 1000000000000000000)) (a := (220040407706454833 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (235439628957473261 / 500000000000000000)) (a := (22004040770645483 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy6_hz9 : B (405802839056381581 / 1000000000000000000) (202901419528190791 / 500000000000000000) (((127405312143 / 200000000000) : ℝ)^2) := bsq (bpoint ((127405312143 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy6_hz10 : B (297098580471809209 / 500000000000000000) (594197160943618419 / 1000000000000000000) ((1 : ℝ) - (((127405312143 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy6_hz9 (by norm_num) (by norm_num)

theorem lowEnergy6_hz11 : B (770841852096536347 / 1000000000000000000) (770841852096536349 / 1000000000000000000) (√((1 : ℝ) - (((127405312143 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy6_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy6_hz12 : B (245366582206550887 / 1000000000000000000) (30670822775818861 / 125000000000000000) ((√((1 : ℝ) - (((127405312143 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy6_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy6_hz13 : B (458554556740328229 / 1000000000000000000) (458554556740328233 / 1000000000000000000) (((127405312143 / 200000000000) : ℝ) * (kdot ((127405312143 / 200000000000)))) := bmul (bpoint ((127405312143 / 200000000000) : ℝ)) lowEnergy6_hz8 (by norm_num) (by norm_num)

theorem lowEnergy6_hz14 : B (175980284736719779 / 250000000000000000) (703921138946879121 / 1000000000000000000) (((√((1 : ℝ) - (((127405312143 / 200000000000) : ℝ)^2))) / Real.pi) + (((127405312143 / 200000000000) : ℝ) * (kdot ((127405312143 / 200000000000))))) := badd lowEnergy6_hz12 lowEnergy6_hz13 (by norm_num) (by norm_num)

theorem lowEnergy6_hz15 : B (175980284736719779 / 250000000000000000) (703921138946879121 / 1000000000000000000) (kappa ((127405312143 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy6_hz14

theorem lowEnergy6 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (537 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (44174937243 / 62500000000) := by
  have hk1 : kappa q ≤ (633918185397 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((537 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy6_hz7.2.trans (by norm_num))
  have hk2 : kappa ((127405312143 / 200000000000) : ℝ) ≤ (703921138947 / 1000000000000) := lowEnergy6_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((796582189983 / 1000000000000) : ℝ)) (R := ((797448215387 / 1000000000000) : ℝ)) (Q2 := ((127405312143 / 200000000000) : ℝ)) (T := ((839726678191 / 1000000000000) : ℝ))
    (B := ((44174937243 / 62500000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy7_hz0 : B (680253861174084121 / 1000000000000000000) (170063465293522181 / 250000000000000000) (kdot ((1073 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (549235483204074569 / 1000000000000000000)) (a := (502256060374599741 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (68654435400509321 / 125000000000000000)) (a := (490484433959563 / 976562500000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy7_hz1 : B (1151329 / 4000000) (1151329 / 4000000) (((1073 / 2000) : ℝ)^2) := bsq (bpoint ((1073 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy7_hz2 : B (2848671 / 4000000) (2848671 / 4000000) ((1 : ℝ) - (((1073 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy7_hz1 (by norm_num) (by norm_num)

theorem lowEnergy7_hz3 : B (843900319943060573 / 1000000000000000000) (421950159971530287 / 500000000000000000) (√((1 : ℝ) - (((1073 / 2000) : ℝ)^2))) := bsqrt lowEnergy7_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy7_hz4 : B (268621814791540143 / 1000000000000000000) (53724362958308029 / 200000000000000000) ((√((1 : ℝ) - (((1073 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy7_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy7_hz5 : B (36495619651989613 / 100000000000000000) (364956196519898601 / 1000000000000000000) (((1073 / 2000) : ℝ) * (kdot ((1073 / 2000)))) := bmul (bpoint ((1073 / 2000) : ℝ)) lowEnergy7_hz0 (by norm_num) (by norm_num)

theorem lowEnergy7_hz6 : B (633578011311436273 / 1000000000000000000) (316789005655719373 / 500000000000000000) (((√((1 : ℝ) - (((1073 / 2000) : ℝ)^2))) / Real.pi) + (((1073 / 2000) : ℝ) * (kdot ((1073 / 2000))))) := badd lowEnergy7_hz4 lowEnergy7_hz5 (by norm_num) (by norm_num)

theorem lowEnergy7_hz7 : B (633578011311436273 / 1000000000000000000) (316789005655719373 / 500000000000000000) (kappa ((1073 / 2000))) := by rw [kappa_eq]; exact lowEnergy7_hz6

theorem lowEnergy7_hz8 : B (359847504892304907 / 500000000000000000) (359847504892304909 / 500000000000000000) (kdot ((636685426133 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (235574786601144983 / 500000000000000000)) (a := (440302049012614341 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (94229914640457993 / 200000000000000000)) (a := (6879719515822099 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy7_hz9 : B (405368331850159799 / 1000000000000000000) (2026841659250799 / 5000000000000000) (((636685426133 / 1000000000000) : ℝ)^2) := bsq (bpoint ((636685426133 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy7_hz10 : B (2973158340749201 / 5000000000000000) (594631668149840201 / 1000000000000000000) ((1 : ℝ) - (((636685426133 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy7_hz9 (by norm_num) (by norm_num)

theorem lowEnergy7_hz11 : B (771123639988971029 / 1000000000000000000) (77112363998897103 / 100000000000000000) (√((1 : ℝ) - (((636685426133 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy7_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy7_hz12 : B (245456278078519741 / 1000000000000000000) (122728139039259871 / 500000000000000000) ((√((1 : ℝ) - (((636685426133 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy7_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy7_hz13 : B (458219323990507903 / 1000000000000000000) (458219323990507907 / 1000000000000000000) (((636685426133 / 1000000000000) : ℝ) * (kdot ((636685426133 / 1000000000000)))) := bmul (bpoint ((636685426133 / 1000000000000) : ℝ)) lowEnergy7_hz8 (by norm_num) (by norm_num)

theorem lowEnergy7_hz14 : B (175918900517256911 / 250000000000000000) (703675602069027649 / 1000000000000000000) (((√((1 : ℝ) - (((636685426133 / 1000000000000) : ℝ)^2))) / Real.pi) + (((636685426133 / 1000000000000) : ℝ) * (kdot ((636685426133 / 1000000000000))))) := badd lowEnergy7_hz12 lowEnergy7_hz13 (by norm_num) (by norm_num)

theorem lowEnergy7_hz15 : B (175918900517256911 / 250000000000000000) (703675602069027649 / 1000000000000000000) (kappa ((636685426133 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy7_hz14

theorem lowEnergy7 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1073 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (141310548901 / 200000000000) := by
  have hk1 : kappa q ≤ (39598625707 / 62500000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1073 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy7_hz7.2.trans (by norm_num))
  have hk2 : kappa ((636685426133 / 1000000000000) : ℝ) ≤ (70367560207 / 100000000000) := lowEnergy7_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((796368640337 / 1000000000000) : ℝ)) (R := ((797234665741 / 1000000000000) : ℝ)) (Q2 := ((636685426133 / 1000000000000) : ℝ)) (T := ((839580211607 / 1000000000000) : ℝ))
    (B := ((141310548901 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy8_hz0 : B (170016325546763393 / 250000000000000000) (21252040693345573 / 31250000000000000) (kdot ((67 / 125))) := by
    constructor
    · apply bkdot_lower (q := (274810540797352483 / 500000000000000000)) (a := (502552248138811493 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (109924216318940993 / 200000000000000000)) (a := (502552248138804011 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy8_hz1 : B (4489 / 15625) (4489 / 15625) (((67 / 125) : ℝ)^2) := bsq (bpoint ((67 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy8_hz2 : B (11136 / 15625) (11136 / 15625) ((1 : ℝ) - (((67 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy8_hz1 (by norm_num) (by norm_num)

theorem lowEnergy8_hz3 : B (422108990664733413 / 500000000000000000) (844217981329466827 / 1000000000000000000) (√((1 : ℝ) - (((67 / 125) : ℝ)^2))) := bsqrt lowEnergy8_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy8_hz4 : B (268722929551292103 / 1000000000000000000) (33590366193911513 / 125000000000000000) ((√((1 : ℝ) - (((67 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy8_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy8_hz5 : B (182257500986130357 / 500000000000000000) (364515001972263269 / 1000000000000000000) (((67 / 125) : ℝ) * (kdot ((67 / 125)))) := bmul (bpoint ((67 / 125) : ℝ)) lowEnergy8_hz0 (by norm_num) (by norm_num)

theorem lowEnergy8_hz6 : B (633237931523552817 / 1000000000000000000) (633237931523555373 / 1000000000000000000) (((√((1 : ℝ) - (((67 / 125) : ℝ)^2))) / Real.pi) + (((67 / 125) : ℝ) * (kdot ((67 / 125))))) := badd lowEnergy8_hz4 lowEnergy8_hz5 (by norm_num) (by norm_num)

theorem lowEnergy8_hz7 : B (633237931523552817 / 1000000000000000000) (633237931523555373 / 1000000000000000000) (kappa ((67 / 125))) := by rw [kappa_eq]; exact lowEnergy8_hz6

theorem lowEnergy8_hz8 : B (719554258515352883 / 1000000000000000000) (89944282314419111 / 125000000000000000) (kdot ((636344386017 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (471419771261982261 / 1000000000000000000)) (a := (13766348143417339 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (23570988563099113 / 50000000000000000)) (a := (220261570294677421 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy8_hz9 : B (80986835523070541 / 200000000000000000) (202467088807676353 / 500000000000000000) (((636344386017 / 1000000000000) : ℝ)^2) := bsq (bpoint ((636344386017 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy8_hz10 : B (297532911192323647 / 500000000000000000) (119013164476929459 / 200000000000000000) ((1 : ℝ) - (((636344386017 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy8_hz9 (by norm_num) (by norm_num)

theorem lowEnergy8_hz11 : B (385702548080981471 / 500000000000000000) (771405096161962943 / 1000000000000000000) (√((1 : ℝ) - (((636344386017 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy8_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy8_hz12 : B (122772934180455261 / 500000000000000000) (245545868360910523 / 1000000000000000000) ((√((1 : ℝ) - (((636344386017 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy8_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy8_hz13 : B (114471078210217481 / 250000000000000000) (57235539105108741 / 125000000000000000) (((636344386017 / 1000000000000) : ℝ) * (kdot ((636344386017 / 1000000000000)))) := bmul (bpoint ((636344386017 / 1000000000000) : ℝ)) lowEnergy8_hz8 (by norm_num) (by norm_num)

theorem lowEnergy8_hz14 : B (351715090600890223 / 500000000000000000) (703430181201780451 / 1000000000000000000) (((√((1 : ℝ) - (((636344386017 / 1000000000000) : ℝ)^2))) / Real.pi) + (((636344386017 / 1000000000000) : ℝ) * (kdot ((636344386017 / 1000000000000))))) := badd lowEnergy8_hz12 lowEnergy8_hz13 (by norm_num) (by norm_num)

theorem lowEnergy8_hz15 : B (351715090600890223 / 500000000000000000) (703430181201780451 / 1000000000000000000) (kappa ((636344386017 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy8_hz14

theorem lowEnergy8 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (67 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (35315330471 / 50000000000) := by
  have hk1 : kappa q ≤ (158309482881 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((67 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy8_hz7.2.trans (by norm_num))
  have hk2 : kappa ((636344386017 / 1000000000000) : ℝ) ≤ (351715090601 / 500000000000) := lowEnergy8_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((796155092633 / 1000000000000) : ℝ)) (R := ((797021118037 / 1000000000000) : ℝ)) (Q2 := ((636344386017 / 1000000000000) : ℝ)) (T := ((839433788687 / 1000000000000) : ℝ))
    (B := ((35315330471 / 50000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy9_hz0 : B (679876814091058883 / 1000000000000000000) (339938407045531907 / 500000000000000000) (kdot ((1071 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (275003330254249897 / 500000000000000000)) (a := (251424162273822257 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (550006660508499793 / 1000000000000000000)) (a := (50284832454763677 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy9_hz1 : B (1147041 / 4000000) (1147041 / 4000000) (((1071 / 2000) : ℝ)^2) := bsq (bpoint ((1071 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy9_hz2 : B (2852959 / 4000000) (2852959 / 4000000) ((1 : ℝ) - (((1071 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy9_hz1 (by norm_num) (by norm_num)

theorem lowEnergy9_hz3 : B (105566903401350179 / 125000000000000000) (844535227210801433 / 1000000000000000000) (√((1 : ℝ) - (((1071 / 2000) : ℝ)^2))) := bsqrt lowEnergy9_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy9_hz4 : B (134411956025835999 / 500000000000000000) (268823912051671999 / 1000000000000000000) ((√((1 : ℝ) - (((1071 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy9_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy9_hz5 : B (364074033945762031 / 1000000000000000000) (364074033945764673 / 1000000000000000000) (((1071 / 2000) : ℝ) * (kdot ((1071 / 2000)))) := bmul (bpoint ((1071 / 2000) : ℝ)) lowEnergy9_hz0 (by norm_num) (by norm_num)

theorem lowEnergy9_hz6 : B (632897945997434029 / 1000000000000000000) (2472257601552487 / 3906250000000000) (((√((1 : ℝ) - (((1071 / 2000) : ℝ)^2))) / Real.pi) + (((1071 / 2000) : ℝ) * (kdot ((1071 / 2000))))) := badd lowEnergy9_hz4 lowEnergy9_hz5 (by norm_num) (by norm_num)

theorem lowEnergy9_hz7 : B (632897945997434029 / 1000000000000000000) (2472257601552487 / 3906250000000000) (kappa ((1071 / 2000))) := by rw [kappa_eq]; exact lowEnergy9_hz6

theorem lowEnergy9_hz8 : B (179853399379550043 / 250000000000000000) (719413597518200177 / 1000000000000000000) (kdot ((79500430041 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (471689852303213243 / 1000000000000000000)) (a := (220372045183502817 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (235844926151606621 / 500000000000000000)) (a := (110186022591751407 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy9_hz9 : B (25281273506815741 / 62500000000000000) (404500376109051857 / 1000000000000000000) (((79500430041 / 125000000000) : ℝ)^2) := bsq (bpoint ((79500430041 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy9_hz10 : B (595499623890948143 / 1000000000000000000) (37218726493184259 / 62500000000000000) ((1 : ℝ) - (((79500430041 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy9_hz9 (by norm_num) (by norm_num)

theorem lowEnergy9_hz11 : B (771686221135863059 / 1000000000000000000) (771686221135863061 / 1000000000000000000) (√((1 : ℝ) - (((79500430041 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy9_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy9_hz12 : B (245635353219356089 / 1000000000000000000) (245635353219356091 / 1000000000000000000) ((√((1 : ℝ) - (((79500430041 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy9_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy9_hz13 : B (457549523040318431 / 1000000000000000000) (114387380760079609 / 250000000000000000) (((79500430041 / 125000000000) : ℝ) * (kdot ((79500430041 / 125000000000)))) := bmul (bpoint ((79500430041 / 125000000000) : ℝ)) lowEnergy9_hz8 (by norm_num) (by norm_num)

theorem lowEnergy9_hz14 : B (17579621906491863 / 25000000000000000) (703184876259674527 / 1000000000000000000) (((√((1 : ℝ) - (((79500430041 / 125000000000) : ℝ)^2))) / Real.pi) + (((79500430041 / 125000000000) : ℝ) * (kdot ((79500430041 / 125000000000))))) := badd lowEnergy9_hz12 lowEnergy9_hz13 (by norm_num) (by norm_num)

theorem lowEnergy9_hz15 : B (17579621906491863 / 25000000000000000) (703184876259674527 / 1000000000000000000) (kappa ((79500430041 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy9_hz14

theorem lowEnergy9 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1071 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (353030295273 / 500000000000) := by
  have hk1 : kappa q ≤ (316448972999 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1071 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy9_hz7.2.trans (by norm_num))
  have hk2 : kappa ((79500430041 / 125000000000) : ℝ) ≤ (35159243813 / 50000000000) := lowEnergy9_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((24873173339 / 31250000000) : ℝ)) (R := ((199201893063 / 250000000000) : ℝ)) (Q2 := ((79500430041 / 125000000000) : ℝ)) (T := ((839287409403 / 1000000000000) : ℝ))
    (B := ((353030295273 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy10_hz0 : B (679688396740185101 / 1000000000000000000) (169922099185047551 / 250000000000000000) (kdot ((107 / 200))) := by
    constructor
    · apply bkdot_lower (q := (275196110115679693 / 500000000000000000)) (a := (125786072457575369 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110078444046271877 / 200000000000000000)) (a := (251572144915146731 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy10_hz1 : B (11449 / 40000) (11449 / 40000) (((107 / 200) : ℝ)^2) := bsq (bpoint ((107 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy10_hz2 : B (28551 / 40000) (28551 / 40000) ((1 : ℝ) - (((107 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy10_hz1 (by norm_num) (by norm_num)

theorem lowEnergy10_hz3 : B (52803253628446041 / 62500000000000000) (844852058055136657 / 1000000000000000000) (√((1 : ℝ) - (((107 / 200) : ℝ)^2))) := bsqrt lowEnergy10_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy10_hz4 : B (268924762441671857 / 1000000000000000000) (268924762441671859 / 1000000000000000000) ((√((1 : ℝ) - (((107 / 200) : ℝ)^2))) / Real.pi) := bdiv lowEnergy10_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy10_hz5 : B (363633292255999029 / 1000000000000000000) (2272708076600011 / 6250000000000000) (((107 / 200) : ℝ) * (kdot ((107 / 200)))) := bmul (bpoint ((107 / 200) : ℝ)) lowEnergy10_hz0 (by norm_num) (by norm_num)

theorem lowEnergy10_hz6 : B (316279027348835443 / 500000000000000000) (632558054697673619 / 1000000000000000000) (((√((1 : ℝ) - (((107 / 200) : ℝ)^2))) / Real.pi) + (((107 / 200) : ℝ) * (kdot ((107 / 200))))) := badd lowEnergy10_hz4 lowEnergy10_hz5 (by norm_num) (by norm_num)

theorem lowEnergy10_hz7 : B (316279027348835443 / 500000000000000000) (632558054697673619 / 1000000000000000000) (kappa ((107 / 200))) := by rw [kappa_eq]; exact lowEnergy10_hz6

theorem lowEnergy10_hz8 : B (359636513326734789 / 500000000000000000) (719273026653469583 / 1000000000000000000) (kdot ((635662589033 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (471959816529874069 / 1000000000000000000)) (a := (440964898564978833 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (117989954132468517 / 250000000000000000)) (a := (440964898564978827 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy10_hz9 : B (404066927096136651 / 1000000000000000000) (101016731774034163 / 250000000000000000) (((635662589033 / 1000000000000) : ℝ)^2) := bsq (bpoint ((635662589033 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy10_hz10 : B (148983268225965837 / 250000000000000000) (595933072903863349 / 1000000000000000000) ((1 : ℝ) - (((635662589033 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy10_hz9 (by norm_num) (by norm_num)

theorem lowEnergy10_hz11 : B (48247938464049593 / 62500000000000000) (77196701542479349 / 100000000000000000) (√((1 : ℝ) - (((635662589033 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy10_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy10_hz12 : B (7678897900547081 / 31250000000000000) (122862366408753297 / 500000000000000000) ((√((1 : ℝ) - (((635662589033 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy10_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy10_hz13 : B (457214954344146487 / 1000000000000000000) (457214954344146491 / 1000000000000000000) (((635662589033 / 1000000000000) : ℝ) * (kdot ((635662589033 / 1000000000000)))) := bmul (bpoint ((635662589033 / 1000000000000) : ℝ)) lowEnergy10_hz8 (by norm_num) (by norm_num)

theorem lowEnergy10_hz14 : B (702939687161653079 / 1000000000000000000) (140587937432330617 / 200000000000000000) (((√((1 : ℝ) - (((635662589033 / 1000000000000) : ℝ)^2))) / Real.pi) + (((635662589033 / 1000000000000) : ℝ) * (kdot ((635662589033 / 1000000000000))))) := badd lowEnergy10_hz12 lowEnergy10_hz13 (by norm_num) (by norm_num)

theorem lowEnergy10_hz15 : B (702939687161653079 / 1000000000000000000) (140587937432330617 / 200000000000000000) (kappa ((635662589033 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy10_hz14

theorem lowEnergy10 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (107 / 200)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (705814687803 / 1000000000000) := by
  have hk1 : kappa q ≤ (316279027349 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((107 / 200) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy10_hz7.2.trans (by norm_num))
  have hk2 : kappa ((635662589033 / 1000000000000) : ℝ) ≤ (351469843581 / 500000000000) := lowEnergy10_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((795728002963 / 1000000000000) : ℝ)) (R := ((796594028367 / 1000000000000) : ℝ)) (Q2 := ((635662589033 / 1000000000000) : ℝ)) (T := ((83914107373 / 100000000000) : ℝ))
    (B := ((705814687803 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy11_hz0 : B (339750024994444997 / 500000000000000000) (27180001999555811 / 40000000000000000) (kdot ((1069 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (275388880524350277 / 500000000000000000)) (a := (503440144215399583 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (550777761048700553 / 1000000000000000000)) (a := (503440144215391289 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy11_hz1 : B (1142761 / 4000000) (1142761 / 4000000) (((1069 / 2000) : ℝ)^2) := bsq (bpoint ((1069 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy11_hz2 : B (2857239 / 4000000) (2857239 / 4000000) ((1 : ℝ) - (((1069 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy11_hz1 (by norm_num) (by norm_num)

theorem lowEnergy11_hz3 : B (845168474329231 / 1000000000000000) (845168474329231001 / 1000000000000000000) (√((1 : ℝ) - (((1069 / 2000) : ℝ)^2))) := bsqrt lowEnergy11_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy11_hz4 : B (269025480869865527 / 1000000000000000000) (33628185108733191 / 125000000000000000) ((√((1 : ℝ) - (((1069 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy11_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy11_hz5 : B (363192776719061701 / 1000000000000000000) (14527711068762581 / 40000000000000000) (((1069 / 2000) : ℝ) * (kdot ((1069 / 2000)))) := bmul (bpoint ((1069 / 2000) : ℝ)) lowEnergy11_hz0 (by norm_num) (by norm_num)

theorem lowEnergy11_hz6 : B (158054564397231807 / 250000000000000000) (632218257588930053 / 1000000000000000000) (((√((1 : ℝ) - (((1069 / 2000) : ℝ)^2))) / Real.pi) + (((1069 / 2000) : ℝ) * (kdot ((1069 / 2000))))) := badd lowEnergy11_hz4 lowEnergy11_hz5 (by norm_num) (by norm_num)

theorem lowEnergy11_hz7 : B (158054564397231807 / 250000000000000000) (632218257588930053 / 1000000000000000000) (kappa ((1069 / 2000))) := by rw [kappa_eq]; exact lowEnergy11_hz6

theorem lowEnergy11_hz8 : B (719132545780192063 / 1000000000000000000) (179783136445048017 / 250000000000000000) (kdot ((127064366419 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (472229664148481449 / 1000000000000000000)) (a := (441185565404708093 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (59028708018560181 / 125000000000000000)) (a := (441185565404708087 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy11_hz9 : B (100908457584136843 / 250000000000000000) (403633830336547373 / 1000000000000000000) (((127064366419 / 200000000000) : ℝ)^2) := bsq (bpoint ((127064366419 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy11_hz10 : B (596366169663452627 / 1000000000000000000) (149091542415863157 / 250000000000000000) ((1 : ℝ) - (((127064366419 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy11_hz9 (by norm_num) (by norm_num)

theorem lowEnergy11_hz11 : B (772247479544901219 / 1000000000000000000) (38612373977245061 / 50000000000000000) (√((1 : ℝ) - (((127064366419 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy11_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy11_hz12 : B (245814007319656721 / 1000000000000000000) (245814007319656723 / 1000000000000000000) ((√((1 : ℝ) - (((127064366419 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy11_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy11_hz13 : B (228440303252106541 / 500000000000000000) (228440303252106543 / 500000000000000000) (((127064366419 / 200000000000) : ℝ) * (kdot ((127064366419 / 200000000000)))) := bmul (bpoint ((127064366419 / 200000000000) : ℝ)) lowEnergy11_hz8 (by norm_num) (by norm_num)

theorem lowEnergy11_hz14 : B (702694613823869803 / 1000000000000000000) (702694613823869809 / 1000000000000000000) (((√((1 : ℝ) - (((127064366419 / 200000000000) : ℝ)^2))) / Real.pi) + (((127064366419 / 200000000000) : ℝ) * (kdot ((127064366419 / 200000000000))))) := badd lowEnergy11_hz12 lowEnergy11_hz13 (by norm_num) (by norm_num)

theorem lowEnergy11_hz15 : B (702694613823869803 / 1000000000000000000) (702694613823869809 / 1000000000000000000) (kappa ((127064366419 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy11_hz14

theorem lowEnergy11 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1069 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (705568901107 / 1000000000000) := by
  have hk1 : kappa q ≤ (632218257589 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1069 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy11_hz7.2.trans (by norm_num))
  have hk2 : kappa ((127064366419 / 200000000000) : ℝ) ≤ (10979603341 / 15625000000) := lowEnergy11_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((198878615239 / 250000000000) : ℝ)) (R := ((19909512159 / 25000000000) : ℝ)) (Q2 := ((127064366419 / 200000000000) : ℝ)) (T := ((20974869541 / 25000000000) : ℝ))
    (B := ((705568901107 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy12_hz0 : B (135862354738400523 / 200000000000000000) (8491397171150101 / 12500000000000000) (kdot ((267 / 500))) := by
    constructor
    · apply bkdot_lower (q := (34447705202841181 / 62500000000000000)) (a := (503735887930972823 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110232656649091779 / 200000000000000000)) (a := (6296698599137053 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy12_hz1 : B (71289 / 250000) (71289 / 250000) (((267 / 500) : ℝ)^2) := bsq (bpoint ((267 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy12_hz2 : B (178711 / 250000) (178711 / 250000) ((1 : ℝ) - (((267 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy12_hz1 (by norm_num) (by norm_num)

theorem lowEnergy12_hz3 : B (169096895299706789 / 200000000000000000) (422742238249266973 / 500000000000000000) (√((1 : ℝ) - (((267 / 500) : ℝ)^2))) := bsqrt lowEnergy12_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy12_hz4 : B (134563033742205089 / 500000000000000000) (13456303374220509 / 50000000000000000) ((√((1 : ℝ) - (((267 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy12_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy12_hz5 : B (90688121787882349 / 250000000000000000) (72550497430306463 / 200000000000000000) (((267 / 500) : ℝ) * (kdot ((267 / 500)))) := bmul (bpoint ((267 / 500) : ℝ)) lowEnergy12_hz0 (by norm_num) (by norm_num)

theorem lowEnergy12_hz6 : B (315939277317969787 / 500000000000000000) (126375710927188499 / 200000000000000000) (((√((1 : ℝ) - (((267 / 500) : ℝ)^2))) / Real.pi) + (((267 / 500) : ℝ) * (kdot ((267 / 500))))) := badd lowEnergy12_hz4 lowEnergy12_hz5 (by norm_num) (by norm_num)

theorem lowEnergy12_hz7 : B (315939277317969787 / 500000000000000000) (126375710927188499 / 200000000000000000) (kappa ((267 / 500))) := by rw [kappa_eq]; exact lowEnergy12_hz6

theorem lowEnergy12_hz8 : B (89874019344823189 / 125000000000000000) (718992154758585517 / 1000000000000000000) (kdot ((634981169479 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (236249697681713467 / 500000000000000000)) (a := (220703045552881323 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (472499395363426933 / 1000000000000000000)) (a := (5517576138822033 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy12_hz9 : B (403201085592918521 / 1000000000000000000) (201600542796459261 / 500000000000000000) (((634981169479 / 1000000000000) : ℝ)^2) := bsq (bpoint ((634981169479 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy12_hz10 : B (298399457203540739 / 500000000000000000) (596798914407081479 / 1000000000000000000) ((1 : ℝ) - (((634981169479 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy12_hz9 (by norm_num) (by norm_num)

theorem lowEnergy12_hz11 : B (193131903502354039 / 250000000000000000) (386263807004708079 / 500000000000000000) (√((1 : ℝ) - (((634981169479 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy12_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy12_hz12 : B (61475794222293157 / 250000000000000000) (24590317688917263 / 100000000000000000) ((√((1 : ℝ) - (((634981169479 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy12_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy12_hz13 : B (456546479274832783 / 1000000000000000000) (456546479274832787 / 1000000000000000000) (((634981169479 / 1000000000000) : ℝ) * (kdot ((634981169479 / 1000000000000)))) := bmul (bpoint ((634981169479 / 1000000000000) : ℝ)) lowEnergy12_hz8 (by norm_num) (by norm_num)

theorem lowEnergy12_hz14 : B (702449656164005411 / 1000000000000000000) (702449656164005417 / 1000000000000000000) (((√((1 : ℝ) - (((634981169479 / 1000000000000) : ℝ)^2))) / Real.pi) + (((634981169479 / 1000000000000) : ℝ) * (kdot ((634981169479 / 1000000000000))))) := badd lowEnergy12_hz12 lowEnergy12_hz13 (by norm_num) (by norm_num)

theorem lowEnergy12_hz15 : B (702449656164005411 / 1000000000000000000) (702449656164005417 / 1000000000000000000) (kappa ((634981169479 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy12_hz14

theorem lowEnergy12 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (267 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (88165403797 / 125000000000) := by
  have hk1 : kappa q ≤ (157969638659 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((267 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy12_hz7.2.trans (by norm_num))
  have hk2 : kappa ((634981169479 / 1000000000000) : ℝ) ≤ (140489931233 / 200000000000) := lowEnergy12_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((795300920807 / 1000000000000) : ℝ)) (R := ((796166946211 / 1000000000000) : ℝ)) (Q2 := ((634981169479 / 1000000000000) : ℝ)) (T := ((209712133277 / 250000000000) : ℝ))
    (B := ((88165403797 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy13_hz0 : B (217319541665511 / 320000000000000) (67912356770472753 / 100000000000000000) (kdot ((1067 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (551548787106091093 / 1000000000000000000)) (a := (504031521204474217 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (137887196776522773 / 250000000000000000)) (a := (100806304240893067 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy13_hz1 : B (1138489 / 4000000) (1138489 / 4000000) (((1067 / 2000) : ℝ)^2) := bsq (bpoint ((1067 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy13_hz2 : B (2861511 / 4000000) (2861511 / 4000000) ((1 : ℝ) - (((1067 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy13_hz1 (by norm_num) (by norm_num)

theorem lowEnergy13_hz3 : B (84580006502719069 / 100000000000000000) (845800065027190691 / 1000000000000000000) (√((1 : ℝ) - (((1067 / 2000) : ℝ)^2))) := bsqrt lowEnergy13_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy13_hz4 : B (269226522433047817 / 1000000000000000000) (134613261216523909 / 500000000000000000) ((√((1 : ℝ) - (((1067 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy13_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy13_hz5 : B (283056580758179 / 781250000000000) (181156211685236069 / 500000000000000000) (((1067 / 2000) : ℝ) * (kdot ((1067 / 2000)))) := bmul (bpoint ((1067 / 2000) : ℝ)) lowEnergy13_hz0 (by norm_num) (by norm_num)

theorem lowEnergy13_hz6 : B (631538945803516937 / 1000000000000000000) (157884736450879989 / 250000000000000000) (((√((1 : ℝ) - (((1067 / 2000) : ℝ)^2))) / Real.pi) + (((1067 / 2000) : ℝ) * (kdot ((1067 / 2000))))) := badd lowEnergy13_hz4 lowEnergy13_hz5 (by norm_num) (by norm_num)

theorem lowEnergy13_hz7 : B (631538945803516937 / 1000000000000000000) (157884736450879989 / 250000000000000000) (kappa ((1067 / 2000))) := by rw [kappa_eq]; exact lowEnergy13_hz6

theorem lowEnergy13_hz8 : B (718851853449228107 / 1000000000000000000) (44928240840576757 / 62500000000000000) (kdot ((12692812023 / 20000000000))) := by
    constructor
    · apply bkdot_lower (q := (118192252594640853 / 250000000000000000)) (a := (110406618971786443 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (472769010378563411 / 1000000000000000000)) (a := (220813237943572883 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy13_hz9 : B (402768692628033381 / 1000000000000000000) (201384346314016691 / 500000000000000000) (((12692812023 / 20000000000) : ℝ)^2) := bsq (bpoint ((12692812023 / 20000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy13_hz10 : B (298615653685983309 / 500000000000000000) (597231307371966619 / 1000000000000000000) ((1 : ℝ) - (((12692812023 / 20000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy13_hz9 (by norm_num) (by norm_num)

theorem lowEnergy13_hz11 : B (772807419330305483 / 1000000000000000000) (154561483866061097 / 200000000000000000) (√((1 : ℝ) - (((12692812023 / 20000000000) : ℝ)^2))) := bsqrt lowEnergy13_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy13_hz12 : B (245992241689018529 / 1000000000000000000) (24599224168901853 / 100000000000000000) ((√((1 : ℝ) - (((12692812023 / 20000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy13_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy13_hz13 : B (228106286205404913 / 500000000000000000) (456212572410809831 / 1000000000000000000) (((12692812023 / 20000000000) : ℝ) * (kdot ((12692812023 / 20000000000)))) := bmul (bpoint ((12692812023 / 20000000000) : ℝ)) lowEnergy13_hz8 (by norm_num) (by norm_num)

theorem lowEnergy13_hz14 : B (140440962819965671 / 200000000000000000) (702204814099828361 / 1000000000000000000) (((√((1 : ℝ) - (((12692812023 / 20000000000) : ℝ)^2))) / Real.pi) + (((12692812023 / 20000000000) : ℝ) * (kdot ((12692812023 / 20000000000))))) := badd lowEnergy13_hz12 lowEnergy13_hz13 (by norm_num) (by norm_num)

theorem lowEnergy13_hz15 : B (140440962819965671 / 200000000000000000) (702204814099828361 / 1000000000000000000) (kappa ((12692812023 / 20000000000))) := by rw [kappa_eq]; exact lowEnergy13_hz14

theorem lowEnergy13 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1067 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (352538837763 / 500000000000) := by
  have hk1 : kappa q ≤ (157884736451 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1067 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy13_hz7.2.trans (by norm_num))
  have hk2 : kappa ((12692812023 / 20000000000) : ℝ) ≤ (7022048141 / 10000000000) := lowEnergy13_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((24846480703 / 31250000000) : ℝ)) (R := ((7959534079 / 10000000000) : ℝ)) (Q2 := ((12692812023 / 20000000000) : ℝ)) (T := ((419351164053 / 500000000000) : ℝ))
    (B := ((352538837763 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy14_hz0 : B (678935431882615119 / 1000000000000000000) (169733857970655243 / 250000000000000000) (kdot ((533 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (551934272914577201 / 1000000000000000000)) (a := (504327044262778047 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1379835682286443 / 2500000000000000)) (a := (100865408852553771 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy14_hz1 : B (284089 / 1000000) (284089 / 1000000) (((533 / 1000) : ℝ)^2) := bsq (bpoint ((533 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy14_hz2 : B (715911 / 1000000) (715911 / 1000000) ((1 : ℝ) - (((533 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy14_hz1 (by norm_num) (by norm_num)

theorem lowEnergy14_hz3 : B (6610275315453491 / 7812500000000000) (846115240378046849 / 1000000000000000000) (√((1 : ℝ) - (((533 / 1000) : ℝ)^2))) := bsqrt lowEnergy14_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy14_hz4 : B (269326845863106777 / 1000000000000000000) (134663422931553389 / 500000000000000000) ((√((1 : ℝ) - (((533 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy14_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy14_hz5 : B (180936292596716929 / 500000000000000000) (361872585193436979 / 1000000000000000000) (((533 / 1000) : ℝ) * (kdot ((533 / 1000)))) := bmul (bpoint ((533 / 1000) : ℝ)) lowEnergy14_hz0 (by norm_num) (by norm_num)

theorem lowEnergy14_hz6 : B (126239886211308127 / 200000000000000000) (631199431056543757 / 1000000000000000000) (((√((1 : ℝ) - (((533 / 1000) : ℝ)^2))) / Real.pi) + (((533 / 1000) : ℝ) * (kdot ((533 / 1000))))) := badd lowEnergy14_hz4 lowEnergy14_hz5 (by norm_num) (by norm_num)

theorem lowEnergy14_hz7 : B (126239886211308127 / 200000000000000000) (631199431056543757 / 1000000000000000000) (kappa ((533 / 1000))) := by rw [kappa_eq]; exact lowEnergy14_hz6

theorem lowEnergy14_hz8 : B (8983895521418359 / 12500000000000000) (359355820856734363 / 500000000000000000) (kdot ((317150063537 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (473038509396415687 / 1000000000000000000)) (a := (220923359983325077 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (236519254698207843 / 500000000000000000)) (a := (441846719966650147 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy14_hz9 : B (402336651206092547 / 1000000000000000000) (100584162801523137 / 250000000000000000) (((317150063537 / 500000000000) : ℝ)^2) := bsq (bpoint ((317150063537 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy14_hz10 : B (149415837198476863 / 250000000000000000) (597663348793907453 / 1000000000000000000) ((1 : ℝ) - (((317150063537 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy14_hz9 (by norm_num) (by norm_num)

theorem lowEnergy14_hz11 : B (386543448008728849 / 500000000000000000) (7730868960174577 / 10000000000000000) (√((1 : ℝ) - (((317150063537 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy14_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy14_hz12 : B (246081201881496973 / 1000000000000000000) (9843248075259879 / 40000000000000000) ((√((1 : ℝ) - (((317150063537 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy14_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy14_hz13 : B (28492430354276023 / 62500000000000000) (113969721417104093 / 250000000000000000) (((317150063537 / 500000000000) : ℝ) * (kdot ((317150063537 / 500000000000)))) := bmul (bpoint ((317150063537 / 500000000000) : ℝ)) lowEnergy14_hz8 (by norm_num) (by norm_num)

theorem lowEnergy14_hz14 : B (701960087549913341 / 1000000000000000000) (701960087549913347 / 1000000000000000000) (((√((1 : ℝ) - (((317150063537 / 500000000000) : ℝ)^2))) / Real.pi) + (((317150063537 / 500000000000) : ℝ) * (kdot ((317150063537 / 500000000000))))) := badd lowEnergy14_hz12 lowEnergy14_hz13 (by norm_num) (by norm_num)

theorem lowEnergy14_hz15 : B (701960087549913341 / 1000000000000000000) (701960087549913347 / 1000000000000000000) (kappa ((317150063537 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy14_hz14

theorem lowEnergy14 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (533 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (704832236477 / 1000000000000) := by
  have hk1 : kappa q ≤ (631199431057 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((533 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy14_hz7.2.trans (by norm_num))
  have hk2 : kappa ((317150063537 / 500000000000) : ℝ) ≤ (14039201751 / 20000000000) := lowEnergy14_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((397436923001 / 500000000000) : ℝ)) (R := ((397869935703 / 500000000000) : ℝ)) (Q2 := ((317150063537 / 500000000000) : ℝ)) (T := ((838556166609 / 1000000000000) : ℝ))
    (B := ((704832236477 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy15_hz0 : B (84843420760202089 / 125000000000000000) (42421710380101423 / 62500000000000000) (kdot ((213 / 400))) := by
    constructor
    · apply bkdot_lower (q := (552319740954422929 / 1000000000000000000)) (a := (126155614333045521 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (34519983809651433 / 62500000000000000)) (a := (504622457332172573 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy15_hz1 : B (45369 / 160000) (45369 / 160000) (((213 / 400) : ℝ)^2) := bsq (bpoint ((213 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy15_hz2 : B (114631 / 160000) (114631 / 160000) ((1 : ℝ) - (((213 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy15_hz1 (by norm_num) (by norm_num)

theorem lowEnergy15_hz3 : B (846430003012653137 / 1000000000000000000) (423215001506326569 / 500000000000000000) (√((1 : ℝ) - (((213 / 400) : ℝ)^2))) := bsqrt lowEnergy15_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy15_hz4 : B (53885407584300643 / 200000000000000000) (16839189870093951 / 62500000000000000) ((√((1 : ℝ) - (((213 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy15_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy15_hz5 : B (361432972438460899 / 1000000000000000000) (90358243109616031 / 250000000000000000) (((213 / 400) : ℝ) * (kdot ((213 / 400)))) := bmul (bpoint ((213 / 400) : ℝ)) lowEnergy15_hz0 (by norm_num) (by norm_num)

theorem lowEnergy15_hz6 : B (315430005179982057 / 500000000000000000) (31543000517998367 / 50000000000000000) (((√((1 : ℝ) - (((213 / 400) : ℝ)^2))) / Real.pi) + (((213 / 400) : ℝ) * (kdot ((213 / 400))))) := badd lowEnergy15_hz4 lowEnergy15_hz5 (by norm_num) (by norm_num)

theorem lowEnergy15_hz7 : B (315430005179982057 / 500000000000000000) (31543000517998367 / 50000000000000000) (kappa ((213 / 400))) := by rw [kappa_eq]; exact lowEnergy15_hz6

theorem lowEnergy15_hz8 : B (718571519411366883 / 1000000000000000000) (89821439926420861 / 125000000000000000) (kdot ((633959747213 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (473307892622139919 / 1000000000000000000)) (a := (110516705891023441 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (236653946311069959 / 500000000000000000)) (a := (221033411782046879 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy15_hz9 : B (401904961086370861 / 1000000000000000000) (200952480543185431 / 500000000000000000) (((633959747213 / 1000000000000) : ℝ)^2) := bsq (bpoint ((633959747213 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy15_hz10 : B (299047519456814569 / 500000000000000000) (598095038913629139 / 1000000000000000000) ((1 : ℝ) - (((633959747213 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy15_hz9 (by norm_num) (by norm_num)

theorem lowEnergy15_hz11 : B (48335377786424343 / 62500000000000000) (773366044582789489 / 1000000000000000000) (√((1 : ℝ) - (((633959747213 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy15_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy15_hz12 : B (30771257203694513 / 125000000000000000) (49234011525911221 / 200000000000000000) ((√((1 : ℝ) - (((633959747213 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy15_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy15_hz13 : B (455545418800491471 / 1000000000000000000) (18221816752019659 / 40000000000000000) (((633959747213 / 1000000000000) : ℝ) * (kdot ((633959747213 / 1000000000000)))) := bmul (bpoint ((633959747213 / 1000000000000) : ℝ)) lowEnergy15_hz8 (by norm_num) (by norm_num)

theorem lowEnergy15_hz14 : B (28068619057201903 / 40000000000000000) (35085773821502379 / 50000000000000000) (((√((1 : ℝ) - (((633959747213 / 1000000000000) : ℝ)^2))) / Real.pi) + (((633959747213 / 1000000000000) : ℝ) * (kdot ((633959747213 / 1000000000000))))) := badd lowEnergy15_hz12 lowEnergy15_hz13 (by norm_num) (by norm_num)

theorem lowEnergy15_hz15 : B (28068619057201903 / 40000000000000000) (35085773821502379 / 50000000000000000) (kappa ((633959747213 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy15_hz14

theorem lowEnergy15 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (213 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (88073364143 / 125000000000) := by
  have hk1 : kappa q ≤ (15771500259 / 25000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((213 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy15_hz7.2.trans (by norm_num))
  have hk2 : kappa ((633959747213 / 1000000000000) : ℝ) ≤ (701715476431 / 1000000000000) := lowEnergy15_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((794660311303 / 1000000000000) : ℝ)) (R := ((795526336707 / 1000000000000) : ℝ)) (Q2 := ((633959747213 / 1000000000000) : ℝ)) (T := ((83841004859 / 100000000000) : ℝ))
    (B := ((88073364143 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy16_hz0 : B (678559370158026631 / 1000000000000000000) (678559370158032899 / 1000000000000000000) (kdot ((133 / 250))) := by
    constructor
    · apply bkdot_lower (q := (110541038301732381 / 200000000000000000)) (a := (504917760638409797 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (34544074469291369 / 62500000000000000)) (a := (252458880319199977 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy16_hz1 : B (17689 / 62500) (17689 / 62500) (((133 / 250) : ℝ)^2) := bsq (bpoint ((133 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy16_hz2 : B (44811 / 62500) (44811 / 62500) ((1 : ℝ) - (((133 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy16_hz1 (by norm_num) (by norm_num)

theorem lowEnergy16_hz3 : B (423372176695635019 / 500000000000000000) (846744353391270039 / 1000000000000000000) (√((1 : ℝ) - (((133 / 250) : ℝ)^2))) := bsqrt lowEnergy16_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy16_hz4 : B (4211360918042853 / 15625000000000000) (269527098754742593 / 1000000000000000000) ((√((1 : ℝ) - (((133 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy16_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy16_hz5 : B (360993584924070167 / 1000000000000000000) (360993584924073503 / 1000000000000000000) (((133 / 250) : ℝ) * (kdot ((133 / 250)))) := bmul (bpoint ((133 / 250) : ℝ)) lowEnergy16_hz0 (by norm_num) (by norm_num)

theorem lowEnergy16_hz6 : B (630520683678812759 / 1000000000000000000) (19703771364963003 / 31250000000000000) (((√((1 : ℝ) - (((133 / 250) : ℝ)^2))) / Real.pi) + (((133 / 250) : ℝ) * (kdot ((133 / 250))))) := badd lowEnergy16_hz4 lowEnergy16_hz5 (by norm_num) (by norm_num)

theorem lowEnergy16_hz7 : B (630520683678812759 / 1000000000000000000) (19703771364963003 / 31250000000000000) (kappa ((133 / 250))) := by rw [kappa_eq]; exact lowEnergy16_hz6

theorem lowEnergy16_hz8 : B (359215743202904419 / 500000000000000000) (718431486405808843 / 1000000000000000000) (kdot ((126723892307 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (473577160255610869 / 1000000000000000000)) (a := (442286786894854391 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (118394290063902717 / 250000000000000000)) (a := (27642924180928399 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy16_hz9 : B (25092101377243959 / 62500000000000000) (80294724407180669 / 200000000000000000) (((126723892307 / 200000000000) : ℝ)^2) := bsq (bpoint ((126723892307 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy16_hz10 : B (119705275592819331 / 200000000000000000) (37407898622756041 / 62500000000000000) ((1 : ℝ) - (((126723892307 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy16_hz9 (by norm_num) (by norm_num)

theorem lowEnergy16_hz11 : B (773644865532045429 / 1000000000000000000) (773644865532045431 / 1000000000000000000) (√((1 : ℝ) - (((126723892307 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy16_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy16_hz12 : B (246258809094179419 / 1000000000000000000) (12312940454708971 / 50000000000000000) ((√((1 : ℝ) - (((126723892307 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy16_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy16_hz13 : B (113803042891559567 / 250000000000000000) (7112690180722473 / 15625000000000000) (((126723892307 / 200000000000) : ℝ) * (kdot ((126723892307 / 200000000000)))) := bmul (bpoint ((126723892307 / 200000000000) : ℝ)) lowEnergy16_hz8 (by norm_num) (by norm_num)

theorem lowEnergy16_hz14 : B (701470980660417687 / 1000000000000000000) (175367745165104423 / 250000000000000000) (((√((1 : ℝ) - (((126723892307 / 200000000000) : ℝ)^2))) / Real.pi) + (((126723892307 / 200000000000) : ℝ) * (kdot ((126723892307 / 200000000000))))) := badd lowEnergy16_hz12 lowEnergy16_hz13 (by norm_num) (by norm_num)

theorem lowEnergy16_hz15 : B (701470980660417687 / 1000000000000000000) (175367745165104423 / 250000000000000000) (kappa ((126723892307 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy16_hz14

theorem lowEnergy16 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (133 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (140868341089 / 200000000000) := by
  have hk1 : kappa q ≤ (630520683679 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((133 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy16_hz7.2.trans (by norm_num))
  have hk2 : kappa ((126723892307 / 200000000000) : ℝ) ≤ (701470980661 / 1000000000000) := lowEnergy16_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((794446778381 / 1000000000000) : ℝ)) (R := ((159062560757 / 200000000000) : ℝ)) (Q2 := ((126723892307 / 200000000000) : ℝ)) (T := ((419131987011 / 500000000000) : ℝ))
    (B := ((140868341089 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy17_hz0 : B (678371443968509063 / 1000000000000000000) (678371443968515547 / 1000000000000000000) (kdot ((1063 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (276545312429928969 / 500000000000000000)) (a := (101042590881322511 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (553090624859857937 / 1000000000000000000)) (a := (505212954406602371 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy17_hz1 : B (1129969 / 4000000) (1129969 / 4000000) (((1063 / 2000) : ℝ)^2) := bsq (bpoint ((1063 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy17_hz2 : B (2870031 / 4000000) (2870031 / 4000000) ((1 : ℝ) - (((1063 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy17_hz1 (by norm_num) (by norm_num)

theorem lowEnergy17_hz3 : B (847058291972872431 / 1000000000000000000) (52941143248304527 / 62500000000000000) (√((1 : ℝ) - (((1063 / 2000) : ℝ)^2))) := bsqrt lowEnergy17_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy17_hz4 : B (5392540570178423 / 20000000000000000) (4212922320451893 / 15625000000000000) ((√((1 : ℝ) - (((1063 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy17_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy17_hz5 : B (180277211234631283 / 500000000000000000) (180277211234633007 / 500000000000000000) (((1063 / 2000) : ℝ) * (kdot ((1063 / 2000)))) := bmul (bpoint ((1063 / 2000) : ℝ)) lowEnergy17_hz0 (by norm_num) (by norm_num)

theorem lowEnergy17_hz6 : B (157545362744545929 / 250000000000000000) (315090725489093583 / 500000000000000000) (((√((1 : ℝ) - (((1063 / 2000) : ℝ)^2))) / Real.pi) + (((1063 / 2000) : ℝ) * (kdot ((1063 / 2000))))) := badd lowEnergy17_hz4 lowEnergy17_hz5 (by norm_num) (by norm_num)

theorem lowEnergy17_hz7 : B (157545362744545929 / 250000000000000000) (315090725489093583 / 500000000000000000) (kappa ((1063 / 2000))) := by rw [kappa_eq]; exact lowEnergy17_hz6

theorem lowEnergy17_hz8 : B (359145771279194413 / 500000000000000000) (22446610704949651 / 31250000000000000) (kdot ((158319817501 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (473846312499338723 / 1000000000000000000)) (a := (442506610176339291 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (236923156249669361 / 500000000000000000)) (a := (110626652544084821 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy17_hz9 : B (200521316908399567 / 500000000000000000) (80208526763359827 / 200000000000000000) (((158319817501 / 250000000000) : ℝ)^2) := bsq (bpoint ((158319817501 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy17_hz10 : B (119791473236640173 / 200000000000000000) (299478683091600433 / 500000000000000000) ((1 : ℝ) - (((158319817501 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy17_hz9 (by norm_num) (by norm_num)

theorem lowEnergy17_hz11 : B (96740419921625901 / 125000000000000000) (77392335937300721 / 100000000000000000) (√((1 : ℝ) - (((158319817501 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy17_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy17_hz12 : B (246347456436998849 / 1000000000000000000) (246347456436998851 / 1000000000000000000) ((√((1 : ℝ) - (((158319817501 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy17_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy17_hz13 : B (227439571860711787 / 500000000000000000) (454879143721423579 / 1000000000000000000) (((158319817501 / 250000000000) : ℝ) * (kdot ((158319817501 / 250000000000)))) := bmul (bpoint ((158319817501 / 250000000000) : ℝ)) lowEnergy17_hz8 (by norm_num) (by norm_num)

theorem lowEnergy17_hz14 : B (701226600158422423 / 1000000000000000000) (70122660015842243 / 100000000000000000) (((√((1 : ℝ) - (((158319817501 / 250000000000) : ℝ)^2))) / Real.pi) + (((158319817501 / 250000000000) : ℝ) * (kdot ((158319817501 / 250000000000))))) := badd lowEnergy17_hz12 lowEnergy17_hz13 (by norm_num) (by norm_num)

theorem lowEnergy17_hz15 : B (701226600158422423 / 1000000000000000000) (70122660015842243 / 100000000000000000) (kappa ((158319817501 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy17_hz14

theorem lowEnergy17 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1063 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (704096613301 / 1000000000000) := by
  have hk1 : kappa q ≤ (630181450979 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1063 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy17_hz7.2.trans (by norm_num))
  have hk2 : kappa ((158319817501 / 250000000000) : ℝ) ≤ (701226600159 / 1000000000000) := lowEnergy17_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((397116623607 / 500000000000) : ℝ)) (R := ((397549636309 / 500000000000) : ℝ)) (Q2 := ((158319817501 / 250000000000) : ℝ)) (T := ((838117942881 / 1000000000000) : ℝ))
    (B := ((704096613301 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy18_hz0 : B (678183587370091009 / 1000000000000000000) (339091793685048859 / 500000000000000000) (kdot ((531 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (553476041290107261 / 1000000000000000000)) (a := (252754019430685909 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (27673802064505363 / 50000000000000000)) (a := (505508038861361281 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy18_hz1 : B (281961 / 1000000) (281961 / 1000000) (((531 / 1000) : ℝ)^2) := bsq (bpoint ((531 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy18_hz2 : B (718039 / 1000000) (718039 / 1000000) ((1 : ℝ) - (((531 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy18_hz1 (by norm_num) (by norm_num)

theorem lowEnergy18_hz3 : B (105921477401894277 / 125000000000000000) (847371819215154217 / 1000000000000000000) (√((1 : ℝ) - (((531 / 1000) : ℝ)^2))) := bsqrt lowEnergy18_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy18_hz4 : B (269726827329727383 / 1000000000000000000) (33715853416215923 / 125000000000000000) ((√((1 : ℝ) - (((531 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy18_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy18_hz5 : B (14404619395740733 / 40000000000000000) (360115484893521889 / 1000000000000000000) (((531 / 1000) : ℝ) * (kdot ((531 / 1000)))) := bmul (bpoint ((531 / 1000) : ℝ)) lowEnergy18_hz0 (by norm_num) (by norm_num)

theorem lowEnergy18_hz6 : B (157460578055811427 / 250000000000000000) (629842312223249273 / 1000000000000000000) (((√((1 : ℝ) - (((531 / 1000) : ℝ)^2))) / Real.pi) + (((531 / 1000) : ℝ) * (kdot ((531 / 1000))))) := badd lowEnergy18_hz4 lowEnergy18_hz5 (by norm_num) (by norm_num)

theorem lowEnergy18_hz7 : B (157460578055811427 / 250000000000000000) (629842312223249273 / 1000000000000000000) (kappa ((531 / 1000))) := by rw [kappa_eq]; exact lowEnergy18_hz6

theorem lowEnergy18_hz8 : B (143630337546211063 / 200000000000000000) (17953792193276383 / 25000000000000000) (kdot ((79117396573 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (474115349555304707 / 1000000000000000000)) (a := (88545258725079861 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (237057674777652353 / 500000000000000000)) (a := (221363146812699649 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy18_hz9 : B (400611996191318537 / 1000000000000000000) (200305998095659269 / 500000000000000000) (((79117396573 / 125000000000) : ℝ)^2) := bsq (bpoint ((79117396573 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy18_hz10 : B (299694001904340731 / 500000000000000000) (599388003808681463 / 1000000000000000000) ((1 : ℝ) - (((79117396573 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy18_hz9 (by norm_num) (by norm_num)

theorem lowEnergy18_hz11 : B (387100763306106599 / 500000000000000000) (1935503816530533 / 2500000000000000) (√((1 : ℝ) - (((79117396573 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy18_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy18_hz12 : B (246435999819250567 / 1000000000000000000) (246435999819250569 / 1000000000000000000) ((√((1 : ℝ) - (((79117396573 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy18_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy18_hz13 : B (90909267004459459 / 200000000000000000) (454546335022297299 / 1000000000000000000) (((79117396573 / 125000000000) : ℝ) * (kdot ((79117396573 / 125000000000)))) := bmul (bpoint ((79117396573 / 125000000000) : ℝ)) lowEnergy18_hz8 (by norm_num) (by norm_num)

theorem lowEnergy18_hz14 : B (350491167420773931 / 500000000000000000) (175245583710386967 / 250000000000000000) (((√((1 : ℝ) - (((79117396573 / 125000000000) : ℝ)^2))) / Real.pi) + (((79117396573 / 125000000000) : ℝ) * (kdot ((79117396573 / 125000000000))))) := badd lowEnergy18_hz12 lowEnergy18_hz13 (by norm_num) (by norm_num)

theorem lowEnergy18_hz15 : B (350491167420773931 / 500000000000000000) (175245583710386967 / 250000000000000000) (kappa ((79117396573 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy18_hz14

theorem lowEnergy18 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (531 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (703851636627 / 1000000000000) := by
  have hk1 : kappa q ≤ (19682572257 / 31250000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((531 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy18_hz7.2.trans (by norm_num))
  have hk2 : kappa ((79117396573 / 125000000000) : ℝ) ≤ (350491167421 / 500000000000) := lowEnergy18_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((794019717781 / 1000000000000) : ℝ)) (R := ((158977148637 / 200000000000) : ℝ)) (Q2 := ((79117396573 / 125000000000) : ℝ)) (T := ((837971955139 / 1000000000000) : ℝ))
    (B := ((703851636627 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy19_hz0 : B (677995800220160897 / 1000000000000000000) (4237473751376049 / 6250000000000000) (kdot ((1061 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (276930720540520387 / 500000000000000000)) (a := (505803014226701321 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (553861441081040773 / 1000000000000000000)) (a := (505803014226690417 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy19_hz1 : B (1125721 / 4000000) (1125721 / 4000000) (((1061 / 2000) : ℝ)^2) := bsq (bpoint ((1061 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy19_hz2 : B (2874279 / 4000000) (2874279 / 4000000) ((1 : ℝ) - (((1061 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy19_hz1 (by norm_num) (by norm_num)

theorem lowEnergy19_hz3 : B (847684935574532903 / 1000000000000000000) (105960616946816613 / 125000000000000000) (√((1 : ℝ) - (((1061 / 2000) : ℝ)^2))) := bsqrt lowEnergy19_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy19_hz4 : B (33728311920305437 / 125000000000000000) (269826495362443497 / 1000000000000000000) ((√((1 : ℝ) - (((1061 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy19_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy19_hz5 : B (71935354403359071 / 200000000000000000) (1123989912552497 / 3125000000000000) (((1061 / 2000) : ℝ) * (kdot ((1061 / 2000)))) := bmul (bpoint ((1061 / 2000) : ℝ)) lowEnergy19_hz0 (by norm_num) (by norm_num)

theorem lowEnergy19_hz6 : B (629503267379238851 / 1000000000000000000) (629503267379242537 / 1000000000000000000) (((√((1 : ℝ) - (((1061 / 2000) : ℝ)^2))) / Real.pi) + (((1061 / 2000) : ℝ) * (kdot ((1061 / 2000))))) := badd lowEnergy19_hz4 lowEnergy19_hz5 (by norm_num) (by norm_num)

theorem lowEnergy19_hz7 : B (629503267379238851 / 1000000000000000000) (629503267379242537 / 1000000000000000000) (kappa ((1061 / 2000))) := by rw [kappa_eq]; exact lowEnergy19_hz6

theorem lowEnergy19_hz8 : B (17950298044663017 / 25000000000000000) (359005960893260343 / 500000000000000000) (kdot ((15814979231 / 25000000000))) := by
    constructor
    · apply bkdot_lower (q := (237192135812086111 / 500000000000000000)) (a := (27684114841105333 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (474384271624172221 / 1000000000000000000)) (a := (442945837457685321 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy19_hz9 : B (200090854461569081 / 500000000000000000) (400181708923138163 / 1000000000000000000) (((15814979231 / 25000000000) : ℝ)^2) := bsq (bpoint ((15814979231 / 25000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy19_hz10 : B (599818291076861837 / 1000000000000000000) (299909145538430919 / 500000000000000000) ((1 : ℝ) - (((15814979231 / 25000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy19_hz9 (by norm_num) (by norm_num)

theorem lowEnergy19_hz11 : B (774479367754146073 / 1000000000000000000) (30979174710165843 / 40000000000000000) (√((1 : ℝ) - (((15814979231 / 25000000000) : ℝ)^2))) := bsqrt lowEnergy19_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy19_hz12 : B (49304887880303279 / 200000000000000000) (246524439401516397 / 1000000000000000000) ((√((1 : ℝ) - (((15814979231 / 25000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy19_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy19_hz13 : B (227106872613284419 / 500000000000000000) (454213745226568843 / 1000000000000000000) (((15814979231 / 25000000000) : ℝ) * (kdot ((15814979231 / 25000000000)))) := bmul (bpoint ((15814979231 / 25000000000) : ℝ)) lowEnergy19_hz8 (by norm_num) (by norm_num)

theorem lowEnergy19_hz14 : B (700738184628085233 / 1000000000000000000) (17518454615702131 / 25000000000000000) (((√((1 : ℝ) - (((15814979231 / 25000000000) : ℝ)^2))) / Real.pi) + (((15814979231 / 25000000000) : ℝ) * (kdot ((15814979231 / 25000000000))))) := badd lowEnergy19_hz12 lowEnergy19_hz13 (by norm_num) (by norm_num)

theorem lowEnergy19_hz15 : B (700738184628085233 / 1000000000000000000) (17518454615702131 / 25000000000000000) (kappa ((15814979231 / 25000000000))) := by rw [kappa_eq]; exact lowEnergy19_hz14

theorem lowEnergy19 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1061 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (351803387671 / 500000000000) := by
  have hk1 : kappa q ≤ (31475163369 / 50000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1061 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy19_hz7.2.trans (by norm_num))
  have hk2 : kappa ((15814979231 / 25000000000) : ℝ) ≤ (700738184629 / 1000000000000) := lowEnergy19_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((396903095031 / 500000000000) : ℝ)) (R := ((397336107733 / 500000000000) : ℝ)) (Q2 := ((15814979231 / 25000000000) : ℝ)) (T := ((83782601077 / 100000000000) : ℝ))
    (B := ((351803387671 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy20_hz0 : B (338904041188233601 / 500000000000000000) (42363005148529649 / 62500000000000000) (kdot ((53 / 100))) := by
    constructor
    · apply bkdot_lower (q := (554246824513826269 / 1000000000000000000)) (a := (126524470181512309 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (138561706128456567 / 250000000000000000)) (a := (101219576145207591 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy20_hz1 : B (2809 / 10000) (2809 / 10000) (((53 / 100) : ℝ)^2) := bsq (bpoint ((53 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy20_hz2 : B (7191 / 10000) (7191 / 10000) ((1 : ℝ) - (((53 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy20_hz1 (by norm_num) (by norm_num)

theorem lowEnergy20_hz3 : B (84799764150615419 / 100000000000000000) (847997641506154191 / 1000000000000000000) (√((1 : ℝ) - (((53 / 100) : ℝ)^2))) := bsqrt lowEnergy20_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy20_hz4 : B (16870377046996679 / 62500000000000000) (53985206550389373 / 200000000000000000) ((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) := bdiv lowEnergy20_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy20_hz5 : B (359238283659527617 / 1000000000000000000) (11226196364360357 / 31250000000000000) (((53 / 100) : ℝ) * (kdot ((53 / 100)))) := bmul (bpoint ((53 / 100) : ℝ)) lowEnergy20_hz0 (by norm_num) (by norm_num)

theorem lowEnergy20_hz6 : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) + (((53 / 100) : ℝ) * (kdot ((53 / 100))))) := badd lowEnergy20_hz4 lowEnergy20_hz5 (by norm_num) (by norm_num)

theorem lowEnergy20_hz7 : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (kappa ((53 / 100))) := by rw [kappa_eq]; exact lowEnergy20_hz6

theorem lowEnergy20_hz8 : B (71787224458867001 / 100000000000000000) (11216753821697969 / 15625000000000000) (kdot ((632259259939 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (474653078904498679 / 1000000000000000000)) (a := (88633048377401233 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (237326539452249339 / 500000000000000000)) (a := (221582620943503079 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy20_hz9 : B (39975177177861197 / 100000000000000000) (399751771778611971 / 1000000000000000000) (((632259259939 / 1000000000000) : ℝ)^2) := bsq (bpoint ((632259259939 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy20_hz10 : B (600248228221388029 / 1000000000000000000) (60024822822138803 / 100000000000000000) ((1 : ℝ) - (((632259259939 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy20_hz9 (by norm_num) (by norm_num)

theorem lowEnergy20_hz11 : B (48422305206276549 / 62500000000000000) (387378441650212393 / 500000000000000000) (√((1 : ℝ) - (((632259259939 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy20_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy20_hz12 : B (61653193835866651 / 250000000000000000) (123306387671733303 / 500000000000000000) ((√((1 : ℝ) - (((632259259939 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy20_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy20_hz13 : B (453881374094381297 / 1000000000000000000) (226940687047190651 / 500000000000000000) (((632259259939 / 1000000000000) : ℝ) * (kdot ((632259259939 / 1000000000000)))) := bmul (bpoint ((632259259939 / 1000000000000) : ℝ)) lowEnergy20_hz8 (by norm_num) (by norm_num)

theorem lowEnergy20_hz14 : B (700494149437847901 / 1000000000000000000) (175123537359461977 / 250000000000000000) (((√((1 : ℝ) - (((632259259939 / 1000000000000) : ℝ)^2))) / Real.pi) + (((632259259939 / 1000000000000) : ℝ) * (kdot ((632259259939 / 1000000000000))))) := badd lowEnergy20_hz12 lowEnergy20_hz13 (by norm_num) (by norm_num)

theorem lowEnergy20_hz15 : B (700494149437847901 / 1000000000000000000) (175123537359461977 / 250000000000000000) (kappa ((632259259939 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy20_hz14

theorem lowEnergy20 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (53 / 100)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (703362029363 / 1000000000000) := by
  have hk1 : kappa q ≤ (157291079103 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((53 / 100) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy20_hz7.2.trans (by norm_num))
  have hk2 : kappa ((632259259939 / 1000000000000) : ℝ) ≤ (350247074719 / 500000000000) := lowEnergy20_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((793592664037 / 1000000000000) : ℝ)) (R := ((794458689441 / 1000000000000) : ℝ)) (Q2 := ((632259259939 / 1000000000000) : ℝ)) (T := ((209420027437 / 250000000000) : ℝ))
    (B := ((703362029363 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy21_hz0 : B (169405108424279267 / 250000000000000000) (1355240867394249 / 2000000000000000) (kdot ((1059 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (69329023983646331 / 125000000000000000)) (a := (506392638582300339 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (554632191869170647 / 1000000000000000000)) (a := (506392638582288667 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy21_hz1 : B (1121481 / 4000000) (1121481 / 4000000) (((1059 / 2000) : ℝ)^2) := bsq (bpoint ((1059 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy21_hz2 : B (2878519 / 4000000) (2878519 / 4000000) ((1 : ℝ) - (((1059 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy21_hz1 (by norm_num) (by norm_num)

theorem lowEnergy21_hz3 : B (169661987492779301 / 200000000000000000) (424154968731948253 / 500000000000000000) (√((1 : ℝ) - (((1059 / 2000) : ℝ)^2))) := bsqrt lowEnergy21_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy21_hz4 : B (135012719821355739 / 500000000000000000) (6750635991067787 / 25000000000000000) ((√((1 : ℝ) - (((1059 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy21_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy21_hz5 : B (358800019642623487 / 1000000000000000000) (358800019642627423 / 1000000000000000000) (((1059 / 2000) : ℝ) * (kdot ((1059 / 2000)))) := bmul (bpoint ((1059 / 2000) : ℝ)) lowEnergy21_hz0 (by norm_num) (by norm_num)

theorem lowEnergy21_hz6 : B (125765091857066993 / 200000000000000000) (628825459285338903 / 1000000000000000000) (((√((1 : ℝ) - (((1059 / 2000) : ℝ)^2))) / Real.pi) + (((1059 / 2000) : ℝ) * (kdot ((1059 / 2000))))) := badd lowEnergy21_hz4 lowEnergy21_hz5 (by norm_num) (by norm_num)

theorem lowEnergy21_hz7 : B (125765091857066993 / 200000000000000000) (628825459285338903 / 1000000000000000000) (kappa ((1059 / 2000))) := by rw [kappa_eq]; exact lowEnergy21_hz6

theorem lowEnergy21_hz8 : B (717732656000504813 / 1000000000000000000) (717732656000504819 / 1000000000000000000) (kdot ((126383888929 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (474921771596691883 / 1000000000000000000)) (a := (221692253564279271 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (237460885798345941 / 500000000000000000)) (a := (88676901425711707 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy21_hz9 : B (399322184520445219 / 1000000000000000000) (19966109226022261 / 50000000000000000) (((126383888929 / 200000000000) : ℝ)^2) := bsq (bpoint ((126383888929 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy21_hz10 : B (30033890773977739 / 50000000000000000) (600677815479554781 / 1000000000000000000) ((1 : ℝ) - (((126383888929 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy21_hz9 (by norm_num) (by norm_num)

theorem lowEnergy21_hz11 : B (96879259219236619 / 125000000000000000) (775034073753892953 / 1000000000000000000) (√((1 : ℝ) - (((126383888929 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy21_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy21_hz12 : B (24670100780516129 / 100000000000000000) (246701007805161291 / 1000000000000000000) ((√((1 : ℝ) - (((126383888929 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy21_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy21_hz13 : B (113387305345854957 / 250000000000000000) (453549221383419833 / 1000000000000000000) (((126383888929 / 200000000000) : ℝ) * (kdot ((126383888929 / 200000000000)))) := bmul (bpoint ((126383888929 / 200000000000) : ℝ)) lowEnergy21_hz8 (by norm_num) (by norm_num)

theorem lowEnergy21_hz14 : B (350125114594290559 / 500000000000000000) (175062557297145281 / 250000000000000000) (((√((1 : ℝ) - (((126383888929 / 200000000000) : ℝ)^2))) / Real.pi) + (((126383888929 / 200000000000) : ℝ) * (kdot ((126383888929 / 200000000000))))) := badd lowEnergy21_hz12 lowEnergy21_hz13 (by norm_num) (by norm_num)

theorem lowEnergy21_hz15 : B (350125114594290559 / 500000000000000000) (175062557297145281 / 250000000000000000) (kappa ((126383888929 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy21_hz14

theorem lowEnergy21 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1059 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (175779349653 / 250000000000) := by
  have hk1 : kappa q ≤ (314412729643 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1059 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy21_hz7.2.trans (by norm_num))
  have hk2 : kappa ((126383888929 / 200000000000) : ℝ) ≤ (700250229189 / 1000000000000) := lowEnergy21_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((158675827937 / 200000000000) : ℝ)) (R := ((794245165089 / 1000000000000) : ℝ)) (Q2 := ((126383888929 / 200000000000) : ℝ)) (T := ((52345890753 / 62500000000) : ℝ))
    (B := ((175779349653 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy22_hz0 : B (677432854040574941 / 1000000000000000000) (67743285404058263 / 100000000000000000) (kdot ((529 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (111003508685464427 / 200000000000000000)) (a := (6333591100222227 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (277508771713661067 / 500000000000000000)) (a := (126671822004441521 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy22_hz1 : B (279841 / 1000000) (279841 / 1000000) (((529 / 1000) : ℝ)^2) := bsq (bpoint ((529 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy22_hz2 : B (720159 / 1000000) (720159 / 1000000) ((1 : ℝ) - (((529 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy22_hz1 (by norm_num) (by norm_num)

theorem lowEnergy22_hz3 : B (848621823900375543 / 1000000000000000000) (106077727987546943 / 125000000000000000) (√((1 : ℝ) - (((529 / 1000) : ℝ)^2))) := bsqrt lowEnergy22_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy22_hz4 : B (270124716178809389 / 1000000000000000000) (27012471617880939 / 100000000000000000) ((√((1 : ℝ) - (((529 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy22_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy22_hz5 : B (358361979787464143 / 1000000000000000000) (89590494946867053 / 250000000000000000) (((529 / 1000) : ℝ) * (kdot ((529 / 1000)))) := bmul (bpoint ((529 / 1000) : ℝ)) lowEnergy22_hz0 (by norm_num) (by norm_num)

theorem lowEnergy22_hz6 : B (157121673991568383 / 250000000000000000) (314243347983138801 / 500000000000000000) (((√((1 : ℝ) - (((529 / 1000) : ℝ)^2))) / Real.pi) + (((529 / 1000) : ℝ) * (kdot ((529 / 1000))))) := badd lowEnergy22_hz4 lowEnergy22_hz5 (by norm_num) (by norm_num)

theorem lowEnergy22_hz7 : B (157121673991568383 / 250000000000000000) (314243347983138801 / 500000000000000000) (kappa ((529 / 1000))) := by rw [kappa_eq]; exact lowEnergy22_hz6

theorem lowEnergy22_hz8 : B (1793982889713439 / 2500000000000000) (358796577942687803 / 500000000000000000) (kdot ((315789861661 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (237595174950319333 / 500000000000000000)) (a := (17744145335879639 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (95038069980127733 / 200000000000000000)) (a := (443603633396990967 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy22_hz9 : B (39889294691149407 / 100000000000000000) (398892946911494071 / 1000000000000000000) (((315789861661 / 500000000000) : ℝ)^2) := bsq (bpoint ((315789861661 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy22_hz10 : B (601107053088505929 / 1000000000000000000) (60110705308850593 / 100000000000000000) ((1 : ℝ) - (((315789861661 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy22_hz9 (by norm_num) (by norm_num)

theorem lowEnergy22_hz11 : B (775310939616168403 / 1000000000000000000) (155062187923233681 / 200000000000000000) (√((1 : ℝ) - (((315789861661 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy22_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy22_hz12 : B (123394568473135183 / 500000000000000000) (246789136946270367 / 1000000000000000000) ((√((1 : ℝ) - (((315789861661 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy22_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy22_hz13 : B (453217286851846337 / 1000000000000000000) (226608643425923171 / 500000000000000000) (((315789861661 / 500000000000) : ℝ) * (kdot ((315789861661 / 500000000000)))) := bmul (bpoint ((315789861661 / 500000000000) : ℝ)) lowEnergy22_hz8 (by norm_num) (by norm_num)

theorem lowEnergy22_hz14 : B (700006423798116703 / 1000000000000000000) (700006423798116709 / 1000000000000000000) (((√((1 : ℝ) - (((315789861661 / 500000000000) : ℝ)^2))) / Real.pi) + (((315789861661 / 500000000000) : ℝ) * (kdot ((315789861661 / 500000000000))))) := badd lowEnergy22_hz12 lowEnergy22_hz13 (by norm_num) (by norm_num)

theorem lowEnergy22_hz15 : B (700006423798116703 / 1000000000000000000) (700006423798116709 / 1000000000000000000) (kappa ((315789861661 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy22_hz14

theorem lowEnergy22 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (529 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (702872883003 / 1000000000000) := by
  have hk1 : kappa q ≤ (628486695967 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((529 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy22_hz7.2.trans (by norm_num))
  have hk2 : kappa ((315789861661 / 500000000000) : ℝ) ≤ (700006423799 / 1000000000000) := lowEnergy22_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((158633123397 / 200000000000) : ℝ)) (R := ((794031642389 / 1000000000000) : ℝ)) (Q2 := ((315789861661 / 500000000000) : ℝ)) (T := ((418694218821 / 500000000000) : ℝ))
    (B := ((702872883003 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy23_hz0 : B (677245343265661211 / 1000000000000000000) (338622671632834583 / 500000000000000000) (kdot ((1057 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (555402879468072469 / 1000000000000000000)) (a := (506981829254247113 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (138850719867018117 / 250000000000000000)) (a := (506981829254234619 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy23_hz1 : B (1117249 / 4000000) (1117249 / 4000000) (((1057 / 2000) : ℝ)^2) := bsq (bpoint ((1057 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy23_hz2 : B (2882751 / 4000000) (2882751 / 4000000) ((1 : ℝ) - (((1057 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy23_hz1 (by norm_num) (by norm_num)

theorem lowEnergy23_hz3 : B (26529165664592149 / 31250000000000000) (848933301266948769 / 1000000000000000000) (√((1 : ℝ) - (((1057 / 2000) : ℝ)^2))) := bsqrt lowEnergy23_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy23_hz4 : B (270223862503912139 / 1000000000000000000) (13511193125195607 / 50000000000000000) ((√((1 : ℝ) - (((1057 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy23_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy23_hz5 : B (7158483278318039 / 20000000000000000) (71584832783181231 / 200000000000000000) (((1057 / 2000) : ℝ) * (kdot ((1057 / 2000)))) := bmul (bpoint ((1057 / 2000) : ℝ)) lowEnergy23_hz0 (by norm_num) (by norm_num)

theorem lowEnergy23_hz6 : B (628148026419814089 / 1000000000000000000) (125629605283963659 / 200000000000000000) (((√((1 : ℝ) - (((1057 / 2000) : ℝ)^2))) / Real.pi) + (((1057 / 2000) : ℝ) * (kdot ((1057 / 2000))))) := badd lowEnergy23_hz4 lowEnergy23_hz5 (by norm_num) (by norm_num)

theorem lowEnergy23_hz7 : B (628148026419814089 / 1000000000000000000) (125629605283963659 / 200000000000000000) (kappa ((1057 / 2000))) := by rw [kappa_eq]; exact lowEnergy23_hz6

theorem lowEnergy23_hz8 : B (717453744108622241 / 1000000000000000000) (89681718013577781 / 125000000000000000) (kdot ((315620047969 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (475458814012545223 / 1000000000000000000)) (a := (443822620903827101 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (237729407006272611 / 500000000000000000)) (a := (443822620903827093 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy23_hz9 : B (99616014679953861 / 250000000000000000) (79692811743963089 / 200000000000000000) (((315620047969 / 500000000000) : ℝ)^2) := bsq (bpoint ((315620047969 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy23_hz10 : B (120307188256036911 / 200000000000000000) (150383985320046139 / 250000000000000000) ((1 : ℝ) - (((315620047969 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy23_hz9 (by norm_num) (by norm_num)

theorem lowEnergy23_hz11 : B (387793740692195983 / 500000000000000000) (24237108793262249 / 31250000000000000) (√((1 : ℝ) - (((315620047969 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy23_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy23_hz12 : B (15429822682814917 / 62500000000000000) (123438581462519337 / 500000000000000000) ((√((1 : ℝ) - (((315620047969 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy23_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy23_hz13 : B (90577114052440801 / 200000000000000000) (452885570262204011 / 1000000000000000000) (((315620047969 / 500000000000) : ℝ) * (kdot ((315620047969 / 500000000000)))) := bmul (bpoint ((315620047969 / 500000000000) : ℝ)) lowEnergy23_hz8 (by norm_num) (by norm_num)

theorem lowEnergy23_hz14 : B (699762733187242677 / 1000000000000000000) (139952546637448537 / 200000000000000000) (((√((1 : ℝ) - (((315620047969 / 500000000000) : ℝ)^2))) / Real.pi) + (((315620047969 / 500000000000) : ℝ) * (kdot ((315620047969 / 500000000000))))) := badd lowEnergy23_hz12 lowEnergy23_hz13 (by norm_num) (by norm_num)

theorem lowEnergy23_hz15 : B (699762733187242677 / 1000000000000000000) (139952546637448537 / 200000000000000000) (kappa ((315620047969 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy23_hz14

theorem lowEnergy23 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1057 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (702628482457 / 1000000000000) := by
  have hk1 : kappa q ≤ (31407401321 / 50000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1057 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy23_hz7.2.trans (by norm_num))
  have hk2 : kappa ((315620047969 / 500000000000) : ℝ) ≤ (174940683297 / 250000000000) := lowEnergy23_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((396476047959 / 500000000000) : ℝ)) (R := ((396909060661 / 500000000000) : ℝ)) (Q2 := ((315620047969 / 500000000000) : ℝ)) (T := ((418621333253 / 500000000000) : ℝ))
    (B := ((702628482457 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy24_hz0 : B (338528950615775423 / 500000000000000000) (169264475307889769 / 250000000000000000) (kdot ((66 / 125))) := by
    constructor
    · apply bkdot_lower (q := (555788200270759099 / 1000000000000000000)) (a := (253638131256457319 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (277894100135379549 / 500000000000000000)) (a := (31704766407056357 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy24_hz1 : B (4356 / 15625) (4356 / 15625) (((66 / 125) : ℝ)^2) := bsq (bpoint ((66 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy24_hz2 : B (11269 / 15625) (11269 / 15625) ((1 : ℝ) - (((66 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy24_hz1 (by norm_num) (by norm_num)

theorem lowEnergy24_hz3 : B (424622185006859951 / 500000000000000000) (849244370013719903 / 1000000000000000000) (√((1 : ℝ) - (((66 / 125) : ℝ)^2))) := bsqrt lowEnergy24_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy24_hz4 : B (270322878761292193 / 1000000000000000000) (135161439380646097 / 500000000000000000) ((√((1 : ℝ) - (((66 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy24_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy24_hz5 : B (178743285925129423 / 500000000000000000) (357486571850263193 / 1000000000000000000) (((66 / 125) : ℝ) * (kdot ((66 / 125)))) := bmul (bpoint ((66 / 125) : ℝ)) lowEnergy24_hz0 (by norm_num) (by norm_num)

theorem lowEnergy24_hz6 : B (627809450611551039 / 1000000000000000000) (627809450611555387 / 1000000000000000000) (((√((1 : ℝ) - (((66 / 125) : ℝ)^2))) / Real.pi) + (((66 / 125) : ℝ) * (kdot ((66 / 125))))) := badd lowEnergy24_hz4 lowEnergy24_hz5 (by norm_num) (by norm_num)

theorem lowEnergy24_hz7 : B (627809450611551039 / 1000000000000000000) (627809450611555387 / 1000000000000000000) (kappa ((66 / 125))) := by rw [kappa_eq]; exact lowEnergy24_hz6

theorem lowEnergy24_hz8 : B (717314420534697899 / 1000000000000000000) (143462884106939581 / 200000000000000000) (kdot ((315450281229 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (475727164130473457 / 1000000000000000000)) (a := (88808293972396679 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (29732947758154591 / 62500000000000000)) (a := (444041469861983387 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy24_hz9 : B (398035519709820759 / 1000000000000000000) (9950887992745519 / 25000000000000000) (((315450281229 / 500000000000) : ℝ)^2) := bsq (bpoint ((315450281229 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy24_hz10 : B (15049112007254481 / 25000000000000000) (601964480290179241 / 1000000000000000000) ((1 : ℝ) - (((315450281229 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy24_hz9 (by norm_num) (by norm_num)

theorem lowEnergy24_hz11 : B (775863699556938441 / 1000000000000000000) (775863699556938443 / 1000000000000000000) (√((1 : ℝ) - (((315450281229 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy24_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy24_hz12 : B (61741271475025959 / 250000000000000000) (246965085900103837 / 1000000000000000000) ((√((1 : ℝ) - (((315450281229 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy24_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy24_hz13 : B (452554071374575249 / 1000000000000000000) (226277035687287627 / 500000000000000000) (((315450281229 / 500000000000) : ℝ) * (kdot ((315450281229 / 500000000000)))) := bmul (bpoint ((315450281229 / 500000000000) : ℝ)) lowEnergy24_hz8 (by norm_num) (by norm_num)

theorem lowEnergy24_hz14 : B (139903831454935817 / 200000000000000000) (699519157274679091 / 1000000000000000000) (((√((1 : ℝ) - (((315450281229 / 500000000000) : ℝ)^2))) / Real.pi) + (((315450281229 / 500000000000) : ℝ) * (kdot ((315450281229 / 500000000000))))) := badd lowEnergy24_hz12 lowEnergy24_hz13 (by norm_num) (by norm_num)

theorem lowEnergy24_hz15 : B (139903831454935817 / 200000000000000000) (699519157274679091 / 1000000000000000000) (kappa ((315450281229 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy24_hz14

theorem lowEnergy24 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (66 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (140476839379 / 200000000000) := by
  have hk1 : kappa q ≤ (156952362653 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((66 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy24_hz7.2.trans (by norm_num))
  have hk2 : kappa ((315450281229 / 500000000000) : ℝ) ≤ (27980766291 / 40000000000) := lowEnergy24_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((792738576463 / 1000000000000) : ℝ)) (R := ((793604601867 / 1000000000000) : ℝ)) (Q2 := ((315450281229 / 500000000000) : ℝ)) (T := ((418548469307 / 500000000000) : ℝ))
    (B := ((140476839379 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy25_hz0 : B (135374105559554411 / 200000000000000000) (676870527797780569 / 1000000000000000000) (kdot ((211 / 400))) := by
    constructor
    · apply bkdot_lower (q := (556173506114267357 / 1000000000000000000)) (a := (507570588014433309 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (139043376528566839 / 250000000000000000)) (a := (507570588014419937 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy25_hz1 : B (44521 / 160000) (44521 / 160000) (((211 / 400) : ℝ)^2) := bsq (bpoint ((211 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy25_hz2 : B (115479 / 160000) (115479 / 160000) ((1 : ℝ) - (((211 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy25_hz1 (by norm_num) (by norm_num)

theorem lowEnergy25_hz3 : B (424777515294771693 / 500000000000000000) (849555030589543387 / 1000000000000000000) (√((1 : ℝ) - (((211 / 400) : ℝ)^2))) := bsqrt lowEnergy25_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy25_hz4 : B (270421765093824357 / 1000000000000000000) (135210882546912179 / 500000000000000000) ((√((1 : ℝ) - (((211 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy25_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy25_hz5 : B (357049203413324759 / 1000000000000000000) (357049203413329251 / 1000000000000000000) (((211 / 400) : ℝ) * (kdot ((211 / 400)))) := bmul (bpoint ((211 / 400) : ℝ)) lowEnergy25_hz0 (by norm_num) (by norm_num)

theorem lowEnergy25_hz6 : B (156867742126787279 / 250000000000000000) (627470968507153609 / 1000000000000000000) (((√((1 : ℝ) - (((211 / 400) : ℝ)^2))) / Real.pi) + (((211 / 400) : ℝ) * (kdot ((211 / 400))))) := badd lowEnergy25_hz4 lowEnergy25_hz5 (by norm_num) (by norm_num)

theorem lowEnergy25_hz7 : B (156867742126787279 / 250000000000000000) (627470968507153609 / 1000000000000000000) (kappa ((211 / 400))) := by rw [kappa_eq]; exact lowEnergy25_hz6

theorem lowEnergy25_hz8 : B (717175185028810423 / 1000000000000000000) (71717518502881043 / 100000000000000000) (kdot ((19705035089 / 31250000000))) := by
    constructor
    · apply bkdot_lower (q := (475995400451180471 / 1000000000000000000)) (a := (55532522560398859 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (47599540045118047 / 100000000000000000)) (a := (444260180483190863 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy25_hz9 : B (397607329647330547 / 1000000000000000000) (99401832411832637 / 250000000000000000) (((19705035089 / 31250000000) : ℝ)^2) := bsq (bpoint ((19705035089 / 31250000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy25_hz10 : B (150598167588167363 / 250000000000000000) (602392670352669453 / 1000000000000000000) ((1 : ℝ) - (((19705035089 / 31250000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy25_hz9 (by norm_num) (by norm_num)

theorem lowEnergy25_hz11 : B (776139594630160233 / 1000000000000000000) (155227918926032047 / 200000000000000000) (√((1 : ℝ) - (((19705035089 / 31250000000) : ℝ)^2))) := bsqrt lowEnergy25_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy25_hz12 : B (247052906029459733 / 1000000000000000000) (123526453014729867 / 500000000000000000) ((√((1 : ℝ) - (((19705035089 / 31250000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy25_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy25_hz13 : B (452222789950488859 / 1000000000000000000) (14131962185952777 / 31250000000000000) (((19705035089 / 31250000000) : ℝ) * (kdot ((19705035089 / 31250000000)))) := bmul (bpoint ((19705035089 / 31250000000) : ℝ)) lowEnergy25_hz8 (by norm_num) (by norm_num)

theorem lowEnergy25_hz14 : B (43704730998746787 / 62500000000000000) (349637847989974299 / 500000000000000000) (((√((1 : ℝ) - (((19705035089 / 31250000000) : ℝ)^2))) / Real.pi) + (((19705035089 / 31250000000) : ℝ) * (kdot ((19705035089 / 31250000000))))) := badd lowEnergy25_hz12 lowEnergy25_hz13 (by norm_num) (by norm_num)

theorem lowEnergy25_hz15 : B (43704730998746787 / 62500000000000000) (349637847989974299 / 500000000000000000) (kappa ((19705035089 / 31250000000))) := by rw [kappa_eq]; exact lowEnergy25_hz14

theorem lowEnergy25 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (211 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (351070013117 / 500000000000) := by
  have hk1 : kappa q ≤ (156867742127 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((211 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy25_hz7.2.trans (by norm_num))
  have hk2 : kappa ((19705035089 / 31250000000) : ℝ) ≤ (34963784799 / 50000000000) := lowEnergy25_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((3962625293 / 5000000000) : ℝ)) (R := ((198347771001 / 250000000000) : ℝ)) (Q2 := ((19705035089 / 31250000000) : ℝ)) (T := ((41847562697 / 50000000000) : ℝ))
    (B := ((351070013117 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy26_hz0 : B (33834161141210247 / 50000000000000000) (169170805706053437 / 250000000000000000) (kdot ((527 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (69569849659629079 / 125000000000000000)) (a := (126966201494725737 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (556558797277032631 / 1000000000000000000)) (a := (253932402989444557 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy26_hz1 : B (277729 / 1000000) (277729 / 1000000) (((527 / 1000) : ℝ)^2) := bsq (bpoint ((527 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy26_hz2 : B (722271 / 1000000) (722271 / 1000000) ((1 : ℝ) - (((527 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy26_hz1 (by norm_num) (by norm_num)

theorem lowEnergy26_hz3 : B (212466320860507207 / 250000000000000000) (849865283442028829 / 1000000000000000000) (√((1 : ℝ) - (((527 / 1000) : ℝ)^2))) := bsqrt lowEnergy26_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy26_hz4 : B (54104104328797439 / 200000000000000000) (67630130410996799 / 250000000000000000) ((√((1 : ℝ) - (((527 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy26_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy26_hz5 : B (356612058428356003 / 1000000000000000000) (178306029214180323 / 500000000000000000) (((527 / 1000) : ℝ) * (kdot ((527 / 1000)))) := bmul (bpoint ((527 / 1000) : ℝ)) lowEnergy26_hz0 (by norm_num) (by norm_num)

theorem lowEnergy26_hz6 : B (313566290036171599 / 500000000000000000) (313566290036173921 / 500000000000000000) (((√((1 : ℝ) - (((527 / 1000) : ℝ)^2))) / Real.pi) + (((527 / 1000) : ℝ) * (kdot ((527 / 1000))))) := badd lowEnergy26_hz4 lowEnergy26_hz5 (by norm_num) (by norm_num)

theorem lowEnergy26_hz7 : B (313566290036171599 / 500000000000000000) (313566290036173921 / 500000000000000000) (kappa ((527 / 1000))) := by rw [kappa_eq]; exact lowEnergy26_hz6

theorem lowEnergy26_hz8 : B (717036037456100407 / 1000000000000000000) (358518018728050207 / 500000000000000000) (kdot ((630221777073 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (59532940396462651 / 125000000000000000)) (a := (444478752979286191 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (476263523171701207 / 1000000000000000000)) (a := (222239376489643091 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy26_hz9 : B (99294872074262527 / 250000000000000000) (397179488297050109 / 1000000000000000000) (((630221777073 / 1000000000000) : ℝ)^2) := bsq (bpoint ((630221777073 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy26_hz10 : B (602820511702949891 / 1000000000000000000) (150705127925737473 / 250000000000000000) ((1 : ℝ) - (((630221777073 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy26_hz9 (by norm_num) (by norm_num)

theorem lowEnergy26_hz11 : B (155283033420003731 / 200000000000000000) (24262973971875583 / 31250000000000000) (√((1 : ℝ) - (((630221777073 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy26_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy26_hz12 : B (247140623470975753 / 1000000000000000000) (123570311735487877 / 500000000000000000) ((√((1 : ℝ) - (((630221777073 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy26_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy26_hz13 : B (112972931437741447 / 250000000000000000) (225945862875482897 / 500000000000000000) (((630221777073 / 1000000000000) : ℝ) * (kdot ((630221777073 / 1000000000000)))) := bmul (bpoint ((630221777073 / 1000000000000) : ℝ)) lowEnergy26_hz8 (by norm_num) (by norm_num)

theorem lowEnergy26_hz14 : B (699032349221941541 / 1000000000000000000) (174758087305485387 / 250000000000000000) (((√((1 : ℝ) - (((630221777073 / 1000000000000) : ℝ)^2))) / Real.pi) + (((630221777073 / 1000000000000) : ℝ) * (kdot ((630221777073 / 1000000000000))))) := badd lowEnergy26_hz12 lowEnergy26_hz13 (by norm_num) (by norm_num)

theorem lowEnergy26_hz15 : B (699032349221941541 / 1000000000000000000) (174758087305485387 / 250000000000000000) (kappa ((630221777073 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy26_hz14

theorem lowEnergy26 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (527 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (350947985197 / 500000000000) := by
  have hk1 : kappa q ≤ (627132580073 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((527 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy26_hz7.2.trans (by norm_num))
  have hk2 : kappa ((630221777073 / 1000000000000) : ℝ) ≤ (349516174611 / 500000000000) := lowEnergy26_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((198077885577 / 250000000000) : ℝ)) (R := ((24786798991 / 31250000000) : ℝ)) (Q2 := ((630221777073 / 1000000000000) : ℝ)) (T := ((836805612459 / 1000000000000) : ℝ))
    (B := ((350947985197 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy27_hz0 : B (4228099913569251 / 6250000000000000) (676495986171089271 / 1000000000000000000) (kdot ((1053 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (556944074037042529 / 1000000000000000000)) (a := (127039729156468181 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (17404502313657579 / 31250000000000000)) (a := (254079458312929207 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy27_hz1 : B (1108809 / 4000000) (1108809 / 4000000) (((1053 / 2000) : ℝ)^2) := bsq (bpoint ((1053 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy27_hz2 : B (2891191 / 4000000) (2891191 / 4000000) ((1 : ℝ) - (((1053 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy27_hz1 (by norm_num) (by norm_num)

theorem lowEnergy27_hz3 : B (850175129017545419 / 1000000000000000000) (42508756450877271 / 50000000000000000) (√((1 : ℝ) - (((1053 / 2000) : ℝ)^2))) := bsqrt lowEnergy27_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy27_hz4 : B (16913696784616527 / 62500000000000000) (270619148553864433 / 1000000000000000000) ((√((1 : ℝ) - (((1053 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy27_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy27_hz5 : B (44521892089884213 / 125000000000000000) (178087568359539251 / 500000000000000000) (((1053 / 2000) : ℝ) * (kdot ((1053 / 2000)))) := bmul (bpoint ((1053 / 2000) : ℝ)) lowEnergy27_hz0 (by norm_num) (by norm_num)

theorem lowEnergy27_hz6 : B (78349285659117267 / 125000000000000000) (125358857054588587 / 200000000000000000) (((√((1 : ℝ) - (((1053 / 2000) : ℝ)^2))) / Real.pi) + (((1053 / 2000) : ℝ) * (kdot ((1053 / 2000))))) := badd lowEnergy27_hz4 lowEnergy27_hz5 (by norm_num) (by norm_num)

theorem lowEnergy27_hz7 : B (78349285659117267 / 125000000000000000) (125358857054588587 / 200000000000000000) (kappa ((1053 / 2000))) := by rw [kappa_eq]; exact lowEnergy27_hz6

theorem lowEnergy27_hz8 : B (358448488840615411 / 500000000000000000) (716896977681230829 / 1000000000000000000) (kdot ((78735315637 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (476531532490139743 / 1000000000000000000)) (a := (22234859378142813 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (238265766245069871 / 500000000000000000)) (a := (444697187562856251 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy27_hz9 : B (396751995421313069 / 1000000000000000000) (39675199542131307 / 100000000000000000) (((78735315637 / 125000000000) : ℝ)^2) := bsq (bpoint ((78735315637 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy27_hz10 : B (60324800457868693 / 100000000000000000) (603248004578686931 / 1000000000000000000) ((1 : ℝ) - (((78735315637 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy27_hz9 (by norm_num) (by norm_num)

theorem lowEnergy27_hz11 : B (776690417462895527 / 1000000000000000000) (776690417462895529 / 1000000000000000000) (√((1 : ℝ) - (((78735315637 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy27_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy27_hz12 : B (247228238382655137 / 1000000000000000000) (247228238382655139 / 1000000000000000000) ((√((1 : ℝ) - (((78735315637 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy27_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy27_hz13 : B (18062435141421777 / 40000000000000000) (45156087853554443 / 100000000000000000) (((78735315637 / 125000000000) : ℝ) * (kdot ((78735315637 / 125000000000)))) := bmul (bpoint ((78735315637 / 125000000000) : ℝ)) lowEnergy27_hz8 (by norm_num) (by norm_num)

theorem lowEnergy27_hz14 : B (349394558459099781 / 500000000000000000) (698789116918199569 / 1000000000000000000) (((√((1 : ℝ) - (((78735315637 / 125000000000) : ℝ)^2))) / Real.pi) + (((78735315637 / 125000000000) : ℝ) * (kdot ((78735315637 / 125000000000))))) := badd lowEnergy27_hz12 lowEnergy27_hz13 (by norm_num) (by norm_num)

theorem lowEnergy27_hz15 : B (349394558459099781 / 500000000000000000) (698789116918199569 / 1000000000000000000) (kappa ((78735315637 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy27_hz14

theorem lowEnergy27 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1053 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (701652029291 / 1000000000000) := by
  have hk1 : kappa q ≤ (626794285273 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1053 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy27_hz7.2.trans (by norm_num))
  have hk2 : kappa ((78735315637 / 125000000000) : ℝ) ≤ (698789116919 / 1000000000000) := lowEnergy27_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((396049013783 / 500000000000) : ℝ)) (R := ((79296405297 / 100000000000) : ℝ)) (Q2 := ((78735315637 / 125000000000) : ℝ)) (T := ((836660014143 / 1000000000000) : ℝ))
    (B := ((701652029291 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy28_hz0 : B (676308817698977599 / 1000000000000000000) (676308817698987023 / 1000000000000000000) (kdot ((263 / 500))) := by
    constructor
    · apply bkdot_lower (q := (278664668335919509 / 500000000000000000)) (a := (12711323004358581 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (557329336671839017 / 1000000000000000000)) (a := (508452920174328437 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy28_hz1 : B (69169 / 250000) (69169 / 250000) (((263 / 500) : ℝ)^2) := bsq (bpoint ((263 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy28_hz2 : B (180831 / 250000) (180831 / 250000) ((1 : ℝ) - (((263 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy28_hz1 (by norm_num) (by norm_num)

theorem lowEnergy28_hz3 : B (850484567761226341 / 1000000000000000000) (425242283880613171 / 500000000000000000) (√((1 : ℝ) - (((263 / 500) : ℝ)^2))) := bsqrt lowEnergy28_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy28_hz4 : B (270717645965146361 / 1000000000000000000) (135358822982573181 / 500000000000000000) ((√((1 : ℝ) - (((263 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy28_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy28_hz5 : B (355738438109662217 / 1000000000000000000) (14229537524386687 / 40000000000000000) (((263 / 500) : ℝ) * (kdot ((263 / 500)))) := bmul (bpoint ((263 / 500) : ℝ)) lowEnergy28_hz0 (by norm_num) (by norm_num)

theorem lowEnergy28_hz6 : B (313228042037404289 / 500000000000000000) (626456084074813537 / 1000000000000000000) (((√((1 : ℝ) - (((263 / 500) : ℝ)^2))) / Real.pi) + (((263 / 500) : ℝ) * (kdot ((263 / 500))))) := badd lowEnergy28_hz4 lowEnergy28_hz5 (by norm_num) (by norm_num)

theorem lowEnergy28_hz7 : B (313228042037404289 / 500000000000000000) (626456084074813537 / 1000000000000000000) (kappa ((263 / 500))) := by rw [kappa_eq]; exact lowEnergy28_hz6

theorem lowEnergy28_hz8 : B (716758005571664679 / 1000000000000000000) (358379002785832343 / 500000000000000000) (kdot ((314771683443 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (476799428599351433 / 1000000000000000000)) (a := (88983096888417939 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (59599928574918929 / 125000000000000000)) (a := (222457742221044843 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy28_hz9 : B (396324850790160801 / 1000000000000000000) (198162425395080401 / 500000000000000000) (((314771683443 / 500000000000) : ℝ)^2) := bsq (bpoint ((314771683443 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy28_hz10 : B (301837574604919599 / 500000000000000000) (603675149209839199 / 1000000000000000000) ((1 : ℝ) - (((314771683443 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy28_hz9 (by norm_num) (by norm_num)

theorem lowEnergy28_hz11 : B (776965346209108091 / 1000000000000000000) (776965346209108093 / 1000000000000000000) (√((1 : ℝ) - (((314771683443 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy28_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy28_hz12 : B (247315750920570711 / 1000000000000000000) (30914468865071339 / 125000000000000000) ((√((1 : ℝ) - (((314771683443 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy28_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy28_hz13 : B (451230248070080129 / 1000000000000000000) (225615124035040067 / 500000000000000000) (((314771683443 / 500000000000) : ℝ) * (kdot ((314771683443 / 500000000000)))) := bmul (bpoint ((314771683443 / 500000000000) : ℝ)) lowEnergy28_hz8 (by norm_num) (by norm_num)

theorem lowEnergy28_hz14 : B (17463649974766271 / 25000000000000000) (349272999495325423 / 500000000000000000) (((√((1 : ℝ) - (((314771683443 / 500000000000) : ℝ)^2))) / Real.pi) + (((314771683443 / 500000000000) : ℝ) * (kdot ((314771683443 / 500000000000))))) := badd lowEnergy28_hz12 lowEnergy28_hz13 (by norm_num) (by norm_num)

theorem lowEnergy28_hz15 : B (17463649974766271 / 25000000000000000) (349272999495325423 / 500000000000000000) (kappa ((314771683443 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy28_hz14

theorem lowEnergy28 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (263 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (701408202847 / 1000000000000) := by
  have hk1 : kappa q ≤ (25058243363 / 40000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((263 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy28_hz7.2.trans (by norm_num))
  have hk2 : kappa ((314771683443 / 500000000000) : ℝ) ≤ (698545998991 / 1000000000000) := lowEnergy28_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((158376902871 / 200000000000) : ℝ)) (R := ((792750539759 / 1000000000000) : ℝ)) (Q2 := ((314771683443 / 500000000000) : ℝ)) (T := ((104564307371 / 125000000000) : ℝ))
    (B := ((701408202847 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy29_hz0 : B (338060858634412523 / 500000000000000000) (169030429317208699 / 250000000000000000) (kdot ((1051 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (278857292729260289 / 500000000000000000)) (a := (101749363368553723 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (557714585458520577 / 1000000000000000000)) (a := (508746816842753301 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy29_hz1 : B (1104601 / 4000000) (1104601 / 4000000) (((1051 / 2000) : ℝ)^2) := bsq (bpoint ((1051 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy29_hz2 : B (2895399 / 4000000) (2895399 / 4000000) ((1 : ℝ) - (((1051 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy29_hz1 (by norm_num) (by norm_num)

theorem lowEnergy29_hz3 : B (850793600116973141 / 1000000000000000000) (425396800058486571 / 500000000000000000) (√((1 : ℝ) - (((1051 / 2000) : ℝ)^2))) := bsqrt lowEnergy29_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy29_hz4 : B (135408007009565617 / 500000000000000000) (54163202803826247 / 200000000000000000) ((√((1 : ℝ) - (((1051 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy29_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy29_hz5 : B (355301962424767561 / 1000000000000000000) (177650981212386343 / 500000000000000000) (((1051 / 2000) : ℝ) * (kdot ((1051 / 2000)))) := bmul (bpoint ((1051 / 2000) : ℝ)) lowEnergy29_hz0 (by norm_num) (by norm_num)

theorem lowEnergy29_hz6 : B (125223595288779759 / 200000000000000000) (626117976443903921 / 1000000000000000000) (((√((1 : ℝ) - (((1051 / 2000) : ℝ)^2))) / Real.pi) + (((1051 / 2000) : ℝ) * (kdot ((1051 / 2000))))) := badd lowEnergy29_hz4 lowEnergy29_hz5 (by norm_num) (by norm_num)

theorem lowEnergy29_hz7 : B (125223595288779759 / 200000000000000000) (626117976443903921 / 1000000000000000000) (kappa ((1051 / 2000))) := by rw [kappa_eq]; exact lowEnergy29_hz6

theorem lowEnergy29_hz8 : B (28664764839758943 / 40000000000000000) (358309560496986791 / 500000000000000000) (kdot ((629204302409 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (238533605847027851 / 500000000000000000)) (a := (222566821913287671 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (477067211694055701 / 1000000000000000000)) (a := (445133643826575333 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy29_hz9 : B (395898054169996323 / 1000000000000000000) (98974513542499081 / 250000000000000000) (((629204302409 / 1000000000000) : ℝ)^2) := bsq (bpoint ((629204302409 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy29_hz10 : B (151025486457500919 / 250000000000000000) (604101945830003677 / 1000000000000000000) ((1 : ℝ) - (((629204302409 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy29_hz9 (by norm_num) (by norm_num)

theorem lowEnergy29_hz11 : B (155447990766044149 / 200000000000000000) (777239953830220747 / 1000000000000000000) (√((1 : ℝ) - (((629204302409 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy29_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy29_hz12 : B (247403161241192281 / 1000000000000000000) (247403161241192283 / 1000000000000000000) ((√((1 : ℝ) - (((629204302409 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy29_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy29_hz13 : B (450899834117963909 / 1000000000000000000) (90179966823592783 / 200000000000000000) (((629204302409 / 1000000000000) : ℝ) * (kdot ((629204302409 / 1000000000000)))) := bmul (bpoint ((629204302409 / 1000000000000) : ℝ)) lowEnergy29_hz8 (by norm_num) (by norm_num)

theorem lowEnergy29_hz14 : B (69830299535915619 / 100000000000000000) (349151497679578099 / 500000000000000000) (((√((1 : ℝ) - (((629204302409 / 1000000000000) : ℝ)^2))) / Real.pi) + (((629204302409 / 1000000000000) : ℝ) * (kdot ((629204302409 / 1000000000000))))) := badd lowEnergy29_hz12 lowEnergy29_hz13 (by norm_num) (by norm_num)

theorem lowEnergy29_hz15 : B (69830299535915619 / 100000000000000000) (349151497679578099 / 500000000000000000) (kappa ((629204302409 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy29_hz14

theorem lowEnergy29 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1051 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (87645561373 / 125000000000) := by
  have hk1 : kappa q ≤ (156529494111 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1051 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy29_hz7.2.trans (by norm_num))
  have hk2 : kappa ((629204302409 / 1000000000000) : ℝ) ≤ (4364393721 / 6250000000) := lowEnergy29_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((158334200531 / 200000000000) : ℝ)) (R := ((792537028059 / 1000000000000) : ℝ)) (Q2 := ((629204302409 / 1000000000000) : ℝ)) (T := ((83636894691 / 100000000000) : ℝ))
    (B := ((87645561373 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy30_hz0 : B (337967342370948439 / 500000000000000000) (168983671185476741 / 250000000000000000) (kdot ((21 / 40))) := by
    constructor
    · apply bkdot_lower (q := (279049910336872163 / 500000000000000000)) (a := (127260151712264637 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (22323992826949773 / 40000000000000000)) (a := (509040606849042707 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy30_hz1 : B (441 / 1600) (441 / 1600) (((21 / 40) : ℝ)^2) := bsq (bpoint ((21 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy30_hz2 : B (1159 / 1600) (1159 / 1600) ((1 : ℝ) - (((21 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy30_hz1 (by norm_num) (by norm_num)

theorem lowEnergy30_hz3 : B (3324618072372891 / 3906250000000000) (851102226527460097 / 1000000000000000000) (√((1 : ℝ) - (((21 / 40) : ℝ)^2))) := bsqrt lowEnergy30_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy30_hz4 : B (33864281607090831 / 125000000000000000) (5418285057134533 / 20000000000000000) ((√((1 : ℝ) - (((21 / 40) : ℝ)^2))) / Real.pi) := bdiv lowEnergy30_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy30_hz5 : B (17743285474474793 / 50000000000000000) (354865709489501157 / 1000000000000000000) (((21 / 40) : ℝ) * (kdot ((21 / 40)))) := bmul (bpoint ((21 / 40) : ℝ)) lowEnergy30_hz0 (by norm_num) (by norm_num)

theorem lowEnergy30_hz6 : B (156444990586555627 / 250000000000000000) (625779962346227807 / 1000000000000000000) (((√((1 : ℝ) - (((21 / 40) : ℝ)^2))) / Real.pi) + (((21 / 40) : ℝ) * (kdot ((21 / 40))))) := badd lowEnergy30_hz4 lowEnergy30_hz5 (by norm_num) (by norm_num)

theorem lowEnergy30_hz7 : B (156444990586555627 / 250000000000000000) (625779962346227807 / 1000000000000000000) (kappa ((21 / 40))) := by rw [kappa_eq]; exact lowEnergy30_hz6

theorem lowEnergy30_hz8 : B (89560040476832177 / 125000000000000000) (358240161907328711 / 500000000000000000) (kdot ((62886533163 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (95466976393851403 / 200000000000000000)) (a := (222675832963007329 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (238667440984628507 / 500000000000000000)) (a := (445351665926014649 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy30_hz9 : B (197735802663054939 / 500000000000000000) (395471605326109879 / 1000000000000000000) (((62886533163 / 100000000000) : ℝ)^2) := bsq (bpoint ((62886533163 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy30_hz10 : B (604528394673890121 / 1000000000000000000) (302264197336945061 / 500000000000000000) ((1 : ℝ) - (((62886533163 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy30_hz9 (by norm_num) (by norm_num)

theorem lowEnergy30_hz11 : B (777514240817420733 / 1000000000000000000) (388757120408710367 / 500000000000000000) (√((1 : ℝ) - (((62886533163 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy30_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy30_hz12 : B (61872617375217401 / 250000000000000000) (123745234750434803 / 500000000000000000) ((√((1 : ℝ) - (((62886533163 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy30_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy30_hz13 : B (225284818221037161 / 500000000000000000) (450569636442074327 / 1000000000000000000) (((62886533163 / 100000000000) : ℝ) * (kdot ((62886533163 / 100000000000)))) := bmul (bpoint ((62886533163 / 100000000000) : ℝ)) lowEnergy30_hz8 (by norm_num) (by norm_num)

theorem lowEnergy30_hz14 : B (349030052971471963 / 500000000000000000) (698060105942943933 / 1000000000000000000) (((√((1 : ℝ) - (((62886533163 / 100000000000) : ℝ)^2))) / Real.pi) + (((62886533163 / 100000000000) : ℝ) * (kdot ((62886533163 / 100000000000))))) := badd lowEnergy30_hz12 lowEnergy30_hz13 (by norm_num) (by norm_num)

theorem lowEnergy30_hz15 : B (349030052971471963 / 500000000000000000) (698060105942943933 / 1000000000000000000) (kappa ((62886533163 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy30_hz14

theorem lowEnergy30 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (21 / 40)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (350460446809 / 500000000000) := by
  have hk1 : kappa q ≤ (625779962347 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((21 / 40) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy30_hz7.2.trans (by norm_num))
  have hk2 : kappa ((62886533163 / 100000000000) : ℝ) ≤ (698060105943 / 1000000000000) := lowEnergy30_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((158291498489 / 200000000000) : ℝ)) (R := ((792323517849 / 1000000000000) : ℝ)) (Q2 := ((62886533163 / 100000000000) : ℝ)) (T := ((836223477941 / 1000000000000) : ℝ))
    (B := ((350460446809 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy31_hz0 : B (168936929994953187 / 250000000000000000) (33787385998991159 / 50000000000000000) (kdot ((1049 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (27924252129686407 / 50000000000000000)) (a := (254667145205290191 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (558485042593728139 / 1000000000000000000)) (a := (509334290410563997 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy31_hz1 : B (1100401 / 4000000) (1100401 / 4000000) (((1049 / 2000) : ℝ)^2) := bsq (bpoint ((1049 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy31_hz2 : B (2899599 / 4000000) (2899599 / 4000000) ((1 : ℝ) - (((1049 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy31_hz1 (by norm_num) (by norm_num)

theorem lowEnergy31_hz3 : B (212852611858534637 / 250000000000000000) (851410447434138549 / 1000000000000000000) (√((1 : ℝ) - (((1049 / 2000) : ℝ)^2))) := bsqrt lowEnergy31_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy31_hz4 : B (271012362618450931 / 1000000000000000000) (67753090654612733 / 250000000000000000) ((√((1 : ℝ) - (((1049 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy31_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy31_hz5 : B (177214839564705893 / 500000000000000000) (177214839564708629 / 500000000000000000) (((1049 / 2000) : ℝ) * (kdot ((1049 / 2000)))) := bmul (bpoint ((1049 / 2000) : ℝ)) lowEnergy31_hz0 (by norm_num) (by norm_num)

theorem lowEnergy31_hz6 : B (625442041747862717 / 1000000000000000000) (62544204174786819 / 100000000000000000) (((√((1 : ℝ) - (((1049 / 2000) : ℝ)^2))) / Real.pi) + (((1049 / 2000) : ℝ) * (kdot ((1049 / 2000))))) := badd lowEnergy31_hz4 lowEnergy31_hz5 (by norm_num) (by norm_num)

theorem lowEnergy31_hz7 : B (625442041747862717 / 1000000000000000000) (62544204174786819 / 100000000000000000) (kappa ((1049 / 2000))) := by rw [kappa_eq]; exact lowEnergy31_hz6

theorem lowEnergy31_hz8 : B (179085403475240599 / 250000000000000000) (716341613900962403 / 1000000000000000000) (kdot ((125705290903 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (477602439618667231 / 1000000000000000000)) (a := (3481012116788569 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (47760243961866723 / 100000000000000000)) (a := (222784775474468411 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy31_hz9 : B (395045504025196363 / 1000000000000000000) (98761376006299091 / 250000000000000000) (((125705290903 / 200000000000) : ℝ)^2) := bsq (bpoint ((125705290903 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy31_hz10 : B (151238623993700909 / 250000000000000000) (604954495974803637 / 1000000000000000000) ((1 : ℝ) - (((125705290903 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy31_hz9 (by norm_num) (by norm_num)

theorem lowEnergy31_hz11 : B (388894103829951257 / 500000000000000000) (155557641531980503 / 200000000000000000) (√((1 : ℝ) - (((125705290903 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy31_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy31_hz12 : B (247577675855318113 / 1000000000000000000) (123788837927659057 / 500000000000000000) ((√((1 : ℝ) - (((125705290903 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy31_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy31_hz13 : B (450239654806724933 / 1000000000000000000) (225119827403362469 / 500000000000000000) (((125705290903 / 200000000000) : ℝ) * (kdot ((125705290903 / 200000000000)))) := bmul (bpoint ((125705290903 / 200000000000) : ℝ)) lowEnergy31_hz8 (by norm_num) (by norm_num)

theorem lowEnergy31_hz14 : B (348908665331021523 / 500000000000000000) (174454332665510763 / 250000000000000000) (((√((1 : ℝ) - (((125705290903 / 200000000000) : ℝ)^2))) / Real.pi) + (((125705290903 / 200000000000) : ℝ) * (kdot ((125705290903 / 200000000000))))) := badd lowEnergy31_hz12 lowEnergy31_hz13 (by norm_num) (by norm_num)

theorem lowEnergy31_hz15 : B (348908665331021523 / 500000000000000000) (174454332665510763 / 250000000000000000) (kappa ((125705290903 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy31_hz14

theorem lowEnergy31 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1049 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (700677410671 / 1000000000000) := by
  have hk1 : kappa q ≤ (156360510437 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1049 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy31_hz7.2.trans (by norm_num))
  have hk2 : kappa ((125705290903 / 200000000000) : ℝ) ≤ (697817330663 / 1000000000000) := lowEnergy31_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((158248796741 / 200000000000) : ℝ)) (R := ((792110009109 / 1000000000000) : ℝ)) (Q2 := ((125705290903 / 200000000000) : ℝ)) (T := ((836078052037 / 1000000000000) : ℝ))
    (B := ((700677410671 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy32_hz0 : B (27022432913781451 / 40000000000000000) (337780411422273533 / 500000000000000000) (kdot ((131 / 250))) := by
    constructor
    · apply bkdot_lower (q := (558870251494252773 / 1000000000000000000)) (a := (254813933872080577 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (139717562873563193 / 250000000000000000)) (a := (254813933872072103 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy32_hz1 : B (17161 / 62500) (17161 / 62500) (((131 / 250) : ℝ)^2) := bsq (bpoint ((131 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy32_hz2 : B (45339 / 62500) (45339 / 62500) ((1 : ℝ) - (((131 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy32_hz1 (by norm_num) (by norm_num)

theorem lowEnergy32_hz3 : B (425859131638620613 / 500000000000000000) (851718263277241227 / 1000000000000000000) (√((1 : ℝ) - (((131 / 250) : ℝ)^2))) := bsqrt lowEnergy32_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy32_hz4 : B (16944396465277157 / 62500000000000000) (271110343444434513 / 1000000000000000000) ((√((1 : ℝ) - (((131 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy32_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy32_hz5 : B (22124616948158563 / 62500000000000000) (353993871170542663 / 1000000000000000000) (((131 / 250) : ℝ) * (kdot ((131 / 250)))) := bmul (bpoint ((131 / 250) : ℝ)) lowEnergy32_hz0 (by norm_num) (by norm_num)

theorem lowEnergy32_hz6 : B (976725335335893 / 1562500000000000) (78138026826872147 / 125000000000000000) (((√((1 : ℝ) - (((131 / 250) : ℝ)^2))) / Real.pi) + (((131 / 250) : ℝ) * (kdot ((131 / 250))))) := badd lowEnergy32_hz4 lowEnergy32_hz5 (by norm_num) (by norm_num)

theorem lowEnergy32_hz7 : B (976725335335893 / 1562500000000000) (78138026826872147 / 125000000000000000) (kappa ((131 / 250))) := by rw [kappa_eq]; exact lowEnergy32_hz6

theorem lowEnergy32_hz8 : B (716202991120469939 / 1000000000000000000) (716202991120469947 / 1000000000000000000) (kdot ((62818767103 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (95573976967099487 / 200000000000000000)) (a := (222893649551672239 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (238934942417748717 / 500000000000000000)) (a := (111446824775836117 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy32_hz9 : B (394619750034095501 / 1000000000000000000) (197309875017047751 / 500000000000000000) (((62818767103 / 100000000000) : ℝ)^2) := bsq (bpoint ((62818767103 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy32_hz10 : B (302690124982952249 / 500000000000000000) (605380249965904499 / 1000000000000000000) ((1 : ℝ) - (((62818767103 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy32_hz9 (by norm_num) (by norm_num)

theorem lowEnergy32_hz11 : B (778061854845682881 / 1000000000000000000) (778061854845682883 / 1000000000000000000) (√((1 : ℝ) - (((62818767103 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy32_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy32_hz12 : B (30958097557484797 / 125000000000000000) (247664780459878377 / 1000000000000000000) ((√((1 : ℝ) - (((62818767103 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy32_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy32_hz13 : B (449909888976687781 / 1000000000000000000) (449909888976687787 / 1000000000000000000) (((62818767103 / 100000000000) : ℝ) * (kdot ((62818767103 / 100000000000)))) := bmul (bpoint ((62818767103 / 100000000000) : ℝ)) lowEnergy32_hz8 (by norm_num) (by norm_num)

theorem lowEnergy32_hz14 : B (697574669436566157 / 1000000000000000000) (174393667359141541 / 250000000000000000) (((√((1 : ℝ) - (((62818767103 / 100000000000) : ℝ)^2))) / Real.pi) + (((62818767103 / 100000000000) : ℝ) * (kdot ((62818767103 / 100000000000))))) := badd lowEnergy32_hz12 lowEnergy32_hz13 (by norm_num) (by norm_num)

theorem lowEnergy32_hz15 : B (697574669436566157 / 1000000000000000000) (174393667359141541 / 250000000000000000) (kappa ((62818767103 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy32_hz14

theorem lowEnergy32 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (131 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (350217021031 / 500000000000) := by
  have hk1 : kappa q ≤ (125020842923 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((131 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy32_hz7.2.trans (by norm_num))
  have hk2 : kappa ((62818767103 / 100000000000) : ℝ) ≤ (697574669437 / 1000000000000) := lowEnergy32_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((395515238207 / 500000000000) : ℝ)) (R := ((395948250909 / 500000000000) : ℝ)) (Q2 := ((62818767103 / 100000000000) : ℝ)) (T := ((208983167293 / 250000000000) : ℝ))
    (B := ((350217021031 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy33_hz0 : B (337686996599186877 / 500000000000000000) (135074798639676983 / 200000000000000000) (kdot ((1047 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (559255447650663959 / 1000000000000000000)) (a := (509921339066089633 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (279627723825331979 / 500000000000000000)) (a := (509921339066072103 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy33_hz1 : B (1096209 / 4000000) (1096209 / 4000000) (((1047 / 2000) : ℝ)^2) := bsq (bpoint ((1047 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy33_hz2 : B (2903791 / 4000000) (2903791 / 4000000) ((1 : ℝ) - (((1047 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy33_hz1 (by norm_num) (by norm_num)

theorem lowEnergy33_hz3 : B (852025674495786541 / 1000000000000000000) (426012837247893271 / 500000000000000000) (√((1 : ℝ) - (((1047 / 2000) : ℝ)^2))) := bsqrt lowEnergy33_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy33_hz4 : B (67802048868605323 / 250000000000000000) (271208195474421293 / 1000000000000000000) ((√((1 : ℝ) - (((1047 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy33_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy33_hz5 : B (17677914271967433 / 50000000000000000) (44194785679919313 / 125000000000000000) (((1047 / 2000) : ℝ) * (kdot ((1047 / 2000)))) := bmul (bpoint ((1047 / 2000) : ℝ)) lowEnergy33_hz0 (by norm_num) (by norm_num)

theorem lowEnergy33_hz6 : B (19523952528555311 / 31250000000000000) (624766480913775797 / 1000000000000000000) (((√((1 : ℝ) - (((1047 / 2000) : ℝ)^2))) / Real.pi) + (((1047 / 2000) : ℝ) * (kdot ((1047 / 2000))))) := badd lowEnergy33_hz4 lowEnergy33_hz5 (by norm_num) (by norm_num)

theorem lowEnergy33_hz7 : B (19523952528555311 / 31250000000000000) (624766480913775797 / 1000000000000000000) (kappa ((1047 / 2000))) := by rw [kappa_eq]; exact lowEnergy33_hz6

theorem lowEnergy33_hz8 : B (358032227670547737 / 500000000000000000) (716064455341095481 / 1000000000000000000) (kdot ((627848981141 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (239068608906229901 / 500000000000000000)) (a := (446004910596715557 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (478137217812459801 / 1000000000000000000)) (a := (446004910596715547 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy33_hz9 : B (394194343119791773 / 1000000000000000000) (197097171559895887 / 500000000000000000) (((627848981141 / 1000000000000) : ℝ)^2) := bsq (bpoint ((627848981141 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy33_hz10 : B (302902828440104113 / 500000000000000000) (605805656880208227 / 1000000000000000000) ((1 : ℝ) - (((627848981141 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy33_hz9 (by norm_num) (by norm_num)

theorem lowEnergy33_hz11 : B (194583795715401271 / 250000000000000000) (389167591430802543 / 500000000000000000) (√((1 : ℝ) - (((627848981141 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy33_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy33_hz12 : B (123875891734758707 / 500000000000000000) (49550356693903483 / 200000000000000000) ((√((1 : ℝ) - (((627848981141 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy33_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy33_hz13 : B (28098771169824493 / 62500000000000000) (224790169358595947 / 500000000000000000) (((627848981141 / 1000000000000) : ℝ) * (kdot ((627848981141 / 1000000000000)))) := bmul (bpoint ((627848981141 / 1000000000000) : ℝ)) lowEnergy33_hz8 (by norm_num) (by norm_num)

theorem lowEnergy33_hz14 : B (348666061093354651 / 500000000000000000) (697332122186709309 / 1000000000000000000) (((√((1 : ℝ) - (((627848981141 / 1000000000000) : ℝ)^2))) / Real.pi) + (((627848981141 / 1000000000000) : ℝ) * (kdot ((627848981141 / 1000000000000))))) := badd lowEnergy33_hz12 lowEnergy33_hz13 (by norm_num) (by norm_num)

theorem lowEnergy33_hz15 : B (348666061093354651 / 500000000000000000) (697332122186709309 / 1000000000000000000) (kappa ((627848981141 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy33_hz14

theorem lowEnergy33 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1047 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (700190787709 / 1000000000000) := by
  have hk1 : kappa q ≤ (312383240457 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1047 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy33_hz7.2.trans (by norm_num))
  have hk2 : kappa ((627848981141 / 1000000000000) : ℝ) ≤ (697332122187 / 1000000000000) := lowEnergy33_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((790816970553 / 1000000000000) : ℝ)) (R := ((791682995957 / 1000000000000) : ℝ)) (Q2 := ((627848981141 / 1000000000000) : ℝ)) (T := ((20894683233 / 25000000000) : ℝ))
    (B := ((700190787709 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy34_hz0 : B (675187230903972857 / 1000000000000000000) (1687968077259961 / 2500000000000000) (kdot ((523 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (559640631337874503 / 1000000000000000000)) (a := (510214704592118349 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (279820315668937251 / 500000000000000000)) (a := (255107352296050109 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy34_hz1 : B (273529 / 1000000) (273529 / 1000000) (((523 / 1000) : ℝ)^2) := bsq (bpoint ((523 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy34_hz2 : B (726471 / 1000000) (726471 / 1000000) ((1 : ℝ) - (((523 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy34_hz1 (by norm_num) (by norm_num)

theorem lowEnergy34_hz3 : B (426166340763791433 / 500000000000000000) (852332681527582867 / 1000000000000000000) (√((1 : ℝ) - (((523 / 1000) : ℝ)^2))) := bsqrt lowEnergy34_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy34_hz4 : B (271305918847770003 / 1000000000000000000) (54261183769554001 / 200000000000000000) ((√((1 : ℝ) - (((523 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy34_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy34_hz5 : B (88280730440694451 / 250000000000000000) (176561460881391921 / 500000000000000000) (((523 / 1000) : ℝ) * (kdot ((523 / 1000)))) := bmul (bpoint ((523 / 1000) : ℝ)) lowEnergy34_hz0 (by norm_num) (by norm_num)

theorem lowEnergy34_hz6 : B (624428840610547807 / 1000000000000000000) (624428840610553847 / 1000000000000000000) (((√((1 : ℝ) - (((523 / 1000) : ℝ)^2))) / Real.pi) + (((523 / 1000) : ℝ) * (kdot ((523 / 1000))))) := badd lowEnergy34_hz4 lowEnergy34_hz5 (by norm_num) (by norm_num)

theorem lowEnergy34_hz7 : B (624428840610547807 / 1000000000000000000) (624428840610553847 / 1000000000000000000) (kappa ((523 / 1000))) := by rw [kappa_eq]; exact lowEnergy34_hz6

theorem lowEnergy34_hz8 : B (715926006431904843 / 1000000000000000000) (14318520128638097 / 20000000000000000) (kdot ((39219399051 / 62500000000))) := by
    constructor
    · apply bkdot_lower (q := (478404438740191183 / 1000000000000000000)) (a := (1394444955108503 / 3125000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (239202219370095591 / 500000000000000000)) (a := (8924447712694419 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy34_hz9 : B (393769283051924403 / 1000000000000000000) (98442320762981101 / 250000000000000000) (((39219399051 / 62500000000) : ℝ)^2) := bsq (bpoint ((39219399051 / 62500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy34_hz10 : B (151557679237018899 / 250000000000000000) (606230716948075597 / 1000000000000000000) ((1 : ℝ) - (((39219399051 / 62500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy34_hz9 (by norm_num) (by norm_num)

theorem lowEnergy34_hz11 : B (778608192191731049 / 1000000000000000000) (778608192191731051 / 1000000000000000000) (√((1 : ℝ) - (((39219399051 / 62500000000) : ℝ)^2))) := bsqrt lowEnergy34_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy34_hz12 : B (123919342519158461 / 500000000000000000) (61959671259579231 / 250000000000000000) ((√((1 : ℝ) - (((39219399051 / 62500000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy34_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy34_hz13 : B (449251003795866699 / 1000000000000000000) (28078187737241669 / 62500000000000000) (((39219399051 / 62500000000) : ℝ) * (kdot ((39219399051 / 62500000000)))) := bmul (bpoint ((39219399051 / 62500000000) : ℝ)) lowEnergy34_hz8 (by norm_num) (by norm_num)

theorem lowEnergy34_hz14 : B (697089688834183621 / 1000000000000000000) (174272422208545907 / 250000000000000000) (((√((1 : ℝ) - (((39219399051 / 62500000000) : ℝ)^2))) / Real.pi) + (((39219399051 / 62500000000) : ℝ) * (kdot ((39219399051 / 62500000000))))) := badd lowEnergy34_hz12 lowEnergy34_hz13 (by norm_num) (by norm_num)

theorem lowEnergy34_hz15 : B (697089688834183621 / 1000000000000000000) (174272422208545907 / 250000000000000000) (kappa ((39219399051 / 62500000000))) := by rw [kappa_eq]; exact lowEnergy34_hz14

theorem lowEnergy34 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (523 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (349973823769 / 500000000000) := by
  have hk1 : kappa q ≤ (624428840611 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((523 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy34_hz7.2.trans (by norm_num))
  have hk2 : kappa ((39219399051 / 62500000000) : ℝ) ≤ (139417937767 / 200000000000) := lowEnergy34_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((395301733051 / 500000000000) : ℝ)) (R := ((395734745753 / 500000000000) : ℝ)) (Q2 := ((39219399051 / 62500000000) : ℝ)) (T := ((835642032459 / 1000000000000) : ℝ))
    (B := ((349973823769 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy35_hz0 : B (675000535824321349 / 1000000000000000000) (675000535824333289 / 1000000000000000000) (kdot ((209 / 400))) := by
    constructor
    · apply bkdot_lower (q := (560025802830366369 / 1000000000000000000)) (a := (255253982268732809 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (17500806338448949 / 31250000000000000)) (a := (102101592907489373 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy35_hz1 : B (43681 / 160000) (43681 / 160000) (((209 / 400) : ℝ)^2) := bsq (bpoint ((209 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy35_hz2 : B (116319 / 160000) (116319 / 160000) ((1 : ℝ) - (((209 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy35_hz1 (by norm_num) (by norm_num)

theorem lowEnergy35_hz3 : B (170527856961846559 / 200000000000000000) (213159821202308199 / 250000000000000000) (√((1 : ℝ) - (((209 / 400) : ℝ)^2))) := bsqrt lowEnergy35_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy35_hz4 : B (271403513703455569 / 1000000000000000000) (27140351370345557 / 100000000000000000) ((√((1 : ℝ) - (((209 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy35_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy35_hz5 : B (11021493124006497 / 31250000000000000) (2755373281001673 / 7812500000000000) (((209 / 400) : ℝ) * (kdot ((209 / 400)))) := bmul (bpoint ((209 / 400) : ℝ)) lowEnergy35_hz0 (by norm_num) (by norm_num)

theorem lowEnergy35_hz6 : B (624091293671663473 / 1000000000000000000) (312045646835834857 / 500000000000000000) (((√((1 : ℝ) - (((209 / 400) : ℝ)^2))) / Real.pi) + (((209 / 400) : ℝ) * (kdot ((209 / 400))))) := badd lowEnergy35_hz4 lowEnergy35_hz5 (by norm_num) (by norm_num)

theorem lowEnergy35_hz7 : B (624091293671663473 / 1000000000000000000) (312045646835834857 / 500000000000000000) (kappa ((209 / 400))) := by rw [kappa_eq]; exact lowEnergy35_hz6

theorem lowEnergy35_hz8 : B (715787644259842257 / 1000000000000000000) (143157528851968453 / 200000000000000000) (kdot ((627171882017 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (95734309562713669 / 200000000000000000)) (a := (223219862213182117 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (59833943476696043 / 125000000000000000)) (a := (446439724426364223 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy35_hz9 : B (393344569592745767 / 1000000000000000000) (49168071199093221 / 125000000000000000) (((627171882017 / 1000000000000) : ℝ)^2) := bsq (bpoint ((627171882017 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy35_hz10 : B (75831928800906779 / 125000000000000000) (606655430407254233 / 1000000000000000000) ((1 : ℝ) - (((627171882017 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy35_hz9 (by norm_num) (by norm_num)

theorem lowEnergy35_hz11 : B (194720220830948601 / 250000000000000000) (155776176664758881 / 200000000000000000) (√((1 : ℝ) - (((627171882017 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy35_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy35_hz12 : B (123962742660763669 / 500000000000000000) (247925485321527339 / 1000000000000000000) ((√((1 : ℝ) - (((627171882017 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy35_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy35_hz13 : B (89784376794992031 / 200000000000000000) (448921883974960161 / 1000000000000000000) (((627171882017 / 1000000000000) : ℝ) * (kdot ((627171882017 / 1000000000000)))) := bmul (bpoint ((627171882017 / 1000000000000) : ℝ)) lowEnergy35_hz8 (by norm_num) (by norm_num)

theorem lowEnergy35_hz14 : B (696847369296487493 / 1000000000000000000) (55747789543719 / 80000000000000) (((√((1 : ℝ) - (((627171882017 / 1000000000000) : ℝ)^2))) / Real.pi) + (((627171882017 / 1000000000000) : ℝ) * (kdot ((627171882017 / 1000000000000))))) := badd lowEnergy35_hz12 lowEnergy35_hz13 (by norm_num) (by norm_num)

theorem lowEnergy35_hz15 : B (696847369296487493 / 1000000000000000000) (55747789543719 / 80000000000000) (kappa ((627171882017 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy35_hz14

theorem lowEnergy35 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (209 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (349852310731 / 500000000000) := by
  have hk1 : kappa q ≤ (78011411709 / 125000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((209 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy35_hz7.2.trans (by norm_num))
  have hk2 : kappa ((627171882017 / 1000000000000) : ℝ) ≤ (696847369297 / 1000000000000) := lowEnergy35_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((790389963039 / 1000000000000) : ℝ)) (R := ((791255988443 / 1000000000000) : ℝ)) (Q2 := ((627171882017 / 1000000000000) : ℝ)) (T := ((835496778559 / 1000000000000) : ℝ))
    (B := ((349852310731 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy36_hz0 : B (674813907822745807 / 1000000000000000000) (168703476955689539 / 250000000000000000) (kdot ((261 / 500))) := by
    constructor
    · apply bkdot_lower (q := (560410962402192759 / 1000000000000000000)) (a := (510801119116817551 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (280205481201096379 / 500000000000000000)) (a := (127700279779199539 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy36_hz1 : B (68121 / 250000) (68121 / 250000) (((261 / 500) : ℝ)^2) := bsq (bpoint ((261 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy36_hz2 : B (181879 / 250000) (181879 / 250000) ((1 : ℝ) - (((261 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy36_hz1 (by norm_num) (by norm_num)

theorem lowEnergy36_hz3 : B (426472742388068689 / 500000000000000000) (852945484776137379 / 1000000000000000000) (√((1 : ℝ) - (((261 / 500) : ℝ)^2))) := bsqrt lowEnergy36_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy36_hz4 : B (271500980180070447 / 1000000000000000000) (271500980180070449 / 1000000000000000000) ((√((1 : ℝ) - (((261 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy36_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy36_hz5 : B (352252859883473311 / 1000000000000000000) (176126429941739879 / 500000000000000000) (((261 / 500) : ℝ) * (kdot ((261 / 500)))) := bmul (bpoint ((261 / 500) : ℝ)) lowEnergy36_hz0 (by norm_num) (by norm_num)

theorem lowEnergy36_hz6 : B (311876920031771879 / 500000000000000000) (623753840063550207 / 1000000000000000000) (((√((1 : ℝ) - (((261 / 500) : ℝ)^2))) / Real.pi) + (((261 / 500) : ℝ) * (kdot ((261 / 500))))) := badd lowEnergy36_hz4 lowEnergy36_hz5 (by norm_num) (by norm_num)

theorem lowEnergy36_hz7 : B (311876920031771879 / 500000000000000000) (623753840063550207 / 1000000000000000000) (kappa ((261 / 500))) := by rw [kappa_eq]; exact lowEnergy36_hz6

theorem lowEnergy36_hz8 : B (89456171086982671 / 125000000000000000) (5725194949566891 / 8000000000000000) (kdot ((125366694543 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (478938545219872631 / 1000000000000000000)) (a := (446656927174350907 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (47893854521987263 / 100000000000000000)) (a := (446656927174350897 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy36_hz9 : B (392920202515946649 / 1000000000000000000) (7858404050318933 / 20000000000000000) (((125366694543 / 200000000000) : ℝ)^2) := bsq (bpoint ((125366694543 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy36_hz10 : B (12141595949681067 / 20000000000000000) (607079797484053351 / 1000000000000000000) ((1 : ℝ) - (((125366694543 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy36_hz9 (by norm_num) (by norm_num)

theorem lowEnergy36_hz11 : B (389576628368557727 / 500000000000000000) (12174269636517429 / 15625000000000000) (√((1 : ℝ) - (((125366694543 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy36_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy36_hz12 : B (62003046117930263 / 250000000000000000) (124006092235860527 / 500000000000000000) ((√((1 : ℝ) - (((125366694543 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy36_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy36_hz13 : B (448592979025924191 / 1000000000000000000) (448592979025924197 / 1000000000000000000) (((125366694543 / 200000000000) : ℝ) * (kdot ((125366694543 / 200000000000)))) := bmul (bpoint ((125366694543 / 200000000000) : ℝ)) lowEnergy36_hz8 (by norm_num) (by norm_num)

theorem lowEnergy36_hz14 : B (696605163497645243 / 1000000000000000000) (696605163497645251 / 1000000000000000000) (((√((1 : ℝ) - (((125366694543 / 200000000000) : ℝ)^2))) / Real.pi) + (((125366694543 / 200000000000) : ℝ) * (kdot ((125366694543 / 200000000000))))) := badd lowEnergy36_hz12 lowEnergy36_hz13 (by norm_num) (by norm_num)

theorem lowEnergy36_hz15 : B (696605163497645243 / 1000000000000000000) (696605163497645251 / 1000000000000000000) (kappa ((125366694543 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy36_hz14

theorem lowEnergy36 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (699461709407 / 1000000000000) := by
  have hk1 : kappa q ≤ (9746153751 / 15625000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((261 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy36_hz7.2.trans (by norm_num))
  have hk2 : kappa ((125366694543 / 200000000000) : ℝ) ≤ (348302581749 / 500000000000) := lowEnergy36_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((395088230673 / 500000000000) : ℝ)) (R := ((3164169947 / 4000000000) : ℝ)) (Q2 := ((125366694543 / 200000000000) : ℝ)) (T := ((417675783799 / 500000000000) : ℝ))
    (B := ((699461709407 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy37_hz0 : B (337313673381455173 / 500000000000000000) (674627346762923117 / 1000000000000000000) (kdot ((1043 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (560796110326980177 / 1000000000000000000)) (a := (511094168544330057 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (35049756895436261 / 62500000000000000)) (a := (511094168544309997 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy37_hz1 : B (1087849 / 4000000) (1087849 / 4000000) (((1043 / 2000) : ℝ)^2) := bsq (bpoint ((1043 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy37_hz2 : B (2912151 / 4000000) (2912151 / 4000000) ((1 : ℝ) - (((1043 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy37_hz1 (by norm_num) (by norm_num)

theorem lowEnergy37_hz3 : B (853251281862500339 / 1000000000000000000) (42662564093125017 / 50000000000000000) (√((1 : ℝ) - (((1043 / 2000) : ℝ)^2))) := bsqrt lowEnergy37_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy37_hz4 : B (33949789801978247 / 125000000000000000) (271598318415825977 / 1000000000000000000) ((√((1 : ℝ) - (((1043 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy37_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy37_hz5 : B (70363632267371549 / 200000000000000000) (175909080668432203 / 500000000000000000) (((1043 / 2000) : ℝ) * (kdot ((1043 / 2000)))) := bmul (bpoint ((1043 / 2000) : ℝ)) lowEnergy37_hz0 (by norm_num) (by norm_num)

theorem lowEnergy37_hz6 : B (623416479752683721 / 1000000000000000000) (623416479752690383 / 1000000000000000000) (((√((1 : ℝ) - (((1043 / 2000) : ℝ)^2))) / Real.pi) + (((1043 / 2000) : ℝ) * (kdot ((1043 / 2000))))) := badd lowEnergy37_hz4 lowEnergy37_hz5 (by norm_num) (by norm_num)

theorem lowEnergy37_hz7 : B (623416479752683721 / 1000000000000000000) (623416479752690383 / 1000000000000000000) (kappa ((1043 / 2000))) := by rw [kappa_eq]; exact lowEnergy37_hz6

theorem lowEnergy37_hz8 : B (715511179607566607 / 1000000000000000000) (143102235921513323 / 200000000000000000) (kdot ((78311894609 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (479205431152995421 / 1000000000000000000)) (a := (111718498521661863 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (23960271557649771 / 50000000000000000)) (a := (446873994086647441 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy37_hz9 : B (24531011349004493 / 62500000000000000) (392496181584071889 / 1000000000000000000) (((78311894609 / 125000000000) : ℝ)^2) := bsq (bpoint ((78311894609 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy37_hz10 : B (607503818415928111 / 1000000000000000000) (37968988650995507 / 62500000000000000) ((1 : ℝ) - (((78311894609 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy37_hz9 (by norm_num) (by norm_num)

theorem lowEnergy37_hz11 : B (389712656458552841 / 500000000000000000) (194856328229276421 / 250000000000000000) (√((1 : ℝ) - (((78311894609 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy37_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy37_hz12 : B (124049391321704669 / 500000000000000000) (12404939132170467 / 50000000000000000) ((√((1 : ℝ) - (((78311894609 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy37_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy37_hz13 : B (28016518044494513 / 62500000000000000) (224132144355956107 / 500000000000000000) (((78311894609 / 125000000000) : ℝ) * (kdot ((78311894609 / 125000000000)))) := bmul (bpoint ((78311894609 / 125000000000) : ℝ)) lowEnergy37_hz8 (by norm_num) (by norm_num)

theorem lowEnergy37_hz14 : B (348181535677660773 / 500000000000000000) (348181535677660777 / 500000000000000000) (((√((1 : ℝ) - (((78311894609 / 125000000000) : ℝ)^2))) / Real.pi) + (((78311894609 / 125000000000) : ℝ) * (kdot ((78311894609 / 125000000000))))) := badd lowEnergy37_hz12 lowEnergy37_hz13 (by norm_num) (by norm_num)

theorem lowEnergy37_hz15 : B (348181535677660773 / 500000000000000000) (348181535677660777 / 500000000000000000) (kappa ((78311894609 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy37_hz14

theorem lowEnergy37 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1043 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (699218911291 / 1000000000000) := by
  have hk1 : kappa q ≤ (623416479753 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1043 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy37_hz7.2.trans (by norm_num))
  have hk2 : kappa ((78311894609 / 125000000000) : ℝ) ≤ (174090767839 / 250000000000) := lowEnergy37_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((789962961001 / 1000000000000) : ℝ)) (R := ((158165797281 / 200000000000) : ℝ)) (Q2 := ((78311894609 / 125000000000) : ℝ)) (T := ((16704127991 / 20000000000) : ℝ))
    (B := ((699218911291 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy38_hz0 : B (168610213127203837 / 250000000000000000) (168610213127207139 / 250000000000000000) (kdot ((521 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (140295311719482623 / 250000000000000000)) (a := (255693556516815417 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (561181246877930491 / 1000000000000000000)) (a := (63923389129201261 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy38_hz1 : B (271441 / 1000000) (271441 / 1000000) (((521 / 1000) : ℝ)^2) := bsq (bpoint ((521 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy38_hz2 : B (728559 / 1000000) (728559 / 1000000) ((1 : ℝ) - (((521 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy38_hz1 (by norm_num) (by norm_num)

theorem lowEnergy38_hz3 : B (213389169125333069 / 250000000000000000) (853556676501332277 / 1000000000000000000) (√((1 : ℝ) - (((521 / 1000) : ℝ)^2))) := bsqrt lowEnergy38_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy38_hz4 : B (27169552854855371 / 100000000000000000) (271695528548553711 / 1000000000000000000) ((√((1 : ℝ) - (((521 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy38_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy38_hz5 : B (87845921039273199 / 250000000000000000) (175691842078549839 / 500000000000000000) (((521 / 1000) : ℝ) * (kdot ((521 / 1000)))) := bmul (bpoint ((521 / 1000) : ℝ)) lowEnergy38_hz0 (by norm_num) (by norm_num)

theorem lowEnergy38_hz6 : B (311539606352823253 / 500000000000000000) (623079212705653389 / 1000000000000000000) (((√((1 : ℝ) - (((521 / 1000) : ℝ)^2))) / Real.pi) + (((521 / 1000) : ℝ) * (kdot ((521 / 1000))))) := badd lowEnergy38_hz4 lowEnergy38_hz5 (by norm_num) (by norm_num)

theorem lowEnergy38_hz7 : B (311539606352823253 / 500000000000000000) (623079212705653389 / 1000000000000000000) (kappa ((521 / 1000))) := by rw [kappa_eq]; exact lowEnergy38_hz6

theorem lowEnergy38_hz8 : B (89421634608371891 / 125000000000000000) (22355408652092973 / 31250000000000000) (kdot ((31307846723 / 50000000000))) := by
    constructor
    · apply bkdot_lower (q := (479472205798449653 / 1000000000000000000)) (a := (447090925364288857 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (119868051449612413 / 250000000000000000)) (a := (223545462682144423 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy38_hz9 : B (78414501314468947 / 200000000000000000) (12252265830385773 / 31250000000000000) (((31307846723 / 50000000000) : ℝ)^2) := bsq (bpoint ((31307846723 / 50000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy38_hz10 : B (18997734169614227 / 31250000000000000) (121585498685531053 / 200000000000000000) ((1 : ℝ) - (((31307846723 / 50000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy38_hz9 (by norm_num) (by norm_num)

theorem lowEnergy38_hz11 : B (779697052339981123 / 1000000000000000000) (6237576418719849 / 8000000000000000) (√((1 : ℝ) - (((31307846723 / 50000000000) : ℝ)^2))) := bsqrt lowEnergy38_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy38_hz12 : B (248185279988176469 / 1000000000000000000) (24818527998817647 / 100000000000000000) ((√((1 : ℝ) - (((31307846723 / 50000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy38_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy38_hz13 : B (447935812806243087 / 1000000000000000000) (447935812806243093 / 1000000000000000000) (((31307846723 / 50000000000) : ℝ) * (kdot ((31307846723 / 50000000000)))) := bmul (bpoint ((31307846723 / 50000000000) : ℝ)) lowEnergy38_hz8 (by norm_num) (by norm_num)

theorem lowEnergy38_hz14 : B (174030273198604889 / 250000000000000000) (696121092794419563 / 1000000000000000000) (((√((1 : ℝ) - (((31307846723 / 50000000000) : ℝ)^2))) / Real.pi) + (((31307846723 / 50000000000) : ℝ) * (kdot ((31307846723 / 50000000000))))) := badd lowEnergy38_hz12 lowEnergy38_hz13 (by norm_num) (by norm_num)

theorem lowEnergy38_hz15 : B (174030273198604889 / 250000000000000000) (696121092794419563 / 1000000000000000000) (kappa ((31307846723 / 50000000000))) := by rw [kappa_eq]; exact lowEnergy38_hz14

theorem lowEnergy38 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (521 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (349488113519 / 500000000000) := by
  have hk1 : kappa q ≤ (311539606353 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((521 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy38_hz7.2.trans (by norm_num))
  have hk2 : kappa ((31307846723 / 50000000000) : ℝ) ≤ (139224218559 / 200000000000) := lowEnergy38_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((394874730993 / 500000000000) : ℝ)) (R := ((79061548739 / 100000000000) : ℝ)) (Q2 := ((31307846723 / 50000000000) : ℝ)) (T := ((835061274391 / 1000000000000) : ℝ))
    (B := ((349488113519 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy39_hz0 : B (674254424924796203 / 1000000000000000000) (337127212462404931 / 500000000000000000) (kdot ((1041 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (561566372327822981 / 1000000000000000000)) (a := (255839976398910677 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (28078318616391149 / 50000000000000000)) (a := (511679952797799899 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy39_hz1 : B (1083681 / 4000000) (1083681 / 4000000) (((1041 / 2000) : ℝ)^2) := bsq (bpoint ((1041 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy39_hz2 : B (2916319 / 4000000) (2916319 / 4000000) ((1 : ℝ) - (((1041 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy39_hz1 (by norm_num) (by norm_num)

theorem lowEnergy39_hz3 : B (426930834562227421 / 500000000000000000) (853861669124454843 / 1000000000000000000) (√((1 : ℝ) - (((1041 / 2000) : ℝ)^2))) := bsqrt lowEnergy39_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy39_hz4 : B (1087170442862827 / 4000000000000000) (271792610715706751 / 1000000000000000000) ((√((1 : ℝ) - (((1041 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy39_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy39_hz5 : B (350949428173356423 / 1000000000000000000) (175474714086681767 / 500000000000000000) (((1041 / 2000) : ℝ) * (kdot ((1041 / 2000)))) := bmul (bpoint ((1041 / 2000) : ℝ)) lowEnergy39_hz0 (by norm_num) (by norm_num)

theorem lowEnergy39_hz6 : B (622742038889063173 / 1000000000000000000) (124548407777814057 / 200000000000000000) (((√((1 : ℝ) - (((1041 / 2000) : ℝ)^2))) / Real.pi) + (((1041 / 2000) : ℝ) * (kdot ((1041 / 2000))))) := badd lowEnergy39_hz4 lowEnergy39_hz5 (by norm_num) (by norm_num)

theorem lowEnergy39_hz7 : B (622742038889063173 / 1000000000000000000) (124548407777814057 / 200000000000000000) (kappa ((1041 / 2000))) := by rw [kappa_eq]; exact lowEnergy39_hz6

theorem lowEnergy39_hz8 : B (715235060342754469 / 1000000000000000000) (357617530171377239 / 500000000000000000) (kdot ((312909402721 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (479738869348360383 / 1000000000000000000)) (a := (223653860606785833 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (239869434674180191 / 500000000000000000)) (a := (223653860606785827 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy39_hz9 : B (48956147155606481 / 125000000000000000) (391649177244851849 / 1000000000000000000) (((312909402721 / 500000000000) : ℝ)^2) := bsq (bpoint ((312909402721 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy39_hz10 : B (608350822755148151 / 1000000000000000000) (76043852844393519 / 125000000000000000) ((1 : ℝ) - (((312909402721 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy39_hz9 (by norm_num) (by norm_num)

theorem lowEnergy39_hz11 : B (155993695097609397 / 200000000000000000) (389984237744023493 / 500000000000000000) (√((1 : ℝ) - (((312909402721 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy39_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy39_hz12 : B (387924494780539 / 1562500000000000) (248271676659544961 / 1000000000000000000) ((√((1 : ℝ) - (((312909402721 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy39_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy39_hz13 : B (111901887768484847 / 250000000000000000) (89521510214787879 / 200000000000000000) (((312909402721 / 500000000000) : ℝ) * (kdot ((312909402721 / 500000000000)))) := bmul (bpoint ((312909402721 / 500000000000) : ℝ)) lowEnergy39_hz8 (by norm_num) (by norm_num)

theorem lowEnergy39_hz14 : B (173969806933371087 / 250000000000000000) (173969806933371089 / 250000000000000000) (((√((1 : ℝ) - (((312909402721 / 500000000000) : ℝ)^2))) / Real.pi) + (((312909402721 / 500000000000) : ℝ) * (kdot ((312909402721 / 500000000000))))) := badd lowEnergy39_hz12 lowEnergy39_hz13 (by norm_num) (by norm_num)

theorem lowEnergy39_hz15 : B (173969806933371087 / 250000000000000000) (173969806933371089 / 250000000000000000) (kappa ((312909402721 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy39_hz14

theorem lowEnergy39 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1041 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (139746731313 / 200000000000) := by
  have hk1 : kappa q ≤ (62274203889 / 100000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1041 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy39_hz7.2.trans (by norm_num))
  have hk2 : kappa ((312909402721 / 500000000000) : ℝ) ≤ (347939613867 / 500000000000) := lowEnergy39_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((19738399107 / 25000000000) : ℝ)) (R := ((197600497421 / 250000000000) : ℝ)) (Q2 := ((312909402721 / 500000000000) : ℝ)) (T := ((166983238419 / 200000000000) : ℝ))
    (B := ((139746731313 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy40_hz0 : B (674068063875522049 / 1000000000000000000) (26962722555021447 / 40000000000000000) (kdot ((13 / 25))) := by
    constructor
    · apply bkdot_lower (q := (28097574347450819 / 50000000000000000)) (a := (255986344024739419 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (561951486949016379 / 1000000000000000000)) (a := (10239453760989133 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy40_hz1 : B (169 / 625) (169 / 625) (((13 / 25) : ℝ)^2) := bsq (bpoint ((13 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy40_hz2 : B (456 / 625) (456 / 625) ((1 : ℝ) - (((13 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy40_hz1 (by norm_num) (by norm_num)

theorem lowEnergy40_hz3 : B (13346347815039139 / 15625000000000000) (854166260162504897 / 1000000000000000000) (√((1 : ℝ) - (((13 / 25) : ℝ)^2))) := bsqrt lowEnergy40_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy40_hz4 : B (54377913010872213 / 200000000000000000) (135944782527180533 / 500000000000000000) ((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) := bdiv lowEnergy40_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy40_hz5 : B (70103078643054293 / 200000000000000000) (350515393215278811 / 1000000000000000000) (((13 / 25) : ℝ) * (kdot ((13 / 25)))) := bmul (bpoint ((13 / 25) : ℝ)) lowEnergy40_hz0 (by norm_num) (by norm_num)

theorem lowEnergy40_hz6 : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) + (((13 / 25) : ℝ) * (kdot ((13 / 25))))) := badd lowEnergy40_hz4 lowEnergy40_hz5 (by norm_num) (by norm_num)

theorem lowEnergy40_hz7 : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (kappa ((13 / 25))) := by rw [kappa_eq]; exact lowEnergy40_hz6

theorem lowEnergy40_hz8 : B (28603885196172297 / 40000000000000000) (715097129904307433 / 1000000000000000000) (kdot ((312740384891 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (480005421993576827 / 1000000000000000000)) (a := (447524381839637493 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (240002710996788413 / 500000000000000000)) (a := (223762190919818741 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy40_hz9 : B (97806548341770821 / 250000000000000000) (78245238673416657 / 200000000000000000) (((312740384891 / 500000000000) : ℝ)^2) := bsq (bpoint ((312740384891 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy40_hz10 : B (121754761326583343 / 200000000000000000) (152193451658229179 / 250000000000000000) ((1 : ℝ) - (((312740384891 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy40_hz9 (by norm_num) (by norm_num)

theorem lowEnergy40_hz11 : B (780239582841653013 / 1000000000000000000) (390119791420826507 / 500000000000000000) (√((1 : ℝ) - (((312740384891 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy40_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy40_hz12 : B (248357972810414883 / 1000000000000000000) (62089493202603721 / 250000000000000000) ((√((1 : ℝ) - (((312740384891 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy40_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy40_hz13 : B (22363975164072253 / 50000000000000000) (223639751640722533 / 500000000000000000) (((312740384891 / 500000000000) : ℝ) * (kdot ((312740384891 / 500000000000)))) := bmul (bpoint ((312740384891 / 500000000000) : ℝ)) lowEnergy40_hz8 (by norm_num) (by norm_num)

theorem lowEnergy40_hz14 : B (695637476091859943 / 1000000000000000000) (13912749521837199 / 20000000000000000) (((√((1 : ℝ) - (((312740384891 / 500000000000) : ℝ)^2))) / Real.pi) + (((312740384891 / 500000000000) : ℝ) * (kdot ((312740384891 / 500000000000))))) := badd lowEnergy40_hz12 lowEnergy40_hz13 (by norm_num) (by norm_num)

theorem lowEnergy40_hz15 : B (695637476091859943 / 1000000000000000000) (13912749521837199 / 20000000000000000) (kappa ((312740384891 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy40_hz14

theorem lowEnergy40 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (13 / 25)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (698491199793 / 1000000000000) := by
  have hk1 : kappa q ≤ (62240495827 / 100000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((13 / 25) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy40_hz7.2.trans (by norm_num))
  have hk2 : kappa ((312740384891 / 500000000000) : ℝ) ≤ (173909369023 / 250000000000) := lowEnergy40_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((789322467861 / 1000000000000) : ℝ)) (R := ((158037698653 / 200000000000) : ℝ)) (Q2 := ((312740384891 / 500000000000) : ℝ)) (T := ((208692788159 / 250000000000) : ℝ))
    (B := ((698491199793 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy41_hz0 : B (168470442306498631 / 250000000000000000) (168470442306502283 / 250000000000000000) (kdot ((1039 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (562336591013450907 / 1000000000000000000)) (a := (512265319000658217 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (281168295506725453 / 500000000000000000)) (a := (64033164875079409 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy41_hz1 : B (1079521 / 4000000) (1079521 / 4000000) (((1039 / 2000) : ℝ)^2) := bsq (bpoint ((1039 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy41_hz2 : B (2920479 / 4000000) (2920479 / 4000000) ((1 : ℝ) - (((1039 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy41_hz1 (by norm_num) (by norm_num)

theorem lowEnergy41_hz3 : B (854470450044938651 / 1000000000000000000) (213617612511234663 / 250000000000000000) (√((1 : ℝ) - (((1039 / 2000) : ℝ)^2))) := bsqrt lowEnergy41_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy41_hz4 : B (135993195850608407 / 500000000000000000) (16999149481326051 / 62500000000000000) ((√((1 : ℝ) - (((1039 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy41_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy41_hz5 : B (70016315822580831 / 200000000000000000) (70016315822582349 / 200000000000000000) (((1039 / 2000) : ℝ) * (kdot ((1039 / 2000)))) := bmul (bpoint ((1039 / 2000) : ℝ)) lowEnergy41_hz0 (by norm_num) (by norm_num)

theorem lowEnergy41_hz6 : B (622067970814120969 / 1000000000000000000) (622067970814128561 / 1000000000000000000) (((√((1 : ℝ) - (((1039 / 2000) : ℝ)^2))) / Real.pi) + (((1039 / 2000) : ℝ) * (kdot ((1039 / 2000))))) := badd lowEnergy41_hz4 lowEnergy41_hz5 (by norm_num) (by norm_num)

theorem lowEnergy41_hz7 : B (622067970814120969 / 1000000000000000000) (622067970814128561 / 1000000000000000000) (kappa ((1039 / 2000))) := by rw [kappa_eq]; exact lowEnergy41_hz6

theorem lowEnergy41_hz8 : B (714959285425032711 / 1000000000000000000) (8936991067812909 / 12500000000000000) (kdot ((625142827453 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (480271863917367779 / 1000000000000000000)) (a := (874493959846389 / 1953125000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (240135931958683889 / 500000000000000000)) (a := (111935226860337789 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy41_hz9 : B (39080355471593133 / 100000000000000000) (390803554715931331 / 1000000000000000000) (((625142827453 / 1000000000000) : ℝ)^2) := bsq (bpoint ((625142827453 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy41_hz10 : B (609196445284068669 / 1000000000000000000) (60919644528406867 / 100000000000000000) ((1 : ℝ) - (((625142827453 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy41_hz9 (by norm_num) (by norm_num)

theorem lowEnergy41_hz11 : B (780510374872793519 / 1000000000000000000) (9756379685909919 / 12500000000000000) (√((1 : ℝ) - (((625142827453 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy41_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy41_hz12 : B (49688833718205339 / 200000000000000000) (31055521073878337 / 125000000000000000) ((√((1 : ℝ) - (((625142827453 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy41_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy41_hz13 : B (446951669204381401 / 1000000000000000000) (13967239662636919 / 31250000000000000) (((625142827453 / 1000000000000) : ℝ) * (kdot ((625142827453 / 1000000000000)))) := bmul (bpoint ((625142827453 / 1000000000000) : ℝ)) lowEnergy41_hz8 (by norm_num) (by norm_num)

theorem lowEnergy41_hz14 : B (21731119931106503 / 31250000000000000) (86924479724426013 / 125000000000000000) (((√((1 : ℝ) - (((625142827453 / 1000000000000) : ℝ)^2))) / Real.pi) + (((625142827453 / 1000000000000) : ℝ) * (kdot ((625142827453 / 1000000000000))))) := badd lowEnergy41_hz12 lowEnergy41_hz13 (by norm_num) (by norm_num)

theorem lowEnergy41_hz15 : B (21731119931106503 / 31250000000000000) (86924479724426013 / 125000000000000000) (kappa ((625142827453 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy41_hz14

theorem lowEnergy41 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1039 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (698248856647 / 1000000000000) := by
  have hk1 : kappa q ≤ (124413594163 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1039 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy41_hz7.2.trans (by norm_num))
  have hk2 : kappa ((625142827453 / 1000000000000) : ℝ) ≤ (173848959449 / 250000000000) := lowEnergy41_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((789108972713 / 1000000000000) : ℝ)) (R := ((789974998117 / 1000000000000) : ℝ)) (Q2 := ((625142827453 / 1000000000000) : ℝ)) (T := ((104328269499 / 125000000000) : ℝ))
    (B := ((698248856647 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy42_hz0 : B (673695540841546517 / 1000000000000000000) (84211942605195203 / 125000000000000000) (kdot ((519 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (56272168479265029 / 100000000000000000)) (a := (512557845862894093 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (562721684792650289 / 1000000000000000000)) (a := (102511569172574073 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy42_hz1 : B (269361 / 1000000) (269361 / 1000000) (((519 / 1000) : ℝ)^2) := bsq (bpoint ((519 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy42_hz2 : B (730639 / 1000000) (730639 / 1000000) ((1 : ℝ) - (((519 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy42_hz1 (by norm_num) (by norm_num)

theorem lowEnergy42_hz3 : B (854774239200035789 / 1000000000000000000) (85477423920003579 / 100000000000000000) (√((1 : ℝ) - (((519 / 1000) : ℝ)^2))) := bsqrt lowEnergy42_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy42_hz4 : B (136041545396299827 / 500000000000000000) (54416618158519931 / 200000000000000000) ((√((1 : ℝ) - (((519 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy42_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy42_hz5 : B (174823992848381321 / 500000000000000000) (349647985696770483 / 1000000000000000000) (((519 / 1000) : ℝ) * (kdot ((519 / 1000)))) := bmul (bpoint ((519 / 1000) : ℝ)) lowEnergy42_hz0 (by norm_num) (by norm_num)

theorem lowEnergy42_hz6 : B (77716384561170287 / 125000000000000000) (310865538244685069 / 500000000000000000) (((√((1 : ℝ) - (((519 / 1000) : ℝ)^2))) / Real.pi) + (((519 / 1000) : ℝ) * (kdot ((519 / 1000))))) := badd lowEnergy42_hz4 lowEnergy42_hz5 (by norm_num) (by norm_num)

theorem lowEnergy42_hz7 : B (77716384561170287 / 125000000000000000) (310865538244685069 / 500000000000000000) (kappa ((519 / 1000))) := by rw [kappa_eq]; exact lowEnergy42_hz6

theorem lowEnergy42_hz8 : B (714821526773756131 / 1000000000000000000) (35741076338687807 / 50000000000000000) (kdot ((39050311151 / 62500000000))) := by
    constructor
    · apply bkdot_lower (q := (240269097655990893 / 500000000000000000)) (a := (447957298224760639 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (96107639062396357 / 200000000000000000)) (a := (447957298224760627 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy42_hz9 : B (15615250442136729 / 40000000000000000) (195190630526709113 / 500000000000000000) (((39050311151 / 62500000000) : ℝ)^2) := bsq (bpoint ((39050311151 / 62500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy42_hz10 : B (304809369473290887 / 500000000000000000) (24384749557863271 / 40000000000000000) ((1 : ℝ) - (((39050311151 / 62500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy42_hz9 (by norm_num) (by norm_num)

theorem lowEnergy42_hz11 : B (780780852061948157 / 1000000000000000000) (390390426030974079 / 500000000000000000) (√((1 : ℝ) - (((39050311151 / 62500000000) : ℝ)^2))) := bsqrt lowEnergy42_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy42_hz12 : B (248530264154321819 / 1000000000000000000) (248530264154321821 / 1000000000000000000) ((√((1 : ℝ) - (((39050311151 / 62500000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy42_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy42_hz13 : B (89324809721433773 / 200000000000000000) (55828006075896109 / 125000000000000000) (((39050311151 / 62500000000) : ℝ) * (kdot ((39050311151 / 62500000000)))) := bmul (bpoint ((39050311151 / 62500000000) : ℝ)) lowEnergy42_hz8 (by norm_num) (by norm_num)

theorem lowEnergy42_hz14 : B (173788578190372671 / 250000000000000000) (695154312761490693 / 1000000000000000000) (((√((1 : ℝ) - (((39050311151 / 62500000000) : ℝ)^2))) / Real.pi) + (((39050311151 / 62500000000) : ℝ) * (kdot ((39050311151 / 62500000000))))) := badd lowEnergy42_hz12 lowEnergy42_hz13 (by norm_num) (by norm_num)

theorem lowEnergy42_hz15 : B (173788578190372671 / 250000000000000000) (695154312761490693 / 1000000000000000000) (kappa ((39050311151 / 62500000000))) := by rw [kappa_eq]; exact lowEnergy42_hz14

theorem lowEnergy42 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (349003313523 / 500000000000) := by
  have hk1 : kappa q ≤ (62173107649 / 100000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((519 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy42_hz7.2.trans (by norm_num))
  have hk2 : kappa ((39050311151 / 62500000000) : ℝ) ≤ (347577156381 / 500000000000) := lowEnergy42_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((197223869703 / 250000000000) : ℝ)) (R := ((98720188027 / 125000000000) : ℝ)) (Q2 := ((39050311151 / 62500000000) : ℝ)) (T := ((104310150267 / 125000000000) : ℝ))
    (B := ((349003313523 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy43_hz0 : B (673509378587840937 / 1000000000000000000) (336754689293928279 / 500000000000000000) (kdot ((1037 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (281553384278861891 / 500000000000000000)) (a := (512850268847202679 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (563106768557723781 / 1000000000000000000)) (a := (512850268847178143 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy43_hz1 : B (1075369 / 4000000) (1075369 / 4000000) (((1037 / 2000) : ℝ)^2) := bsq (bpoint ((1037 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy43_hz2 : B (2924631 / 4000000) (2924631 / 4000000) ((1 : ℝ) - (((1037 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy43_hz1 (by norm_num) (by norm_num)

theorem lowEnergy43_hz3 : B (427538814027451781 / 500000000000000000) (855077628054903563 / 1000000000000000000) (√((1 : ℝ) - (((1037 / 2000) : ℝ)^2))) := bsqrt lowEnergy43_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy43_hz4 : B (136089831232231023 / 500000000000000000) (272179662464462047 / 1000000000000000000) ((√((1 : ℝ) - (((1037 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy43_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy43_hz5 : B (13968584511911821 / 40000000000000000) (174607306398901813 / 500000000000000000) (((1037 / 2000) : ℝ) * (kdot ((1037 / 2000)))) := bmul (bpoint ((1037 / 2000) : ℝ)) lowEnergy43_hz0 (by norm_num) (by norm_num)

theorem lowEnergy43_hz6 : B (621394275262257571 / 1000000000000000000) (621394275262265673 / 1000000000000000000) (((√((1 : ℝ) - (((1037 / 2000) : ℝ)^2))) / Real.pi) + (((1037 / 2000) : ℝ) * (kdot ((1037 / 2000))))) := badd lowEnergy43_hz4 lowEnergy43_hz5 (by norm_num) (by norm_num)

theorem lowEnergy43_hz7 : B (621394275262257571 / 1000000000000000000) (621394275262265673 / 1000000000000000000) (kappa ((1037 / 2000))) := by rw [kappa_eq]; exact lowEnergy43_hz6

theorem lowEnergy43_hz8 : B (22333870431978007 / 31250000000000000) (89335481727912029 / 125000000000000000) (kdot ((624467222641 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (480804416362091209 / 1000000000000000000)) (a := (224086777194821039 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (60100552045261401 / 125000000000000000)) (a := (224086777194821033 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy43_hz9 : B (389959312152964263 / 1000000000000000000) (48744914019120533 / 125000000000000000) (((624467222641 / 1000000000000) : ℝ)^2) := bsq (bpoint ((624467222641 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy43_hz10 : B (76255085980879467 / 125000000000000000) (610040687847035737 / 1000000000000000000) ((1 : ℝ) - (((624467222641 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy43_hz9 (by norm_num) (by norm_num)

theorem lowEnergy43_hz11 : B (390525507440626641 / 500000000000000000) (781051014881253283 / 1000000000000000000) (√((1 : ℝ) - (((624467222641 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy43_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy43_hz12 : B (124308129825292963 / 500000000000000000) (248616259650585927 / 1000000000000000000) ((√((1 : ℝ) - (((624467222641 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy43_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy43_hz13 : B (223148320631700111 / 500000000000000000) (111574160315850057 / 250000000000000000) (((624467222641 / 1000000000000) : ℝ) * (kdot ((624467222641 / 1000000000000)))) := bmul (bpoint ((624467222641 / 1000000000000) : ℝ)) lowEnergy43_hz8 (by norm_num) (by norm_num)

theorem lowEnergy43_hz14 : B (173728225228496537 / 250000000000000000) (138982580182797231 / 200000000000000000) (((√((1 : ℝ) - (((624467222641 / 1000000000000) : ℝ)^2))) / Real.pi) + (((624467222641 / 1000000000000) : ℝ) * (kdot ((624467222641 / 1000000000000))))) := badd lowEnergy43_hz12 lowEnergy43_hz13 (by norm_num) (by norm_num)

theorem lowEnergy43_hz15 : B (173728225228496537 / 250000000000000000) (138982580182797231 / 200000000000000000) (kappa ((624467222641 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy43_hz14

theorem lowEnergy43 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1037 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (697764510909 / 1000000000000) := by
  have hk1 : kappa q ≤ (621394275263 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1037 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy43_hz7.2.trans (by norm_num))
  have hk2 : kappa ((624467222641 / 1000000000000) : ℝ) ≤ (347456450457 / 500000000000) := lowEnergy43_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((788681986141 / 1000000000000) : ℝ)) (R := ((157909602309 / 200000000000) : ℝ)) (Q2 := ((624467222641 / 1000000000000) : ℝ)) (T := ((834336291043 / 1000000000000) : ℝ))
    (B := ((697764510909 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy44_hz0 : B (134664656466173893 / 200000000000000000) (673323282330885619 / 1000000000000000000) (kdot ((259 / 500))) := by
    constructor
    · apply bkdot_lower (q := (70436480322421021 / 125000000000000000)) (a := (256571294082041873 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (563491842579368167 / 1000000000000000000)) (a := (513142588164058373 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy44_hz1 : B (67081 / 250000) (67081 / 250000) (((259 / 500) : ℝ)^2) := bsq (bpoint ((259 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy44_hz2 : B (182919 / 250000) (182919 / 250000) ((1 : ℝ) - (((259 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy44_hz1 (by norm_num) (by norm_num)

theorem lowEnergy44_hz3 : B (427690308517740439 / 500000000000000000) (855380617035480879 / 1000000000000000000) (√((1 : ℝ) - (((259 / 500) : ℝ)^2))) := bsqrt lowEnergy44_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy44_hz4 : B (136138053426192277 / 500000000000000000) (54455221370476911 / 200000000000000000) ((√((1 : ℝ) - (((259 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy44_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy44_hz5 : B (174390730123695191 / 500000000000000000) (348781460247398751 / 1000000000000000000) (((259 / 500) : ℝ) * (kdot ((259 / 500)))) := bmul (bpoint ((259 / 500) : ℝ)) lowEnergy44_hz0 (by norm_num) (by norm_num)

theorem lowEnergy44_hz6 : B (77632195887471867 / 125000000000000000) (310528783549891653 / 500000000000000000) (((√((1 : ℝ) - (((259 / 500) : ℝ)^2))) / Real.pi) + (((259 / 500) : ℝ) * (kdot ((259 / 500))))) := badd lowEnergy44_hz4 lowEnergy44_hz5 (by norm_num) (by norm_num)

theorem lowEnergy44_hz7 : B (77632195887471867 / 125000000000000000) (310528783549891653 / 500000000000000000) (kappa ((259 / 500))) := by rw [kappa_eq]; exact lowEnergy44_hz6

theorem lowEnergy44_hz8 : B (142909253289113591 / 200000000000000000) (178636566611391991 / 250000000000000000) (kdot ((124825912019 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (481070527254255413 / 1000000000000000000)) (a := (56048709517148873 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (120267631813563853 / 250000000000000000)) (a := (448389676137190971 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy44_hz9 : B (48692213473047277 / 125000000000000000) (389537707784378217 / 1000000000000000000) (((124825912019 / 200000000000) : ℝ)^2) := bsq (bpoint ((124825912019 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy44_hz10 : B (610462292215621783 / 1000000000000000000) (76307786526952723 / 125000000000000000) ((1 : ℝ) - (((124825912019 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy44_hz9 (by norm_num) (by norm_num)

theorem lowEnergy44_hz11 : B (15626417276082471 / 20000000000000000) (24416276993878861 / 31250000000000000) (√((1 : ℝ) - (((124825912019 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy44_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy44_hz12 : B (248702155230511579 / 1000000000000000000) (248702155230511581 / 1000000000000000000) ((√((1 : ℝ) - (((124825912019 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy44_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy44_hz13 : B (445969446944196987 / 1000000000000000000) (445969446944196993 / 1000000000000000000) (((124825912019 / 200000000000) : ℝ) * (kdot ((124825912019 / 200000000000)))) := bmul (bpoint ((124825912019 / 200000000000) : ℝ)) lowEnergy44_hz8 (by norm_num) (by norm_num)

theorem lowEnergy44_hz14 : B (347335801087354283 / 500000000000000000) (347335801087354287 / 500000000000000000) (((√((1 : ℝ) - (((124825912019 / 200000000000) : ℝ)^2))) / Real.pi) + (((124825912019 / 200000000000) : ℝ) * (kdot ((124825912019 / 200000000000))))) := badd lowEnergy44_hz12 lowEnergy44_hz13 (by norm_num) (by norm_num)

theorem lowEnergy44_hz15 : B (347335801087354283 / 500000000000000000) (347335801087354287 / 500000000000000000) (kappa ((124825912019 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy44_hz14

theorem lowEnergy44 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (259 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (348761254081 / 500000000000) := by
  have hk1 : kappa q ≤ (6210575671 / 10000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((259 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy44_hz7.2.trans (by norm_num))
  have hk2 : kappa ((124825912019 / 200000000000) : ℝ) ≤ (27786864087 / 40000000000) := lowEnergy44_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((788468494679 / 1000000000000) : ℝ)) (R := ((789334520083 / 1000000000000) : ℝ)) (Q2 := ((124825912019 / 200000000000) : ℝ)) (T := ((83419142269 / 100000000000) : ℝ))
    (B := ((348761254081 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy45_hz0 : B (673137251936951343 / 1000000000000000000) (673137251936968047 / 1000000000000000000) (kdot ((207 / 400))) := by
    constructor
    · apply bkdot_lower (q := (563876907127869759 / 1000000000000000000)) (a := (513434804023522539 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (281938453563934879 / 500000000000000000)) (a := (513434804023496303 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy45_hz1 : B (42849 / 160000) (42849 / 160000) (((207 / 400) : ℝ)^2) := bsq (bpoint ((207 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy45_hz2 : B (117151 / 160000) (117151 / 160000) ((1 : ℝ) - (((207 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy45_hz1 (by norm_num) (by norm_num)

theorem lowEnergy45_hz3 : B (427841603283271179 / 500000000000000000) (855683206566542359 / 1000000000000000000) (√((1 : ℝ) - (((207 / 400) : ℝ)^2))) := bsqrt lowEnergy45_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy45_hz4 : B (13618621204578857 / 50000000000000000) (272372424091577141 / 1000000000000000000) ((√((1 : ℝ) - (((207 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy45_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy45_hz5 : B (2177178299233577 / 6250000000000000) (69669705575476193 / 200000000000000000) (((207 / 400) : ℝ) * (kdot ((207 / 400)))) := bmul (bpoint ((207 / 400) : ℝ)) lowEnergy45_hz0 (by norm_num) (by norm_num)

theorem lowEnergy45_hz6 : B (31036047598447473 / 50000000000000000) (310360475984479053 / 500000000000000000) (((√((1 : ℝ) - (((207 / 400) : ℝ)^2))) / Real.pi) + (((207 / 400) : ℝ) * (kdot ((207 / 400))))) := badd lowEnergy45_hz4 lowEnergy45_hz5 (by norm_num) (by norm_num)

theorem lowEnergy45_hz7 : B (31036047598447473 / 50000000000000000) (310360475984479053 / 500000000000000000) (kappa ((207 / 400))) := by rw [kappa_eq]; exact lowEnergy45_hz6

theorem lowEnergy45_hz8 : B (714408764511990941 / 1000000000000000000) (714408764511990951 / 1000000000000000000) (kdot ((623791990743 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (60167066022016621 / 125000000000000000)) (a := (448605663669380953 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (481336528176132967 / 1000000000000000000)) (a := (22430283183469047 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy45_hz9 : B (389116447715114997 / 1000000000000000000) (194558223857557499 / 500000000000000000) (((623791990743 / 1000000000000) : ℝ)^2) := bsq (bpoint ((623791990743 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy45_hz10 : B (305441776142442501 / 500000000000000000) (610883552284885003 / 1000000000000000000) ((1 : ℝ) - (((623791990743 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy45_hz9 (by norm_num) (by norm_num)

theorem lowEnergy45_hz11 : B (781590399304447061 / 1000000000000000000) (781590399304447063 / 1000000000000000000) (√((1 : ℝ) - (((623791990743 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy45_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy45_hz12 : B (248787951044942047 / 1000000000000000000) (248787951044942049 / 1000000000000000000) ((√((1 : ℝ) - (((623791990743 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy45_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy45_hz13 : B (445642465419181919 / 1000000000000000000) (445642465419181927 / 1000000000000000000) (((623791990743 / 1000000000000) : ℝ) * (kdot ((623791990743 / 1000000000000)))) := bmul (bpoint ((623791990743 / 1000000000000) : ℝ)) lowEnergy45_hz8 (by norm_num) (by norm_num)

theorem lowEnergy45_hz14 : B (347215208232061983 / 500000000000000000) (86803802058015497 / 125000000000000000) (((√((1 : ℝ) - (((623791990743 / 1000000000000) : ℝ)^2))) / Real.pi) + (((623791990743 / 1000000000000) : ℝ) * (kdot ((623791990743 / 1000000000000))))) := badd lowEnergy45_hz12 lowEnergy45_hz13 (by norm_num) (by norm_num)

theorem lowEnergy45_hz15 : B (347215208232061983 / 500000000000000000) (86803802058015497 / 125000000000000000) (kappa ((623791990743 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy45_hz14

theorem lowEnergy45 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (207 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (174320154681 / 250000000000) := by
  have hk1 : kappa q ≤ (620720951969 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((207 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy45_hz7.2.trans (by norm_num))
  have hk2 : kappa ((623791990743 / 1000000000000) : ℝ) ≤ (138886083293 / 200000000000) := lowEnergy45_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((157651000881 / 200000000000) : ℝ)) (R := ((789121029809 / 1000000000000) : ℝ)) (Q2 := ((623791990743 / 1000000000000) : ℝ)) (T := ((834046597051 / 1000000000000) : ℝ))
    (B := ((174320154681 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy46_hz0 : B (672951287272732141 / 1000000000000000000) (168237821818187353 / 250000000000000000) (kdot ((517 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (282130981236553193 / 500000000000000000)) (a := (513726916634991709 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (112852392494621277 / 200000000000000000)) (a := (513726916634964581 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy46_hz1 : B (267289 / 1000000) (267289 / 1000000) (((517 / 1000) : ℝ)^2) := bsq (bpoint ((517 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy46_hz2 : B (732711 / 1000000) (732711 / 1000000) ((1 : ℝ) - (((517 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy46_hz1 (by norm_num) (by norm_num)

theorem lowEnergy46_hz3 : B (427992698535851193 / 500000000000000000) (855985397071702387 / 1000000000000000000) (√((1 : ℝ) - (((517 / 1000) : ℝ)^2))) := bsqrt lowEnergy46_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy46_hz4 : B (272468614316880451 / 1000000000000000000) (68117153579220113 / 250000000000000000) ((√((1 : ℝ) - (((517 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy46_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy46_hz5 : B (86978953880000629 / 250000000000000000) (347915815520011447 / 1000000000000000000) (((517 / 1000) : ℝ) * (kdot ((517 / 1000)))) := bmul (bpoint ((517 / 1000) : ℝ)) lowEnergy46_hz0 (by norm_num) (by norm_num)

theorem lowEnergy46_hz6 : B (620384429836882967 / 1000000000000000000) (620384429836891899 / 1000000000000000000) (((√((1 : ℝ) - (((517 / 1000) : ℝ)^2))) / Real.pi) + (((517 / 1000) : ℝ) * (kdot ((517 / 1000))))) := badd lowEnergy46_hz4 lowEnergy46_hz5 (by norm_num) (by norm_num)

theorem lowEnergy46_hz7 : B (620384429836882967 / 1000000000000000000) (620384429836891899 / 1000000000000000000) (kappa ((517 / 1000))) := by rw [kappa_eq]; exact lowEnergy46_hz6

theorem lowEnergy46_hz8 : B (714271347895932407 / 1000000000000000000) (714271347895932417 / 1000000000000000000) (kdot ((311727257277 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (48160241931175537 / 100000000000000000)) (a := (112205379296281571 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (481602419311755369 / 1000000000000000000)) (a := (44882151718512627 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy46_hz9 : B (388695531717763797 / 1000000000000000000) (194347765858881899 / 500000000000000000) (((311727257277 / 500000000000) : ℝ)^2) := bsq (bpoint ((311727257277 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy46_hz10 : B (305652234141118101 / 500000000000000000) (611304468282236203 / 1000000000000000000) ((1 : ℝ) - (((311727257277 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy46_hz9 (by norm_num) (by norm_num)

theorem lowEnergy46_hz11 : B (97732452731474721 / 125000000000000000) (781859621851797769 / 1000000000000000000) (√((1 : ℝ) - (((311727257277 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy46_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy46_hz12 : B (248873647243347361 / 1000000000000000000) (124436823621673681 / 500000000000000000) ((√((1 : ℝ) - (((311727257277 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy46_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy46_hz13 : B (111328924115572447 / 250000000000000000) (89063139292457959 / 200000000000000000) (((311727257277 / 500000000000) : ℝ) * (kdot ((311727257277 / 500000000000)))) := bmul (bpoint ((311727257277 / 500000000000) : ℝ)) lowEnergy46_hz8 (by norm_num) (by norm_num)

theorem lowEnergy46_hz14 : B (694189343705637149 / 1000000000000000000) (694189343705637157 / 1000000000000000000) (((√((1 : ℝ) - (((311727257277 / 500000000000) : ℝ)^2))) / Real.pi) + (((311727257277 / 500000000000) : ℝ) * (kdot ((311727257277 / 500000000000))))) := badd lowEnergy46_hz12 lowEnergy46_hz13 (by norm_num) (by norm_num)

theorem lowEnergy46_hz15 : B (694189343705637149 / 1000000000000000000) (694189343705637157 / 1000000000000000000) (kappa ((311727257277 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy46_hz14

theorem lowEnergy46 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (517 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (348519421259 / 500000000000) := by
  have hk1 : kappa q ≤ (620384429837 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((517 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy46_hz7.2.trans (by norm_num))
  have hk2 : kappa ((311727257277 / 500000000000) : ℝ) ≤ (347094671853 / 500000000000) := lowEnergy46_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((788041515301 / 1000000000000) : ℝ)) (R := ((157781508141 / 200000000000) : ℝ)) (Q2 := ((311727257277 / 500000000000) : ℝ)) (T := ((416950907051 / 500000000000) : ℝ))
    (B := ((348519421259 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy47_hz0 : B (336382694102591271 / 500000000000000000) (672765388205200401 / 1000000000000000000) (kdot ((1033 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (2205652378455271 / 3906250000000000)) (a := (257009463103726607 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (903435214215279 / 1600000000000000)) (a := (128504731551856291 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy47_hz1 : B (1067089 / 4000000) (1067089 / 4000000) (((1033 / 2000) : ℝ)^2) := bsq (bpoint ((1033 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy47_hz2 : B (2932911 / 4000000) (2932911 / 4000000) ((1 : ℝ) - (((1033 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy47_hz1 (by norm_num) (by norm_num)

theorem lowEnergy47_hz3 : B (856287188973419127 / 1000000000000000000) (107035898621677391 / 125000000000000000) (√((1 : ℝ) - (((1033 / 2000) : ℝ)^2))) := bsqrt lowEnergy47_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy47_hz4 : B (34070584707845887 / 125000000000000000) (136282338831383549 / 500000000000000000) ((√((1 : ℝ) - (((1033 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy47_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy47_hz5 : B (173741661503988391 / 500000000000000000) (43435415375998251 / 125000000000000000) (((1033 / 2000) : ℝ) * (kdot ((1033 / 2000)))) := bmul (bpoint ((1033 / 2000) : ℝ)) lowEnergy47_hz0 (by norm_num) (by norm_num)

theorem lowEnergy47_hz6 : B (310024000335371939 / 500000000000000000) (310024000335376553 / 500000000000000000) (((√((1 : ℝ) - (((1033 / 2000) : ℝ)^2))) / Real.pi) + (((1033 / 2000) : ℝ) * (kdot ((1033 / 2000))))) := badd lowEnergy47_hz4 lowEnergy47_hz5 (by norm_num) (by norm_num)

theorem lowEnergy47_hz7 : B (310024000335371939 / 500000000000000000) (310024000335376553 / 500000000000000000) (kappa ((1033 / 2000))) := by rw [kappa_eq]; exact lowEnergy47_hz6

theorem lowEnergy47_hz8 : B (714134016469854383 / 1000000000000000000) (714134016469854393 / 1000000000000000000) (kdot ((311558565747 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (240934100423522493 / 500000000000000000)) (a := (449037236884763149 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (96373640169408997 / 200000000000000000)) (a := (89807447376952627 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy47_hz9 : B (194137479780655443 / 500000000000000000) (388274959561310887 / 1000000000000000000) (((311558565747 / 500000000000) : ℝ)^2) := bsq (bpoint ((311558565747 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy47_hz10 : B (611725040438689113 / 1000000000000000000) (305862520219344557 / 500000000000000000) ((1 : ℝ) - (((311558565747 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy47_hz9 (by norm_num) (by norm_num)

theorem lowEnergy47_hz11 : B (391064265958515159 / 500000000000000000) (782128531917030319 / 1000000000000000000) (√((1 : ℝ) - (((311558565747 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy47_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy47_hz12 : B (24895924397560521 / 100000000000000000) (248959243975605211 / 1000000000000000000) ((√((1 : ℝ) - (((311558565747 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy47_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy47_hz13 : B (88997827968996923 / 200000000000000000) (222494569922492311 / 500000000000000000) (((311558565747 / 500000000000) : ℝ) * (kdot ((311558565747 / 500000000000)))) := bmul (bpoint ((311558565747 / 500000000000) : ℝ)) lowEnergy47_hz8 (by norm_num) (by norm_num)

theorem lowEnergy47_hz14 : B (27757935352823593 / 40000000000000000) (693948383820589833 / 1000000000000000000) (((√((1 : ℝ) - (((311558565747 / 500000000000) : ℝ)^2))) / Real.pi) + (((311558565747 / 500000000000) : ℝ) * (kdot ((311558565747 / 500000000000))))) := badd lowEnergy47_hz12 lowEnergy47_hz13 (by norm_num) (by norm_num)

theorem lowEnergy47_hz15 : B (27757935352823593 / 40000000000000000) (693948383820589833 / 1000000000000000000) (kappa ((311558565747 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy47_hz14

theorem lowEnergy47 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1033 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (87099647433 / 125000000000) := by
  have hk1 : kappa q ≤ (620048000671 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1033 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy47_hz7.2.trans (by norm_num))
  have hk2 : kappa ((311558565747 / 500000000000) : ℝ) ≤ (693948383821 / 1000000000000) := lowEnergy47_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((393914013673 / 500000000000) : ℝ)) (R := ((3154776211 / 4000000000) : ℝ)) (Q2 := ((311558565747 / 500000000000) : ℝ)) (T := ((416878536909 / 500000000000) : ℝ))
    (B := ((87099647433 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy48_hz0 : B (672579554601597137 / 1000000000000000000) (336289777300807801 / 500000000000000000) (kdot ((129 / 250))) := by
    constructor
    · apply bkdot_lower (q := (565032046631265529 / 1000000000000000000)) (a := (128577708237340057 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (70629005828908191 / 125000000000000000)) (a := (20572433317973249 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy48_hz1 : B (16641 / 62500) (16641 / 62500) (((129 / 250) : ℝ)^2) := bsq (bpoint ((129 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy48_hz2 : B (45859 / 62500) (45859 / 62500) ((1 : ℝ) - (((129 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy48_hz1 (by norm_num) (by norm_num)

theorem lowEnergy48_hz3 : B (856588582692998541 / 1000000000000000000) (428294291346499271 / 500000000000000000) (√((1 : ℝ) - (((129 / 250) : ℝ)^2))) := bsqrt lowEnergy48_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy48_hz4 : B (272660614263342929 / 1000000000000000000) (27266061426334293 / 100000000000000000) ((√((1 : ℝ) - (((129 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy48_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy48_hz5 : B (173525525087212061 / 500000000000000000) (347051050174433651 / 1000000000000000000) (((129 / 250) : ℝ) * (kdot ((129 / 250)))) := bmul (bpoint ((129 / 250) : ℝ)) lowEnergy48_hz0 (by norm_num) (by norm_num)

theorem lowEnergy48_hz6 : B (619711664437767051 / 1000000000000000000) (619711664437776581 / 1000000000000000000) (((√((1 : ℝ) - (((129 / 250) : ℝ)^2))) / Real.pi) + (((129 / 250) : ℝ) * (kdot ((129 / 250))))) := badd lowEnergy48_hz4 lowEnergy48_hz5 (by norm_num) (by norm_num)

theorem lowEnergy48_hz7 : B (619711664437767051 / 1000000000000000000) (619711664437776581 / 1000000000000000000) (kappa ((129 / 250))) := by rw [kappa_eq]; exact lowEnergy48_hz6

theorem lowEnergy48_hz8 : B (356998385053267591 / 500000000000000000) (713996770106535191 / 1000000000000000000) (kdot ((622779841529 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (482133872967452347 / 1000000000000000000)) (a := (112313205742032727 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (241066936483726173 / 500000000000000000)) (a := (224626411484065447 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy48_hz9 : B (387854731014886353 / 1000000000000000000) (193927365507443177 / 500000000000000000) (((622779841529 / 1000000000000) : ℝ)^2) := bsq (bpoint ((622779841529 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy48_hz10 : B (306072634492556823 / 500000000000000000) (612145268985113647 / 1000000000000000000) ((1 : ℝ) - (((622779841529 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy48_hz9 (by norm_num) (by norm_num)

theorem lowEnergy48_hz11 : B (156479425993977067 / 200000000000000000) (782397129969885337 / 1000000000000000000) (√((1 : ℝ) - (((622779841529 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy48_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy48_hz12 : B (124522370695619339 / 500000000000000000) (249044741391238679 / 1000000000000000000) ((√((1 : ℝ) - (((622779841529 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy48_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy48_hz13 : B (17786511813566633 / 40000000000000000) (444662795339165831 / 1000000000000000000) (((622779841529 / 1000000000000) : ℝ) * (kdot ((622779841529 / 1000000000000)))) := bmul (bpoint ((622779841529 / 1000000000000) : ℝ)) lowEnergy48_hz8 (by norm_num) (by norm_num)

theorem lowEnergy48_hz14 : B (693707536730404503 / 1000000000000000000) (69370753673040451 / 100000000000000000) (((√((1 : ℝ) - (((622779841529 / 1000000000000) : ℝ)^2))) / Real.pi) + (((622779841529 / 1000000000000) : ℝ) * (kdot ((622779841529 / 1000000000000))))) := badd lowEnergy48_hz12 lowEnergy48_hz13 (by norm_num) (by norm_num)

theorem lowEnergy48_hz15 : B (693707536730404503 / 1000000000000000000) (69370753673040451 / 100000000000000000) (kappa ((622779841529 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy48_hz14

theorem lowEnergy48 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (129 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (348277814743 / 500000000000) := by
  have hk1 : kappa q ≤ (309855832219 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((129 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy48_hz7.2.trans (by norm_num))
  have hk2 : kappa ((622779841529 / 1000000000000) : ℝ) ≤ (693707536731 / 1000000000000) := lowEnergy48_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((19690363513 / 25000000000) : ℝ)) (R := ((197120141481 / 250000000000) : ℝ)) (Q2 := ((622779841529 / 1000000000000) : ℝ)) (T := ((33344495047 / 40000000000) : ℝ))
    (B := ((348277814743 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy49_hz0 : B (168098446582398303 / 250000000000000000) (672393786329612303 / 1000000000000000000) (kdot ((1031 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (14135426899547977 / 25000000000000000)) (a := (514602637068659029 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (565417075981919079 / 1000000000000000000)) (a := (257301318534314521 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy49_hz1 : B (1062961 / 4000000) (1062961 / 4000000) (((1031 / 2000) : ℝ)^2) := bsq (bpoint ((1031 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy49_hz2 : B (2937039 / 4000000) (2937039 / 4000000) ((1 : ℝ) - (((1031 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy49_hz1 (by norm_num) (by norm_num)

theorem lowEnergy49_hz3 : B (214222394662649591 / 250000000000000000) (171377915730119673 / 200000000000000000) (√((1 : ℝ) - (((1031 / 2000) : ℝ)^2))) := bsqrt lowEnergy49_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy49_hz4 : B (27275642425234831 / 100000000000000000) (272756424252348311 / 1000000000000000000) ((√((1 : ℝ) - (((1031 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy49_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy49_hz5 : B (3466189968529053 / 10000000000000000) (346618996852915143 / 1000000000000000000) (((1031 / 2000) : ℝ) * (kdot ((1031 / 2000)))) := bmul (bpoint ((1031 / 2000) : ℝ)) lowEnergy49_hz0 (by norm_num) (by norm_num)

theorem lowEnergy49_hz6 : B (61937542110525361 / 100000000000000000) (309687710552631727 / 500000000000000000) (((√((1 : ℝ) - (((1031 / 2000) : ℝ)^2))) / Real.pi) + (((1031 / 2000) : ℝ) * (kdot ((1031 / 2000))))) := badd lowEnergy49_hz4 lowEnergy49_hz5 (by norm_num) (by norm_num)

theorem lowEnergy49_hz7 : B (61937542110525361 / 100000000000000000) (309687710552631727 / 500000000000000000) (kappa ((1031 / 2000))) := by rw [kappa_eq]; exact lowEnergy49_hz6

theorem lowEnergy49_hz8 : B (35692980434034753 / 50000000000000000) (71385960868069507 / 100000000000000000) (kdot ((622442644629 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (482399435854807859 / 1000000000000000000)) (a := (224734137816009261 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (241199717927403929 / 500000000000000000)) (a := (449468275632018507 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy49_hz9 : B (193717422926371791 / 500000000000000000) (387434845852743583 / 1000000000000000000) (((622442644629 / 1000000000000) : ℝ)^2) := bsq (bpoint ((622442644629 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy49_hz10 : B (612565154147256417 / 1000000000000000000) (306282577073628209 / 500000000000000000) ((1 : ℝ) - (((622442644629 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy49_hz9 (by norm_num) (by norm_num)

theorem lowEnergy49_hz11 : B (391332708237906053 / 500000000000000000) (195666354118953027 / 250000000000000000) (√((1 : ℝ) - (((622442644629 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy49_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy49_hz12 : B (1993041117107239 / 8000000000000000) (249130139638404877 / 1000000000000000000) ((√((1 : ℝ) - (((622442644629 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy49_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy49_hz13 : B (222168331360517439 / 500000000000000000) (88867332544206977 / 200000000000000000) (((622442644629 / 1000000000000) : ℝ) * (kdot ((622442644629 / 1000000000000)))) := bmul (bpoint ((622442644629 / 1000000000000) : ℝ)) lowEnergy49_hz8 (by norm_num) (by norm_num)

theorem lowEnergy49_hz14 : B (693466802359439753 / 1000000000000000000) (346733401179719881 / 500000000000000000) (((√((1 : ℝ) - (((622442644629 / 1000000000000) : ℝ)^2))) / Real.pi) + (((622442644629 / 1000000000000) : ℝ) * (kdot ((622442644629 / 1000000000000))))) := badd lowEnergy49_hz12 lowEnergy49_hz13 (by norm_num) (by norm_num)

theorem lowEnergy49_hz15 : B (693466802359439753 / 1000000000000000000) (346733401179719881 / 500000000000000000) (kappa ((622442644629 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy49_hz14

theorem lowEnergy49 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1031 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (348157096253 / 500000000000) := by
  have hk1 : kappa q ≤ (309687710553 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1031 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy49_hz7.2.trans (by norm_num))
  have hk2 : kappa ((622442644629 / 1000000000000) : ℝ) ≤ (17336670059 / 25000000000) := lowEnergy49_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((196850263701 / 250000000000) : ℝ)) (R := ((49266692513 / 62500000000) : ℝ)) (Q2 := ((622442644629 / 1000000000000) : ℝ)) (T := ((208366930287 / 250000000000) : ℝ))
    (B := ((348157096253 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy50_hz0 : B (336104041628554777 / 500000000000000000) (672208083257129293 / 1000000000000000000) (kdot ((103 / 200))) := by
    constructor
    · apply bkdot_lower (q := (141450524301193413 / 250000000000000000)) (a := (102978867754558177 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (565802097204773651 / 1000000000000000000)) (a := (514894338772759881 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy50_hz1 : B (10609 / 40000) (10609 / 40000) (((103 / 200) : ℝ)^2) := bsq (bpoint ((103 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy50_hz2 : B (29391 / 40000) (29391 / 40000) ((1 : ℝ) - (((103 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy50_hz1 (by norm_num) (by norm_num)

theorem lowEnergy50_hz3 : B (428595088632616041 / 500000000000000000) (857190177265232083 / 1000000000000000000) (√((1 : ℝ) - (((103 / 200) : ℝ)^2))) := bsqrt lowEnergy50_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy50_hz4 : B (136426053881579687 / 500000000000000000) (87312674484211 / 320000000000000) ((√((1 : ℝ) - (((103 / 200) : ℝ)^2))) / Real.pi) := bdiv lowEnergy50_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy50_hz5 : B (17309358143870571 / 50000000000000000) (173093581438710793 / 500000000000000000) (((103 / 200) : ℝ) * (kdot ((103 / 200)))) := bmul (bpoint ((103 / 200) : ℝ)) lowEnergy50_hz0 (by norm_num) (by norm_num)

theorem lowEnergy50_hz6 : B (309519635320285397 / 500000000000000000) (619039270640580961 / 1000000000000000000) (((√((1 : ℝ) - (((103 / 200) : ℝ)^2))) / Real.pi) + (((103 / 200) : ℝ) * (kdot ((103 / 200))))) := badd lowEnergy50_hz4 lowEnergy50_hz5 (by norm_num) (by norm_num)

theorem lowEnergy50_hz7 : B (309519635320285397 / 500000000000000000) (619039270640580961 / 1000000000000000000) (kappa ((103 / 200))) := by rw [kappa_eq]; exact lowEnergy50_hz6

theorem lowEnergy50_hz8 : B (142744506413066651 / 200000000000000000) (356861266032666633 / 500000000000000000) (kdot ((622105540759 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (482664889694412263 / 1000000000000000000)) (a := (449683595075918321 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (241332444847206131 / 500000000000000000)) (a := (224841797537959153 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy50_hz9 : B (38701530384304781 / 100000000000000000) (387015303843047811 / 1000000000000000000) (((622105540759 / 1000000000000) : ℝ)^2) := bsq (bpoint ((622105540759 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy50_hz10 : B (612984696156952189 / 1000000000000000000) (61298469615695219 / 100000000000000000) ((1 : ℝ) - (((622105540759 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy50_hz9 (by norm_num) (by norm_num)

theorem lowEnergy50_hz11 : B (782933391903137689 / 1000000000000000000) (78293339190313769 / 100000000000000000) (√((1 : ℝ) - (((622105540759 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy50_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy50_hz12 : B (124607719433088467 / 500000000000000000) (31151929858272117 / 125000000000000000) ((√((1 : ℝ) - (((622105540759 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy50_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy50_hz13 : B (444010741762386861 / 1000000000000000000) (444010741762386869 / 1000000000000000000) (((622105540759 / 1000000000000) : ℝ) * (kdot ((622105540759 / 1000000000000)))) := bmul (bpoint ((622105540759 / 1000000000000) : ℝ)) lowEnergy50_hz8 (by norm_num) (by norm_num)

theorem lowEnergy50_hz14 : B (138645236125712759 / 200000000000000000) (138645236125712761 / 200000000000000000) (((√((1 : ℝ) - (((622105540759 / 1000000000000) : ℝ)^2))) / Real.pi) + (((622105540759 / 1000000000000) : ℝ) * (kdot ((622105540759 / 1000000000000))))) := badd lowEnergy50_hz12 lowEnergy50_hz13 (by norm_num) (by norm_num)

theorem lowEnergy50_hz15 : B (138645236125712759 / 200000000000000000) (138645236125712761 / 200000000000000000) (kappa ((622105540759 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy50_hz14

theorem lowEnergy50 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (103 / 200)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (139214573689 / 200000000000) := by
  have hk1 : kappa q ≤ (619039270641 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((103 / 200) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy50_hz7.2.trans (by norm_num))
  have hk2 : kappa ((622105540759 / 1000000000000) : ℝ) ≤ (693226180629 / 1000000000000) := lowEnergy50_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((787187570177 / 1000000000000) : ℝ)) (R := ((788053595581 / 1000000000000) : ℝ)) (Q2 := ((622105540759 / 1000000000000) : ℝ)) (T := ((833323108713 / 1000000000000) : ℝ))
    (B := ((139214573689 / 200000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy51_hz0 : B (134404489050481051 / 200000000000000000) (672022445252425663 / 1000000000000000000) (kdot ((1029 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (56618711056769421 / 100000000000000000)) (a := (515185938268693931 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (566187110567694209 / 1000000000000000000)) (a := (128796484567165469 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy51_hz1 : B (1058841 / 4000000) (1058841 / 4000000) (((1029 / 2000) : ℝ)^2) := bsq (bpoint ((1029 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy51_hz2 : B (2941159 / 4000000) (2941159 / 4000000) ((1 : ℝ) - (((1029 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy51_hz1 (by norm_num) (by norm_num)

theorem lowEnergy51_hz3 : B (857490378954772879 / 1000000000000000000) (10718629736934661 / 12500000000000000) (√((1 : ℝ) - (((1029 / 2000) : ℝ)^2))) := bsqrt lowEnergy51_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy51_hz4 : B (136473832464394643 / 500000000000000000) (34118458116098661 / 125000000000000000) ((√((1 : ℝ) - (((1029 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy51_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy51_hz5 : B (345755548082362503 / 1000000000000000000) (86438887020593251 / 250000000000000000) (((1029 / 2000) : ℝ) * (kdot ((1029 / 2000)))) := bmul (bpoint ((1029 / 2000) : ℝ)) lowEnergy51_hz0 (by norm_num) (by norm_num)

theorem lowEnergy51_hz6 : B (618703213011151789 / 1000000000000000000) (154675803252790573 / 250000000000000000) (((√((1 : ℝ) - (((1029 / 2000) : ℝ)^2))) / Real.pi) + (((1029 / 2000) : ℝ) * (kdot ((1029 / 2000))))) := badd lowEnergy51_hz4 lowEnergy51_hz5 (by norm_num) (by norm_num)

theorem lowEnergy51_hz7 : B (618703213011151789 / 1000000000000000000) (154675803252790573 / 250000000000000000) (kappa ((1029 / 2000))) := by rw [kappa_eq]; exact lowEnergy51_hz6

theorem lowEnergy51_hz8 : B (178396385033948639 / 250000000000000000) (356792770067897283 / 500000000000000000) (kdot ((621768529889 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (482930234667162751 / 1000000000000000000)) (a := (28118673843477391 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1931720938668651 / 4000000000000000)) (a := (449898781495638241 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy51_hz9 : B (193298052380164143 / 500000000000000000) (386596104760328287 / 1000000000000000000) (((621768529889 / 1000000000000) : ℝ)^2) := bsq (bpoint ((621768529889 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy51_hz10 : B (613403895239671713 / 1000000000000000000) (306701947619835857 / 500000000000000000) ((1 : ℝ) - (((621768529889 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy51_hz9 (by norm_num) (by norm_num)

theorem lowEnergy51_hz11 : B (783201056715114317 / 1000000000000000000) (391600528357557159 / 500000000000000000) (√((1 : ℝ) - (((621768529889 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy51_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy51_hz12 : B (12465031961100631 / 50000000000000000) (124650319611006311 / 500000000000000000) ((√((1 : ℝ) - (((621768529889 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy51_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy51_hz13 : B (221842516120140493 / 500000000000000000) (443685032240280993 / 1000000000000000000) (((621768529889 / 1000000000000) : ℝ) * (kdot ((621768529889 / 1000000000000)))) := bmul (bpoint ((621768529889 / 1000000000000) : ℝ)) lowEnergy51_hz8 (by norm_num) (by norm_num)

theorem lowEnergy51_hz14 : B (346492835731146803 / 500000000000000000) (138597134292458723 / 200000000000000000) (((√((1 : ℝ) - (((621768529889 / 1000000000000) : ℝ)^2))) / Real.pi) + (((621768529889 / 1000000000000) : ℝ) * (kdot ((621768529889 / 1000000000000))))) := badd lowEnergy51_hz12 lowEnergy51_hz13 (by norm_num) (by norm_num)

theorem lowEnergy51_hz15 : B (346492835731146803 / 500000000000000000) (138597134292458723 / 200000000000000000) (kappa ((621768529889 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy51_hz14

theorem lowEnergy51 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1029 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (695831657229 / 1000000000000) := by
  have hk1 : kappa q ≤ (154675803253 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1029 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy51_hz7.2.trans (by norm_num))
  have hk2 : kappa ((621768529889 / 1000000000000) : ℝ) ≤ (692985671463 / 1000000000000) := lowEnergy51_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((786974086621 / 1000000000000) : ℝ)) (R := ((31513604481 / 40000000000) : ℝ)) (Q2 := ((621768529889 / 1000000000000) : ℝ)) (T := ((833178538847 / 1000000000000) : ℝ))
    (B := ((695831657229 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy52_hz0 : B (335918436092029263 / 500000000000000000) (83979609023009953 / 125000000000000000) (kdot ((257 / 500))) := by
    constructor
    · apply bkdot_lower (q := (4426344658891789 / 7812500000000000)) (a := (64434679470350629 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (566572116338148991 / 1000000000000000000)) (a := (128869358940692973 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy52_hz1 : B (66049 / 250000) (66049 / 250000) (((257 / 500) : ℝ)^2) := bsq (bpoint ((257 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy52_hz2 : B (183951 / 250000) (183951 / 250000) ((1 : ℝ) - (((257 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy52_hz1 (by norm_num) (by norm_num)

theorem lowEnergy52_hz3 : B (857790184135957573 / 1000000000000000000) (428895092067978787 / 500000000000000000) (√((1 : ℝ) - (((257 / 500) : ℝ)^2))) := bsqrt lowEnergy52_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy52_hz4 : B (273043095881889497 / 1000000000000000000) (136521547940944749 / 500000000000000000) ((√((1 : ℝ) - (((257 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy52_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy52_hz5 : B (172662076151303041 / 500000000000000000) (345324152302616927 / 1000000000000000000) (((257 / 500) : ℝ) * (kdot ((257 / 500)))) := bmul (bpoint ((257 / 500) : ℝ)) lowEnergy52_hz0 (by norm_num) (by norm_num)

theorem lowEnergy52_hz6 : B (618367248184495579 / 1000000000000000000) (24734689927380257 / 40000000000000000) (((√((1 : ℝ) - (((257 / 500) : ℝ)^2))) / Real.pi) + (((257 / 500) : ℝ) * (kdot ((257 / 500))))) := badd lowEnergy52_hz4 lowEnergy52_hz5 (by norm_num) (by norm_num)

theorem lowEnergy52_hz7 : B (618367248184495579 / 1000000000000000000) (24734689927380257 / 40000000000000000) (kappa ((257 / 500))) := by rw [kappa_eq]; exact lowEnergy52_hz6

theorem lowEnergy52_hz8 : B (178362158191323899 / 250000000000000000) (713448632765295607 / 1000000000000000000) (kdot ((621431611983 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (241597735479108203 / 500000000000000000)) (a := (450113835090329169 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (96639094191643281 / 200000000000000000)) (a := (225056917545164577 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy52_hz9 : B (386177248371789869 / 1000000000000000000) (38617724837178987 / 100000000000000000) (((621431611983 / 1000000000000) : ℝ)^2) := bsq (bpoint ((621431611983 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy52_hz10 : B (61382275162821013 / 100000000000000000) (613822751628210131 / 1000000000000000000) ((1 : ℝ) - (((621431611983 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy52_hz9 (by norm_num) (by norm_num)

theorem lowEnergy52_hz11 : B (783468411378665687 / 1000000000000000000) (783468411378665689 / 1000000000000000000) (√((1 : ℝ) - (((621431611983 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy52_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy52_hz12 : B (249385740854538363 / 1000000000000000000) (62346435213634591 / 250000000000000000) ((√((1 : ℝ) - (((621431611983 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy52_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy52_hz13 : B (443359533926405033 / 1000000000000000000) (5541994174080063 / 12500000000000000) (((621431611983 / 1000000000000) : ℝ) * (kdot ((621431611983 / 1000000000000)))) := bmul (bpoint ((621431611983 / 1000000000000) : ℝ)) lowEnergy52_hz8 (by norm_num) (by norm_num)

theorem lowEnergy52_hz14 : B (173186318695235849 / 250000000000000000) (173186318695235851 / 250000000000000000) (((√((1 : ℝ) - (((621431611983 / 1000000000000) : ℝ)^2))) / Real.pi) + (((621431611983 / 1000000000000) : ℝ) * (kdot ((621431611983 / 1000000000000))))) := badd lowEnergy52_hz12 lowEnergy52_hz13 (by norm_num) (by norm_num)

theorem lowEnergy52_hz15 : B (173186318695235849 / 250000000000000000) (173186318695235851 / 250000000000000000) (kappa ((621431611983 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy52_hz14

theorem lowEnergy52 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (257 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (86948819847 / 125000000000) := by
  have hk1 : kappa q ≤ (123673449637 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((257 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy52_hz7.2.trans (by norm_num))
  have hk2 : kappa ((621431611983 / 1000000000000) : ℝ) ≤ (692745274781 / 1000000000000) := lowEnergy52_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((393380302057 / 500000000000) : ℝ)) (R := ((393813314759 / 500000000000) : ℝ)) (Q2 := ((621431611983 / 1000000000000) : ℝ)) (T := ((833034011523 / 1000000000000) : ℝ))
    (B := ((86948819847 / 125000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy53_hz0 : B (335825681960482753 / 500000000000000000) (671651363920987319 / 1000000000000000000) (kdot ((1027 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (70869639347901431 / 125000000000000000)) (a := (32235551966316353 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (566957114783211447 / 1000000000000000000)) (a := (257884415730513693 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy53_hz1 : B (1054729 / 4000000) (1054729 / 4000000) (((1027 / 2000) : ℝ)^2) := bsq (bpoint ((1027 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy53_hz2 : B (2945271 / 4000000) (2945271 / 4000000) ((1 : ℝ) - (((1027 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy53_hz1 (by norm_num) (by norm_num)

theorem lowEnergy53_hz3 : B (429044796612195263 / 500000000000000000) (858089593224390527 / 1000000000000000000) (√((1 : ℝ) - (((1027 / 2000) : ℝ)^2))) := bsqrt lowEnergy53_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy53_hz4 : B (273138400754750983 / 1000000000000000000) (34142300094343873 / 125000000000000000) ((√((1 : ℝ) - (((1027 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy53_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy53_hz5 : B (344892975373415787 / 1000000000000000000) (344892975373426989 / 1000000000000000000) (((1027 / 2000) : ℝ) * (kdot ((1027 / 2000)))) := bmul (bpoint ((1027 / 2000) : ℝ)) lowEnergy53_hz0 (by norm_num) (by norm_num)

theorem lowEnergy53_hz6 : B (61803137612816677 / 100000000000000000) (618031376128177973 / 1000000000000000000) (((√((1 : ℝ) - (((1027 / 2000) : ℝ)^2))) / Real.pi) + (((1027 / 2000) : ℝ) * (kdot ((1027 / 2000))))) := badd lowEnergy53_hz4 lowEnergy53_hz5 (by norm_num) (by norm_num)

theorem lowEnergy53_hz7 : B (61803137612816677 / 100000000000000000) (618031376128177973 / 1000000000000000000) (kappa ((1027 / 2000))) := by rw [kappa_eq]; exact lowEnergy53_hz6

theorem lowEnergy53_hz8 : B (356655904914697747 / 500000000000000000) (142662361965879101 / 200000000000000000) (kdot ((62109478701 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (483460598748330809 / 1000000000000000000)) (a := (450328756055462343 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (60432574843541351 / 125000000000000000)) (a := (56291094506932791 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy53_hz9 : B (24109920903187329 / 62500000000000000) (77151746890199453 / 200000000000000000) (((62109478701 / 100000000000) : ℝ)^2) := bsq (bpoint ((62109478701 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy53_hz10 : B (122848253109800547 / 200000000000000000) (38390079096812671 / 62500000000000000) ((1 : ℝ) - (((62109478701 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy53_hz9 (by norm_num) (by norm_num)

theorem lowEnergy53_hz11 : B (195933864088913101 / 250000000000000000) (391867728177826203 / 500000000000000000) (√((1 : ℝ) - (((62109478701 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy53_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy53_hz12 : B (124735371955384479 / 500000000000000000) (249470743910768959 / 1000000000000000000) ((√((1 : ℝ) - (((62109478701 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy53_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy53_hz13 : B (221517123298853009 / 500000000000000000) (221517123298853013 / 500000000000000000) (((62109478701 / 100000000000) : ℝ) * (kdot ((62109478701 / 100000000000)))) := bmul (bpoint ((62109478701 / 100000000000) : ℝ)) lowEnergy53_hz8 (by norm_num) (by norm_num)

theorem lowEnergy53_hz14 : B (21640780953389843 / 31250000000000000) (138500998101694997 / 200000000000000000) (((√((1 : ℝ) - (((62109478701 / 100000000000) : ℝ)^2))) / Real.pi) + (((62109478701 / 100000000000) : ℝ) * (kdot ((62109478701 / 100000000000))))) := badd lowEnergy53_hz12 lowEnergy53_hz13 (by norm_num) (by norm_num)

theorem lowEnergy53_hz15 : B (21640780953389843 / 31250000000000000) (138500998101694997 / 200000000000000000) (kappa ((62109478701 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy53_hz14

theorem lowEnergy53 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1027 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (69534957301 / 100000000000) := by
  have hk1 : kappa q ≤ (618031376129 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1027 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy53_hz7.2.trans (by norm_num))
  have hk2 : kappa ((62109478701 / 100000000000) : ℝ) ≤ (692504990509 / 1000000000000) := lowEnergy53_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((393273561319 / 500000000000) : ℝ)) (R := ((393706574021 / 500000000000) : ℝ)) (Q2 := ((62109478701 / 100000000000) : ℝ)) (T := ((416444763359 / 500000000000) : ℝ))
    (B := ((69534957301 / 100000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy54_hz0 : B (671465920332339097 / 1000000000000000000) (41966620020772603 / 62500000000000000) (kdot ((513 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (283671053084781079 / 500000000000000000)) (a := (129015031392225919 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (567342106169562157 / 1000000000000000000)) (a := (103212025113773651 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy54_hz1 : B (263169 / 1000000) (263169 / 1000000) (((513 / 1000) : ℝ)^2) := bsq (bpoint ((513 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy54_hz2 : B (736831 / 1000000) (736831 / 1000000) ((1 : ℝ) - (((513 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy54_hz1 (by norm_num) (by norm_num)

theorem lowEnergy54_hz3 : B (107298575829318443 / 125000000000000000) (171677721326909509 / 200000000000000000) (√((1 : ℝ) - (((513 / 1000) : ℝ)^2))) := bsqrt lowEnergy54_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy54_hz4 : B (27323357967930549 / 100000000000000000) (68308394919826373 / 250000000000000000) ((√((1 : ℝ) - (((513 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy54_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy54_hz5 : B (86115504282622489 / 250000000000000000) (172231008565250763 / 500000000000000000) (((513 / 1000) : ℝ) * (kdot ((513 / 1000)))) := bmul (bpoint ((513 / 1000) : ℝ)) lowEnergy54_hz0 (by norm_num) (by norm_num)

theorem lowEnergy54_hz6 : B (308847798404897723 / 500000000000000000) (308847798404903509 / 500000000000000000) (((√((1 : ℝ) - (((513 / 1000) : ℝ)^2))) / Real.pi) + (((513 / 1000) : ℝ) * (kdot ((513 / 1000))))) := badd lowEnergy54_hz4 lowEnergy54_hz5 (by norm_num) (by norm_num)

theorem lowEnergy54_hz7 : B (308847798404897723 / 500000000000000000) (308847798404903509 / 500000000000000000) (kappa ((513 / 1000))) := by rw [kappa_eq]; exact lowEnergy54_hz6

theorem lowEnergy54_hz8 : B (178293767800888809 / 250000000000000000) (713175071203555247 / 1000000000000000000) (kdot ((310379027469 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (96745123643718049 / 200000000000000000)) (a := (450543544586663203 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (120931404554647561 / 250000000000000000)) (a := (450543544586663187 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy54_hz9 : B (192670281385204513 / 500000000000000000) (385340562770409027 / 1000000000000000000) (((310379027469 / 500000000000) : ℝ)^2) := bsq (bpoint ((310379027469 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy54_hz10 : B (614659437229590973 / 1000000000000000000) (307329718614795487 / 500000000000000000) ((1 : ℝ) - (((310379027469 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy54_hz9 (by norm_num) (by norm_num)

theorem lowEnergy54_hz11 : B (784002192107643901 / 1000000000000000000) (392001096053821951 / 500000000000000000) (√((1 : ℝ) - (((310379027469 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy54_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy54_hz12 : B (249555648537626519 / 1000000000000000000) (6238891213440663 / 25000000000000000) ((√((1 : ℝ) - (((310379027469 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy54_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy54_hz13 : B (221354585015294301 / 500000000000000000) (44270917003058861 / 100000000000000000) (((310379027469 / 500000000000) : ℝ) * (kdot ((310379027469 / 500000000000)))) := bmul (bpoint ((310379027469 / 500000000000) : ℝ)) lowEnergy54_hz8 (by norm_num) (by norm_num)

theorem lowEnergy54_hz14 : B (692264818568215121 / 1000000000000000000) (69226481856821513 / 100000000000000000) (((√((1 : ℝ) - (((310379027469 / 500000000000) : ℝ)^2))) / Real.pi) + (((310379027469 / 500000000000) : ℝ) * (kdot ((310379027469 / 500000000000))))) := badd lowEnergy54_hz12 lowEnergy54_hz13 (by norm_num) (by norm_num)

theorem lowEnergy54_hz15 : B (692264818568215121 / 1000000000000000000) (69226481856821513 / 100000000000000000) (kappa ((310379027469 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy54_hz14

theorem lowEnergy54 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (43444293741 / 62500000000) := by
  have hk1 : kappa q ≤ (61769559681 / 100000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((513 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy54_hz7.2.trans (by norm_num))
  have hk2 : kappa ((310379027469 / 500000000000) : ℝ) ≤ (692264818569 / 1000000000000) := lowEnergy54_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((196583410543 / 250000000000) : ℝ)) (R := ((98399958447 / 125000000000) : ℝ)) (Q2 := ((310379027469 / 500000000000) : ℝ)) (T := ((832745084409 / 1000000000000) : ℝ))
    (B := ((43444293741 / 62500000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy55_hz0 : B (671280541287707781 / 1000000000000000000) (671280541287731093 / 1000000000000000000) (kdot ((41 / 80))) := by
    constructor
    · apply bkdot_lower (q := (283863545381745373 / 500000000000000000)) (a := (103270263658255059 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (113545418152698149 / 200000000000000000)) (a := (516351318291238677 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy55_hz1 : B (1681 / 6400) (1681 / 6400) (((41 / 80) : ℝ)^2) := bsq (bpoint ((41 / 80) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy55_hz2 : B (4719 / 6400) (4719 / 6400) ((1 : ℝ) - (((41 / 80) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy55_hz1 (by norm_num) (by norm_num)

theorem lowEnergy55_hz3 : B (858687224779779753 / 1000000000000000000) (429343612389889877 / 500000000000000000) (√((1 : ℝ) - (((41 / 80) : ℝ)^2))) := bsqrt lowEnergy55_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy55_hz4 : B (273328632787126769 / 1000000000000000000) (273328632787126771 / 1000000000000000000) ((√((1 : ℝ) - (((41 / 80) : ℝ)^2))) / Real.pi) := bdiv lowEnergy55_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy55_hz5 : B (344031277409950237 / 1000000000000000000) (172015638704981093 / 500000000000000000) (((41 / 80) : ℝ) * (kdot ((41 / 80)))) := bmul (bpoint ((41 / 80) : ℝ)) lowEnergy55_hz0 (by norm_num) (by norm_num)

theorem lowEnergy55_hz6 : B (308679955098538503 / 500000000000000000) (617359910197088957 / 1000000000000000000) (((√((1 : ℝ) - (((41 / 80) : ℝ)^2))) / Real.pi) + (((41 / 80) : ℝ) * (kdot ((41 / 80))))) := badd lowEnergy55_hz4 lowEnergy55_hz5 (by norm_num) (by norm_num)

theorem lowEnergy55_hz7 : B (308679955098538503 / 500000000000000000) (617359910197088957 / 1000000000000000000) (kappa ((41 / 80))) := by rw [kappa_eq]; exact lowEnergy55_hz6

theorem lowEnergy55_hz8 : B (713038416762731399 / 1000000000000000000) (713038416762731411 / 1000000000000000000) (kdot ((620421415733 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (483990529551193741 / 1000000000000000000)) (a := (56344775110043687 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (24199526477559687 / 50000000000000000)) (a := (450758200880349479 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy55_hz9 : B (384922733100140019 / 1000000000000000000) (19246136655007001 / 50000000000000000) (((620421415733 / 1000000000000) : ℝ)^2) := bsq (bpoint ((620421415733 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy55_hz10 : B (30753863344992999 / 50000000000000000) (615077266899859981 / 1000000000000000000) ((1 : ℝ) - (((620421415733 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy55_hz9 (by norm_num) (by norm_num)

theorem lowEnergy55_hz11 : B (784268619096709733 / 1000000000000000000) (156853723819341947 / 200000000000000000) (√((1 : ℝ) - (((620421415733 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy55_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy55_hz12 : B (124820227441096177 / 500000000000000000) (49928090976438471 / 200000000000000000) ((√((1 : ℝ) - (((620421415733 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy55_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy55_hz13 : B (442384303999950693 / 1000000000000000000) (442384303999950701 / 1000000000000000000) (((620421415733 / 1000000000000) : ℝ) * (kdot ((620421415733 / 1000000000000)))) := bmul (bpoint ((620421415733 / 1000000000000) : ℝ)) lowEnergy55_hz8 (by norm_num) (by norm_num)

theorem lowEnergy55_hz14 : B (692024758882143047 / 1000000000000000000) (43251547430133941 / 62500000000000000) (((√((1 : ℝ) - (((620421415733 / 1000000000000) : ℝ)^2))) / Real.pi) + (((620421415733 / 1000000000000) : ℝ) * (kdot ((620421415733 / 1000000000000))))) := badd lowEnergy55_hz12 lowEnergy55_hz13 (by norm_num) (by norm_num)

theorem lowEnergy55_hz15 : B (692024758882143047 / 1000000000000000000) (43251547430133941 / 62500000000000000) (kappa ((620421415733 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy55_hz14

theorem lowEnergy55 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (41 / 80)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (694867939233 / 1000000000000) := by
  have hk1 : kappa q ≤ (308679955099 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((41 / 80) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy55_hz7.2.trans (by norm_num))
  have hk2 : kappa ((620421415733 / 1000000000000) : ℝ) ≤ (692024758883 / 1000000000000) := lowEnergy55_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((786120162697 / 1000000000000) : ℝ)) (R := ((786986188101 / 1000000000000) : ℝ)) (Q2 := ((620421415733 / 1000000000000) : ℝ)) (T := ((832600684569 / 1000000000000) : ℝ))
    (B := ((694867939233 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy56_hz0 : B (83886903332114307 / 125000000000000000) (167773806664234639 / 250000000000000000) (kdot ((64 / 125))) := by
    constructor
    · apply bkdot_lower (q := (568112068830897793 / 1000000000000000000)) (a := (516642409832626801 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (4438375537741389 / 7812500000000000)) (a := (516642409832588947 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy56_hz1 : B (4096 / 15625) (4096 / 15625) (((64 / 125) : ℝ)^2) := bsq (bpoint ((64 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy56_hz2 : B (11529 / 15625) (11529 / 15625) ((1 : ℝ) - (((64 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy56_hz1 (by norm_num) (by norm_num)

theorem lowEnergy56_hz3 : B (429492724036158731 / 500000000000000000) (858985448072317463 / 1000000000000000000) (√((1 : ℝ) - (((64 / 125) : ℝ)^2))) := bsqrt lowEnergy56_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy56_hz4 : B (273423560209431803 / 1000000000000000000) (68355890052357951 / 250000000000000000) ((√((1 : ℝ) - (((64 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy56_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy56_hz5 : B (343600756048340201 / 1000000000000000000) (343600756048352541 / 1000000000000000000) (((64 / 125) : ℝ) * (kdot ((64 / 125)))) := bmul (bpoint ((64 / 125) : ℝ)) lowEnergy56_hz0 (by norm_num) (by norm_num)

theorem lowEnergy56_hz6 : B (154256079064443001 / 250000000000000000) (123404863251556869 / 200000000000000000) (((√((1 : ℝ) - (((64 / 125) : ℝ)^2))) / Real.pi) + (((64 / 125) : ℝ) * (kdot ((64 / 125))))) := badd lowEnergy56_hz4 lowEnergy56_hz5 (by norm_num) (by norm_num)

theorem lowEnergy56_hz7 : B (154256079064443001 / 250000000000000000) (123404863251556869 / 200000000000000000) (kappa ((64 / 125))) := by rw [kappa_eq]; exact lowEnergy56_hz6

theorem lowEnergy56_hz8 : B (712901846383810819 / 1000000000000000000) (712901846383810831 / 1000000000000000000) (kdot ((124016973873 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (24212766646236753 / 50000000000000000)) (a := (450972725129906931 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (484255332924735059 / 1000000000000000000)) (a := (225486362564953457 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy56_hz9 : B (76901049043081823 / 200000000000000000) (96126311303852279 / 250000000000000000) (((124016973873 / 200000000000) : ℝ)^2) := bsq (bpoint ((124016973873 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy56_hz10 : B (153873688696147721 / 250000000000000000) (123098950956918177 / 200000000000000000) ((1 : ℝ) - (((124016973873 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy56_hz9 (by norm_num) (by norm_num)

theorem lowEnergy56_hz11 : B (392267368890336991 / 500000000000000000) (784534737780673983 / 1000000000000000000) (√((1 : ℝ) - (((124016973873 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy56_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy56_hz12 : B (124862581545098197 / 500000000000000000) (49945032618039279 / 200000000000000000) ((√((1 : ℝ) - (((124016973873 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy56_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy56_hz13 : B (442059648284972629 / 1000000000000000000) (442059648284972637 / 1000000000000000000) (((124016973873 / 200000000000) : ℝ) * (kdot ((124016973873 / 200000000000)))) := bmul (bpoint ((124016973873 / 200000000000) : ℝ)) lowEnergy56_hz8 (by norm_num) (by norm_num)

theorem lowEnergy56_hz14 : B (691784811375169023 / 1000000000000000000) (86473101421896129 / 125000000000000000) (((√((1 : ℝ) - (((124016973873 / 200000000000) : ℝ)^2))) / Real.pi) + (((124016973873 / 200000000000) : ℝ) * (kdot ((124016973873 / 200000000000))))) := badd lowEnergy56_hz12 lowEnergy56_hz13 (by norm_num) (by norm_num)

theorem lowEnergy56_hz15 : B (691784811375169023 / 1000000000000000000) (86473101421896129 / 125000000000000000) (kappa ((124016973873 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy56_hz14

theorem lowEnergy56 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (64 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (173656822767 / 250000000000) := by
  have hk1 : kappa q ≤ (308512158129 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((64 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy56_hz7.2.trans (by norm_num))
  have hk2 : kappa ((124016973873 / 200000000000) : ℝ) ≤ (43236550711 / 62500000000) := lowEnergy56_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((785906684193 / 1000000000000) : ℝ)) (R := ((786772709597 / 1000000000000) : ℝ)) (Q2 := ((124016973873 / 200000000000) : ℝ)) (T := ((832456327177 / 1000000000000) : ℝ))
    (B := ((173656822767 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy57_hz0 : B (8386374703876441 / 12500000000000000) (335454988155070097 / 500000000000000000) (kdot ((1023 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (568497040637296729 / 1000000000000000000)) (a := (129233350099229107 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (71062130079662091 / 125000000000000000)) (a := (103386680079375459 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy57_hz1 : B (1046529 / 4000000) (1046529 / 4000000) (((1023 / 2000) : ℝ)^2) := bsq (bpoint ((1023 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy57_hz2 : B (2953471 / 4000000) (2953471 / 4000000) ((1 : ℝ) - (((1023 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy57_hz1 (by norm_num) (by norm_num)

theorem lowEnergy57_hz3 : B (214820819230818501 / 250000000000000000) (171856655384654801 / 200000000000000000) (√((1 : ℝ) - (((1023 / 2000) : ℝ)^2))) := bsqrt lowEnergy57_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy57_hz4 : B (273518362077082029 / 1000000000000000000) (27351836207708203 / 100000000000000000) ((√((1 : ℝ) - (((1023 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy57_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy57_hz5 : B (68634090576524793 / 200000000000000000) (34317045288263671 / 100000000000000000) (((1023 / 2000) : ℝ) * (kdot ((1023 / 2000)))) := bmul (bpoint ((1023 / 2000) : ℝ)) lowEnergy57_hz0 (by norm_num) (by norm_num)

theorem lowEnergy57_hz6 : B (308344407479852997 / 500000000000000000) (30834440747985937 / 50000000000000000) (((√((1 : ℝ) - (((1023 / 2000) : ℝ)^2))) / Real.pi) + (((1023 / 2000) : ℝ) * (kdot ((1023 / 2000))))) := badd lowEnergy57_hz4 lowEnergy57_hz5 (by norm_num) (by norm_num)

theorem lowEnergy57_hz7 : B (308344407479852997 / 500000000000000000) (30834440747985937 / 50000000000000000) (kappa ((1023 / 2000))) := by rw [kappa_eq]; exact lowEnergy57_hz6

theorem lowEnergy57_hz8 : B (178191339985489099 / 250000000000000000) (89095669992744551 / 125000000000000000) (kdot ((619748415799 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (484520028521286483 / 1000000000000000000)) (a := (451187117531429163 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (242260014260643241 / 500000000000000000)) (a := (225593558765714573 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy57_hz9 : B (24005506180335637 / 62500000000000000) (384088098885370193 / 1000000000000000000) (((619748415799 / 1000000000000) : ℝ)^2) := bsq (bpoint ((619748415799 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy57_hz10 : B (615911901114629807 / 1000000000000000000) (38494493819664363 / 62500000000000000) ((1 : ℝ) - (((619748415799 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy57_hz9 (by norm_num) (by norm_num)

theorem lowEnergy57_hz11 : B (31392021944809603 / 40000000000000000) (784800548620240077 / 1000000000000000000) (√((1 : ℝ) - (((619748415799 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy57_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy57_hz12 : B (49961954661657019 / 200000000000000000) (249809773308285097 / 1000000000000000000) ((√((1 : ℝ) - (((619748415799 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy57_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy57_hz13 : B (441735202660431491 / 1000000000000000000) (441735202660431499 / 1000000000000000000) (((619748415799 / 1000000000000) : ℝ) * (kdot ((619748415799 / 1000000000000)))) := bmul (bpoint ((619748415799 / 1000000000000) : ℝ)) lowEnergy57_hz8 (by norm_num) (by norm_num)

theorem lowEnergy57_hz14 : B (345772487984358293 / 500000000000000000) (172886243992179149 / 250000000000000000) (((√((1 : ℝ) - (((619748415799 / 1000000000000) : ℝ)^2))) / Real.pi) + (((619748415799 / 1000000000000) : ℝ) * (kdot ((619748415799 / 1000000000000))))) := badd lowEnergy57_hz12 lowEnergy57_hz13 (by norm_num) (by norm_num)

theorem lowEnergy57_hz15 : B (345772487984358293 / 500000000000000000) (172886243992179149 / 250000000000000000) (kappa ((619748415799 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy57_hz14

theorem lowEnergy57 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1023 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (8679834441 / 12500000000) := by
  have hk1 : kappa q ≤ (7708610187 / 12500000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1023 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy57_hz7.2.trans (by norm_num))
  have hk2 : kappa ((619748415799 / 1000000000000) : ℝ) ≤ (691544975969 / 1000000000000) := lowEnergy57_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((9821165083 / 12500000000) : ℝ)) (R := ((196639808011 / 250000000000) : ℝ)) (Q2 := ((619748415799 / 1000000000000) : ℝ)) (T := ((416156006103 / 500000000000) : ℝ))
    (B := ((8679834441 / 12500000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy58_hz0 : B (167681197529444627 / 250000000000000000) (335362395058902131 / 500000000000000000) (kdot ((511 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (568882006447815727 / 1000000000000000000)) (a := (258612145093806081 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (284441003223907863 / 500000000000000000)) (a := (51722429018757171 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy58_hz1 : B (261121 / 1000000) (261121 / 1000000) (((511 / 1000) : ℝ)^2) := bsq (bpoint ((511 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy58_hz2 : B (738879 / 1000000) (738879 / 1000000) ((1 : ℝ) - (((511 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy58_hz1 (by norm_num) (by norm_num)

theorem lowEnergy58_hz3 : B (429790355871324781 / 500000000000000000) (859580711742649563 / 1000000000000000000) (√((1 : ℝ) - (((511 / 1000) : ℝ)^2))) := bsqrt lowEnergy58_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy58_hz4 : B (273613038520584559 / 1000000000000000000) (3420162981507307 / 12500000000000000) ((√((1 : ℝ) - (((511 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy58_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy58_hz5 : B (342740367750184817 / 1000000000000000000) (171370183875098989 / 500000000000000000) (((511 / 1000) : ℝ) * (kdot ((511 / 1000)))) := bmul (bpoint ((511 / 1000) : ℝ)) lowEnergy58_hz0 (by norm_num) (by norm_num)

theorem lowEnergy58_hz6 : B (19261043945961543 / 31250000000000000) (308176703135391269 / 500000000000000000) (((√((1 : ℝ) - (((511 / 1000) : ℝ)^2))) / Real.pi) + (((511 / 1000) : ℝ) * (kdot ((511 / 1000))))) := badd lowEnergy58_hz4 lowEnergy58_hz5 (by norm_num) (by norm_num)

theorem lowEnergy58_hz7 : B (19261043945961543 / 31250000000000000) (308176703135391269 / 500000000000000000) (kappa ((511 / 1000))) := by rw [kappa_eq]; exact lowEnergy58_hz6

theorem lowEnergy58_hz8 : B (178157239328767367 / 250000000000000000) (17815723932876737 / 25000000000000000) (kdot ((309706027503 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (242392308258872819 / 500000000000000000)) (a := (18056055131068333 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (484784616517745637 / 1000000000000000000)) (a := (451401378276708307 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy58_hz9 : B (383671293886755969 / 1000000000000000000) (38367129388675597 / 100000000000000000) (((309706027503 / 500000000000) : ℝ)^2) := bsq (bpoint ((309706027503 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy58_hz10 : B (61632870611324403 / 100000000000000000) (616328706113244031 / 1000000000000000000) ((1 : ℝ) - (((309706027503 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy58_hz9 (by norm_num) (by norm_num)

theorem lowEnergy58_hz11 : B (392533026035149057 / 500000000000000000) (157013210414059623 / 200000000000000000) (√((1 : ℝ) - (((309706027503 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy58_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy58_hz12 : B (249894285681254473 / 1000000000000000000) (124947142840627237 / 500000000000000000) ((√((1 : ℝ) - (((309706027503 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy58_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy58_hz13 : B (88282193381462047 / 200000000000000000) (441410966907310243 / 1000000000000000000) (((309706027503 / 500000000000) : ℝ) * (kdot ((309706027503 / 500000000000)))) := bmul (bpoint ((309706027503 / 500000000000) : ℝ)) lowEnergy58_hz8 (by norm_num) (by norm_num)

theorem lowEnergy58_hz14 : B (172826313147141177 / 250000000000000000) (691305252588564717 / 1000000000000000000) (((√((1 : ℝ) - (((309706027503 / 500000000000) : ℝ)^2))) / Real.pi) + (((309706027503 / 500000000000) : ℝ) * (kdot ((309706027503 / 500000000000))))) := badd lowEnergy58_hz12 lowEnergy58_hz13 (by norm_num) (by norm_num)

theorem lowEnergy58_hz15 : B (172826313147141177 / 250000000000000000) (691305252588564717 / 1000000000000000000) (kappa ((309706027503 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy58_hz14

theorem lowEnergy58 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (694146331799 / 1000000000000) := by
  have hk1 : kappa q ≤ (616353406271 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((511 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy58_hz7.2.trans (by norm_num))
  have hk2 : kappa ((309706027503 / 500000000000) : ℝ) ≤ (691305252589 / 1000000000000) := lowEnergy58_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((39273986501 / 50000000000) : ℝ)) (R := ((24573304857 / 31250000000) : ℝ)) (Q2 := ((309706027503 / 500000000000) : ℝ)) (T := ((208041934909 / 250000000000) : ℝ))
    (B := ((694146331799 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy59_hz0 : B (335269833975341673 / 500000000000000000) (670539667950709967 / 1000000000000000000) (kdot ((1021 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (569266966527199587 / 1000000000000000000)) (a := (103503015881538711 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (284633483263599793 / 500000000000000000)) (a := (25875753970382587 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy59_hz1 : B (1042441 / 4000000) (1042441 / 4000000) (((1021 / 2000) : ℝ)^2) := bsq (bpoint ((1021 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy59_hz2 : B (2957559 / 4000000) (2957559 / 4000000) ((1 : ℝ) - (((1021 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy59_hz1 (by norm_num) (by norm_num)

theorem lowEnergy59_hz3 : B (13435589889677109 / 15625000000000000) (859877752939334977 / 1000000000000000000) (√((1 : ℝ) - (((1021 / 2000) : ℝ)^2))) := bsqrt lowEnergy59_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy59_hz4 : B (27370758967009339 / 100000000000000000) (17106724354380837 / 62500000000000000) ((√((1 : ℝ) - (((1021 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy59_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy59_hz5 : B (42788812561102981 / 125000000000000000) (342310500488837439 / 1000000000000000000) (((1021 / 2000) : ℝ) * (kdot ((1021 / 2000)))) := bmul (bpoint ((1021 / 2000) : ℝ)) lowEnergy59_hz0 (by norm_num) (by norm_num)

theorem lowEnergy59_hz6 : B (308009045079458619 / 500000000000000000) (616018090158930831 / 1000000000000000000) (((√((1 : ℝ) - (((1021 / 2000) : ℝ)^2))) / Real.pi) + (((1021 / 2000) : ℝ) * (kdot ((1021 / 2000))))) := badd lowEnergy59_hz4 lowEnergy59_hz5 (by norm_num) (by norm_num)

theorem lowEnergy59_hz7 : B (308009045079458619 / 500000000000000000) (616018090158930831 / 1000000000000000000) (kappa ((1021 / 2000))) := by rw [kappa_eq]; exact lowEnergy59_hz6

theorem lowEnergy59_hz8 : B (178123159594730193 / 250000000000000000) (44530789898682549 / 62500000000000000) (kdot ((619075786951 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (60631137136909729 / 125000000000000000)) (a := (90323101512176657 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (485049097095277831 / 1000000000000000000)) (a := (451615507560883267 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy59_hz9 : B (383254829988999941 / 1000000000000000000) (191627414994499971 / 500000000000000000) (((619075786951 / 1000000000000) : ℝ)^2) := bsq (bpoint ((619075786951 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy59_hz10 : B (308372585005500029 / 500000000000000000) (616745170011000059 / 1000000000000000000) ((1 : ℝ) - (((619075786951 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy59_hz9 (by norm_num) (by norm_num)

theorem lowEnergy59_hz11 : B (785331248589408963 / 1000000000000000000) (157066249717881793 / 200000000000000000) (√((1 : ℝ) - (((619075786951 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy59_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy59_hz12 : B (49995740071013797 / 200000000000000000) (249978700355068987 / 1000000000000000000) ((√((1 : ℝ) - (((619075786951 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy59_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy59_hz13 : B (441086940801224641 / 1000000000000000000) (8821738816024493 / 20000000000000000) (((619075786951 / 1000000000000) : ℝ) * (kdot ((619075786951 / 1000000000000)))) := bmul (bpoint ((619075786951 / 1000000000000) : ℝ)) lowEnergy59_hz8 (by norm_num) (by norm_num)

theorem lowEnergy59_hz14 : B (345532820578146813 / 500000000000000000) (691065641156293637 / 1000000000000000000) (((√((1 : ℝ) - (((619075786951 / 1000000000000) : ℝ)^2))) / Real.pi) + (((619075786951 / 1000000000000) : ℝ) * (kdot ((619075786951 / 1000000000000))))) := badd lowEnergy59_hz12 lowEnergy59_hz13 (by norm_num) (by norm_num)

theorem lowEnergy59_hz15 : B (345532820578146813 / 500000000000000000) (691065641156293637 / 1000000000000000000) (kappa ((619075786951 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy59_hz14

theorem lowEnergy59 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1021 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (346953010271 / 500000000000) := by
  have hk1 : kappa q ≤ (616018090159 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1021 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy59_hz7.2.trans (by norm_num))
  have hk2 : kappa ((619075786951 / 1000000000000) : ℝ) ≤ (691065641157 / 1000000000000) := lowEnergy59_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((785266254311 / 1000000000000) : ℝ)) (R := ((157226455943 / 200000000000) : ℝ)) (Q2 := ((619075786951 / 1000000000000) : ℝ)) (T := ((832023509439 / 1000000000000) : ℝ))
    (B := ((346953010271 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy60_hz0 : B (335177304839959399 / 500000000000000000) (167588652419986579 / 250000000000000000) (kdot ((51 / 100))) := by
    constructor
    · apply bkdot_lower (q := (569651921139811611 / 1000000000000000000)) (a := (258902884129826761 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56965192113981161 / 100000000000000000)) (a := (258902884129805149 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy60_hz1 : B (2601 / 10000) (2601 / 10000) (((51 / 100) : ℝ)^2) := bsq (bpoint ((51 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy60_hz2 : B (7399 / 10000) (7399 / 10000) ((1 : ℝ) - (((51 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy60_hz1 (by norm_num) (by norm_num)

theorem lowEnergy60_hz3 : B (860174400921115531 / 1000000000000000000) (215043600230278883 / 250000000000000000) (√((1 : ℝ) - (((51 / 100) : ℝ)^2))) := bsqrt lowEnergy60_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy60_hz4 : B (27380201565541061 / 100000000000000000) (273802015655410611 / 1000000000000000000) ((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) := bdiv lowEnergy60_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy60_hz5 : B (170940425468379293 / 500000000000000000) (170940425468386311 / 500000000000000000) (((51 / 100) : ℝ) * (kdot ((51 / 100)))) := bmul (bpoint ((51 / 100) : ℝ)) lowEnergy60_hz0 (by norm_num) (by norm_num)

theorem lowEnergy60_hz6 : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) + (((51 / 100) : ℝ) * (kdot ((51 / 100))))) := badd lowEnergy60_hz4 lowEnergy60_hz5 (by norm_num) (by norm_num)

theorem lowEnergy60_hz7 : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (kappa ((51 / 100))) := by rw [kappa_eq]; exact lowEnergy60_hz6

theorem lowEnergy60_hz8 : B (142471280602484171 / 200000000000000000) (178089100753105217 / 250000000000000000) (kdot ((309369805803 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (485313470429091891 / 1000000000000000000)) (a := (45182950557416091 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (48531347042909189 / 100000000000000000)) (a := (451829505574160891 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy60_hz9 : B (382838706970343729 / 1000000000000000000) (38283870697034373 / 100000000000000000) (((309369805803 / 500000000000) : ℝ)^2) := bsq (bpoint ((309369805803 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy60_hz10 : B (61716129302965627 / 100000000000000000) (617161293029656271 / 1000000000000000000) ((1 : ℝ) - (((309369805803 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy60_hz9 (by norm_num) (by norm_num)

theorem lowEnergy60_hz11 : B (196399034657387043 / 250000000000000000) (785596138629548173 / 1000000000000000000) (√((1 : ℝ) - (((309369805803 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy60_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy60_hz12 : B (62515754368399229 / 250000000000000000) (125031508736798459 / 500000000000000000) ((√((1 : ℝ) - (((309369805803 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy60_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy60_hz13 : B (55095390515619061 / 125000000000000000) (440763124124952497 / 1000000000000000000) (((309369805803 / 500000000000) : ℝ) * (kdot ((309369805803 / 500000000000)))) := bmul (bpoint ((309369805803 / 500000000000) : ℝ)) lowEnergy60_hz8 (by norm_num) (by norm_num)

theorem lowEnergy60_hz14 : B (172706535399637351 / 250000000000000000) (138165228319709883 / 200000000000000000) (((√((1 : ℝ) - (((309369805803 / 500000000000) : ℝ)^2))) / Real.pi) + (((309369805803 / 500000000000) : ℝ) * (kdot ((309369805803 / 500000000000))))) := badd lowEnergy60_hz12 lowEnergy60_hz13 (by norm_num) (by norm_num)

theorem lowEnergy60_hz15 : B (172706535399637351 / 250000000000000000) (138165228319709883 / 200000000000000000) (kappa ((309369805803 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy60_hz14

theorem lowEnergy60 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (51 / 100)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (173416455359 / 250000000000) := by
  have hk1 : kappa q ≤ (615682866593 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((51 / 100) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy60_hz7.2.trans (by norm_num))
  have hk2 : kappa ((309369805803 / 500000000000) : ℝ) ≤ (690826141599 / 1000000000000) := lowEnergy60_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((98131597437 / 125000000000) : ℝ)) (R := ((7859188049 / 10000000000) : ℝ)) (Q2 := ((309369805803 / 500000000000) : ℝ)) (T := ((415939660797 / 500000000000) : ℝ))
    (B := ((173416455359 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy61_hz0 : B (670169615176882537 / 1000000000000000000) (670169615176910981 / 1000000000000000000) (kdot ((1019 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (285018435274817733 / 500000000000000000)) (a := (518096356945500127 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (114007374109927093 / 200000000000000000)) (a := (518096356945455449 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy61_hz1 : B (1038361 / 4000000) (1038361 / 4000000) (((1019 / 2000) : ℝ)^2) := bsq (bpoint ((1019 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy61_hz2 : B (2961639 / 4000000) (2961639 / 4000000) ((1 : ℝ) - (((1019 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy61_hz1 (by norm_num) (by norm_num)

theorem lowEnergy61_hz3 : B (172094131218934947 / 200000000000000000) (53779416005917171 / 62500000000000000) (√((1 : ℝ) - (((1019 / 2000) : ℝ)^2))) := bsqrt lowEnergy61_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy61_hz4 : B (273896316605987599 / 1000000000000000000) (273896316605987601 / 1000000000000000000) ((√((1 : ℝ) - (((1019 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy61_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy61_hz5 : B (85362854733155413 / 250000000000000000) (68290283786527229 / 200000000000000000) (((1019 / 2000) : ℝ) * (kdot ((1019 / 2000)))) := bmul (bpoint ((1019 / 2000) : ℝ)) lowEnergy61_hz0 (by norm_num) (by norm_num)

theorem lowEnergy61_hz6 : B (615347735538609251 / 1000000000000000000) (307673867769311873 / 500000000000000000) (((√((1 : ℝ) - (((1019 / 2000) : ℝ)^2))) / Real.pi) + (((1019 / 2000) : ℝ) * (kdot ((1019 / 2000))))) := badd lowEnergy61_hz4 lowEnergy61_hz5 (by norm_num) (by norm_num)

theorem lowEnergy61_hz7 : B (615347735538609251 / 1000000000000000000) (307673867769311873 / 500000000000000000) (kappa ((1019 / 2000))) := by rw [kappa_eq]; exact lowEnergy61_hz6

theorem lowEnergy61_hz8 : B (712220251090323387 / 1000000000000000000) (712220251090323401 / 1000000000000000000) (kdot ((154600882233 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (60697217087824761 / 125000000000000000)) (a := (226021686256638839 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (485577736702598087 / 1000000000000000000)) (a := (226021686256638829 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy61_hz9 : B (382422924595550961 / 1000000000000000000) (191211462297775481 / 500000000000000000) (((154600882233 / 250000000000) : ℝ)^2) := bsq (bpoint ((154600882233 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy61_hz10 : B (308788537702224519 / 500000000000000000) (617577075404449039 / 1000000000000000000) ((1 : ℝ) - (((154600882233 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy61_hz9 (by norm_num) (by norm_num)

theorem lowEnergy61_hz11 : B (785860722650298281 / 1000000000000000000) (392930361325149141 / 500000000000000000) (√((1 : ℝ) - (((154600882233 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy61_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy61_hz12 : B (250147237183127933 / 1000000000000000000) (125073618591563967 / 500000000000000000) ((√((1 : ℝ) - (((154600882233 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy61_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy61_hz13 : B (440439516651091103 / 1000000000000000000) (55054939581386389 / 125000000000000000) (((154600882233 / 250000000000) : ℝ) * (kdot ((154600882233 / 250000000000)))) := bmul (bpoint ((154600882233 / 250000000000) : ℝ)) lowEnergy61_hz8 (by norm_num) (by norm_num)

theorem lowEnergy61_hz14 : B (172646688458554759 / 250000000000000000) (345293376917109523 / 500000000000000000) (((√((1 : ℝ) - (((154600882233 / 250000000000) : ℝ)^2))) / Real.pi) + (((154600882233 / 250000000000) : ℝ) * (kdot ((154600882233 / 250000000000))))) := badd lowEnergy61_hz12 lowEnergy61_hz13 (by norm_num) (by norm_num)

theorem lowEnergy61_hz15 : B (172646688458554759 / 250000000000000000) (345293376917109523 / 500000000000000000) (kappa ((154600882233 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy61_hz14

theorem lowEnergy61 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1019 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (346712867201 / 500000000000) := by
  have hk1 : kappa q ≤ (615347735539 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1019 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy61_hz7.2.trans (by norm_num))
  have hk2 : kappa ((154600882233 / 250000000000) : ℝ) ≤ (138117350767 / 200000000000) := lowEnergy61_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((49052456597 / 62500000000) : ℝ)) (R := ((196426332739 / 250000000000) : ℝ)) (Q2 := ((154600882233 / 250000000000) : ℝ)) (T := ((33269407043 / 40000000000) : ℝ))
    (B := ((346712867201 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy62_hz0 : B (669984684313279763 / 1000000000000000000) (669984684313309163 / 1000000000000000000) (kdot ((509 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (142605453755069263 / 250000000000000000)) (a := (259193422833379187 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (570421815020277051 / 1000000000000000000)) (a := (518386845666712193 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy62_hz1 : B (259081 / 1000000) (259081 / 1000000) (((509 / 1000) : ℝ)^2) := bsq (bpoint ((509 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy62_hz2 : B (740919 / 1000000) (740919 / 1000000) ((1 : ℝ) - (((509 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy62_hz1 (by norm_num) (by norm_num)

theorem lowEnergy62_hz3 : B (860766518865598071 / 1000000000000000000) (107595814858199759 / 125000000000000000) (√((1 : ℝ) - (((509 / 1000) : ℝ)^2))) := bsqrt lowEnergy62_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy62_hz4 : B (273990492650926227 / 1000000000000000000) (273990492650926229 / 1000000000000000000) ((√((1 : ℝ) - (((509 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy62_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy62_hz5 : B (341022204315459399 / 1000000000000000000) (85255551078868591 / 250000000000000000) (((509 / 1000) : ℝ) * (kdot ((509 / 1000)))) := bmul (bpoint ((509 / 1000) : ℝ)) lowEnergy62_hz0 (by norm_num) (by norm_num)

theorem lowEnergy62_hz6 : B (307506348483192813 / 500000000000000000) (615012696966400593 / 1000000000000000000) (((√((1 : ℝ) - (((509 / 1000) : ℝ)^2))) / Real.pi) + (((509 / 1000) : ℝ) * (kdot ((509 / 1000))))) := badd lowEnergy62_hz4 lowEnergy62_hz5 (by norm_num) (by norm_num)

theorem lowEnergy62_hz7 : B (307506348483192813 / 500000000000000000) (615012696966400593 / 1000000000000000000) (kappa ((509 / 1000))) := by rw [kappa_eq]; exact lowEnergy62_hz6

theorem lowEnergy62_hz8 : B (44505261405859953 / 62500000000000000) (712084182493759261 / 1000000000000000000) (kdot ((123613507781 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (485841896086964003 / 1000000000000000000)) (a := (113064277141238191 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (242920948043482001 / 500000000000000000)) (a := (90451421712990549 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy62_hz9 : B (47750935331010461 / 125000000000000000) (382007482648083689 / 1000000000000000000) (((123613507781 / 200000000000) : ℝ)^2) := bsq (bpoint ((123613507781 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy62_hz10 : B (617992517351916311 / 1000000000000000000) (77249064668989539 / 125000000000000000) ((1 : ℝ) - (((123613507781 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy62_hz9 (by norm_num) (by norm_num)

theorem lowEnergy62_hz11 : B (786125001098372593 / 1000000000000000000) (393062500549186297 / 500000000000000000) (√((1 : ℝ) - (((123613507781 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy62_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy62_hz12 : B (3909864994153989 / 15625000000000000) (125115679812927649 / 500000000000000000) ((√((1 : ℝ) - (((123613507781 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy62_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy62_hz13 : B (440116118167096663 / 1000000000000000000) (13753628692721771 / 31250000000000000) (((123613507781 / 200000000000) : ℝ) * (kdot ((123613507781 / 200000000000)))) := bmul (bpoint ((123613507781 / 200000000000) : ℝ)) lowEnergy62_hz8 (by norm_num) (by norm_num)

theorem lowEnergy62_hz14 : B (690347477792951959 / 1000000000000000000) (69034747779295197 / 100000000000000000) (((√((1 : ℝ) - (((123613507781 / 200000000000) : ℝ)^2))) / Real.pi) + (((123613507781 / 200000000000) : ℝ) * (kdot ((123613507781 / 200000000000))))) := badd lowEnergy62_hz12 lowEnergy62_hz13 (by norm_num) (by norm_num)

theorem lowEnergy62_hz15 : B (690347477792951959 / 1000000000000000000) (69034747779295197 / 100000000000000000) (kappa ((123613507781 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy62_hz14

theorem lowEnergy62 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (509 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (693185759367 / 1000000000000) := by
  have hk1 : kappa q ≤ (615012696967 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((509 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy62_hz7.2.trans (by norm_num))
  have hk2 : kappa ((123613507781 / 200000000000) : ℝ) ≤ (690347477793 / 1000000000000) := lowEnergy62_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((784625832463 / 1000000000000) : ℝ)) (R := ((785491857867 / 1000000000000) : ℝ)) (Q2 := ((123613507781 / 200000000000) : ℝ)) (T := ((41579553643 / 50000000000) : ℝ))
    (B := ((693185759367 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy63_hz0 : B (669799816961122069 / 1000000000000000000) (334899908480576229 / 500000000000000000) (kdot ((1017 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (285403377407483173 / 500000000000000000)) (a := (518677234624471977 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (114161350962993269 / 200000000000000000)) (a := (129669308656106061 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy63_hz1 : B (1034289 / 4000000) (1034289 / 4000000) (((1017 / 2000) : ℝ)^2) := bsq (bpoint ((1017 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy63_hz2 : B (2965711 / 4000000) (2965711 / 4000000) ((1 : ℝ) - (((1017 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy63_hz1 (by norm_num) (by norm_num)

theorem lowEnergy63_hz3 : B (215265497409594183 / 250000000000000000) (861061989638376733 / 1000000000000000000) (√((1 : ℝ) - (((1017 / 2000) : ℝ)^2))) := bsqrt lowEnergy63_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy63_hz4 : B (6852113597974501 / 25000000000000000) (274084543918980041 / 1000000000000000000) ((√((1 : ℝ) - (((1017 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy63_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy63_hz5 : B (85148301731182643 / 250000000000000000) (13623728276989841 / 40000000000000000) (((1017 / 2000) : ℝ) * (kdot ((1017 / 2000)))) := bmul (bpoint ((1017 / 2000) : ℝ)) lowEnergy63_hz0 (by norm_num) (by norm_num)

theorem lowEnergy63_hz6 : B (153669437710927653 / 250000000000000000) (307338875421863033 / 500000000000000000) (((√((1 : ℝ) - (((1017 / 2000) : ℝ)^2))) / Real.pi) + (((1017 / 2000) : ℝ) * (kdot ((1017 / 2000))))) := badd lowEnergy63_hz4 lowEnergy63_hz5 (by norm_num) (by norm_num)

theorem lowEnergy63_hz7 : B (153669437710927653 / 250000000000000000) (307338875421863033 / 500000000000000000) (kappa ((1017 / 2000))) := by rw [kappa_eq]; exact lowEnergy63_hz6

theorem lowEnergy63_hz8 : B (88993524637310851 / 125000000000000000) (711948197098486821 / 1000000000000000000) (kdot ((617731641487 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (486105948763919487 / 1000000000000000000)) (a := (226235356962172233 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (243052974381959743 / 500000000000000000)) (a := (226235356962172223 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy63_hz9 : B (381592380894223499 / 1000000000000000000) (763184761788447 / 2000000000000000) (((617731641487 / 1000000000000) : ℝ)^2) := bsq (bpoint ((617731641487 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy63_hz10 : B (1236815238211553 / 2000000000000000) (618407619105776501 / 1000000000000000000) ((1 : ℝ) - (((617731641487 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy63_hz9 (by norm_num) (by norm_num)

theorem lowEnergy63_hz11 : B (786388974430450989 / 1000000000000000000) (786388974430450991 / 1000000000000000000) (√((1 : ℝ) - (((617731641487 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy63_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy63_hz12 : B (125157692473572363 / 500000000000000000) (31289423118393091 / 125000000000000000) ((√((1 : ℝ) - (((617731641487 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy63_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy63_hz13 : B (219896464223679233 / 500000000000000000) (17591717137894339 / 40000000000000000) (((617731641487 / 1000000000000) : ℝ) * (kdot ((617731641487 / 1000000000000)))) := bmul (bpoint ((617731641487 / 1000000000000) : ℝ)) lowEnergy63_hz8 (by norm_num) (by norm_num)

theorem lowEnergy63_hz14 : B (86263539174312899 / 125000000000000000) (690108313394503203 / 1000000000000000000) (((√((1 : ℝ) - (((617731641487 / 1000000000000) : ℝ)^2))) / Real.pi) + (((617731641487 / 1000000000000) : ℝ) * (kdot ((617731641487 / 1000000000000))))) := badd lowEnergy63_hz12 lowEnergy63_hz13 (by norm_num) (by norm_num)

theorem lowEnergy63_hz15 : B (86263539174312899 / 125000000000000000) (690108313394503203 / 1000000000000000000) (kappa ((617731641487 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy63_hz14

theorem lowEnergy63 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1017 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (346472948127 / 500000000000) := by
  have hk1 : kappa q ≤ (153669437711 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1017 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy63_hz7.2.trans (by norm_num))
  have hk2 : kappa ((617731641487 / 1000000000000) : ℝ) ≤ (138021662679 / 200000000000) := lowEnergy63_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((784412360207 / 1000000000000) : ℝ)) (R := ((785278385611 / 1000000000000) : ℝ)) (Q2 := ((617731641487 / 1000000000000) : ℝ)) (T := ((33257880477 / 40000000000) : ℝ))
    (B := ((346472948127 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy64_hz0 : B (83701876624090791 / 125000000000000000) (83701876624094717 / 125000000000000000) (kdot ((127 / 250))) := by
    constructor
    · apply bkdot_lower (q := (142797922549139813 / 250000000000000000)) (a := (64870940502400641 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (571191690196559251 / 1000000000000000000)) (a := (518967524019155793 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy64_hz1 : B (16129 / 62500) (16129 / 62500) (((127 / 250) : ℝ)^2) := bsq (bpoint ((127 / 250) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy64_hz2 : B (46371 / 62500) (46371 / 62500) ((1 : ℝ) - (((127 / 250) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy64_hz1 (by norm_num) (by norm_num)

theorem lowEnergy64_hz3 : B (861357068816411351 / 1000000000000000000) (107669633602051419 / 125000000000000000) (√((1 : ℝ) - (((127 / 250) : ℝ)^2))) := bsqrt lowEnergy64_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy64_hz4 : B (137089235269277723 / 500000000000000000) (274178470538555447 / 1000000000000000000) ((√((1 : ℝ) - (((127 / 250) : ℝ)^2))) / Real.pi) := bdiv lowEnergy64_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy64_hz5 : B (170082213300152487 / 500000000000000000) (34016442660032093 / 100000000000000000) (((127 / 250) : ℝ) * (kdot ((127 / 250)))) := bmul (bpoint ((127 / 250) : ℝ)) lowEnergy64_hz0 (by norm_num) (by norm_num)

theorem lowEnergy64_hz6 : B (30717144856943021 / 50000000000000000) (614342897138876377 / 1000000000000000000) (((√((1 : ℝ) - (((127 / 250) : ℝ)^2))) / Real.pi) + (((127 / 250) : ℝ) * (kdot ((127 / 250))))) := badd lowEnergy64_hz4 lowEnergy64_hz5 (by norm_num) (by norm_num)

theorem lowEnergy64_hz7 : B (30717144856943021 / 50000000000000000) (614342897138876377 / 1000000000000000000) (kappa ((127 / 250))) := by rw [kappa_eq]; exact lowEnergy64_hz6

theorem lowEnergy64_hz8 : B (711812294784207067 / 1000000000000000000) (711812294784207081 / 1000000000000000000) (kdot ((617395836649 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (243184947453837067 / 500000000000000000)) (a := (56585523597552251 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (486369894907674133 / 1000000000000000000)) (a := (113171047195104497 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy64_hz9 : B (381177619111518691 / 1000000000000000000) (95294404777879673 / 250000000000000000) (((617395836649 / 1000000000000) : ℝ)^2) := bsq (bpoint ((617395836649 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy64_hz10 : B (154705595222120327 / 250000000000000000) (618822380888481309 / 1000000000000000000) ((1 : ℝ) - (((617395836649 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy64_hz9 (by norm_num) (by norm_num)

theorem lowEnergy64_hz11 : B (24582895096721369 / 31250000000000000) (78665264309508381 / 100000000000000000) (√((1 : ℝ) - (((617395836649 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy64_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy64_hz12 : B (250399313289774231 / 1000000000000000000) (250399313289774233 / 1000000000000000000) ((√((1 : ℝ) - (((617395836649 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy64_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy64_hz13 : B (439469947275340141 / 1000000000000000000) (8789398945506803 / 20000000000000000) (((617395836649 / 1000000000000) : ℝ) * (kdot ((617395836649 / 1000000000000)))) := bmul (bpoint ((617395836649 / 1000000000000) : ℝ)) lowEnergy64_hz8 (by norm_num) (by norm_num)

theorem lowEnergy64_hz14 : B (172467315141278593 / 250000000000000000) (689869260565114383 / 1000000000000000000) (((√((1 : ℝ) - (((617395836649 / 1000000000000) : ℝ)^2))) / Real.pi) + (((617395836649 / 1000000000000) : ℝ) * (kdot ((617395836649 / 1000000000000))))) := badd lowEnergy64_hz12 lowEnergy64_hz13 (by norm_num) (by norm_num)

theorem lowEnergy64_hz15 : B (172467315141278593 / 250000000000000000) (689869260565114383 / 1000000000000000000) (kappa ((617395836649 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy64_hz14

theorem lowEnergy64 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127 / 250)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (346353072493 / 500000000000) := by
  have hk1 : kappa q ≤ (614342897139 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((127 / 250) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy64_hz7.2.trans (by norm_num))
  have hk2 : kappa ((617395836649 / 1000000000000) : ℝ) ≤ (344934630283 / 500000000000) := lowEnergy64_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((156839777753 / 200000000000) : ℝ)) (R := ((785064914169 / 1000000000000) : ℝ)) (Q2 := ((617395836649 / 1000000000000) : ℝ)) (T := ((415651496623 / 500000000000) : ℝ))
    (B := ((346353072493 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy65_hz0 : B (334715136140356781 / 500000000000000000) (83678784035093253 / 125000000000000000) (kdot ((203 / 400))) := by
    constructor
    · apply bkdot_lower (q := (571576621427539433 / 1000000000000000000)) (a := (103851542810208851 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (71447077678442429 / 125000000000000000)) (a := (32453607128187079 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy65_hz1 : B (41209 / 160000) (41209 / 160000) (((203 / 400) : ℝ)^2) := bsq (bpoint ((203 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy65_hz2 : B (118791 / 160000) (118791 / 160000) ((1 : ℝ) - (((203 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy65_hz1 (by norm_num) (by norm_num)

theorem lowEnergy65_hz3 : B (430825878401007847 / 500000000000000000) (172330351360403139 / 200000000000000000) (√((1 : ℝ) - (((203 / 400) : ℝ)^2))) := bsqrt lowEnergy65_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy65_hz4 : B (54854454527542579 / 200000000000000000) (535688032495533 / 1953125000000000) ((√((1 : ℝ) - (((203 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy65_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy65_hz5 : B (84933965795615533 / 250000000000000000) (21233491448904913 / 62500000000000000) (((203 / 400) : ℝ) * (kdot ((203 / 400)))) := bmul (bpoint ((203 / 400) : ℝ)) lowEnergy65_hz0 (by norm_num) (by norm_num)

theorem lowEnergy65_hz6 : B (614008135820175027 / 1000000000000000000) (38375508488761969 / 62500000000000000) (((√((1 : ℝ) - (((203 / 400) : ℝ)^2))) / Real.pi) + (((203 / 400) : ℝ) * (kdot ((203 / 400))))) := badd lowEnergy65_hz4 lowEnergy65_hz5 (by norm_num) (by norm_num)

theorem lowEnergy65_hz7 : B (614008135820175027 / 1000000000000000000) (38375508488761969 / 62500000000000000) (kappa ((203 / 400))) := by rw [kappa_eq]; exact lowEnergy65_hz6

theorem lowEnergy65_hz8 : B (711676475429702461 / 1000000000000000000) (28467059017188099 / 40000000000000000) (kdot ((617060124359 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (97326746938870747 / 200000000000000000)) (a := (452897533323581497 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (243316867347176867 / 500000000000000000)) (a := (113224383330895369 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy65_hz9 : B (76152639414788909 / 200000000000000000) (190381598536972273 / 500000000000000000) (((617060124359 / 1000000000000) : ℝ)^2) := bsq (bpoint ((617060124359 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy65_hz10 : B (309618401463027727 / 500000000000000000) (123847360585211091 / 200000000000000000) ((1 : ℝ) - (((617060124359 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy65_hz9 (by norm_num) (by norm_num)

theorem lowEnergy65_hz11 : B (786916007542136261 / 1000000000000000000) (786916007542136263 / 1000000000000000000) (√((1 : ℝ) - (((617060124359 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy65_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy65_hz12 : B (125241572398470177 / 500000000000000000) (62620786199235089 / 250000000000000000) ((√((1 : ℝ) - (((617060124359 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy65_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy65_hz13 : B (3430837300250211 / 7812500000000000) (219573587216013509 / 500000000000000000) (((617060124359 / 1000000000000) : ℝ) * (kdot ((617060124359 / 1000000000000)))) := bmul (bpoint ((617060124359 / 1000000000000) : ℝ)) lowEnergy65_hz8 (by norm_num) (by norm_num)

theorem lowEnergy65_hz14 : B (344815159614483681 / 500000000000000000) (344815159614483687 / 500000000000000000) (((√((1 : ℝ) - (((617060124359 / 1000000000000) : ℝ)^2))) / Real.pi) + (((617060124359 / 1000000000000) : ℝ) * (kdot ((617060124359 / 1000000000000))))) := badd lowEnergy65_hz12 lowEnergy65_hz13 (by norm_num) (by norm_num)

theorem lowEnergy65_hz15 : B (344815159614483681 / 500000000000000000) (344815159614483687 / 500000000000000000) (kappa ((617060124359 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy65_hz14

theorem lowEnergy65 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (203 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (346233252743 / 500000000000) := by
  have hk1 : kappa q ≤ (614008135821 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((203 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy65_hz7.2.trans (by norm_num))
  have hk2 : kappa ((617060124359 / 1000000000000) : ℝ) ≤ (689630319229 / 1000000000000) := lowEnergy65_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((391992709059 / 500000000000) : ℝ)) (R := ((392425721761 / 500000000000) : ℝ)) (Q2 := ((617060124359 / 1000000000000) : ℝ)) (T := ((415579508399 / 500000000000) : ℝ))
    (B := ((346233252743 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy66_hz0 : B (83655699337250979 / 125000000000000000) (83655699337255173 / 125000000000000000) (kdot ((507 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (114392309754004029 / 200000000000000000)) (a := (20781912196783991 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (35747596798126259 / 62500000000000000)) (a := (259773902459773537 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy66_hz1 : B (257049 / 1000000) (257049 / 1000000) (((507 / 1000) : ℝ)^2) := bsq (bpoint ((507 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy66_hz2 : B (742951 / 1000000) (742951 / 1000000) ((1 : ℝ) - (((507 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy66_hz1 (by norm_num) (by norm_num)

theorem lowEnergy66_hz3 : B (430973026998210179 / 500000000000000000) (861946053996420359 / 1000000000000000000) (√((1 : ℝ) - (((507 / 1000) : ℝ)^2))) := bsqrt lowEnergy66_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy66_hz4 : B (68591487586042013 / 250000000000000000) (274365950344168053 / 1000000000000000000) ((√((1 : ℝ) - (((507 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy66_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy66_hz5 : B (33930751651188997 / 100000000000000000) (169653758255953491 / 500000000000000000) (((507 / 1000) : ℝ) * (kdot ((507 / 1000)))) := bmul (bpoint ((507 / 1000) : ℝ)) lowEnergy66_hz0 (by norm_num) (by norm_num)

theorem lowEnergy66_hz6 : B (306836733428029011 / 500000000000000000) (122734693371215007 / 200000000000000000) (((√((1 : ℝ) - (((507 / 1000) : ℝ)^2))) / Real.pi) + (((507 / 1000) : ℝ) * (kdot ((507 / 1000))))) := badd lowEnergy66_hz4 lowEnergy66_hz5 (by norm_num) (by norm_num)

theorem lowEnergy66_hz7 : B (306836733428029011 / 500000000000000000) (122734693371215007 / 200000000000000000) (kappa ((507 / 1000))) := by rw [kappa_eq]; exact lowEnergy66_hz6

theorem lowEnergy66_hz8 : B (35577036945682329 / 50000000000000000) (355770369456823297 / 500000000000000000) (kdot ((77090563073 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (97379493660085771 / 200000000000000000)) (a := (113277686936103503 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (243448734150214427 / 500000000000000000)) (a := (453110747744413991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy66_hz9 : B (380349114554380237 / 1000000000000000000) (190174557277190119 / 500000000000000000) (((77090563073 / 125000000000) : ℝ)^2) := bsq (bpoint ((77090563073 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy66_hz10 : B (309825442722809881 / 500000000000000000) (619650885445619763 / 1000000000000000000) ((1 : ℝ) - (((77090563073 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy66_hz9 (by norm_num) (by norm_num)

theorem lowEnergy66_hz11 : B (196794767055303671 / 250000000000000000) (157435813644242937 / 200000000000000000) (√((1 : ℝ) - (((77090563073 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy66_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy66_hz12 : B (125283439805878619 / 500000000000000000) (250566879611757239 / 1000000000000000000) ((√((1 : ℝ) - (((77090563073 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy66_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy66_hz13 : B (438824609697851977 / 1000000000000000000) (438824609697851987 / 1000000000000000000) (((77090563073 / 125000000000) : ℝ) * (kdot ((77090563073 / 125000000000)))) := bmul (bpoint ((77090563073 / 125000000000) : ℝ)) lowEnergy66_hz8 (by norm_num) (by norm_num)

theorem lowEnergy66_hz14 : B (137878297861921843 / 200000000000000000) (344695744654804613 / 500000000000000000) (((√((1 : ℝ) - (((77090563073 / 125000000000) : ℝ)^2))) / Real.pi) + (((77090563073 / 125000000000) : ℝ) * (kdot ((77090563073 / 125000000000))))) := badd lowEnergy66_hz12 lowEnergy66_hz13 (by norm_num) (by norm_num)

theorem lowEnergy66_hz15 : B (137878297861921843 / 200000000000000000) (344695744654804613 / 500000000000000000) (kappa ((77090563073 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy66_hz14

theorem lowEnergy66 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (507 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (8652837221 / 12500000000) := by
  have hk1 : kappa q ≤ (613673466857 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((507 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy66_hz7.2.trans (by norm_num))
  have hk2 : kappa ((77090563073 / 125000000000) : ℝ) ≤ (68939148931 / 100000000000) := lowEnergy66_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((391885974123 / 500000000000) : ℝ)) (R := ((15692759473 / 20000000000) : ℝ)) (Q2 := ((77090563073 / 125000000000) : ℝ)) (T := ((831015082559 / 1000000000000) : ℝ))
    (B := ((8652837221 / 12500000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy67_hz0 : B (669060980117835133 / 1000000000000000000) (41816311257366863 / 62500000000000000) (kdot ((1013 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (71543309060718257 / 125000000000000000)) (a := (259918898412003917 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (114469294497149211 / 200000000000000000)) (a := (519837796823953367 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy67_hz1 : B (1026169 / 4000000) (1026169 / 4000000) (((1013 / 2000) : ℝ)^2) := bsq (bpoint ((1013 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy67_hz2 : B (2973831 / 4000000) (2973831 / 4000000) ((1 : ℝ) - (((1013 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy67_hz1 (by norm_num) (by norm_num)

theorem lowEnergy67_hz3 : B (862239960799776433 / 1000000000000000000) (431119980399888217 / 500000000000000000) (√((1 : ℝ) - (((1013 / 2000) : ℝ)^2))) := bsqrt lowEnergy67_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy67_hz4 : B (137229751892646483 / 500000000000000000) (274459503785292967 / 1000000000000000000) ((√((1 : ℝ) - (((1013 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy67_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy67_hz5 : B (169439693214841747 / 500000000000000000) (169439693214850529 / 500000000000000000) (((1013 / 2000) : ℝ) * (kdot ((1013 / 2000)))) := bmul (bpoint ((1013 / 2000) : ℝ)) lowEnergy67_hz0 (by norm_num) (by norm_num)

theorem lowEnergy67_hz6 : B (30666944510748823 / 50000000000000000) (24533555608599761 / 40000000000000000) (((√((1 : ℝ) - (((1013 / 2000) : ℝ)^2))) / Real.pi) + (((1013 / 2000) : ℝ) * (kdot ((1013 / 2000))))) := badd lowEnergy67_hz4 lowEnergy67_hz5 (by norm_num) (by norm_num)

theorem lowEnergy67_hz7 : B (30666944510748823 / 50000000000000000) (24533555608599761 / 40000000000000000) (kappa ((1013 / 2000))) := by rw [kappa_eq]; exact lowEnergy67_hz6

theorem lowEnergy67_hz8 : B (2223140890989453 / 3125000000000000) (28456203404664999 / 40000000000000000) (kdot ((123277795459 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (487161095898787623 / 1000000000000000000)) (a := (453323832230491353 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (243580547949393811 / 500000000000000000)) (a := (453323832230491331 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy67_hz9 : B (15197414853231041 / 40000000000000000) (189967685665388013 / 500000000000000000) (((123277795459 / 200000000000) : ℝ)^2) := bsq (bpoint ((123277795459 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy67_hz10 : B (310032314334611987 / 500000000000000000) (24802585146768959 / 40000000000000000) ((1 : ℝ) - (((123277795459 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy67_hz9 (by norm_num) (by norm_num)

theorem lowEnergy67_hz11 : B (393720912788876371 / 500000000000000000) (98430228197219093 / 125000000000000000) (√((1 : ℝ) - (((123277795459 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy67_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy67_hz12 : B (250650517876010821 / 1000000000000000000) (125325258938005411 / 500000000000000000) ((√((1 : ℝ) - (((123277795459 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy67_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy67_hz13 : B (109625563214374721 / 250000000000000000) (87700450571499779 / 200000000000000000) (((123277795459 / 200000000000) : ℝ) * (kdot ((123277795459 / 200000000000)))) := bmul (bpoint ((123277795459 / 200000000000) : ℝ)) lowEnergy67_hz8 (by norm_num) (by norm_num)

theorem lowEnergy67_hz14 : B (137830554146701941 / 200000000000000000) (689152770733509717 / 1000000000000000000) (((√((1 : ℝ) - (((123277795459 / 200000000000) : ℝ)^2))) / Real.pi) + (((123277795459 / 200000000000) : ℝ) * (kdot ((123277795459 / 200000000000))))) := badd lowEnergy67_hz12 lowEnergy67_hz13 (by norm_num) (by norm_num)

theorem lowEnergy67_hz15 : B (137830554146701941 / 200000000000000000) (689152770733509717 / 1000000000000000000) (kappa ((123277795459 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy67_hz14

theorem lowEnergy67 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1013 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (691987561493 / 1000000000000) := by
  have hk1 : kappa q ≤ (122667778043 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1013 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy67_hz7.2.trans (by norm_num))
  have hk2 : kappa ((123277795459 / 200000000000) : ℝ) ≤ (344576385367 / 500000000000) := lowEnergy67_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((78355847913 / 100000000000) : ℝ)) (R := ((392212252267 / 500000000000) : ℝ)) (Q2 := ((123277795459 / 200000000000) : ℝ)) (T := ((415435595253 / 500000000000) : ℝ))
    (B := ((691987561493 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy68_hz0 : B (334438214206861139 / 500000000000000000) (133775285682751623 / 200000000000000000) (kdot ((253 / 500))) := by
    constructor
    · apply bkdot_lower (q := (28636569641804753 / 50000000000000000)) (a := (104025537992586409 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (572731392836095059 / 1000000000000000000)) (a := (520127689962875753 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy68_hz1 : B (64009 / 250000) (64009 / 250000) (((253 / 500) : ℝ)^2) := bsq (bpoint ((253 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy68_hz2 : B (185991 / 250000) (185991 / 250000) ((1 : ℝ) - (((253 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy68_hz1 (by norm_num) (by norm_num)

theorem lowEnergy68_hz3 : B (21563336940278979 / 25000000000000000) (862533477611159161 / 1000000000000000000) (√((1 : ℝ) - (((253 / 500) : ℝ)^2))) := bsqrt lowEnergy68_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy68_hz4 : B (274552933088117231 / 1000000000000000000) (17159558318007327 / 62500000000000000) ((√((1 : ℝ) - (((253 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy68_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy68_hz5 : B (21153217048583967 / 62500000000000000) (338451472777361607 / 1000000000000000000) (((253 / 500) : ℝ) * (kdot ((253 / 500)))) := bmul (bpoint ((253 / 500) : ℝ)) lowEnergy68_hz0 (by norm_num) (by norm_num)

theorem lowEnergy68_hz6 : B (613004405865460703 / 1000000000000000000) (613004405865478839 / 1000000000000000000) (((√((1 : ℝ) - (((253 / 500) : ℝ)^2))) / Real.pi) + (((253 / 500) : ℝ) * (kdot ((253 / 500))))) := badd lowEnergy68_hz4 lowEnergy68_hz5 (by norm_num) (by norm_num)

theorem lowEnergy68_hz7 : B (613004405865460703 / 1000000000000000000) (613004405865478839 / 1000000000000000000) (kappa ((253 / 500))) := by rw [kappa_eq]; exact lowEnergy68_hz6

theorem lowEnergy68_hz8 : B (88908689239686809 / 125000000000000000) (88908689239686811 / 125000000000000000) (kdot ((308026771229 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (487424617665809359 / 1000000000000000000)) (a := (226768393486052351 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (243712308832904679 / 500000000000000000)) (a := (453536786972104679 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy68_hz9 : B (47440245896881351 / 125000000000000000) (379521967175050809 / 1000000000000000000) (((308026771229 / 500000000000) : ℝ)^2) := bsq (bpoint ((308026771229 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy68_hz10 : B (620478032824949191 / 1000000000000000000) (77559754103118649 / 125000000000000000) ((1 : ℝ) - (((308026771229 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy68_hz9 (by norm_num) (by norm_num)

theorem lowEnergy68_hz11 : B (39385214003003373 / 50000000000000000) (787704280060067461 / 1000000000000000000) (√((1 : ℝ) - (((308026771229 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy68_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy68_hz12 : B (62683514933101211 / 250000000000000000) (125367029866202423 / 500000000000000000) ((√((1 : ℝ) - (((308026771229 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy68_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy68_hz13 : B (219090051845626101 / 500000000000000000) (438180103691252213 / 1000000000000000000) (((308026771229 / 500000000000) : ℝ) * (kdot ((308026771229 / 500000000000)))) := bmul (bpoint ((308026771229 / 500000000000) : ℝ)) lowEnergy68_hz8 (by norm_num) (by norm_num)

theorem lowEnergy68_hz14 : B (344457081711828523 / 500000000000000000) (688914163423657059 / 1000000000000000000) (((√((1 : ℝ) - (((308026771229 / 500000000000) : ℝ)^2))) / Real.pi) + (((308026771229 / 500000000000) : ℝ) * (kdot ((308026771229 / 500000000000))))) := badd lowEnergy68_hz12 lowEnergy68_hz13 (by norm_num) (by norm_num)

theorem lowEnergy68_hz15 : B (344457081711828523 / 500000000000000000) (688914163423657059 / 1000000000000000000) (kappa ((308026771229 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy68_hz14

theorem lowEnergy68 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (253 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (691748256849 / 1000000000000) := by
  have hk1 : kappa q ≤ (306502202933 / 500000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((253 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy68_hz7.2.trans (by norm_num))
  have hk2 : kappa ((308026771229 / 500000000000) : ℝ) ≤ (21528567607 / 31250000000) := lowEnergy68_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((3133380043 / 4000000000) : ℝ)) (R := ((392105518077 / 500000000000) : ℝ)) (Q2 := ((308026771229 / 500000000000) : ℝ)) (T := ((415363670307 / 500000000000) : ℝ))
    (B := ((691748256849 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy69_hz0 : B (668691939459495811 / 1000000000000000000) (41793246216220803 / 62500000000000000) (kdot ((1011 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (114623262016416017 / 200000000000000000)) (a := (520417484534565211 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (143279077520520021 / 250000000000000000)) (a := (104083496906901407 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy69_hz1 : B (1022121 / 4000000) (1022121 / 4000000) (((1011 / 2000) : ℝ)^2) := bsq (bpoint ((1011 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy69_hz2 : B (2977879 / 4000000) (2977879 / 4000000) ((1 : ℝ) - (((1011 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy69_hz1 (by norm_num) (by norm_num)

theorem lowEnergy69_hz3 : B (862826604828571567 / 1000000000000000000) (53926662801785723 / 62500000000000000) (√((1 : ℝ) - (((1011 / 2000) : ℝ)^2))) := bsqrt lowEnergy69_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy69_hz4 : B (137323119189664573 / 500000000000000000) (274646238379329147 / 1000000000000000000) ((√((1 : ℝ) - (((1011 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy69_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy69_hz5 : B (84505943849193783 / 250000000000000000) (67604755079358771 / 200000000000000000) (((1011 / 2000) : ℝ) * (kdot ((1011 / 2000)))) := bmul (bpoint ((1011 / 2000) : ℝ)) lowEnergy69_hz0 (by norm_num) (by norm_num)

theorem lowEnergy69_hz6 : B (306335006888052139 / 500000000000000000) (306335006888061501 / 500000000000000000) (((√((1 : ℝ) - (((1011 / 2000) : ℝ)^2))) / Real.pi) + (((1011 / 2000) : ℝ) * (kdot ((1011 / 2000))))) := badd lowEnergy69_hz4 lowEnergy69_hz5 (by norm_num) (by norm_num)

theorem lowEnergy69_hz7 : B (306335006888052139 / 500000000000000000) (306335006888061501 / 500000000000000000) (kappa ((1011 / 2000))) := by rw [kappa_eq]; exact lowEnergy69_hz6

theorem lowEnergy69_hz8 : B (28445361007880853 / 40000000000000000) (35556701259851067 / 50000000000000000) (kdot ((615718200043 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (121922008443573627 / 250000000000000000)) (a := (453749612156546063 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (487688033774294507 / 1000000000000000000)) (a := (11343740303913651 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy69_hz9 : B (75821780372838353 / 200000000000000000) (189554450932095883 / 500000000000000000) (((615718200043 / 1000000000000) : ℝ)^2) := bsq (bpoint ((615718200043 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy69_hz10 : B (310445549067904117 / 500000000000000000) (124178219627161647 / 200000000000000000) ((1 : ℝ) - (((615718200043 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy69_hz9 (by norm_num) (by norm_num)

theorem lowEnergy69_hz11 : B (49247902007019557 / 62500000000000000) (393983216056156457 / 500000000000000000) (√((1 : ℝ) - (((615718200043 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy69_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy69_hz12 : B (250817505322317941 / 1000000000000000000) (250817505322317943 / 1000000000000000000) ((√((1 : ℝ) - (((615718200043 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy69_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy69_hz13 : B (218929080991821689 / 500000000000000000) (109464540495910847 / 250000000000000000) (((615718200043 / 1000000000000) : ℝ) * (kdot ((615718200043 / 1000000000000)))) := bmul (bpoint ((615718200043 / 1000000000000) : ℝ)) lowEnergy69_hz8 (by norm_num) (by norm_num)

theorem lowEnergy69_hz14 : B (688675667305961319 / 1000000000000000000) (688675667305961331 / 1000000000000000000) (((√((1 : ℝ) - (((615718200043 / 1000000000000) : ℝ)^2))) / Real.pi) + (((615718200043 / 1000000000000) : ℝ) * (kdot ((615718200043 / 1000000000000))))) := badd lowEnergy69_hz12 lowEnergy69_hz13 (by norm_num) (by norm_num)

theorem lowEnergy69_hz15 : B (688675667305961319 / 1000000000000000000) (688675667305961331 / 1000000000000000000) (kappa ((615718200043 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy69_hz14

theorem lowEnergy69 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1011 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (691509063673 / 1000000000000) := by
  have hk1 : kappa q ≤ (612670013777 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1011 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy69_hz7.2.trans (by norm_num))
  have hk2 : kappa ((615718200043 / 1000000000000) : ℝ) ≤ (344337833653 / 500000000000) := lowEnergy69_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((783131543087 / 1000000000000) : ℝ)) (R := ((783997568491 / 1000000000000) : ℝ)) (Q2 := ((615718200043 / 1000000000000) : ℝ)) (T := ((830583532861 / 1000000000000) : ℝ))
    (B := ((691509063673 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy70_hz0 : B (83563439141160113 / 125000000000000000) (33425375656465959 / 50000000000000000) (kdot ((101 / 200))) := by
    constructor
    · apply bkdot_lower (q := (573501224484350891 / 1000000000000000000)) (a := (520707180736631049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (57350122448435089 / 100000000000000000)) (a := (520707180736570927 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy70_hz1 : B (10201 / 40000) (10201 / 40000) (((101 / 200) : ℝ)^2) := bsq (bpoint ((101 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy70_hz2 : B (29799 / 40000) (29799 / 40000) ((1 : ℝ) - (((101 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy70_hz1 (by norm_num) (by norm_num)

theorem lowEnergy70_hz3 : B (86311934284894809 / 100000000000000000) (863119342848948091 / 1000000000000000000) (√((1 : ℝ) - (((101 / 200) : ℝ)^2))) := bsqrt lowEnergy70_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy70_hz4 : B (54947883957055373 / 200000000000000000) (137369709892638433 / 500000000000000000) ((√((1 : ℝ) - (((101 / 200) : ℝ)^2))) / Real.pi) := bdiv lowEnergy70_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy70_hz5 : B (42199536766285857 / 125000000000000000) (168798147065153093 / 500000000000000000) (((101 / 200) : ℝ) * (kdot ((101 / 200)))) := bmul (bpoint ((101 / 200) : ℝ)) lowEnergy70_hz0 (by norm_num) (by norm_num)

theorem lowEnergy70_hz6 : B (612335713915563721 / 1000000000000000000) (153083928478895763 / 250000000000000000) (((√((1 : ℝ) - (((101 / 200) : ℝ)^2))) / Real.pi) + (((101 / 200) : ℝ) * (kdot ((101 / 200))))) := badd lowEnergy70_hz4 lowEnergy70_hz5 (by norm_num) (by norm_num)

theorem lowEnergy70_hz7 : B (612335713915563721 / 1000000000000000000) (153083928478895763 / 250000000000000000) (kappa ((101 / 200))) := by rw [kappa_eq]; exact lowEnergy70_hz6

theorem lowEnergy70_hz8 : B (355499309417727183 / 500000000000000000) (355499309417727191 / 500000000000000000) (kdot ((307691475009 / 500000000000))) := by
    constructor
    · apply bkdot_lower (q := (60993918049772547 / 125000000000000000)) (a := (56745288496490013 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (3903610755185443 / 8000000000000000)) (a := (5674528849649001 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy70_hz9 : B (189348087586428143 / 500000000000000000) (378696175172856287 / 1000000000000000000) (((307691475009 / 500000000000) : ℝ)^2) := bsq (bpoint ((307691475009 / 500000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy70_hz10 : B (621303824827143713 / 1000000000000000000) (310651912413571857 / 500000000000000000) ((1 : ℝ) - (((307691475009 / 500000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy70_hz9 (by norm_num) (by norm_num)

theorem lowEnergy70_hz11 : B (788228282179181713 / 1000000000000000000) (157645656435836343 / 200000000000000000) (√((1 : ℝ) - (((307691475009 / 500000000000) : ℝ)^2))) := bsqrt lowEnergy70_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy70_hz12 : B (250900854787300167 / 1000000000000000000) (250900854787300169 / 1000000000000000000) ((√((1 : ℝ) - (((307691475009 / 500000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy70_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy70_hz13 : B (437536427517685447 / 1000000000000000000) (218768213758842729 / 500000000000000000) (((307691475009 / 500000000000) : ℝ) * (kdot ((307691475009 / 500000000000)))) := bmul (bpoint ((307691475009 / 500000000000) : ℝ)) lowEnergy70_hz8 (by norm_num) (by norm_num)

theorem lowEnergy70_hz14 : B (344218641152492807 / 500000000000000000) (688437282304985627 / 1000000000000000000) (((√((1 : ℝ) - (((307691475009 / 500000000000) : ℝ)^2))) / Real.pi) + (((307691475009 / 500000000000) : ℝ) * (kdot ((307691475009 / 500000000000))))) := badd lowEnergy70_hz12 lowEnergy70_hz13 (by norm_num) (by norm_num)

theorem lowEnergy70_hz15 : B (344218641152492807 / 500000000000000000) (688437282304985627 / 1000000000000000000) (kappa ((307691475009 / 500000000000))) := by rw [kappa_eq]; exact lowEnergy70_hz14

theorem lowEnergy70 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (101 / 200)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (691269981889 / 1000000000000) := by
  have hk1 : kappa q ≤ (153083928479 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((101 / 200) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy70_hz7.2.trans (by norm_num))
  have hk2 : kappa ((307691475009 / 500000000000) : ℝ) ≤ (137687456461 / 200000000000) := lowEnergy70_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((782918076121 / 1000000000000) : ℝ)) (R := ((31351364061 / 40000000000) : ℝ)) (Q2 := ((307691475009 / 500000000000) : ℝ)) (T := ((830439767223 / 1000000000000) : ℝ))
    (B := ((691269981889 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy71_hz0 : B (668323149297500273 / 1000000000000000000) (167080787324384957 / 250000000000000000) (kdot ((1009 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (114777227260639173 / 200000000000000000)) (a := (520996778766385897 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (71735767037899483 / 125000000000000000)) (a := (260498389383161883 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy71_hz1 : B (1018081 / 4000000) (1018081 / 4000000) (((1009 / 2000) : ℝ)^2) := bsq (bpoint ((1009 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy71_hz2 : B (2981919 / 4000000) (2981919 / 4000000) ((1 : ℝ) - (((1009 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy71_hz1 (by norm_num) (by norm_num)

theorem lowEnergy71_hz3 : B (431705846034079089 / 500000000000000000) (863411692068158179 / 1000000000000000000) (√((1 : ℝ) - (((1009 / 2000) : ℝ)^2))) := bsqrt lowEnergy71_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy71_hz4 : B (68708119357992387 / 250000000000000000) (274832477431969549 / 1000000000000000000) ((√((1 : ℝ) - (((1009 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy71_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy71_hz5 : B (337169028820588887 / 1000000000000000000) (84292257205152211 / 250000000000000000) (((1009 / 2000) : ℝ) * (kdot ((1009 / 2000)))) := bmul (bpoint ((1009 / 2000) : ℝ)) lowEnergy71_hz0 (by norm_num) (by norm_num)

theorem lowEnergy71_hz6 : B (122400301250511687 / 200000000000000000) (612001506252578393 / 1000000000000000000) (((√((1 : ℝ) - (((1009 / 2000) : ℝ)^2))) / Real.pi) + (((1009 / 2000) : ℝ) * (kdot ((1009 / 2000))))) := badd lowEnergy71_hz4 lowEnergy71_hz5 (by norm_num) (by norm_num)

theorem lowEnergy71_hz7 : B (122400301250511687 / 200000000000000000) (612001506252578393 / 1000000000000000000) (kappa ((1009 / 2000))) := by rw [kappa_eq]; exact lowEnergy71_hz6

theorem lowEnergy71_hz8 : B (355431647356666397 / 500000000000000000) (710863294713332811 / 1000000000000000000) (kdot ((615047792351 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (61026818713871397 / 125000000000000000)) (a := (113543718651468853 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (19528581988438847 / 40000000000000000)) (a := (454174874605875387 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy71_hz9 : B (189141893437919407 / 500000000000000000) (75656757375167763 / 200000000000000000) (((615047792351 / 1000000000000) : ℝ)^2) := bsq (bpoint ((615047792351 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy71_hz10 : B (124343242624832237 / 200000000000000000) (310858106562080593 / 500000000000000000) ((1 : ℝ) - (((615047792351 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy71_hz9 (by norm_num) (by norm_num)

theorem lowEnergy71_hz11 : B (788489830704341541 / 1000000000000000000) (788489830704341543 / 1000000000000000000) (√((1 : ℝ) - (((615047792351 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy71_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy71_hz12 : B (250984108268575331 / 1000000000000000000) (62746027067143833 / 250000000000000000) ((√((1 : ℝ) - (((615047792351 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy71_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy71_hz13 : B (54651862509599203 / 125000000000000000) (87442980015358727 / 200000000000000000) (((615047792351 / 1000000000000) : ℝ) * (kdot ((615047792351 / 1000000000000)))) := bmul (bpoint ((615047792351 / 1000000000000) : ℝ)) lowEnergy71_hz8 (by norm_num) (by norm_num)

theorem lowEnergy71_hz14 : B (137639801669073791 / 200000000000000000) (688199008345368967 / 1000000000000000000) (((√((1 : ℝ) - (((615047792351 / 1000000000000) : ℝ)^2))) / Real.pi) + (((615047792351 / 1000000000000) : ℝ) * (kdot ((615047792351 / 1000000000000))))) := badd lowEnergy71_hz12 lowEnergy71_hz13 (by norm_num) (by norm_num)

theorem lowEnergy71_hz15 : B (137639801669073791 / 200000000000000000) (688199008345368967 / 1000000000000000000) (kappa ((615047792351 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy71_hz14

theorem lowEnergy71 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1009 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (345515505711 / 500000000000) := by
  have hk1 : kappa q ≤ (612001506253 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1009 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy71_hz7.2.trans (by norm_num))
  have hk2 : kappa ((615047792351 / 1000000000000) : ℝ) ≤ (344099504173 / 500000000000) := lowEnergy71_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((782704609833 / 1000000000000) : ℝ)) (R := ((783570635237 / 1000000000000) : ℝ)) (Q2 := ((615047792351 / 1000000000000) : ℝ)) (T := ((207574010919 / 250000000000) : ℝ))
    (B := ((345515505711 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy72_hz0 : B (668138847838873087 / 1000000000000000000) (668138847838913963 / 1000000000000000000) (kdot ((63 / 125))) := by
    constructor
    · apply bkdot_lower (q := (574271045798543801 / 1000000000000000000)) (a := (260643139410310211 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2871355228992719 / 5000000000000000)) (a := (65160784852569527 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy72_hz1 : B (3969 / 15625) (3969 / 15625) (((63 / 125) : ℝ)^2) := bsq (bpoint ((63 / 125) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy72_hz2 : B (11656 / 15625) (11656 / 15625) ((1 : ℝ) - (((63 / 125) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy72_hz1 (by norm_num) (by norm_num)

theorem lowEnergy72_hz3 : B (215925913220252469 / 250000000000000000) (863703652881009877 / 1000000000000000000) (√((1 : ℝ) - (((63 / 125) : ℝ)^2))) := bsqrt lowEnergy72_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy72_hz4 : B (274925411445078499 / 1000000000000000000) (549850822890157 / 2000000000000000) ((√((1 : ℝ) - (((63 / 125) : ℝ)^2))) / Real.pi) := bdiv lowEnergy72_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy72_hz5 : B (67348395862158407 / 200000000000000000) (168370989655406319 / 500000000000000000) (((63 / 125) : ℝ) * (kdot ((63 / 125)))) := bmul (bpoint ((63 / 125) : ℝ)) lowEnergy72_hz0 (by norm_num) (by norm_num)

theorem lowEnergy72_hz6 : B (305833695377935267 / 500000000000000000) (305833695377945569 / 500000000000000000) (((√((1 : ℝ) - (((63 / 125) : ℝ)^2))) / Real.pi) + (((63 / 125) : ℝ) * (kdot ((63 / 125))))) := badd lowEnergy72_hz4 lowEnergy72_hz5 (by norm_num) (by norm_num)

theorem lowEnergy72_hz7 : B (305833695377935267 / 500000000000000000) (305833695377945569 / 500000000000000000) (kappa ((63 / 125))) := by rw [kappa_eq]; exact lowEnergy72_hz6

theorem lowEnergy72_hz8 : B (710728052711888707 / 1000000000000000000) (177682013177972181 / 250000000000000000) (kdot ((614712727011 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (48847764988495441 / 100000000000000000)) (a := (18175492489798887 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (488477649884954409 / 1000000000000000000)) (a := (9087746244899443 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy72_hz9 : B (23616983546831263 / 62500000000000000) (377871736749300209 / 1000000000000000000) (((614712727011 / 1000000000000) : ℝ)^2) := bsq (bpoint ((614712727011 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy72_hz10 : B (622128263250699791 / 1000000000000000000) (38883016453168737 / 62500000000000000) ((1 : ℝ) - (((614712727011 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy72_hz9 (by norm_num) (by norm_num)

theorem lowEnergy72_hz11 : B (31550043125186369 / 40000000000000000) (394375539064829613 / 500000000000000000) (√((1 : ℝ) - (((614712727011 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy72_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy72_hz12 : B (251067265906794011 / 1000000000000000000) (62766816476698503 / 250000000000000000) ((√((1 : ℝ) - (((614712727011 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy72_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy72_hz13 : B (21844678972287143 / 50000000000000000) (54611697430717859 / 125000000000000000) (((614712727011 / 1000000000000) : ℝ) * (kdot ((614712727011 / 1000000000000)))) := bmul (bpoint ((614712727011 / 1000000000000) : ℝ)) lowEnergy72_hz8 (by norm_num) (by norm_num)

theorem lowEnergy72_hz14 : B (687960845352536871 / 1000000000000000000) (171990211338134221 / 250000000000000000) (((√((1 : ℝ) - (((614712727011 / 1000000000000) : ℝ)^2))) / Real.pi) + (((614712727011 / 1000000000000) : ℝ) * (kdot ((614712727011 / 1000000000000))))) := badd lowEnergy72_hz12 lowEnergy72_hz13 (by norm_num) (by norm_num)

theorem lowEnergy72_hz15 : B (687960845352536871 / 1000000000000000000) (171990211338134221 / 250000000000000000) (kappa ((614712727011 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy72_hz14

theorem lowEnergy72 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (63 / 125)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (345396076099 / 500000000000) := by
  have hk1 : kappa q ≤ (152916847689 / 250000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((63 / 125) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy72_hz7.2.trans (by norm_num))
  have hk2 : kappa ((614712727011 / 1000000000000) : ℝ) ≤ (687960845353 / 1000000000000) := lowEnergy72_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((782491144203 / 1000000000000) : ℝ)) (R := ((783357169607 / 1000000000000) : ℝ)) (Q2 := ((614712727011 / 1000000000000) : ℝ)) (T := ((415076181099 / 500000000000) : ℝ))
    (B := ((345396076099 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy73_hz0 : B (133590921725682779 / 200000000000000000) (83494326078557017 / 125000000000000000) (kdot ((1007 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (574655953229965683 / 1000000000000000000)) (a := (2037405004279927 / 3906250000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (287327976614982841 / 500000000000000000)) (a := (521575681095594963 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy73_hz1 : B (1014049 / 4000000) (1014049 / 4000000) (((1007 / 2000) : ℝ)^2) := bsq (bpoint ((1007 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy73_hz2 : B (2985951 / 4000000) (2985951 / 4000000) ((1 : ℝ) - (((1007 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy73_hz1 (by norm_num) (by norm_num)

theorem lowEnergy73_hz3 : B (863995225681253403 / 1000000000000000000) (215998806420313351 / 250000000000000000) (√((1 : ℝ) - (((1007 / 2000) : ℝ)^2))) := bsqrt lowEnergy73_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy73_hz4 : B (55003644389987661 / 200000000000000000) (275018221949938307 / 1000000000000000000) ((√((1 : ℝ) - (((1007 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy73_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy73_hz5 : B (84078786361101599 / 250000000000000000) (67263029088885533 / 200000000000000000) (((1007 / 2000) : ℝ) * (kdot ((1007 / 2000)))) := bmul (bpoint ((1007 / 2000) : ℝ)) lowEnergy73_hz0 (by norm_num) (by norm_num)

theorem lowEnergy73_hz6 : B (611333367394344701 / 1000000000000000000) (152833341848591493 / 250000000000000000) (((√((1 : ℝ) - (((1007 / 2000) : ℝ)^2))) / Real.pi) + (((1007 / 2000) : ℝ) * (kdot ((1007 / 2000))))) := badd lowEnergy73_hz4 lowEnergy73_hz5 (by norm_num) (by norm_num)

theorem lowEnergy73_hz7 : B (611333367394344701 / 1000000000000000000) (152833341848591493 / 250000000000000000) (kappa ((1007 / 2000))) := by rw [kappa_eq]; exact lowEnergy73_hz6

theorem lowEnergy73_hz8 : B (710592892713448833 / 1000000000000000000) (710592892713448851 / 1000000000000000000) (kdot ((614377753969 / 1000000000000))) := by
    constructor
    · apply bkdot_lower (q := (244370322545208917 / 500000000000000000)) (a := (113649905268512783 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (488740645090417833 / 1000000000000000000)) (a := (227299810537025553 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy73_hz9 : B (75492004914398619 / 200000000000000000) (47182503071499137 / 125000000000000000) (((614377753969 / 1000000000000) : ℝ)^2) := bsq (bpoint ((614377753969 / 1000000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy73_hz10 : B (77817496928500863 / 125000000000000000) (124507995085601381 / 200000000000000000) ((1 : ℝ) - (((614377753969 / 1000000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy73_hz9 (by norm_num) (by norm_num)

theorem lowEnergy73_hz11 : B (197253006223607227 / 250000000000000000) (78901202489442891 / 100000000000000000) (√((1 : ℝ) - (((614377753969 / 1000000000000) : ℝ)^2))) := bsqrt lowEnergy73_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy73_hz12 : B (251150327841787877 / 1000000000000000000) (251150327841787879 / 1000000000000000000) ((√((1 : ℝ) - (((614377753969 / 1000000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy73_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy73_hz13 : B (436572465411623279 / 1000000000000000000) (436572465411623291 / 1000000000000000000) (((614377753969 / 1000000000000) : ℝ) * (kdot ((614377753969 / 1000000000000)))) := bmul (bpoint ((614377753969 / 1000000000000) : ℝ)) lowEnergy73_hz8 (by norm_num) (by norm_num)

theorem lowEnergy73_hz14 : B (171930698313352789 / 250000000000000000) (68772279325341117 / 100000000000000000) (((√((1 : ℝ) - (((614377753969 / 1000000000000) : ℝ)^2))) / Real.pi) + (((614377753969 / 1000000000000) : ℝ) * (kdot ((614377753969 / 1000000000000))))) := badd lowEnergy73_hz12 lowEnergy73_hz13 (by norm_num) (by norm_num)

theorem lowEnergy73_hz15 : B (171930698313352789 / 250000000000000000) (68772279325341117 / 100000000000000000) (kappa ((614377753969 / 1000000000000))) := by rw [kappa_eq]; exact lowEnergy73_hz14

theorem lowEnergy73 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1007 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (690553404141 / 1000000000000) := by
  have hk1 : kappa q ≤ (122266673479 / 200000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1007 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy73_hz7.2.trans (by norm_num))
  have hk2 : kappa ((614377753969 / 1000000000000) : ℝ) ≤ (343861396627 / 500000000000) := lowEnergy73_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((391138839607 / 500000000000) : ℝ)) (R := ((391571852309 / 500000000000) : ℝ)) (Q2 := ((614377753969 / 1000000000000) : ℝ)) (T := ((166001744553 / 200000000000) : ℝ))
    (B := ((690553404141 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy74_hz0 : B (166942607885357887 / 250000000000000000) (667770431541475197 / 1000000000000000000) (kdot ((503 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (575040858856676449 / 1000000000000000000)) (a := (521864985787372967 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (17970026839271139 / 31250000000000000)) (a := (104372997157460881 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy74_hz1 : B (253009 / 1000000) (253009 / 1000000) (((503 / 1000) : ℝ)^2) := bsq (bpoint ((503 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy74_hz2 : B (746991 / 1000000) (746991 / 1000000) ((1 : ℝ) - (((503 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy74_hz1 (by norm_num) (by norm_num)

theorem lowEnergy74_hz3 : B (432143205430792351 / 500000000000000000) (864286410861584703 / 1000000000000000000) (√((1 : ℝ) - (((503 / 1000) : ℝ)^2))) := bsqrt lowEnergy74_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy74_hz4 : B (4298607954242937 / 15625000000000000) (275110909071547969 / 1000000000000000000) ((√((1 : ℝ) - (((503 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy74_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy74_hz5 : B (83972131766335017 / 250000000000000000) (13435541082614481 / 40000000000000000) (((503 / 1000) : ℝ) * (kdot ((503 / 1000)))) := bmul (bpoint ((503 / 1000) : ℝ)) lowEnergy74_hz0 (by norm_num) (by norm_num)

theorem lowEnergy74_hz6 : B (152749859034222009 / 250000000000000000) (305499718068454997 / 500000000000000000) (((√((1 : ℝ) - (((503 / 1000) : ℝ)^2))) / Real.pi) + (((503 / 1000) : ℝ) * (kdot ((503 / 1000))))) := badd lowEnergy74_hz4 lowEnergy74_hz5 (by norm_num) (by norm_num)

theorem lowEnergy74_hz7 : B (152749859034222009 / 250000000000000000) (305499718068454997 / 500000000000000000) (kappa ((503 / 1000))) := by rw [kappa_eq]; exact lowEnergy74_hz6

theorem lowEnergy74_hz8 : B (710457814598205841 / 1000000000000000000) (710457814598205859 / 1000000000000000000) (kdot ((61404287319 / 100000000000))) := by
    constructor
    · apply bkdot_lower (q := (48900353550193179 / 100000000000000000)) (a := (227405900640652601 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (489003535501931789 / 1000000000000000000)) (a := (56851475160163147 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy74_hz9 : B (18852432505771521 / 50000000000000000) (377048650115430421 / 1000000000000000000) (((61404287319 / 100000000000) : ℝ)^2) := bsq (bpoint ((61404287319 / 100000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy74_hz10 : B (622951349884569579 / 1000000000000000000) (31147567494228479 / 50000000000000000) ((1 : ℝ) - (((61404287319 / 100000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy74_hz9 (by norm_num) (by norm_num)

theorem lowEnergy74_hz11 : B (394636335720803077 / 500000000000000000) (157854534288321231 / 200000000000000000) (√((1 : ℝ) - (((61404287319 / 100000000000) : ℝ)^2))) := bsqrt lowEnergy74_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy74_hz12 : B (15702080888409629 / 62500000000000000) (125616647107277033 / 500000000000000000) ((√((1 : ℝ) - (((61404287319 / 100000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy74_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy74_hz13 : B (5453144471952133 / 12500000000000000) (109062889439042663 / 250000000000000000) (((61404287319 / 100000000000) : ℝ) * (kdot ((61404287319 / 100000000000)))) := bmul (bpoint ((61404287319 / 100000000000) : ℝ)) lowEnergy74_hz8 (by norm_num) (by norm_num)

theorem lowEnergy74_hz14 : B (21483901624085147 / 31250000000000000) (343742425985362359 / 500000000000000000) (((√((1 : ℝ) - (((61404287319 / 100000000000) : ℝ)^2))) / Real.pi) + (((61404287319 / 100000000000) : ℝ) * (kdot ((61404287319 / 100000000000))))) := badd lowEnergy74_hz12 lowEnergy74_hz13 (by norm_num) (by norm_num)

theorem lowEnergy74_hz15 : B (21483901624085147 / 31250000000000000) (343742425985362359 / 500000000000000000) (kappa ((61404287319 / 100000000000))) := by rw [kappa_eq]; exact lowEnergy74_hz14

theorem lowEnergy74 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (503 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (690314767177 / 1000000000000) := by
  have hk1 : kappa q ≤ (610999436137 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((503 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy74_hz7.2.trans (by norm_num))
  have hk2 : kappa ((61404287319 / 100000000000) : ℝ) ≤ (687484851971 / 1000000000000) := lowEnergy74_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((782064214843 / 1000000000000) : ℝ)) (R := ((782930240247 / 1000000000000) : ℝ)) (Q2 := ((61404287319 / 100000000000) : ℝ)) (T := ((414932562677 / 500000000000) : ℝ))
    (B := ((690314767177 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy75_hz0 : B (10431036194586377 / 15625000000000000) (667586316453573231 / 1000000000000000000) (kdot ((201 / 400))) := by
    constructor
    · apply bkdot_lower (q := (575425762937536763 / 1000000000000000000)) (a := (26107709654557959 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (287712881468768381 / 500000000000000000)) (a := (522154193091088333 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy75_hz1 : B (40401 / 160000) (40401 / 160000) (((201 / 400) : ℝ)^2) := bsq (bpoint ((201 / 400) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy75_hz2 : B (119599 / 160000) (119599 / 160000) ((1 : ℝ) - (((201 / 400) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy75_hz1 (by norm_num) (by norm_num)

theorem lowEnergy75_hz3 : B (108072151101706123 / 125000000000000000) (172915441762729797 / 200000000000000000) (√((1 : ℝ) - (((201 / 400) : ℝ)^2))) := bsqrt lowEnergy75_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy75_hz4 : B (275203472934572029 / 1000000000000000000) (27520347293457203 / 100000000000000000) ((√((1 : ℝ) - (((201 / 400) : ℝ)^2))) / Real.pi) := bdiv lowEnergy75_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy75_hz5 : B (83865531004474471 / 250000000000000000) (335462124017920549 / 1000000000000000000) (((201 / 400) : ℝ) * (kdot ((201 / 400)))) := bmul (bpoint ((201 / 400) : ℝ)) lowEnergy75_hz0 (by norm_num) (by norm_num)

theorem lowEnergy75_hz6 : B (610665596952469913 / 1000000000000000000) (610665596952492579 / 1000000000000000000) (((√((1 : ℝ) - (((201 / 400) : ℝ)^2))) / Real.pi) + (((201 / 400) : ℝ) * (kdot ((201 / 400))))) := badd lowEnergy75_hz4 lowEnergy75_hz5 (by norm_num) (by norm_num)

theorem lowEnergy75_hz7 : B (610665596952469913 / 1000000000000000000) (610665596952492579 / 1000000000000000000) (kappa ((201 / 400))) := by rw [kappa_eq]; exact lowEnergy75_hz6

theorem lowEnergy75_hz8 : B (177580704562264817 / 250000000000000000) (355161409124529643 / 500000000000000000) (kdot ((122741616929 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (244633160644464629 / 500000000000000000)) (a := (2843899081566721 / 6250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (489266321288929257 / 1000000000000000000)) (a := (227511926525337667 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy75_hz9 : B (94159403289658621 / 250000000000000000) (75327522631726897 / 200000000000000000) (((122741616929 / 200000000000) : ℝ)^2) := bsq (bpoint ((122741616929 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy75_hz10 : B (124672477368273103 / 200000000000000000) (155840596710341379 / 250000000000000000) ((1 : ℝ) - (((122741616929 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy75_hz9 (by norm_num) (by norm_num)

theorem lowEnergy75_hz11 : B (39476650910423161 / 50000000000000000) (789533018208463221 / 1000000000000000000) (√((1 : ℝ) - (((122741616929 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy75_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy75_hz12 : B (50263233032856131 / 200000000000000000) (15707260322767541 / 62500000000000000) ((√((1 : ℝ) - (((122741616929 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy75_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy75_hz13 : B (87186171253453723 / 200000000000000000) (435930856267268627 / 1000000000000000000) (((122741616929 / 200000000000) : ℝ) * (kdot ((122741616929 / 200000000000)))) := bmul (bpoint ((122741616929 / 200000000000) : ℝ)) lowEnergy75_hz8 (by norm_num) (by norm_num)

theorem lowEnergy75_hz14 : B (68724702143154927 / 100000000000000000) (687247021431549283 / 1000000000000000000) (((√((1 : ℝ) - (((122741616929 / 200000000000) : ℝ)^2))) / Real.pi) + (((122741616929 / 200000000000) : ℝ) * (kdot ((122741616929 / 200000000000))))) := badd lowEnergy75_hz12 lowEnergy75_hz13 (by norm_num) (by norm_num)

theorem lowEnergy75_hz15 : B (68724702143154927 / 100000000000000000) (687247021431549283 / 1000000000000000000) (kappa ((122741616929 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy75_hz14

theorem lowEnergy75 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (201 / 400)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (690076241231 / 1000000000000) := by
  have hk1 : kappa q ≤ (610665596953 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((201 / 400) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy75_hz7.2.trans (by norm_num))
  have hk2 : kappa ((122741616929 / 200000000000) : ℝ) ≤ (85905877679 / 125000000000) := lowEnergy75_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((781850751073 / 1000000000000) : ℝ)) (R := ((782716776477 / 1000000000000) : ℝ)) (Q2 := ((122741616929 / 200000000000) : ℝ)) (T := ((414860784971 / 500000000000) : ℝ))
    (B := ((690076241231 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy76_hz0 : B (333701131620298941 / 500000000000000000) (83425282905080561 / 125000000000000000) (kdot ((251 / 500))) := by
    constructor
    · apply bkdot_lower (q := (575810665731054759 / 1000000000000000000)) (a := (65305412900245601 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (287905332865527379 / 500000000000000000)) (a := (522443303201891601 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy76_hz1 : B (63001 / 250000) (63001 / 250000) (((251 / 500) : ℝ)^2) := bsq (bpoint ((251 / 500) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy76_hz2 : B (186999 / 250000) (186999 / 250000) ((1 : ℝ) - (((251 / 500) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy76_hz1 (by norm_num) (by norm_num)

theorem lowEnergy76_hz3 : B (864867619928044247 / 1000000000000000000) (108108452491005531 / 125000000000000000) (√((1 : ℝ) - (((251 / 500) : ℝ)^2))) := bsqrt lowEnergy76_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy76_hz4 : B (275295913663341693 / 1000000000000000000) (137647956831670847 / 500000000000000000) ((√((1 : ℝ) - (((251 / 500) : ℝ)^2))) / Real.pi) := bdiv lowEnergy76_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy76_hz5 : B (41879492018347517 / 125000000000000000) (335035936146803533 / 1000000000000000000) (((251 / 500) : ℝ) * (kdot ((251 / 500)))) := bmul (bpoint ((251 / 500) : ℝ)) lowEnergy76_hz0 (by norm_num) (by norm_num)

theorem lowEnergy76_hz6 : B (610331849810121829 / 1000000000000000000) (610331849810145227 / 1000000000000000000) (((√((1 : ℝ) - (((251 / 500) : ℝ)^2))) / Real.pi) + (((251 / 500) : ℝ) * (kdot ((251 / 500))))) := badd lowEnergy76_hz4 lowEnergy76_hz5 (by norm_num) (by norm_num)

theorem lowEnergy76_hz7 : B (610331849810121829 / 1000000000000000000) (610331849810145227 / 1000000000000000000) (kappa ((251 / 500))) := by rw [kappa_eq]; exact lowEnergy76_hz6

theorem lowEnergy76_hz8 : B (710187903548789323 / 1000000000000000000) (355093951774394671 / 500000000000000000) (kdot ((38335836769 / 62500000000))) := by
    constructor
    · apply bkdot_lower (q := (24476450131060189 / 50000000000000000)) (a := (56904472070786253 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (489529002621203779 / 1000000000000000000)) (a := (455235776566289997 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy76_hz9 : B (376226913479529563 / 1000000000000000000) (94056728369882391 / 250000000000000000) (((38335836769 / 62500000000) : ℝ)^2) := bsq (bpoint ((38335836769 / 62500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy76_hz10 : B (155943271630117609 / 250000000000000000) (623773086520470437 / 1000000000000000000) ((1 : ℝ) - (((38335836769 / 62500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy76_hz9 (by norm_num) (by norm_num)

theorem lowEnergy76_hz11 : B (394896532816024619 / 500000000000000000) (19744826640801231 / 25000000000000000) (√((1 : ℝ) - (((38335836769 / 62500000000) : ℝ)^2))) := bsqrt lowEnergy76_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy76_hz12 : B (62849735207521177 / 250000000000000000) (25139894083008471 / 100000000000000000) ((√((1 : ℝ) - (((38335836769 / 62500000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy76_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy76_hz13 : B (435610360732235253 / 1000000000000000000) (87122072146447053 / 200000000000000000) (((38335836769 / 62500000000) : ℝ) * (kdot ((38335836769 / 62500000000)))) := bmul (bpoint ((38335836769 / 62500000000) : ℝ)) lowEnergy76_hz8 (by norm_num) (by norm_num)

theorem lowEnergy76_hz14 : B (687009301562319961 / 1000000000000000000) (27480372062492799 / 40000000000000000) (((√((1 : ℝ) - (((38335836769 / 62500000000) : ℝ)^2))) / Real.pi) + (((38335836769 / 62500000000) : ℝ) * (kdot ((38335836769 / 62500000000))))) := badd lowEnergy76_hz12 lowEnergy76_hz13 (by norm_num) (by norm_num)

theorem lowEnergy76_hz15 : B (687009301562319961 / 1000000000000000000) (27480372062492799 / 40000000000000000) (kappa ((38335836769 / 62500000000))) := by rw [kappa_eq]; exact lowEnergy76_hz14

theorem lowEnergy76 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (251 / 500)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (172459456557 / 250000000000) := by
  have hk1 : kappa q ≤ (610331849811 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((251 / 500) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy76_hz7.2.trans (by norm_num))
  have hk2 : kappa ((38335836769 / 62500000000) : ℝ) ≤ (687009301563 / 1000000000000) := lowEnergy76_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((156327457577 / 200000000000) : ℝ)) (R := ((782503313289 / 1000000000000) : ℝ)) (Q2 := ((38335836769 / 62500000000) : ℝ)) (T := ((414789028253 / 500000000000) : ℝ))
    (B := ((172459456557 / 250000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy77_hz0 : B (83402283972353271 / 125000000000000000) (26688730871154973 / 40000000000000000) (kdot ((1003 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (144048891873846951 / 250000000000000000)) (a := (522732316314277441 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (576195567495387803 / 1000000000000000000)) (a := (261366158157100899 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy77_hz1 : B (1006009 / 4000000) (1006009 / 4000000) (((1003 / 2000) : ℝ)^2) := bsq (bpoint ((1003 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy77_hz2 : B (2993991 / 4000000) (2993991 / 4000000) ((1 : ℝ) - (((1003 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy77_hz1 (by norm_num) (by norm_num)

theorem lowEnergy77_hz3 : B (432578822297162393 / 500000000000000000) (865157644594324787 / 1000000000000000000) (√((1 : ℝ) - (((1003 / 2000) : ℝ)^2))) := bsqrt lowEnergy77_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy77_hz4 : B (275388231381855943 / 1000000000000000000) (34423528922731993 / 125000000000000000) ((√((1 : ℝ) - (((1003 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy77_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy77_hz5 : B (334609963297081323 / 1000000000000000000) (167304981648552737 / 500000000000000000) (((1003 / 2000) : ℝ) * (kdot ((1003 / 2000)))) := bmul (bpoint ((1003 / 2000) : ℝ)) lowEnergy77_hz0 (by norm_num) (by norm_num)

theorem lowEnergy77_hz6 : B (304999097339468633 / 500000000000000000) (304999097339480709 / 500000000000000000) (((√((1 : ℝ) - (((1003 / 2000) : ℝ)^2))) / Real.pi) + (((1003 / 2000) : ℝ) * (kdot ((1003 / 2000))))) := badd lowEnergy77_hz4 lowEnergy77_hz5 (by norm_num) (by norm_num)

theorem lowEnergy77_hz7 : B (304999097339468633 / 500000000000000000) (304999097339480709 / 500000000000000000) (kappa ((1003 / 2000))) := by rw [kappa_eq]; exact lowEnergy77_hz6

theorem lowEnergy77_hz8 : B (355026535189222487 / 500000000000000000) (710053070378444993 / 1000000000000000000) (kdot ((153259696033 / 250000000000))) := by
    constructor
    · apply bkdot_lower (q := (61223947459006157 / 125000000000000000)) (a := (227723786007498519 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (97958315934409851 / 200000000000000000)) (a := (45544757201499701 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy77_hz9 : B (187908275425020447 / 500000000000000000) (75163310170008179 / 200000000000000000) (((153259696033 / 250000000000) : ℝ)^2) := bsq (bpoint ((153259696033 / 250000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy77_hz10 : B (124836689829991821 / 200000000000000000) (312091724574979553 / 500000000000000000) ((1 : ℝ) - (((153259696033 / 250000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy77_hz9 (by norm_num) (by norm_num)

theorem lowEnergy77_hz11 : B (395026407076146969 / 500000000000000000) (790052814152293939 / 1000000000000000000) (√((1 : ℝ) - (((153259696033 / 250000000000) : ℝ)^2))) := bsqrt lowEnergy77_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy77_hz12 : B (251481621352000207 / 1000000000000000000) (15717601334500013 / 62500000000000000) ((√((1 : ℝ) - (((153259696033 / 250000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy77_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy77_hz13 : B (435290070933995331 / 1000000000000000000) (27205629433374709 / 62500000000000000) (((153259696033 / 250000000000) : ℝ) * (kdot ((153259696033 / 250000000000)))) := bmul (bpoint ((153259696033 / 250000000000) : ℝ)) lowEnergy77_hz8 (by norm_num) (by norm_num)

theorem lowEnergy77_hz14 : B (343385846142997769 / 500000000000000000) (21461615383937361 / 31250000000000000) (((√((1 : ℝ) - (((153259696033 / 250000000000) : ℝ)^2))) / Real.pi) + (((153259696033 / 250000000000) : ℝ) * (kdot ((153259696033 / 250000000000))))) := badd lowEnergy77_hz12 lowEnergy77_hz13 (by norm_num) (by norm_num)

theorem lowEnergy77_hz15 : B (343385846142997769 / 500000000000000000) (21461615383937361 / 31250000000000000) (kappa ((153259696033 / 250000000000))) := by rw [kappa_eq]; exact lowEnergy77_hz14

theorem lowEnergy77 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1003 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (344799761047 / 500000000000) := by
  have hk1 : kappa q ≤ (609998194679 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1003 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy77_hz7.2.trans (by norm_num))
  have hk2 : kappa ((153259696033 / 250000000000) : ℝ) ≤ (343385846143 / 500000000000) := lowEnergy77_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((781423825257 / 1000000000000) : ℝ)) (R := ((782289850661 / 1000000000000) : ℝ)) (Q2 := ((153259696033 / 250000000000) : ℝ)) (T := ((414717292511 / 500000000000) : ℝ))
    (B := ((344799761047 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy78_hz0 : B (667034341944688391 / 1000000000000000000) (13340686838894763 / 20000000000000000) (kdot ((501 / 1000))) := by
    constructor
    · apply bkdot_lower (q := (23063218739533769 / 40000000000000000)) (a := (104604246524425811 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (18018139640260757 / 31250000000000000)) (a := (32688827038878181 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy78_hz1 : B (251001 / 1000000) (251001 / 1000000) (((501 / 1000) : ℝ)^2) := bsq (bpoint ((501 / 1000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy78_hz2 : B (748999 / 1000000) (748999 / 1000000) ((1 : ℝ) - (((501 / 1000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy78_hz1 (by norm_num) (by norm_num)

theorem lowEnergy78_hz3 : B (865447283201004681 / 1000000000000000000) (432723641600502341 / 500000000000000000) (√((1 : ℝ) - (((501 / 1000) : ℝ)^2))) := bsqrt lowEnergy78_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy78_hz4 : B (68870106553445663 / 250000000000000000) (275480426213782653 / 1000000000000000000) ((√((1 : ℝ) - (((501 / 1000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy78_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy78_hz5 : B (334184205314288883 / 1000000000000000000) (167092102657156907 / 500000000000000000) (((501 / 1000) : ℝ) * (kdot ((501 / 1000)))) := bmul (bpoint ((501 / 1000) : ℝ)) lowEnergy78_hz0 (by norm_num) (by norm_num)

theorem lowEnergy78_hz6 : B (121932926305614307 / 200000000000000000) (609664631528096467 / 1000000000000000000) (((√((1 : ℝ) - (((501 / 1000) : ℝ)^2))) / Real.pi) + (((501 / 1000) : ℝ) * (kdot ((501 / 1000))))) := badd lowEnergy78_hz4 lowEnergy78_hz5 (by norm_num) (by norm_num)

theorem lowEnergy78_hz7 : B (121932926305614307 / 200000000000000000) (609664631528096467 / 1000000000000000000) (kappa ((501 / 1000))) := by rw [kappa_eq]; exact lowEnergy78_hz6

theorem lowEnergy78_hz8 : B (709918318623790497 / 1000000000000000000) (177479579655947629 / 250000000000000000) (kdot ((122540854421 / 200000000000))) := by
    constructor
    · apply bkdot_lower (q := (24502702630285277 / 50000000000000000)) (a := (227829619788118729 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (490054052605705539 / 1000000000000000000)) (a := (45565923957623743 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy78_hz9 : B (375406525055717881 / 1000000000000000000) (187703262527858941 / 500000000000000000) (((122540854421 / 200000000000) : ℝ)^2) := bsq (bpoint ((122540854421 / 200000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy78_hz10 : B (312296737472141059 / 500000000000000000) (624593474944282119 / 1000000000000000000) ((1 : ℝ) - (((122540854421 / 200000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy78_hz9 (by norm_num) (by norm_num)

theorem lowEnergy78_hz11 : B (790312264199589729 / 1000000000000000000) (790312264199589731 / 1000000000000000000) (√((1 : ℝ) - (((122540854421 / 200000000000) : ℝ)^2))) := bsqrt lowEnergy78_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy78_hz12 : B (251564206867025309 / 1000000000000000000) (251564206867025311 / 1000000000000000000) ((√((1 : ℝ) - (((122540854421 / 200000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy78_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy78_hz13 : B (434969986666395021 / 1000000000000000000) (217484993333197517 / 500000000000000000) (((122540854421 / 200000000000) : ℝ) * (kdot ((122540854421 / 200000000000)))) := bmul (bpoint ((122540854421 / 200000000000) : ℝ)) lowEnergy78_hz8 (by norm_num) (by norm_num)

theorem lowEnergy78_hz14 : B (68653419353342033 / 100000000000000000) (137306838706684069 / 200000000000000000) (((√((1 : ℝ) - (((122540854421 / 200000000000) : ℝ)^2))) / Real.pi) + (((122540854421 / 200000000000) : ℝ) * (kdot ((122540854421 / 200000000000))))) := badd lowEnergy78_hz12 lowEnergy78_hz13 (by norm_num) (by norm_num)

theorem lowEnergy78_hz15 : B (68653419353342033 / 100000000000000000) (137306838706684069 / 200000000000000000) (kappa ((122540854421 / 200000000000))) := by rw [kappa_eq]; exact lowEnergy78_hz14

theorem lowEnergy78 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (501 / 1000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (344680664379 / 500000000000) := by
  have hk1 : kappa q ≤ (609664631529 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((501 / 1000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy78_hz7.2.trans (by norm_num))
  have hk2 : kappa ((122540854421 / 200000000000) : ℝ) ≤ (343267096767 / 500000000000) := lowEnergy78_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((390605181587 / 500000000000) : ℝ)) (R := ((391038194289 / 500000000000) : ℝ)) (Q2 := ((122540854421 / 200000000000) : ℝ)) (T := ((82929115547 / 100000000000) : ℝ))
    (B := ((344680664379 / 500000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

theorem lowEnergy79_hz0 : B (166712618403737239 / 250000000000000000) (66685047361500037 / 100000000000000000) (kdot ((1001 / 2000))) := by
    constructor
    · apply bkdot_lower (q := (288482684483692529 / 500000000000000000)) (a := (65413756539887209 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (576965368967385057 / 1000000000000000000)) (a := (261655026159508457 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy79_hz1 : B (1002001 / 4000000) (1002001 / 4000000) (((1001 / 2000) : ℝ)^2) := bsq (bpoint ((1001 / 2000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy79_hz2 : B (2997999 / 4000000) (2997999 / 4000000) ((1 : ℝ) - (((1001 / 2000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy79_hz1 (by norm_num) (by norm_num)

theorem lowEnergy79_hz3 : B (432868268067780639 / 500000000000000000) (865736536135561279 / 1000000000000000000) (√((1 : ℝ) - (((1001 / 2000) : ℝ)^2))) := bsqrt lowEnergy79_hz2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy79_hz4 : B (27557249828245969 / 100000000000000000) (275572498282459691 / 1000000000000000000) ((√((1 : ℝ) - (((1001 / 2000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy79_hz3 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy79_hz5 : B (10429958188883811 / 31250000000000000) (166879331022153843 / 500000000000000000) (((1001 / 2000) : ℝ) * (kdot ((1001 / 2000)))) := bmul (bpoint ((1001 / 2000) : ℝ)) lowEnergy79_hz0 (by norm_num) (by norm_num)

theorem lowEnergy79_hz6 : B (304665580163370821 / 500000000000000000) (609331160326767377 / 1000000000000000000) (((√((1 : ℝ) - (((1001 / 2000) : ℝ)^2))) / Real.pi) + (((1001 / 2000) : ℝ) * (kdot ((1001 / 2000))))) := badd lowEnergy79_hz4 lowEnergy79_hz5 (by norm_num) (by norm_num)

theorem lowEnergy79_hz7 : B (304665580163370821 / 500000000000000000) (609331160326767377 / 1000000000000000000) (kappa ((1001 / 2000))) := by rw [kappa_eq]; exact lowEnergy79_hz6

theorem lowEnergy79_hz8 : B (709783648164828769 / 1000000000000000000) (709783648164828789 / 1000000000000000000) (kdot ((76546231523 / 125000000000))) := by
    constructor
    · apply bkdot_lower (q := (122579105399440553 / 250000000000000000)) (a := (455870779438502323 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (490316421597762211 / 1000000000000000000)) (a := (455870779438502293 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowEnergy79_hz9 : B (374996835863854009 / 1000000000000000000) (37499683586385401 / 100000000000000000) (((76546231523 / 125000000000) : ℝ)^2) := bsq (bpoint ((76546231523 / 125000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy79_hz10 : B (62500316413614599 / 100000000000000000) (625003164136145991 / 1000000000000000000) ((1 : ℝ) - (((76546231523 / 125000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) lowEnergy79_hz9 (by norm_num) (by norm_num)

theorem lowEnergy79_hz11 : B (790571416214971681 / 1000000000000000000) (790571416214971683 / 1000000000000000000) (√((1 : ℝ) - (((76546231523 / 125000000000) : ℝ)^2))) := bsqrt lowEnergy79_hz10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy79_hz12 : B (125823348757772919 / 500000000000000000) (3145583718944323 / 12500000000000000) ((√((1 : ℝ) - (((76546231523 / 125000000000) : ℝ)^2))) / Real.pi) := bdiv lowEnergy79_hz11 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowEnergy79_hz13 : B (54331263463664557 / 125000000000000000) (434650107709316469 / 1000000000000000000) (((76546231523 / 125000000000) : ℝ) * (kdot ((76546231523 / 125000000000)))) := bmul (bpoint ((76546231523 / 125000000000) : ℝ)) lowEnergy79_hz8 (by norm_num) (by norm_num)

theorem lowEnergy79_hz14 : B (343148402612431147 / 500000000000000000) (686296805224862309 / 1000000000000000000) (((√((1 : ℝ) - (((76546231523 / 125000000000) : ℝ)^2))) / Real.pi) + (((76546231523 / 125000000000) : ℝ) * (kdot ((76546231523 / 125000000000))))) := badd lowEnergy79_hz12 lowEnergy79_hz13 (by norm_num) (by norm_num)

theorem lowEnergy79_hz15 : B (343148402612431147 / 500000000000000000) (686296805224862309 / 1000000000000000000) (kappa ((76546231523 / 125000000000))) := by rw [kappa_eq]; exact lowEnergy79_hz14

theorem lowEnergy79 {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (1001 / 2000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ (689123246139 / 1000000000000) := by
  have hk1 : kappa q ≤ (609331160327 / 1000000000000) := by
    have hm := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show ((1001 / 2000) : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hqu
    exact hm.trans (lowEnergy79_hz7.2.trans (by norm_num))
  have hk2 : kappa ((76546231523 / 125000000000) : ℝ) ≤ (27451872209 / 40000000000) := lowEnergy79_hz15.2.trans (by norm_num)
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := ((1732050807569 / 500000000000) : ℝ)) (s0 := ((499999992187 / 500000000000) : ℝ)) (g0 := ((998268667967 / 1000000000000) : ℝ))
    (G := ((125216600101 / 125000000000) : ℝ)) (t2 := ((3467101615139 / 1000000000000) : ℝ)) (r := ((89442719099991 / 1000000000000) : ℝ)) (F := ((10727 / 1000000) : ℝ))
    (U := ((195249225403 / 250000000000) : ℝ)) (R := ((97732865877 / 125000000000) : ℝ)) (Q2 := ((76546231523 / 125000000000) : ℝ)) (T := ((414573883911 / 500000000000) : ℝ))
    (B := ((689123246139 / 1000000000000) : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),h.2⟩

end BstLean.BlueprintLow
